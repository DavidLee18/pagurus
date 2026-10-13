||| Intra-procedural ownership checker with join and loop fixpoints.
module Pagurus.Checker

import Data.String
import Decidable.Equality
import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice

%default total

public export
Env : Type
Env = List (Place, Status)

||| A single environment: places are interned uniquely per binding, so
||| shadowing does not need a scope stack.
public export
Scopes : Type
Scopes = Env

public export
lookupName : Place -> Env -> Maybe Status
lookupName n [] = Nothing
lookupName n ((k, v) :: xs) = if n == k then Just v else lookupName n xs

public export
setName : Place -> Status -> Env -> Env
setName n v [] = [(n, v)]
setName n v ((k, x) :: xs) = if n == k then (n, v) :: xs else (k, x) :: setName n v xs

public export
deleteName : Place -> Env -> Env
deleteName _ [] = []
deleteName n ((k, v) :: xs) =
  if k == n then deleteName n xs else (k, v) :: deleteName n xs

public export
lookupPlace : Place -> Scopes -> Maybe Status
lookupPlace = lookupName

public export
setPlace : Place -> Status -> Scopes -> Scopes
setPlace = setName

public export
declarePlace : Place -> Status -> Scopes -> Scopes
declarePlace = setName

public export
joinEnv : Env -> Env -> Env
joinEnv [] ys = ys
joinEnv ((n, s) :: xs) ys =
  case lookupName n ys of
    Nothing => (n, s) :: joinEnv xs ys
    Just s2 => (n, join s s2) :: joinEnv xs (deleteName n ys)

public export
joinScopes : Scopes -> Scopes -> Scopes
joinScopes = joinEnv

public export
eqStatus : Status -> Status -> Bool
eqStatus [] [] = True
eqStatus (a :: as) (b :: bs) = a == b && eqStatus as bs
eqStatus _ _ = False

public export
eqEnv : Env -> Env -> Bool
eqEnv [] [] = True
eqEnv ((n, s) :: xs) ys =
  case lookupName n ys of
    Nothing => False
    Just s2 => eqStatus s s2 && eqEnv xs (deleteName n ys)
eqEnv _ _ = False

public export
eqScopes : Scopes -> Scopes -> Bool
eqScopes = eqEnv

mutual
  ||| True when `p` is used as a unique-owner rvalue (move/return), not a borrow.
  export
  movedInExpr : Place -> Expr -> Bool
  movedInExpr p (EVar _ q _) = p == q
  movedInExpr p (EAssign _ _ _ _ rhs) = movedInExpr p rhs
  movedInExpr p (EMalloc _ args) = movedInExprs p args
  movedInExpr p (ECall _ _ args) = movedInExprs p args
  movedInExpr p (EUse _ args) = movedInExprs p args
  movedInExpr _ (ELit _) = False
  movedInExpr _ (ENull _) = False
  movedInExpr _ (EUnsupported _ _) = False

  export
  movedInExprs : Place -> List Expr -> Bool
  movedInExprs _ [] = False
  movedInExprs p (e :: es) = movedInExpr p e || movedInExprs p es

||| Per-parameter consume summary. `May` is the join of Always and Never
||| (consumed on some path). Call sites treat `May` as a move.
public export
data Consume = Never | May | Always

public export
Eq Consume where
  Never == Never = True
  May == May = True
  Always == Always = True
  _ == _ = False

||| True when a call-site argument must be moved (Always or May).
public export
doesConsume : Consume -> Bool
doesConsume Never = False
doesConsume May = True
doesConsume Always = True

||| Place of a variable argument. A pointer assignment is not an `EVar`;
||| `valuePlaces` tracks the destination it stores into.
public export
argVarPlace : Expr -> Maybe Place
argVarPlace (EVar _ p _) = Just p
argVarPlace _ = Nothing

public export
placeIn : Place -> List Place -> Bool
placeIn _ [] = False
placeIn p (q :: qs) = (p == q) || placeIn p qs

||| Places of Never (borrow) `EVar` arguments. Extra args beyond `modes`
||| are treated as consumed, matching `consumeHead [] = Always`.
public export
borrowPlaces : List Expr -> List Consume -> List Place
borrowPlaces [] _ = []
borrowPlaces (e :: es) [] = borrowPlaces es []
borrowPlaces (e :: es) (m :: ms) =
  case (doesConsume m, argVarPlace e) of
    (False, Just p) => p :: borrowPlaces es ms
    _ => borrowPlaces es ms

||| Places of May/Always (consume) `EVar` arguments, including extras.
public export
consumePlaces : List Expr -> List Consume -> List Place
consumePlaces [] _ = []
consumePlaces (e :: es) [] =
  case argVarPlace e of
    Just p => p :: consumePlaces es []
    Nothing => consumePlaces es []
consumePlaces (e :: es) (m :: ms) =
  case (doesConsume m, argVarPlace e) of
    (True, Just p) => p :: consumePlaces es ms
    _ => consumePlaces es ms

public export
placesOverlap : List Place -> List Place -> Bool
placesOverlap [] _ = False
placesOverlap (p :: ps) qs = placeIn p qs || placesOverlap ps qs

||| True when the same tracked owner (or an alias of it, via the same
||| interned place) is passed to a borrowed (Never) parameter and also to
||| a consuming (May/Always) parameter. Consuming arguments are still
||| checked against each other by `checkArgsModes` / `takeOwner`.
public export
mixedAlias : List Expr -> List Consume -> Bool
mixedAlias es ms = placesOverlap (borrowPlaces es ms) (consumePlaces es ms)

||| Call-site mixed borrow+consume of the same owner.
public export
mixedAliasDiag : Nat -> String -> Expr -> Diag
mixedAliasDiag nid callee e =
  MkDiag KUnproven
    ("aliased pointer passed as both a borrow and a consume to `" ++ callee ++ "`")
    (exprId e) "passed here"
    [(nid, "called here")]
    "the same owner (or an alias of it) is passed to a Never parameter and a May/Always parameter; after the callee consumes it, the borrowed name would be a use-after-free"

||| Extra arguments beyond the summarised parameter list are treated as
||| consumed (variadic / unknown tail). Empty list therefore heads at Always.
public export
consumeHead : List Consume -> Consume
consumeHead [] = Always
consumeHead (m :: _) = m

public export
consumeTail : List Consume -> List Consume
consumeTail [] = []
consumeTail (_ :: ms) = ms

||| True when evaluation can yield a live pointer (`HVPtr`).
||| Null, literals, uses, and ordinary calls do not. Prototype `realloc`
||| does, matching `HERealloc`. A defined function of that name still
||| returns `HVNone`, so this is a slight over-approx only for that name.
public export
maybeLivePtr : Expr -> Bool
maybeLivePtr (EVar _ _ _) = True
maybeLivePtr (EMalloc _ _) = True
maybeLivePtr (ECall _ callee _) = callee == "realloc"
maybeLivePtr (EAssign _ _ _ _ rhs) = maybeLivePtr rhs
maybeLivePtr (ELit _) = False
maybeLivePtr (ENull _) = False
maybeLivePtr (EUse _ _) = False
maybeLivePtr (EUnsupported _ _) = False

||| Places that hold this expression's pointer value.
||| `HEAsgPtr` stores a live rhs address into the destination and does
||| not clear the rhs. A null or non-pointer rhs does not, so the
||| destination is left out. Fresh `malloc` has no existing place.
public export
valuePlaces : Expr -> List Place
valuePlaces (EVar _ p _) = [p]
valuePlaces (EAssign _ p _ Ptr rhs) =
  let rest = valuePlaces rhs in
  if maybeLivePtr rhs then p :: rest else rest
valuePlaces (EAssign _ _ _ Copy rhs) = valuePlaces rhs
valuePlaces (EMalloc _ _) = []
valuePlaces (ECall _ _ _) = []
valuePlaces (ELit _) = []
valuePlaces (ENull _) = []
valuePlaces (EUse _ _) = []
valuePlaces (EUnsupported _ _) = []

||| True when any place is in both lists.
public export
placesHitBoth : List Place -> List Place -> List Place -> Bool
placesHitBoth [] _ _ = False
placesHitBoth (p :: ps) bs cs =
  (placeIn p bs && placeIn p cs) || placesHitBoth ps bs cs

||| Places of Never arguments, including a pointer assignment's destination.
||| Extra arguments are consumed, matching `borrowPlaces` on `[]`.
public export
aliasBorrowPlaces : List Expr -> List Consume -> List Place
aliasBorrowPlaces [] _ = []
aliasBorrowPlaces (_ :: es) [] = aliasBorrowPlaces es []
aliasBorrowPlaces (e :: es) (m :: ms) =
  if doesConsume m
    then aliasBorrowPlaces es ms
    else valuePlaces e ++ aliasBorrowPlaces es ms

||| Places of May/Always arguments, including extras and assignment
||| destinations that hold the consumed value.
public export
aliasConsumePlaces : List Expr -> List Consume -> List Place
aliasConsumePlaces [] _ = []
aliasConsumePlaces (e :: es) [] = valuePlaces e ++ aliasConsumePlaces es []
aliasConsumePlaces (e :: es) (m :: ms) =
  if doesConsume m
    then valuePlaces e ++ aliasConsumePlaces es ms
    else aliasConsumePlaces es ms

||| Borrow and consume arguments that denote one place, where the borrow
||| may be a pointer assignment. `f(p, p)` is already `mixedAlias`.
||| This is `f(q = malloc(), q)` and a nested store of that address,
||| `f(r = (q = malloc()), q)`. `f(q = NULL, q)` is not: null is not a
||| live pointer. Distinct places stay apart.
public export
assignAlias : List Expr -> List Consume -> Bool
assignAlias es ms =
  placesOverlap (aliasBorrowPlaces es ms) (aliasConsumePlaces es ms)

||| First argument whose value shares a place with both sides.
public export
mixedAliasArg : List Expr -> List Consume -> Expr
mixedAliasArg [] _ = EUnsupported 0 "mixed alias"
mixedAliasArg (e :: es) ms =
  let bs = aliasBorrowPlaces (e :: es) ms
      cs = aliasConsumePlaces (e :: es) ms
  in if placesHitBoth (valuePlaces e) bs cs
       then e
       else mixedAliasArg es (consumeTail ms)

public export
record Ctx where
  constructor MkCtx
  ||| Per defined function, one `Consume` per parameter (Copy params are Never).
  summaries : List (String, List Consume)
  defined : List String

public export
isDefined : Ctx -> String -> Bool
isDefined ctx n = elem n ctx.defined

lookupNamed : List (String, List Consume) -> String -> Maybe (List Consume)
lookupNamed [] _ = Nothing
lookupNamed ((n, ms) :: xs) k with (decEq n k)
  lookupNamed ((n, ms) :: xs) k | Yes _ = Just ms
  lookupNamed ((n, ms) :: xs) k | No _ = lookupNamed xs k

lookupNamedList : List (String, List Consume) -> String -> List Consume
lookupNamedList acc n = case lookupNamed acc n of
  Nothing => []
  Just ms => ms

||| Parameter consume modes of a defined function; `[]` if unknown.
public export
funModes : Ctx -> String -> List Consume
funModes ctx n = lookupNamedList ctx.summaries n

||| True when any parameter of `n` is May or Always.
public export
isConsuming : Ctx -> String -> Bool
isConsuming ctx n = any doesConsume (funModes ctx n)

||| `malloc`/`calloc` only. `free` is `SDrop` in the C lowering; a
||| hand-written `(call free …)` is not a builtin use — it is opaque
||| (unsupported) unless a user function of that name is defined.
||| `realloc` is handled separately (`isRealloc`): it consumes the first
||| argument and yields a fresh owner, and is not a builtin borrow.
public export
isBuiltin : String -> Bool
isBuiltin n = n == "malloc" || n == "calloc"

||| Prototype `realloc` (no body in this TU). A definition of that name in
||| the unit is summarised like any other function.
public export
isRealloc : String -> Bool
isRealloc n = n == "realloc"

mutual
  ||| True when this statement returns from the function on every path.
  public export
  stmtEnds : Stmt -> Bool
  stmtEnds (SReturn _ _) = True
  stmtEnds (SBlock _ b) = stmtsEnded b
  stmtEnds (SIf _ _ t e) = stmtsEnded t && stmtsEnded e
  stmtEnds _ = False

  ||| True when every execution of this list returns (a prefix `return`
  ||| ends the list; a trailing `return` after non-returning statements
  ||| also counts).
  public export
  stmtsEnded : List Stmt -> Bool
  stmtsEnded [] = False
  stmtsEnded (s :: ss) = stmtEnds s || stmtsEnded ss

public export
isReturnStmt : Stmt -> Bool
isReturnStmt (SReturn _ _) = True
isReturnStmt _ = False

joinConsume : Consume -> Consume -> Consume
joinConsume Never x = x
joinConsume May Never = May
joinConsume May _ = May
joinConsume Always Never = Always
joinConsume Always May = May
joinConsume Always Always = Always

||| Sequential composition: a must-consume on either side is Always.
seqConsume : Consume -> Consume -> Consume
seqConsume Always _ = Always
seqConsume Never rest = rest
seqConsume May Always = Always
seqConsume May _ = May

||| A loop body may run zero times, so Always inside a loop is only May.
loopWeaken : Consume -> Consume
loopWeaken Never = Never
loopWeaken _ = May

||| Modes of a callee during summarising. Unknown names are all-Never
||| (least fixpoint). Prototype `realloc` consumes its first argument.
export
calleeModes : List (String, List Consume) -> String -> List Consume
calleeModes acc callee =
  case lookupNamed acc callee of
    Nothing => if callee == "realloc" then [Always] else []
    Just ms => ms

||| `funModes` and `calleeModes` agree, except a missing summary for the
||| realloc name: `funModes` is `[]` and `calleeModes` is `[Always]`.
export
calleeModesFunModes : (ctx : Ctx) -> (n : String) ->
  Either (calleeModes ctx.summaries n = funModes ctx n)
         (funModes ctx n = [], calleeModes ctx.summaries n = [Always])
calleeModesFunModes ctx n = go (lookupNamed ctx.summaries n) Refl
  where
    modesJust : (ms : List Consume) ->
                lookupNamed ctx.summaries n = Just ms ->
                calleeModes ctx.summaries n = ms
    modesJust _ prf = rewrite prf in Refl
    listJust : (ms : List Consume) ->
               lookupNamed ctx.summaries n = Just ms ->
               funModes ctx n = ms
    listJust _ prf = rewrite prf in Refl
    go : (r : Maybe (List Consume)) -> lookupNamed ctx.summaries n = r ->
         Either (calleeModes ctx.summaries n = funModes ctx n)
                (funModes ctx n = [], calleeModes ctx.summaries n = [Always])
    go (Just ms) prf =
      Left (trans (modesJust ms prf) (sym (listJust ms prf)))
    go Nothing prf = missGo (n == "realloc") Refl
      where
        missGo : (b : Bool) -> n == "realloc" = b ->
                 Either (calleeModes ctx.summaries n = funModes ctx n)
                        (funModes ctx n = [], calleeModes ctx.summaries n = [Always])
        missGo True pb =
          Right (rewrite prf in Refl, rewrite prf in rewrite pb in Refl)
        missGo False pb =
          Left (trans (rewrite prf in rewrite pb in Refl)
                      (sym (rewrite prf in Refl)))

||| During summarising, a missing mode is Never (not yet known to consume).
sumHead : List Consume -> Consume
sumHead [] = Never
sumHead (m :: _) = m

asConsume : Bool -> Consume
asConsume True = Always
asConsume False = Never

mutual
  consumeInExpr : List (String, List Consume) -> Place -> Expr -> Consume
  consumeInExpr _ _ (EVar _ _ _) = Never
  consumeInExpr _ p (EAssign _ _ _ _ rhs) = asConsume (movedInExpr p rhs)
  consumeInExpr _ _ (EMalloc _ _) = Never
  consumeInExpr acc p (ECall _ callee args) = consumeInArgs acc p callee args
  consumeInExpr _ _ (EUse _ _) = Never
  consumeInExpr _ _ (ELit _) = Never
  consumeInExpr _ _ (ENull _) = Never
  consumeInExpr _ _ (EUnsupported _ _) = Never

  export
  consumeInArgs : List (String, List Consume) -> Place -> String -> List Expr -> Consume
  consumeInArgs acc p callee args = consumeInArgsGo p args (calleeModes acc callee)

  consumeInArgsGo : Place -> List Expr -> List Consume -> Consume
  consumeInArgsGo _ [] _ = Never
  consumeInArgsGo p (e :: es) modes =
    let here = if doesConsume (sumHead modes) && movedInExpr p e then Always else Never
    in seqConsume here (consumeInArgsGo p es (consumeTail modes))

  consumeInStmt : List (String, List Consume) -> Place -> Stmt -> Consume
  consumeInStmt acc p (SBlock _ body) = consumeInStmts acc p body
  consumeInStmt _ p (SDecl _ _ _ _ (Just e)) = asConsume (movedInExpr p e)
  consumeInStmt _ _ (SDecl _ _ _ _ Nothing) = Never
  consumeInStmt _ p (SAssign _ _ _ _ e) = asConsume (movedInExpr p e)
  consumeInStmt _ p (SDrop _ q _) = if p == q then Always else Never
  consumeInStmt acc p (SCall _ callee args) = consumeInArgs acc p callee args
  consumeInStmt acc p (SReturn _ (Just e)) =
    seqConsume (asConsume (movedInExpr p e)) (consumeInExpr acc p e)
  consumeInStmt _ _ (SReturn _ Nothing) = Never
  consumeInStmt acc p (SIf _ cond t e) =
    seqConsume (consumeInExpr acc p cond)
      (joinConsume (consumeInStmts acc p t) (consumeInStmts acc p e))
  consumeInStmt acc p (SLoop _ body) = loopWeaken (consumeInStmts acc p body)
  consumeInStmt acc p (SExpr _ e) = consumeInExpr acc p e
  consumeInStmt _ _ (SUnsupported _ _) = Never

  consumeInStmts : List (String, List Consume) -> Place -> List Stmt -> Consume
  consumeInStmts _ _ [] = Never
  consumeInStmts acc p (s :: ss) =
    if stmtEnds s
      then consumeInStmt acc p s
      else seqConsume (consumeInStmt acc p s) (consumeInStmts acc p ss)

paramModes : List (String, List Consume) -> Fun -> List Consume
paramModes acc f =
  map (\p => if p.ty == Copy then Never else consumeInStmts acc p.place f.body) f.params

eqConsumes : List Consume -> List Consume -> Bool
eqConsumes [] [] = True
eqConsumes (x :: xs) (y :: ys) = x == y && eqConsumes xs ys
eqConsumes _ _ = False

eqNamedModes : List (String, List Consume) -> List (String, List Consume) -> Bool
eqNamedModes [] [] = True
eqNamedModes ((n, ms) :: xs) ((n2, ms2) :: ys) =
  n == n2 && eqConsumes ms ms2 && eqNamedModes xs ys
eqNamedModes _ _ = False

joinModes : List Consume -> List Consume -> List Consume
joinModes [] ys = ys
joinModes xs [] = xs
joinModes (x :: xs) (y :: ys) = joinConsume x y :: joinModes xs ys

||| Least fixpoint of per-parameter consume modes over defined functions.
summarise : Nat -> List Fun -> List (String, List Consume) -> List (String, List Consume)
summarise Z _ acc = acc
summarise (S k) funs acc =
  let defs = filter (\f => f.defined) funs
      next = map (\f => (f.name, joinModes (lookupNamedList acc f.name) (paramModes acc f))) defs
  in if eqNamedModes next acc then acc else summarise k funs next

||| Destinations a borrow assignment still holds. The rhs place is not
||| included: the assignment moves it, and a later use is use-after-move.
public export
nestAssigns : Expr -> List Place
nestAssigns (EAssign _ p _ Ptr rhs) =
  let rest = nestAssigns rhs in
  if maybeLivePtr rhs then p :: rest else rest
nestAssigns _ = []

||| Place a borrow argument still denotes: the variable, or the
||| destinations of a pointer assignment (`f(q = malloc(), …)`).
public export
nestPlace : Expr -> List Place
nestPlace (EVar _ p _) = [p]
nestPlace (EAssign _ p _ Ptr rhs) =
  let rest = nestAssigns rhs in
  if maybeLivePtr rhs then p :: rest else rest
-- Copy assignment uses the rhs; it does not move it. `valuePlaces`
-- still denote that source, so `f(x = p, g(p))` is `nestedMixed`.
nestPlace (EAssign _ _ _ Copy rhs) = valuePlaces rhs
nestPlace _ = []

||| Borrow-argument places for `nestedMixed`. Extras are consumes.
public export
nestBorrowPlaces : List Expr -> List Consume -> List Place
nestBorrowPlaces [] _ = []
nestBorrowPlaces (_ :: es) [] = nestBorrowPlaces es []
nestBorrowPlaces (e :: es) (m :: ms) =
  if doesConsume m
    then nestBorrowPlaces es ms
    else nestPlace e ++ nestBorrowPlaces es ms

mutual
  ||| True when evaluating `e` can free `p`, including a consume nested
  ||| under a Never-mode call (`f(p, h(g(p)))` where `h` does not consume).
  export
  argFrees : List (String, List Consume) -> Place -> Expr -> Bool
  argFrees acc p (ECall _ callee args) =
    doesConsume (consumeInArgs acc p callee args) || argsFree acc p args
  argFrees acc p (EMalloc _ args) = argsFree acc p args
  argFrees acc p (EUse _ args) = argsFree acc p args
  argFrees acc p (EAssign _ _ _ _ rhs) = argFrees acc p rhs
  argFrees _ _ _ = False

  export
  argsFree : List (String, List Consume) -> Place -> List Expr -> Bool
  argsFree _ _ [] = False
  argsFree acc p (e :: es) = argFrees acc p e || argsFree acc p es

||| `argFrees` of one place across an argument list.
export
argsHit : List (String, List Consume) -> Place -> List Expr -> Bool
argsHit _ _ [] = False
argsHit acc p (e :: rest) = argFrees acc p e || argsHit acc p rest

||| Any borrow place freed by any argument.
export
nestedGo : List (String, List Consume) -> List Place -> List Expr -> Bool
nestedGo _ [] _ = False
nestedGo acc (p :: ps) es0 = argsHit acc p es0 || nestedGo acc ps es0

||| Nested consume of a borrow-argument place (e.g. `f(p, g(p))` where `g`
||| consumes `p`, or `f(q = malloc(), g(q))`). Direct Never+May/Always of
||| the same `EVar` is `mixedAlias`. A freeing call under a Never wrapper
||| (`f(p, h(g(p)))`) counts too.
export
nestedMixed : Ctx -> List Expr -> List Consume -> Bool
nestedMixed ctx es ms = nestedGo ctx.summaries (nestBorrowPlaces es ms) es

||| `nestedMixed` is `export`, so other modules transport through this.
export
nestedMixedEq : {ctx : Ctx} -> {es : List Expr} -> {ms : List Consume} ->
  nestedMixed ctx es ms = nestedGo ctx.summaries (nestBorrowPlaces es ms) es
nestedMixedEq = Refl

||| True when the call aliases a borrow with a consume, including nested
||| callees in later arguments and a pointer assignment used as a borrow.
public export
aliasBad : Ctx -> List Expr -> String -> Bool
aliasBad ctx args callee =
  mixedAlias args (funModes ctx callee)
    || nestedMixed ctx args (funModes ctx callee)
    || assignAlias args (funModes ctx callee)

public export
paramStatus : Consume -> Nat -> Status
paramStatus Never fid = Pagurus.Status.singleton (ABorrowed fid)
paramStatus May _ = Pagurus.Status.singleton AOwned
paramStatus Always _ = Pagurus.Status.singleton AOwned

export
paramStatusNever : (fid : Nat) ->
  paramStatus Never fid = Pagurus.Status.singleton (ABorrowed fid)
paramStatusNever _ = Refl

export
paramStatusMay : (fid : Nat) ->
  paramStatus May fid = Pagurus.Status.singleton AOwned
paramStatusMay _ = Refl

export
paramStatusAlways : (fid : Nat) ->
  paramStatus Always fid = Pagurus.Status.singleton AOwned
paramStatusAlways _ = Refl

public export
bindParams : Nat -> List Param -> List Consume -> Env
bindParams _ [] _ = []
bindParams fid (p :: ps) [] =
  case p.ty of
    Ptr => (p.place, Pagurus.Status.singleton (ABorrowed fid)) :: bindParams fid ps []
    Copy => bindParams fid ps []
bindParams fid (p :: ps) (m :: ms) =
  case p.ty of
    Ptr => (p.place, paramStatus m fid) :: bindParams fid ps ms
    Copy => bindParams fid ps ms

||| Starting abstract environment of a function: one status per pointer
||| parameter, from that parameter's `Consume` mode (`funModes`). Copy
||| parameters are omitted. Per-argument Never/May/Always (#6) slots in
||| here: `paramScopes` already takes `List Consume`, not a function-level Bool.
export
paramScopes : Ctx -> Fun -> Scopes
paramScopes ctx f = bindParams f.id f.params (funModes ctx f.name)

||| Whether `takeOwner` produced a unique owner (`Owner`), a known null
||| (`Null`, only from `ENull`: `0` / `NULL` / `(void*)0`), or another
||| non-owner (`Ghost`, including `ELit`). `Ghost` must not be treated as
||| null: a non-null integer/string literal, or a non-consuming call that
||| happens to return a heap pointer, would otherwise make `free` a no-op
||| and hide a double free.
public export
data Flag = Owner | Ghost | Null

export
withName : String -> Diag -> Diag
withName n d =
  case d.kind of
    KUseAfterMove => { message := "use of moved value `" ++ n ++ "`" } d
    KDoubleFree => { message := "double free of `" ++ n ++ "`" } d
    KUseAfterFree => { message := "use of freed value `" ++ n ++ "`" } d
    _ => { message := d.message ++ " `" ++ n ++ "`" } d

exprArgName : Expr -> String
exprArgName (EVar _ _ nm) = nm
exprArgName (EAssign _ _ nm _ _) = nm
exprArgName _ = "this argument"

||| Rewrite a failed consuming-argument diagnostic so it names the callee
||| and the argument.
public export
nameConsumedArg : String -> Expr -> Diag -> Diag
nameConsumedArg callee e d =
  let nm = exprArgName e in
    { help :=
        "argument `" ++ nm ++ "` is consumed by `" ++ callee ++
        "` (always, or on some path); the caller must not use it afterwards"
    } d

public export
mapDiscardFlag : Either Diag (Scopes, Flag) -> Either Diag Scopes
mapDiscardFlag (Left d) = Left d
mapDiscardFlag (Right (sc, _)) = Right sc

||| Copy-assignment, literals, and non-realloc calls are `Ghost`: they do
||| not transfer unique ownership. Passing them as May/Always (or extra
||| Always) would leave the source use-safe while BindOk unique-owns the
||| address — leftover unique-owner-of-Freed. Null is allowed (`free(NULL)`).
public export
ghostNotOwner : Expr -> Diag
ghostNotOwner e =
  MkDiag KUnproven
    "cannot prove unique ownership of this argument"
    (exprId e) "consumed here"
    []
    "a consuming argument must be a unique owner or null; copy-assignment, literals, and non-realloc calls do not transfer ownership"

||| Consume-mode take: keep Owner and Null, reject Ghost.
public export
consumeTake : Expr -> Either Diag (Scopes, Flag) -> Either Diag Scopes
consumeTake _ (Left d) = Left d
consumeTake _ (Right (sc, Owner)) = Right sc
consumeTake _ (Right (sc, Null)) = Right sc
consumeTake e (Right (_, Ghost)) = Left (ghostNotOwner e)

public export
usePlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
usePlace sc n nid nm =
  case lookupPlace n sc of
    Nothing => Right sc
    Just st =>
      case stepStatus st Use nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

public export
movePlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
movePlace sc n nid nm =
  case lookupPlace n sc of
    Nothing =>
      Left (MkDiag KUnproven
        ("cannot prove unique ownership of `" ++ nm ++ "`")
        nid "moved here"
        []
        "this name is not a tracked unique pointer in the current scope")
    Just st =>
      case stepStatus st Move nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

public export
dropPlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
dropPlace sc n nid nm =
  case lookupPlace n sc of
    Nothing =>
      Left (MkDiag KUnproven
        ("cannot prove `" ++ nm ++ "` is a unique owner")
        nid "freed here"
        []
        "pagurus cannot track unique ownership through a call, cast, or integer conversion; this may be a double free")
    Just st =>
      case stepStatus st Drop nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

unsupported : Nat -> String -> Diag
unsupported id reason =
  MkDiag KUnsupported
    ("unsupported construct: " ++ reason)
    id "unsupported here"
    []
    "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"

||| First-order eliminators so Safety can `rewrite` a result equality
||| without Idris 0.8.0 inserting a quantity-0 `let` around `case`.
public export
mapToGhost : Either Diag Scopes -> Either Diag (Scopes, Flag)
mapToGhost (Left d) = Left d
mapToGhost (Right sc') = Right (sc', Ghost)

public export
mapToOwner : Either Diag Scopes -> Either Diag (Scopes, Flag)
mapToOwner (Left d) = Left d
mapToOwner (Right sc') = Right (sc', Owner)

public export
takeVarFrom : Scopes -> Nat -> Place -> String -> Maybe Status -> Either Diag (Scopes, Flag)
takeVarFrom sc _ _ _ Nothing = Right (sc, Ghost)
takeVarFrom sc nid n nm (Just _) = mapToOwner (movePlace sc n nid nm)

public export
takeAssignPtrFrom : Nat -> Place -> String -> Either Diag (Scopes, Flag) -> Either Diag (Scopes, Flag)
takeAssignPtrFrom _ _ _ (Left d) = Left d
takeAssignPtrFrom id n nm (Right (sc', Owner)) =
  mapToOwner (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc') n id nm)
takeAssignPtrFrom _ n _ (Right (sc', Ghost)) =
  Right (setPlace n (Pagurus.Status.singleton AEmpty) sc', Ghost)
takeAssignPtrFrom _ n _ (Right (sc', Null)) =
  Right (setPlace n (Pagurus.Status.singleton ANull) sc', Null)

public export
assignPtrFrom : Bool -> Nat -> Place -> String -> Either Diag (Scopes, Flag) -> Either Diag Scopes
assignPtrFrom _ _ _ _ (Left d) = Left d
assignPtrFrom asMove id n nm (Right (sc', Owner)) =
  if asMove
    then movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc') n id nm
    else usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc') n id nm
assignPtrFrom _ _ n _ (Right (sc', Ghost)) =
  Right (setPlace n (Pagurus.Status.singleton AEmpty) sc')
assignPtrFrom _ _ n _ (Right (sc', Null)) =
  Right (setPlace n (Pagurus.Status.singleton ANull) sc')

public export
declPtrFrom : Nat -> Place -> String -> Either Diag (Scopes, Flag) -> Either Diag Scopes
declPtrFrom _ _ _ (Left d) = Left d
declPtrFrom _ n _ (Right (sc', Owner)) =
  Right (declarePlace n (Pagurus.Status.singleton AOwned) sc')
declPtrFrom _ n _ (Right (sc', Ghost)) =
  Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc')
declPtrFrom _ n _ (Right (sc', Null)) =
  Right (declarePlace n (Pagurus.Status.singleton ANull) sc')

public export
stmtAsgPtrFrom : Place -> Either Diag (Scopes, Flag) -> Either Diag Scopes
stmtAsgPtrFrom _ (Left d) = Left d
stmtAsgPtrFrom n (Right (sc', Owner)) =
  Right (setPlace n (Pagurus.Status.singleton AOwned) sc')
stmtAsgPtrFrom n (Right (sc', Ghost)) =
  Right (setPlace n (Pagurus.Status.singleton AEmpty) sc')
stmtAsgPtrFrom n (Right (sc', Null)) =
  Right (setPlace n (Pagurus.Status.singleton ANull) sc')

public export
retVarFrom : Either Diag (Scopes, Flag) -> Either Diag Scopes
retVarFrom (Left d) = Left d
retVarFrom (Right (sc', _)) = Right sc'

public export
ifJoin : Scopes -> Either Diag Scopes -> Either Diag Scopes
ifJoin _ (Left d) = Left d
ifJoin scT (Right scE) = Right (joinScopes scT scE)

||| Join if-branches, dropping a path that always returns so it does not
||| poison the continuation.
public export
ifJoinFrom : Bool -> Bool -> Scopes -> Either Diag Scopes -> Either Diag Scopes
ifJoinFrom _ _ _ (Left d) = Left d
ifJoinFrom True True _ (Right _) = Right []
ifJoinFrom True False _ (Right scE) = Right scE
ifJoinFrom False True scT (Right _) = Right scT
ifJoinFrom False False scT (Right scE) = Right (joinScopes scT scE)

-- Checker functions are `export` (opaque outside this module) so proof
-- modules cannot unfold them. Use the unfold lemmas below; first-order
-- eliminators stay `public export` for `rewrite`.
mutual
  export
  checkExpr : Ctx -> Scopes -> Expr -> Either Diag Scopes
  checkExpr ctx sc (ELit _) = Right sc
  checkExpr ctx sc (ENull _) = Right sc
  checkExpr ctx sc (EMalloc _ args) = checkArgsBorrow ctx sc args
  checkExpr ctx sc (EVar id n nm) = usePlace sc n id nm
  checkExpr ctx sc (ECall id callee args) = checkCall ctx sc id callee args
  checkExpr ctx sc (EAssign id n nm ty rhs) = assignPlace ctx sc id n nm ty rhs False
  checkExpr ctx sc (EUse _ args) = checkArgsBorrow ctx sc args
  checkExpr _ _ (EUnsupported id reason) = Left (unsupported id reason)

  ||| Evaluate an expression as a unique-owner rvalue.
  export
  takeOwner : Ctx -> Scopes -> Expr -> Either Diag (Scopes, Flag)
  takeOwner ctx sc (EMalloc _ args) = mapToOwner (checkArgsBorrow ctx sc args)
  -- Non-null literals are not owners (Ghost → AEmpty on store).
  takeOwner _ sc (ELit _) = Right (sc, Ghost)
  -- Only the null pointer constant is `ANull`.
  takeOwner _ sc (ENull _) = Right (sc, Null)
  takeOwner _ sc (EVar id n nm) = takeVarFrom sc id n nm (lookupPlace n sc)
  takeOwner ctx sc (EAssign id n nm ty rhs) =
    case ty of
      Copy => mapToGhost (checkExpr ctx sc rhs)
      Ptr => takeAssignPtrFrom id n nm (takeOwner ctx sc rhs)
  takeOwner ctx sc (ECall id callee args) =
    reallocOwner (isRealloc callee && not (isDefined ctx callee))
      (checkCall ctx sc id callee args)
  takeOwner ctx sc e = mapToGhost (checkExpr ctx sc e)

  ||| Store into `n`. If `asMove` then yield the stored owner (assignment rvalue).
  export
  assignPlace : Ctx -> Scopes -> Nat -> Place -> String -> Ty -> Expr -> Bool -> Either Diag Scopes
  assignPlace ctx sc id n nm ty rhs asMove =
    case ty of
      Copy => checkExpr ctx sc rhs
      Ptr => assignPtrFrom asMove id n nm (takeOwner ctx sc rhs)

  public export
  argsBorrowFrom : Ctx -> List Expr -> Either Diag Scopes -> Either Diag Scopes
  argsBorrowFrom _ _ (Left d) = Left d
  argsBorrowFrom ctx es (Right sc') = checkArgsBorrow ctx sc' es

  export
  checkArgsBorrow : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkArgsBorrow _ sc [] = Right sc
  checkArgsBorrow ctx sc (e :: es) = argsBorrowFrom ctx es (checkExpr ctx sc e)

  public export
  argsMoveFrom : Ctx -> List Expr -> Either Diag (Scopes, Flag) -> Either Diag Scopes
  argsMoveFrom _ _ (Left d) = Left d
  argsMoveFrom ctx es (Right (sc', _)) = checkArgsMove ctx sc' es

  export
  checkArgsMove : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkArgsMove _ sc [] = Right sc
  checkArgsMove ctx sc (e :: es) = argsMoveFrom ctx es (takeOwner ctx sc e)

  public export
  argAction : Bool -> Ctx -> Scopes -> Expr -> Either Diag Scopes
  argAction False ctx sc e = checkExpr ctx sc e
  argAction True ctx sc e = consumeTake e (takeOwner ctx sc e)

  public export
  argsModesFrom : Bool -> String -> Expr -> Ctx -> List Expr -> List Consume ->
                  Either Diag Scopes -> Either Diag Scopes
  argsModesFrom True callee e _ _ _ (Left d) = Left (nameConsumedArg callee e d)
  argsModesFrom False _ _ _ _ _ (Left d) = Left d
  argsModesFrom _ callee _ ctx es ms (Right sc') = checkArgsModes ctx sc' callee es ms

  export
  checkArgsModes : Ctx -> Scopes -> String -> List Expr -> List Consume -> Either Diag Scopes
  checkArgsModes _ sc _ [] _ = Right sc
  checkArgsModes ctx sc callee (e :: es) modes =
    argsModesFrom (doesConsume (consumeHead modes)) callee e ctx es (consumeTail modes)
      (argAction (doesConsume (consumeHead modes)) ctx sc e)

  public export
  reallocOwner : Bool -> Either Diag Scopes -> Either Diag (Scopes, Flag)
  reallocOwner True r = mapToOwner r
  reallocOwner False r = mapToGhost r

  public export
  reallocTail : Ctx -> List Expr -> Either Diag (Scopes, Flag) -> Either Diag Scopes
  reallocTail _ _ (Left d) = Left d
  reallocTail ctx es (Right (sc', _)) = checkArgsBorrow ctx sc' es

  export
  checkRealloc : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkRealloc _ sc [] = Right sc
  checkRealloc ctx sc (e :: es) = reallocTail ctx es (takeOwner ctx sc e)

  public export
  definedCallFrom : Bool -> Ctx -> Scopes -> Nat -> String -> List Expr -> List Consume -> Either Diag Scopes
  definedCallFrom True _ _ nid callee args modes =
    Left (mixedAliasDiag nid callee (mixedAliasArg args modes))
  definedCallFrom False ctx sc _ callee args modes =
    checkArgsModes ctx sc callee args modes

  export
  checkCall : Ctx -> Scopes -> Nat -> String -> List Expr -> Either Diag Scopes
  checkCall ctx sc id callee args =
    if isBuiltin callee
      then checkArgsBorrow ctx sc args
      else if isDefined ctx callee
        then definedCallFrom (aliasBad ctx args callee) ctx sc id callee args (funModes ctx callee)
        else if isRealloc callee
          then checkRealloc ctx sc args
          else Left (MkDiag KUnsupported
            ("unsupported call to `" ++ callee ++ "`: no function body, so pagurus cannot prove the call is safe")
            id "called here"
            []
            "provide a definition in this translation unit, or avoid passing unique pointers to opaque functions")

  export
  checkStmt : Nat -> Ctx -> Scopes -> Stmt -> Either Diag Scopes
  checkStmt Z _ _ s =
    Left (MkDiag KUnproven
      "analysis fuel exhausted"
      (stmtId s) "here"
      []
      "this is an internal limitation; simplify control flow")
  checkStmt (S fuel) ctx sc (SBlock _ body) =
    checkStmts fuel ctx sc body
  checkStmt (S fuel) ctx sc (SDecl id n nm ty init) =
    case ty of
      Copy =>
        case init of
          Nothing => Right sc
          Just e => checkExpr ctx sc e
      Ptr =>
        case init of
          Nothing => Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc)
          Just e => declPtrFrom id n nm (takeOwner ctx sc e)
  checkStmt (S fuel) ctx sc (SAssign id n nm ty rhs) =
    case ty of
      Copy => checkExpr ctx sc rhs
      Ptr => stmtAsgPtrFrom n (takeOwner ctx sc rhs)
  checkStmt (S fuel) ctx sc (SDrop id n nm) = dropPlace sc n id nm
  checkStmt (S fuel) ctx sc (SCall id callee args) = checkCall ctx sc id callee args
  checkStmt (S fuel) ctx sc (SReturn id (Just e)) =
    case e of
      EVar nid n nm => retVarFrom (takeOwner ctx sc e)
      _ => checkExpr ctx sc e
  checkStmt (S fuel) _ sc (SReturn _ Nothing) = Right sc
  checkStmt (S fuel) ctx sc (SIf _ cond thn els) =
    ifFromCond fuel ctx thn els (checkExpr ctx sc cond)
  checkStmt (S fuel) ctx sc (SLoop id body) = loopFix fuel ctx sc id body
  checkStmt (S fuel) ctx sc (SExpr _ e) = checkExpr ctx sc e
  checkStmt (S fuel) _ _ (SUnsupported id reason) = Left (unsupported id reason)

  public export
  ifFromThn : Nat -> Ctx -> Scopes -> List Stmt -> List Stmt -> Either Diag Scopes -> Either Diag Scopes
  ifFromThn _ _ _ _ _ (Left d) = Left d
  ifFromThn fuel ctx sc0 thn els (Right scT) =
    ifJoinFrom (stmtsEnded thn) (stmtsEnded els) scT (checkStmts fuel ctx sc0 els)

  public export
  ifFromCond : Nat -> Ctx -> List Stmt -> List Stmt -> Either Diag Scopes -> Either Diag Scopes
  ifFromCond _ _ _ _ (Left d) = Left d
  ifFromCond fuel ctx thn els (Right sc0) =
    ifFromThn fuel ctx sc0 thn els (checkStmts fuel ctx sc0 thn)

  export
  checkStmts : Nat -> Ctx -> Scopes -> List Stmt -> Either Diag Scopes
  checkStmts Z _ _ (s :: _) =
    Left (MkDiag KUnproven "analysis fuel exhausted" (stmtId s) "here" []
      "this is an internal limitation; simplify control flow")
  checkStmts _ _ sc [] = Right sc
  checkStmts (S fuel) ctx sc (s :: ss) =
    stmtsConsFrom fuel ctx s ss (checkStmt fuel ctx sc s)

  public export
  stmtsConsFrom : Nat -> Ctx -> Stmt -> List Stmt -> Either Diag Scopes -> Either Diag Scopes
  stmtsConsFrom _ _ _ _ (Left d) = Left d
  stmtsConsFrom fuel ctx s ss (Right sc') =
    if isReturnStmt s then Right sc' else checkStmts fuel ctx sc' ss

  export
  loopFix : Nat -> Ctx -> Scopes -> Nat -> List Stmt -> Either Diag Scopes
  loopFix Z _ _ id _ =
    Left (MkDiag KUnproven
      "loop fixpoint fuel exhausted"
      id "loop here"
      []
      "the ownership lattice did not stabilise; simplify the loop")
  loopFix (S fuel) ctx sc id body =
    loopFixFrom fuel ctx sc id body (checkStmts fuel ctx sc body)

  public export
  loopFixEnded : Bool -> Nat -> Ctx -> Scopes -> Nat -> List Stmt -> Scopes -> Either Diag Scopes
  loopFixEnded True _ _ sc _ _ _ = Right sc
  loopFixEnded False fuel ctx sc id body sc' =
    if eqScopes (joinScopes sc sc') sc
      then Right (joinScopes sc sc')
      else loopFix fuel ctx (joinScopes sc sc') id body

  public export
  loopFixFrom : Nat -> Ctx -> Scopes -> Nat -> List Stmt -> Either Diag Scopes -> Either Diag Scopes
  loopFixFrom _ _ _ _ _ (Left d) = Left d
  loopFixFrom fuel ctx sc id body (Right sc') =
    loopFixEnded (stmtsEnded body) fuel ctx sc id body sc'

export
checkFun : Nat -> Ctx -> Fun -> Either Diag ()
checkFun fuel ctx f =
  if not f.defined then Right ()
  else case checkStmts fuel ctx (paramScopes ctx f) f.body of
         Left d => Left d
         Right _ => Right ()

export
definedNames : List Fun -> List String
definedNames funs = map (\f => f.name) (filter (\f => f.defined) funs)

export
definedNamesConsTrue :
  (g : Fun) -> (gs : List Fun) ->
  g.defined = True ->
  definedNames (g :: gs) = g.name :: definedNames gs
definedNamesConsTrue g gs pd = rewrite pd in Refl

export
definedNamesConsFalse :
  (g : Fun) -> (gs : List Fun) ->
  g.defined = False ->
  definedNames (g :: gs) = definedNames gs
definedNamesConsFalse g gs pd = rewrite pd in Refl

export
mkProgCtx : List Fun -> Ctx
mkProgCtx funs = MkCtx (summarise 32 funs []) (definedNames funs)

export
mkProgCtxEq : (funs : List Fun) ->
  mkProgCtx funs = MkCtx (summarise 32 funs []) (definedNames funs)
mkProgCtxEq _ = Refl

public export
checkFunsFrom : Nat -> Ctx -> List Fun -> Either Diag ()
checkFunsFrom _ _ [] = Right ()
checkFunsFrom fuel ctx (f :: fs) =
  case checkFun fuel ctx f of
    Left d => Left d
    Right () => checkFunsFrom fuel ctx fs

export
checkProgram : Program -> Either Diag ()
checkProgram (MkProgram funs) = checkFunsFrom 2048 (mkProgCtx funs) funs

export
checkProgramEq : (funs : List Fun) ->
  checkProgram (MkProgram funs) = checkFunsFrom 2048 (mkProgCtx funs) funs
checkProgramEq _ = Refl

export
checkFunUndef :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = False ->
  checkFun fuel ctx f = Right ()
checkFunUndef prf = rewrite prf in Refl

export
checkFunDefLeft :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} -> {d : Diag} ->
  f.defined = True ->
  checkStmts fuel ctx (paramScopes ctx f) f.body = Left d ->
  checkFun fuel ctx f = Left d
checkFunDefLeft prf pB = rewrite prf in rewrite pB in Refl

export
checkFunDefRight :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} -> {sc' : Scopes} ->
  f.defined = True ->
  checkStmts fuel ctx (paramScopes ctx f) f.body = Right sc' ->
  checkFun fuel ctx f = Right ()
checkFunDefRight prf pB = rewrite prf in rewrite pB in Refl

export
checkFunDefCase :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = True ->
  checkFun fuel ctx f =
    case checkStmts fuel ctx (paramScopes ctx f) f.body of
      Left d => Left d
      Right _ => Right ()
checkFunDefCase prf = rewrite prf in Refl

export
paramScopesEq : (ctx : Ctx) -> (f : Fun) ->
  paramScopes ctx f = bindParams f.id f.params (funModes ctx f.name)
paramScopesEq _ _ = Refl

export
paramScopesNil : (ctx : Ctx) -> (f : Fun) ->
  f.params = [] ->
  paramScopes ctx f = []
paramScopesNil ctx f prf = rewrite prf in Refl

export
bindParamsNil : (fid : Nat) -> (ms : List Consume) -> bindParams fid [] ms = []
bindParamsNil _ _ = Refl

export
borrowPlacesNilModes : (es : List Expr) -> borrowPlaces es [] = []
borrowPlacesNilModes [] = Refl
borrowPlacesNilModes (_ :: es) = borrowPlacesNilModes es

export
mixedAliasNilModes : (es : List Expr) -> mixedAlias es [] = False
mixedAliasNilModes es = rewrite borrowPlacesNilModes es in Refl

export
nestBorrowNil : (es : List Expr) -> nestBorrowPlaces es [] = []
nestBorrowNil [] = Refl
nestBorrowNil (_ :: es) = nestBorrowNil es

export
nestedMixedNilModes : (ctx : Ctx) -> (es : List Expr) -> nestedMixed ctx es [] = False
nestedMixedNilModes ctx es = rewrite nestBorrowNil es in Refl

export
aliasBorrowNil : (es : List Expr) -> aliasBorrowPlaces es [] = []
aliasBorrowNil [] = Refl
aliasBorrowNil (_ :: es) = aliasBorrowNil es

export
assignAliasNilModes : (es : List Expr) -> assignAlias es [] = False
assignAliasNilModes es = rewrite aliasBorrowNil es in Refl

export
aliasBadNilModes :
  {ctx : Ctx} -> {callee : String} -> {args : List Expr} ->
  funModes ctx callee = [] ->
  aliasBad ctx args callee = False
aliasBadNilModes {ctx} {callee} {args} prf =
  rewrite prf in
    rewrite mixedAliasNilModes args in
      rewrite nestedMixedNilModes ctx args in
        rewrite assignAliasNilModes args in Refl

trueNotFalseC : Not (True = False)
trueNotFalseC Refl impossible

orFalseC : (x, y : Bool) -> x || y = False -> (x = False, y = False)
orFalseC False False Refl = (Refl, Refl)
orFalseC True _ prf = void (trueNotFalseC prf)

orFalseIntro : {x, y : Bool} -> x = False -> y = False -> x || y = False
orFalseIntro Refl Refl = Refl

placeInAppendR : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p ys = False
placeInAppendR {xs = []} prf = prf
placeInAppendR {xs = _ :: qs} prf =
  let (_, rest) = orFalseC _ _ prf
  in placeInAppendR {xs = qs} rest

placesOverlapAppendL : {xs, ys, zs : List Place} ->
  placesOverlap (xs ++ ys) zs = False -> placesOverlap ys zs = False
placesOverlapAppendL {xs = []} prf = prf
placesOverlapAppendL {xs = _ :: ps} prf =
  let (_, rest) = orFalseC _ _ prf
  in placesOverlapAppendL {xs = ps} rest

placesOverlapAppendR : {xs, ys, zs : List Place} ->
  placesOverlap xs (ys ++ zs) = False -> placesOverlap xs zs = False
placesOverlapAppendR {xs = []} _ = Refl
placesOverlapAppendR {xs = _ :: ps} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (placeInAppendR {xs = ys} hd) (placesOverlapAppendR {xs = ps} tl)

export
nestBorrowBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  nestBorrowPlaces (e :: es) (m :: ms) = nestPlace e ++ nestBorrowPlaces es ms
nestBorrowBorrow {m = Never} _ = Refl
nestBorrowBorrow {m = May} prf = void (trueNotFalseC prf)
nestBorrowBorrow {m = Always} prf = void (trueNotFalseC prf)

nestBorrowConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  nestBorrowPlaces (e :: es) (m :: ms) = nestBorrowPlaces es ms
nestBorrowConsume {m = Never} prf = void (trueNotFalseC (sym prf))
nestBorrowConsume {m = May} _ = Refl
nestBorrowConsume {m = Always} _ = Refl

aliasBorrowBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  aliasBorrowPlaces (e :: es) (m :: ms) = valuePlaces e ++ aliasBorrowPlaces es ms
aliasBorrowBorrow {m = Never} _ = Refl
aliasBorrowBorrow {m = May} prf = void (trueNotFalseC prf)
aliasBorrowBorrow {m = Always} prf = void (trueNotFalseC prf)

aliasBorrowConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  aliasBorrowPlaces (e :: es) (m :: ms) = aliasBorrowPlaces es ms
aliasBorrowConsume {m = Never} prf = void (trueNotFalseC (sym prf))
aliasBorrowConsume {m = May} _ = Refl
aliasBorrowConsume {m = Always} _ = Refl

aliasConsumeBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  aliasConsumePlaces (e :: es) (m :: ms) = aliasConsumePlaces es ms
aliasConsumeBorrow {m = Never} _ = Refl
aliasConsumeBorrow {m = May} prf = void (trueNotFalseC prf)
aliasConsumeBorrow {m = Always} prf = void (trueNotFalseC prf)

aliasConsumeConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  aliasConsumePlaces (e :: es) (m :: ms) = valuePlaces e ++ aliasConsumePlaces es ms
aliasConsumeConsume {m = Never} prf = void (trueNotFalseC (sym prf))
aliasConsumeConsume {m = May} _ = Refl
aliasConsumeConsume {m = Always} _ = Refl

consumePlacesBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  consumePlaces (e :: es) (m :: ms) = consumePlaces es ms
consumePlacesBorrow {m = Never} _ = Refl
consumePlacesBorrow {m = May} prf = void (trueNotFalseC prf)
consumePlacesBorrow {m = Always} prf = void (trueNotFalseC prf)

consumePlacesConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  consumePlaces (e :: es) (m :: ms) =
    case argVarPlace e of
      Just p => p :: consumePlaces es ms
      Nothing => consumePlaces es ms
consumePlacesConsume {m = Never} prf = void (trueNotFalseC (sym prf))
consumePlacesConsume {m = May} _ with (argVarPlace e)
  consumePlacesConsume _ | Just _ = Refl
  consumePlacesConsume _ | Nothing = Refl
consumePlacesConsume {m = Always} _ with (argVarPlace e)
  consumePlacesConsume _ | Just _ = Refl
  consumePlacesConsume _ | Nothing = Refl

borrowPlacesBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  borrowPlaces (e :: es) (m :: ms) =
    case argVarPlace e of
      Just p => p :: borrowPlaces es ms
      Nothing => borrowPlaces es ms
borrowPlacesBorrow {m = Never} _ with (argVarPlace e)
  borrowPlacesBorrow _ | Just _ = Refl
  borrowPlacesBorrow _ | Nothing = Refl
borrowPlacesBorrow {m = May} prf = void (trueNotFalseC prf)
borrowPlacesBorrow {m = Always} prf = void (trueNotFalseC prf)

borrowPlacesConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  borrowPlaces (e :: es) (m :: ms) = borrowPlaces es ms
borrowPlacesConsume {m = Never} prf = void (trueNotFalseC (sym prf))
borrowPlacesConsume {m = May} _ = Refl
borrowPlacesConsume {m = Always} _ = Refl

export
argsHitTail : {acc : List (String, List Consume)} -> {p : Place} ->
  {e : Expr} -> {es : List Expr} ->
  argsHit acc p (e :: es) = False -> argsHit acc p es = False
argsHitTail prf = snd (orFalseC _ _ prf)

nestedGoPlacesAppend : {acc : List (String, List Consume)} -> {xs, ys : List Place} ->
  {es : List Expr} ->
  nestedGo acc (xs ++ ys) es = False -> nestedGo acc ys es = False
nestedGoPlacesAppend {xs = []} prf = prf
nestedGoPlacesAppend {xs = _ :: ps} prf =
  let (_, rest) = orFalseC _ _ prf
  in nestedGoPlacesAppend {xs = ps} rest

||| Head places of a `nestedGo` over a concatenation stay quiet when the
||| whole concatenation is quiet. Dual of `nestedGoPlacesAppend`.
export
nestedGoPlacesHead : {acc : List (String, List Consume)} -> {xs, ys : List Place} ->
  {es : List Expr} ->
  nestedGo acc (xs ++ ys) es = False -> nestedGo acc xs es = False
nestedGoPlacesHead {xs = []} _ = Refl
nestedGoPlacesHead {xs = _ :: ps} prf =
  let (hd, rest) = orFalseC _ _ prf
  in orFalseIntro hd (nestedGoPlacesHead {xs = ps} rest)

||| A place named in `ps` is not freed by `es` when `nestedGo` is quiet.
export
argsHitIn : {acc : List (String, List Consume)} -> {p : Place} ->
  {ps : List Place} -> {es : List Expr} ->
  placeIn p ps = True ->
  nestedGo acc ps es = False ->
  argsHit acc p es = False
argsHitIn {ps = []} pin _ = void (trueNotFalseC (sym pin))
argsHitIn {ps = q :: qs} pin prf = hitGo (p == q) Refl pin prf
  where
    hitGo : (eqb : Bool) -> p == q = eqb ->
            placeIn p (q :: qs) = True ->
            nestedGo acc (q :: qs) es = False ->
            argsHit acc p es = False
    hitGo True pq _ prf0 =
      replace {p = \n => argsHit acc n es = False}
        (sym (eqNatTrue p q pq)) (fst (orFalseC _ _ prf0))
    hitGo False pq pin0 prf0 =
      argsHitIn {ps = qs}
        (replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0)
        (snd (orFalseC _ _ prf0))

nestedGoArgsTail : {acc : List (String, List Consume)} -> {ps : List Place} ->
  {e : Expr} -> {es : List Expr} ->
  nestedGo acc ps (e :: es) = False -> nestedGo acc ps es = False
nestedGoArgsTail {ps = []} _ = Refl
nestedGoArgsTail {ps = _ :: qs} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (argsHitTail hd) (nestedGoArgsTail tl)

mixedOverlapBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  mixedAlias (e :: es) (m :: ms) = False ->
  mixedAlias es ms = False
mixedOverlapBorrow {m = Never} _ prf with (argVarPlace e)
  mixedOverlapBorrow {m = Never} _ prf | Just _ = snd (orFalseC _ _ prf)
  mixedOverlapBorrow {m = Never} _ prf | Nothing = prf
mixedOverlapBorrow {m = May} pc _ = void (trueNotFalseC pc)
mixedOverlapBorrow {m = Always} pc _ = void (trueNotFalseC pc)

mixedOverlapConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  mixedAlias (e :: es) (m :: ms) = False ->
  mixedAlias es ms = False
mixedOverlapConsume {m = May} _ prf with (argVarPlace e)
  mixedOverlapConsume {m = May} _ prf | Just p =
    placesOverlapAppendR {ys = [p]} prf
  mixedOverlapConsume {m = May} _ prf | Nothing = prf
mixedOverlapConsume {m = Always} _ prf with (argVarPlace e)
  mixedOverlapConsume {m = Always} _ prf | Just p =
    placesOverlapAppendR {ys = [p]} prf
  mixedOverlapConsume {m = Always} _ prf | Nothing = prf
mixedOverlapConsume {m = Never} pc _ = void (trueNotFalseC (sym pc))

assignOverlapBorrow : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  assignAlias (e :: es) (m :: ms) = False ->
  assignAlias es ms = False
assignOverlapBorrow {m = Never} _ prf =
  placesOverlapAppendL
    {xs = valuePlaces e} {ys = aliasBorrowPlaces es ms} {zs = aliasConsumePlaces es ms}
    prf
assignOverlapBorrow {m = May} pc _ = void (trueNotFalseC pc)
assignOverlapBorrow {m = Always} pc _ = void (trueNotFalseC pc)

assignOverlapConsume : {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  mixedAlias (e :: es) (m :: ms) = False ->
  assignAlias (e :: es) (m :: ms) = False ->
  assignAlias es ms = False
assignOverlapConsume {m = May} _ _ prf =
  placesOverlapAppendR
    {xs = aliasBorrowPlaces es ms} {ys = valuePlaces e} {zs = aliasConsumePlaces es ms}
    prf
assignOverlapConsume {m = Always} _ _ prf =
  placesOverlapAppendR
    {xs = aliasBorrowPlaces es ms} {ys = valuePlaces e} {zs = aliasConsumePlaces es ms}
    prf
assignOverlapConsume {m = Never} pc _ _ = void (trueNotFalseC (sym pc))

nestedOverlapBorrow : {ctx : Ctx} -> {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  nestedMixed ctx (e :: es) (m :: ms) = False ->
  nestedMixed ctx es ms = False
nestedOverlapBorrow {m = Never} _ prf =
  nestedGoArgsTail
    (nestedGoPlacesAppend {acc = ctx.summaries} {xs = nestPlace e}
       {ys = nestBorrowPlaces es ms} {es = e :: es} prf)
nestedOverlapBorrow {m = May} pc _ = void (trueNotFalseC pc)
nestedOverlapBorrow {m = Always} pc _ = void (trueNotFalseC pc)

nestedOverlapConsume : {ctx : Ctx} -> {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  nestedMixed ctx (e :: es) (m :: ms) = False ->
  nestedMixed ctx es ms = False
nestedOverlapConsume {m = May} _ prf =
  nestedGoArgsTail {acc = ctx.summaries} {ps = nestBorrowPlaces es ms} {e} {es} prf
nestedOverlapConsume {m = Always} _ prf =
  nestedGoArgsTail {acc = ctx.summaries} {ps = nestBorrowPlaces es ms} {e} {es} prf
nestedOverlapConsume {m = Never} pc _ = void (trueNotFalseC (sym pc))

||| Tail of a borrow-head argument list keeps all three alias flags false.
export
aliasQuietBorrowTail :
  {ctx : Ctx} -> {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  mixedAlias (e :: es) (m :: ms) = False ->
  nestedMixed ctx (e :: es) (m :: ms) = False ->
  assignAlias (e :: es) (m :: ms) = False ->
  (mixedAlias es ms = False, nestedMixed ctx es ms = False, assignAlias es ms = False)
aliasQuietBorrowTail pc pm pn pa =
  (mixedOverlapBorrow pc pm, nestedOverlapBorrow pc pn, assignOverlapBorrow pc pa)

||| Tail of a consume-head argument list keeps all three alias flags false.
export
aliasQuietConsumeTail :
  {ctx : Ctx} -> {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  mixedAlias (e :: es) (m :: ms) = False ->
  nestedMixed ctx (e :: es) (m :: ms) = False ->
  assignAlias (e :: es) (m :: ms) = False ->
  (mixedAlias es ms = False, nestedMixed ctx es ms = False, assignAlias es ms = False)
aliasQuietConsumeTail pc pm pn pa =
  (mixedOverlapConsume pc pm, nestedOverlapConsume pc pn, assignOverlapConsume pc pm pa)

||| `argFrees` of a call is false only when the callee does not consume `p`
||| and no argument expression frees `p`.
export
argFreesCallSplit :
  {acc : List (String, List Consume)} -> {p : Place} -> {id : Nat} ->
  {callee : String} -> {args : List Expr} ->
  argFrees acc p (ECall id callee args) = False ->
  (doesConsume (consumeInArgs acc p callee args) = False, argsFree acc p args = False)
argFreesCallSplit prf = orFalseC _ _ prf

export
argFreesAssignEq :
  {acc : List (String, List Consume)} -> {p : Place} ->
  {id, n : Nat} -> {nm : String} -> {ty : Ty} -> {rhs : Expr} ->
  argFrees acc p (EAssign id n nm ty rhs) = argFrees acc p rhs
argFreesAssignEq = Refl

export
argFreesMallocEq :
  {acc : List (String, List Consume)} -> {p : Place} -> {id : Nat} -> {args : List Expr} ->
  argFrees acc p (EMalloc id args) = argsFree acc p args
argFreesMallocEq = Refl

export
argFreesUseEq :
  {acc : List (String, List Consume)} -> {p : Place} -> {id : Nat} -> {args : List Expr} ->
  argFrees acc p (EUse id args) = argsFree acc p args
argFreesUseEq = Refl

export
argFreesVarFalse :
  {acc : List (String, List Consume)} -> {p : Place} -> {id, q : Nat} -> {nm : String} ->
  argFrees acc p (EVar id q nm) = False
argFreesVarFalse = Refl

export
argFreesOtherFalse :
  {acc : List (String, List Consume)} -> {p : Place} -> {e : Expr} ->
  argFrees acc p e = False ->
  argsFree acc p [] = False
argFreesOtherFalse _ = Refl

||| Consume positions under `modes` do not move `p`. Extras (past `modes`)
||| are not consume positions of `consumeInArgs` (`sumHead []` is Never).
export
data MoveQuiet : Place -> List Expr -> List Consume -> Type where
  MQNil : MoveQuiet p [] ms
  MQBorrow : doesConsume m = False -> MoveQuiet p es ms -> MoveQuiet p (e :: es) (m :: ms)
  MQMove : doesConsume m = True -> movedInExpr p e = False ->
           MoveQuiet p es ms -> MoveQuiet p (e :: es) (m :: ms)
  MQExtra : MoveQuiet p es [] -> MoveQuiet p (e :: es) []

doesConsumeNeverOnly : {c : Consume} -> doesConsume c = False -> c = Never
doesConsumeNeverOnly {c = Never} _ = Refl
doesConsumeNeverOnly {c = May} prf = void (trueNotFalseC prf)
doesConsumeNeverOnly {c = Always} prf = void (trueNotFalseC prf)

consumeMaySkip : {p : Place} -> {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  movedInExpr p e = False ->
  consumeInArgsGo p (e :: es) (May :: ms) = consumeInArgsGo p es ms
consumeMaySkip pm = rewrite pm in Refl

consumeMayHit : {p : Place} -> {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  movedInExpr p e = True ->
  consumeInArgsGo p (e :: es) (May :: ms) = Always
consumeMayHit pm = rewrite pm in Refl

consumeAlwaysSkip : {p : Place} -> {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  movedInExpr p e = False ->
  consumeInArgsGo p (e :: es) (Always :: ms) = consumeInArgsGo p es ms
consumeAlwaysSkip pm = rewrite pm in Refl

consumeAlwaysHit : {p : Place} -> {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  movedInExpr p e = True ->
  consumeInArgsGo p (e :: es) (Always :: ms) = Always
consumeAlwaysHit pm = rewrite pm in Refl

consumeGoQuiet : {p : Place} -> {es : List Expr} -> {modes : List Consume} ->
  consumeInArgsGo p es modes = Never ->
  MoveQuiet p es modes
consumeGoQuiet {es = []} _ = MQNil
consumeGoQuiet {p} {es = e :: es} {modes = []} prf =
  MQExtra (consumeGoQuiet prf)
consumeGoQuiet {p} {es = e :: es} {modes = Never :: ms} prf =
  MQBorrow Refl (consumeGoQuiet prf)
consumeGoQuiet {p} {es = e :: es} {modes = May :: ms} prf =
  mayArm (movedInExpr p e) Refl prf
  where
    mayArm : (b : Bool) -> movedInExpr p e = b ->
             consumeInArgsGo p (e :: es) (May :: ms) = Never ->
             MoveQuiet p (e :: es) (May :: ms)
    mayArm False pb eq =
      MQMove Refl pb
        (consumeGoQuiet (replace {p = \c => c = Never} (consumeMaySkip pb) eq))
    mayArm True pb eq =
      void (trueNotFalseC (cong doesConsume (trans (sym (consumeMayHit pb)) eq)))
consumeGoQuiet {p} {es = e :: es} {modes = Always :: ms} prf =
  alwaysArm (movedInExpr p e) Refl prf
  where
    alwaysArm : (b : Bool) -> movedInExpr p e = b ->
                consumeInArgsGo p (e :: es) (Always :: ms) = Never ->
                MoveQuiet p (e :: es) (Always :: ms)
    alwaysArm False pb eq =
      MQMove Refl pb
        (consumeGoQuiet (replace {p = \c => c = Never} (consumeAlwaysSkip pb) eq))
    alwaysArm True pb eq =
      void (trueNotFalseC (cong doesConsume (trans (sym (consumeAlwaysHit pb)) eq)))

||| `consumeInArgs` is Never, so no consume-mode argument moves `p`.
export
moveQuietOfConsume :
  {acc : List (String, List Consume)} -> {p : Place} -> {callee : String} ->
  {args : List Expr} ->
  doesConsume (consumeInArgs acc p callee args) = False ->
  MoveQuiet p args (calleeModes acc callee)
moveQuietOfConsume prf = consumeGoQuiet (doesConsumeNeverOnly prf)

export
checkFunsFromNil : (fuel : Nat) -> (ctx : Ctx) ->
  checkFunsFrom fuel ctx [] = Right ()
checkFunsFromNil _ _ = Refl

export
checkFunsFromLeft :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} -> {fs : List Fun} -> {d : Diag} ->
  checkFun fuel ctx f = Left d ->
  checkFunsFrom fuel ctx (f :: fs) = Left d
checkFunsFromLeft prf = rewrite prf in Refl

export
checkFunsFromRight :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} -> {fs : List Fun} ->
  checkFun fuel ctx f = Right () ->
  checkFunsFrom fuel ctx (f :: fs) = checkFunsFrom fuel ctx fs
checkFunsFromRight prf = rewrite prf in Refl

--------------------------------------------------------------------------------
-- Unfold lemmas (visible here; checker bodies are opaque elsewhere)
--------------------------------------------------------------------------------

export
checkExprLit : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) ->
               checkExpr ctx sc (ELit id) = Right sc
checkExprLit _ _ _ = Refl

export
checkExprNull : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) ->
                checkExpr ctx sc (ENull id) = Right sc
checkExprNull _ _ _ = Refl

export
checkExprMalloc : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (args : List Expr) ->
                  checkExpr ctx sc (EMalloc id args) = checkArgsBorrow ctx sc args
checkExprMalloc _ _ _ _ = Refl

export
checkExprVar : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (n : Place) -> (nm : String) ->
               checkExpr ctx sc (EVar id n nm) = usePlace sc n id nm
checkExprVar _ _ _ _ _ = Refl

export
checkExprCall : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (callee : String) ->
                (args : List Expr) ->
                checkExpr ctx sc (ECall id callee args) = checkCall ctx sc id callee args
checkExprCall _ _ _ _ _ = Refl

export
checkExprAsgCopy : (id : Nat) -> (n : Place) -> (nm : String) ->
                   {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} ->
                   checkExpr ctx sc (EAssign id n nm Copy rhs) = checkExpr ctx sc rhs
checkExprAsgCopy _ _ _ = Refl

export
checkExprUse : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (args : List Expr) ->
               checkExpr ctx sc (EUse id args) = checkArgsBorrow ctx sc args
checkExprUse _ _ _ _ = Refl

export
checkExprUnsup : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (reason : String) ->
                 checkExpr ctx sc (EUnsupported id reason) =
                   Left (MkDiag KUnsupported
                     ("unsupported construct: " ++ reason)
                     id "unsupported here" []
                     "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove")
checkExprUnsup _ _ _ _ = Refl

export
takeLit : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) ->
          takeOwner ctx sc (ELit id) = Right (sc, Ghost)
takeLit _ _ _ = Refl

export
takeNull : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) ->
           takeOwner ctx sc (ENull id) = Right (sc, Null)
takeNull _ _ _ = Refl

export
takeUnsup : (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (reason : String) ->
            takeOwner ctx sc (EUnsupported id reason) =
              Left (MkDiag KUnsupported
                ("unsupported construct: " ++ reason)
                id "unsupported here" []
                "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove")
takeUnsup _ _ _ _ = Refl

export
checkArgsBorrowNil : (ctx : Ctx) -> (sc : Scopes) ->
                     checkArgsBorrow ctx sc [] = Right sc
checkArgsBorrowNil _ _ = Refl

export
checkArgsMoveNil : (ctx : Ctx) -> (sc : Scopes) ->
                   checkArgsMove ctx sc [] = Right sc
checkArgsMoveNil _ _ = Refl

export
checkArgsModesNil : (ctx : Ctx) -> (sc : Scopes) -> (callee : String) ->
                    (modes : List Consume) ->
                    checkArgsModes ctx sc callee [] modes = Right sc
checkArgsModesNil _ _ _ _ = Refl

export
consumeHeadCons : (m : Consume) -> (ms : List Consume) -> consumeHead (m :: ms) = m
consumeHeadCons _ _ = Refl

export
consumeTailCons : (m : Consume) -> (ms : List Consume) -> consumeTail (m :: ms) = ms
consumeTailCons _ _ = Refl

export
consumeHeadNil : consumeHead [] = Always
consumeHeadNil = Refl

export
doesConsumeAlways : doesConsume Always = True
doesConsumeAlways = Refl

export
doesConsumeNever : doesConsume Never = False
doesConsumeNever = Refl

export
mapDiscardFlagLeft : {d : Diag} -> mapDiscardFlag (Left d) = Left d
mapDiscardFlagLeft = Refl

export
mapDiscardFlagRight : {sc : Scopes} -> {fl : Flag} ->
                      mapDiscardFlag (Right (sc, fl)) = Right sc
mapDiscardFlagRight = Refl

export
consumeTakeLeft : {e : Expr} -> {d : Diag} ->
                  consumeTake e (Left d) = Left d
consumeTakeLeft = Refl

export
consumeTakeOwner : {e : Expr} -> {sc : Scopes} ->
                   consumeTake e (Right (sc, Owner)) = Right sc
consumeTakeOwner = Refl

export
consumeTakeNull : {e : Expr} -> {sc : Scopes} ->
                  consumeTake e (Right (sc, Null)) = Right sc
consumeTakeNull = Refl

export
consumeTakeGhost : {e : Expr} -> {sc : Scopes} ->
                   consumeTake e (Right (sc, Ghost)) = Left (ghostNotOwner e)
consumeTakeGhost = Refl

export
ownerNotGhost : Not (Owner = Ghost)
ownerNotGhost Refl impossible

export
nullNotGhost : Not (Null = Ghost)
nullNotGhost Refl impossible

export
ownerNotNull : Not (Owner = Null)
ownerNotNull Refl impossible

export
checkReallocNil : (ctx : Ctx) -> (sc : Scopes) ->
                  checkRealloc ctx sc [] = Right sc
checkReallocNil _ _ = Refl

export
reallocTailLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkRealloc ctx sc (e :: es) = Left d
reallocTailLeft _ prf = rewrite prf in Refl

export
reallocTailRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {fl : Flag} ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  checkRealloc ctx sc (e :: es) = checkArgsBorrow ctx sc1 es
reallocTailRight _ prf = rewrite prf in Refl

export
checkCallBuiltin :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = checkArgsBorrow ctx sc args
checkCallBuiltin pb = rewrite pb in Refl

export
checkCallOpaque :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isRealloc callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args =
    Left (MkDiag KUnsupported
      ("unsupported call to `" ++ callee ++ "`: no function body, so pagurus cannot prove the call is safe")
      nid "called here"
      []
      "provide a definition in this translation unit, or avoid passing unique pointers to opaque functions")
checkCallOpaque pb pr pd = rewrite pb in rewrite pd in rewrite pr in Refl

export
checkCallRealloc :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isRealloc callee = True ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = checkRealloc ctx sc args
checkCallRealloc pb pr pd = rewrite pb in rewrite pd in rewrite pr in Refl

export
definedCallFromFalse :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} -> {modes : List Consume} ->
  definedCallFrom False ctx sc nid callee args modes =
    checkArgsModes ctx sc callee args modes
definedCallFromFalse = Refl

export
definedCallFromTrue :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} -> {modes : List Consume} ->
  definedCallFrom True ctx sc nid callee args modes =
    Left (mixedAliasDiag nid callee (mixedAliasArg args modes))
definedCallFromTrue = Refl

export
checkCallDefined :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  aliasBad ctx args callee = False ->
  checkCall ctx sc nid callee args =
    checkArgsModes ctx sc callee args (funModes ctx callee)
checkCallDefined pb pd pbad = rewrite pb in rewrite pd in rewrite pbad in Refl

export
checkCallMixedAlias :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  aliasBad ctx args callee = True ->
  checkCall ctx sc nid callee args =
    Left (mixedAliasDiag nid callee (mixedAliasArg args (funModes ctx callee)))
checkCallMixedAlias pb pd pbad = rewrite pb in rewrite pd in rewrite pbad in Refl

leftNotRightChk : {0 d : a} -> {0 x : b} -> Not (Left d = Right x)
leftNotRightChk Refl impossible

rightInjChk : Right x = Right y -> x = y
rightInjChk Refl = Refl

export
callDefinedNoAlias :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  checkCall ctx sc nid callee args = Right sc' ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  aliasBad ctx args callee = False
callDefinedNoAlias eq pb pd with (aliasBad ctx args callee) proof pbad
  callDefinedNoAlias eq pb pd | False = Refl
  callDefinedNoAlias eq pb pd | True =
    void (leftNotRightChk (trans (sym (checkCallMixedAlias pb pd pbad)) eq))

||| A call with no arguments does not change scopes.
export
callNilScope :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {nid : Nat} -> {callee : String} ->
  checkCall ctx sc nid callee [] = Right sc' ->
  sc' = sc
callNilScope eq =
  nilGo (isBuiltin callee) Refl (isDefined ctx callee) Refl (isRealloc callee) Refl
  where
    nilGo :
      (b : Bool) -> isBuiltin callee = b ->
      (d : Bool) -> isDefined ctx callee = d ->
      (r : Bool) -> isRealloc callee = r ->
      sc' = sc
    nilGo True pb _ _ _ _ =
      sym (rightInjChk (trans (sym (trans (checkCallBuiltin {args = []} pb)
                                  (checkArgsBorrowNil ctx sc))) eq))
    nilGo False pb True pd _ _ =
      let pbad = callDefinedNoAlias {args = []} eq pb pd
      in sym (rightInjChk (trans (sym (trans (checkCallDefined {args = []} pb pd pbad)
                                     (checkArgsModesNil ctx sc callee (funModes ctx callee)))) eq))
    nilGo False pb False pd True pr =
      sym (rightInjChk (trans (sym (trans (checkCallRealloc {args = []} pb pr pd)
                                  (checkReallocNil ctx sc))) eq))
    nilGo False pb False pd False pr =
      void (leftNotRightChk (trans (sym (checkCallOpaque {args = []} pb pr pd)) eq))

export
assignPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrLeft _ _ _ prf = rewrite prf in Refl

export
assignPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  assignPlace ctx sc id n nm Ptr rhs False = Right sc2
assignPtrOwner pT pU = rewrite pT in rewrite pU in Refl

export
assignPtrUseFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrUseFail pT pU = rewrite pT in rewrite pU in Refl

export
assignPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  assignPlace ctx sc id n nm Ptr rhs False =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
assignPtrGhost _ _ _ pT = rewrite pT in Refl

export
assignPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  assignPlace ctx sc id n nm Ptr rhs False =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
assignPtrNull _ _ _ pT = rewrite pT in Refl

export
checkExprAsgPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Left d
checkExprAsgPtrLeft _ _ _ prf = rewrite prf in Refl

export
checkExprAsgPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc2
checkExprAsgPtrOwner pT pU = rewrite pT in rewrite pU in Refl

export
checkExprAsgPtrUseFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Left d
checkExprAsgPtrUseFail pT pU = rewrite pT in rewrite pU in Refl

export
checkExprAsgPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
checkExprAsgPtrGhost _ _ _ pT = rewrite pT in Refl

export
checkExprAsgPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
checkExprAsgPtrNull _ _ _ pT = rewrite pT in Refl

export
takeMallocLeft :
  (mid : Nat) ->
  {ctx : Ctx} -> {sc : Scopes} -> {args : List Expr} -> {d : Diag} ->
  checkArgsBorrow ctx sc args = Left d ->
  takeOwner ctx sc (EMalloc mid args) = Left d
takeMallocLeft _ prf = rewrite prf in Refl

export
takeMallocRight :
  (mid : Nat) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {args : List Expr} ->
  checkArgsBorrow ctx sc args = Right sc1 ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc1, Owner)
takeMallocRight _ prf = rewrite prf in Refl

export
takeAsgCopyLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  checkExpr ctx sc rhs = Left d ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Left d
takeAsgCopyLeft _ _ _ prf = rewrite prf in Refl

export
takeAsgCopyRight :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  checkExpr ctx sc rhs = Right sc1 ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, Ghost)
takeAsgCopyRight _ _ _ prf = rewrite prf in Refl

export
takeAsgPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrLeft _ _ _ prf = rewrite prf in Refl

export
takeAsgPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc2, Owner)
takeAsgPtrOwner pT pM = rewrite pT in rewrite pM in Refl

export
takeAsgPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1, Ghost)
takeAsgPtrGhost _ _ _ pT = rewrite pT in Refl

export
takeAsgPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1, Null)
takeAsgPtrNull _ _ _ pT = rewrite pT in Refl

export
takeAsgPtrFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrFail pT pM = rewrite pT in rewrite pM in Refl

export
takeVarMiss :
  (ctx : Ctx) -> (nid : Nat) -> (nm : String) ->
  {sc : Scopes} -> {n : Place} ->
  lookupPlace n sc = Nothing ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc, Ghost)
takeVarMiss _ _ _ prf = rewrite prf in Refl

export
takeVarJustL :
  (ctx : Ctx) ->
  {sc : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Left d ->
  takeOwner ctx sc (EVar nid n nm) = Left d
takeVarJustL _ pLook pM = rewrite pLook in rewrite pM in Refl

export
takeVarJustR :
  (ctx : Ctx) ->
  {sc, sc1 : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} ->
  {st : Status} ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Right sc1 ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc1, Owner)
takeVarJustR _ pLook pM = rewrite pLook in rewrite pM in Refl

export
reallocOwnerLeft : (b : Bool) -> {d : Diag} ->
                   reallocOwner b (Left d) = Left d
reallocOwnerLeft True = Refl
reallocOwnerLeft False = Refl

export
takeCallLeft :
  {ctx : Ctx} -> {sc : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} -> {d : Diag} ->
  checkExpr ctx sc (ECall id callee args) = Left d ->
  takeOwner ctx sc (ECall id callee args) = Left d
takeCallLeft prf =
  trans
    (cong (reallocOwner (isRealloc callee && not (isDefined ctx callee)))
          (trans (sym (checkExprCall ctx sc id callee args)) prf))
    (reallocOwnerLeft (isRealloc callee && not (isDefined ctx callee)))

export
takeCallRight :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isRealloc callee && not (isDefined ctx callee) = False ->
  checkExpr ctx sc (ECall id callee args) = Right sc1 ->
  takeOwner ctx sc (ECall id callee args) = Right (sc1, Ghost)
takeCallRight pFresh prf =
  rewrite pFresh in
  rewrite (sym (checkExprCall ctx sc id callee args)) in
  rewrite prf in Refl

pairFstChk : {x, y : t} -> {p, q : u} -> (x, p) = (y, q) -> x = y
pairFstChk Refl = Refl

||| A non-prototype call's `takeOwner` is `mapToGhost` of `checkCall`.
export
takeCallCheck :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} -> {fl : Flag} ->
  isRealloc callee && not (isDefined ctx callee) = False ->
  takeOwner ctx sc (ECall id callee args) = Right (sc1, fl) ->
  checkCall ctx sc id callee args = Right sc1
takeCallCheck pFresh pT =
  go (checkCall ctx sc id callee args) Refl
    (replace {p = \b =>
        reallocOwner b (checkCall ctx sc id callee args) = Right (sc1, fl)}
       pFresh pT)
  where
    go : (res : Either Diag Scopes) ->
         checkCall ctx sc id callee args = res ->
         reallocOwner False res = Right (sc1, fl) ->
         checkCall ctx sc id callee args = Right sc1
    go (Left _) _ eq = void (leftNotRightChk eq)
    go (Right scA) pr eq =
      rewrite pr in rewrite (pairFstChk (rightInjChk eq)) in Refl

export
takeReallocLeft :
  {ctx : Ctx} -> {sc : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} -> {d : Diag} ->
  isRealloc callee && not (isDefined ctx callee) = True ->
  checkCall ctx sc id callee args = Left d ->
  takeOwner ctx sc (ECall id callee args) = Left d
takeReallocLeft pFresh prf = rewrite pFresh in rewrite prf in Refl

export
takeReallocRight :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isRealloc callee && not (isDefined ctx callee) = True ->
  checkCall ctx sc id callee args = Right sc1 ->
  takeOwner ctx sc (ECall id callee args) = Right (sc1, Owner)
takeReallocRight pFresh prf = rewrite pFresh in rewrite prf in Refl

export
takeUseLeft :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc : Scopes} -> {args : List Expr} -> {d : Diag} ->
  checkArgsBorrow ctx sc args = Left d ->
  takeOwner ctx sc (EUse uid args) = Left d
takeUseLeft _ prf = rewrite prf in Refl

export
takeUseRight :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {args : List Expr} ->
  checkArgsBorrow ctx sc args = Right sc1 ->
  takeOwner ctx sc (EUse uid args) = Right (sc1, Ghost)
takeUseRight _ prf = rewrite prf in Refl

export
checkStmtZero :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) ->
  checkStmt Z ctx sc s =
    Left (MkDiag KUnproven
      "analysis fuel exhausted"
      (stmtId s) "here" []
      "this is an internal limitation; simplify control flow")
checkStmtZero _ _ _ = Refl

export
checkStmtBlock :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (body : List Stmt) ->
  checkStmt (S fuel) ctx sc (SBlock id body) = checkStmts fuel ctx sc body
checkStmtBlock _ _ _ _ _ = Refl

export
checkStmtDeclCopyNone :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (n : Place) -> (nm : String) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy Nothing) = Right sc
checkStmtDeclCopyNone _ _ _ _ _ _ = Refl

export
checkStmtDeclCopyJust :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy (Just e)) = checkExpr ctx sc e
checkStmtDeclCopyJust _ _ _ _ = Refl

export
checkStmtDeclPtrNone :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (n : Place) -> (nm : String) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr Nothing) =
    Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc)
checkStmtDeclPtrNone _ _ _ _ _ _ = Refl

export
checkStmtAsgCopy :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Copy rhs) = checkExpr ctx sc rhs
checkStmtAsgCopy _ _ _ _ = Refl

export
checkStmtDrop :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (n : Place) -> (nm : String) ->
  checkStmt (S fuel) ctx sc (SDrop id n nm) = dropPlace sc n id nm
checkStmtDrop _ _ _ _ _ _ = Refl

export
checkStmtCall :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (callee : String) -> (args : List Expr) ->
  checkStmt (S fuel) ctx sc (SCall id callee args) = checkCall ctx sc id callee args
checkStmtCall _ _ _ _ _ _ = Refl

export
checkStmtRetNone :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) ->
  checkStmt (S fuel) ctx sc (SReturn id Nothing) = Right sc
checkStmtRetNone _ _ _ _ = Refl

export
checkStmtRetLit :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) -> (id : Nat) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ELit id))) = checkExpr ctx sc (ELit id)
checkStmtRetLit _ _ _ _ _ = Refl

export
checkStmtRetNull :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) -> (id : Nat) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ENull id))) = checkExpr ctx sc (ENull id)
checkStmtRetNull _ _ _ _ _ = Refl

export
checkStmtRetMalloc :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (mid : Nat) -> (args : List Expr) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EMalloc mid args))) =
    checkExpr ctx sc (EMalloc mid args)
checkStmtRetMalloc _ _ _ _ _ _ = Refl

export
checkStmtRetCall :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (id : Nat) -> (callee : String) -> (args : List Expr) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ECall id callee args))) =
    checkExpr ctx sc (ECall id callee args)
checkStmtRetCall _ _ _ _ _ _ _ = Refl

export
checkStmtRetUse :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (uid : Nat) -> (args : List Expr) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EUse uid args))) =
    checkExpr ctx sc (EUse uid args)
checkStmtRetUse _ _ _ _ _ _ = Refl

export
checkStmtRetAsg :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (id : Nat) -> (n : Place) -> (nm : String) -> (ty : Ty) -> (rhs : Expr) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EAssign id n nm ty rhs))) =
    checkExpr ctx sc (EAssign id n nm ty rhs)
checkStmtRetAsg _ _ _ _ _ _ _ _ _ = Refl

export
checkStmtRetUnsup :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (id : Nat) -> (reason : String) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EUnsupported id reason))) =
    checkExpr ctx sc (EUnsupported id reason)
checkStmtRetUnsup _ _ _ _ _ _ = Refl

export
checkStmtExpr :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (e : Expr) ->
  checkStmt (S fuel) ctx sc (SExpr id e) = checkExpr ctx sc e
checkStmtExpr _ _ _ _ _ = Refl

export
checkStmtUnsup :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (reason : String) ->
  checkStmt (S fuel) ctx sc (SUnsupported id reason) =
    Left (MkDiag KUnsupported
      ("unsupported construct: " ++ reason)
      id "unsupported here" []
      "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove")
checkStmtUnsup _ _ _ _ _ = Refl

export
checkStmtLoop :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (body : List Stmt) ->
  checkStmt (S fuel) ctx sc (SLoop id body) = loopFix fuel ctx sc id body
checkStmtLoop _ _ _ _ _ = Refl

export
checkStmtsZero :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) -> (ss : List Stmt) ->
  checkStmts Z ctx sc (s :: ss) =
    Left (MkDiag KUnproven "analysis fuel exhausted" (stmtId s) "here" []
      "this is an internal limitation; simplify control flow")
checkStmtsZero _ _ _ _ = Refl

export
checkStmtsNil :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  checkStmts fuel ctx sc [] = Right sc
checkStmtsNil Z _ _ = Refl
checkStmtsNil (S _) _ _ = Refl

export
loopFixZero :
  (ctx : Ctx) -> (sc : Scopes) -> (id : Nat) -> (body : List Stmt) ->
  loopFix Z ctx sc id body =
    Left (MkDiag KUnproven
      "loop fixpoint fuel exhausted"
      id "loop here" []
      "the ownership lattice did not stabilise; simplify the loop")
loopFixZero _ _ _ _ = Refl

export
declPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Left d
declPtrLeft _ _ _ _ prf = rewrite prf in Refl

export
declPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  takeOwner ctx sc e = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton AOwned) sc1)
declPtrOwner _ _ _ _ prf = rewrite prf in Refl

export
declPtrGhostEq :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  takeOwner ctx sc e = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc1)
declPtrGhostEq _ _ _ _ prf = rewrite prf in Refl

export
declPtrNullEq :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  takeOwner ctx sc e = Right (sc1, Null) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton ANull) sc1)
declPtrNullEq _ _ _ _ prf = rewrite prf in Refl

export
stmtAsgPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Left d
stmtAsgPtrLeft _ _ _ _ prf = rewrite prf in Refl

export
stmtAsgPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AOwned) sc1)
stmtAsgPtrOwner _ _ _ _ prf = rewrite prf in Refl

export
stmtAsgPtrGhost :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
stmtAsgPtrGhost _ _ _ _ prf = rewrite prf in Refl

export
stmtAsgPtrNull :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
stmtAsgPtrNull _ _ _ _ prf = rewrite prf in Refl

export
retVarLeft :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  {sc : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} -> {d : Diag} ->
  takeOwner ctx sc (EVar nid n nm) = Left d ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Left d
retVarLeft _ _ _ prf = rewrite prf in Refl

export
retVarRight :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  {sc, sc1 : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc1, fl) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Right sc1
retVarRight _ _ _ prf = rewrite prf in Refl

export
argsBorrowLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  checkExpr ctx sc e = Left d ->
  checkArgsBorrow ctx sc (e :: es) = Left d
argsBorrowLeft _ prf = rewrite prf in Refl

export
argsBorrowRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  checkExpr ctx sc e = Right sc1 ->
  checkArgsBorrow ctx sc (e :: es) = checkArgsBorrow ctx sc1 es
argsBorrowRight _ prf = rewrite prf in Refl

export
argsBorrowSplit :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {es : List Expr} ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  (sc1 ** (checkExpr ctx sc e = Right sc1, checkArgsBorrow ctx sc1 es = Right sc'))
argsBorrowSplit eq = splitGo (checkExpr ctx sc e) Refl
  where
    splitGo :
      (res : Either Diag Scopes) ->
      checkExpr ctx sc e = res ->
      (sc1 ** (checkExpr ctx sc e = Right sc1, checkArgsBorrow ctx sc1 es = Right sc'))
    splitGo (Left d) pE =
      void (leftNotRightChk (trans (sym (argsBorrowLeft es pE)) eq))
    splitGo (Right sc1) pE =
      (sc1 ** (pE, trans (sym (argsBorrowRight es pE)) eq))

export
argsMoveLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkArgsMove ctx sc (e :: es) = Left d
argsMoveLeft _ prf = rewrite prf in Refl

export
argsMoveRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {fl : Flag} ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  checkArgsMove ctx sc (e :: es) = checkArgsMove ctx sc1 es
argsMoveRight _ prf = rewrite prf in Refl

export
argsModesLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {callee : String} ->
  {modes : List Consume} -> {d : Diag} ->
  argAction (doesConsume (consumeHead modes)) ctx sc e = Left d ->
  checkArgsModes ctx sc callee (e :: es) modes =
    argsModesFrom (doesConsume (consumeHead modes)) callee e ctx es (consumeTail modes) (Left d)
argsModesLeft _ prf = rewrite prf in Refl

export
argsModesRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  {modes : List Consume} ->
  argAction (doesConsume (consumeHead modes)) ctx sc e = Right sc1 ->
  checkArgsModes ctx sc callee (e :: es) modes =
    argsModesFrom (doesConsume (consumeHead modes)) callee e ctx es (consumeTail modes) (Right sc1)
argsModesRight _ prf = rewrite prf in Refl

export
argsModesFromRight :
  {cons : Bool} -> {callee : String} -> {e : Expr} ->
  {ctx : Ctx} -> {es : List Expr} -> {ms : List Consume} -> {sc1 : Scopes} ->
  argsModesFrom cons callee e ctx es ms (Right sc1) =
    checkArgsModes ctx sc1 callee es ms
argsModesFromRight {cons = False} = Refl
argsModesFromRight {cons = True} = Refl

export
argsModesBorrowLeft :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} -> {d : Diag} ->
  doesConsume m = False ->
  checkExpr ctx sc e = Left d ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Left d
argsModesBorrowLeft _ _ pc pE = rewrite pc in rewrite pE in Refl

export
argsModesBorrowRight :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} ->
  doesConsume m = False ->
  checkExpr ctx sc e = Right sc1 ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) =
    checkArgsModes ctx sc1 callee es ms
argsModesBorrowRight _ _ pc pE = rewrite pc in rewrite pE in Refl

export
argsModesMoveLeft :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} -> {d : Diag} ->
  doesConsume m = True ->
  takeOwner ctx sc e = Left d ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Left (nameConsumedArg callee e d)
argsModesMoveLeft _ _ pc pT = rewrite pc in rewrite pT in Refl

export
argsModesMoveGhost :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} ->
  doesConsume m = True ->
  takeOwner ctx sc e = Right (sc1, Ghost) ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) =
    Left (nameConsumedArg callee e (ghostNotOwner e))
argsModesMoveGhost _ _ pc pT = rewrite pc in rewrite pT in Refl

export
argsModesMoveRight :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} -> {fl : Flag} ->
  doesConsume m = True ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  Not (fl = Ghost) ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) =
    checkArgsModes ctx sc1 callee es ms
argsModesMoveRight {fl = Owner} _ _ pc pT _ = rewrite pc in rewrite pT in Refl
argsModesMoveRight {fl = Null} _ _ pc pT _ = rewrite pc in rewrite pT in Refl
argsModesMoveRight {fl = Ghost} _ _ _ _ ng = void (ng Refl)

export
argsModesExtraLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {callee : String} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkArgsModes ctx sc callee (e :: es) [] = Left (nameConsumedArg callee e d)
argsModesExtraLeft _ pT = rewrite pT in Refl

export
argsModesExtraGhost :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  takeOwner ctx sc e = Right (sc1, Ghost) ->
  checkArgsModes ctx sc callee (e :: es) [] =
    Left (nameConsumedArg callee e (ghostNotOwner e))
argsModesExtraGhost _ pT = rewrite pT in Refl

export
argsModesExtraRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} -> {fl : Flag} ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  Not (fl = Ghost) ->
  checkArgsModes ctx sc callee (e :: es) [] =
    checkArgsModes ctx sc1 callee es []
argsModesExtraRight {fl = Owner} _ pT _ = rewrite pT in Refl
argsModesExtraRight {fl = Null} _ pT _ = rewrite pT in Refl
argsModesExtraRight {fl = Ghost} _ _ ng = void (ng Refl)

export
argsModesBorrowSplit :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {es : List Expr} ->
  {callee : String} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (sc1 ** (checkExpr ctx sc e = Right sc1,
           checkArgsModes ctx sc1 callee es ms = Right sc'))
argsModesBorrowSplit pc eq = splitGo (checkExpr ctx sc e) Refl
  where
    splitGo :
      (res : Either Diag Scopes) ->
      checkExpr ctx sc e = res ->
      (sc1 ** (checkExpr ctx sc e = Right sc1,
               checkArgsModes ctx sc1 callee es ms = Right sc'))
    splitGo (Left d) pE =
      void (leftNotRightChk (trans (sym (argsModesBorrowLeft es ms pc pE)) eq))
    splitGo (Right sc1) pE =
      (sc1 ** (pE, trans (sym (argsModesBorrowRight es ms pc pE)) eq))

export
argsModesMoveSplit :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {es : List Expr} ->
  {callee : String} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (sc1 ** (fl : Flag ** (takeOwner ctx sc e = Right (sc1, fl),
           checkArgsModes ctx sc1 callee es ms = Right sc')))
argsModesMoveSplit pc eq = splitGo (takeOwner ctx sc e) Refl
  where
    splitGo :
      (res : Either Diag (Scopes, Flag)) ->
      takeOwner ctx sc e = res ->
      (sc1 ** (fl : Flag ** (takeOwner ctx sc e = Right (sc1, fl),
               checkArgsModes ctx sc1 callee es ms = Right sc')))
    splitGo (Left d) pT =
      void (leftNotRightChk (trans (sym (argsModesMoveLeft es ms pc pT)) eq))
    splitGo (Right (sc1, Ghost)) pT =
      void (leftNotRightChk (trans (sym (argsModesMoveGhost es ms pc pT)) eq))
    splitGo (Right (sc1, Owner)) pT =
      (sc1 ** (Owner ** (pT, trans (sym (argsModesMoveRight es ms pc pT ownerNotGhost)) eq)))
    splitGo (Right (sc1, Null)) pT =
      (sc1 ** (Null ** (pT, trans (sym (argsModesMoveRight es ms pc pT nullNotGhost)) eq)))

export
argsModesExtraSplit :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {es : List Expr} ->
  {callee : String} ->
  checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
  (sc1 ** (fl : Flag ** (takeOwner ctx sc e = Right (sc1, fl),
           checkArgsModes ctx sc1 callee es [] = Right sc')))
argsModesExtraSplit eq = splitGo (takeOwner ctx sc e) Refl
  where
    splitGo :
      (res : Either Diag (Scopes, Flag)) ->
      takeOwner ctx sc e = res ->
      (sc1 ** (fl : Flag ** (takeOwner ctx sc e = Right (sc1, fl),
               checkArgsModes ctx sc1 callee es [] = Right sc')))
    splitGo (Left d) pT =
      void (leftNotRightChk (trans (sym (argsModesExtraLeft es pT)) eq))
    splitGo (Right (sc1, Ghost)) pT =
      void (leftNotRightChk (trans (sym (argsModesExtraGhost es pT)) eq))
    splitGo (Right (sc1, Owner)) pT =
      (sc1 ** (Owner ** (pT, trans (sym (argsModesExtraRight es pT ownerNotGhost)) eq)))
    splitGo (Right (sc1, Null)) pT =
      (sc1 ** (Null ** (pT, trans (sym (argsModesExtraRight es pT nullNotGhost)) eq)))

export
stmtsConsLeft :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc : Scopes} -> {s : Stmt} -> {d : Diag} ->
  checkStmt fuel ctx sc s = Left d ->
  checkStmts (S fuel) ctx sc (s :: ss) = Left d
stmtsConsLeft _ prf = rewrite prf in Refl

export
stmtsConsRight :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc1 : Scopes} -> {s : Stmt} ->
  isReturnStmt s = False ->
  checkStmt fuel ctx sc s = Right sc1 ->
  checkStmts (S fuel) ctx sc (s :: ss) = checkStmts fuel ctx sc1 ss
stmtsConsRight _ pR prf = rewrite prf in rewrite pR in Refl

export
stmtsConsRet :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc1 : Scopes} -> {s : Stmt} ->
  isReturnStmt s = True ->
  checkStmt fuel ctx sc s = Right sc1 ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc1
stmtsConsRet _ pR prf = rewrite prf in rewrite pR in Refl

export
ifExprLeft :
  (fuel : Nat) -> (iid : Nat) -> (thn : List Stmt) -> (els : List Stmt) ->
  {ctx : Ctx} -> {sc : Scopes} -> {cond : Expr} -> {d : Diag} ->
  checkExpr ctx sc cond = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifExprLeft _ _ _ _ prf = rewrite prf in Refl

export
ifThenLeft :
  (iid : Nat) -> (els : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0 : Scopes} ->
  {cond : Expr} -> {thn : List Stmt} -> {d : Diag} ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifThenLeft _ _ pC pT = rewrite pC in rewrite pT in Refl

export
ifElseLeft :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} -> {d : Diag} ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifElseLeft _ pC pT pE = rewrite pC in rewrite pT in rewrite pE in Refl

export
ifFull :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT, scE : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  stmtsEnded thn = False ->
  stmtsEnded els = False ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Right scE ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right (joinScopes scT scE)
ifFull _ pThn pEls pC pT pE =
  rewrite pC in rewrite pT in rewrite pE in rewrite pThn in rewrite pEls in Refl

export
ifThenEnded :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT, scE : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  stmtsEnded thn = True ->
  stmtsEnded els = False ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Right scE ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right scE
ifThenEnded _ pThn pEls pC pT pE =
  rewrite pC in rewrite pT in rewrite pE in rewrite pThn in rewrite pEls in Refl

export
ifElseEnded :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT, scE : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  stmtsEnded thn = False ->
  stmtsEnded els = True ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Right scE ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right scT
ifElseEnded _ pThn pEls pC pT pE =
  rewrite pC in rewrite pT in rewrite pE in rewrite pThn in rewrite pEls in Refl

export
ifBothEnded :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT, scE : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  stmtsEnded thn = True ->
  stmtsEnded els = True ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Right scE ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right []
ifBothEnded _ pThn pEls pC pT pE =
  rewrite pC in rewrite pT in rewrite pE in rewrite pThn in rewrite pEls in Refl

export
loopFixLeft :
  (lid : Nat) ->
  {k : Nat} -> {ctx : Ctx} -> {sc : Scopes} -> {bod : List Stmt} -> {d : Diag} ->
  checkStmts k ctx sc bod = Left d ->
  loopFix (S k) ctx sc lid bod = Left d
loopFixLeft _ prf = rewrite prf in Refl

export
loopFixTrue :
  {k : Nat} -> {ctx : Ctx} -> {sc, scB : Scopes} -> {lid : Nat} -> {bod : List Stmt} ->
  stmtsEnded bod = False ->
  checkStmts k ctx sc bod = Right scB ->
  eqScopes (joinScopes sc scB) sc = True ->
  loopFix (S k) ctx sc lid bod = Right (joinScopes sc scB)
loopFixTrue pEnd pB pEq = rewrite pB in rewrite pEnd in rewrite pEq in Refl

export
loopFixFalse :
  (lid : Nat) ->
  {k : Nat} -> {ctx : Ctx} -> {sc, scB : Scopes} -> {bod : List Stmt} ->
  stmtsEnded bod = False ->
  checkStmts k ctx sc bod = Right scB ->
  eqScopes (joinScopes sc scB) sc = False ->
  loopFix (S k) ctx sc lid bod = loopFix k ctx (joinScopes sc scB) lid bod
loopFixFalse _ pEnd pB pEq = rewrite pB in rewrite pEnd in rewrite pEq in Refl

export
loopFixBodyEnded :
  {k : Nat} -> {ctx : Ctx} -> {sc, scB : Scopes} -> {lid : Nat} -> {bod : List Stmt} ->
  stmtsEnded bod = True ->
  checkStmts k ctx sc bod = Right scB ->
  loopFix (S k) ctx sc lid bod = Right sc
loopFixBodyEnded pEnd pB = rewrite pB in rewrite pEnd in Refl

natEqReflChk : (n : Nat) -> n == n = True
natEqReflChk Z = Refl
natEqReflChk (S k) = natEqReflChk k

justInjChk : Just x = Just y -> x = y
justInjChk Refl = Refl

nothingNotJustChk : {0 x : a} -> Not (Nothing = Just x)
nothingNotJustChk Refl impossible

orTrueChk : {x, y : Bool} -> x || y = True -> Either (x = True) (y = True)
orTrueChk {x = True} Refl = Left Refl
orTrueChk {x = False} {y = True} Refl = Right Refl

export
placeInSplit :
  {p, q : Place} -> {qs : List Place} ->
  placeIn p (q :: qs) = True ->
  Either (p == q = True) (placeIn p qs = True)
placeInSplit pin = orTrueChk pin

||| The intern of a consume-mode `EVar` argument is in `consumePlaces`.
export
consumePlacesVar :
  (e : Expr) -> (es : List Expr) -> (m : Consume) -> (ms : List Consume) ->
  (p : Place) ->
  doesConsume m = True ->
  argVarPlace e = Just p ->
  placeIn p (consumePlaces (e :: es) (m :: ms)) = True
consumePlacesVar (EVar _ q _) es m ms p pc prf =
  rewrite pc in
  rewrite justInjChk prf in
  rewrite natEqReflChk p in Refl
consumePlacesVar (EAssign _ _ _ _ _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (ELit _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (ENull _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (EMalloc _ _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (ECall _ _ _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (EUse _ _) _ _ _ _ _ prf = void (nothingNotJustChk prf)
consumePlacesVar (EUnsupported _ _) _ _ _ _ _ prf = void (nothingNotJustChk prf)

||| Extra arguments beyond `funModes` are treated as consumed.
export
consumePlacesExtraVar :
  (e : Expr) -> (es : List Expr) ->
  (p : Place) ->
  argVarPlace e = Just p ->
  placeIn p (consumePlaces (e :: es) []) = True
consumePlacesExtraVar (EVar _ q _) es p prf =
  rewrite justInjChk prf in
  rewrite natEqReflChk p in Refl
consumePlacesExtraVar (EAssign _ _ _ _ _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (ELit _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (ENull _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (EMalloc _ _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (ECall _ _ _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (EUse _ _) _ _ prf = void (nothingNotJustChk prf)
consumePlacesExtraVar (EUnsupported _ _) _ _ prf = void (nothingNotJustChk prf)
