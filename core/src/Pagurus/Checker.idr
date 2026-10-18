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

||| Non-empty place list. Fresh malloc and realloc name no place.
public export
hasPlace : List Place -> Bool
hasPlace [] = False
hasPlace (_ :: _) = True

||| A copy that still names a pointer place. Storing it into a pointer
||| destination leaves that place a use-safe owner outside `nestPlace`.
||| Fresh malloc and realloc, and null or literals, name no place.
||| A pointer assignment only propagates a leak already in its rhs.
||| A direct `q = p`, `q = malloc()`, or `q = (x = malloc())` is not a leak.
public export
ghostCopyLeak : Expr -> Bool
ghostCopyLeak (EAssign _ _ _ Copy rhs) =
  maybeLivePtr rhs && hasPlace (valuePlaces rhs)
ghostCopyLeak (EAssign _ _ _ Ptr rhs) = ghostCopyLeak rhs
ghostCopyLeak _ = False

||| Pointer store of a copy that still names a live pointer place.
public export
ghostCopyDiag : Nat -> String -> Diag
ghostCopyDiag id nm =
  MkDiag KUnproven
    ("pointer assignment to `" ++ nm ++ "` copies a live pointer without taking it")
    id "assigned here"
    []
    "the source stays a use-safe owner, so this alias is not tracked; move the pointer instead"

export
ghostCopyLeakDirect : ghostCopyLeak (EVar 0 1 "p") = False
ghostCopyLeakDirect = Refl

export
ghostCopyLeakMalloc : ghostCopyLeak (EMalloc 0 []) = False
ghostCopyLeakMalloc = Refl

export
ghostCopyLeakCopyMalloc :
  ghostCopyLeak (EAssign 0 1 "x" Copy (EMalloc 2 [])) = False
ghostCopyLeakCopyMalloc = Refl

export
ghostCopyLeakCopyNull :
  ghostCopyLeak (EAssign 0 1 "x" Copy (ENull 2)) = False
ghostCopyLeakCopyNull = Refl

export
ghostCopyLeakCopyVar :
  ghostCopyLeak (EAssign 0 1 "x" Copy (EVar 2 3 "p")) = True
ghostCopyLeakCopyVar = Refl

export
ghostCopyLeakPtrOfCopy :
  ghostCopyLeak (EAssign 0 1 "r" Ptr (EAssign 2 3 "x" Copy (EVar 4 5 "p"))) = True
ghostCopyLeakPtrOfCopy = Refl

export
ghostCopyLeakCopyOfPtrMalloc :
  ghostCopyLeak (EAssign 0 1 "x" Copy (EAssign 2 3 "r" Ptr (EMalloc 4 []))) = True
ghostCopyLeakCopyOfPtrMalloc = Refl

||| `n = use(n = x)`: the use is not a live pointer, so the outer dest
||| is not a value-place.
export
nestedUseAssignNotLive :
  maybeLivePtr (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")]) = False
nestedUseAssignNotLive = Refl

export
nestedUseAssignValuePlaces :
  valuePlaces (EAssign 0 1 "n" Ptr
    (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])) = []
nestedUseAssignValuePlaces = Refl

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
||| Kept for the old shape predicates; `checkCall` diagnostics use
||| `overlapArg` on the footprint list.
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

mutual
  ||| Pointer-assignment destinations that stay live in the caller.
  ||| A call, malloc, or use returns before the next argument, so a store
  ||| in an argument is still there. The source is not included. A bare
  ||| variable is not a destination, so f(g(p), h(p)) stays accepted.
  ||| valuePlaces of a call stays empty, so a later move of the dest
  ||| (f(g(r = p), r)) is not assignAlias.
  public export
  nestStored : Expr -> List Place
  nestStored (EAssign _ p _ Ptr rhs) =
    let rest = nestStored rhs in
    if maybeLivePtr rhs then p :: rest else rest
  nestStored (EAssign _ _ _ Copy rhs) = nestStored rhs
  nestStored (ECall _ _ args) = nestStoreds args
  nestStored (EMalloc _ args) = nestStoreds args
  nestStored (EUse _ args) = nestStoreds args
  nestStored _ = []

  public export
  nestStoreds : List Expr -> List Place
  nestStoreds [] = []
  nestStoreds (e :: es) = nestStored e ++ nestStoreds es

||| True when a pointer assignment's value is an existing place, not a
||| fresh allocation. `takeOwner` of that variable moves it, and `argFrees`
||| of a variable is false, so an outer `argsHit` does not see the move.
public export
heldFromVar : Expr -> Bool
heldFromVar (EVar _ _ _) = True
heldFromVar (EAssign _ _ _ Ptr rhs) = heldFromVar rhs
heldFromVar _ = False

mutual
  ||| Destinations that can hold an address which was already live.
  ||| A fresh `malloc` is not one: its result is new, and a free of that
  ||| result does not kill a cell the caller already owned. A bare variable
  ||| is not a destination. The source is not included.
  public export
  nestHeld : Expr -> List Place
  nestHeld (EAssign _ p _ Ptr rhs) =
    let rest = nestHeld rhs in
    if heldFromVar rhs then p :: rest else rest
  nestHeld (EAssign _ _ _ Copy rhs) = nestHeld rhs
  nestHeld (ECall _ _ args) = nestHelds args
  nestHeld (EMalloc _ args) = nestHelds args
  nestHeld (EUse _ args) = nestHelds args
  nestHeld _ = []

  public export
  nestHelds : List Expr -> List Place
  nestHelds [] = []
  nestHelds (e :: es) = nestHeld e ++ nestHelds es

||| Pointer destinations stored inside a call, malloc, or use.
||| An assignment is walked through and its own destination is not
||| added: `nestAssigns` and `valuePlaces` already name that. The
||| source is not included, so `f(r = g(p), h(p))` stays accepted.
public export
nestBuried : Expr -> List Place
nestBuried (EAssign _ _ _ _ rhs) = nestBuried rhs
nestBuried (ECall _ _ args) = nestStoreds args
nestBuried (EMalloc _ args) = nestStoreds args
nestBuried (EUse _ args) = nestStoreds args
nestBuried _ = []

||| Place a borrow argument still denotes: the variable, the
||| destinations of a pointer assignment (`f(q = malloc(), …)`), a
||| destination stored inside a call on that assignment's right-hand
||| side (`f(r = g(q = p), h(q))`), or a destination stored inside a
||| call, malloc, or use. The source is not included. `valuePlaces`
||| of a call stays empty.
public export
nestPlace : Expr -> List Place
nestPlace (EVar _ p _) = [p]
nestPlace (EAssign id p nm Ptr rhs) =
  nestAssigns (EAssign id p nm Ptr rhs) ++ nestBuried rhs
-- Copy assignment uses the rhs; it does not move it. `valuePlaces`
-- still denote that source, so `f(x = p, g(p))` is `nestedMixed`.
-- A destination stored inside a call on the rhs is appended, so
-- `f(x = g(r = p), h(r))` is `nestedMixed` too.
nestPlace (EAssign _ _ _ Copy rhs) = valuePlaces rhs ++ nestBuried rhs
nestPlace (ECall _ _ args) = nestStoreds args
nestPlace (EMalloc _ args) = nestStoreds args
nestPlace (EUse _ args) = nestStoreds args
nestPlace _ = []

||| A pointer assignment's borrow places are its destinations, then any
||| destination stored inside a call on the right-hand side.
export
nestPlaceAsgPtr : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  nestPlace (EAssign id dest nm Ptr rhs) =
    nestAssigns (EAssign id dest nm Ptr rhs) ++ nestBuried rhs
nestPlaceAsgPtr _ _ _ _ = Refl

||| `g(r = p)` exposes the destination, not the source.
export
nestPlaceCallDest :
  nestPlace (ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]) = [2]
nestPlaceCallDest = Refl

||| `g(p)` names no stored destination.
export
nestPlaceCallVar :
  nestPlace (ECall 0 "g" [EVar 1 2 "p"]) = []
nestPlaceCallVar = Refl

||| `g(h(r = p))` still exposes the destination.
export
nestPlaceCallNested :
  nestPlace (ECall 0 "g" [ECall 1 "h" [EAssign 2 3 "r" Ptr (EVar 4 5 "p")]]) = [3]
nestPlaceCallNested = Refl

||| A copy inside a call does not store a pointer destination.
export
nestPlaceCallCopy :
  nestPlace (ECall 0 "g" [EAssign 1 2 "x" Copy (EVar 3 4 "p")]) = []
nestPlaceCallCopy = Refl

||| `r = NULL` does not store a live pointer.
export
nestPlaceCallNull :
  nestPlace (ECall 0 "g" [EAssign 1 2 "r" Ptr (ENull 3)]) = []
nestPlaceCallNull = Refl

export
nestPlaceMallocDest :
  nestPlace (EMalloc 0 [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]) = [2]
nestPlaceMallocDest = Refl

export
nestPlaceUseDest :
  nestPlace (EUse 0 [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]) = [2]
nestPlaceUseDest = Refl

||| A call's `valuePlaces` stay empty, including when it stores a dest.
export
valuePlacesCallEmpty :
  valuePlaces (ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]) = []
valuePlacesCallEmpty = Refl

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

||| A borrow-only argument list (`malloc`, `use`, a builtin) stores an
||| existing pointer and a later argument frees that destination.
||| `nestBorrowPlaces` skips a consume argument, so `f(p, malloc(r = p, g(r)))`
||| with `g` consuming `r` has `nestedMixed` and `argsHit` of `p` both false
||| while `g` frees `p`. A fresh destination (`r = malloc()`) is not included.
||| A bare `malloc(p, g(p))` is not included either: that free names `p`,
||| which an outer `argsHit` already sees. `g(p, p = NULL)` is not this list.
public export
borrowHeldFrees : List (String, List Consume) -> List Expr -> Bool
borrowHeldFrees acc es = nestedGo acc (nestHelds es) es

public export
borrowHeldAt : List Expr -> Nat
borrowHeldAt [] = 0
borrowHeldAt (e :: _) = exprId e

public export
borrowHeldDiag : List Expr -> Diag
borrowHeldDiag es =
  MkDiag KUnproven
    "later argument frees a pointer stored by an earlier argument"
    (borrowHeldAt es) "freed here"
    []
    "a malloc, use, or builtin argument stores an existing pointer and a later argument frees that temporary"

||| `malloc(r = p, g(r))` where `g` consumes `r`.
export
borrowHeldFreesMallocDest :
  borrowHeldFrees [("g", [Always])]
    [ EAssign 1 2 "r" Ptr (EVar 3 4 "p")
    , ECall 5 "g" [EVar 6 2 "r"]
    ] = True
borrowHeldFreesMallocDest = Refl

||| A fresh cell stored and then freed is not an existing address.
export
borrowHeldFreesFresh :
  borrowHeldFrees [("g", [Always])]
    [ EAssign 1 2 "r" Ptr (EMalloc 3 [])
    , ECall 4 "g" [EVar 5 2 "r"]
    ] = False
borrowHeldFreesFresh = Refl

||| `malloc(p, g(p))` names no stored destination. The free of `p` is `argsHit`.
export
borrowHeldFreesBare :
  borrowHeldFrees [("g", [Always])]
    [ EVar 0 1 "p"
    , ECall 2 "g" [EVar 3 1 "p"]
    ] = False
borrowHeldFreesBare = Refl

||| Storing `p` without a later free of that destination.
export
borrowHeldFreesNoFree :
  borrowHeldFrees [("g", [Always])]
    [EAssign 1 2 "r" Ptr (EVar 3 4 "p")] = False
borrowHeldFreesNoFree = Refl

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

||| `f(p, g(r = p), h(r))`: `r` stays live after `g`, and `h` frees it.
export
nestedCallFreesDest :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , ECall 6 "h" [EVar 7 4 "r"]
    ]
    [Never, Never, Always] = True
nestedCallFreesDest = Refl

||| `f(g(p), h(p))`: the call names no stored destination.
export
nestedCallBareVar :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ ECall 0 "g" [EVar 1 2 "p"]
    , ECall 3 "h" [EVar 4 2 "p"]
    ]
    [Never, Always] = False
nestedCallBareVar = Refl

||| `f(g(r = p), r)`: the later argument moves `r`. It does not free it.
export
nestedCallMoveDest :
  nestedMixed
    (MkCtx [("g", [Never])] ["g"])
    [ ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    [Never, Always] = False
nestedCallMoveDest = Refl

||| Moving that dest is not `assignAlias` either (`valuePlaces` of the call is empty).
export
assignAliasMoveDest :
  assignAlias
    [ ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    [Never, Always] = False
assignAliasMoveDest = Refl

||| `f(p, g(r = p))`: nothing later frees `p` or `r`.
export
nestedCallNoFree :
  nestedMixed
    (MkCtx [("g", [Never])] ["g"])
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    ]
    [Never, Never] = False
nestedCallNoFree = Refl

||| `r = g(q = p)` exposes `q`, not `r` and not the source.
export
nestPlaceAssignCallDest :
  nestPlace (EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])) = [4]
nestPlaceAssignCallDest = Refl

||| `r = p` is only the destination.
export
nestPlaceAssignVar :
  nestPlace (EAssign 0 1 "r" Ptr (EVar 2 3 "p")) = [1]
nestPlaceAssignVar = Refl

||| `r = g(p)` names no stored destination.
export
nestPlaceAssignCallVar :
  nestPlace (EAssign 0 1 "r" Ptr (ECall 2 "g" [EVar 3 4 "p"])) = []
nestPlaceAssignCallVar = Refl

||| `r = g(h(q = p))` still exposes the inner destination.
export
nestPlaceAssignCallNested :
  nestPlace (EAssign 0 1 "r" Ptr
    (ECall 2 "g" [ECall 3 "h" [EAssign 4 5 "q" Ptr (EVar 6 7 "p")]])) = [5]
nestPlaceAssignCallNested = Refl

||| `r = g(q = NULL)` stores nothing live.
export
nestPlaceAssignCallNull :
  nestPlace (EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (ENull 5)])) = []
nestPlaceAssignCallNull = Refl

||| `r = malloc(q = p)` keeps both the fresh destination and the inner one.
export
nestPlaceAssignMallocDest :
  nestPlace (EAssign 0 1 "r" Ptr (EMalloc 2 [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])) = [1, 4]
nestPlaceAssignMallocDest = Refl

||| `use` does not yield a live pointer, so only the inner destination remains.
export
nestPlaceAssignUseDest :
  nestPlace (EAssign 0 1 "r" Ptr (EUse 2 [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])) = [4]
nestPlaceAssignUseDest = Refl

||| `x = g(r = p)` exposes `r`.
export
nestPlaceCopyCallDest :
  nestPlace (EAssign 0 1 "x" Copy (ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 6 "p")])) = [4]
nestPlaceCopyCallDest = Refl

||| `x = p` still denotes the source.
export
nestPlaceCopyVar :
  nestPlace (EAssign 0 1 "x" Copy (EVar 2 3 "p")) = [3]
nestPlaceCopyVar = Refl

||| `x = (r = g(q = p))` exposes `q`.
export
nestPlaceCopyPtrCall :
  nestPlace (EAssign 0 1 "x" Copy
    (EAssign 2 3 "r" Ptr (ECall 4 "g" [EAssign 5 6 "q" Ptr (EVar 7 8 "p")]))) = [6]
nestPlaceCopyPtrCall = Refl

||| `f(r = g(q = p), h(q))`: `q` stays live after `g`, and `h` frees it.
export
nestedAssignCallFrees :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , ECall 7 "h" [EVar 8 4 "q"]
    ]
    [Never, Always] = True
nestedAssignCallFrees = Refl

||| The same free under a Never-mode wrapper still counts.
export
nestedAssignCallWrapped :
  nestedMixed
    (MkCtx [("g", [Never]), ("k", [Never]), ("h", [Always])] ["g", "k", "h"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , ECall 7 "k" [ECall 8 "h" [EVar 9 4 "q"]]
    ]
    [Never, Never] = True
nestedAssignCallWrapped = Refl

||| `f(x = g(r = p), h(r))` frees the destination stored in the call.
export
nestedCopyCallFrees :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ EAssign 0 1 "x" Copy (ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 6 "p")])
    , ECall 7 "h" [EVar 8 4 "r"]
    ]
    [Never, Always] = True
nestedCopyCallFrees = Refl

||| `f(r = g(q = p), q)` moves `q`. It does not free it.
export
nestedAssignCallMove :
  nestedMixed
    (MkCtx [("g", [Never])] ["g"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , EVar 7 4 "q"
    ]
    [Never, Always] = False
nestedAssignCallMove = Refl

||| That move is not `assignAlias` (`valuePlaces` of the call is empty).
export
assignAliasAssignCallMove :
  assignAlias
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , EVar 7 4 "q"
    ]
    [Never, Always] = False
assignAliasAssignCallMove = Refl

||| `f(x = g(r = p), r)` moves the stored destination and does not free it.
export
nestedCopyCallMove :
  nestedMixed
    (MkCtx [("g", [Never])] ["g"])
    [ EAssign 0 1 "x" Copy (ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 6 "p")])
    , EVar 7 4 "r"
    ]
    [Never, Always] = False
nestedCopyCallMove = Refl

export
assignAliasCopyCallMove :
  assignAlias
    [ EAssign 0 1 "x" Copy (ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 6 "p")])
    , EVar 7 4 "r"
    ]
    [Never, Always] = False
assignAliasCopyCallMove = Refl

||| `f(r = g(p), h(p))`: a bare argument is not a stored destination.
export
nestedAssignCallBare :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EVar 3 4 "p"])
    , ECall 5 "h" [EVar 6 4 "p"]
    ]
    [Never, Always] = False
nestedAssignCallBare = Refl

||| `f(r = g(q = p), h(p))` frees the source, which is not a borrow place.
export
nestedAssignCallSource :
  nestedMixed
    (MkCtx [("g", [Never]), ("h", [Always])] ["g", "h"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , ECall 7 "h" [EVar 8 6 "p"]
    ]
    [Never, Always] = False
nestedAssignCallSource = Refl

||| `f(r = g(q = p))`: nothing later frees `q`.
export
nestedAssignCallNoFree :
  nestedMixed
    (MkCtx [("g", [Never])] ["g"])
    [ EAssign 0 1 "r" Ptr (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    ]
    [Never] = False
nestedAssignCallNoFree = Refl

||| `use(r = p)` hides the same store as a call.
export
nestedUseFreesDest :
  nestedMixed
    (MkCtx [("h", [Always])] ["h"])
    [ EVar 0 1 "p"
    , EUse 2 [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , ECall 6 "h" [EVar 7 4 "r"]
    ]
    [Never, Never, Always] = True
nestedUseFreesDest = Refl

||| Places the value of `e` is read from. A pointer assignment yields its
||| right-hand side, so the destination is not one of them: `r = malloc()`
||| yields the fresh cell, not whatever `r` held before.
public export
readPlaces : Expr -> List Place
readPlaces (EVar _ p _) = [p]
readPlaces (EAssign _ _ _ _ rhs) = readPlaces rhs
readPlaces _ = []

||| Drop every copy of `p`. An overwrite with a non-captured value must
||| not leave the old destination live.
public export
forgetPlace : Place -> List Place -> List Place
forgetPlace _ [] = []
forgetPlace p (q :: qs) = if p == q then forgetPlace p qs else q :: forgetPlace p qs

||| Keep `d` when `cap` says the right-hand side read a captured place.
public export
placeAfter : Place -> List Place -> Bool -> List Place
placeAfter d live True = d :: live
placeAfter d live False = forgetPlace d live

mutual
  ||| Places that hold an address already captured by an earlier borrow,
  ||| after evaluating `e`. A store from a captured place makes the
  ||| destination captured. A store from anywhere else overwrites it.
  public export
  xferLive : List Place -> Expr -> List Place
  xferLive live (EAssign _ d _ Ptr rhs) =
    placeAfter d (xferLive live rhs)
      (placesOverlap (readPlaces rhs) (xferLive live rhs))
  xferLive live (EAssign _ _ _ Copy rhs) = xferLive live rhs
  xferLive live (ECall _ _ args) = xferArgs live args
  xferLive live (EMalloc _ args) = xferArgs live args
  xferLive live (EUse _ args) = xferArgs live args
  xferLive live _ = live

  public export
  xferArgs : List Place -> List Expr -> List Place
  xferArgs live [] = live
  xferArgs live (e :: es) = xferArgs (xferLive live e) es

mutual
  ||| Overlap flag for one consume. `True` means this argument reads a
  ||| captured place. `False` continues with that argument's stores only.
  public export
  storedOn : List (String, List Consume) -> Bool -> List Place -> Expr ->
             List Expr -> List Consume -> Bool
  storedOn _ True _ _ _ _ = True
  storedOn acc False live e es ms = storedLiveGo acc (xferLive live e) es ms

  ||| Non-consume head. `True` means this argument frees a place `live`
  ||| still holds. `False` continues with the places this head captured.
  public export
  storedFree : List (String, List Consume) -> Bool -> List Place -> Expr ->
               List Expr -> List Consume -> Bool
  storedFree _ True _ _ _ _ = True
  storedFree acc False live e es ms =
    storedLiveGo acc (valuePlaces e ++ xferLive live e) es ms

  ||| `True` when a consume reads a place that holds an address captured by
  ||| an earlier borrow, or a non-consume argument frees a place the running
  ||| live set still holds. `live` is empty at the start of a call. Borrow
  ||| arguments add `valuePlaces` (the address just captured, including a
  ||| fresh `q = malloc()`) and any destination a nested store copied a
  ||| captured address into. `f(g(r = p), r)` stays accepted: nothing before
  ||| `g` captured `p`, so `r` is not live when it is consumed. Overwriting
  ||| with `r = malloc()` drops `r`, so a later free of that name is the
  ||| fresh cell. `f(r = p, malloc(s = r), g(s))` is rejected: after the
  ||| malloc, `s` is still live and `g` frees it.
  public export
  storedLiveGo : List (String, List Consume) -> List Place -> List Expr ->
                 List Consume -> Bool
  storedLiveGo _ _ [] _ = False
  storedLiveGo acc live (e :: es) [] =
    storedOn acc (placesOverlap (readPlaces e) live) live e es []
  storedLiveGo acc live (e :: es) (m :: ms) =
    case doesConsume m of
      False =>
        storedFree acc (nestedGo acc live [e]) live e es ms
      True =>
        storedOn acc (placesOverlap (readPlaces e) live) live e es ms

||| `storedLiveGo` from an empty capture set. `acc` is the callee summaries
||| `argFrees` reads; a missing name is all-Never.
public export
storedBorrowConsume : List (String, List Consume) -> List Expr -> List Consume -> Bool
storedBorrowConsume acc es ms = storedLiveGo acc [] es ms

mutual
  ||| Per-argument write and read places. `W` is stores, nested callee
  ||| consumes, and nested frees. `R` is every place the expression may
  ||| read. Nested `ECall` uses `calleeModes` (prototype `realloc` is
  ||| `[Always]`). Consume-mode arguments additionally treat every place
  ||| the argument reads or denotes as written (`argModeFoot`).
  public export
  argFootprint : List (String, List Consume) -> Expr -> (List Place, List Place)
  argFootprint acc (EVar _ p _) = ([], [p])
  argFootprint acc (EAssign _ d _ Ptr rhs) =
    (d :: fst (argFootprint acc rhs), snd (argFootprint acc rhs))
  argFootprint acc (EAssign _ _ _ Copy rhs) = argFootprint acc rhs
  argFootprint acc (ECall _ callee args) =
    argsCallFoot acc args (calleeModes acc callee)
  argFootprint acc (EMalloc _ args) = argsEvalFoot acc args
  argFootprint acc (EUse _ args) = argsEvalFoot acc args
  argFootprint _ (ELit _) = ([], [])
  argFootprint _ (ENull _) = ([], [])
  argFootprint _ (EUnsupported _ _) = ([], [])

  ||| Union of evaluation footprints. No extra consume: `malloc` / `use`
  ||| borrow every argument. Nested calls still consume via `ECall`.
  public export
  argsEvalFoot : List (String, List Consume) -> List Expr ->
                 (List Place, List Place)
  argsEvalFoot _ [] = ([], [])
  argsEvalFoot acc (e :: es) =
    (fst (argFootprint acc e) ++ fst (argsEvalFoot acc es),
     snd (argFootprint acc e) ++ snd (argsEvalFoot acc es))

  ||| Evaluation footprints plus this callee's consume of each argument.
  public export
  argsCallFoot : List (String, List Consume) -> List Expr -> List Consume ->
                 (List Place, List Place)
  argsCallFoot _ [] _ = ([], [])
  argsCallFoot acc (e :: es) ms =
    (fst (argModeFoot acc e (consumeHead ms)) ++
       fst (argsCallFoot acc es (consumeTail ms)),
     snd (argModeFoot acc e (consumeHead ms)) ++
       snd (argsCallFoot acc es (consumeTail ms)))

  ||| One argument at a call: consume-mode writes everything the
  ||| expression reads or denotes; borrow-mode adds those denotations
  ||| to the read set only. `fst` / `snd` so a `Never`/`May`/`Always`
  ||| split reduces; a `let (w, r) = argFootprint` does not.
  public export
  argModeFoot : List (String, List Consume) -> Expr -> Consume ->
                (List Place, List Place)
  argModeFoot acc e m =
    if doesConsume m
      then (fst (argFootprint acc e) ++ snd (argFootprint acc e) ++
              valuePlaces e,
            snd (argFootprint acc e))
      else (fst (argFootprint acc e),
            snd (argFootprint acc e) ++ valuePlaces e)

||| `(W_i, R_i)` for each argument of a call with these modes.
public export
callFoots : List (String, List Consume) -> List Expr -> List Consume ->
            List (List Place, List Place)
callFoots _ [] _ = []
callFoots acc (e :: es) ms =
  argModeFoot acc e (consumeHead ms) :: callFoots acc es (consumeTail ms)

||| Union of every argument's write set.
public export
footsWrites : List (List Place, List Place) -> List Place
footsWrites [] = []
footsWrites ((w, _) :: fs) = w ++ footsWrites fs

||| `W ∩ (R ∪ W')` for one pair, then the rest of the list.
public export
footHits : (List Place, List Place) -> List (List Place, List Place) -> Bool
footHits _ [] = False
footHits (w, r) ((w2, r2) :: rest) =
  placesOverlap w (r2 ++ w2) || placesOverlap w2 (r ++ w) ||
    footHits (w, r) rest

||| Some pair `i ≠ j` has `W_i ∩ (R_j ∪ W_j) ≠ ∅`. Order-independent.
public export
footsOverlap : List (List Place, List Place) -> Bool
footsOverlap [] = False
footsOverlap (f :: fs) = footHits f fs || footsOverlap fs

||| True when the call's argument footprints are not pairwise disjoint.
public export
callOverlap : List (String, List Consume) -> List Expr -> List Consume -> Bool
callOverlap acc es ms = footsOverlap (callFoots acc es ms)

||| The C11 §6.5p2 / post-call aliasing accept condition.
public export
callDisjoint : List (String, List Consume) -> List Expr -> List Consume -> Bool
callDisjoint acc es ms = not (callOverlap acc es ms)

--------------------------------------------------------------------------------
-- Inductive image of the footprint functions
--------------------------------------------------------------------------------

mutual
  ||| Inductive image of `argFootprint`. Frame lemmas induct on `Foot`
  ||| (or on `HEvalExpr`) instead of computing through the pair-returning
  ||| functions, so proofs stay out of `with`.
  public export
  data Foot : List (String, List Consume) -> Expr ->
              (w : List Place) -> (r : List Place) -> Type where
    FVar : Foot acc (EVar nid p nm) [] [p]
    FAsgPtr : (w, r : List Place) -> Foot acc rhs w r ->
              Foot acc (EAssign nid d nm Ptr rhs) (d :: w) r
    FAsgCopy : (w, r : List Place) -> Foot acc rhs w r ->
               Foot acc (EAssign nid n nm Copy rhs) w r
    FCall : (w, r : List Place) ->
            CallFoot acc args (calleeModes acc callee) w r ->
            Foot acc (ECall nid callee args) w r
    FMalloc : (w, r : List Place) -> EvalFoot acc args w r ->
              Foot acc (EMalloc mid args) w r
    FUse : (w, r : List Place) -> EvalFoot acc args w r ->
           Foot acc (EUse uid args) w r
    FLit : Foot acc (ELit n) [] []
    FNull : Foot acc (ENull nid) [] []
    FUnsup : Foot acc (EUnsupported nid reason) [] []

  ||| Inductive image of `argsEvalFoot`.
  public export
  data EvalFoot : List (String, List Consume) -> List Expr ->
                  (w : List Place) -> (r : List Place) -> Type where
    EFNil : EvalFoot acc [] [] []
    EFCons : (w, r, ws, rs : List Place) ->
             Foot acc e w r -> EvalFoot acc es ws rs ->
             EvalFoot acc (e :: es) (w ++ ws) (r ++ rs)

  ||| Inductive image of `argModeFoot`.
  public export
  data ModeFoot : List (String, List Consume) -> Expr -> Consume ->
                  (w : List Place) -> (r : List Place) -> Type where
    MFConsume : (w0, r0 : List Place) ->
                doesConsume m = True ->
                Foot acc e w0 r0 ->
                ModeFoot acc e m (w0 ++ r0 ++ valuePlaces e) r0
    MFBorrow : (w0, r0 : List Place) ->
               doesConsume m = False ->
               Foot acc e w0 r0 ->
               ModeFoot acc e m w0 (r0 ++ valuePlaces e)

  ||| Inductive image of `argsCallFoot`.
  public export
  data CallFoot : List (String, List Consume) -> List Expr ->
                  List Consume -> (w : List Place) -> (r : List Place) -> Type where
    CFNil : CallFoot acc [] ms [] []
    CFCons : (w, r, ws, rs : List Place) ->
             ModeFoot acc e (consumeHead ms) w r ->
             CallFoot acc es (consumeTail ms) ws rs ->
             CallFoot acc (e :: es) ms (w ++ ws) (r ++ rs)

mutual
  ||| Soundness: a `Foot` tree names the lists `argFootprint` computes.
  export
  footSound : {acc : List (String, List Consume)} -> {e : Expr} ->
              {w, r : List Place} ->
              Foot acc e w r -> argFootprint acc e = (w, r)
  footSound FVar = Refl
  footSound (FAsgPtr {d} w r ft) =
    replace {p = \wr => (d :: fst wr, snd wr) = (d :: w, r)}
      (sym (footSound ft)) Refl
  footSound (FAsgCopy _ _ ft) = footSound ft
  footSound (FCall _ _ cf) = callFootSound cf
  footSound (FMalloc _ _ ef) = evalFootSound ef
  footSound (FUse _ _ ef) = evalFootSound ef
  footSound FLit = Refl
  footSound FNull = Refl
  footSound FUnsup = Refl

  export
  evalFootSound : {acc : List (String, List Consume)} ->
                  {es : List Expr} -> {w, r : List Place} ->
                  EvalFoot acc es w r -> argsEvalFoot acc es = (w, r)
  evalFootSound EFNil = Refl
  evalFootSound (EFCons {e} {es} w r ws rs ft ef) =
    replace {p = \wr => (fst wr ++ fst (argsEvalFoot acc es),
                         snd wr ++ snd (argsEvalFoot acc es)) = (w ++ ws, r ++ rs)}
      (sym (footSound ft))
      (replace {p = \wr => (w ++ fst wr, r ++ snd wr) = (w ++ ws, r ++ rs)}
         (sym (evalFootSound ef)) Refl)

  export
  modeFootSound : {acc : List (String, List Consume)} ->
                  {e : Expr} -> {m : Consume} -> {w, r : List Place} ->
                  ModeFoot acc e m w r -> argModeFoot acc e m = (w, r)
  modeFootSound {m = Never} (MFConsume _ _ pc _) =
    void (falseNotTrue pc)
  modeFootSound {m = May} {e} (MFConsume w0 r0 _ ft) =
    replace {p = \wr => (fst wr ++ snd wr ++ valuePlaces e, snd wr) =
                          (w0 ++ r0 ++ valuePlaces e, r0)}
      (sym (footSound ft)) Refl
  modeFootSound {m = Always} {e} (MFConsume w0 r0 _ ft) =
    replace {p = \wr => (fst wr ++ snd wr ++ valuePlaces e, snd wr) =
                          (w0 ++ r0 ++ valuePlaces e, r0)}
      (sym (footSound ft)) Refl
  modeFootSound {m = Never} {e} (MFBorrow w0 r0 _ ft) =
    replace {p = \wr => (fst wr, snd wr ++ valuePlaces e) =
                          (w0, r0 ++ valuePlaces e)}
      (sym (footSound ft)) Refl
  modeFootSound {m = May} (MFBorrow _ _ pc _) =
    void (falseNotTrue (sym pc))
  modeFootSound {m = Always} (MFBorrow _ _ pc _) =
    void (falseNotTrue (sym pc))

  export
  callFootSound : {acc : List (String, List Consume)} ->
                  {es : List Expr} -> {ms : List Consume} ->
                  {w, r : List Place} ->
                  CallFoot acc es ms w r -> argsCallFoot acc es ms = (w, r)
  callFootSound CFNil = Refl
  callFootSound (CFCons {e} {es} {ms} w r ws rs mf cf) =
    replace {p = \wr => (fst wr ++ fst (argsCallFoot acc es (consumeTail ms)),
                         snd wr ++ snd (argsCallFoot acc es (consumeTail ms))) =
                          (w ++ ws, r ++ rs)}
      (sym (modeFootSound mf))
      (replace {p = \wr => (w ++ fst wr, r ++ snd wr) = (w ++ ws, r ++ rs)}
         (sym (callFootSound cf)) Refl)

mutual
  ||| Completeness: `argFootprint` yields a `Foot` tree.
  export
  footOf : (acc : List (String, List Consume)) -> (e : Expr) ->
           Foot acc e (fst (argFootprint acc e)) (snd (argFootprint acc e))
  footOf acc (EVar _ p _) = FVar
  footOf acc (EAssign _ d _ Ptr rhs) =
    FAsgPtr (fst (argFootprint acc rhs)) (snd (argFootprint acc rhs))
      (footOf acc rhs)
  footOf acc (EAssign _ _ _ Copy rhs) =
    FAsgCopy (fst (argFootprint acc rhs)) (snd (argFootprint acc rhs))
      (footOf acc rhs)
  footOf acc (ECall _ callee args) =
    FCall (fst (argsCallFoot acc args (calleeModes acc callee)))
          (snd (argsCallFoot acc args (calleeModes acc callee)))
          (callFootOf acc args (calleeModes acc callee))
  footOf acc (EMalloc _ args) =
    FMalloc (fst (argsEvalFoot acc args)) (snd (argsEvalFoot acc args))
      (evalFootOf acc args)
  footOf acc (EUse _ args) =
    FUse (fst (argsEvalFoot acc args)) (snd (argsEvalFoot acc args))
      (evalFootOf acc args)
  footOf acc (ELit _) = FLit
  footOf acc (ENull _) = FNull
  footOf acc (EUnsupported _ _) = FUnsup

  export
  evalFootOf : (acc : List (String, List Consume)) -> (es : List Expr) ->
               EvalFoot acc es (fst (argsEvalFoot acc es))
                               (snd (argsEvalFoot acc es))
  evalFootOf _ [] = EFNil
  evalFootOf acc (e :: es) =
    EFCons (fst (argFootprint acc e)) (snd (argFootprint acc e))
           (fst (argsEvalFoot acc es)) (snd (argsEvalFoot acc es))
           (footOf acc e) (evalFootOf acc es)

  export
  modeFootOf : (acc : List (String, List Consume)) -> (e : Expr) ->
               (m : Consume) ->
               ModeFoot acc e m (fst (argModeFoot acc e m))
                                (snd (argModeFoot acc e m))
  modeFootOf acc e Never =
    MFBorrow (fst (argFootprint acc e)) (snd (argFootprint acc e))
      Refl (footOf acc e)
  modeFootOf acc e May =
    MFConsume (fst (argFootprint acc e)) (snd (argFootprint acc e))
      Refl (footOf acc e)
  modeFootOf acc e Always =
    MFConsume (fst (argFootprint acc e)) (snd (argFootprint acc e))
      Refl (footOf acc e)

  export
  callFootOf : (acc : List (String, List Consume)) -> (es : List Expr) ->
               (ms : List Consume) ->
               CallFoot acc es ms (fst (argsCallFoot acc es ms))
                                  (snd (argsCallFoot acc es ms))
  callFootOf _ [] _ = CFNil
  callFootOf acc (e :: es) ms =
    CFCons (fst (argModeFoot acc e (consumeHead ms)))
           (snd (argModeFoot acc e (consumeHead ms)))
           (fst (argsCallFoot acc es (consumeTail ms)))
           (snd (argsCallFoot acc es (consumeTail ms)))
           (modeFootOf acc e (consumeHead ms))
           (callFootOf acc es (consumeTail ms))

||| Inversion the frame lemmas use: a computed pair is a `Foot` tree.
export
footFrom : {acc : List (String, List Consume)} -> {e : Expr} ->
           {w, r : List Place} ->
           argFootprint acc e = (w, r) -> Foot acc e w r
footFrom {acc} {e} eq =
  replace {p = \wr => Foot acc e (fst wr) (snd wr)} eq (footOf acc e)

||| Write set of `n = use(n = x)` is `[n, n]`. The owner intern `x` is
||| only in `R`, so a borrow `nin` of `W` holds while the inner assign
||| destOwns onto `n` and the outer Ghost store sets `n` to `AEmpty`.
export
nestedUseAssignWrites :
  fst (argFootprint [] (EAssign 0 1 "n" Ptr
        (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")]))) = 1 :: 1 :: []
nestedUseAssignWrites = Refl

export
nestedUseAssignMissesOwner :
  placeIn 2 (fst (argFootprint [] (EAssign 0 1 "n" Ptr
        (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])))) = False
nestedUseAssignMissesOwner = Refl

export
nestedUseAssignReadsOwner :
  snd (argFootprint [] (EAssign 0 1 "n" Ptr
        (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")]))) = 2 :: []
nestedUseAssignReadsOwner = Refl

export
evalFootFrom : {acc : List (String, List Consume)} -> {es : List Expr} ->
               {w, r : List Place} ->
               argsEvalFoot acc es = (w, r) -> EvalFoot acc es w r
evalFootFrom {acc} {es} eq =
  replace {p = \wr => EvalFoot acc es (fst wr) (snd wr)} eq (evalFootOf acc es)

export
modeFootFrom : {acc : List (String, List Consume)} -> {e : Expr} ->
               {m : Consume} -> {w, r : List Place} ->
               argModeFoot acc e m = (w, r) -> ModeFoot acc e m w r
modeFootFrom {acc} {e} {m} eq =
  replace {p = \wr => ModeFoot acc e m (fst wr) (snd wr)} eq
    (modeFootOf acc e m)

export
callFootFrom : {acc : List (String, List Consume)} -> {es : List Expr} ->
               {ms : List Consume} -> {w, r : List Place} ->
               argsCallFoot acc es ms = (w, r) -> CallFoot acc es ms w r
callFootFrom {acc} {es} {ms} eq =
  replace {p = \wr => CallFoot acc es ms (fst wr) (snd wr)} eq
    (callFootOf acc es ms)

||| First argument whose `W` meets another argument's `R ∪ W`.
public export
overlapArg : List Expr -> List (List Place, List Place) -> Expr
overlapArg [] _ = EUnsupported 0 "mixed alias"
overlapArg (e :: _) [] = e
overlapArg (e :: es) (f :: fs) =
  if footHits f fs then e else overlapArg es fs

||| True when the call aliases a write with another argument's read or
||| write. The structural, order-independent footprint rule replaces
||| `mixedAlias` / `nestedMixed` / `assignAlias` at `checkCall`.
||| `storedBorrowConsume` stays as a disjunct so Restore can still read
||| empty-start `storedLiveGo` off `aliasBad = False` until
||| `storedQuietFromFoots` lands. The four `storedBorrowConsume = True`
||| shapes already have `callOverlap = True`. It does not accept anything
||| the footprint rule rejects.
public export
aliasBad : Ctx -> List Expr -> String -> Bool
aliasBad ctx args callee =
  callOverlap ctx.summaries args (funModes ctx callee)
    || storedBorrowConsume ctx.summaries args (funModes ctx callee)

||| `f(p, malloc(r = p, g(r)))` with modes `[Never, Always]`. The malloc
||| argument reads `p` and frees `r`; consume-mode writes those reads, so
||| the borrow of `p` overlaps. Previously only `checkArgsBorrow` rejected.
export
mallocHeldOuterAlias :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Always])] ["f", "g"])
    [ EVar 0 1 "p"
    , EMalloc 2
        [ EAssign 3 4 "r" Ptr (EVar 5 1 "p")
        , ECall 6 "g" [EVar 7 4 "r"]
        ]
    ]
    "f" = True
mallocHeldOuterAlias = Refl

||| `g(p, p = NULL)`: the assignment writes `p` unsequenced with the
||| other argument's read of `p` (C11 §6.5p2). Previously accepted.
export
nullAssignNotAlias :
  aliasBad
    (MkCtx [("g", [Never, Never])] ["g"])
    [ EVar 0 1 "p"
    , EAssign 2 1 "p" Ptr (ENull 3)
    ]
    "g" = True
nullAssignNotAlias = Refl

||| `f(p, g(r = p), r)`: an earlier borrow captured `p`, `g` copies it into
||| `r`, and the last argument consumes `r`. The frame would hold that
||| address twice.
export
storedBorrowConsumeCopy :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Never, Always] = True
storedBorrowConsumeCopy = Refl

export
storedBorrowAlias :
  aliasBad
    (MkCtx [("f", [Never, Never, Always]), ("g", [Never])] ["f", "g"])
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    "f" = True
storedBorrowAlias = Refl

||| The copy can sit in a consume-position argument. The frame still
||| borrows `p` and then owns `r`.
export
storedBorrowConsumeMid :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Always, Always] = True
storedBorrowConsumeMid = Refl

||| `f(p, malloc(r = p), r)` is the same copy when `malloc` is borrowed.
export
storedBorrowMallocBorrow :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , EMalloc 2 [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Never, Always] = True
storedBorrowMallocBorrow = Refl

||| `f(q = p, g(r = q), r)`: the first borrow's destination holds `p`.
export
storedBorrowViaDest :
  storedBorrowConsume []
    [ EAssign 0 1 "q" Ptr (EVar 2 3 "p")
    , ECall 4 "g" [EAssign 5 6 "r" Ptr (EVar 7 1 "q")]
    , EVar 8 6 "r"
    ]
    [Never, Never, Always] = True
storedBorrowViaDest = Refl

||| The four `storedBorrowConsume = True` shapes above are also
||| `callOverlap`: a later write meets an earlier write or read. If any
||| of these were `False`, empty-start `storedLiveGo` would be independent
||| of the footprint rule.
export
storedBorrowCopyOverlaps :
  callOverlap []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Never, Always] = True
storedBorrowCopyOverlaps = Refl

export
storedBorrowMidOverlaps :
  callOverlap []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Always, Always] = True
storedBorrowMidOverlaps = Refl

export
storedBorrowMallocOverlaps :
  callOverlap []
    [ EVar 0 1 "p"
    , EMalloc 2 [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EVar 6 4 "r"
    ]
    [Never, Never, Always] = True
storedBorrowMallocOverlaps = Refl

export
storedBorrowViaDestOverlaps :
  callOverlap []
    [ EAssign 0 1 "q" Ptr (EVar 2 3 "p")
    , ECall 4 "g" [EAssign 5 6 "r" Ptr (EVar 7 1 "q")]
    , EVar 8 6 "r"
    ]
    [Never, Never, Always] = True
storedBorrowViaDestOverlaps = Refl

||| Completeness of `Foot` at a variable and a pointer store.
export
footOfVar : footOf [] (EVar 0 1 "p") = FVar
footOfVar = Refl

export
footOfPtrAssign :
  footOf [] (EAssign 0 1 "r" Ptr (EVar 2 3 "p")) = FAsgPtr [] [3] FVar
footOfPtrAssign = Refl

||| Soundness of `Foot` agrees with `argFootprint` on those shapes.
export
footSoundVar : argFootprint [] (EVar 0 1 "p") = ([], [1])
footSoundVar = footSound (footOf [] (EVar 0 1 "p"))

export
footSoundPtrAssign :
  argFootprint [] (EAssign 0 1 "r" Ptr (EVar 2 3 "p")) = ([1], [3])
footSoundPtrAssign = footSound (footOf [] (EAssign 0 1 "r" Ptr (EVar 2 3 "p")))

||| `f(g(r = p), r)`: no earlier borrow captured `p`. The only frame copy
||| of that address is the consume. `storedBorrowConsume` stays false;
||| the footprint rule rejects the unsequenced store of `r` with the
||| later consume of `r`.
export
storedBorrowMoveDest :
  storedBorrowConsume []
    [ ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    [Never, Always] = False
storedBorrowMoveDest = Refl

export
storedBorrowMoveAlias :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Never])] ["f", "g"])
    [ ECall 0 "g" [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    "f" = True
storedBorrowMoveAlias = Refl

||| `g(p, p)` with Never then Always: the consume writes `p`, the borrow
||| reads it.
export
footprintDupVar :
  aliasBad
    (MkCtx [("g", [Never, Always])] ["g"])
    [ EVar 0 1 "p"
    , EVar 2 1 "p"
    ]
    "g" = True
footprintDupVar = Refl

||| `f(q = malloc(), q)`: the assignment writes `q`, the consume writes
||| and reads `q`.
export
footprintAssignMalloc :
  aliasBad
    (MkCtx [("f", [Never, Always])] ["f"])
    [ EAssign 0 1 "q" Ptr (EMalloc 2 [])
    , EVar 3 1 "q"
    ]
    "f" = True
footprintAssignMalloc = Refl

||| `f(r = g(q = p), h(q))`: `g` stores `q`, `h` frees `q`.
export
footprintNestedStoreFree :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Never]), ("h", [Always])]
           ["f", "g", "h"])
    [ EAssign 0 1 "r" Ptr
        (ECall 2 "g" [EAssign 3 4 "q" Ptr (EVar 5 6 "p")])
    , ECall 7 "h" [EVar 8 4 "q"]
    ]
    "f" = True
footprintNestedStoreFree = Refl

||| Distinct owners: `f(q = malloc(), p)` stays disjoint.
export
footprintAssignDistinct :
  aliasBad
    (MkCtx [("f", [Never, Always])] ["f"])
    [ EAssign 0 1 "q" Ptr (EMalloc 2 [])
    , EVar 3 4 "p"
    ]
    "f" = False
footprintAssignDistinct = Refl

||| `f(g(p), h(q))` with distinct places stays disjoint.
export
footprintNestedDistinct :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Never]), ("h", [Always])]
           ["f", "g", "h"])
    [ ECall 0 "g" [EVar 1 2 "p"]
    , ECall 3 "h" [EVar 4 5 "q"]
    ]
    "f" = False
footprintNestedDistinct = Refl

||| `f(g(p), p)`: the borrow argument reads `p`, the consume writes it.
||| Conservative: `g`'s result may alias `p`. Previously accepted.
export
footprintCallThenVar :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Never])] ["f", "g"])
    [ ECall 0 "g" [EVar 1 2 "p"]
    , EVar 3 2 "p"
    ]
    "f" = True
footprintCallThenVar = Refl

||| `f(g(p), h(p))` with `h` Always: evaluating `h(p)` frees `p` while
||| `g(p)` reads it. Previously `nestedMixed` / `aliasBad` both false.
export
footprintNestedBare :
  aliasBad
    (MkCtx [("f", [Never, Always]), ("g", [Never]), ("h", [Always])]
           ["f", "g", "h"])
    [ ECall 0 "g" [EVar 1 2 "p"]
    , ECall 3 "h" [EVar 4 2 "p"]
    ]
    "f" = True
footprintNestedBare = Refl

||| `f(malloc(r = p), r)`: `r` is stored under malloc, then consumed.
export
footprintMallocStoreConsume :
  aliasBad
    (MkCtx [("f", [Never, Always])] ["f"])
    [ EMalloc 0 [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    "f" = True
footprintMallocStoreConsume = Refl

||| Empty argument list.
export
footprintNil :
  aliasBad (MkCtx [("f", [Never])] ["f"]) [] "f" = False
footprintNil = Refl

||| `f(malloc(r = p), r)`: `malloc` returns a fresh cell, not `p`.
export
storedBorrowMallocOnly :
  storedBorrowConsume []
    [ EMalloc 0 [EAssign 1 2 "r" Ptr (EVar 3 4 "p")]
    , EVar 5 2 "r"
    ]
    [Never, Always] = False
storedBorrowMallocOnly = Refl

||| Nothing later consumes the copy.
export
storedBorrowNoConsume :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    ]
    [Never, Never] = False
storedBorrowNoConsume = Refl

||| `r = malloc()` overwrites the copy. A later consume of `r` is the
||| fresh cell.
export
storedBorrowOverwrite :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , ECall 2 "g" [EAssign 3 4 "r" Ptr (EVar 5 1 "p")]
    , EAssign 6 4 "r" Ptr (EMalloc 7 [])
    ]
    [Never, Never, Always] = False
storedBorrowOverwrite = Refl

||| `p = NULL` drops `p` from the captured set.
export
storedBorrowNull :
  storedBorrowConsume []
    [ EVar 0 1 "p"
    , EAssign 2 1 "p" Ptr (ENull 3)
    ]
    [Never, Never] = False
storedBorrowNull = Refl

||| `f(r = p, malloc(s = r), g(s))` with `f` at `[Never, Always, Never]`
||| and `g` at `[Always]`. `s` receives the address held in `r`, and `g`
||| frees `s` while the arguments are still being evaluated.
export
storedLiveFreesAlias :
  aliasBad
    (MkCtx [("f", [Never, Always, Never]), ("g", [Always])] ["f", "g"])
    [ EAssign 1 4 "r" Ptr (EVar 2 1 "p")
    , EMalloc 3 [EAssign 4 8 "s" Ptr (EVar 5 4 "r")]
    , ECall 6 "g" [EVar 7 8 "s"]
    ]
    "f" = True
storedLiveFreesAlias = Refl

||| `f(r = p, r = malloc(), g(r))`. Two unsequenced writes of `r`, and
||| `g` frees `r`. The order-sensitive overwrite analysis accepted this;
||| the footprint rule rejects it.
export
storedLiveOverwriteAlias :
  aliasBad
    (MkCtx [("f", [Always, Always, Never]), ("g", [Always])] ["f", "g"])
    [ EAssign 1 4 "r" Ptr (EVar 2 1 "p")
    , EAssign 3 4 "r" Ptr (EMalloc 5 [])
    , ECall 6 "g" [EVar 7 4 "r"]
    ]
    "f" = True
storedLiveOverwriteAlias = Refl

||| The same overwrite, starting from the live set `r = p` captured.
||| The consume drops `r` before the free.
export
storedLiveOverwriteForget :
  storedLiveGo [("g", [Always])] [4, 1]
    [ EAssign 3 4 "r" Ptr (EMalloc 5 [])
    , ECall 6 "g" [EVar 7 4 "r"]
    ]
    [Always, Never] = False
storedLiveOverwriteForget = Refl

export
storedLiveOverwriteHeld :
  borrowHeldFrees [("g", [Always])]
    [ EAssign 1 4 "r" Ptr (EVar 2 1 "p")
    , EAssign 3 4 "r" Ptr (EMalloc 5 [])
    , ECall 6 "g" [EVar 7 4 "r"]
    ] = True
storedLiveOverwriteHeld = Refl

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

||| A Ghost `takeOwner` of the rhs stores `AEmpty` at the dest. Combined
||| with an inner destOwn onto `n`, Own of the source cell is dropped.
export
nestedGhostStoreEmpty :
  {sc : Scopes} ->
  takeAssignPtrFrom 0 1 "n" (Right (sc, Ghost)) =
    Right (setPlace 1 (Pagurus.Status.singleton AEmpty) sc, Ghost)
nestedGhostStoreEmpty = Refl

export
nestedGhostAssignEmpty :
  {sc : Scopes} ->
  assignPtrFrom False 0 1 "n" (Right (sc, Ghost)) =
    Right (setPlace 1 (Pagurus.Status.singleton AEmpty) sc)
nestedGhostAssignEmpty = Refl

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
      Ptr => case ghostCopyLeak rhs of
        True => Left (ghostCopyDiag id nm)
        False => takeAssignPtrFrom id n nm (takeOwner ctx sc rhs)
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
      Ptr => case ghostCopyLeak rhs of
        True => Left (ghostCopyDiag id nm)
        False => assignPtrFrom asMove id n nm (takeOwner ctx sc rhs)

  public export
  argsBorrowFrom : Ctx -> List Expr -> Either Diag Scopes -> Either Diag Scopes
  argsBorrowFrom _ _ (Left d) = Left d
  argsBorrowFrom ctx es (Right sc') = checkArgsBorrow ctx sc' es

  export
  checkArgsBorrow : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkArgsBorrow _ sc [] = Right sc
  checkArgsBorrow ctx sc (e :: es) =
    if borrowHeldFrees ctx.summaries (e :: es)
      then Left (borrowHeldDiag (e :: es))
      else argsBorrowFrom ctx es (checkExpr ctx sc e)

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
  definedCallFrom True ctx _ nid callee args modes =
    Left (mixedAliasDiag nid callee (overlapArg args (callFoots ctx.summaries args modes)))
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
          Just e => case ghostCopyLeak e of
            True => Left (ghostCopyDiag id nm)
            False => declPtrFrom id n nm (takeOwner ctx sc e)
  checkStmt (S fuel) ctx sc (SAssign id n nm ty rhs) =
    case ty of
      Copy => checkExpr ctx sc rhs
      Ptr => case ghostCopyLeak rhs of
        True => Left (ghostCopyDiag id nm)
        False => stmtAsgPtrFrom n (takeOwner ctx sc rhs)
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

placesOverlapNil : (ps : List Place) -> placesOverlap ps [] = False
placesOverlapNil [] = Refl
placesOverlapNil (_ :: ps) = placesOverlapNil ps

mutual
  xferEmpty : (e : Expr) -> xferLive [] e = []
  xferEmpty (ELit _) = Refl
  xferEmpty (ENull _) = Refl
  xferEmpty (EVar _ _ _) = Refl
  xferEmpty (EUnsupported _ _) = Refl
  xferEmpty (EAssign _ _ _ Ptr rhs) =
    rewrite xferEmpty rhs in
      rewrite placesOverlapNil (readPlaces rhs) in
        Refl
  xferEmpty (EAssign _ _ _ Copy rhs) = xferEmpty rhs
  xferEmpty (ECall _ _ args) = xferArgsEmpty args
  xferEmpty (EMalloc _ args) = xferArgsEmpty args
  xferEmpty (EUse _ args) = xferArgsEmpty args

  xferArgsEmpty : (es : List Expr) -> xferArgs [] es = []
  xferArgsEmpty [] = Refl
  xferArgsEmpty (e :: es) =
    rewrite xferEmpty e in xferArgsEmpty es

storedLiveGoNil : (acc : List (String, List Consume)) -> (es : List Expr) ->
  storedLiveGo acc [] es [] = False
storedLiveGoNil _ [] = Refl
storedLiveGoNil acc (e :: es) =
  rewrite placesOverlapNil (readPlaces e) in
    rewrite xferEmpty e in
      storedLiveGoNil acc es

export
storedBorrowConsumeNil : (acc : List (String, List Consume)) -> (es : List Expr) ->
  storedBorrowConsume acc es [] = False
storedBorrowConsumeNil acc es = storedLiveGoNil acc es

||| Empty argument list: no pair to overlap. Nonempty extras with
||| `funModes = []` are all consume (`consumeHead [] = Always`) and may
||| overlap, so the old "any args, empty modes" fact is false.
export
aliasBadNilArgs :
  {ctx : Ctx} -> {callee : String} ->
  aliasBad ctx [] callee = False
aliasBadNilArgs = Refl

export
aliasBadNilModes :
  {ctx : Ctx} -> {callee : String} ->
  funModes ctx callee = [] ->
  aliasBad ctx [] callee = False
aliasBadNilModes _ = Refl

trueNotFalseC : Not (True = False)
trueNotFalseC Refl impossible

orFalseC : (x, y : Bool) -> x || y = False -> (x = False, y = False)
orFalseC False False Refl = (Refl, Refl)
orFalseC True _ prf = void (trueNotFalseC prf)

orFalseIntro : {x, y : Bool} -> x = False -> y = False -> x || y = False
orFalseIntro Refl Refl = Refl

||| A borrow head with `storedLiveGo` false leaves the tail quiet for the
||| places captured so far, including this head. The head did not free a
||| place the running live set still holds.
export
storedLiveBorrow :
  {acc : List (String, List Consume)} ->
  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  storedLiveGo acc live (e :: es) (m :: ms) = False ->
  storedLiveGo acc (valuePlaces e ++ xferLive live e) es ms = False
storedLiveBorrow {m = Never} {acc} {live} {e} {es} {ms} _ prf =
  freeGo (nestedGo acc live [e]) Refl prf
  where
    freeGo : (b : Bool) -> nestedGo acc live [e] = b ->
             storedFree acc b live e es ms = False ->
             storedLiveGo acc (valuePlaces e ++ xferLive live e) es ms = False
    freeGo False _ pr0 = pr0
    freeGo True _ pr0 = void (trueNotFalseC pr0)
storedLiveBorrow {m = May} pc _ = void (trueNotFalseC pc)
storedLiveBorrow {m = Always} pc _ = void (trueNotFalseC pc)

||| `storedLiveBorrow` from an empty capture set.
export
storedLiveBorrowTail :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  storedBorrowConsume acc (e :: es) (m :: ms) = False ->
  storedLiveGo acc (valuePlaces e ++ xferLive [] e) es ms = False
storedLiveBorrowTail pc prf = storedLiveBorrow {live = []} pc prf

||| A consume head that is not itself a captured read leaves the tail
||| quiet after that head's stores.
export
storedLiveConsume :
  {acc : List (String, List Consume)} ->
  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  storedLiveGo acc live (e :: es) (m :: ms) = False ->
  storedLiveGo acc (xferLive live e) es ms = False
storedLiveConsume {m = Never} pc _ = void (trueNotFalseC (sym pc))
storedLiveConsume {m = May} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         storedLiveGo acc (xferLive live e) es ms = False
    go False _ pr0 = pr0
    go True _ pr0 = void (trueNotFalseC pr0)
storedLiveConsume {m = Always} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         storedLiveGo acc (xferLive live e) es ms = False
    go False _ pr0 = pr0
    go True _ pr0 = void (trueNotFalseC pr0)

||| Empty modes are consumes. The same split as `storedLiveConsume`.
export
storedLiveExtra :
  {acc : List (String, List Consume)} ->
  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
  storedLiveGo acc live (e :: es) [] = False ->
  storedLiveGo acc (xferLive live e) es [] = False
storedLiveExtra {acc} {live} {e} {es} prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es [] = False ->
         storedLiveGo acc (xferLive live e) es [] = False
    go False _ pr0 = pr0
    go True _ pr0 = void (trueNotFalseC pr0)

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

||| `nestedGo` does not reduce outside Checker.
export
nestedGoHead :
  {acc : List (String, List Consume)} -> {p : Place} -> {ps : List Place} ->
  {es : List Expr} ->
  nestedGo acc (p :: ps) es = False -> argsHit acc p es = False
nestedGoHead prf = fst (orFalseC _ _ prf)

export
nestedGoTail :
  {acc : List (String, List Consume)} -> {p : Place} -> {ps : List Place} ->
  {es : List Expr} ->
  nestedGo acc (p :: ps) es = False -> nestedGo acc ps es = False
nestedGoTail prf = snd (orFalseC _ _ prf)

||| Drop one argument from every protected place.
export
nestedGoExprTail :
  {acc : List (String, List Consume)} -> {ps : List Place} ->
  {e : Expr} -> {es : List Expr} ->
  nestedGo acc ps (e :: es) = False -> nestedGo acc ps es = False
nestedGoExprTail {ps = []} _ = Refl
nestedGoExprTail {ps = _ :: ps} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (argsHitTail hd) (nestedGoExprTail {ps} tl)

||| `argsHit` does not reduce outside Checker. The head `argFrees` is the
||| other half of `argsHitTail`.
export
argsHitHead : {acc : List (String, List Consume)} -> {p : Place} ->
              {e : Expr} -> {es : List Expr} ->
              argsHit acc p (e :: es) = False -> argFrees acc p e = False
argsHitHead prf = fst (orFalseC _ _ prf)

export
argsFreeHead : {acc : List (String, List Consume)} -> {p : Place} ->
               {e : Expr} -> {es : List Expr} ->
               argsFree acc p (e :: es) = False -> argFrees acc p e = False
argsFreeHead prf = fst (orFalseC _ _ prf)

export
argsFreeTail : {acc : List (String, List Consume)} -> {p : Place} ->
               {e : Expr} -> {es : List Expr} ->
               argsFree acc p (e :: es) = False -> argsFree acc p es = False
argsFreeTail prf = snd (orFalseC _ _ prf)

||| `argsFree` and `argsHit` are the same recursion, both opaque outside.
export
argsFreeIsHit : (acc : List (String, List Consume)) -> (p : Place) ->
                (es : List Expr) ->
                argsFree acc p es = argsHit acc p es
argsFreeIsHit _ _ [] = Refl
argsFreeIsHit acc p (e :: es) with (argFrees acc p e)
  argsFreeIsHit acc p (e :: es) | False = argsFreeIsHit acc p es
  argsFreeIsHit acc p (e :: es) | True = Refl

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

||| `malloc(r = p, g(r))` is rejected before any scope step.
export
checkExprMallocHeldFree :
  checkExpr (MkCtx [("g", [Always])] ["g"]) []
    (EMalloc 0 [ EAssign 1 2 "r" Ptr (EVar 3 4 "p")
               , ECall 5 "g" [EVar 6 2 "r"] ])
    = Left (borrowHeldDiag
        [ EAssign 1 2 "r" Ptr (EVar 3 4 "p")
        , ECall 5 "g" [EVar 6 2 "r"] ])
checkExprMallocHeldFree = Refl

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
    Left (mixedAliasDiag nid callee (overlapArg args (callFoots ctx.summaries args modes)))
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
    Left (mixedAliasDiag nid callee
      (overlapArg args (callFoots ctx.summaries args (funModes ctx callee))))
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
assignPtrLeak :
  {ctx : Ctx} -> {sc : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  ghostCopyLeak rhs = True ->
  assignPlace ctx sc id n nm Ptr rhs False = Left (ghostCopyDiag id nm)
assignPtrLeak leak = rewrite leak in Refl

export
assignPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrLeft _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
assignPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  assignPlace ctx sc id n nm Ptr rhs False = Right sc2
assignPtrOwner leak pT pU = rewrite leak in rewrite pT in rewrite pU in Refl

export
assignPtrUseFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrUseFail leak pT pU = rewrite leak in rewrite pT in rewrite pU in Refl

export
assignPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  assignPlace ctx sc id n nm Ptr rhs False =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
assignPtrGhost _ _ _ leak pT = rewrite leak in rewrite pT in Refl

export
assignPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  assignPlace ctx sc id n nm Ptr rhs False =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
assignPtrNull _ _ _ leak pT = rewrite leak in rewrite pT in Refl

export
checkExprAsgPtrLeak :
  {ctx : Ctx} -> {sc : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  ghostCopyLeak rhs = True ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Left (ghostCopyDiag id nm)
checkExprAsgPtrLeak leak = rewrite leak in Refl

||| A pointer store the checker accepted did not copy a named live pointer.
export
ghostCopyLeakFalseChk :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
  ghostCopyLeak rhs = False
ghostCopyLeakFalseChk eq = leakFalseGo (ghostCopyLeak rhs) Refl eq
  where
    leakFalseGo : (b : Bool) -> ghostCopyLeak rhs = b ->
                  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
                  ghostCopyLeak rhs = False
    leakFalseGo True p eq1 =
      void (leftNotRightChk (trans (sym (checkExprAsgPtrLeak p)) eq1))
    leakFalseGo False p _ = p

export
checkExprAsgPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Left d ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Left d
checkExprAsgPtrLeft _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
checkExprAsgPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc2
checkExprAsgPtrOwner leak pT pU = rewrite leak in rewrite pT in rewrite pU in Refl

export
checkExprAsgPtrUseFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Left d
checkExprAsgPtrUseFail leak pT pU = rewrite leak in rewrite pT in rewrite pU in Refl

export
checkExprAsgPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
checkExprAsgPtrGhost _ _ _ leak pT = rewrite leak in rewrite pT in Refl

export
checkExprAsgPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
checkExprAsgPtrNull _ _ _ leak pT = rewrite leak in rewrite pT in Refl

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
takeAsgPtrLeak :
  {ctx : Ctx} -> {sc : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  ghostCopyLeak rhs = True ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left (ghostCopyDiag id nm)
takeAsgPtrLeak leak = rewrite leak in Refl

||| A taken pointer store the checker accepted did not copy a named live pointer.
export
ghostCopyLeakFalseTake :
  {ctx : Ctx} -> {sc : Scopes} -> {r : (Scopes, Flag)} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right r ->
  ghostCopyLeak rhs = False
ghostCopyLeakFalseTake eq = leakFalseGo (ghostCopyLeak rhs) Refl eq
  where
    leakFalseGo : (b : Bool) -> ghostCopyLeak rhs = b ->
                  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right r ->
                  ghostCopyLeak rhs = False
    leakFalseGo True p eq1 =
      void (leftNotRightChk (trans (sym (takeAsgPtrLeak p)) eq1))
    leakFalseGo False p _ = p

export
takeAsgPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrLeft _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
takeAsgPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc2, Owner)
takeAsgPtrOwner leak pT pM = rewrite leak in rewrite pT in rewrite pM in Refl

export
takeAsgPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1, Ghost)
takeAsgPtrGhost _ _ _ leak pT = rewrite leak in rewrite pT in Refl

export
takeAsgPtrNull :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1, Null)
takeAsgPtrNull _ _ _ leak pT = rewrite leak in rewrite pT in Refl

export
takeAsgPtrFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrFail leak pT pM = rewrite leak in rewrite pT in rewrite pM in Refl

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
declPtrLeak :
  {fuel : Nat} -> {ctx : Ctx} -> {sc : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {e : Expr} ->
  ghostCopyLeak e = True ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Left (ghostCopyDiag id nm)
declPtrLeak leak = rewrite leak in Refl

||| A pointer initialiser the checker accepted did not copy a named live pointer.
export
ghostCopyLeakFalseDecl :
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {e : Expr} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
  ghostCopyLeak e = False
ghostCopyLeakFalseDecl eq = leakFalseGo (ghostCopyLeak e) Refl eq
  where
    leakFalseGo : (b : Bool) -> ghostCopyLeak e = b ->
                  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
                  ghostCopyLeak e = False
    leakFalseGo True p eq1 =
      void (leftNotRightChk (trans (sym (declPtrLeak p)) eq1))
    leakFalseGo False p _ = p

export
declPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak e = False) ->
  takeOwner ctx sc e = Left d ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Left d
declPtrLeft _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
declPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  (leak : ghostCopyLeak e = False) ->
  takeOwner ctx sc e = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton AOwned) sc1)
declPtrOwner _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
declPtrGhostEq :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  (leak : ghostCopyLeak e = False) ->
  takeOwner ctx sc e = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc1)
declPtrGhostEq _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
declPtrNullEq :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  (leak : ghostCopyLeak e = False) ->
  takeOwner ctx sc e = Right (sc1, Null) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton ANull) sc1)
declPtrNullEq _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
stmtAsgPtrLeak :
  {fuel : Nat} -> {ctx : Ctx} -> {sc : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  ghostCopyLeak rhs = True ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Left (ghostCopyDiag id nm)
stmtAsgPtrLeak leak = rewrite leak in Refl

||| A pointer statement the checker accepted did not copy a named live pointer.
export
ghostCopyLeakFalseStmt :
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  ghostCopyLeak rhs = False
ghostCopyLeakFalseStmt eq = leakFalseGo (ghostCopyLeak rhs) Refl eq
  where
    leakFalseGo : (b : Bool) -> ghostCopyLeak rhs = b ->
                  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
                  ghostCopyLeak rhs = False
    leakFalseGo True p eq1 =
      void (leftNotRightChk (trans (sym (stmtAsgPtrLeak p)) eq1))
    leakFalseGo False p _ = p

export
stmtAsgPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Left d ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Left d
stmtAsgPtrLeft _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
stmtAsgPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AOwned) sc1)
stmtAsgPtrOwner _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
stmtAsgPtrGhost :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
stmtAsgPtrGhost _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

export
stmtAsgPtrNull :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  (leak : ghostCopyLeak rhs = False) ->
  takeOwner ctx sc rhs = Right (sc1, Null) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton ANull) sc1)
stmtAsgPtrNull _ _ _ _ leak prf = rewrite leak in rewrite prf in Refl

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

||| The stored-destination free is its own `Left`. It is not the head
||| expression's failure, so the old cons equations need this flag quiet.
export
argsBorrowHeld :
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {es : List Expr} ->
  borrowHeldFrees ctx.summaries (e :: es) = True ->
  checkArgsBorrow ctx sc (e :: es) = Left (borrowHeldDiag (e :: es))
argsBorrowHeld prf = rewrite prf in Refl

||| A successful borrow list did not free a stored existing pointer.
||| `borrowHeldFrees` unfolds, so the flag is matched as a `Bool`, the
||| same way `ghostCopyLeakFalseTake` matches its flag.
export
borrowHeldFreesFalse :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {es : List Expr} ->
  checkArgsBorrow ctx sc es = Right sc' ->
  borrowHeldFrees ctx.summaries es = False
borrowHeldFreesFalse {es = []} _ = Refl
borrowHeldFreesFalse {es = e :: es} eq =
  heldQuiet (borrowHeldFrees ctx.summaries (e :: es)) Refl eq
  where
    heldQuiet : (b : Bool) ->
                borrowHeldFrees ctx.summaries (e :: es) = b ->
                checkArgsBorrow ctx sc (e :: es) = Right sc' ->
                b = False
    heldQuiet False _ _ = Refl
    heldQuiet True p eq1 =
      void (leftNotRightChk (trans (sym (argsBorrowHeld p)) eq1))

export
argsBorrowLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  (quiet : borrowHeldFrees ctx.summaries (e :: es) = False) ->
  checkExpr ctx sc e = Left d ->
  checkArgsBorrow ctx sc (e :: es) = Left d
argsBorrowLeft _ quiet prf = rewrite quiet in rewrite prf in Refl

export
argsBorrowRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  (quiet : borrowHeldFrees ctx.summaries (e :: es) = False) ->
  checkExpr ctx sc e = Right sc1 ->
  checkArgsBorrow ctx sc (e :: es) = checkArgsBorrow ctx sc1 es
argsBorrowRight _ quiet prf = rewrite quiet in rewrite prf in Refl

export
argsBorrowSplit :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {es : List Expr} ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  (sc1 ** (checkExpr ctx sc e = Right sc1, checkArgsBorrow ctx sc1 es = Right sc'))
argsBorrowSplit eq =
  splitHeld (borrowHeldFrees ctx.summaries (e :: es)) Refl eq
  where
    splitHeld : (b : Bool) ->
                borrowHeldFrees ctx.summaries (e :: es) = b ->
                checkArgsBorrow ctx sc (e :: es) = Right sc' ->
                (sc1 ** (checkExpr ctx sc e = Right sc1,
                         checkArgsBorrow ctx sc1 es = Right sc'))
    splitHeld True p eq1 =
      void (leftNotRightChk (trans (sym (argsBorrowHeld p)) eq1))
    splitHeld False p eq1 = splitGo (checkExpr ctx sc e) Refl
      where
        splitGo :
          (res : Either Diag Scopes) ->
          checkExpr ctx sc e = res ->
          (sc1 ** (checkExpr ctx sc e = Right sc1,
                   checkArgsBorrow ctx sc1 es = Right sc'))
        splitGo (Left d) pE =
          void (leftNotRightChk (trans (sym (argsBorrowLeft es p pE)) eq1))
        splitGo (Right sc1) pE =
          (sc1 ** (pE, trans (sym (argsBorrowRight es p pE)) eq1))

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

||| `ms` has a mode for every argument. The empty tail, where
||| `consumeHead` and `sumHead` disagree, is `False`.
public export
modesCover : List Consume -> List a -> Bool
modesCover _ [] = True
modesCover [] (_ :: _) = False
modesCover (_ :: ms) (_ :: es) = modesCover ms es

||| Every place of `xs` occurs in `ys`.
placeSub : List Place -> List Place -> Bool
placeSub [] _ = True
placeSub (p :: ps) ys = placeIn p ys && placeSub ps ys

andTrueC : (x, y : Bool) -> x && y = True -> (x = True, y = True)
andTrueC True True Refl = (Refl, Refl)
andTrueC False _ prf = void (trueNotFalseC (sym prf))
andTrueC True False prf = void (trueNotFalseC (sym prf))

andIntro : {x, y : Bool} -> x = True -> y = True -> x && y = True
andIntro Refl Refl = Refl

orTrueLeft : (y : Bool) -> True || y = True
orTrueLeft _ = Refl

orFalseRightEq : {x : Bool} -> x || False = False -> x = False
orFalseRightEq {x = True} prf = void (trueNotFalseC prf)
orFalseRightEq {x = False} prf = Refl

appendAssoc : (xs, ys, zs : List a) -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssoc [] _ _ = Refl
appendAssoc (x :: xs) ys zs = cong (x ::) (appendAssoc xs ys zs)

placeInHere : (p : Place) -> (ps : List Place) -> placeIn p (p :: ps) = True
placeInHere p ps = rewrite eqNatRefl p in Refl

placeInTail : {p, q : Place} -> {qs : List Place} ->
              placeIn p qs = True -> placeIn p (q :: qs) = True
placeInTail pin = rewrite pin in orTrueRight (p == q)

placeInAppendL : {p : Place} -> {xs, ys : List Place} ->
                 placeIn p xs = True -> placeIn p (xs ++ ys) = True
placeInAppendL {xs = []} pin = void (trueNotFalseC (sym pin))
placeInAppendL {p} {xs = q :: qs} {ys} pin = appGo (p == q) Refl pin
  where
    appGo : (b : Bool) -> p == q = b -> placeIn p (q :: qs) = True ->
            placeIn p ((q :: qs) ++ ys) = True
    appGo True pq _ = rewrite sym (eqNatTrue p q pq) in placeInHere p (qs ++ ys)
    appGo False pq pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
      in placeInTail (placeInAppendL {p} {xs = qs} {ys} pinq)

placeInJoinR : {p : Place} -> {xs, ys : List Place} ->
               placeIn p ys = True -> placeIn p (xs ++ ys) = True
placeInJoinR {xs = []} prf = prf
placeInJoinR {p} {xs = q :: qs} {ys} prf =
  placeInTail {p} {q} {qs = qs ++ ys} (placeInJoinR {p} {xs = qs} {ys} prf)

inAppend : {p : Place} -> {xs, ys : List Place} ->
           placeIn p (xs ++ ys) = True ->
           Either (placeIn p xs = True) (placeIn p ys = True)
inAppend {xs = []} pin = Right pin
inAppend {xs = q :: qs} pin = appGo (p == q) Refl pin
  where
    appGo : (b : Bool) -> p == q = b -> placeIn p ((q :: qs) ++ ys) = True ->
            Either (placeIn p (q :: qs) = True) (placeIn p ys = True)
    appGo True pq _ = Left (rewrite sym (eqNatTrue p q pq) in placeInHere p qs)
    appGo False pq pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p (qs ++ ys))) = True} pq pin
      in case inAppend {xs = qs} pinq of
           Left rest => Left (placeInTail rest)
           Right rest => Right rest

subIn : {p : Place} -> {xs, ys : List Place} ->
        placeSub xs ys = True -> placeIn p xs = True -> placeIn p ys = True
subIn {xs = []} _ pin = void (trueNotFalseC (sym pin))
subIn {xs = q :: qs} psub pin = subGo (p == q) Refl psub pin
  where
    subGo : (b : Bool) -> p == q = b -> placeSub (q :: qs) ys = True ->
            placeIn p (q :: qs) = True -> placeIn p ys = True
    subGo True pq psub _ =
      let (hd, _) = andTrueC _ _ psub
      in replace {p = \n => placeIn n ys = True} (sym (eqNatTrue p q pq)) hd
    subGo False pq psub pin =
      let (_, tl) = andTrueC _ _ psub
          pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
      in subIn tl pinq

subFrom : {xs, ys : List Place} ->
          ((p : Place) -> placeIn p xs = True -> placeIn p ys = True) ->
          placeSub xs ys = True
subFrom {xs = []} _ = Refl
subFrom {xs = q :: qs} f =
  andIntro (f q (placeInHere q qs))
           (subFrom (\p, pin => f p (placeInTail pin)))

subTail : {p : Place} -> {ps, ys : List Place} ->
          placeSub (p :: ps) ys = True -> placeSub ps ys = True
subTail prf = snd (andTrueC _ _ prf)

subAppend : {xs, ys, zs : List Place} ->
            placeSub (xs ++ ys) zs = True ->
            (placeSub xs zs = True, placeSub ys zs = True)
subAppend {xs = []} prf = (Refl, prf)
subAppend {xs = p :: ps} prf =
  let (hd, tl) = andTrueC _ _ prf
      (psSub, ysSub) = subAppend {xs = ps} tl
  in (andIntro hd psSub, ysSub)

subJoinL : {xs, ys : List Place} -> placeSub xs (xs ++ ys) = True
subJoinL = subFrom (\p, pin => placeInAppendL pin)

subJoinR : {xs, ys : List Place} -> placeSub ys (xs ++ ys) = True
subJoinR = subFrom (\p, pin => placeInJoinR pin)

shiftIn : {p : Place} -> {xs, ys, zs : List Place} ->
          placeIn p (ys ++ zs) = True ->
          placeIn p ((xs ++ ys) ++ zs) = True
shiftIn {xs} {ys} {zs} pin =
  rewrite appendAssoc xs ys zs in placeInJoinR {xs} pin

||| A place read by `e` is a place `movedInExpr` sees.
readPlaceMoved : {p : Place} -> {e : Expr} ->
                 placeIn p (readPlaces e) = True -> movedInExpr p e = True
readPlaceMoved {e = EVar id q nm} pin = varGo (p == q) Refl pin
  where
    varGo : (b : Bool) -> p == q = b ->
            placeIn p [q] = True -> movedInExpr p (EVar id q nm) = True
    varGo True pq _ = pq
    varGo False pq pin0 =
      let pinq = replace {p = \b => (b || Delay (placeIn p [])) = True} pq pin0
      in void (trueNotFalseC (sym pinq))
readPlaceMoved {e = EAssign _ _ _ _ rhs} pin = readPlaceMoved {e = rhs} pin
readPlaceMoved {e = ELit _} pin = void (trueNotFalseC (sym pin))
readPlaceMoved {e = ENull _} pin = void (trueNotFalseC (sym pin))
readPlaceMoved {e = EMalloc _ _} pin = void (trueNotFalseC (sym pin))
readPlaceMoved {e = ECall _ _ _} pin = void (trueNotFalseC (sym pin))
readPlaceMoved {e = EUse _ _} pin = void (trueNotFalseC (sym pin))
readPlaceMoved {e = EUnsupported _ _} pin = void (trueNotFalseC (sym pin))

||| A nonempty read is a variable, so the value can be a live pointer.
readHasLive : {e : Expr} -> {qs : List Place} ->
              placesOverlap (readPlaces e) qs = True -> maybeLivePtr e = True
readHasLive {e = EVar _ _ _} _ = Refl
readHasLive {e = EAssign _ _ _ _ rhs} prf = readHasLive {e = rhs} prf
readHasLive {e = ELit _} prf = void (trueNotFalseC (sym prf))
readHasLive {e = ENull _} prf = void (trueNotFalseC (sym prf))
readHasLive {e = EMalloc _ _} prf = void (trueNotFalseC (sym prf))
readHasLive {e = ECall _ _ _} prf = void (trueNotFalseC (sym prf))
readHasLive {e = EUse _ _} prf = void (trueNotFalseC (sym prf))
readHasLive {e = EUnsupported _ _} prf = void (trueNotFalseC (sym prf))

forgetCons : {d, q : Place} -> {qs : List Place} ->
             (b : Bool) -> d == q = b ->
             forgetPlace d (q :: qs) =
               if b then forgetPlace d qs else q :: forgetPlace d qs
forgetCons True eq = rewrite eq in Refl
forgetCons False eq = rewrite eq in Refl

forgetMiss : {p, d : Place} -> {xs : List Place} ->
             placeIn p (forgetPlace d xs) = True -> placeIn p xs = True
forgetMiss {xs = []} pin = void (trueNotFalseC (sym pin))
forgetMiss {p} {d} {xs = q :: qs} pin = missGo (d == q) Refl pin
  where
    missGo : (b : Bool) -> d == q = b ->
             placeIn p (forgetPlace d (q :: qs)) = True -> placeIn p (q :: qs) = True
    missGo True eq pin =
      placeInTail
        (forgetMiss {p} {d} {xs = qs}
          (replace {p = \xs => placeIn p xs = True} (forgetCons True eq) pin))
    missGo False eq pin =
      keepGo (p == q) Refl
        (replace {p = \xs => placeIn p xs = True} (forgetCons False eq) pin)
      where
        keepGo : (c : Bool) -> p == q = c ->
                 placeIn p (q :: forgetPlace d qs) = True ->
                 placeIn p (q :: qs) = True
        keepGo True pq _ = rewrite sym (eqNatTrue p q pq) in placeInHere p qs
        keepGo False pq pin =
          let pinq = replace {p = \b => (b || Delay (placeIn p (forgetPlace d qs))) = True} pq pin
          in placeInTail (forgetMiss {p} {d} {xs = qs} pinq)

forgetNotDest : {d : Place} -> {xs : List Place} ->
                placeIn d (forgetPlace d xs) = False
forgetNotDest {xs = []} = Refl
forgetNotDest {xs = q :: qs} = notGo (d == q) Refl
  where
    notGo : (b : Bool) -> d == q = b ->
            placeIn d (forgetPlace d (q :: qs)) = False
    notGo True eq = rewrite eq in forgetNotDest {xs = qs}
    notGo False eq =
      rewrite eq in orFalseIntro eq (forgetNotDest {xs = qs})

forgetKeep : {p, d : Place} -> {xs : List Place} ->
             p == d = False -> placeIn p xs = True ->
             placeIn p (forgetPlace d xs) = True
forgetKeep {xs = []} _ pin = void (trueNotFalseC (sym pin))
forgetKeep {p} {d} {xs = q :: qs} pd pin =
  keepGo (d == q) Refl (p == q) Refl pd pin
  where
    keepGo : (bd : Bool) -> d == q = bd -> (bp : Bool) -> p == q = bp ->
             p == d = False -> placeIn p (q :: qs) = True ->
             placeIn p (forgetPlace d (q :: qs)) = True
    keepGo True ed True ep pd _ =
      void (eqNatFalse p d pd (trans (eqNatTrue p q ep) (sym (eqNatTrue d q ed))))
    keepGo True ed False ep pd pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} ep pin
      in rewrite ed in forgetKeep {p} {d} {xs = qs} pd pinq
    keepGo False ed True ep _ _ =
      rewrite ed in rewrite sym (eqNatTrue p q ep) in placeInHere p (forgetPlace d qs)
    keepGo False ed False ep pd pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} ep pin
      in rewrite ed in placeInTail (forgetKeep {p} {d} {xs = qs} pd pinq)

||| Places a covering consume actually moves. An empty mode tail is
||| `False`: `consumeInArgs` does not see it (`sumHead []` is `Never`).
movedConsume : Place -> List Expr -> List Consume -> Bool
movedConsume _ [] _ = False
movedConsume _ (_ :: _) [] = False
movedConsume p (e :: es) (m :: ms) =
  (doesConsume m && movedInExpr p e) || movedConsume p es ms

consumeQuiet : List Place -> List Expr -> List Consume -> Bool
consumeQuiet [] _ _ = False
consumeQuiet (p :: ps) es ms = movedConsume p es ms || consumeQuiet ps es ms

movedFromGo : {p : Place} -> {es : List Expr} -> {ms : List Consume} ->
              consumeInArgsGo p es ms = Never -> movedConsume p es ms = False
movedFromGo {es = []} _ = Refl
movedFromGo {es = _ :: _} {ms = []} _ = Refl
movedFromGo {es = e :: es} {ms = Never :: ms} prf = movedFromGo prf
movedFromGo {es = e :: es} {ms = May :: ms} prf = mayGo (movedInExpr p e) Refl prf
  where
    mayGo : (b : Bool) -> movedInExpr p e = b ->
            consumeInArgsGo p (e :: es) (May :: ms) = Never ->
            movedConsume p (e :: es) (May :: ms) = False
    mayGo False pb eq =
      rewrite pb in movedFromGo (replace {p = \c => c = Never} (consumeMaySkip pb) eq)
    mayGo True pb eq =
      void (trueNotFalseC (cong doesConsume (trans (sym (consumeMayHit pb)) eq)))
movedFromGo {es = e :: es} {ms = Always :: ms} prf =
  alwaysGo (movedInExpr p e) Refl prf
  where
    alwaysGo : (b : Bool) -> movedInExpr p e = b ->
               consumeInArgsGo p (e :: es) (Always :: ms) = Never ->
               movedConsume p (e :: es) (Always :: ms) = False
    alwaysGo False pb eq =
      rewrite pb in
        movedFromGo (replace {p = \c => c = Never} (consumeAlwaysSkip pb) eq)
    alwaysGo True pb eq =
      void (trueNotFalseC (cong doesConsume (trans (sym (consumeAlwaysHit pb)) eq)))

movedFromCall : {acc : List (String, List Consume)} -> {p : Place} ->
                {id : Nat} -> {callee : String} -> {es : List Expr} ->
                {ms : List Consume} ->
                argFrees acc p (ECall id callee es) = False ->
                calleeModes acc callee = ms ->
                movedConsume p es ms = False
movedFromCall {acc} {p} {id} {callee} {es} {ms} prf modes =
  let (held, _) = argFreesCallSplit {acc} {p} {id} {callee} {args = es} prf
  in movedFromGo {p} {es} {ms}
       (replace {p = \c => consumeInArgsGo p es c = Never} modes
          (doesConsumeNeverOnly held))

quietMoves : {acc : List (String, List Consume)} -> {ps : List Place} ->
             {id : Nat} -> {callee : String} -> {es : List Expr} ->
             {ms : List Consume} ->
             nestedGo acc ps [ECall id callee es] = False ->
             calleeModes acc callee = ms ->
             consumeQuiet ps es ms = False
quietMoves {ps = []} _ _ = Refl
quietMoves {acc} {id} {callee} {es} {ms} {ps = p :: ps} prf modes =
  let (hd, tl) = orFalseC _ _ prf
      one = orFalseRightEq hd
  in orFalseIntro (movedFromCall {acc} {p} {id} {callee} {es} {ms} one modes)
       (quietMoves {acc} {id} {callee} {es} {ms} {ps} tl modes)

callOne : {acc : List (String, List Consume)} -> {p : Place} ->
          {id : Nat} -> {callee : String} -> {es : List Expr} ->
          argsHit acc p [ECall id callee es] = False ->
          argsHit acc p es = False
callOne {acc} {p} {id} {callee} {es} prf =
  let freed = orFalseRightEq prf
      (_, rest) = argFreesCallSplit {acc} {p} {id} {callee} {args = es} freed
  in replace {p = \b => b = False} (argsFreeIsHit acc p es) rest

callArgsQuiet : {acc : List (String, List Consume)} -> {ps : List Place} ->
                {id : Nat} -> {callee : String} -> {es : List Expr} ->
                nestedGo acc ps [ECall id callee es] = False ->
                nestedGo acc ps es = False
callArgsQuiet {ps = []} _ = Refl
callArgsQuiet {acc} {id} {callee} {es} {ps = p :: ps} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (callOne {acc} {p} {id} {callee} {es} hd)
       (callArgsQuiet {acc} {id} {callee} {es} {ps} tl)

nestedGoAppendQuiet : {acc : List (String, List Consume)} ->
                      {xs, ys : List Place} -> {es : List Expr} ->
                      nestedGo acc xs es = False ->
                      nestedGo acc ys es = False ->
                      nestedGo acc (xs ++ ys) es = False
nestedGoAppendQuiet {xs = []} _ pry = pry
nestedGoAppendQuiet {xs = _ :: qs} prx pry =
  let (hd, tl) = orFalseC _ _ prx
  in orFalseIntro hd (nestedGoAppendQuiet {xs = qs} tl pry)

consumeInQuiet : {p : Place} -> {ps : List Place} ->
                 {es : List Expr} -> {ms : List Consume} ->
                 placeIn p ps = True ->
                 consumeQuiet ps es ms = False ->
                 movedConsume p es ms = False
consumeInQuiet {ps = []} pin _ = void (trueNotFalseC (sym pin))
consumeInQuiet {ps = q :: qs} pin prf = qGo (p == q) Refl pin prf
  where
    qGo : (b : Bool) -> p == q = b ->
          placeIn p (q :: qs) = True ->
          consumeQuiet (q :: qs) es ms = False ->
          movedConsume p es ms = False
    qGo True pq _ prf0 =
      replace {p = \n => movedConsume n es ms = False}
        (sym (eqNatTrue p q pq)) (fst (orFalseC _ _ prf0))
    qGo False pq pin0 prf0 =
      consumeInQuiet {ps = qs}
        (replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0)
        (snd (orFalseC _ _ prf0))

peelMoved : {p : Place} -> {e : Expr} -> {es : List Expr} ->
            {m : Consume} -> {ms : List Consume} ->
            movedConsume p (e :: es) (m :: ms) = False ->
            movedConsume p es ms = False
peelMoved prf = snd (orFalseC _ _ prf)

peelQuiet : {ps : List Place} -> {e : Expr} -> {es : List Expr} ->
            {m : Consume} -> {ms : List Consume} ->
            consumeQuiet ps (e :: es) (m :: ms) = False ->
            consumeQuiet ps es ms = False
peelQuiet {ps = []} _ = Refl
peelQuiet {ps = _ :: qs} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (peelMoved hd) (peelQuiet {ps = qs} tl)

movedHead : {p : Place} -> {e : Expr} -> {es : List Expr} ->
            {m : Consume} -> {ms : List Consume} ->
            doesConsume m = True -> movedInExpr p e = True ->
            movedConsume p (e :: es) (m :: ms) = True
movedHead pc pm = rewrite pc in rewrite pm in Refl

overlapTail : {q : Place} -> {qs, ys : List Place} ->
              placesOverlap qs ys = True -> placesOverlap (q :: qs) ys = True
overlapTail prf = rewrite prf in orTrueRight (placeIn q ys)

overlapBuild : {p : Place} -> {xs, ys : List Place} ->
               placeIn p xs = True -> placeIn p ys = True ->
               placesOverlap xs ys = True
overlapBuild {xs = []} pin _ = void (trueNotFalseC (sym pin))
overlapBuild {p} {xs = q :: qs} {ys} pin iny = ovGo (p == q) Refl pin
  where
    ovGo : (b : Bool) -> p == q = b -> placeIn p (q :: qs) = True ->
           placesOverlap (q :: qs) ys = True
    ovGo True pq _ =
      rewrite sym (eqNatTrue p q pq) in rewrite iny in orTrueLeft (placesOverlap qs ys)
    ovGo False pq pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
      in overlapTail (overlapBuild {p} {xs = qs} {ys} pinq iny)

hitTail : {acc : List (String, List Consume)} ->
         {q : Place} -> {qs : List Place} -> {e : Expr} ->
         nestedGo acc qs [e] = True -> nestedGo acc (q :: qs) [e] = True
hitTail prf = rewrite prf in orTrueRight (argsHit acc q [e])

hitOne : {acc : List (String, List Consume)} -> {p : Place} ->
         {xs : List Place} -> {e : Expr} ->
         placeIn p xs = True -> argFrees acc p e = True ->
         nestedGo acc xs [e] = True
hitOne {xs = []} pin _ = void (trueNotFalseC (sym pin))
hitOne {acc} {p} {xs = q :: qs} {e} pin fr = hitGo (p == q) Refl pin
  where
    hitGo : (b : Bool) -> p == q = b -> placeIn p (q :: qs) = True ->
            nestedGo acc (q :: qs) [e] = True
    hitGo True pq _ =
      rewrite sym (eqNatTrue p q pq) in rewrite fr in orTrueLeft (nestedGo acc qs [e])
    hitGo False pq pin =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
      in hitTail (hitOne {acc} {p} {xs = qs} {e} pinq fr)

nestSkip : {acc : List (String, List Consume)} -> {p : Place} ->
           {ps : List Place} -> {e : Expr} ->
           argFrees acc p e = False ->
           nestedGo acc (p :: ps) [e] = nestedGo acc ps [e]
nestSkip af = rewrite af in Refl

nestSkipTrue : {acc : List (String, List Consume)} ->
               {p : Place} -> {ps : List Place} -> {e : Expr} ->
               argFrees acc p e = False ->
               nestedGo acc (p :: ps) [e] = True ->
               nestedGo acc ps [e] = True
nestSkipTrue af pr = replace {p = \b => b = True} (nestSkip af) pr

storedHeadFree : {acc : List (String, List Consume)} ->
                 {live : List Place} -> {e : Expr} -> {es : List Expr} ->
                 {ms : List Consume} ->
                 storedLiveGo acc live (e :: es) (Never :: ms) = False ->
                 nestedGo acc live [e] = False
storedHeadFree prf = go (nestedGo acc live [e]) Refl prf
  where
    go : (b : Bool) -> nestedGo acc live [e] = b ->
         storedFree acc b live e es ms = False ->
         nestedGo acc live [e] = False
    go False eq _ = eq
    go True _ pr0 = void (trueNotFalseC pr0)

storedHeadOverlap : {acc : List (String, List Consume)} ->
                    {live : List Place} -> {e : Expr} -> {es : List Expr} ->
                    {m : Consume} -> {ms : List Consume} ->
                    doesConsume m = True ->
                    storedLiveGo acc live (e :: es) (m :: ms) = False ->
                    placesOverlap (readPlaces e) live = False
storedHeadOverlap {m = Never} pc _ = void (trueNotFalseC (sym pc))
storedHeadOverlap {m = May} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         placesOverlap (readPlaces e) live = False
    go False eq _ = eq
    go True _ pr0 = void (trueNotFalseC pr0)
storedHeadOverlap {m = Always} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         placesOverlap (readPlaces e) live = False
    go False eq _ = eq
    go True _ pr0 = void (trueNotFalseC pr0)

||| Unfold one pointer-store. `rewrite` on `Refl` would rewrite both
||| sides, so the right-hand side is the reduced `if`.
nestStoredPtr : {id : Nat} -> {d : Place} -> {nm : String} -> {rhs : Expr} ->
                (b : Bool) -> maybeLivePtr rhs = b ->
                nestStored (EAssign id d nm Ptr rhs) =
                  if b then d :: nestStored rhs else nestStored rhs
nestStoredPtr True eq = rewrite eq in Refl
nestStoredPtr False eq = rewrite eq in Refl

rhsStored : {id : Nat} -> {d : Place} -> {nm : String} -> {rhs : Expr} ->
            {prot : List Place} ->
            placeSub (nestStored (EAssign id d nm Ptr rhs)) prot = True ->
            placeSub (nestStored rhs) prot = True
rhsStored {id} {d} {nm} {rhs} {prot} sub = liveGo (maybeLivePtr rhs) Refl sub
  where
    liveGo : (b : Bool) -> maybeLivePtr rhs = b ->
             placeSub (nestStored (EAssign id d nm Ptr rhs)) prot = True ->
             placeSub (nestStored rhs) prot = True
    liveGo True eq sub0 =
      snd (andTrueC _ _
            (replace {p = \xs => placeSub xs prot = True} (nestStoredPtr True eq) sub0))
    liveGo False eq sub0 =
      replace {p = \xs => placeSub xs prot = True} (nestStoredPtr False eq) sub0

||| `p` is not the destination, so it survives `placeAfter` on either flag.
placeAfterIn : {p, d : Place} -> {xs, prot : List Place} ->
               (b : Bool) -> p == d = False ->
               placeIn p (xs ++ prot) = True ->
               placeIn p (placeAfter d xs b ++ prot) = True
placeAfterIn True _ pin = placeInTail pin
placeAfterIn False neq pin =
  case inAppend pin of
    Left in0 => placeInAppendL (forgetKeep neq in0)
    Right inP => placeInJoinR inP

mutual
  xferIn : {p : Place} -> {live0, live1, prot : List Place} -> {e : Expr} ->
           placeIn p (xferLive live1 e) = True ->
           placeSub live1 (live0 ++ prot) = True ->
           placeSub (nestStored e) prot = True ->
           placeIn p (xferLive live0 e ++ prot) = True
  xferIn {e = EVar _ _ _} pin sub _ = subIn sub pin
  xferIn {e = ELit _} pin sub _ = subIn sub pin
  xferIn {e = ENull _} pin sub _ = subIn sub pin
  xferIn {e = EUnsupported _ _} pin sub _ = subIn sub pin
  xferIn {e = EAssign _ _ _ Copy rhs} pin sub ns = xferIn {e = rhs} pin sub ns
  xferIn {e = EAssign id d nm Ptr rhs} pin sub ns =
    flagGo (placesOverlap (readPlaces rhs) (xferLive live1 rhs)) Refl pin
    where
      flagGo : (b : Bool) ->
               placesOverlap (readPlaces rhs) (xferLive live1 rhs) = b ->
               placeIn p (placeAfter d (xferLive live1 rhs) b) = True ->
               placeIn p (xferLive live0 (EAssign id d nm Ptr rhs) ++ prot) = True
      flagGo True eq pin0 = onDest (p == d) Refl eq pin0
        where
          onDest : (c : Bool) -> p == d = c ->
                   placesOverlap (readPlaces rhs) (xferLive live1 rhs) = True ->
                   placeIn p (d :: xferLive live1 rhs) = True ->
                   placeIn p (xferLive live0 (EAssign id d nm Ptr rhs) ++ prot) = True
          onDest True pd eq _ =
            let live = readHasLive {e = rhs} eq
                (hd, _) = andTrueC _ _ (rhsHere live ns)
            in placeInJoinR {xs = xferLive live0 (EAssign id d nm Ptr rhs)}
                 (replace {p = \n => placeIn n prot = True} (sym (eqNatTrue p d pd)) hd)
            where
              rhsHere : maybeLivePtr rhs = True ->
                        placeSub (nestStored (EAssign id d nm Ptr rhs)) prot = True ->
                        placeSub (d :: nestStored rhs) prot = True
              rhsHere lv sub0 =
                replace {p = \xs => placeSub xs prot = True}
                  (nestStoredPtr {id} {d} {nm} {rhs} True lv) sub0
          onDest False pd eq pin1 =
            let pinq = replace {p = \b => (b || Delay (placeIn p (xferLive live1 rhs))) = True} pd pin1
                inRhs = xferIn {e = rhs} pinq sub (rhsStored ns)
            in placeAfterIn
                 (placesOverlap (readPlaces rhs) (xferLive live0 rhs)) pd inRhs
      flagGo False eq pin0 =
        let pin1 = forgetMiss pin0
            neq = notDest (p == d) Refl eq pin0
        in placeAfterIn
             (placesOverlap (readPlaces rhs) (xferLive live0 rhs)) neq
             (xferIn {e = rhs} pin1 sub (rhsStored ns))
        where
          notDest : (c : Bool) -> p == d = c ->
                    placesOverlap (readPlaces rhs) (xferLive live1 rhs) = False ->
                    placeIn p (forgetPlace d (xferLive live1 rhs)) = True ->
                    p == d = False
          notDest True pd _ pin1 =
            void (trueNotFalseC
              (trans (sym (replace {p = \n => placeIn n (forgetPlace d (xferLive live1 rhs)) = True}
                              (eqNatTrue p d pd) pin1))
                     (forgetNotDest {xs = xferLive live1 rhs})))
          notDest False pd _ _ = pd
  xferIn {e = ECall _ _ args} pin sub ns = xferArgsIn pin sub ns
  xferIn {e = EMalloc _ args} pin sub ns = xferArgsIn pin sub ns
  xferIn {e = EUse _ args} pin sub ns = xferArgsIn pin sub ns

  xferArgsIn : {p : Place} -> {live0, live1, prot : List Place} ->
               {es : List Expr} ->
               placeIn p (xferArgs live1 es) = True ->
               placeSub live1 (live0 ++ prot) = True ->
               placeSub (nestStoreds es) prot = True ->
               placeIn p (xferArgs live0 es ++ prot) = True
  xferArgsIn {es = []} pin sub _ = subIn sub pin
  xferArgsIn {es = e :: es} pin sub ns =
    let (nHere, nTail) = subAppend ns
        subX = subFrom (\q, qin => xferIn {e = e} qin sub nHere)
    in xferArgsIn {live1 = xferLive live1 e} {live0 = xferLive live0 e} {es = es}
         pin subX nTail

freeContra : {acc : List (String, List Consume)} ->
             {live0, live1, prot : List Place} -> {e : Expr} -> {es : List Expr} ->
             placeSub live1 (live0 ++ prot) = True ->
             nestedGo acc prot (e :: es) = False ->
             nestedGo acc live0 [e] = False ->
             nestedGo acc live1 [e] = True -> Void
freeContra {live1 = []} _ _ _ pr = void (trueNotFalseC (sym pr))
freeContra {acc} {live0} {prot} {live1 = p :: ps} {e} sub nq n0 pr =
  arm (argFrees acc p e) Refl pr
  where
    arm : (b : Bool) -> argFrees acc p e = b ->
          nestedGo acc (p :: ps) [e] = True -> Void
    arm True af _ =
      let mem = subIn {xs = p :: ps} {ys = live0 ++ prot} sub (placeInHere p ps)
      in case inAppend mem of
           Left in0 =>
             void (trueNotFalseC (trans (sym (hitOne in0 af)) n0))
           Right inP =>
             void (trueNotFalseC (trans (sym af) (argsHitHead (argsHitIn inP nq))))
    arm False af pr0 =
      freeContra {live1 = ps} (subTail sub) nq n0 (nestSkipTrue af pr0)

readContra : {live0, live1, prot : List Place} -> {e : Expr} ->
             {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
             placeSub live1 (live0 ++ prot) = True ->
             consumeQuiet prot (e :: es) (m :: ms) = False ->
             placesOverlap (readPlaces e) live0 = False ->
             doesConsume m = True ->
             placesOverlap (readPlaces e) live1 = True -> Void
readContra {live0} {live1} {prot} {e} sub cq ov0 pc ov =
  overlapVoid (readPlaces e) ov (\q, pin => pin)
  where
    overlapVoid : (xs : List Place) ->
                  placesOverlap xs live1 = True ->
                  ((q : Place) -> placeIn q xs = True -> placeIn q (readPlaces e) = True) ->
                  Void
    overlapVoid [] ov1 _ = void (trueNotFalseC (sym ov1))
    overlapVoid (q :: qs) ov1 embed = step (placeIn q live1) Refl ov1
      where
        step : (b : Bool) -> placeIn q live1 = b ->
               placesOverlap (q :: qs) live1 = True -> Void
        step True iq _ =
          let inRead = embed q (placeInHere q qs)
              mem = subIn {xs = live1} {ys = live0 ++ prot} sub iq
          in case inAppend mem of
               Left in0 =>
                 void (trueNotFalseC (trans (sym (overlapBuild inRead in0)) ov0))
               Right inP =>
                 void (trueNotFalseC
                   (trans (sym (movedHead pc (readPlaceMoved inRead)))
                          (consumeInQuiet inP cq)))
        step False iq ov2 =
          overlapVoid qs
            (replace {p = \b => (b || Delay (placesOverlap qs live1)) = True} iq ov2)
            (\r, pin => embed r (placeInTail pin))

neverSub : {live0, live1, prot : List Place} -> {e : Expr} ->
           placeSub live1 (live0 ++ prot) = True ->
           placeSub (nestStored e) prot = True ->
           placeSub (valuePlaces e ++ xferLive live1 e)
                    ((valuePlaces e ++ xferLive live0 e) ++ prot) = True
neverSub {live0} {prot} {e} sub ns = subFrom one
  where
    one : (p : Place) ->
          placeIn p (valuePlaces e ++ xferLive live1 e) = True ->
          placeIn p ((valuePlaces e ++ xferLive live0 e) ++ prot) = True
    one p pin = case inAppend pin of
      Left inV => placeInAppendL (placeInAppendL inV)
      Right inX => shiftIn {xs = valuePlaces e} {ys = xferLive live0 e} {zs = prot}
                     (xferIn {live0} {live1} {prot} {e} inX sub ns)

consumeSub : {live0, live1, prot : List Place} -> {e : Expr} ->
             placeSub live1 (live0 ++ prot) = True ->
             placeSub (nestStored e) prot = True ->
             placeSub (xferLive live1 e) (xferLive live0 e ++ prot) = True
consumeSub sub ns = subFrom (\p, pin => xferIn pin sub ns)

mutual
  covGo : {acc : List (String, List Consume)} ->
          {live0, live1, prot : List Place} ->
          {es : List Expr} -> {ms : List Consume} ->
          modesCover ms es = True ->
          consumeQuiet prot es ms = False ->
          nestedGo acc prot es = False ->
          storedLiveGo acc live0 es ms = False ->
          placeSub live1 (live0 ++ prot) = True ->
          placeSub (nestStoreds es) prot = True ->
          storedLiveGo acc live1 es ms = False
  covGo {es = []} _ _ _ _ _ _ = Refl
  covGo {es = _ :: _} {ms = []} cov _ _ _ _ _ = void (trueNotFalseC (sym cov))
  covGo {acc} {live0} {live1} {prot} {es = e :: es} {ms = Never :: ms}
       cov cq nq s0 sub nsub =
    covNever acc live0 live1 prot e es ms cov cq nq s0 sub nsub
      (nestedGo acc live1 [e]) Refl
  covGo {acc} {live0} {live1} {prot} {es = e :: es} {ms = May :: ms}
       cov cq nq s0 sub nsub =
    covMay acc live0 live1 prot e es ms cov cq nq s0 sub nsub
      (placesOverlap (readPlaces e) live1) Refl
  covGo {acc} {live0} {live1} {prot} {es = e :: es} {ms = Always :: ms}
       cov cq nq s0 sub nsub =
    covAlways acc live0 live1 prot e es ms cov cq nq s0 sub nsub
      (placesOverlap (readPlaces e) live1) Refl

  covNever : (acc : List (String, List Consume)) ->
             (live0, live1, prot : List Place) ->
             (e : Expr) -> (es : List Expr) -> (ms : List Consume) ->
             modesCover (Never :: ms) (e :: es) = True ->
             consumeQuiet prot (e :: es) (Never :: ms) = False ->
             nestedGo acc prot (e :: es) = False ->
             storedLiveGo acc live0 (e :: es) (Never :: ms) = False ->
             placeSub live1 (live0 ++ prot) = True ->
             placeSub (nestStoreds (e :: es)) prot = True ->
             (b : Bool) -> nestedGo acc live1 [e] = b ->
             storedLiveGo acc live1 (e :: es) (Never :: ms) = False
  covNever acc live0 live1 prot e es ms cov cq nq s0 sub nsub True nb =
    void (freeContra {acc} {live0} {live1} {prot} {e} {es} sub nq
            (storedHeadFree s0) nb)
  covNever acc live0 live1 prot e es ms cov cq nq s0 sub nsub False nb =
    let (nHere, nTail) = subAppend nsub
    in rewrite nb in
       covGo {acc} {live0 = valuePlaces e ++ xferLive live0 e}
             {live1 = valuePlaces e ++ xferLive live1 e} {prot} {es} {ms}
             cov (peelQuiet cq) (nestedGoArgsTail nq)
             (storedLiveBorrow {acc} {live = live0} {e} {es} {m = Never} {ms} Refl s0)
             (neverSub {live0} {live1} {prot} {e} sub nHere) nTail

  covMay : (acc : List (String, List Consume)) ->
           (live0, live1, prot : List Place) ->
           (e : Expr) -> (es : List Expr) -> (ms : List Consume) ->
           modesCover (May :: ms) (e :: es) = True ->
           consumeQuiet prot (e :: es) (May :: ms) = False ->
           nestedGo acc prot (e :: es) = False ->
           storedLiveGo acc live0 (e :: es) (May :: ms) = False ->
           placeSub live1 (live0 ++ prot) = True ->
           placeSub (nestStoreds (e :: es)) prot = True ->
           (b : Bool) -> placesOverlap (readPlaces e) live1 = b ->
           storedLiveGo acc live1 (e :: es) (May :: ms) = False
  covMay acc live0 live1 prot e es ms cov cq nq s0 sub nsub True ob =
    void (readContra {live0} {live1} {prot} {e} {es} {m = May} {ms}
            sub cq (storedHeadOverlap {acc} {live = live0} {e} {es} {m = May} {ms} Refl s0)
            Refl ob)
  covMay acc live0 live1 prot e es ms cov cq nq s0 sub nsub False ob =
    let (nHere, nTail) = subAppend nsub
    in rewrite ob in
       covGo {acc} {live0 = xferLive live0 e} {live1 = xferLive live1 e}
             {prot} {es} {ms}
             cov (peelQuiet cq) (nestedGoArgsTail nq)
             (storedLiveConsume {acc} {live = live0} {e} {es} {m = May} {ms} Refl s0)
             (consumeSub {live0} {live1} {prot} {e} sub nHere) nTail

  covAlways : (acc : List (String, List Consume)) ->
              (live0, live1, prot : List Place) ->
              (e : Expr) -> (es : List Expr) -> (ms : List Consume) ->
              modesCover (Always :: ms) (e :: es) = True ->
              consumeQuiet prot (e :: es) (Always :: ms) = False ->
              nestedGo acc prot (e :: es) = False ->
              storedLiveGo acc live0 (e :: es) (Always :: ms) = False ->
              placeSub live1 (live0 ++ prot) = True ->
              placeSub (nestStoreds (e :: es)) prot = True ->
              (b : Bool) -> placesOverlap (readPlaces e) live1 = b ->
              storedLiveGo acc live1 (e :: es) (Always :: ms) = False
  covAlways acc live0 live1 prot e es ms cov cq nq s0 sub nsub True ob =
    void (readContra {live0} {live1} {prot} {e} {es} {m = Always} {ms}
            sub cq
            (storedHeadOverlap {acc} {live = live0} {e} {es} {m = Always} {ms} Refl s0)
            Refl ob)
  covAlways acc live0 live1 prot e es ms cov cq nq s0 sub nsub False ob =
    let (nHere, nTail) = subAppend nsub
    in rewrite ob in
       covGo {acc} {live0 = xferLive live0 e} {live1 = xferLive live1 e}
             {prot} {es} {ms}
             cov (peelQuiet cq) (nestedGoArgsTail nq)
             (storedLiveConsume {acc} {live = live0} {e} {es} {m = Always} {ms} Refl s0)
             (consumeSub {live0} {live1} {prot} {e} sub nHere) nTail

||| A call whose mode list covers every argument. `live` is the pin live
||| at a `Never` argument, so the outer check only sees `argFrees`.
||| Stored destinations are `nestStoreds`. The empty-start check is the
||| `storedBorrowConsume` half of `aliasBad`. Together they force the
||| pin-live check quiet. A missing mode is not covered: `h(f(p))` with
||| `f` at `[]` is the counterexample to the statement without `modesCover`.
export
coveredStored : {acc : List (String, List Consume)} ->
                {live : List Place} ->
                {id : Nat} -> {callee : String} ->
                {es : List Expr} -> {ms : List Consume} ->
                modesCover ms es = True ->
                calleeModes acc callee = ms ->
                nestedGo acc live [ECall id callee es] = False ->
                nestedGo acc (nestStoreds es) [ECall id callee es] = False ->
                storedLiveGo acc [] es ms = False ->
                storedLiveGo acc live es ms = False
coveredStored {acc} {live} {es} {ms} cov modesEq nLive nNest s0 =
  covGo {acc} {live0 = []} {live1 = live}
       {prot = live ++ nestStoreds es} {es} {ms}
       cov (quietMoves (nestedGoAppendQuiet nLive nNest) modesEq)
       (callArgsQuiet (nestedGoAppendQuiet nLive nNest))
       s0 subJoinL subJoinR

--------------------------------------------------------------------------------
-- M2(a): empty-start storedLiveGo is subsumed by callOverlap
--------------------------------------------------------------------------------

ovAppL : {xs, ys, zs : List Place} ->
         placesOverlap xs zs = True -> placesOverlap (xs ++ ys) zs = True
ovAppL {xs = []} prf = void (trueNotFalseC (sym prf))
ovAppL {xs = p :: ps} {ys} {zs} prf =
  case orTrueChk prf of
    Left pin =>
      replace {p = \b => (b || Delay (placesOverlap (ps ++ ys) zs)) = True}
        (sym pin) (orTrueLeft (placesOverlap (ps ++ ys) zs))
    Right ov => overlapTail (ovAppL {xs = ps} {ys} {zs} ov)

ovAppR : {xs, ys, zs : List Place} ->
         placesOverlap ys zs = True -> placesOverlap (xs ++ ys) zs = True
ovAppR {xs = []} prf = prf
ovAppR {xs = _ :: ps} prf = overlapTail (ovAppR {xs = ps} prf)

ovInAppendL : {xs, ys, zs : List Place} ->
              placesOverlap xs ys = True -> placesOverlap xs (ys ++ zs) = True
ovInAppendL {xs = []} prf = void (trueNotFalseC (sym prf))
ovInAppendL {xs = p :: ps} {ys} {zs} prf =
  case orTrueChk prf of
    Left pin =>
      replace {p = \b => (b || Delay (placesOverlap ps (ys ++ zs))) = True}
        (sym (placeInAppendL {xs = ys} {ys = zs} pin))
        (orTrueLeft (placesOverlap ps (ys ++ zs)))
    Right ov => overlapTail (ovInAppendL {xs = ps} {ys} {zs} ov)

ovInJoinR : {xs, ys, zs : List Place} ->
            placesOverlap xs zs = True -> placesOverlap xs (ys ++ zs) = True
ovInJoinR {xs = []} prf = void (trueNotFalseC (sym prf))
ovInJoinR {xs = p :: ps} {ys} {zs} prf =
  case orTrueChk prf of
    Left pin =>
      replace {p = \b => (b || Delay (placesOverlap ps (ys ++ zs))) = True}
        (sym (placeInJoinR {xs = ys} {ys = zs} pin))
        (orTrueLeft (placesOverlap ps (ys ++ zs)))
    Right ov => overlapTail (ovInJoinR {xs = ps} {ys} {zs} ov)

ovInCons : {q : Place} -> {xs, ys : List Place} ->
           placesOverlap xs ys = True -> placesOverlap xs (q :: ys) = True
ovInCons {q} prf = ovInJoinR {ys = [q]} prf

overlapSplitL : {xs, ys, zs : List Place} ->
                placesOverlap (xs ++ ys) zs = True ->
                Either (placesOverlap xs zs = True) (placesOverlap ys zs = True)
overlapSplitL {xs = []} prf = Right prf
overlapSplitL {xs = p :: ps} {ys} {zs} prf =
  case orTrueChk prf of
    Left pin =>
      Left (replace {p = \b => (b || Delay (placesOverlap ps zs)) = True}
              (sym pin) (orTrueLeft (placesOverlap ps zs)))
    Right ov =>
      case overlapSplitL {xs = ps} {ys} {zs} ov of
        Left h => Left (overlapTail h)
        Right h => Right h

overlapSplitR : {xs, ys, zs : List Place} ->
                placesOverlap xs (ys ++ zs) = True ->
                Either (placesOverlap xs ys = True) (placesOverlap xs zs = True)
overlapSplitR {xs = []} prf = void (trueNotFalseC (sym prf))
overlapSplitR {xs = p :: ps} {ys} {zs} prf =
  case orTrueChk prf of
    Left pin =>
      case inAppend {xs = ys} {ys = zs} pin of
        Left inY =>
          Left (replace {p = \b => (b || Delay (placesOverlap ps ys)) = True}
                  (sym inY) (orTrueLeft (placesOverlap ps ys)))
        Right inZ =>
          Right (replace {p = \b => (b || Delay (placesOverlap ps zs)) = True}
                   (sym inZ) (orTrueLeft (placesOverlap ps zs)))
    Right ov =>
      case overlapSplitR {xs = ps} {ys} {zs} ov of
        Left h => Left (overlapTail h)
        Right h => Right (overlapTail h)

overlapSubL : {xs, ys, zs : List Place} ->
              placeSub xs ys = True ->
              placesOverlap xs zs = True ->
              placesOverlap ys zs = True
overlapSubL {xs = []} _ prf = void (trueNotFalseC (sym prf))
overlapSubL {xs = q :: qs} {ys} {zs} psub ov =
  case orTrueChk ov of
    Left pin =>
      overlapBuild {p = q} {xs = ys} {ys = zs}
        (subIn {xs = q :: qs} psub (placeInHere q qs)) pin
    Right ovt => overlapSubL {xs = qs} (subTail psub) ovt

overlapSubR : {xs, ys, zs : List Place} ->
              placeSub ys zs = True ->
              placesOverlap xs ys = True ->
              placesOverlap xs zs = True
overlapSubR {xs = []} _ prf = void (trueNotFalseC (sym prf))
overlapSubR {xs = p :: ps} {ys} {zs} psub ov =
  case orTrueChk ov of
    Left pin =>
      overlapBuild {p} {xs = p :: ps} {ys = zs} (placeInHere p ps)
        (subIn psub pin)
    Right ovt => overlapTail (overlapSubR {xs = ps} psub ovt)

ptrAssignW : {acc : List (String, List Consume)} ->
             {id : Nat} -> {d : Place} -> {nm : String} -> {rhs : Expr} ->
             fst (argFootprint acc (EAssign id d nm Ptr rhs)) =
               d :: fst (argFootprint acc rhs)
ptrAssignW = Refl

ptrAssignR : {acc : List (String, List Consume)} ->
             {id : Nat} -> {d : Place} -> {nm : String} -> {rhs : Expr} ->
             snd (argFootprint acc (EAssign id d nm Ptr rhs)) =
               snd (argFootprint acc rhs)
ptrAssignR = Refl

neverEqMay : Always = May -> Void
neverEqMay Refl impossible

neverEqAlways : Never = Always -> Void
neverEqAlways Refl impossible

readSubR : (acc : List (String, List Consume)) -> (e : Expr) ->
           placeSub (readPlaces e) (snd (argFootprint acc e)) = True
readSubR acc (EVar _ p _) = rewrite eqNatRefl p in Refl
readSubR acc (EAssign id d nm Ptr rhs) =
  replace {p = \xs => placeSub (readPlaces rhs) xs = True}
    (sym (ptrAssignR {acc} {id} {d} {nm} {rhs}))
    (readSubR acc rhs)
readSubR acc (EAssign _ _ _ Copy rhs) = readSubR acc rhs
readSubR _ (ELit _) = Refl
readSubR _ (ENull _) = Refl
readSubR _ (EMalloc _ _) = Refl
readSubR _ (ECall _ _ _) = Refl
readSubR _ (EUse _ _) = Refl
readSubR _ (EUnsupported _ _) = Refl

modeWNever : {acc : List (String, List Consume)} -> {e : Expr} ->
             fst (argModeFoot acc e Never) = fst (argFootprint acc e)
modeWNever = Refl

modeRNever : {acc : List (String, List Consume)} -> {e : Expr} ->
             snd (argModeFoot acc e Never) =
               snd (argFootprint acc e) ++ valuePlaces e
modeRNever = Refl

modeWMay : {acc : List (String, List Consume)} -> {e : Expr} ->
           fst (argModeFoot acc e May) =
             fst (argFootprint acc e) ++ snd (argFootprint acc e) ++ valuePlaces e
modeWMay = Refl

modeWAlways : {acc : List (String, List Consume)} -> {e : Expr} ->
              fst (argModeFoot acc e Always) =
                fst (argFootprint acc e) ++ snd (argFootprint acc e) ++
                  valuePlaces e
modeWAlways = Refl

modeWConsume : {acc : List (String, List Consume)} -> {e : Expr} ->
               {m : Consume} ->
               doesConsume m = True ->
               fst (argModeFoot acc e m) =
                 fst (argFootprint acc e) ++ snd (argFootprint acc e) ++
                   valuePlaces e
modeWConsume {m = Never} pc = void (trueNotFalseC (sym pc))
modeWConsume {m = May} _ = modeWMay
modeWConsume {m = Always} _ = modeWAlways

evalWSubMode : {acc : List (String, List Consume)} -> {e : Expr} ->
               {m : Consume} -> {p : Place} ->
               placeIn p (fst (argFootprint acc e)) = True ->
               placeIn p (fst (argModeFoot acc e m)) = True
evalWSubMode {acc} {e} {m = Never} {p = q} pin =
  replace {p = \xs => placeIn q xs = True} (sym (modeWNever {acc} {e})) pin
evalWSubMode {acc} {e} {m = May} {p = q} pin =
  replace {p = \xs => placeIn q xs = True} (sym (modeWMay {acc} {e}))
    (placeInAppendL pin)
evalWSubMode {acc} {e} {m = Always} {p = q} pin =
  replace {p = \xs => placeIn q xs = True} (sym (modeWAlways {acc} {e}))
    (placeInAppendL pin)

argsEvalFootCons :
  {acc : List (String, List Consume)} -> {e : Expr} -> {es : List Expr} ->
  argsEvalFoot acc (e :: es) =
    (fst (argFootprint acc e) ++ fst (argsEvalFoot acc es),
     snd (argFootprint acc e) ++ snd (argsEvalFoot acc es))
argsEvalFootCons = Refl

argsCallFootCons :
  {acc : List (String, List Consume)} -> {e : Expr} -> {es : List Expr} ->
  {ms : List Consume} ->
  argsCallFoot acc (e :: es) ms =
    (fst (argModeFoot acc e (consumeHead ms)) ++
       fst (argsCallFoot acc es (consumeTail ms)),
     snd (argModeFoot acc e (consumeHead ms)) ++
       snd (argsCallFoot acc es (consumeTail ms)))
argsCallFootCons = Refl

||| `aliasBad` is the footprint overlap or empty-start `storedLiveGo`.
||| Unfolding lets `orFalseC` see the `||`; the function name alone does not.
||| M2(a) remaining: `callOverlap = False -> storedLiveGo acc [] es ms = False`
||| (`storedQuietFromFoots`). The four `storedBorrowConsume = True` shapes
||| already have `callOverlap = True` (`storedBorrow*Overlaps`). Until the
||| implication lands, `storedBorrowConsume` stays in `aliasBad`.
aliasBadOpen : (ctx : Ctx) -> (es : List Expr) -> (callee : String) ->
  aliasBad ctx es callee =
    callOverlap ctx.summaries es (funModes ctx callee)
      || storedBorrowConsume ctx.summaries es (funModes ctx callee)
aliasBadOpen _ _ _ = Refl

||| Empty-start `storedLiveGo` is the second flag of `aliasBad`.
export
aliasStoredQuiet : {ctx : Ctx} -> {es : List Expr} -> {callee : String} ->
                   aliasBad ctx es callee = False ->
                   storedLiveGo ctx.summaries [] es (funModes ctx callee) = False
aliasStoredQuiet {ctx} {es} {callee} prf =
  let opened = replace {p = \b => b = False} (aliasBadOpen ctx es callee) prf
  in snd (orFalseC _ _ opened)

||| `callOverlap` is the first flag of `aliasBad`.
export
aliasCallQuiet : {ctx : Ctx} -> {es : List Expr} -> {callee : String} ->
                 aliasBad ctx es callee = False ->
                 callOverlap ctx.summaries es (funModes ctx callee) = False
aliasCallQuiet {ctx} {es} {callee} prf =
  let opened = replace {p = \b => b = False} (aliasBadOpen ctx es callee) prf
  in fst (orFalseC _ _ opened)

||| Unfold `callOverlap` on a cons so `orFalseC` sees the `||`.
export
callOverlapOpen :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  callOverlap acc (e :: es) ms =
    footHits (argModeFoot acc e (consumeHead ms))
      (callFoots acc es (consumeTail ms))
    || callOverlap acc es (consumeTail ms)
callOverlapOpen = Refl

||| Tail footprints stay disjoint.
export
callOverlapTail :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  callOverlap acc (e :: es) ms = False ->
  callOverlap acc es (consumeTail ms) = False
callOverlapTail {acc} {e} {es} {ms} prf =
  snd (orFalseC _ _
    (replace {p = \b => b = False} (callOverlapOpen {acc} {e} {es} {ms}) prf))

||| Head-vs-rest footprints stay disjoint.
export
callOverlapHits :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  callOverlap acc (e :: es) ms = False ->
  footHits (argModeFoot acc e (consumeHead ms))
    (callFoots acc es (consumeTail ms)) = False
callOverlapHits {acc} {e} {es} {ms} prf =
  fst (orFalseC _ _
    (replace {p = \b => b = False} (callOverlapOpen {acc} {e} {es} {ms}) prf))

pairEq : (x : (a, b)) -> (fst x, snd x) = x
pairEq (u, v) = Refl

||| A consume-mode write set includes `valuePlaces`.
export
valueInConsumeW :
  {acc : List (String, List Consume)} -> {e : Expr} -> {m : Consume} ->
  {p : Place} ->
  doesConsume m = True ->
  placeIn p (valuePlaces e) = True ->
  placeIn p (fst (argModeFoot acc e m)) = True
valueInConsumeW {acc} {e} {m} {p} pc pin =
  replace {p = \xs => placeIn p xs = True}
    (sym (modeWConsume {acc} {e} {m} pc))
    (placeInJoinR {p} {xs = fst (argFootprint acc e)}
       {ys = snd (argFootprint acc e) ++ valuePlaces e}
       (placeInJoinR {p} {xs = snd (argFootprint acc e)}
          {ys = valuePlaces e} pin))

||| A borrow-mode read set includes `valuePlaces`.
export
valueInBorrowR :
  {acc : List (String, List Consume)} -> {e : Expr} -> {m : Consume} ->
  {p : Place} ->
  doesConsume m = False ->
  placeIn p (valuePlaces e) = True ->
  placeIn p (snd (argModeFoot acc e m)) = True
valueInBorrowR {acc} {e} {m = Never} {p} _ pin =
  placeInJoinR {p} {xs = snd (argFootprint acc e)} {ys = valuePlaces e} pin
valueInBorrowR {m = May} pc _ = void (trueNotFalseC pc)
valueInBorrowR {m = Always} pc _ = void (trueNotFalseC pc)

||| `p` in `W` and in a later `R ∪ W` makes `footHits` true.
hitsFromWriteRead :
  {w, r, w2, r2 : List Place} -> {rest : List (List Place, List Place)} ->
  {p : Place} ->
  placeIn p w = True ->
  placeIn p (r2 ++ w2) = True ->
  footHits (w, r) ((w2, r2) :: rest) = True
hitsFromWriteRead {w} {r} {r2} {w2} {rest} pinW pinR =
  rewrite overlapBuild {xs = w} {ys = r2 ++ w2} pinW pinR in
    orTrueLeft (placesOverlap w2 (r ++ w) || footHits (w, r) rest)

||| `p` in this `R ∪ W` and in a later `W` makes `footHits` true.
hitsFromReadWrite :
  {w, r, w2, r2 : List Place} -> {rest : List (List Place, List Place)} ->
  {p : Place} ->
  placeIn p (r ++ w) = True ->
  placeIn p w2 = True ->
  footHits (w, r) ((w2, r2) :: rest) = True
hitsFromReadWrite {w} {r} {w2} {r2} {rest} pinR pinW =
  rewrite overlapBuild {xs = w2} {ys = r ++ w} pinW pinR in
    rewrite orTrueLeft (footHits (w, r) rest) in
      orTrueRight (placesOverlap w (r2 ++ w2))

||| A later `footHits` stays a `footHits` after one more pair.
hitsSuff :
  {w, r : List Place} -> {f : (List Place, List Place)} ->
  {rest : List (List Place, List Place)} ->
  footHits (w, r) rest = True ->
  footHits (w, r) (f :: rest) = True
hitsSuff {f} {w} {r} {rest} prf =
  replace {p = \pair => footHits (w, r) (pair :: rest) = True}
    (pairEq f)
    (suffGo (fst f) (snd f) prf)
  where
    suffGo : (w2, r2 : List Place) ->
             footHits (w, r) rest = True ->
             footHits (w, r) ((w2, r2) :: rest) = True
    suffGo w2 r2 prf0 =
      rewrite prf0 in
        rewrite orTrueRight (placesOverlap w2 (r ++ w)) in
          orTrueRight (placesOverlap w (r2 ++ w2))

borrowRHasValue :
  {acc : List (String, List Consume)} -> {e : Expr} -> {m : Consume} ->
  {p : Place} ->
  doesConsume m = False ->
  placeIn p (valuePlaces e) = True ->
  placeIn p (snd (argModeFoot acc e m) ++ fst (argModeFoot acc e m)) = True
borrowRHasValue {acc} {e} {p} pc pin =
  placeInAppendL (valueInBorrowR {acc} {e} pc pin)

hitHereConsume :
  {acc : List (String, List Consume)} ->
  {e, e1 : Expr} -> {m, m1 : Consume} -> {es1 : List Expr} ->
  {ms1 : List Consume} -> {p : Place} ->
  doesConsume m = False ->
  doesConsume m1 = True ->
  placeIn p (valuePlaces e) = True ->
  placeIn p (valuePlaces e1) = True ->
  footHits (argModeFoot acc e m)
    (argModeFoot acc e1 m1 :: callFoots acc es1 ms1) = True
hitHereConsume {acc} {e} {e1} {m} {m1} {es1} {ms1} {p} pc pc1 pinH pinV =
  replace {p = \wr => footHits wr (argModeFoot acc e1 m1 :: callFoots acc es1 ms1) = True}
    (pairEq (argModeFoot acc e m))
    (replace {p = \wr =>
                footHits (fst (argModeFoot acc e m), snd (argModeFoot acc e m))
                  (wr :: callFoots acc es1 ms1) = True}
       (pairEq (argModeFoot acc e1 m1))
       (hitsFromReadWrite {w = fst (argModeFoot acc e m)}
          {r = snd (argModeFoot acc e m)}
          {w2 = fst (argModeFoot acc e1 m1)}
          {r2 = snd (argModeFoot acc e1 m1)}
          {rest = callFoots acc es1 ms1}
          (borrowRHasValue {acc} {e} {m} {p} pc pinH)
          (valueInConsumeW {acc} {e = e1} {m = m1} {p} pc1 pinV)))

||| Later consume `valuePlaces` sit in that argument's write set, so a
||| borrow head that already named `p` overlaps.
laterConsumeHits :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  {p : Place} ->
  doesConsume m = False ->
  placeIn p (valuePlaces e) = True ->
  placeIn p (aliasConsumePlaces es ms) = True ->
  footHits (argModeFoot acc e m) (callFoots acc es ms) = True
laterConsumeHits {es = []} _ _ pinC =
  void (trueNotFalseC (sym pinC))
laterConsumeHits {acc} {e} {es = e1 :: es1} {m} {ms = []} {p} pc pinH pinC =
  case inAppend {p} {xs = valuePlaces e1} {ys = aliasConsumePlaces es1 []} pinC of
    Left pinV =>
      hitHereConsume {acc} {e} {e1} {m} {m1 = Always} {es1} {ms1 = []} {p}
        pc Refl pinH pinV
    Right pinRest =>
      replace {p = \wr => footHits wr (callFoots acc (e1 :: es1) []) = True}
        (pairEq (argModeFoot acc e m))
        (hitsSuff {w = fst (argModeFoot acc e m)} {r = snd (argModeFoot acc e m)}
           {f = argModeFoot acc e1 Always}
           (replace {p = \wr => footHits wr (callFoots acc es1 []) = True}
              (sym (pairEq (argModeFoot acc e m)))
              (laterConsumeHits {acc} {e} {es = es1} {m} {ms = []} {p}
                 pc pinH pinRest)))
laterConsumeHits {acc} {e} {es = e1 :: es1} {m} {ms = m1 :: ms1} {p} pc pinH pinC =
  go (doesConsume m1) Refl
  where
    go : (b : Bool) -> doesConsume m1 = b ->
         footHits (argModeFoot acc e m) (callFoots acc (e1 :: es1) (m1 :: ms1)) = True
    rec : {ms' : List Consume} ->
          placeIn p (aliasConsumePlaces es1 ms') = True ->
          footHits (fst (argModeFoot acc e m), snd (argModeFoot acc e m))
            (callFoots acc es1 ms') = True
    rec {ms'} pinRest =
      replace {p = \wr => footHits wr (callFoots acc es1 ms') = True}
        (sym (pairEq (argModeFoot acc e m)))
        (laterConsumeHits {acc} {e} {es = es1} {m} {ms = ms'} {p} pc pinH pinRest)
    go True pc1 =
      case inAppend {p} {xs = valuePlaces e1} {ys = aliasConsumePlaces es1 ms1}
             (replace {p = \ps => placeIn p ps = True}
                (aliasConsumeConsume {e = e1} {es = es1} {m = m1} {ms = ms1} pc1)
                pinC) of
        Left pinV =>
          hitHereConsume {acc} {e} {e1} {m} {m1} {es1} {ms1} {p} pc pc1 pinH pinV
        Right pinRest =>
          replace {p = \wr => footHits wr (callFoots acc (e1 :: es1) (m1 :: ms1)) = True}
            (pairEq (argModeFoot acc e m))
            (hitsSuff {w = fst (argModeFoot acc e m)} {r = snd (argModeFoot acc e m)}
               {f = argModeFoot acc e1 m1} (rec pinRest))
    go False pc1 =
      replace {p = \wr => footHits wr (callFoots acc (e1 :: es1) (m1 :: ms1)) = True}
        (pairEq (argModeFoot acc e m))
        (hitsSuff {w = fst (argModeFoot acc e m)} {r = snd (argModeFoot acc e m)}
           {f = argModeFoot acc e1 m1}
           (rec (replace {p = \ps => placeIn p ps = True}
                   (aliasConsumeBorrow {e = e1} {es = es1} {m = m1} {ms = ms1} pc1)
                   pinC)))

||| A borrow head whose value is `p` is not a later consume.
export
consumeQuietFromOverlap :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  {p : Place} ->
  doesConsume m = False ->
  placeIn p (valuePlaces e) = True ->
  callOverlap acc (e :: es) (m :: ms) = False ->
  placeIn p (aliasConsumePlaces es ms) = False
consumeQuietFromOverlap {acc} {e} {es} {m} {ms} {p} pc pin ov =
  missGo (placeIn p (aliasConsumePlaces es ms)) Refl
  where
    missGo : (b : Bool) -> placeIn p (aliasConsumePlaces es ms) = b ->
             placeIn p (aliasConsumePlaces es ms) = False
    missGo False pb = pb
    missGo True pb =
      void (trueNotFalseC
        (trans (sym (laterConsumeHits {acc} {e} {es} {m} {ms} {p} pc pin pb))
          (callOverlapHits {acc} {e} {es} {ms = m :: ms} ov)))

||| Empty argument list: no pair to overlap.
export
callOverlapNil : {acc : List (String, List Consume)} -> {ms : List Consume} ->
                 callOverlap acc [] ms = False
callOverlapNil = Refl

||| Unfold `footsWrites` on a cons without matching the pair constructor.
export
footsWritesOpen :
  {f : (List Place, List Place)} -> {fs : List (List Place, List Place)} ->
  footsWrites (f :: fs) = fst f ++ footsWrites fs
footsWritesOpen {f} {fs} =
  replace {p = \pair => footsWrites (pair :: fs) = fst pair ++ footsWrites fs}
    (pairEq f) Refl

||| `p` in a later write set and in this `R ∪ W` makes `footHits` true.
laterWriteHits :
  {w, r : List Place} -> {fs : List (List Place, List Place)} -> {p : Place} ->
  placeIn p (r ++ w) = True ->
  placeIn p (footsWrites fs) = True ->
  footHits (w, r) fs = True
laterWriteHits {fs = []} _ pinW = void (trueNotFalseC (sym pinW))
laterWriteHits {w} {r} {fs = f :: rest} {p} pinR pinW =
  replace {p = \pair => footHits (w, r) (pair :: rest) = True}
    (pairEq f)
    (go (fst f) (snd f)
      (replace {p = \xs => placeIn p xs = True} (footsWritesOpen {f} {fs = rest}) pinW))
  where
    go : (w2, r2 : List Place) ->
         placeIn p (w2 ++ footsWrites rest) = True ->
         footHits (w, r) ((w2, r2) :: rest) = True
    go w2 r2 pin =
      case inAppend {p} {xs = w2} {ys = footsWrites rest} pin of
        Left pinH =>
          hitsFromReadWrite {w} {r} {w2} {r2} {rest} pinR pinH
        Right pinT =>
          hitsSuff {w} {r} {f = (w2, r2)} {rest}
            (laterWriteHits {w} {r} {fs = rest} {p} pinR pinT)

||| A quiet `footHits` cannot write a place this pair already named.
export
laterWriteQuiet :
  {w, r : List Place} -> {fs : List (List Place, List Place)} -> {p : Place} ->
  placeIn p (r ++ w) = True ->
  footHits (w, r) fs = False ->
  placeIn p (footsWrites fs) = False
laterWriteQuiet {w} {r} {fs} {p} pinR hits =
  missGo (placeIn p (footsWrites fs)) Refl
  where
    missGo : (b : Bool) -> placeIn p (footsWrites fs) = b ->
             placeIn p (footsWrites fs) = False
    missGo False pb = pb
    missGo True pb =
      void (trueNotFalseC (trans (sym (laterWriteHits {w} {r} {fs} {p} pinR pb)) hits))

||| A borrow head whose value is `p` is not in a later write set.
export
laterWriteQuietFromOverlap :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  {p : Place} ->
  doesConsume m = False ->
  placeIn p (valuePlaces e) = True ->
  callOverlap acc (e :: es) (m :: ms) = False ->
  placeIn p (footsWrites (callFoots acc es ms)) = False
laterWriteQuietFromOverlap {acc} {e} {es} {m} {ms} {p} pc pin ov =
  laterWriteQuiet {w = fst (argModeFoot acc e m)} {r = snd (argModeFoot acc e m)}
    {fs = callFoots acc es ms} {p}
    (borrowRHasValue {acc} {e} {m} {p} pc pin)
    (replace {p = \wr => footHits wr (callFoots acc es ms) = False}
       (sym (pairEq (argModeFoot acc e m)))
       (callOverlapHits {acc} {e} {es} {ms = m :: ms} ov))

||| Membership in concatenated later `W ++ R` is this pair's `R ∪ W` or the rest.
callWRMember :
  {p : Place} -> {w2, wt, r2, rt : List Place} ->
  placeIn p ((w2 ++ wt) ++ (r2 ++ rt)) = True ->
  Either (placeIn p (r2 ++ w2) = True) (placeIn p (wt ++ rt) = True)
callWRMember {p} {w2} {wt} {r2} {rt} pin =
  case inAppend {p} {xs = w2 ++ wt} {ys = r2 ++ rt} pin of
    Left inW =>
      case inAppend {p} {xs = w2} {ys = wt} inW of
        Left inW2 => Left (placeInJoinR {p} {xs = r2} {ys = w2} inW2)
        Right inWt => Right (placeInAppendL {p} {xs = wt} {ys = rt} inWt)
    Right inR =>
      case inAppend {p} {xs = r2} {ys = rt} inR of
        Left inR2 => Left (placeInAppendL {p} {xs = r2} {ys = w2} inR2)
        Right inRt => Right (placeInJoinR {p} {xs = wt} {ys = rt} inRt)

||| `p` in this write set and in a later `W ++ R` makes `footHits` true.
||| Twin of `laterWriteHits` (later `W` from `R ∪ W` of this pair). Head
||| `W` vs later `R ∪ W` is `hitsFromWriteRead`.
laterCallWRHits :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  {p : Place} ->
  placeIn p (fst (argModeFoot acc e m)) = True ->
  placeIn p (fst (argsCallFoot acc es ms) ++
             snd (argsCallFoot acc es ms)) = True ->
  footHits (argModeFoot acc e m) (callFoots acc es ms) = True
laterCallWRHits {es = []} _ pin = void (trueNotFalseC (sym pin))
laterCallWRHits {acc} {e} {es = e1 :: es1} {m} {ms} {p} pinW pinRest =
  replace {p = \wr => footHits wr (callFoots acc (e1 :: es1) ms) = True}
    (pairEq (argModeFoot acc e m))
    (replace {p = \wr =>
                footHits (fst (argModeFoot acc e m), snd (argModeFoot acc e m))
                  (wr :: callFoots acc es1 (consumeTail ms)) = True}
       (pairEq (argModeFoot acc e1 (consumeHead ms)))
       (hereOrLater pinRest))
  where
    hereOrLater :
      placeIn p (fst (argsCallFoot acc (e1 :: es1) ms) ++
                 snd (argsCallFoot acc (e1 :: es1) ms)) = True ->
      footHits (fst (argModeFoot acc e m), snd (argModeFoot acc e m))
        ((fst (argModeFoot acc e1 (consumeHead ms)),
          snd (argModeFoot acc e1 (consumeHead ms))) ::
         callFoots acc es1 (consumeTail ms)) = True
    hereOrLater pin0 =
      case callWRMember {p}
             {w2 = fst (argModeFoot acc e1 (consumeHead ms))}
             {wt = fst (argsCallFoot acc es1 (consumeTail ms))}
             {r2 = snd (argModeFoot acc e1 (consumeHead ms))}
             {rt = snd (argsCallFoot acc es1 (consumeTail ms))}
             pin0 of
        Left pinHere =>
          hitsFromWriteRead
            {w = fst (argModeFoot acc e m)}
            {r = snd (argModeFoot acc e m)}
            {w2 = fst (argModeFoot acc e1 (consumeHead ms))}
            {r2 = snd (argModeFoot acc e1 (consumeHead ms))}
            {rest = callFoots acc es1 (consumeTail ms)}
            pinW pinHere
        Right pinTail =>
          hitsSuff
            {w = fst (argModeFoot acc e m)}
            {r = snd (argModeFoot acc e m)}
            {f = (fst (argModeFoot acc e1 (consumeHead ms)),
                  snd (argModeFoot acc e1 (consumeHead ms)))}
            {rest = callFoots acc es1 (consumeTail ms)}
            (replace {p = \wr =>
                footHits wr (callFoots acc es1 (consumeTail ms)) = True}
               (sym (pairEq (argModeFoot acc e m)))
               (laterCallWRHits {acc} {e} {es = es1} {m}
                  {ms = consumeTail ms} {p} pinW pinTail))

||| Dest intern in this argument's write set and a quiet M1 `callOverlap`
||| cannot sit in a later argument's `W ++ R`. Twin of `laterWriteQuiet`
||| (later `W` from `R ∪ W` of this pair). Extra Always `[]` gets the same
||| miss from Always writes (`argsModesKeepLookupExtraMiss`); remaining
||| modes need the `W ++ R` form for `modesKeepWR`.
export
laterCallWRQuiet :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  {p : Place} ->
  placeIn p (fst (argModeFoot acc e m)) = True ->
  callOverlap acc (e :: es) (m :: ms) = False ->
  placeIn p (fst (argsCallFoot acc es ms) ++
             snd (argsCallFoot acc es ms)) = False
laterCallWRQuiet {acc} {e} {es} {m} {ms} {p} pinW ov =
  missGo (placeIn p (fst (argsCallFoot acc es ms) ++
                     snd (argsCallFoot acc es ms))) Refl
  where
    missGo : (b : Bool) ->
             placeIn p (fst (argsCallFoot acc es ms) ++
                        snd (argsCallFoot acc es ms)) = b ->
             placeIn p (fst (argsCallFoot acc es ms) ++
                        snd (argsCallFoot acc es ms)) = False
    missGo False pb = pb
    missGo True pb =
      void (trueNotFalseC
        (trans (sym (laterCallWRHits {acc} {e} {es} {m} {ms} {p} pinW pb))
          (callOverlapHits {acc} {e} {es} {ms = m :: ms} ov)))

||| `modesCover []` holds only for an empty argument list, and that walk
||| is quiet at every live set.
storedLiveGoCoverNil : (acc : List (String, List Consume)) ->
                       (live : List Place) ->
                       (es : List Expr) ->
                       modesCover [] es = True ->
                       storedLiveGo acc live es [] = False
storedLiveGoCoverNil _ _ [] _ = Refl
storedLiveGoCoverNil _ _ (_ :: _) prf = void (trueNotFalseC (sym prf))

||| An accepted defined call whose modes cover its arguments has a quiet
||| pin-live `storedLiveGo`. Empty-start quiet is `aliasBad`'s second
||| flag, from `checkCall = Right`. The two `nestedGo` facts stay
||| premises: they are the outer `Never` head, not this call. A short
||| mode list is excluded (`h(f(p))`, `f` at `[]`). This does not say
||| the callee body keeps the cell live.
export
acceptedCovered : {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} ->
                  {callee : String} -> {es : List Expr} -> {live : List Place} ->
                  modesCover (funModes ctx callee) es = True ->
                  checkCall ctx sc id callee es = Right sc' ->
                  isBuiltin callee = False ->
                  isDefined ctx callee = True ->
                  nestedGo ctx.summaries live [ECall id callee es] = False ->
                  nestedGo ctx.summaries (nestStoreds es) [ECall id callee es] = False ->
                  storedLiveGo ctx.summaries live es (funModes ctx callee) = False
acceptedCovered {ctx} {id} {callee} {es} {live} cov eq pb pd nLive nNest =
  let bad = callDefinedNoAlias {nid = id} {args = es} eq pb pd
  in case calleeModesFunModes ctx callee of
       Left same =>
         coveredStored {acc = ctx.summaries} {live} {id} {callee} {es}
                       {ms = funModes ctx callee}
                       cov same nLive nNest (aliasStoredQuiet bad)
       Right (fm, _) =>
         replace {p = \ms => storedLiveGo ctx.summaries live es ms = False}
                 (sym fm)
                 (storedLiveGoCoverNil ctx.summaries live es
                    (replace {p = \ms => modesCover ms es = True} fm cov))

||| `readPlaces` of a variable is that one place.
varOverlap : {id : Nat} -> {p : Place} -> {nm : String} -> {live : List Place} ->
             placeIn p live = True ->
             placesOverlap (readPlaces (EVar id p nm)) live = True
varOverlap pin = rewrite pin in orTrueLeft (placesOverlap [] live)

||| A missing mode is a consume, so a quiet walk did not read `live`.
storedHeadExtra : {acc : List (String, List Consume)} ->
                  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
                  storedLiveGo acc live (e :: es) [] = False ->
                  placesOverlap (readPlaces e) live = False
storedHeadExtra {acc} {live} {e} {es} prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es [] = False ->
         placesOverlap (readPlaces e) live = False
    go False eq _ = eq
    go True _ pr0 = void (trueNotFalseC pr0)

||| A consume head that is a variable in the pin live is not quiet.
||| Covering modes use `May` or `Always` (`doesConsume`). The owner place
||| is such a variable, so this head is not `EVar ownQ`.
export
storedVarOwner : {acc : List (String, List Consume)} ->
                 {live : List Place} ->
                 {id : Nat} -> {p : Place} -> {nm : String} ->
                 {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                 placeIn p live = True ->
                 doesConsume m = True ->
                 storedLiveGo acc live (EVar id p nm :: es) (m :: ms) = False ->
                 Void
storedVarOwner {id} {p} {nm} pin pc quiet =
  trueNotFalseC (trans (sym (varOverlap {id} {p} {nm} pin))
                       (storedHeadOverlap pc quiet))

||| Same fact when the mode list has run out. `consumeHead [] = Always`.
export
storedVarExtra : {acc : List (String, List Consume)} ->
                 {live : List Place} ->
                 {id : Nat} -> {p : Place} -> {nm : String} ->
                 {es : List Expr} ->
                 placeIn p live = True ->
                 storedLiveGo acc live (EVar id p nm :: es) [] = False ->
                 Void
storedVarExtra {id} {p} {nm} pin quiet =
  trueNotFalseC (trans (sym (varOverlap {id} {p} {nm} pin))
                       (storedHeadExtra quiet))

||| An empty mode list binds a pointer parameter as borrowed. `h(f(p))`
||| with `f` at `[]` is this binding. Copy parameters are skipped by
||| `bindParams`; this is the pointer at the head of the remaining list.
export
bindExtraBorrowed : (fid : Nat) -> (p : Param) -> (ps : List Param) ->
                    p.ty = Ptr ->
                    lookupPlace p.place (bindParams fid (p :: ps) []) =
                      Just (Pagurus.Status.singleton (ABorrowed fid))
bindExtraBorrowed fid p ps pty =
  rewrite pty in rewrite eqNatRefl p.place in Refl

||| Dropping a borrowed status is not a successful step.
export
borrowedDropStep : (fid, nid : Nat) -> (st' : Status) ->
                   stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Drop nid = Right st' ->
                   Void
borrowedDropStep _ _ _ eq = leftNotRightChk eq

dropPlaceLeft : {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
                {st : Status} -> {d : Diag} ->
                lookupPlace n sc = Just st ->
                stepStatus st Drop nid = Left d ->
                dropPlace sc n nid nm = Left (withName nm d)
dropPlaceLeft pL pS = rewrite pL in rewrite pS in Refl

||| The initial scope of an empty mode list rejects `free` of that parameter.
export
extraDropVoid : (fid, nid : Nat) -> (nm : String) ->
                (p : Param) -> (ps : List Param) ->
                p.ty = Ptr ->
                (sc' : Scopes) ->
                dropPlace (bindParams fid (p :: ps) []) p.place nid nm = Right sc' ->
                Void
extraDropVoid fid nid nm p ps pty sc' eq =
  let look = bindExtraBorrowed fid p ps pty
  in stepGo (stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Drop nid) Refl look
  where
    stepGo : (r : Either Diag Status) ->
             stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Drop nid = r ->
             lookupPlace p.place (bindParams fid (p :: ps) []) =
               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
             Void
    stepGo (Left d) pS look =
      void (leftNotRightChk (trans (sym (dropPlaceLeft look pS)) eq))
    stepGo (Right st') pS _ = borrowedDropStep fid nid st' pS

||| Same rejection through `checkStmt`. One drop, at this scope.
export
extraStmtDropVoid : (fuel : Nat) -> (ctx : Ctx) ->
                    (fid, nid : Nat) -> (nm : String) ->
                    (p : Param) -> (ps : List Param) ->
                    p.ty = Ptr ->
                    (sc' : Scopes) ->
                    checkStmt (S fuel) ctx (bindParams fid (p :: ps) [])
                      (SDrop nid p.place nm) = Right sc' ->
                    Void
extraStmtDropVoid fuel ctx fid nid nm p ps pty sc' eq =
  extraDropVoid fid nid nm p ps pty sc'
    (trans (sym (checkStmtDrop fuel ctx (bindParams fid (p :: ps) [])
                   nid p.place nm)) eq)

||| Moving a borrowed status is not a successful step.
export
borrowedMoveStep : (fid, nid : Nat) -> (st' : Status) ->
                   stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Move nid = Right st' ->
                   Void
borrowedMoveStep _ _ _ eq = leftNotRightChk eq

movePlaceLeft : {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
                {st : Status} -> {d : Diag} ->
                lookupPlace n sc = Just st ->
                stepStatus st Move nid = Left d ->
                movePlace sc n nid nm = Left (withName nm d)
movePlaceLeft pL pS = rewrite pL in rewrite pS in Refl

||| Any scope whose lookup is still this borrowed status rejects a move.
export
borrowedMovePlace : {sc, sc' : Scopes} -> {fid, nid : Nat} ->
                    {n : Place} -> {nm : String} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    movePlace sc n nid nm = Right sc' ->
                    Void
borrowedMovePlace {fid} {nid} look eq =
  stepGo (stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Move nid) Refl
  where
    stepGo : (r : Either Diag Status) ->
             stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Move nid = r ->
             Void
    stepGo (Left d) pS =
      void (leftNotRightChk (trans (sym (movePlaceLeft look pS)) eq))
    stepGo (Right st') pS = borrowedMoveStep fid nid st' pS

||| `takeOwner` of that variable moves it, so it is not `Right`.
export
borrowedTakeVar : {ctx : Ctx} -> {sc, sc' : Scopes} -> {fl : Flag} ->
                  {fid, id : Nat} -> {n : Place} -> {nm : String} ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  takeOwner ctx sc (EVar id n nm) = Right (sc', fl) ->
                  Void
borrowedTakeVar {ctx} {sc} {id} {n} {nm} look eq =
  go (movePlace sc n id nm) Refl
  where
    go : (r : Either Diag Scopes) -> movePlace sc n id nm = r -> Void
    go (Left d) pM =
      void (leftNotRightChk (trans (sym (takeVarJustL ctx look pM)) eq))
    go (Right sc1) pM = borrowedMovePlace look pM

||| Use keeps the borrowed atom. `stepStatus []` is `Right []`, and
||| `insertSorted a []` is `[a]`.
export
borrowedUseStep : (fid, nid : Nat) ->
                  stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Use nid =
                    Right (Pagurus.Status.singleton (ABorrowed fid))
borrowedUseStep _ _ = Refl

usePlaceJust : {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
               {st, st' : Status} ->
               lookupPlace n sc = Just st ->
               stepStatus st Use nid = Right st' ->
               usePlace sc n nid nm = Right (setPlace n st' sc)
usePlaceJust pL pS = rewrite pL in rewrite pS in Refl

||| An accepted use of a borrowed place writes the same borrowed status back.
export
borrowedUsePlace : {sc : Scopes} -> {fid, nid : Nat} ->
                   {n : Place} -> {nm : String} ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   usePlace sc n nid nm =
                     Right (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
borrowedUsePlace {fid} {nid} look = usePlaceJust look (borrowedUseStep fid nid)

||| `checkExpr` of a variable is that use.
export
borrowedCheckVar : {ctx : Ctx} -> {sc : Scopes} -> {fid, id : Nat} ->
                   {n : Place} -> {nm : String} ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   checkExpr ctx sc (EVar id n nm) =
                     Right (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
borrowedCheckVar {ctx} {sc} {fid} {id} {n} {nm} look =
  trans (checkExprVar ctx sc id n nm) (borrowedUsePlace {fid} {nid = id} look)

||| Same use through an expression statement.
export
borrowedStmtUse : (fuel : Nat) -> {ctx : Ctx} -> {sc : Scopes} ->
                  {fid, eid, id : Nat} -> {n : Place} -> {nm : String} ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  checkStmt (S fuel) ctx sc (SExpr eid (EVar id n nm)) =
                    Right (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
borrowedStmtUse fuel {ctx} {sc} {fid} {eid} {id} {n} {nm} look =
  trans (checkStmtExpr fuel ctx sc eid (EVar id n nm))
        (borrowedCheckVar {ctx} {sc} {fid} {id} {n} {nm} look)

||| A copy assignment only checks the right-hand side, so the borrowed
||| place stays borrowed.
export
borrowedStmtAsgCopy : (fuel : Nat) -> {ctx : Ctx} -> {sc : Scopes} ->
                      {fid, aid, id : Nat} -> {dest, n : Place} ->
                      {dnm, nm : String} ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      checkStmt (S fuel) ctx sc
                        (SAssign aid dest dnm Copy (EVar id n nm)) =
                        Right (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
borrowedStmtAsgCopy fuel {ctx} {sc} {fid} {aid} {id} {dest} {n} {dnm} {nm} look =
  trans (checkStmtAsgCopy fuel aid dest dnm {ctx} {sc} {rhs = EVar id n nm})
        (borrowedCheckVar {ctx} {sc} {fid} {id} {n} {nm} look)

||| A copy initialiser is the same use.
export
borrowedStmtDeclCopy : (fuel : Nat) -> {ctx : Ctx} -> {sc : Scopes} ->
                       {fid, did, id : Nat} -> {dest, n : Place} ->
                       {dnm, nm : String} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S fuel) ctx sc
                         (SDecl did dest dnm Copy (Just (EVar id n nm))) =
                         Right (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
borrowedStmtDeclCopy fuel {ctx} {sc} {fid} {did} {id} {dest} {n} {dnm} {nm} look =
  trans (checkStmtDeclCopyJust fuel did dest dnm {ctx} {sc} {e = EVar id n nm})
        (borrowedCheckVar {ctx} {sc} {fid} {id} {n} {nm} look)

||| Dropping the borrowed place is void in any scope, not only the
||| initial `bindParams` scope.
export
borrowedDropPlace : {sc, sc' : Scopes} -> {fid, nid : Nat} ->
                    {n : Place} -> {nm : String} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    dropPlace sc n nid nm = Right sc' ->
                    Void
borrowedDropPlace {fid} {nid} look eq =
  stepGo (stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Drop nid) Refl
  where
    stepGo : (r : Either Diag Status) ->
             stepStatus (Pagurus.Status.singleton (ABorrowed fid)) Drop nid = r ->
             Void
    stepGo (Left d) pS =
      void (leftNotRightChk (trans (sym (dropPlaceLeft look pS)) eq))
    stepGo (Right st') pS = borrowedDropStep fid nid st' pS

||| Same rejection through `checkStmt`.
export
borrowedStmtDrop : (fuel : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                   {fid, nid : Nat} -> {n : Place} -> {nm : String} ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
                   Void
borrowedStmtDrop fuel ctx {sc} {fid} {nid} {n} {nm} look eq =
  borrowedDropPlace {fid} {nid} {n} {nm} look
    (trans (sym (checkStmtDrop fuel ctx sc nid n nm)) eq)

||| A pointer assignment of the borrowed variable moves it.
||| `ghostCopyLeak` of a variable is false, so the existing `stmtAsgPtrLeft`
||| applies. An overwrite from `malloc` is a different right-hand side.
borrowedAsgGo : (fuel : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                (fid, aid, id : Nat) -> (dest, n : Place) ->
                (dnm, nm : String) ->
                lookupPlace n sc =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                checkStmt (S fuel) ctx sc
                  (SAssign aid dest dnm Ptr (EVar id n nm)) = Right sc' ->
                (r : Either Diag (Scopes, Flag)) ->
                takeOwner ctx sc (EVar id n nm) = r ->
                Void
borrowedAsgGo fuel ctx sc _ fid aid id dest n dnm nm look eq (Left d) pT =
  void (leftNotRightChk
    (trans (sym (stmtAsgPtrLeft fuel aid dest dnm
                   {ctx} {sc} {rhs = EVar id n nm} Refl pT)) eq))
borrowedAsgGo _ ctx sc _ fid _ id _ n _ nm look _ (Right (sc1, fl1)) pT =
  borrowedTakeVar {ctx} {sc} {sc' = sc1} {fl = fl1} {fid} {id} {n} {nm} look pT

export
borrowedStmtAsgVar : (fuel : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                     {fid, aid, id : Nat} -> {dest, n : Place} ->
                     {dnm, nm : String} ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmt (S fuel) ctx sc
                       (SAssign aid dest dnm Ptr (EVar id n nm)) = Right sc' ->
                     Void
borrowedStmtAsgVar fuel ctx {sc} {sc'} {fid} {aid} {id} {dest} {n} {dnm} {nm}
                   look eq =
  borrowedAsgGo fuel ctx sc sc' fid aid id dest n dnm nm look eq
    (takeOwner ctx sc (EVar id n nm)) Refl

||| Returning the borrowed variable moves it.
borrowedRetGo : (fuel : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                (fid, rid, id : Nat) -> (n : Place) -> (nm : String) ->
                lookupPlace n sc =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                checkStmt (S fuel) ctx sc
                  (SReturn rid (Just (EVar id n nm))) = Right sc' ->
                (r : Either Diag (Scopes, Flag)) ->
                takeOwner ctx sc (EVar id n nm) = r ->
                Void
borrowedRetGo fuel ctx sc _ _ rid id n nm look eq (Left d) pT =
  void (leftNotRightChk
    (trans (sym (retVarLeft fuel ctx rid {sc} {nid = id} {n} {nm} pT)) eq))
borrowedRetGo _ ctx sc _ fid _ id n nm look _ (Right (sc1, fl1)) pT =
  borrowedTakeVar {ctx} {sc} {sc' = sc1} {fl = fl1} {fid} {id} {n} {nm} look pT

export
borrowedStmtRet : (fuel : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                  {fid, rid, id : Nat} -> {n : Place} -> {nm : String} ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  checkStmt (S fuel) ctx sc
                    (SReturn rid (Just (EVar id n nm))) = Right sc' ->
                  Void
borrowedStmtRet fuel ctx {sc} {sc'} {fid} {rid} {id} {n} {nm} look eq =
  borrowedRetGo fuel ctx sc sc' fid rid id n nm look eq
    (takeOwner ctx sc (EVar id n nm)) Refl

||| A consume head that reads a pin-live place is not a quiet
||| `storedLiveGo`. An assignment reads its right-hand side, so
||| `r = p` with `p` in the pin is this head. This does not change
||| what the checker accepts.
export
storedReadOwner : {acc : List (String, List Consume)} ->
                  {live : List Place} -> {p : Place} -> {e : Expr} ->
                  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                  placeIn p (readPlaces e) = True ->
                  placeIn p live = True ->
                  doesConsume m = True ->
                  storedLiveGo acc live (e :: es) (m :: ms) = False ->
                  Void
storedReadOwner inR pin pc quiet =
  trueNotFalseC (trans (sym (overlapBuild inR pin)) (storedHeadOverlap pc quiet))

||| Same fact when the mode list has run out.
export
storedReadExtra : {acc : List (String, List Consume)} ->
                  {live : List Place} -> {p : Place} -> {e : Expr} ->
                  {es : List Expr} ->
                  placeIn p (readPlaces e) = True ->
                  placeIn p live = True ->
                  storedLiveGo acc live (e :: es) [] = False ->
                  Void
storedReadExtra inR pin quiet =
  trueNotFalseC (trans (sym (overlapBuild inR pin)) (storedHeadExtra quiet))

||| `readPlaces` of an assignment is the right-hand side, and a variable
||| reads itself.
export
readAssignVar : (id, sid : Nat) -> (d, p : Place) -> (nm, snm : String) ->
                (ty : Ty) ->
                placeIn p (readPlaces (EAssign id d nm ty (EVar sid p snm))) = True
readAssignVar _ _ _ p _ _ _ = placeInHere p []

||| One argument's `argsHit` is that argument's `argFrees`.
argsHitSingleton : {acc : List (String, List Consume)} -> {p : Place} ->
                   {e : Expr} ->
                   argFrees acc p e = False ->
                   argsHit acc p [e] = False
argsHitSingleton prf = rewrite prf in Refl

||| Quiet across a longer argument list is quiet on the first argument.
nestedGoSingleton : {acc : List (String, List Consume)} ->
                    {ps : List Place} -> {e : Expr} -> {es : List Expr} ->
                    nestedGo acc ps (e :: es) = False ->
                    nestedGo acc ps [e] = False
nestedGoSingleton {ps = []} _ = Refl
nestedGoSingleton {acc} {ps = p :: qs} {e} {es} prf =
  let (hd, tl) = orFalseC _ _ prf
  in orFalseIntro (argsHitSingleton {acc} {p} {e} (argsHitHead {acc} {p} {e} {es} hd))
                  (nestedGoSingleton {acc} {ps = qs} {e} {es} tl)

nestPlaceCallEq : (id : Nat) -> (callee : String) -> (args : List Expr) ->
                  nestPlace (ECall id callee args) = nestStoreds args
nestPlaceCallEq _ _ _ = Refl

||| An outer `Never` head's `nestedMixed` says the inner call does not
||| free its own stored destinations. Empty mode tails are not this fact:
||| `modesCover [] (_ :: _)` is false, and `h(f(p))` stays accepted.
export
neverHeadStored : {ctx : Ctx} -> {id : Nat} -> {callee : String} ->
                  {inner, es : List Expr} -> {ms : List Consume} ->
                  nestedMixed ctx (ECall id callee inner :: es) (Never :: ms) = False ->
                  nestedGo ctx.summaries (nestStoreds inner)
                    [ECall id callee inner] = False
neverHeadStored {ctx} {id} {callee} {inner} {es} {ms} prf =
  let nb = nestBorrowBorrow {e = ECall id callee inner} {es} {m = Never} {ms} Refl
      mixed = replace {p = \b => b = False}
                (nestedMixedEq {ctx}
                   {es = ECall id callee inner :: es} {ms = Never :: ms}) prf
      opened0 = replace {p = \xs =>
                           nestedGo ctx.summaries xs
                             (ECall id callee inner :: es) = False}
                  nb mixed
      opened = replace {p = \xs =>
                          nestedGo ctx.summaries
                            (xs ++ nestBorrowPlaces es ms)
                            (ECall id callee inner :: es) = False}
                 (nestPlaceCallEq id callee inner) opened0
      head = nestedGoPlacesHead {acc = ctx.summaries}
               {xs = nestStoreds inner} {ys = nestBorrowPlaces es ms}
               {es = ECall id callee inner :: es} opened
  in nestedGoSingleton {acc = ctx.summaries} {ps = nestStoreds inner}
       {e = ECall id callee inner} {es} head

||| The two `nestedGo` premises of `acceptedCovered`, from an outer
||| `Never` head. The conclusion is pin-live `storedLiveGo` of the inner
||| arguments. It does not say the callee body keeps the cell live.
export
neverHeadCovered : {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} ->
                   {callee : String} -> {inner, es : List Expr} ->
                   {ms : List Consume} -> {live : List Place} ->
                   modesCover (funModes ctx callee) inner = True ->
                   checkCall ctx sc id callee inner = Right sc' ->
                   isBuiltin callee = False ->
                   isDefined ctx callee = True ->
                   storedLiveGo ctx.summaries live
                     (ECall id callee inner :: es) (Never :: ms) = False ->
                   nestedMixed ctx (ECall id callee inner :: es) (Never :: ms) = False ->
                   storedLiveGo ctx.summaries live inner (funModes ctx callee) = False
neverHeadCovered cov eq pb pd quiet mixed =
  acceptedCovered cov eq pb pd (storedHeadFree quiet) (neverHeadStored mixed)

