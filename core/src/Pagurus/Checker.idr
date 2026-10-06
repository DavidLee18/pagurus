||| Intra-procedural ownership checker with join and loop fixpoints.
module Pagurus.Checker

import Data.String
import Pagurus.IR
import Pagurus.Status
import Pagurus.Step

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
  movedInExpr : Place -> Expr -> Bool
  movedInExpr p (EVar _ q _) = p == q
  movedInExpr p (EAssign _ _ _ _ rhs) = movedInExpr p rhs
  movedInExpr p (EMalloc _ args) = movedInExprs p args
  movedInExpr p (ECall _ _ args) = movedInExprs p args
  movedInExpr p (EUse _ args) = movedInExprs p args
  movedInExpr _ (ELit _) = False
  movedInExpr _ (ENull _) = False
  movedInExpr _ (EUnsupported _ _) = False

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
lookupNamed ((n, ms) :: xs) k = if n == k then Just ms else lookupNamed xs k

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
calleeModes : List (String, List Consume) -> String -> List Consume
calleeModes acc callee =
  case lookupNamed acc callee of
    Nothing => if callee == "realloc" then [Always] else []
    Just ms => ms

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

export
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
  argAction True ctx sc e = mapDiscardFlag (takeOwner ctx sc e)

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

  export
  checkCall : Ctx -> Scopes -> Nat -> String -> List Expr -> Either Diag Scopes
  checkCall ctx sc id callee args =
    if isBuiltin callee
      then checkArgsBorrow ctx sc args
      else if isDefined ctx callee
        then checkArgsModes ctx sc callee args (funModes ctx callee)
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
paramScopesNil : (ctx : Ctx) -> (f : Fun) ->
  f.params = [] ->
  paramScopes ctx f = []
paramScopesNil ctx f prf = rewrite prf in Refl

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
checkCallDefined :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  checkCall ctx sc nid callee args =
    checkArgsModes ctx sc callee args (funModes ctx callee)
checkCallDefined pb pd = rewrite pb in rewrite pd in Refl

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
argsModesMoveRight :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} ->
  {m : Consume} -> {fl : Flag} ->
  doesConsume m = True ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) =
    checkArgsModes ctx sc1 callee es ms
argsModesMoveRight _ _ pc pT = rewrite pc in rewrite pT in Refl

export
argsModesExtraLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {callee : String} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkArgsModes ctx sc callee (e :: es) [] = Left (nameConsumedArg callee e d)
argsModesExtraLeft _ pT = rewrite pT in Refl

export
argsModesExtraRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {callee : String} -> {fl : Flag} ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  checkArgsModes ctx sc callee (e :: es) [] =
    checkArgsModes ctx sc1 callee es []
argsModesExtraRight _ pT = rewrite pT in Refl

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
