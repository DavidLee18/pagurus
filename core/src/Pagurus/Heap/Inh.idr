||| Leftover `InHand` through `checkExpr` / `takeOwner`, parameterized by
||| `ExprIHs` so Unique/Restore do not import Dispatch. Nested `HECallUser`
||| cannot consume leftover intern (`InHand` already unsafe), so the nested
||| frame is unheld and `framePres` keeps leftover `a` live.
module Pagurus.Heap.Inh

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Act
import Pagurus.Heap.Frame
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Args
import Pagurus.Heap.Call
import Pagurus.Heap.Pres
import Pagurus.Heap.Assign
import Pagurus.Heap.Unique
import Data.Nat
import Control.WellFounded

%default total

||| `S n` is never `<= Z`.
lteSuccZero : {n : Nat} -> LTE (S n) Z -> Void
lteSuccZero LTEZero impossible
lteSuccZero (LTESucc _) impossible

export
lteRefl : {n : Nat} -> LTE n n
lteRefl {n = Z} = LTEZero
lteRefl {n = S n} = LTESucc lteRefl

lteSuccR : {n, m : Nat} -> LTE n m -> LTE n (S m)
lteSuccR LTEZero = LTEZero
lteSuccR (LTESucc p) = LTESucc (lteSuccR p)

lteTrans : {a, b, c : Nat} -> LTE a b -> LTE b c -> LTE a c
lteTrans LTEZero _ = LTEZero
lteTrans (LTESucc p) (LTESucc q) = LTESucc (lteTrans p q)

ltePlusL : {a, b, c : Nat} -> LTE (a + b) c -> LTE a c
ltePlusL {a = Z} _ = LTEZero
ltePlusL {a = S a} (LTESucc p) = LTESucc (ltePlusL p)

ltePlusR : {a, b, c : Nat} -> LTE (a + b) c -> LTE b c
ltePlusR {a = Z} p = p
ltePlusR {a = S _} (LTESucc p) = lteSuccR (ltePlusR p)

-- `with` and `where` become their own functions in the mutual group, so a
-- recursive call there is not smaller than that helper's `Nat`. `case` is
-- inlined back into the `(S k)` clause, and the call on `k` counts.
-- The equality is returned, because `case` does not rewrite the scrutinee.
boolEq : (b : Bool) -> Either (b = False) (b = True)
boolEq False = Left Refl
boolEq True = Right Refl

eitherEq : (r : Either e a) ->
           Either (x ** r = Left x) (x ** r = Right x)
eitherEq (Left x) = Left (x ** Refl)
eitherEq (Right x) = Right (x ** Refl)


-- The size-change closure of one mutual group does not finish. `rec` is
-- this family at a strictly smaller fuel (`wfInd` on `Nat`). Each helper
-- takes a proof that the value's size fits in the fuel, so fuel Z on an
-- S-constructor is void. Same-fuel calls go to `*_b` and do not re-enter `rec`.
ltSucc : (n : Nat) -> LT n (S n)
ltSucc n = LTESucc lteRefl

record InhOps (k : Nat) where
  constructor MkInhOps
  inhExprH :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
  inhMallocGo :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA : HEnv} -> {h0, hA : Heap} -> {sc0, scY : Scopes} ->
      {mid : Nat} -> {margs : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA)) ->
      checkExpr ctx sc0 (EMalloc mid margs) = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhBorrow :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {es0 : List Expr} -> {vB : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhCallArgs :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhCallCons :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhModes :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhModesRest :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhTakeH :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      takeOwner ctx sc0 e0 = Right (scY, fl0) ->
      OverApprox envY hY scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
  inhTakeMalloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {mid : Nat} -> {margs : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (EMalloc mid margs) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhTakeAsgCopy :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Copy rhs) = Right (scY, fl0) ->
      {fk : LTE (evalSize ev) k} ->
      InHand envA hA scY a
  inhTakeUse :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {uid : Nat} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (EUse uid args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hA scY a
  inhTakeCall :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hA scY a
  inhTakeCallUser :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhTakeCallUserRet :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhTakeRealloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      (evs : HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  takeAsgNull :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  takeAsgMove :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  inhTakeAsgPtr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  exprAsgNull :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  exprAsgUse :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  inhAsgPtr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  inhCallUser :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhCallUserRet :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhRealloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      (evs : HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhReallocArgs :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalReallocArgs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envY hY scY a
  inhReallocTail :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhNoTakeLeftover :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {envY : HEnv} -> {hY : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      takeOwner ctx sc0 e0 = Right (scT, fl0) ->
      v0 = HVPtr a ->
      {fk : LTE (evalSize ev0) k} ->
      Void
  inhNotPtrExpr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      Not (v0 = HVPtr a)
  inhValsCall :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
  inhValsCons :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsReallocTail :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsBorrow :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {es0 : List Expr} -> {vB : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
  inhValsModes :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsModesRest :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a

InhRec : Nat -> Type
InhRec k = (j : Nat) -> LT j k -> InhOps j

mutual
  ||| Preserve leftover `InHand` through `checkExpr` of a remaining
  ||| (or nested) argument. Nested `HECallUser` cannot consume leftover
  ||| intern (`InHand` already unsafe), so the nested frame is unheld
  ||| and `framePres` keeps leftover `a` live.
  inhExprH_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
  inhExprH_b Z rec ihs inh oa (HEMalloc env1 hA evs) {e0 = EMalloc mid margs} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HEAsgCopy w env1 hA ev) {e0 = EAssign id n nm Copy rhs} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HEUse env1 hA evs) {e0 = EUse uid args} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HECall unk env1 hA evs) {e0 = ECall id calleeC args} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HECallUser pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HECallUserRet pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HERealloc pName pMiss env1 hA evs)
        {e0 = ECall id calleeC args} eq =
      void (lteSuccZero fk)
  inhExprH_b Z rec ihs inh oa (HEAsgPtr w env1 hA ev) {e0 = EAssign id n nm Ptr rhs} eq =
      void (lteSuccZero fk)
  inhExprH_b k rec ihs inh oa HELit {e0 = ELit id} eq =
      let scEq = rightInj (trans (sym (checkExprLit ctx sc0 id)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhExprH_b k rec ihs inh oa HENull {e0 = ENull id} eq =
      let scEq = rightInj (trans (sym (checkExprNull ctx sc0 id)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhExprH_b k rec ihs inh oa (HEVarLive c lookN cl) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH_b k rec ihs inh oa (HEVarNone lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH_b k rec ihs inh oa (HEVarCopy lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH_b k rec ihs inh oa (HEVarMiss lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH_b k rec ihs _ _ HEUnsup {e0 = EUnsupported nid reason} eq =
      void (unsupExprContraH nid reason eq)
  inhExprH_b (S k) rec ihs inh oa (HEMalloc env1 hA evs) {e0 = EMalloc mid margs} eq =
      (rec k (ltSucc k)).inhMallocGo {fk = fromLteSucc fk} ihs inh oa evs eq
  inhExprH_b (S k) rec ihs inh oa (HEAsgCopy w env1 hA ev) {e0 = EAssign id n nm Copy rhs} eq =
      (rec k (ltSucc k)).inhExprH {fk = fromLteSucc fk} ihs inh oa ev (trans (sym (checkExprAsgCopy id n nm)) eq)
  inhExprH_b (S k) rec ihs inh oa (HEUse env1 hA evs) {e0 = EUse uid args} eq =
      (rec k (ltSucc k)).inhBorrow {fk = fromLteSucc fk} ihs inh oa evs (trans (sym (checkExprUse ctx sc0 uid args)) eq)
  inhExprH_b (S k) rec ihs inh oa (HECall unk env1 hA evs) {e0 = ECall id calleeC args} eq =
      (rec k (ltSucc k)).inhCallArgs {fk = fromLteSucc fk} ihs inh oa evs
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH_b (S k) rec ihs inh oa (HECallUser pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      (rec k (ltSucc k)).inhCallUser {fk = fromLteSucc fk} ihs inh oa pB f look pDef evs evBody
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH_b (S k) rec ihs inh oa (HECallUserRet pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      (rec k (ltSucc k)).inhCallUserRet {fk = fromLteSucc fk} ihs inh oa pB f look pDef evs evBody
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH_b (S k) rec ihs inh oa (HERealloc pName pMiss env1 hA evs)
        {e0 = ECall id calleeC args} eq =
      (rec k (ltSucc k)).inhRealloc {fk = fromLteSucc fk} ihs inh oa pName evs
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH_b (S k) rec ihs inh oa (HEAsgPtr w env1 hA ev) {e0 = EAssign id n nm Ptr rhs} eq =
      (rec k (ltSucc k)).inhAsgPtr {fk = fromLteSucc fk} ihs inh oa ev eq

  inhMallocGo_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA : HEnv} -> {h0, hA : Heap} -> {sc0, scY : Scopes} ->
      {mid : Nat} -> {margs : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA)) ->
      checkExpr ctx sc0 (EMalloc mid margs) = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhMallocGo_b k rec ihs inh oa evs eq =
      let pA = trans (sym (checkExprMalloc ctx sc0 mid margs)) eq
          inhA = inhBorrow_b {fk = fk} k rec ihs inh oa evs pA
          nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
      in inhAllocPres inhA nf

  inhBorrow_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {es0 : List Expr} -> {vB : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhBorrow_b Z rec ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      void (lteSuccZero fk)
  inhBorrow_b k rec ihs inh _ HEArgsNil eq =
      let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc0)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhBorrow_b (S k) rec ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      let (scA ** (pE, pEs)) = argsBorrowSplit eq
          inhA = (rec k (ltSucc k)).inhExprH {fk = ltePlusL (fromLteSucc fk)} ihs inh oa evE pE
          oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
      in (rec k (ltSucc k)).inhBorrow {fk = ltePlusR (fromLteSucc fk)} ihs inhA oaA evEs pEs

  inhCallArgs_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhCallArgs_b Z rec ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      void (lteSuccZero fk)
  inhCallArgs_b k rec ihs inh oa HEArgsNil eq =
      let scEq = callNilScope eq
      in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
  inhCallArgs_b (S k) rec ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      (rec k (ltSucc k)).inhCallCons {fk = fromLteSucc fk} ihs inh oa eq evE evEs

  inhCallCons_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhCallCons_b k rec ihs inh oa eq evE evEs =
      case boolEq (isBuiltin calleeC) of
        Right pb =>
          let (scA ** (pE, pEs)) = argsBorrowSplit
                (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
              inhA = inhExprH_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
          in inhBorrow_b {fk = ltePlusR fk} k rec ihs inhA oaA evEs pEs
        Left pb =>
          case boolEq (isDefined ctx calleeC) of
            Left pd =>
              case boolEq (isRealloc calleeC) of
                Left pr =>
                  void (callOpaqueContraH pb pr pd eq)
                Right pr =>
                  inhReallocTail_b {fk = fk} k rec ihs inh oa
                    (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
            Right pd =>
              let pbad = callDefinedNoAlias eq pb pd
                  pModes = trans (sym (checkCallDefined pb pd pbad)) eq
              in inhModes_b {fk = fk} k rec ihs inh oa pModes evE evEs

  inhModes_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhModes_b k rec ihs inh oa eq evE evEs {modes = []} =
      case argsModesExtraSplit eq of
        (_ ** (Ghost ** (pT, _))) =>
          void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
        (sc2 ** (Owner ** (pT, pEs2))) =>
          let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in inhModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs
        (sc2 ** (Null ** (pT, pEs2))) =>
          let ht = ihs.takeIH evE sc0 sc2 Null pT oa
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in inhModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs
  inhModes_b k rec ihs inh oa eq evE evEs {modes = m :: ms} =
      case boolEq (doesConsume m) of
        Left pc =>
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc eq
              inh1 = inhExprH_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
          in inhModesRest_b {fk = ltePlusR fk} k rec ihs inh1 oa1 pEs2 evEs
        Right pc =>
          case argsModesMoveSplit pc eq of
            (_ ** (Ghost ** (pT, _))) =>
              void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
            (sc2 ** (Owner ** (pT, pEs2))) =>
              let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                  inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
              in inhModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs
            (sc2 ** (Null ** (pT, pEs2))) =>
              let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                  inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
              in inhModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs

  inhModesRest_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
  inhModesRest_b Z rec ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      void (lteSuccZero fk)
  inhModesRest_b k rec ihs inh _ eq HEArgsNil =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 calleeC modes)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhModesRest_b (S k) rec ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      (rec k (ltSucc k)).inhModes {fk = fromLteSucc fk} ihs inh oa eq evE evEs

  inhTakeH_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      takeOwner ctx sc0 e0 = Right (scY, fl0) ->
      OverApprox envY hY scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
  inhTakeH_b Z rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HEAsgCopy w envA hA ev) {e0 = EAssign id n nm Copy rhs} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HEUse envA hA evs) {e0 = EUse uid args} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HECall unk envA hA evs) {e0 = ECall id calleeC args} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HECallUser pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HECallUserRet pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b Z rec ihs inh oa (HEAsgPtr w envA hA ev) {e0 = EAssign id n nm Ptr rhs} pT _ =
      void (lteSuccZero fk)
  inhTakeH_b k rec ihs inh oa HELit {e0 = ELit id} pT _ =
      let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc0 id)) pT))
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhTakeH_b k rec ihs inh oa HENull {e0 = ENull id} pT _ =
      let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc0 id)) pT))
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhTakeH_b k rec ihs inh oa (HEVarLive c lookN cl) {e0 = EVar nid n nm} pT _ =
      inhTakeVar k ihs inh pT lookN
  inhTakeH_b k rec ihs inh oa (HEVarNone lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVar k ihs inh pT lookN
  inhTakeH_b k rec ihs inh oa (HEVarCopy lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVar k ihs inh pT lookN
  inhTakeH_b k rec ihs inh oa (HEVarMiss lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVarMiss k ihs inh pT
  inhTakeH_b k rec ihs inh oa HEUnsup {e0 = EUnsupported nid reason} pT _ =
      void (takeUnsupContraH nid reason pT)
  inhTakeH_b (S k) rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT _ =
      (rec k (ltSucc k)).inhTakeMalloc {fk = fromLteSucc fk} ihs inh oa evs pT
  inhTakeH_b (S k) rec ihs inh oa (HEAsgCopy w envA hA ev) {e0 = EAssign id n nm Copy rhs} pT _ =
      (rec k (ltSucc k)).inhTakeAsgCopy {fk = fromLteSucc fk} ihs inh oa ev pT
  inhTakeH_b (S k) rec ihs inh oa (HEUse envA hA evs) {e0 = EUse uid args} pT _ =
      (rec k (ltSucc k)).inhTakeUse {fk = fromLteSucc fk} ihs inh oa evs pT
  inhTakeH_b (S k) rec ihs inh oa (HECall unk envA hA evs) {e0 = ECall id calleeC args} pT _ =
      (rec k (ltSucc k)).inhTakeCall {fk = fromLteSucc fk} ihs inh oa evs pT
  inhTakeH_b (S k) rec ihs inh oa (HECallUser pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      (rec k (ltSucc k)).inhTakeCallUser {fk = fromLteSucc fk} ihs inh oa pB f look pDef evs evBody pT
  inhTakeH_b (S k) rec ihs inh oa (HECallUserRet pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      (rec k (ltSucc k)).inhTakeCallUserRet {fk = fromLteSucc fk} ihs inh oa pB f look pDef evs evBody pT
  inhTakeH_b (S k) rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT _ =
      (rec k (ltSucc k)).inhTakeRealloc {fk = fromLteSucc fk} ihs inh oa pName evs pT
  inhTakeH_b (S k) rec ihs inh oa (HEAsgPtr w envA hA ev) {e0 = EAssign id n nm Ptr rhs} pT _ =
      (rec k (ltSucc k)).inhTakeAsgPtr {fk = fromLteSucc fk} ihs inh oa ev pT

  inhTakeVar :
      (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} -> {cv : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
      lookupH n env0 = Just cv ->
      InHand env0 h0 scY a
  inhTakeVar k ihs inh pT lookN = tv (lookupPlace n sc0) Refl
      where
        tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
             InHand env0 h0 scY a
        tv Nothing pL =
          let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
          in replace {p = \s => InHand env0 h0 s a} scEq inh
        tv (Just stN) pL =
          let mv = takeVarMove pT pL
          in inhMove {n} {nid} {nm} {b = a} inh mv

  inhTakeVarMiss :
      (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
      InHand env0 h0 scY a
  inhTakeVarMiss k ihs inh pT = tv (lookupPlace n sc0) Refl
      where
        tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
             InHand env0 h0 scY a
        tv Nothing pL =
          let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
          in replace {p = \s => InHand env0 h0 s a} scEq inh
        tv (Just stN) pL =
          let mv = takeVarMove pT pL
          in inhMove {n} {nid} {nm} {b = a} inh mv

  inhTakeMalloc_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {mid : Nat} -> {margs : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (EMalloc mid margs) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhTakeMalloc_b k rec ihs inh oa evs pT =
      case eitherEq (checkArgsBorrow ctx sc0 margs) of
        Left (d ** pA) =>
          void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
        Right (scA ** pA) =>
          let scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
              inhA = inhBorrow_b {fk = fk} k rec ihs inh oa evs pA
              nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
          in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq
               (inhAllocPres inhA nf)

  inhTakeAsgCopy_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Copy rhs) = Right (scY, fl0) ->
      {fk : LTE (evalSize ev) k} ->
      InHand envA hA scY a
  inhTakeAsgCopy_b k rec ihs inh oa ev pT =
      case eitherEq (checkExpr ctx sc0 rhs) of
        Left (d ** pE) =>
          void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
        Right (scA ** pE) =>
          let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
              inhA = inhExprH_b {fk = fk} k rec ihs inh oa ev pE
          in replace {p = \s => InHand envA hA s a} scEq inhA

  inhTakeUse_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {uid : Nat} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (EUse uid args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hA scY a
  inhTakeUse_b k rec ihs inh oa evs pT =
      case eitherEq (checkArgsBorrow ctx sc0 args) of
        Left (d ** pA) =>
          void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
        Right (scA ** pA) =>
          let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
              inhA = inhBorrow_b {fk = fk} k rec ihs inh oa evs pA
          in replace {p = \s => InHand envA hA s a} scEq inhA

  inhTakeCall_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hA scY a
  inhTakeCall_b k rec ihs inh oa evs pT =
      case eitherEq (checkCall ctx sc0 id calleeC args) of
        Left (d ** pC) =>
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        Right (scA ** pC) =>
          let inhA = inhCallArgs_b {fk = fk} k rec ihs inh oa evs pC
          in case boolEq (isRealloc calleeC && not (isDefined ctx calleeC)) of
               Left pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                       (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
                 in replace {p = \s => InHand envA hA s a} scEq inhA
               Right pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
                 in replace {p = \s => InHand envA hA s a} scEq inhA

  inhTakeCallUser_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhTakeCallUser_b k rec ihs inh oa pB f look pDef evs evBody pT =
      case eitherEq (checkCall ctx sc0 id calleeC args) of
        Left (d ** pC) =>
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        Right (scA ** pC) =>
          let inhB = inhCallUser_b {fk = fk} k rec ihs inh oa pB f look pDef evs evBody pC
          in case boolEq (isRealloc calleeC && not (isDefined ctx calleeC)) of
               Left pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                       (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
                 in replace {p = \s => InHand envA hB s a} scEq inhB
               Right pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
                 in replace {p = \s => InHand envA hB s a} scEq inhB

  inhTakeCallUserRet_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhTakeCallUserRet_b k rec ihs inh oa pB f look pDef evs evBody pT =
      case eitherEq (checkCall ctx sc0 id calleeC args) of
        Left (d ** pC) =>
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        Right (scA ** pC) =>
          let inhB = inhCallUserRet_b {fk = fk} k rec ihs inh oa pB f look pDef evs evBody pC
          in case boolEq (isRealloc calleeC && not (isDefined ctx calleeC)) of
               Left pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                       (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
                 in replace {p = \s => InHand envA hB s a} scEq inhB
               Right pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
                 in replace {p = \s => InHand envA hB s a} scEq inhB

  inhTakeRealloc_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      (evs : HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhTakeRealloc_b k rec ihs inh oa pName evs pT =
      case eitherEq (checkCall ctx sc0 id calleeC args) of
        Left (d ** pC) =>
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        Right (scA ** pC) =>
          let inhA = inhRealloc_b {fk = fk} k rec ihs inh oa pName evs pC
          in case boolEq (isRealloc calleeC && not (isDefined ctx calleeC)) of
               Left pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                       (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
                 in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA
               Right pF =>
                 let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
                 in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA

  takeAsgNull_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  takeAsgNull_b k rec ihs inh oa ev pT pR oaT HNull =
      let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pR oaT
          scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pR)) pT))
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhSetHPlaceNull inhR noneNotPtrA)

  takeAsgMove_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  takeAsgMove_b k rec ihs inh oa ev pT pR scEq oaT HOwnNone pM0 =
      let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pR oaT
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhMove {n} {nid = id} {nm} {b = a}
              (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pM0)
  takeAsgMove_b k rec ihs inh oa ev pT pR scEq oaT (HOwnLive {a = b} clB ihB) pM0 =
      case valNotPtrA {a} (HVPtr b) of
        Left veq =>
          void (inhNoTakeLeftover_b {fk = fk} k rec ihs inh oa ev pR veq)
        Right nv =>
          let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pR oaT
          in replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a} scEq
               (inhMove {n} {nid = id} {nm} {b = a}
                  (inhSetHPlaceOwnedUnsafe inhR nv) pM0)

  inhTakeAsgPtr_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  inhTakeAsgPtr_b k rec ihs inh oa ev pT =
      case eitherEq (takeOwner ctx sc0 rhs) of
        Left (d ** pR) =>
          void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT))
        Right ((scT, Ghost) ** pR) =>
          let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pR
                       (htFromOk (ihs.takeIH ev sc0 scT Ghost pR oa))
              scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pR)) pT))
          in replace {p = \s => InHand (setH n w envA) hA s a} scEq
               (inhSetHPlaceEmpty inhR)
        Right ((scT, Null) ** pR) =>
          let ht = ihs.takeIH ev sc0 scT Null pR oa
          in takeAsgNull_b {fk = fk} k rec ihs inh oa ev pT pR (htFromOk ht) (htTaken ht)
        Right ((scT, Owner) ** pR) =>
          case eitherEq
                 (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) of
            Left (d ** pM) =>
              void (leftNotRight (trans (sym (takeAsgPtrFail pR pM)) pT))
            Right (sc2 ** pM) =>
              let ht = ihs.takeIH ev sc0 scT Owner pR oa
                  scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner pR pM)) pT))
              in takeAsgMove_b {fk = fk} k rec ihs inh oa ev pT pR scEq (htFromOk ht) (htTaken ht) pM

  exprAsgNull_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  exprAsgNull_b k rec ihs inh oa ev eq pT oaT HNull =
      let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pT oaT
          scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq)
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhSetHPlaceNull inhR noneNotPtrA)

  exprAsgUse_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  exprAsgUse_b k rec ihs inh oa ev eq pT scEq oaT HOwnNone pU0 =
      let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pT oaT
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhUse {n} {nid = id} {nm} {b = a}
              (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pU0)
  exprAsgUse_b k rec ihs inh oa ev eq pT scEq oaT (HOwnLive {a = b} clB ihB) pU0 =
      case valNotPtrA {a} (HVPtr b) of
        Left veq =>
          void (inhNoTakeLeftover_b {fk = fk} k rec ihs inh oa ev pT veq)
        Right nv =>
          let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pT oaT
          in replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a} scEq
               (inhUse {n} {nid = id} {nm} {b = a}
                  (inhSetHPlaceOwnedUnsafe inhR nv) pU0)

  inhAsgPtr_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev : HEvalExpr {funs} env0 h0 rhs (HROk w envA hA)) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      {fk : LTE (evalSize ev) k} ->
      InHand (setH n w envA) hA scY a
  inhAsgPtr_b k rec ihs inh oa ev eq =
      case eitherEq (takeOwner ctx sc0 rhs) of
        Left (d ** pT) =>
          void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
        Right ((scT, Ghost) ** pT) =>
          let inhR = inhTakeH_b {fk = fk} k rec ihs inh oa ev pT
                       (htFromOk (ihs.takeIH ev sc0 scT Ghost pT oa))
              scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq)
          in replace {p = \s => InHand (setH n w envA) hA s a} scEq
               (inhSetHPlaceEmpty inhR)
        Right ((scT, Null) ** pT) =>
          let ht = ihs.takeIH ev sc0 scT Null pT oa
          in exprAsgNull_b {fk = fk} k rec ihs inh oa ev eq pT (htFromOk ht) (htTaken ht)
        Right ((scT, Owner) ** pT) =>
          case eitherEq
                 (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) of
            Left (d ** pU) =>
              void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
            Right (sc2 ** pU) =>
              let ht = ihs.takeIH ev sc0 scT Owner pT oa
                  scEq = rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq)
              in exprAsgUse_b {fk = fk} k rec ihs inh oa ev eq pT scEq (htFromOk ht) (htTaken ht) pU

  ||| `usePlace` of leftover intern of `a` fails: intern is already unsafe.
  inhUseLeftover :
      (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} ->
      {envU : HEnv} -> {hU : Heap} -> {scU0, scU : Scopes} ->
      InHand envU hU scU0 a ->
      OverApprox envU hU scU0 ->
      lookupH n envU = Just (HVPtr a) ->
      usePlace scU0 n nid nm = Right scU ->
      Void
  inhUseLeftover k ihs {n} {nid} {scU0} inh oa lookN eq =
      let (stU ** lpU) = oa.tracked n (HVPtr a) lookN
      in useGo stU lpU
      where
        useGo : (st0 : Status) -> lookupPlace n scU0 = Just st0 -> Void
        useGo st0 lpU with (stepStatus st0 Use nid) proof pS
          useGo st0 lpU | Left d =
            void (leftNotRight (trans (sym (usePlaceJustL lpU pS)) eq))
          useGo st0 lpU | Right st' =
            let uns0 = inh.holdersUnsafe n st0 lookN lpU
            in trueNotFalse (trans (sym uns0) (stepUseSafe st0 nid st' pS))

  ||| `takeOwner` of leftover intern of `a` fails: intern is already unsafe.
  inhTakeVarLeftover :
      (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} -> {flV : Flag} ->
      {envU : HEnv} -> {hU : Heap} -> {scU0, scU : Scopes} ->
      InHand envU hU scU0 a ->
      OverApprox envU hU scU0 ->
      lookupH n envU = Just (HVPtr a) ->
      takeOwner ctx scU0 (EVar nid n nm) = Right (scU, flV) ->
      Void
  inhTakeVarLeftover k ihs {n} {nid} {nm} {scU0} inh oa lookN pT =
      let (stU ** lpU) = oa.tracked n (HVPtr a) lookN
          mv = takeVarMove pT lpU
      in mvGo stU lpU mv
      where
        mvGo : (st0 : Status) ->
               lookupPlace n scU0 = Just st0 ->
               movePlace scU0 n nid nm = Right scU ->
               Void
        mvGo st0 lpU mv with (stepStatus st0 Move nid) proof pS
          mvGo st0 lpU mv | Left d =
            void (leftNotRight (trans (sym (movePlaceJustL lpU pS)) mv))
          mvGo st0 lpU mv | Right st' =
            let uns0 = inh.holdersUnsafe n st0 lookN lpU
            in trueNotFalse (trans (sym uns0) (stepMoveSafe st0 nid st' pS))

  ||| Nested `HECallUser`: leftover intern is already unsafe, so nested
  ||| args cannot name leftover `a`. The nested frame is unheld and
  ||| `framePres` keeps leftover `a` live.
  inhCallUser_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhCallUser_b k rec ihs inh oa pB f look pDef evs evBody pC =
      let inhA = inhCallArgs_b {fk = fk} k rec ihs inh oa evs pC
          vn = inhValsCall_b {fk = fk} k rec ihs inh oa evs pC
          nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
          liveB = framePres {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
      in MkInHand liveB
           (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

  inhCallUserRet_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envA hB scY a
  inhCallUserRet_b k rec ihs inh oa pB f look pDef evs evBody pC =
      let inhA = inhCallArgs_b {fk = fk} k rec ihs inh oa evs pC
          vn = inhValsCall_b {fk = fk} k rec ihs inh oa evs pC
          nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
          liveB = framePresRet {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
      in MkInHand liveB
           (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

  inhRealloc_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      (evs : HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envA (snd (alloc hA)) scY a
  inhRealloc_b k rec ihs inh oa _ evs pC =
      let inhA = inhReallocArgs_b {fk = fk} k rec ihs inh oa evs pC
          nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
      in inhAllocPres inhA nf

  inhReallocArgs_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalReallocArgs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (reallocSize evs) k} ->
      InHand envY hY scY a
  inhReallocArgs_b Z rec ihs inh oa (HRHeadOk w envA hA evE evEs) {argsC = eC :: esC} pC =
      void (lteSuccZero fk)
  inhReallocArgs_b k rec ihs inh _ HRNil pC =
      let scEq = callNilScope pC
      in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
  inhReallocArgs_b (S k) rec ihs inh oa (HRHeadOk w envA hA evE evEs) {argsC = eC :: esC} pC =
      (rec k (ltSucc k)).inhCallCons {fk = fromLteSucc fk} ihs inh oa pC evE evEs

  inhReallocTail_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
  inhReallocTail_b k rec ihs inh oa eq evE evEs =
      case eitherEq (takeOwner ctx sc0 eC) of
        Left (d ** pT) =>
          void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
        Right ((sc1, fl) ** pT) =>
          let ht = ihs.takeIH evE sc0 sc1 fl pT oa
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in inhBorrow_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) evEs
               (trans (sym (reallocTailRight esC pT)) eq)

  inhNoTakeLeftover_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {envY : HEnv} -> {hY : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      takeOwner ctx sc0 e0 = Right (scT, fl0) ->
      v0 = HVPtr a ->
      {fk : LTE (evalSize ev0) k} ->
      Void
  inhNoTakeLeftover_b Z rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT veq =
      void (lteSuccZero fk)
  inhNoTakeLeftover_b Z rec ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} pT veq =
      void (lteSuccZero fk)
  inhNoTakeLeftover_b Z rec ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} pT veq =
      void (lteSuccZero fk)
  inhNoTakeLeftover_b Z rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT veq =
      void (lteSuccZero fk)
  inhNoTakeLeftover_b k rec ihs inh oa HELit pT veq =
      void (copyNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa HENull pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HEVarLive b lookN cl) {e0 = EVar nid n nm} pT veq =
      inhTakeVarLeftover k ihs inh oa
        (replace {p = \x => lookupH n env0 = Just (HVPtr x)}
           (hvPtrInj veq) lookN)
        pT
  inhNoTakeLeftover_b k rec ihs inh oa (HEVarNone lookN) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HEVarCopy lookN) pT veq =
      void (copyNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HEVarMiss lookN) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa HEUnsup {e0 = EUnsupported nid reason} pT _ =
      void (takeUnsupContraH nid reason pT)
  inhNoTakeLeftover_b (S k) rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT veq =
      case eitherEq (checkArgsBorrow ctx sc0 margs) of
        Left (d ** pA) =>
          void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
        Right (scA ** pA) =>
          let inhA = (rec k (ltSucc k)).inhBorrow {fk = fromLteSucc fk} ihs inh oa evs pA
              nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
          in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
  inhNoTakeLeftover_b (S k) rec ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} pT veq =
      case eitherEq (checkExpr ctx sc0 rhs) of
        Left (d ** pE) =>
          void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
        Right (scA ** pE) =>
          (rec k (ltSucc k)).inhNotPtrExpr {fk = fromLteSucc fk} ihs inh oa evR pE veq
  inhNoTakeLeftover_b (S k) rec ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} pT veq =
      case eitherEq (takeOwner ctx sc0 rhs) of
        Left (d ** pR) =>
          void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT))
        Right ((scR, flR) ** pR) =>
          (rec k (ltSucc k)).inhNoTakeLeftover {fk = fromLteSucc fk} ihs inh oa evR pR veq
  inhNoTakeLeftover_b k rec ihs inh oa (HEUse envA hA evs) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HECall unk envA hA evs) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HECallUser pBu f look pDef envA hA evs envB hB evBody) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b k rec ihs inh oa (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover_b (S k) rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT veq =
      case eitherEq (checkCall ctx sc0 id calleeC args) of
        Left (d ** pC) =>
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        Right (scA ** pC) =>
          let inhA = (rec k (ltSucc k)).inhReallocArgs {fk = fromLteSucc fk} ihs inh oa evs pC
              nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
          in eqNatFalse a hA.next nf (hvPtrInj (sym veq))

  inhNotPtrExpr_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      Not (v0 = HVPtr a)
  inhNotPtrExpr_b Z rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} eq veq =
      void (lteSuccZero fk)
  inhNotPtrExpr_b Z rec ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} eq veq =
      void (lteSuccZero fk)
  inhNotPtrExpr_b Z rec ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} eq veq =
      void (lteSuccZero fk)
  inhNotPtrExpr_b Z rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} eq veq =
      void (lteSuccZero fk)
  inhNotPtrExpr_b k rec ihs inh oa HELit eq veq =
      copyNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa HENull eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HEVarLive b lookN cl) {e0 = EVar nid n nm} eq veq =
      inhUseLeftover k ihs inh oa
        (replace {p = \x => lookupH n env0 = Just (HVPtr x)} (hvPtrInj veq) lookN)
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhNotPtrExpr_b k rec ihs inh oa (HEVarNone lookN) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HEVarCopy lookN) eq veq =
      copyNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HEVarMiss lookN) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs _ _ HEUnsup {e0 = EUnsupported nid reason} eq _ =
      void (unsupExprContraH nid reason eq)
  inhNotPtrExpr_b (S k) rec ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} eq veq =
      let pA = trans (sym (checkExprMalloc ctx sc0 mid margs)) eq
          inhA = (rec k (ltSucc k)).inhBorrow {fk = fromLteSucc fk} ihs inh oa evs pA
          nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
      in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
  inhNotPtrExpr_b (S k) rec ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} eq veq =
      (rec k (ltSucc k)).inhNotPtrExpr {fk = fromLteSucc fk} ihs inh oa evR (trans (sym (checkExprAsgCopy id n nm)) eq) veq
  inhNotPtrExpr_b (S k) rec ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} eq veq =
      case eitherEq (takeOwner ctx sc0 rhs) of
        Left (d ** pT) =>
          void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
        Right ((scR, fl) ** pT) =>
          (rec k (ltSucc k)).inhNoTakeLeftover {fk = fromLteSucc fk} ihs inh oa evR pT veq
  inhNotPtrExpr_b k rec ihs inh oa (HEUse envA hA evs) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HECall unk envA hA evs) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HECallUser pBu f look pDef envA hA evs envB hB evBody) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b k rec ihs inh oa (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr_b (S k) rec ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} eq veq =
      let pC = trans (sym (checkExprCall ctx sc0 id calleeC args)) eq
          inhA = (rec k (ltSucc k)).inhReallocArgs {fk = fromLteSucc fk} ihs inh oa evs pC
          nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
      in eqNatFalse a hA.next nf (hvPtrInj (sym veq))

  inhValsCall_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
  inhValsCall_b Z rec ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      void (lteSuccZero fk)
  inhValsCall_b k rec ihs inh oa HEArgsNil eq = VNNil
  inhValsCall_b (S k) rec ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      (rec k (ltSucc k)).inhValsCons {fk = fromLteSucc fk} ihs inh oa eq evE evEs

  inhValsCons_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsCons_b k rec ihs inh oa eq evE evEs =
      case boolEq (isBuiltin calleeC) of
        Right pb =>
          let (scA ** (pE, pEs)) = argsBorrowSplit
                (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
              nv = inhNotPtrExpr_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              inhA = inhExprH_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
          in notPtrVal nv (inhValsBorrow_b {fk = ltePlusR fk} k rec ihs inhA oaA evEs pEs)
        Left pb =>
          case boolEq (isDefined ctx calleeC) of
            Left pd =>
              case boolEq (isRealloc calleeC) of
                Left pr =>
                  void (callOpaqueContraH pb pr pd eq)
                Right pr =>
                  inhValsReallocTail_b {fk = fk} k rec ihs inh oa
                    (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
            Right pd =>
              let pbad = callDefinedNoAlias eq pb pd
                  pModes = trans (sym (checkCallDefined pb pd pbad)) eq
              in inhValsModes_b {fk = fk} k rec ihs inh oa pModes evE evEs

  inhValsReallocTail_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsReallocTail_b k rec ihs inh oa eq evE evEs =
      case eitherEq (takeOwner ctx sc0 eC) of
        Left (d ** pT) =>
          void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
        Right ((sc1, fl) ** pT) =>
          let ht = ihs.takeIH evE sc0 sc1 fl pT oa
              nv = \veq => inhNoTakeLeftover_b {fk = ltePlusL fk} k rec ihs inh oa evE pT veq
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsBorrow_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) evEs
               (trans (sym (reallocTailRight esC pT)) eq))

  inhValsBorrow_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {es0 : List Expr} -> {vB : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
  inhValsBorrow_b Z rec ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      void (lteSuccZero fk)
  inhValsBorrow_b k rec ihs inh oa HEArgsNil eq = VNNil
  inhValsBorrow_b (S k) rec ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      let (scA ** (pE, pEs)) = argsBorrowSplit eq
          nv = (rec k (ltSucc k)).inhNotPtrExpr {fk = ltePlusL (fromLteSucc fk)} ihs inh oa evE pE
          inhA = (rec k (ltSucc k)).inhExprH {fk = ltePlusL (fromLteSucc fk)} ihs inh oa evE pE
          oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
      in notPtrVal nv ((rec k (ltSucc k)).inhValsBorrow {fk = ltePlusR (fromLteSucc fk)} ihs inhA oaA evEs pEs)

  inhValsModes_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsModes_b k rec ihs inh oa eq evE evEs {modes = []} =
      case argsModesExtraSplit eq of
        (_ ** (Ghost ** (pT, _))) =>
          void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
        (sc2 ** (Owner ** (pT, pEs2))) =>
          let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
              nv = \veq => inhNoTakeLeftover_b {fk = ltePlusL fk} k rec ihs inh oa evE pT veq
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs)
        (sc2 ** (Null ** (pT, pEs2))) =>
          let ht = ihs.takeIH evE sc0 sc2 Null pT oa
              nv = \veq => inhNoTakeLeftover_b {fk = ltePlusL fk} k rec ihs inh oa evE pT veq
              inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs)
  inhValsModes_b k rec ihs inh oa eq evE evEs {modes = m :: ms} =
      case boolEq (doesConsume m) of
        Left pc =>
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc eq
              nv = inhNotPtrExpr_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              inh1 = inhExprH_b {fk = ltePlusL fk} k rec ihs inh oa evE pE
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
          in notPtrVal nv (inhValsModesRest_b {fk = ltePlusR fk} k rec ihs inh1 oa1 pEs2 evEs)
        Right pc =>
          case argsModesMoveSplit pc eq of
            (_ ** (Ghost ** (pT, _))) =>
              void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
            (sc2 ** (Owner ** (pT, pEs2))) =>
              let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                  nv = \veq => inhNoTakeLeftover_b {fk = ltePlusL fk} k rec ihs inh oa evE pT veq
                  inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
              in notPtrVal nv (inhValsModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs)
            (sc2 ** (Null ** (pT, pEs2))) =>
              let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                  nv = \veq => inhNoTakeLeftover_b {fk = ltePlusL fk} k rec ihs inh oa evE pT veq
                  inh1 = inhTakeH_b {fk = ltePlusL fk} k rec ihs inh oa evE pT (htFromOk ht)
              in notPtrVal nv (inhValsModesRest_b {fk = ltePlusR fk} k rec ihs inh1 (htFromOk ht) pEs2 evEs)

  inhValsModesRest_b :
      (k : Nat) ->
      (rec : InhRec k) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
  inhValsModesRest_b Z rec ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      void (lteSuccZero fk)
  inhValsModesRest_b k rec ihs inh oa eq HEArgsNil = VNNil
  inhValsModesRest_b (S k) rec ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      (rec k (ltSucc k)).inhValsModes {fk = fromLteSucc fk} ihs inh oa eq evE evEs


inhOps : (k : Nat) -> InhOps k
inhOps = wfInd {a = Nat} {rel = LT} {P = InhOps} step
  where
    step : (k : Nat) -> ((j : Nat) -> LT j k -> InhOps j) -> InhOps k
    step k rec = MkInhOps
      (inhExprH_b k rec)
      (inhMallocGo_b k rec)
      (inhBorrow_b k rec)
      (inhCallArgs_b k rec)
      (inhCallCons_b k rec)
      (inhModes_b k rec)
      (inhModesRest_b k rec)
      (inhTakeH_b k rec)
      (inhTakeMalloc_b k rec)
      (inhTakeAsgCopy_b k rec)
      (inhTakeUse_b k rec)
      (inhTakeCall_b k rec)
      (inhTakeCallUser_b k rec)
      (inhTakeCallUserRet_b k rec)
      (inhTakeRealloc_b k rec)
      (takeAsgNull_b k rec)
      (takeAsgMove_b k rec)
      (inhTakeAsgPtr_b k rec)
      (exprAsgNull_b k rec)
      (exprAsgUse_b k rec)
      (inhAsgPtr_b k rec)
      (inhCallUser_b k rec)
      (inhCallUserRet_b k rec)
      (inhRealloc_b k rec)
      (inhReallocArgs_b k rec)
      (inhReallocTail_b k rec)
      (inhNoTakeLeftover_b k rec)
      (inhNotPtrExpr_b k rec)
      (inhValsCall_b k rec)
      (inhValsCons_b k rec)
      (inhValsReallocTail_b k rec)
      (inhValsBorrow_b k rec)
      (inhValsModes_b k rec)
      (inhValsModesRest_b k rec)

export
inhExprH : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
inhExprH k = (inhOps k).inhExprH

export
inhModes : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      InHand envY hY scY a
inhModes k = (inhOps k).inhModes

export
inhModesRest : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      InHand envY hY scY a
inhModesRest k = (inhOps k).inhModesRest

export
inhTakeH : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      takeOwner ctx sc0 e0 = Right (scY, fl0) ->
      OverApprox envY hY scY ->
      {fk : LTE (evalSize ev0) k} ->
      InHand envY hY scY a
inhTakeH k = (inhOps k).inhTakeH

export
inhNotPtrExpr : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (ev0 : HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY)) ->
      checkExpr ctx sc0 e0 = Right scY ->
      {fk : LTE (evalSize ev0) k} ->
      Not (v0 = HVPtr a)
inhNotPtrExpr k = (inhOps k).inhNotPtrExpr

export
inhValsModes : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      (evE : HEvalExpr {funs} env0 h0 eC (HROk w envA hA)) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      {fk : LTE (evalSize evE + exprsSize evEs) k} ->
      ValsNot (w :: collectArgVals evEs) a
inhValsModes k = (inhOps k).inhValsModes

export
inhValsModesRest : (k : Nat) ->
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      {fk : LTE (exprsSize evs) k} ->
      ValsNot (collectArgVals evs) a
inhValsModesRest k = (inhOps k).inhValsModesRest
