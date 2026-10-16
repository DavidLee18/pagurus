||| Computational helpers for internShiftXfer: destOwn of leftover intern
||| (leftover intern in live, leftover intern read by the rhs) puts dest
||| intern in `xferLive` via `placeAfter`. Checker unchanged.
module Pagurus.Heap.Xfer

import Pagurus.IR
import Pagurus.Lattice
import Pagurus.Checker

%default total

trueNotFalseX : Not (True = False)
trueNotFalseX Refl impossible

overlapHereX :
  {p : Place} -> {zs : List Place} ->
  placeIn p zs = True ->
  placesOverlap [p] zs = True
overlapHereX pin = rewrite pin in Refl

||| leftover intern in `readPlaces` and in `ys` overlaps.
export
overlapRead :
  {q : Place} -> {e : Expr} -> {ys : List Place} ->
  placeIn q (readPlaces e) = True ->
  placeIn q ys = True ->
  placesOverlap (readPlaces e) ys = True
overlapRead {e = EVar _ p _} inR inY = hit (q == p) Refl inR
  where
    hit : (eqb : Bool) -> q == p = eqb ->
          placeIn q [p] = True ->
          placesOverlap [p] ys = True
    hit True pq _ =
      overlapHereX {p = p} {zs = ys}
        (replace {p = \x => placeIn x ys = True} (eqNatTrue q p pq) inY)
    hit False pq pin0 =
      void (trueNotFalseX (trans (sym pin0) (rewrite pq in Refl)))
overlapRead {e = EAssign _ _ _ _ rhs} inR inY = overlapRead {e = rhs} inR inY
overlapRead {e = ELit _} inR _ = void (trueNotFalseX (sym inR))
overlapRead {e = ENull _} inR _ = void (trueNotFalseX (sym inR))
overlapRead {e = ECall _ _ _} inR _ = void (trueNotFalseX (sym inR))
overlapRead {e = EMalloc _ _} inR _ = void (trueNotFalseX (sym inR))
overlapRead {e = EUse _ _} inR _ = void (trueNotFalseX (sym inR))
overlapRead {e = EUnsupported _ _} inR _ = void (trueNotFalseX (sym inR))

export
overlapReadVar :
  placesOverlap (readPlaces (EVar 0 2 "x")) [2] = True
overlapReadVar = overlapRead {q = 2} {e = EVar 0 2 "x"} {ys = [2]} Refl Refl

export
overlapReadNested :
  placesOverlap (readPlaces (EAssign 1 1 "n" Ptr (EVar 3 4 "x"))) [4] = True
overlapReadNested =
  overlapRead {q = 4} {e = EAssign 1 1 "n" Ptr (EVar 3 4 "x")} {ys = [4]}
    Refl Refl

placeInHeadX : (d : Place) -> (qs : List Place) -> placeIn d (d :: qs) = True
placeInHeadX d qs = rewrite eqNatRefl d in Refl

placeAfterTrue : (d : Place) -> (xs : List Place) ->
  placeAfter d xs True = d :: xs
placeAfterTrue _ _ = Refl

||| dest intern of leftover intern (leftover intern in `xferLive` of the
||| rhs and in `readPlaces`) is in `xferLive` of the pointer assignment
||| via `placeAfter` True.
export
asgDestInXfer :
  {d, q : Place} -> {live : List Place} ->
  {id : Nat} -> {nm : String} -> {rhs : Expr} ->
  placeIn q (xferLive live rhs) = True ->
  placeIn q (readPlaces rhs) = True ->
  placeIn d (xferLive live (EAssign id d nm Ptr rhs)) = True
asgDestInXfer {d} {q} {live} {rhs} inX inR =
  let ov = overlapRead {q} {e = rhs} {ys = xferLive live rhs} inR inX
  in ovGo (placesOverlap (readPlaces rhs) (xferLive live rhs)) Refl ov
  where
    ovGo : (b : Bool) ->
           placesOverlap (readPlaces rhs) (xferLive live rhs) = b ->
           placesOverlap (readPlaces rhs) (xferLive live rhs) = True ->
           placeIn d (placeAfter d (xferLive live rhs) b) = True
    ovGo True _ _ =
      replace {p = \xs => placeIn d xs = True}
        (sym (placeAfterTrue d (xferLive live rhs)))
        (placeInHeadX d (xferLive live rhs))
    ovGo False peq ovT = void (trueNotFalseX (trans (sym ovT) peq))

export
asgDestInXferVar :
  placeIn 1 (xferLive [2] (EAssign 0 1 "n" Ptr (EVar 3 2 "x"))) = True
asgDestInXferVar =
  asgDestInXfer {d = 1} {q = 2} {live = [2]} {id = 0} {nm = "n"}
    {rhs = EVar 3 2 "x"} Refl Refl

||| `nestAssigns` of EUse/ECall/EMalloc is empty, so internShiftXfer's
||| nestGo False is the dest-intern path (dest intern is not a
||| nestAssigns destination). Checker unchanged.
export
nestNoneUse :
  {p : Place} -> {id : Nat} -> {args : List Expr} ->
  placeIn p (nestAssigns (EUse id args)) = False
nestNoneUse = Refl

export
nestNoneCall :
  {p : Place} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
  placeIn p (nestAssigns (ECall id callee args)) = False
nestNoneCall = Refl

export
nestNoneMalloc :
  {p : Place} -> {id : Nat} -> {args : List Expr} ->
  placeIn p (nestAssigns (EMalloc id args)) = False
nestNoneMalloc = Refl

||| leftover intern in `live` is leftover intern in `xferLive` of that
||| leftover intern's variable (`xferLive` is identity on EVar).
export
xferKeepVar :
  {q : Place} -> {live : List Place} ->
  {id : Nat} -> {nm : String} ->
  placeIn q live = True ->
  placeIn q (xferLive live (EVar id q nm)) = True
xferKeepVar pin = pin

||| dest intern of leftover intern: leftover intern in `live`, rhs is
||| that leftover intern's variable. dest intern is in `xferLive` of the
||| pointer assignment via `placeAfter` True.
export
asgDestFromLive :
  {d, q : Place} -> {live : List Place} ->
  {id, nid : Nat} -> {nm, vnm : String} ->
  placeIn q live = True ->
  placeIn d (xferLive live (EAssign id d nm Ptr (EVar nid q vnm))) = True
asgDestFromLive {d} {q} {live} {id} {nid} {nm} {vnm} pin =
  asgDestInXfer {d} {q} {live} {id} {nm} {rhs = EVar nid q vnm}
    pin (placeInHeadX q [])

||| dest intern of leftover intern in a singleton EUse argument
||| (`n = use(n = x)` inner). `valuePlaces` of EUse is empty, so the
||| internShiftXfer goal `valuePlaces ++ xferLive` is `xferArgs`.
export
internShiftXferUseAsg :
  {d, q : Place} -> {live : List Place} ->
  {uid, id, nid : Nat} -> {nm, vnm : String} ->
  placeIn q live = True ->
  placeIn d
    (valuePlaces (EUse uid [EAssign id d nm Ptr (EVar nid q vnm)])
     ++ xferLive live (EUse uid [EAssign id d nm Ptr (EVar nid q vnm)])) = True
internShiftXferUseAsg {id} {nid} {nm} {vnm} pin =
  asgDestFromLive {id} {nid} {nm} {vnm} pin

export
internShiftXferCallAsg :
  {d, q : Place} -> {live : List Place} ->
  {cid, id, nid : Nat} -> {callee, nm, vnm : String} ->
  placeIn q live = True ->
  placeIn d
    (valuePlaces (ECall cid callee [EAssign id d nm Ptr (EVar nid q vnm)])
     ++ xferLive live
          (ECall cid callee [EAssign id d nm Ptr (EVar nid q vnm)])) = True
internShiftXferCallAsg {id} {nid} {nm} {vnm} pin =
  asgDestFromLive {id} {nid} {nm} {vnm} pin

export
internShiftXferMallocAsg :
  {d, q : Place} -> {live : List Place} ->
  {mid, id, nid : Nat} -> {nm, vnm : String} ->
  placeIn q live = True ->
  placeIn d
    (valuePlaces (EMalloc mid [EAssign id d nm Ptr (EVar nid q vnm)])
     ++ xferLive live
          (EMalloc mid [EAssign id d nm Ptr (EVar nid q vnm)])) = True
internShiftXferMallocAsg {id} {nid} {nm} {vnm} pin =
  asgDestFromLive {id} {nid} {nm} {vnm} pin

||| dest intern survives a non-overwriting ELit tail in `xferArgs`.
export
internShiftXferUseAsgLit :
  {d, q : Place} -> {live : List Place} ->
  {uid, id, nid, lid : Nat} -> {nm, vnm : String} ->
  placeIn q live = True ->
  placeIn d
    (xferLive live
      (EUse uid [EAssign id d nm Ptr (EVar nid q vnm), ELit lid])) = True
internShiftXferUseAsgLit {id} {nid} {nm} {vnm} pin =
  asgDestFromLive {id} {nid} {nm} {vnm} pin

||| Checker `n = use(n = x)`: leftover intern 2 in live, dest intern 1
||| in `xferLive` of the EUse (internShiftXferArgs).
export
internShiftXferUseAsgCanary :
  placeIn 1
    (valuePlaces (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])
     ++ xferLive [2] (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])) = True
internShiftXferUseAsgCanary =
  internShiftXferUseAsg {d = 1} {q = 2} {live = [2]}
    {uid = 2} {id = 3} {nid = 4} {nm = "n"} {vnm = "x"} Refl
