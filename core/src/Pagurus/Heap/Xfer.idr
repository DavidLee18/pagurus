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
