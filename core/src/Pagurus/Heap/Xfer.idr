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
