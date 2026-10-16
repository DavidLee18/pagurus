||| Computational helpers for internShiftXfer: destOwn of leftover intern
||| (leftover intern in live, leftover intern read by the rhs) puts dest
||| intern in `xferLive` via `placeAfter`. Checker unchanged.
module Pagurus.Heap.Xfer

import Pagurus.IR
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Status
import Pagurus.Heap
import Pagurus.Heap.Fits

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

orFX : (x, y : Bool) -> x || y = False -> (x = False, y = False)
orFX False False Refl = (Refl, Refl)
orFX True _ prf = void (trueNotFalseX prf)

neqNatSymX : {x, y : Nat} -> x == y = False -> y == x = False
neqNatSymX {x} {y} ne with (y == x) proof pyx
  neqNatSymX {x} {y} ne | True =
    void (eqNatFalse x y ne (sym (eqNatTrue y x pyx)))
  neqNatSymX {x} {y} ne | False = Refl

placeInTailX : {p, q : Place} -> {qs : List Place} ->
  placeIn p qs = True -> placeIn p (q :: qs) = True
placeInTailX {p} {q} pin = rewrite pin in orTrueRight (p == q)

pinForgetX : {p, d : Place} -> {live : List Place} ->
  placeIn p live = True ->
  p == d = False ->
  placeIn p (forgetPlace d live) = True
pinForgetX {live = []} pin _ = void (trueNotFalseX (sym pin))
pinForgetX {p} {d} {live = q :: qs} pin ne with (d == q) proof dq
  pinForgetX {p} {d} {live = q :: qs} pin ne | True =
    let pq = replace {p = \x => p == x = False} (eqNatTrue d q dq) ne
        pin1 = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
    in pinForgetX {p} {d} {live = qs} pin1 ne
  pinForgetX {p} {d} {live = q :: qs} pin ne | False =
    keepGo (p == q) Refl pin
    where
      keepGo : (eqb : Bool) -> p == q = eqb ->
               placeIn p (q :: qs) = True ->
               placeIn p (q :: forgetPlace d qs) = True
      keepGo True pq _ =
        replace {p = \x => placeIn x (q :: forgetPlace d qs) = True}
          (sym (eqNatTrue p q pq))
          (placeInHeadX q (forgetPlace d qs))
      keepGo False pq pin1 =
        let pinT = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin1
        in placeInTailX (pinForgetX {p} {d} {live = qs} pinT ne)

placeInPrefX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p xs = False
placeInPrefX {xs = []} _ = Refl
placeInPrefX {xs = q :: qs} prf =
  let (hd, tl) = orFX (p == q) (placeIn p (qs ++ ys)) prf
  in rewrite hd in placeInPrefX tl

placeInSuffX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p ys = False
placeInSuffX {xs = []} prf = prf
placeInSuffX {xs = q :: qs} prf =
  let (_, rest) = orFX (p == q) (placeIn p (qs ++ ys)) prf
  in placeInSuffX {xs = qs} rest

placeInJoinFalseX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p xs = False -> placeIn p ys = False ->
  placeIn p (xs ++ ys) = False
placeInJoinFalseX {xs = []} _ ny = ny
placeInJoinFalseX {p} {xs = q :: qs} {ys} nx ny =
  let (ne, nrest) = orFX (p == q) (placeIn p qs) nx
  in replace {p = \b => (b || Delay (placeIn p (qs ++ ys))) = False} (sym ne)
       (placeInJoinFalseX {xs = qs} nrest ny)

placeInJoinRX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p ys = True -> placeIn p (xs ++ ys) = True
placeInJoinRX {xs = []} pin = pin
placeInJoinRX {p} {xs = q :: qs} {ys} pin =
  placeInTailX {p} {q} {qs = qs ++ ys}
    (placeInJoinRX {p} {xs = qs} {ys} pin)

||| leftover intern miss of a mode footprint is leftover intern miss of
||| evaluation writes (`nH0` at nestGo False). Checker unchanged.
export
ninEvalWX :
  {acc : List (String, List Consume)} -> {e : Expr} -> {m : Consume} ->
  {p : Place} ->
  placeIn p (fst (argModeFoot acc e m)) = False ->
  placeIn p (fst (argFootprint acc e)) = False
ninEvalWX {m = Never} nin = nin
ninEvalWX {m = May} nin = placeInPrefX nin
ninEvalWX {m = Always} nin = placeInPrefX nin

||| leftover intern miss of a call footprint is leftover intern miss of
||| evaluation writes (nested `ECall` at nestGo False). Checker unchanged.
export
callMissEvalX :
  {acc : List (String, List Consume)} -> {p : Place} ->
  {es : List Expr} -> {ms : List Consume} ->
  placeIn p (fst (argsCallFoot acc es ms)) = False ->
  placeIn p (fst (argsEvalFoot acc es)) = False
callMissEvalX {es = []} _ = Refl
callMissEvalX {acc} {p} {es = e :: es} {ms} nin =
  let nMode = placeInPrefX {xs = fst (argModeFoot acc e (consumeHead ms))}
                {ys = fst (argsCallFoot acc es (consumeTail ms))} nin
      nRest = placeInSuffX {xs = fst (argModeFoot acc e (consumeHead ms))}
                {ys = fst (argsCallFoot acc es (consumeTail ms))} nin
  in placeInJoinFalseX (ninEvalWX {e} {m = consumeHead ms} nMode)
       (callMissEvalX {es} {ms = consumeTail ms} nRest)

mutual
  ||| dest intern is a nested pointer-assignment dest whose rhs reads leftover intern.
  public export
  shiftTo : Place -> Place -> Expr -> Bool
  shiftTo d q (EAssign _ p _ Ptr rhs) =
    ((p == d) && placeIn q (readPlaces rhs)) || shiftTo d q rhs
  shiftTo d q (EAssign _ _ _ Copy rhs) = shiftTo d q rhs
  shiftTo d q (ECall _ _ args) = shiftTos d q args
  shiftTo d q (EMalloc _ args) = shiftTos d q args
  shiftTo d q (EUse _ args) = shiftTos d q args
  shiftTo _ _ _ = False

  public export
  shiftTos : Place -> Place -> List Expr -> Bool
  shiftTos _ _ [] = False
  shiftTos d q (e :: es) = shiftTo d q e || shiftTos d q es

mutual
  ||| Every later pointer-assignment onto dest intern still reads leftover intern,
  ||| so dest intern is not forgotten after destOwn.
  public export
  keepsDest : Place -> Place -> Expr -> Bool
  keepsDest d q (EAssign _ p _ Ptr rhs) =
    if p == d then placeIn q (readPlaces rhs) && keepsDest d q rhs
              else keepsDest d q rhs
  keepsDest d q (EAssign _ _ _ Copy rhs) = keepsDest d q rhs
  keepsDest d q (ECall _ _ args) = keepsDests d q args
  keepsDest d q (EMalloc _ args) = keepsDests d q args
  keepsDest d q (EUse _ args) = keepsDests d q args
  keepsDest _ _ _ = True

  public export
  keepsDests : Place -> Place -> List Expr -> Bool
  keepsDests _ _ [] = True
  keepsDests d q (e :: es) = keepsDest d q e && keepsDests d q es

keepsDestPtrEq :
  {d, q, p : Place} -> {aid : Nat} -> {nm : String} -> {rhs : Expr} ->
  p == d = True ->
  keepsDest d q (EAssign aid p nm Ptr rhs) =
    placeIn q (readPlaces rhs) && keepsDest d q rhs
keepsDestPtrEq pd = rewrite pd in Refl

keepsDestPtrNeq :
  {d, q, p : Place} -> {aid : Nat} -> {nm : String} -> {rhs : Expr} ->
  p == d = False ->
  keepsDest d q (EAssign aid p nm Ptr rhs) = keepsDest d q rhs
keepsDestPtrNeq pd = rewrite pd in Refl

shiftToPtrNeq :
  {d, q, p : Place} -> {aid : Nat} -> {nm : String} -> {rhs : Expr} ->
  p == d = False ->
  shiftTo d q (EAssign aid p nm Ptr rhs) = shiftTo d q rhs
shiftToPtrNeq pd = rewrite pd in Refl

||| dest intern-assign onto dest intern: the destination test is True.
export
shiftToPtrEq :
  {d, q, p : Place} -> {aid : Nat} -> {nm : String} -> {rhs : Expr} ->
  p == d = True ->
  shiftTo d q (EAssign aid p nm Ptr rhs) =
    (True && placeIn q (readPlaces rhs)) || shiftTo d q rhs
shiftToPtrEq pd = rewrite pd in Refl

||| Leaves never destOwn leftover intern onto dest intern.
export
shiftToLit : {d, q : Place} -> {id : Nat} -> shiftTo d q (ELit id) = False
shiftToLit = Refl

export
shiftToNull : {d, q : Place} -> {id : Nat} -> shiftTo d q (ENull id) = False
shiftToNull = Refl

export
shiftToVar : {d, q : Place} -> {id, n : Nat} -> {nm : String} ->
  shiftTo d q (EVar id n nm) = False
shiftToVar = Refl

export
shiftToUnsup : {d, q : Place} -> {id : Nat} -> {reason : String} ->
  shiftTo d q (EUnsupported id reason) = False
shiftToUnsup = Refl

export
shiftTosNil : {d, q : Place} -> shiftTos d q [] = False
shiftTosNil = Refl

export
shiftToUseNil : {d, q : Place} -> {id : Nat} ->
  shiftTo d q (EUse id []) = False
shiftToUseNil = Refl

export
shiftToCallNil : {d, q : Place} -> {id : Nat} -> {callee : String} ->
  shiftTo d q (ECall id callee []) = False
shiftToCallNil = Refl

export
shiftToMallocNil : {d, q : Place} -> {id : Nat} ->
  shiftTo d q (EMalloc id []) = False
shiftToMallocNil = Refl

||| Leaves keep dest intern Unique Own of leftover intern (no later store).
export
keepsDestLit : {d, q : Place} -> {id : Nat} -> keepsDest d q (ELit id) = True
keepsDestLit = Refl

export
keepsDestNull : {d, q : Place} -> {id : Nat} -> keepsDest d q (ENull id) = True
keepsDestNull = Refl

export
keepsDestVar : {d, q : Place} -> {id, n : Nat} -> {nm : String} ->
  keepsDest d q (EVar id n nm) = True
keepsDestVar = Refl

export
keepsDestUnsup : {d, q : Place} -> {id : Nat} -> {reason : String} ->
  keepsDest d q (EUnsupported id reason) = True
keepsDestUnsup = Refl

export
keepsDestsNil : {d, q : Place} -> keepsDests d q [] = True
keepsDestsNil = Refl

||| EUse/ECall/EMalloc intern-shift is the argument-list intern-shift.
export
shiftToUse : {d, q : Place} -> {id : Nat} -> {args : List Expr} ->
  shiftTo d q (EUse id args) = shiftTos d q args
shiftToUse = Refl

export
shiftToCall : {d, q : Place} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
  shiftTo d q (ECall id callee args) = shiftTos d q args
shiftToCall = Refl

export
shiftToMalloc : {d, q : Place} -> {id : Nat} -> {args : List Expr} ->
  shiftTo d q (EMalloc id args) = shiftTos d q args
shiftToMalloc = Refl

export
shiftToCopy : {d, q : Place} -> {id, n : Nat} -> {nm : String} -> {rhs : Expr} ->
  shiftTo d q (EAssign id n nm Copy rhs) = shiftTo d q rhs
shiftToCopy = Refl

export
keepsDestUse : {d, q : Place} -> {id : Nat} -> {args : List Expr} ->
  keepsDest d q (EUse id args) = keepsDests d q args
keepsDestUse = Refl

export
keepsDestCall : {d, q : Place} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
  keepsDest d q (ECall id callee args) = keepsDests d q args
keepsDestCall = Refl

export
keepsDestMalloc : {d, q : Place} -> {id : Nat} -> {args : List Expr} ->
  keepsDest d q (EMalloc id args) = keepsDests d q args
keepsDestMalloc = Refl

export
keepsDestCopy : {d, q : Place} -> {id, n : Nat} -> {nm : String} -> {rhs : Expr} ->
  keepsDest d q (EAssign id n nm Copy rhs) = keepsDest d q rhs
keepsDestCopy = Refl

export
shiftTosCons : {d, q : Place} -> {e : Expr} -> {es : List Expr} ->
  shiftTos d q (e :: es) = shiftTo d q e || shiftTos d q es
shiftTosCons = Refl

export
keepsDestsCons : {d, q : Place} -> {e : Expr} -> {es : List Expr} ->
  keepsDests d q (e :: es) = keepsDest d q e && keepsDests d q es
keepsDestsCons = Refl

||| dest intern assigned from a place already in `xferLive` of the rhs
||| (chained intern: dest intern = r after r = leftover intern).
export
asgDestFromCaptured :
  {d, r : Place} -> {live : List Place} ->
  {id : Nat} -> {nm : String} -> {rhs : Expr} ->
  placeIn r (xferLive live rhs) = True ->
  placeIn r (readPlaces rhs) = True ->
  placeIn d (xferLive live (EAssign id d nm Ptr rhs)) = True
asgDestFromCaptured {id} {nm} inX inR = asgDestInXfer {id} {nm} inX inR

mutual
  ||| leftover intern in `live` and not in evaluation writes stays in `xferLive`.
  export
  xferKeepsX :
    {acc : List (String, List Consume)} ->
    {p : Place} -> {live : List Place} -> {e : Expr} ->
    placeIn p live = True ->
    placeIn p (fst (argFootprint acc e)) = False ->
    placeIn p (xferLive live e) = True
  xferKeepsX {e = EVar _ _ _} pin _ = pin
  xferKeepsX {e = ELit _} pin _ = pin
  xferKeepsX {e = ENull _} pin _ = pin
  xferKeepsX {e = EUnsupported _ _} pin _ = pin
  xferKeepsX {acc} {e = EAssign _ _ _ Copy rhs} pin nin =
    xferKeepsX {acc} {e = rhs} pin nin
  xferKeepsX {acc} {p} {live} {e = EAssign id d nm Ptr rhs} pin nin =
    let (ne, ninR) = orFX (p == d) (placeIn p (fst (argFootprint acc rhs))) nin
        rec = xferKeepsX {acc} {e = rhs} pin ninR
    in asgGo (placesOverlap (readPlaces rhs) (xferLive live rhs)) Refl rec ne
    where
      asgGo : (b : Bool) ->
              placesOverlap (readPlaces rhs) (xferLive live rhs) = b ->
              placeIn p (xferLive live rhs) = True ->
              p == d = False ->
              placeIn p (placeAfter d (xferLive live rhs) b) = True
      asgGo True _ rec _ =
        placeInTailX {p} {q = d} {qs = xferLive live rhs} rec
      asgGo False _ rec ne = pinForgetX {p} {d} rec ne
  xferKeepsX {acc} {e = ECall _ callee args} pin nin =
    xferArgsKeepsX {acc} pin (callMissEvalX {ms = calleeModes acc callee} nin)
  xferKeepsX {acc} {e = EMalloc _ args} pin nin = xferArgsKeepsX {acc} pin nin
  xferKeepsX {acc} {e = EUse _ args} pin nin = xferArgsKeepsX {acc} pin nin

  export
  xferArgsKeepsX :
    {acc : List (String, List Consume)} ->
    {p : Place} -> {live : List Place} -> {es : List Expr} ->
    placeIn p live = True ->
    placeIn p (fst (argsEvalFoot acc es)) = False ->
    placeIn p (xferArgs live es) = True
  xferArgsKeepsX {es = []} pin _ = pin
  xferArgsKeepsX {acc} {p} {live} {es = e :: es} pin nin =
    let nH = placeInPrefX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
        nT = placeInSuffX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
    in xferArgsKeepsX {acc} {live = xferLive live e} {es}
         (xferKeepsX {acc} {e} pin nH) nT

mutual
  ||| dest intern already in `live` stays in `xferLive` when leftover intern
  ||| stays captured and dest intern-assigns still read leftover intern.
  export
  xferKeepDest :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {live : List Place} -> {e : Expr} ->
    placeIn d live = True ->
    placeIn q live = True ->
    placeIn q (fst (argFootprint acc e)) = False ->
    keepsDest d q e = True ->
    placeIn d (xferLive live e) = True
  xferKeepDest {e = EVar _ _ _} pinD _ _ _ = pinD
  xferKeepDest {e = ELit _} pinD _ _ _ = pinD
  xferKeepDest {e = ENull _} pinD _ _ _ = pinD
  xferKeepDest {e = EUnsupported _ _} pinD _ _ _ = pinD
  xferKeepDest {acc} {e = EAssign _ _ _ Copy rhs} pinD pinQ nin kd =
    xferKeepDest {acc} {e = rhs} pinD pinQ nin kd
  xferKeepDest {acc} {d} {q} {live} {e = EAssign aid p nm Ptr rhs} pinD pinQ nin kd =
    let (neQ, ninR) = orFX (q == p) (placeIn q (fst (argFootprint acc rhs))) nin
        recQ = xferKeepsX {acc} {e = rhs} pinQ ninR
    in pdGo ninR (p == d) Refl kd recQ
    where
      afterGo : (b : Bool) ->
                placesOverlap (readPlaces rhs) (xferLive live rhs) = b ->
                placeIn d (xferLive live rhs) = True ->
                d == p = False ->
                placeIn d (placeAfter p (xferLive live rhs) b) = True
      afterGo True _ pinR _ =
        placeInTailX {p = d} {q = p} {qs = xferLive live rhs} pinR
      afterGo False _ pinR ned = pinForgetX {p = d} {d = p} pinR ned
      pdGo : (ninR : placeIn q (fst (argFootprint acc rhs)) = False) ->
             (eqb : Bool) -> p == d = eqb ->
             keepsDest d q (EAssign aid p nm Ptr rhs) = True ->
             placeIn q (xferLive live rhs) = True ->
             placeIn d (placeAfter p (xferLive live rhs)
                          (placesOverlap (readPlaces rhs) (xferLive live rhs))) = True
      pdGo _ True pd kd0 recQ =
        let kd1 = replace {p = \k => k = True} (keepsDestPtrEq {aid} {nm} {rhs} pd) kd0
            (inR, _) = andTrue kd1
            asg = asgDestInXfer {d} {q} {live} {id = aid} {nm} {rhs} recQ inR
        in replace {p = \x => placeIn d (xferLive live (EAssign aid x nm Ptr rhs)) = True}
             (sym (eqNatTrue p d pd)) asg
      pdGo ninR False pd kd0 recQ =
        let kd1 = replace {p = \k => k = True} (keepsDestPtrNeq {aid} {nm} {rhs} pd) kd0
            recD = xferKeepDest {acc} {e = rhs} pinD pinQ ninR kd1
        in afterGo (placesOverlap (readPlaces rhs) (xferLive live rhs)) Refl recD
             (neqNatSymX pd)
  xferKeepDest {acc} {e = ECall _ callee args} pinD pinQ nin kd =
    xferKeepDests {acc} pinD pinQ
      (callMissEvalX {ms = calleeModes acc callee} nin) kd
  xferKeepDest {acc} {e = EMalloc _ args} pinD pinQ nin kd =
    xferKeepDests {acc} pinD pinQ nin kd
  xferKeepDest {acc} {e = EUse _ args} pinD pinQ nin kd =
    xferKeepDests {acc} pinD pinQ nin kd

  export
  xferKeepDests :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {live : List Place} -> {es : List Expr} ->
    placeIn d live = True ->
    placeIn q live = True ->
    placeIn q (fst (argsEvalFoot acc es)) = False ->
    keepsDests d q es = True ->
    placeIn d (xferArgs live es) = True
  xferKeepDests {es = []} pinD _ _ _ = pinD
  xferKeepDests {acc} {live} {es = e :: es} pinD pinQ nin kd =
    let nH = placeInPrefX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
        nT = placeInSuffX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
        (kdH, kdT) = andTrue kd
        pinD1 = xferKeepDest {acc} {e} pinD pinQ nH kdH
        pinQ1 = xferKeepsX {acc} {e} pinQ nH
    in xferKeepDests {acc} {live = xferLive live e} {es} pinD1 pinQ1 nT kdT

  ||| dest intern of leftover intern is in `xferLive` after destOwn of leftover intern
  ||| (leftover intern in live, leftover intern not written, dest intern-assign reads leftover intern,
  ||| dest intern not forgotten).
  export
  internShiftXferLive :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {live : List Place} -> {e : Expr} ->
    placeIn q live = True ->
    placeIn q (fst (argFootprint acc e)) = False ->
    shiftTo d q e = True ->
    keepsDest d q e = True ->
    placeIn d (xferLive live e) = True
  internShiftXferLive {e = EVar _ _ _} _ _ hit _ = void (trueNotFalseX (sym hit))
  internShiftXferLive {e = ELit _} _ _ hit _ = void (trueNotFalseX (sym hit))
  internShiftXferLive {e = ENull _} _ _ hit _ = void (trueNotFalseX (sym hit))
  internShiftXferLive {e = EUnsupported _ _} _ _ hit _ = void (trueNotFalseX (sym hit))
  internShiftXferLive {acc} {e = EAssign _ _ _ Copy rhs} pin nin hit kd =
    internShiftXferLive {acc} {e = rhs} pin nin hit kd
  internShiftXferLive {acc} {d} {q} {live} {e = EAssign aid p nm Ptr rhs} pin nin hit kd =
    let (neQ, ninR) = orFX (q == p) (placeIn q (fst (argFootprint acc rhs))) nin
        recQ = xferKeepsX {acc} {e = rhs} pin ninR
    in hitGo ninR (p == d) Refl hit kd recQ
    where
      afterGo : (b : Bool) ->
                placesOverlap (readPlaces rhs) (xferLive live rhs) = b ->
                placeIn d (xferLive live rhs) = True ->
                d == p = False ->
                placeIn d (placeAfter p (xferLive live rhs) b) = True
      afterGo True _ pinR _ =
        placeInTailX {p = d} {q = p} {qs = xferLive live rhs} pinR
      afterGo False _ pinR ned = pinForgetX {p = d} {d = p} pinR ned
      hitGo : (ninR : placeIn q (fst (argFootprint acc rhs)) = False) ->
              (eqb : Bool) -> p == d = eqb ->
              shiftTo d q (EAssign aid p nm Ptr rhs) = True ->
              keepsDest d q (EAssign aid p nm Ptr rhs) = True ->
              placeIn q (xferLive live rhs) = True ->
              placeIn d (placeAfter p (xferLive live rhs)
                           (placesOverlap (readPlaces rhs) (xferLive live rhs))) = True
      hitGo _ True pd hit0 kd0 recQ =
        let kd1 = replace {p = \k => k = True} (keepsDestPtrEq {aid} {nm} {rhs} pd) kd0
            (inR, _) = andTrue kd1
            asg = asgDestInXfer {d} {q} {live} {id = aid} {nm} {rhs} recQ inR
        in replace {p = \x => placeIn d (xferLive live (EAssign aid x nm Ptr rhs)) = True}
             (sym (eqNatTrue p d pd)) asg
      hitGo ninR False pd hit0 kd0 recQ =
        let hit1 = replace {p = \k => k = True} (shiftToPtrNeq {aid} {nm} {rhs} pd) hit0
            kd1 = replace {p = \k => k = True} (keepsDestPtrNeq {aid} {nm} {rhs} pd) kd0
            recD = internShiftXferLive {acc} {e = rhs} pin ninR hit1 kd1
        in afterGo (placesOverlap (readPlaces rhs) (xferLive live rhs)) Refl recD
             (neqNatSymX pd)
  internShiftXferLive {acc} {e = ECall _ callee args} pin nin hit kd =
    internShiftXferArgs {acc} pin (callMissEvalX {ms = calleeModes acc callee} nin) hit kd
  internShiftXferLive {acc} {e = EMalloc _ args} pin nin hit kd =
    internShiftXferArgs {acc} pin nin hit kd
  internShiftXferLive {acc} {e = EUse _ args} pin nin hit kd =
    internShiftXferArgs {acc} pin nin hit kd

  ||| dest intern of leftover intern in `xferArgs` of a general argument list.
  export
  internShiftXferArgs :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {live : List Place} -> {es : List Expr} ->
    placeIn q live = True ->
    placeIn q (fst (argsEvalFoot acc es)) = False ->
    shiftTos d q es = True ->
    keepsDests d q es = True ->
    placeIn d (xferArgs live es) = True
  internShiftXferArgs {es = []} _ _ hit _ = void (trueNotFalseX (sym hit))
  internShiftXferArgs {acc} {d} {q} {live} {es = e :: es} pin nin hit kd =
    let nH = placeInPrefX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
        nT = placeInSuffX {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nin
        (kdH, kdT) = andTrue kd
    in orGo nH nT kdH kdT (shiftTo d q e) (shiftTos d q es) Refl Refl hit
    where
      orGo : (nH : placeIn q (fst (argFootprint acc e)) = False) ->
             (nT : placeIn q (fst (argsEvalFoot acc es)) = False) ->
             (kdH : keepsDest d q e = True) ->
             (kdT : keepsDests d q es = True) ->
             (h : Bool) -> (t : Bool) ->
             shiftTo d q e = h ->
             shiftTos d q es = t ->
             (h || Delay t) = True ->
             placeIn d (xferArgs (xferLive live e) es) = True
      orGo nH nT kdH kdT True _ ph _ _ =
        let pinD = internShiftXferLive {acc} {e} pin nH ph kdH
            pinQ = xferKeepsX {acc} {e} pin nH
        in xferKeepDests {acc} {live = xferLive live e} {es} pinD pinQ nT kdT
      orGo nH nT _ kdT False True _ pt _ =
        let pinQ = xferKeepsX {acc} {e} pin nH
        in internShiftXferArgs {acc} {live = xferLive live e} {es} pinQ nT pt kdT
      orGo _ _ _ _ False False _ _ hit0 = void (trueNotFalseX (sym hit0))

||| dest intern of leftover intern is in `valuePlaces ++ xferLive`
||| (ownerFrameGo nestGo False goal). Checker unchanged.
export
internShiftXfer :
  {acc : List (String, List Consume)} ->
  {d, q : Place} -> {live : List Place} -> {e : Expr} ->
  placeIn q live = True ->
  placeIn q (fst (argFootprint acc e)) = False ->
  shiftTo d q e = True ->
  keepsDest d q e = True ->
  placeIn d (valuePlaces e ++ xferLive live e) = True
internShiftXfer {acc} {d} {e} pin nin hit kd =
  placeInJoinRX {p = d} {xs = valuePlaces e} {ys = xferLive live e}
    (internShiftXferLive {acc} {e} pin nin hit kd)

||| `nH0` form: leftover intern miss of `argModeFoot` (borrow/consume)
||| is leftover intern miss of evaluation writes.
export
internShiftXferMode :
  {acc : List (String, List Consume)} ->
  {d, q : Place} -> {live : List Place} -> {e : Expr} -> {m : Consume} ->
  placeIn q live = True ->
  placeIn q (fst (argModeFoot acc e m)) = False ->
  shiftTo d q e = True ->
  keepsDest d q e = True ->
  placeIn d (valuePlaces e ++ xferLive live e) = True
internShiftXferMode {acc} {e} {m} pin nin hit kd =
  internShiftXfer {acc} {e} pin (ninEvalWX {acc} {e} {m} nin) hit kd

||| Dest intern Unique Own of leftover `a` after destOwn: the cell is live
||| (`oaLive`: `ownSafe` vs `deadUnsafe`) and dest intern is in `xferLive`
||| / `valuePlaces ++ xferLive` (`internShiftXferLive`). Live is at this
||| heap; a later tail is `ownerCellGo` of this dest intern.
export
destOwnsLive :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {acc : List (String, List Consume)} ->
  {d, q : Place} -> {live : List Place} -> {e : Expr} ->
  {st : Status} ->
  OverApprox env h sc ->
  lookupH d env = Just (HVPtr a) ->
  lookupPlace d sc = Just st ->
  unsafeUse st = False ->
  placeIn q live = True ->
  placeIn q (fst (argFootprint acc e)) = False ->
  shiftTo d q e = True ->
  keepsDest d q e = True ->
  (placeIn d (valuePlaces e ++ xferLive live e) = True,
   placeIn d (xferLive live e) = True,
   cell h a = Just Live)
destOwnsLive {acc} {d} {q} {live} {e} oa look lp safe pin nin hit kd =
  let pinL = internShiftXferLive {acc} {d} {q} {live} {e} pin nin hit kd
  in (internShiftXfer {acc} {d} {q} {live} {e} pin nin hit kd,
      pinL,
      oaLive oa d st a lp look safe)

||| `nH0` form of `destOwnsLive`: leftover intern miss of `argModeFoot`.
export
destOwnsLiveMode :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {acc : List (String, List Consume)} ->
  {d, q : Place} -> {live : List Place} -> {e : Expr} -> {m : Consume} ->
  {st : Status} ->
  OverApprox env h sc ->
  lookupH d env = Just (HVPtr a) ->
  lookupPlace d sc = Just st ->
  unsafeUse st = False ->
  placeIn q live = True ->
  placeIn q (fst (argModeFoot acc e m)) = False ->
  shiftTo d q e = True ->
  keepsDest d q e = True ->
  (placeIn d (valuePlaces e ++ xferLive live e) = True,
   placeIn d (xferLive live e) = True,
   cell h a = Just Live)
destOwnsLiveMode {acc} {e} {m} oa look lp safe pin nin hit kd =
  destOwnsLive oa look lp safe pin (ninEvalWX {acc} {e} {m} nin) hit kd

orTrueX : (x, y : Bool) -> x || y = True -> Either (x = True) (y = True)
orTrueX True _ Refl = Left Refl
orTrueX False True Refl = Right Refl

placeInJoinLX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p xs = True -> placeIn p (xs ++ ys) = True
placeInJoinLX {xs = []} pin = void (trueNotFalseX (sym pin))
placeInJoinLX {p} {xs = q :: qs} {ys} pin = appGo (p == q) Refl pin
  where
    appGo : (b : Bool) -> p == q = b -> placeIn p (q :: qs) = True ->
            placeIn p ((q :: qs) ++ ys) = True
    appGo True pq _ =
      replace {p = \n => placeIn n (q :: qs ++ ys) = True}
        (sym (eqNatTrue p q pq))
        (rewrite eqNatRefl q in Refl)
    appGo False pq pin0 =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0
      in replace {p = \b => (b || Delay (placeIn p (qs ++ ys))) = True} (sym pq)
           (placeInJoinLX {xs = qs} {ys} pinq)

placeInSuffTrueX : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = True ->
  placeIn p xs = False ->
  placeIn p ys = True
placeInSuffTrueX {xs = []} pin _ = pin
placeInSuffTrueX {p} {xs = q :: qs} {ys} pin nxs =
  let (ne, nrest) = orFX (p == q) (placeIn p qs) nxs
      pin1 = replace {p = \b => (b || Delay (placeIn p (qs ++ ys))) = True} ne pin
  in placeInSuffTrueX {xs = qs} {ys} pin1 nrest

||| Evaluation writes sit inside consume-mode writes.
export
evalInModeX :
  {acc : List (String, List Consume)} -> {e : Expr} -> {m : Consume} ->
  {p : Place} ->
  placeIn p (fst (argFootprint acc e)) = True ->
  placeIn p (fst (argModeFoot acc e m)) = True
evalInModeX {m = Never} pin = pin
evalInModeX {m = May} pin = placeInJoinLX pin
evalInModeX {m = Always} pin = placeInJoinLX pin

||| Evaluation writes of the argument list sit inside the call writes.
evalInCallX :
  {acc : List (String, List Consume)} -> {p : Place} ->
  {es : List Expr} -> {ms : List Consume} ->
  placeIn p (fst (argsEvalFoot acc es)) = True ->
  placeIn p (fst (argsCallFoot acc es ms)) = True
evalInCallX {es = []} pin = void (trueNotFalseX (sym pin))
evalInCallX {acc} {p} {es = e :: es} {ms} pin =
  orGo (placeIn p (fst (argFootprint acc e))) Refl pin
  where
    orGo : (b : Bool) ->
           placeIn p (fst (argFootprint acc e)) = b ->
           placeIn p (fst (argFootprint acc e) ++
                        fst (argsEvalFoot acc es)) = True ->
           placeIn p (fst (argModeFoot acc e (consumeHead ms)) ++
                        fst (argsCallFoot acc es (consumeTail ms))) = True
    orGo True pinE _ =
      placeInJoinLX (evalInModeX {e} {m = consumeHead ms} pinE)
    orGo False nE pin0 =
      placeInJoinRX (evalInCallX {es} {ms = consumeTail ms}
        (placeInSuffTrueX {xs = fst (argFootprint acc e)}
           {ys = fst (argsEvalFoot acc es)} pin0 nE))

mutual
  ||| Intern-shift dest is in evaluation writes (Ptr dest, or nested).
  export
  shiftToWrites :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {e : Expr} ->
    shiftTo d q e = True ->
    placeIn d (fst (argFootprint acc e)) = True
  shiftToWrites {e = ELit _} hit = void (trueNotFalseX (sym hit))
  shiftToWrites {e = ENull _} hit = void (trueNotFalseX (sym hit))
  shiftToWrites {e = EVar _ _ _} hit = void (trueNotFalseX (sym hit))
  shiftToWrites {e = EUnsupported _ _} hit = void (trueNotFalseX (sym hit))
  shiftToWrites {acc} {d} {q} {e = EAssign id n nm Copy rhs} hit =
    shiftToWrites {acc} {d} {q} {e = rhs} hit
  shiftToWrites {acc} {d} {q} {e = EAssign id p nm Ptr rhs} hit =
    pdGo (p == d) Refl hit
    where
      pdGo : (eqb : Bool) -> p == d = eqb ->
             shiftTo d q (EAssign id p nm Ptr rhs) = True ->
             placeIn d (p :: fst (argFootprint acc rhs)) = True
      pdGo True pd _ =
        replace {p = \x => placeIn d (x :: fst (argFootprint acc rhs)) = True}
          (sym (eqNatTrue p d pd))
          (placeInHeadX d (fst (argFootprint acc rhs)))
      pdGo False pd hit0 =
        placeInTailX (shiftToWrites {acc} {d} {q} {e = rhs}
          (replace {p = \b => b = True} (shiftToPtrNeq {d} {q} {p} {aid = id} {nm} {rhs} pd) hit0))
  shiftToWrites {acc} {d} {q} {e = ECall _ callee args} hit =
    evalInCallX {acc} {p = d} {es = args} {ms = calleeModes acc callee}
      (shiftTosWrites {acc} {d} {q} {es = args} hit)
  shiftToWrites {acc} {d} {q} {e = EMalloc _ args} hit =
    shiftTosWrites {acc} {d} {q} {es = args} hit
  shiftToWrites {acc} {d} {q} {e = EUse _ args} hit =
    shiftTosWrites {acc} {d} {q} {es = args} hit

  export
  shiftTosWrites :
    {acc : List (String, List Consume)} ->
    {d, q : Place} -> {es : List Expr} ->
    shiftTos d q es = True ->
    placeIn d (fst (argsEvalFoot acc es)) = True
  shiftTosWrites {es = []} hit = void (trueNotFalseX (sym hit))
  shiftTosWrites {acc} {d} {q} {es = e :: es} hit =
    case orTrueX (shiftTo d q e) (shiftTos d q es) hit of
      Left hitE =>
        placeInJoinLX (shiftToWrites {acc} {d} {q} {e} hitE)
      Right hitEs =>
        placeInJoinRX (shiftTosWrites {acc} {d} {q} {es} hitEs)

||| Leftover intern Unique Own of `a` at START, dest intern a different intern
||| that already holds `HVPtr a` use-safe Unique Own at START: `uniqueLive`
||| forces dest intern unsafe, contradicting dest intern `ownSafe`. Closes
||| `shiftTo`/`keepsDest` False once EnvFrame / useKeepLookupInv recover dest
||| intern Own of `a` at START (e did not intern-shift leftover intern onto
||| dest intern). Checker unchanged. Does not edit `uniqueLive`.
export
noShiftContra :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {d, q : Place} -> {stQ, stD : Status} ->
  OverApprox env h sc ->
  q == d = False ->
  lookupH q env = Just (HVPtr a) ->
  lookupPlace q sc = Just stQ ->
  unsafeUse stQ = False ->
  hasOwned stQ = True ->
  hasBorrowed stQ = Nothing ->
  lookupH d env = Just (HVPtr a) ->
  lookupPlace d sc = Just stD ->
  unsafeUse stD = False ->
  Void
noShiftContra oa ne lookQ lpQ safeQ ownQ nbQ lookD lpD safeD =
  trueNotFalseX (trans (sym
    (oa.uniqueLive q d a ne lookQ lookD (oaLive oa q stQ a lpQ lookQ safeQ)
       stQ lpQ stD lpD safeQ ownQ nbQ))
    safeD)

pairEqX : (x : (a, b)) -> (fst x, snd x) = x
pairEqX (u, v) = Refl

||| Dest intern in eval writes of extra Always head `e`, and in tail
||| Always writes, contradicts M1 `callOverlap` of `e :: es` at `[]`.
||| Honest recX `dw True` route (b): both `liveStay` call sites have dest
||| intern in eval `W` of `e` (`dMiss True`, `shiftToWrites` of `sh True
||| False`). (a) write-status Live/Gone is for dest intern not in head `W`
||| (not this case). (c) `goneWrittenWrite` would restate a case M1 forbids
||| here. Checker unchanged.
export
extraAlwaysTailHitContra :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} ->
  placeIn p (fst (argFootprint acc e)) = True ->
  placeIn p (footsWrites (callFoots acc es [])) = True ->
  callOverlap acc (e :: es) [] = False ->
  Void
extraAlwaysTailHitContra {acc} {e} {es} {p} pinE pinT ov =
  let pinW = evalInModeX {acc} {e} {m = Always} {p} pinE
      pinRW = placeInJoinRX {p}
                {xs = snd (argModeFoot acc e Always)}
                {ys = fst (argModeFoot acc e Always)} pinW
      ninT = laterWriteQuiet {w = fst (argModeFoot acc e Always)}
               {r = snd (argModeFoot acc e Always)}
               {fs = callFoots acc es []} {p} pinRW
               (replace {p = \wr =>
                  footHits wr (callFoots acc es []) = False}
                  (sym (pairEqX (argModeFoot acc e Always)))
                  (callOverlapHits {acc} {e} {es} {ms = []} ov))
  in trueNotFalseX (trans (sym pinT) ninT)

export
extraAlwaysTailHitContraCanary :
  callOverlap []
    [EAssign 0 1 "n" Ptr (EVar 2 2 "x"), EVar 3 1 "n"] [] = False ->
  Void
extraAlwaysTailHitContraCanary ov =
  extraAlwaysTailHitContra {acc = []} {p = 1}
    {e = EAssign 0 1 "n" Ptr (EVar 2 2 "x")}
    {es = [EVar 3 1 "n"]} Refl Refl ov

export
shiftToWritesCanary :
  placeIn 1
    (fst (argFootprint [] (EAssign 0 1 "n" Ptr (EVar 2 2 "x")))) = True
shiftToWritesCanary =
  shiftToWrites {acc = []} {d = 1} {q = 2}
    {e = EAssign 0 1 "n" Ptr (EVar 2 2 "x")} Refl

export
internShiftXferModeCanary :
  placeIn 1
    (valuePlaces (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])
     ++ xferLive [2] (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])) = True
internShiftXferModeCanary =
  internShiftXferMode {acc = []} {d = 1} {q = 2} {live = [2]}
    {e = EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")]} {m = Never}
    Refl Refl Refl Refl

export
internShiftXferCanary :
  placeIn 1
    (valuePlaces (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])
     ++ xferLive [2] (EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")])) = True
internShiftXferCanary =
  internShiftXfer {acc = []} {d = 1} {q = 2} {live = [2]}
    {e = EUse 2 [EAssign 3 1 "n" Ptr (EVar 4 2 "x")]} Refl Refl Refl Refl

||| leftover intern dest intern-assign is a later argument, not the head.
export
internShiftXferArgsCanary :
  placeIn 1
    (xferLive [2]
      (EUse 5 [ELit 0, EAssign 3 1 "n" Ptr (EVar 4 2 "x")])) = True
internShiftXferArgsCanary =
  internShiftXferLive {acc = []} {d = 1} {q = 2} {live = [2]}
    {e = EUse 5 [ELit 0, EAssign 3 1 "n" Ptr (EVar 4 2 "x")]} Refl Refl Refl Refl

||| Leaves: Unique Own dest intern leftover intern AFTER cannot come from destOwn.
export
shiftToLeafCanary :
  (shiftTo 1 2 (ELit 0) = False,
   shiftTo 1 2 (ENull 0) = False,
   shiftTo 1 2 (EVar 0 3 "x") = False,
   shiftTo 1 2 (EUse 0 []) = False,
   keepsDest 1 2 (ELit 0) = True,
   keepsDests 1 2 [] = True)
shiftToLeafCanary = (Refl, Refl, Refl, Refl, Refl, Refl)

||| dest intern = r after r = leftover intern is dest intern in `xferLive`
||| even though `shiftTo` dest intern leftover intern is False (chained intern).
export
internShiftXferChainCanary :
  placeIn 1
    (xferLive [2]
      (EUse 0
         [ EAssign 3 3 "r" Ptr (EVar 4 2 "x")
         , EAssign 5 1 "n" Ptr (EVar 6 3 "r") ])) = True
internShiftXferChainCanary =
  asgDestFromCaptured {d = 1} {r = 3} {live = [3, 2]}
    {id = 5} {nm = "n"} {rhs = EVar 6 3 "r"} Refl Refl

||| Copy assignment is transparent to `valuePlaces` / `xferLive` /
||| footprints, so Unique Own AFTER Copy is Unique Own AFTER the rhs.
export
valuePlacesCopyEq : {id, n : Nat} -> {nm : String} -> {rhs : Expr} ->
  valuePlaces (EAssign id n nm Copy rhs) = valuePlaces rhs
valuePlacesCopyEq = Refl

export
xferLiveCopyEq : {live : List Place} -> {id, n : Nat} -> {nm : String} ->
  {rhs : Expr} ->
  xferLive live (EAssign id n nm Copy rhs) = xferLive live rhs
xferLiveCopyEq = Refl

export
argFootprintCopyEq : {acc : List (String, List Consume)} ->
  {id, n : Nat} -> {nm : String} -> {rhs : Expr} ->
  argFootprint acc (EAssign id n nm Copy rhs) = argFootprint acc rhs
argFootprintCopyEq = Refl

export
argModeFootCopyEq : {acc : List (String, List Consume)} ->
  {id, n : Nat} -> {nm : String} -> {rhs : Expr} -> {m : Consume} ->
  argModeFoot acc (EAssign id n nm Copy rhs) m = argModeFoot acc rhs m
argModeFootCopyEq {m = Never} = Refl
argModeFootCopyEq {m = May} = Refl
argModeFootCopyEq {m = Always} = Refl

export
xferArgsNilEq : {live : List Place} -> xferArgs live [] = live
xferArgsNilEq = Refl

export
copyUnfoldCanary :
  (valuePlaces (EAssign 0 1 "n" Copy (EVar 2 3 "x")) = [3],
   xferLive [2] (EAssign 0 1 "n" Copy (EVar 3 4 "y")) = [2],
   argFootprint [] (EAssign 0 1 "n" Copy (EVar 2 3 "x")) = ([], [3]),
   argModeFoot [] (EAssign 0 1 "n" Copy (EVar 2 3 "x")) Never =
     argModeFoot [] (EVar 2 3 "x") Never,
   xferArgs [2] [] = [2])
copyUnfoldCanary = (Refl, Refl, Refl, Refl, Refl)

||| dest intern stays in `xferLive` of a pointer assignment whose dest is
||| a different intern (`placeAfter` only forgets that dest).
export
xferLivePtrNeq :
  {d, p : Place} -> {live : List Place} ->
  {id : Nat} -> {nm : String} -> {rhs : Expr} ->
  p == d = False ->
  placeIn d (xferLive live rhs) = True ->
  placeIn d (xferLive live (EAssign id p nm Ptr rhs)) = True
xferLivePtrNeq {d} {p} {live} {rhs} pd pin =
  afterGo (placesOverlap (readPlaces rhs) (xferLive live rhs)) Refl
  where
    afterGo : (b : Bool) ->
              placesOverlap (readPlaces rhs) (xferLive live rhs) = b ->
              placeIn d (placeAfter p (xferLive live rhs) b) = True
    afterGo True _ =
      placeInTailX {p = d} {q = p} {qs = xferLive live rhs} pin
    afterGo False _ =
      pinForgetX {p = d} {d = p} pin (neqNatSymX pd)

export
ninFootprintPtrRhs :
  {acc : List (String, List Consume)} ->
  {id : Nat} -> {p, q : Place} -> {nm : String} -> {rhs : Expr} ->
  placeIn q (fst (argFootprint acc (EAssign id p nm Ptr rhs))) = False ->
  placeIn q (fst (argFootprint acc rhs)) = False
ninFootprintPtrRhs nin =
  snd (orFX (q == p) (placeIn q (fst (argFootprint acc rhs))) nin)

export
xferLivePtrNeqCanary :
  placeIn 1
    (xferLive [2]
      (EAssign 0 3 "r" Ptr (EAssign 1 1 "n" Ptr (EVar 2 2 "x")))) = True
xferLivePtrNeqCanary =
  xferLivePtrNeq {d = 1} {p = 3} {live = [2]} {id = 0} {nm = "r"}
    {rhs = EAssign 1 1 "n" Ptr (EVar 2 2 "x")} Refl Refl

export
callMissEvalXCanary :
  placeIn 1 (fst (argsEvalFoot [] [])) = False
callMissEvalXCanary = callMissEvalX {acc = []} {p = 1} {es = []} {ms = []} Refl
