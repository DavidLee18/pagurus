||| Lookup, update, and join lemmas for interned (`Nat`) places.
module Pagurus.Store

import Pagurus.IR
import Pagurus.Status
import Pagurus.Lattice
import Pagurus.Checker

%default total

export
justInj : Just x = Just y -> x = y
justInj Refl = Refl

export
justNotNothing : {0 x : a} -> Not (Just x = Nothing)
justNotNothing Refl impossible

export
nothingNotJust : {0 x : a} -> Not (Nothing = Just x)
nothingNotJust Refl impossible

--------------------------------------------------------------------------------
-- Env lookup / set / delete
--------------------------------------------------------------------------------

export
lookupSetHit : (n : Place) -> (v : Status) -> (e : Env) ->
               lookupName n (setName n v e) = Just v
lookupSetHit n v [] = rewrite eqNatRefl n in Refl
lookupSetHit n v ((k, x) :: xs) with (n == k) proof p
  lookupSetHit n v ((k, x) :: xs) | True =
    rewrite eqNatRefl n in Refl
  lookupSetHit n v ((k, x) :: xs) | False =
    rewrite p in lookupSetHit n v xs

export
lookupSetMiss : (n, m : Place) -> (v : Status) -> (e : Env) ->
                n == m = False ->
                lookupName n (setName m v e) = lookupName n e
lookupSetMiss n m v [] neqm = rewrite neqm in Refl
lookupSetMiss n m v ((k, x) :: xs) neqm with (m == k) proof pm
  lookupSetMiss n m v ((k, x) :: xs) neqm | True with (eqNatTrue m k pm)
    lookupSetMiss n m v ((m, x) :: xs) neqm | True | Refl = rewrite neqm in Refl
  lookupSetMiss n m v ((k, x) :: xs) neqm | False with (n == k) proof pn
    lookupSetMiss n m v ((k, x) :: xs) neqm | False | True = Refl
    lookupSetMiss n m v ((k, x) :: xs) neqm | False | False =
      lookupSetMiss n m v xs neqm

export
deleteGone : (n : Place) -> (e : Env) -> lookupName n (deleteName n e) = Nothing
deleteGone n [] = Refl
deleteGone n ((k, v) :: xs) with (k == n) proof p
  deleteGone n ((k, v) :: xs) | True = deleteGone n xs
  deleteGone n ((k, v) :: xs) | False =
    rewrite trans (eqNatSym n k) p in deleteGone n xs

export
deletePres : (n, m : Place) -> (e : Env) ->
             n == m = False ->
             lookupName n (deleteName m e) = lookupName n e
deletePres n m [] _ = Refl
deletePres n m ((k, v) :: xs) neqm with (k == m) proof p
  deletePres n m ((k, v) :: xs) neqm | True =
    rewrite eqNatTrue k m p in rewrite neqm in deletePres n m xs neqm
  deletePres n m ((k, v) :: xs) neqm | False with (n == k) proof pn
    deletePres n m ((k, v) :: xs) neqm | False | True = Refl
    deletePres n m ((k, v) :: xs) neqm | False | False =
      deletePres n m xs neqm

export
lookupPlaceSetHit : (n : Place) -> (v : Status) -> (sc : Scopes) ->
                    lookupPlace n (setPlace n v sc) = Just v
lookupPlaceSetHit = lookupSetHit

export
lookupPlaceSetMiss : (n, m : Place) -> (v : Status) -> (sc : Scopes) ->
                     n == m = False ->
                     lookupPlace n (setPlace m v sc) = lookupPlace n sc
lookupPlaceSetMiss = lookupSetMiss

export
setNameSetName : (n : Place) -> (v, v' : Status) -> (e : Env) ->
                 setName n v' (setName n v e) = setName n v' e
setNameSetName n v v' [] = rewrite eqNatRefl n in Refl
setNameSetName n v v' ((k, x) :: xs) with (n == k) proof p
  setNameSetName n v v' ((k, x) :: xs) | True = rewrite eqNatRefl n in Refl
  setNameSetName n v v' ((k, x) :: xs) | False =
    rewrite p in cong (\ys => (k, x) :: ys) (setNameSetName n v v' xs)

export
setPlaceSetPlace : (n : Place) -> (v, v' : Status) -> (sc : Scopes) ->
                   setPlace n v' (setPlace n v sc) = setPlace n v' sc
setPlaceSetPlace = setNameSetName

export
declareLookupHit : (n : Place) -> (v : Status) -> (sc : Scopes) ->
                   lookupPlace n (declarePlace n v sc) = Just v
declareLookupHit = lookupSetHit

--------------------------------------------------------------------------------
-- Join over-approximates each operand
--------------------------------------------------------------------------------

export
joinEnvLookupLeft :
  (xs, ys : Env) -> (n : Place) -> (s : Status) ->
  lookupName n xs = Just s ->
  (st : Status ** (lookupName n (joinEnv xs ys) = Just st, SubStatus s st))
joinEnvLookupLeft [] ys n s prf = void (nothingNotJust prf)
joinEnvLookupLeft ((k, v) :: xs) ys n s prf with (n == k) proof pn
  joinEnvLookupLeft ((k, v) :: xs) ys n s prf | True with (lookupName k ys)
    joinEnvLookupLeft ((k, v) :: xs) ys n s prf | True | Nothing =
      let sEq = justInj prf
      in rewrite pn in
           (v ** (Refl, replace {p = \x => SubStatus s x} (sym sEq) (subStatusRefl s)))
    joinEnvLookupLeft ((k, v) :: xs) ys n s prf | True | Just s2 =
      let sEq = justInj prf
      in rewrite pn in
           (join v s2 ** (Refl, replace {p = \x => SubStatus x (join v s2)} sEq (joinContainsLeft v s2)))
  joinEnvLookupLeft ((k, v) :: xs) ys n s prf | False with (lookupName k ys)
    joinEnvLookupLeft ((k, v) :: xs) ys n s prf | False | Nothing =
      rewrite pn in joinEnvLookupLeft xs ys n s prf
    joinEnvLookupLeft ((k, v) :: xs) ys n s prf | False | Just s2 =
      rewrite pn in
        joinEnvLookupLeft xs (deleteName k ys) n s prf

export
joinEnvLookupRight :
  (xs, ys : Env) -> (n : Place) -> (s : Status) ->
  lookupName n ys = Just s ->
  (st : Status ** (lookupName n (joinEnv xs ys) = Just st, SubStatus s st))
joinEnvLookupRight [] ys n s prf = (s ** (prf, subStatusRefl s))
joinEnvLookupRight ((k, v) :: xs) ys n s prf with (n == k) proof pn
  joinEnvLookupRight ((k, v) :: xs) ys n s prf | True with (lookupName k ys) proof pk
    joinEnvLookupRight ((k, v) :: xs) ys n s prf | True | Nothing =
      let nk = eqNatTrue n k pn
          prfK = replace {p = \x => lookupName x ys = Just s} nk prf
      in void (nothingNotJust (trans (sym pk) prfK))
    joinEnvLookupRight ((k, v) :: xs) ys n s prf | True | Just s2 =
      let nk = eqNatTrue n k pn
          prfK = replace {p = \x => lookupName x ys = Just s} nk prf
          sEq = justInj (trans (sym pk) prfK)
          sub = replace {p = \x => SubStatus x (join v s2)} sEq
                       (joinContainsRight v s2)
      in rewrite pn in (join v s2 ** (Refl, sub))
  joinEnvLookupRight ((k, v) :: xs) ys n s prf | False with (lookupName k ys)
    joinEnvLookupRight ((k, v) :: xs) ys n s prf | False | Nothing =
      rewrite pn in joinEnvLookupRight xs ys n s prf
    joinEnvLookupRight ((k, v) :: xs) ys n s prf | False | Just s2 =
      rewrite pn in
        let prf' = trans (deletePres n k ys pn) prf
        in joinEnvLookupRight xs (deleteName k ys) n s prf'

export
joinScopesLookupLeft :
  (xs, ys : Scopes) -> (n : Place) -> (s : Status) ->
  lookupPlace n xs = Just s ->
  (st : Status ** (lookupPlace n (joinScopes xs ys) = Just st, SubStatus s st))
joinScopesLookupLeft = joinEnvLookupLeft

export
joinScopesLookupRight :
  (xs, ys : Scopes) -> (n : Place) -> (s : Status) ->
  lookupPlace n ys = Just s ->
  (st : Status ** (lookupPlace n (joinScopes xs ys) = Just st, SubStatus s st))
joinScopesLookupRight = joinEnvLookupRight
