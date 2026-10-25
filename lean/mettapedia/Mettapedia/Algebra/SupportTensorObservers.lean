import Mettapedia.Algebra.SupportTensor
import Mettapedia.GSLT.Dynamics.PartialRegionPlan

/-!
# Ordered packed tensor observers

A private row loop publishes only after every partial projection succeeds.
Its accumulator implementation agrees with the ordinary monadic map, keeps
coordinates and occurrences, and commutes with support-aware lookup.
The gather loop keeps output positions even when source values are absent.
These are algorithm/representation laws, not native-C or IEEE verification.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensorObservers

open SupportTensor

universe u
variable {I R S : Type u}

def projectRows (f : R → Option S) (rows : List (I × R)) : Option (List (I × S)) :=
  rows.mapM fun row => (f row.2).map (row.1, ·)

theorem projectRows_cons (f : R → Option S) (coordinate : I) (value : R)
    (rest : List (I × R)) :
    projectRows f ((coordinate,value) :: rest) = (do
      let result ← f value
      let tail ← projectRows f rest
      pure ((coordinate,result) :: tail)) := by
  cases h : f value <;> simp [projectRows, List.mapM_cons, h]

def projectLoop (f : R → Option S) : List (I × R) → List (I × S) → Option (List (I × S))
  | [], reversed => some reversed.reverse
  | (coordinate, value) :: rest, reversed => do
      let result ← f value
      projectLoop f rest ((coordinate, result) :: reversed)

theorem projectLoop_eq (f : R → Option S) (rows : List (I × R))
    (reversed : List (I × S)) :
    projectLoop f rows reversed =
      (projectRows f rows).map (reversed.reverse ++ ·) := by
  induction rows generalizing reversed with
  | nil => simp [projectLoop, projectRows]
  | cons row rest ih =>
      rcases row with ⟨coordinate,value⟩
      cases h : f value <;> cases tail : projectRows f rest <;>
        simp [projectLoop, projectRows_cons, h, ih, tail,
          List.reverse_cons, List.append_assoc]

theorem projectLoop_empty (f : R → Option S) (rows : List (I × R)) :
    projectLoop f rows [] = projectRows f rows := by
  simpa using projectLoop_eq f rows []

open Mettapedia.GSLT.Dynamics.PartialRegionPlan in
theorem project_bounded_fallback (f : R → Option S) (capacity : Nat) :
    realize
      (boundedAttempt List.length capacity (fun rows : List (I × R) => projectLoop f rows []))
      (projectRows f) = projectRows f := by
  apply realize_boundedAttempt_exact
  funext rows
  exact projectLoop_empty f rows

theorem project_coordinates (f : R → Option S) (rows : List (I × R))
    (result : List (I × S)) (succeeds : projectRows f rows = some result) :
    result.map Prod.fst = rows.map Prod.fst := by
  induction rows generalizing result with
  | nil => simp [projectRows] at succeeds; subst result; rfl
  | cons row rest ih =>
      rcases row with ⟨coordinate,value⟩
      cases hf : f value <;> cases hr : projectRows f rest <;>
        simp [projectRows_cons, hf, hr] at succeeds
      subst result
      simpa using congrArg (coordinate :: ·) (ih _ hr)

theorem project_lookup [DecidableEq I] (f : R → Option S)
    (rows : List (I × R)) (result : List (I × S))
    (succeeds : projectRows f rows = some result) (wanted : I) :
    lookupFirst result wanted = (lookupFirst rows wanted).bind f := by
  induction rows generalizing result with
  | nil => simp [projectRows] at succeeds; subst result; rfl
  | cons row rest ih =>
      rcases row with ⟨coordinate,value⟩
      cases hf : f value <;> cases hr : projectRows f rest <;>
        simp [projectRows_cons, hf, hr] at succeeds
      subst result
      by_cases same : coordinate = wanted
      · simp [lookupFirst, same, hf]
      · simp [lookupFirst, same, ih _ hr]

theorem project_total (f : R → S) (rows : List (I × R)) :
    projectRows (some ∘ f) rows = some (rows.map fun row => (row.1,f row.2)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨coordinate,value⟩
      simp [projectRows_cons, ih]

theorem project_total_value [DecidableEq I] (f : R → S) (rows : List (I × R)) :
    lookupFirst (rows.map fun row => (row.1,f row.2)) = SupportTensor.map f (lookupFirst rows) := by
  funext coordinate
  have h := project_lookup (some ∘ f) rows _ (project_total f rows) coordinate
  cases value : lookupFirst rows coordinate <;>
    simpa [SupportTensor.map, value] using h

def gatherFrom (source : Value I R) : Nat → List I → List (Nat × R)
  | _, [] => []
  | start, index :: rest =>
      match source index with
      | none => gatherFrom source (start+1) rest
      | some value => (start,value) :: gatherFrom source (start+1) rest

theorem gather_below (source : Value I R) (indices : List I) (start wanted : Nat)
    (below : wanted < start) : lookupFirst (gatherFrom source start indices) wanted = none := by
  induction indices generalizing start with
  | nil => rfl
  | cons index rest ih =>
      cases h : source index <;>
        simp [gatherFrom, h, lookupFirst, Nat.ne_of_gt below, ih (start+1) (by omega)]

theorem gather_lookup (source : Value I R) (indices : List I) (start offset : Nat) :
    lookupFirst (gatherFrom source start indices) (start+offset) =
      indices[offset]?.bind source := by
  induction indices generalizing start offset with
  | nil => simp [gatherFrom, lookupFirst]
  | cons index rest ih =>
      cases offset with
      | zero =>
          cases h : source index <;>
            simp [gatherFrom, h, lookupFirst,
              gather_below source rest (start+1) start (by omega)]
      | succ offset =>
          have different : start ≠ start + (offset+1) := by omega
          cases h : source index <;>
            simpa [gatherFrom, h, lookupFirst, different, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using ih (start+1) offset

example : lookupFirst (gatherFrom (fun i : Nat => if i = 3 then some 0 else none) 0 [1,3,3]) 0 = none := by decide
example : lookupFirst (gatherFrom (fun i : Nat => if i = 3 then some 0 else none) 0 [1,3,3]) 2 = some 0 := by decide

#print axioms projectLoop_empty
#print axioms project_bounded_fallback
#print axioms project_lookup
#print axioms project_total_value
#print axioms gather_lookup

end Mettapedia.Algebra.SupportTensorObservers
