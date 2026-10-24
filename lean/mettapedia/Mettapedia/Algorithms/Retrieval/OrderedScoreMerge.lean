import Mettapedia.Algebra.SupportTensor

/-!
# Ordered support-aware score merging

Premise-ranking signals are partial coordinate maps.  Their packed
realization merges overlap, background, nearest-neighbour, and Bayes signals
in the same left-to-right order as the ordinary contribution fold.  These
results require no associativity or commutativity, so they also state the
schedule required by binary floating-point execution.

This is an algorithmic observation law.  It does not verify a native tensor
kernel or an IEEE implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.OrderedScoreMerge

open Mettapedia.Algebra.SupportTensor

universe u
variable {I R : Type u}

def mergeOption (combine : R → R → R) : Option R → Option R → Option R
  | none, right => right
  | left, none => left
  | some left, some right => some (combine left right)

def merge (combine : R → R → R) (left right : Value I R) : Value I R :=
  fun coordinate => mergeOption combine (left coordinate) (right coordinate)

def mergeSignals (combine : R → R → R) (signals : List (Value I R)) : Value I R :=
  signals.foldl (merge combine) (fun _ => none)

def foldPresent (combine : R → R → R) (values : List (Option R)) : Option R :=
  values.foldl (mergeOption combine) none

private theorem fold_merge_apply (combine : R → R → R)
    (signals : List (Value I R)) (accumulator : Value I R) (coordinate : I) :
    (signals.foldl (merge combine) accumulator) coordinate =
      (signals.map (· coordinate)).foldl
        (mergeOption combine) (accumulator coordinate) := by
  induction signals generalizing accumulator with
  | nil => rfl
  | cons signal rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih (merge combine accumulator signal)

/-- Packed coordinate merging observes exactly the ordinary left fold over
the present signal values.  No reassociation law is assumed. -/
theorem mergeSignals_apply (combine : R → R → R)
    (signals : List (Value I R)) (coordinate : I) :
    mergeSignals combine signals coordinate =
      foldPresent combine (signals.map (· coordinate)) := by
  simpa [mergeSignals, foldPresent] using
    fold_merge_apply combine signals (fun _ => none) coordinate

theorem mergeOption_eq_none_iff (combine : R → R → R)
    (left right : Option R) :
    mergeOption combine left right = none ↔ left = none ∧ right = none := by
  cases left <;> cases right <;> simp [mergeOption]

/-- Merging preserves the union of supports, including explicit zero values. -/
theorem merge_eq_none_iff (combine : R → R → R)
    (left right : Value I R) (coordinate : I) :
    merge combine left right coordinate = none ↔
      left coordinate = none ∧ right coordinate = none := by
  exact mergeOption_eq_none_iff combine (left coordinate) (right coordinate)

/-- The four ranking signals are combined in their declared order. -/
theorem four_signal_schedule (combine : R → R → R)
    (overlap background nearest bayes : Value I R) (coordinate : I) :
    mergeSignals combine [overlap, background, nearest, bayes] coordinate =
      mergeOption combine
        (mergeOption combine
          (mergeOption combine (overlap coordinate) (background coordinate))
          (nearest coordinate))
        (bayes coordinate) := rfl

def appendDigit (left right : Nat) : Nat := left * 10 + right

example :
    foldPresent appendDigit [some 1, some 2, some 3] = some 123 := by decide

/-- Reordering signals can change the observation; the theorem above does not
silently commute or reassociate them. -/
example :
    foldPresent appendDigit [some 1, some 2, some 3] ≠
      foldPresent appendDigit [some 1, some 3, some 2] := by decide

/-- Absence differs from an explicit zero coordinate. -/
example : mergeOption Nat.add none (some 0) ≠ none := by decide

#print axioms mergeSignals_apply
#print axioms merge_eq_none_iff
#print axioms four_signal_schedule

end Mettapedia.Algorithms.Retrieval.OrderedScoreMerge
