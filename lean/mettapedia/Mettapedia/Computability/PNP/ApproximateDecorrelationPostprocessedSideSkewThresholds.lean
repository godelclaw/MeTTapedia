import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCoinEquiv

/-!
# PNP approximate decorrelation: postprocessed-side layer

This module contains the finite skew-threshold calculations and counterexamples.
-/

namespace Mettapedia.Computability.PNP

/-- In the concrete skew three-coin instance, the observed value `true`
appears twice on the true side. -/
theorem postprocessedSidePointwiseCollisionSkew_true_count_true :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) = 2 := by
  decide

/-- In the concrete skew three-coin instance, the observed value `true`
appears once on the false side. -/
theorem postprocessedSidePointwiseCollisionSkew_false_count_true :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) = 1 := by
  decide

/-- The concrete skew three-coin instance has an observed-fiber multiplicity
mismatch at the value `true`.  This is the exact local obstruction that blocks
below-threshold approximate independence despite pointwise support overlap. -/
theorem postprocessedSidePointwiseCollisionSkew_true_count_ne :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) ≠
      finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) := by
  rw [postprocessedSidePointwiseCollisionSkew_true_count_true,
    postprocessedSidePointwiseCollisionSkew_false_count_true]
  decide

/-- The concrete skew three-coin audit instance fails approximate output
independence below the natural source/coin threshold `3`, even though it has
two-sided pointwise collisions.  This blocks the repair route that replaces
exact multiplicity matching by mere support overlap. -/
theorem postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
    {τ : Nat} (htol : τ < 3) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  have htrue : 1 ≤ finiteEventCount Bool (fun ω => True ∧ ω = true) := by
    decide
  have hfalse : 1 ≤ finiteEventCount Bool (fun ω => True ∧ ¬ (ω = true)) := by
    decide
  have hlt : τ < 1 * 1 * Fintype.card (Fin 3) := by
    simpa using htol
  have hne :
      finiteEventCount (Fin 3)
          (fun c => (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) = true) ≠
        finiteEventCount (Fin 3)
          (fun c => (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding false c, ()) = true) := by
    simpa using postprocessedSidePointwiseCollisionSkew_true_count_ne
  have hblock :=
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
      (Ω := Bool) (Coin := Fin 3) (α := Bool) (Side := Unit) (β := Bool)
      (C := fun _ω => True) (E := fun ω => ω = true)
      postprocessedSidePointwiseCollisionSkewRecoding (fun _c => ())
      (fun x : Bool × Unit => x.1)
      true htrue hfalse hlt hne
  simpa using hblock

/-- In the concrete skew three-coin audit instance, the output fiber `true`
has forward defect exactly `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 3 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `true`
has zero backward defect. -/
theorem postprocessedSidePointwiseCollisionSkew_true_backward_gap_eq_zero :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 0 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `false`
has zero forward defect. -/
theorem postprocessedSidePointwiseCollisionSkew_false_forward_gap_eq_zero :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 0 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `false`
has backward defect exactly `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 3 := by
  decide

/-- The concrete skew three-coin audit instance satisfies approximate output
independence exactly once the tolerance reaches `3`.  This shows the local
lower bound from the multiplicity mismatch is sharp, not merely one-sided. -/
theorem postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le
    {τ : Nat} (hτ : 3 ≤ τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  intro y
  cases y with
  | false =>
      constructor
      · rw [postprocessedSidePointwiseCollisionSkew_false_forward_gap_eq_zero]
        exact Nat.zero_le τ
      · rw [postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three]
        exact hτ
  | true =>
      constructor
      · rw [postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three]
        exact hτ
      · rw [postprocessedSidePointwiseCollisionSkew_true_backward_gap_eq_zero]
        exact Nat.zero_le τ

/-- The skew three-coin postprocessed-side witness has sharp approximate output
threshold `3`: it fails below `3`, and it succeeds from `3` onward. -/
theorem postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_iff_three_le
    {τ : Nat} :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ ↔
      3 ≤ τ := by
  constructor
  · intro h
    by_contra hlt
    exact
      postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
        (Nat.lt_of_not_ge hlt) h
  · intro hτ
    exact
      postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le hτ

/-- Concrete counterexample package for the postprocessed-side repair route:
the skew three-coin instance has pointwise support collisions and even a
one-sided preserving witness map, but still fails approximate independence for
every tolerance below `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_collision_and_oneSidedMap_counterexample_of_lt_three
    {τ : Nat} (htol : τ < 3) :
    ((∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse)) ∧
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true c =
            postprocessedSidePointwiseCollisionSkewRecoding false (f c)) ∧
      ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
        (fun _xr => True)
        (fun xr => xr.1 = true)
        (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  refine ⟨postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions, ?_, ?_⟩
  · exact
      ⟨postprocessedSidePointwiseCollisionSkewTrueToFalseMap,
        postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving⟩
  · exact
      postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
        htol

end Mettapedia.Computability.PNP
