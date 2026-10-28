import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledTolerance

namespace Mettapedia.Computability.PNP

/-- The distinguishing true-side fiber of an arbitrary-codomain deterministic
recoding has the same forward product defect as a copied conditioned bit. -/
theorem countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true = y) (hf : r false ≠ y) :
    countIndependentWithinForwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  refine countIndependentWithinForwardGap_coupled C E
    (fun ω => r (decide (E ω)) = y) ?_
  intro ω _hC
  by_cases hE : E ω
  · simp [hE, ht]
  · simp [hE, hf]

/-- The distinguishing false-side fiber of an arbitrary-codomain deterministic
recoding has the same backward product defect as a complemented conditioned
bit. -/
theorem countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true ≠ y) (hf : r false = y) :
    countIndependentWithinBackwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  refine countIndependentWithinBackwardGap_anticoupled C E
    (fun ω => r (decide (E ω)) = y) ?_
  intro ω _hC
  by_cases hE : E ω
  · have hnotF : ¬ r (decide (E ω)) = y := by simpa [hE] using ht
    exact iff_of_true hE hnotF
  · have hF : r (decide (E ω)) = y := by simpa [hE] using hf
    exact iff_of_false hE (not_not.mpr hF)

/-- A true-side distinguishing fiber cannot satisfy a tolerance smaller than
the explicit source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true = y) (hf : r false ≠ y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  have hgap :
      countIndependentWithinForwardGap (Ω := Ω) C E
          (fun ω => r (decide (E ω)) = y) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
      C E r y ht hf
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.1)

/-- A false-side distinguishing fiber cannot satisfy a tolerance smaller than
the explicit source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true ≠ y) (hf : r false = y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  have hgap :
      countIndependentWithinBackwardGap (Ω := Ω) C E
          (fun ω => r (decide (E ω)) = y) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
      C E r y ht hf
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.2)

/-- Any deterministic output fiber that distinguishes the two source-bit values
inherits the same product lower bound on symmetric approximate independence. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  by_cases ht : r true = y
  · by_cases hf : r false = y
    · exact False.elim (hdistinguish (iff_of_true ht hf))
    · exact
        not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
          C E r y τ ht hf htol
  · by_cases hf : r false = y
    · exact
        not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
          C E r y τ ht hf htol
    · exact False.elim (hdistinguish (iff_of_false ht hf))

/-- Obligation form for deterministic recoding fibers: approximate
independence of any informative fiber forces the tolerance to dominate the
source-fiber product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y τ hdistinguish
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Deterministic distinguishing-fiber obligation with explicit lower bounds:
if both source-bit fibers have lower bounds, every approximate-independence
tolerance certificate for the informative output fiber must dominate the
product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ hdistinguish happrox)

/-- Deterministic distinguishing-fiber contradiction with explicit lower
bounds: substantial mass on both source-bit sides rules out any smaller
symmetric tolerance for an informative output fiber. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_lowerBounds_mul_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ loTrue loFalse hdistinguish htrue hfalse happrox)


end Mettapedia.Computability.PNP
