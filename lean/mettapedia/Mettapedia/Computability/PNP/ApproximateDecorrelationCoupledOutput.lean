import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledFiberRecoding

namespace Mettapedia.Computability.PNP

/-- Output-variable obligation for nonconstant deterministic recodings of the
conditioned bit.  If every output fiber is approximately independent with
tolerance `τ`, then `τ` must dominate the same source-fiber product; it is
enough to inspect the `r true` fiber. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  have hdistinguish : ¬ (r true = r true ↔ r false = r true) := by
    intro hiff
    exact hnonconst ((hiff.mp rfl).symm)
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r (r true) τ hdistinguish (happrox (r true))

/-- Output-variable lower-bound obligation for nonconstant deterministic
recodings: lower bounds on both conditioned source-bit sides force the shared
fiber tolerance to dominate their product. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox)

/-- A nonconstant deterministic output variable cannot be approximately
independent of the source bit with tolerance below the explicit source-fiber
product. -/
theorem not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Lower-bound contradiction for output-variable approximate independence:
substantial mass on both source-bit sides rules out any smaller tolerance for a
nonconstant deterministic recoding. -/
theorem not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_lowerBounds_mul_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ loTrue loFalse hnonconst htrue hfalse happrox)


end Mettapedia.Computability.PNP
