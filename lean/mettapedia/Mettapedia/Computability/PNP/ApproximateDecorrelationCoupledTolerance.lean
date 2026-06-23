import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledGaps

namespace Mettapedia.Computability.PNP

/-- A coupled nondegenerate conditioning surface cannot satisfy a symmetric
approximate-independence tolerance smaller than the explicit source-fiber
product. -/
theorem not_countIndependentWithinTolerance_of_coupled_product_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  have hgap :
      countIndependentWithinForwardGap (Ω := Ω) C E F =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinForwardGap_coupled C E F hcouple
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.1)

/-- Obligation form of the coupled approximate-decorrelation blocker: any
successful symmetric tolerance certificate must dominate the source-fiber
product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_coupled_product_gt C E F τ hcouple
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Coupled obligation with explicit lower bounds: if both conditioned source
fibers have lower bounds, every approximate-independence tolerance certificate
must dominate the product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      C E F τ hcouple happrox)

/-- Coupled contradiction with explicit lower bounds: substantial mass on both
conditioned source-bit sides rules out any smaller symmetric tolerance. -/
theorem not_countIndependentWithinTolerance_of_coupled_lowerBounds_mul_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
      C E F τ loTrue loFalse hcouple htrue hfalse happrox)

/-- An anti-coupled nondegenerate conditioning surface cannot satisfy a
symmetric approximate-independence tolerance smaller than the explicit
source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_anticoupled_product_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  have hgap :
      countIndependentWithinBackwardGap (Ω := Ω) C E F =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinBackwardGap_anticoupled C E F hanti
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.2)

/-- Obligation form of the anti-coupled approximate-decorrelation blocker: any
successful symmetric tolerance certificate must dominate the source-fiber
product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_anticoupled_product_gt C E F τ hanti
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Anti-coupled obligation with explicit lower bounds: if both conditioned
source fibers have lower bounds, every approximate-independence tolerance
certificate must dominate the product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ hanti happrox)

/-- Anti-coupled contradiction with explicit lower bounds: substantial mass on
both conditioned source-bit sides rules out any smaller symmetric tolerance. -/
theorem not_countIndependentWithinTolerance_of_anticoupled_lowerBounds_mul_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ loTrue loFalse hanti htrue hfalse happrox)

end Mettapedia.Computability.PNP
