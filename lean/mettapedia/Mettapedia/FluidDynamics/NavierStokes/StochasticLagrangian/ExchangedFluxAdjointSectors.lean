import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointWeightedSum

/-!
# Exact Fourier cancellation sectors of the nonlinear adjoint

The outer slot selects small projected vorticity cross products. The
inner slot selects nearly opposite nonzero frequencies. These are
explicit Fourier predicates, not spatial coherence hypotheses. The
complementary contribution is retained in an exact decomposition.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSectors

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxAdjoint
open ExchangedFluxAdjointSeries ExchangedFluxAdjointGeometry ExchangedFluxOutputAdjoint
open ExchangedFluxAdjointSquareSum PeriodicTensorFourierFrame

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def SmallProjectedCross (δ : ℝ) (u : FourierVelocity) (p : Wavevector × Wavevector) : Prop :=
  ‖differenceCLM (0, p) (coefficientCross (fourierCurl u p.1) (fourierCurl u p.2))‖ ≤
    δ * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖)

def NearlyOpposite (η : ℝ) (q m : Wavevector) : Prop :=
  q ≠ 0 ∧ m ≠ 0 ∧ ‖frequencyVec (q + m)‖ ≤ η * ‖frequencyVec q‖

def smallCrossOuter (δ : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) : C3 :=
  if SmallProjectedCross δ u p then outerTest u F (q, p) else 0

def nearOppositeLeft (η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) : C3 :=
  if NearlyOpposite η q p.2 then leftTest u F (p.1, (q, p.2)) else 0

def selectedTerm (δ η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) : C3 :=
  -smallCrossOuter δ u F p q - (2 : ℝ) • nearOppositeLeft η u F p q

def remainderTerm (δ η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) : C3 :=
  combinedTest u F p q - selectedTerm δ η u F p q

def selectedTest (δ η : ℝ) (u : FourierVelocity) (F : H) (q : Wavevector) : C3 :=
  ∑' p, selectedTerm δ η u F p q

def remainderTest (δ η : ℝ) (u : FourierVelocity) (F : H) (q : Wavevector) : C3 :=
  ∑' p, remainderTerm δ η u F p q

/-- Relative to the coarse coefficient bound `54 * (2 * pi)`. -/
def sectorFactor (δ η : ℝ) : ℝ := δ / 36 + 4 * η / 3

theorem sectorFactor_nonneg {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 ≤ sectorFactor δ η := by unfold sectorFactor; positivity

theorem norm_smallCrossOuter_le_norm (δ : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖smallCrossOuter δ u F p q‖ ≤ ‖outerTest u F (q, p)‖ := by
  unfold smallCrossOuter
  split_ifs <;> simp

theorem norm_nearOppositeLeft_le_norm (η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖nearOppositeLeft η u F p q‖ ≤ ‖leftTest u F (p.1, (q, p.2))‖ := by
  unfold nearOppositeLeft
  split_ifs <;> simp

theorem summable_selectedTerm (δ η : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (q : Wavevector) :
    Summable (fun p ↦ selectedTerm δ η u F p q) := by
  have ho : Summable (fun p ↦ smallCrossOuter δ u F p q) :=
    ((summable_norm_outerTest u hu F q).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun p ↦ norm_smallCrossOuter_le_norm δ u F p q)).of_norm
  have hl : Summable (fun p ↦ nearOppositeLeft η u F p q) :=
    ((summable_norm_leftTest u hu F q).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun p ↦ norm_nearOppositeLeft_le_norm η u F p q)).of_norm
  exact ho.neg.sub (hl.const_smul 2)

theorem summable_remainderTerm (δ η : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (q : Wavevector) :
    Summable (fun p ↦ remainderTerm δ η u F p q) :=
  (summable_combinedTest u hu F q).sub (summable_selectedTerm δ η u hu F q)

theorem selectedTerm_add_remainderTerm (δ η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    selectedTerm δ η u F p q + remainderTerm δ η u F p q = combinedTest u F p q := by
  unfold remainderTerm
  abel

theorem remainderTerm_eq_complement (δ η : ℝ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    remainderTerm δ η u F p q =
      -(if SmallProjectedCross δ u p then 0 else outerTest u F (q, p)) -
        (2 : ℝ) • (if NearlyOpposite η q p.2 then 0 else leftTest u F (p.1, (q, p.2))) := by
  unfold remainderTerm combinedTest selectedTerm smallCrossOuter nearOppositeLeft
  split_ifs <;> simp
  abel

theorem coefficientTest_eq_selected_add_remainder (δ η : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (q : Wavevector) :
    coefficientTest u F q = selectedTest δ η u F q + remainderTest δ η u F q := by
  rw [← tsum_combinedTest u hu F q, selectedTest, remainderTest,
    ← (summable_selectedTerm δ η u hu F q).tsum_add (summable_remainderTerm δ η u hu F q)]
  exact tsum_congr (fun p ↦ (selectedTerm_add_remainderTerm δ η u F p q).symm)

theorem inner_coefficientTest_eq_selected_add_remainder (δ η : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (q : Wavevector) (a : C3) :
    ⟪a, coefficientTest u F q⟫ = ⟪a, selectedTest δ η u F q⟫ +
      ⟪a, remainderTest δ η u F q⟫ := by
  rw [coefficientTest_eq_selected_add_remainder δ η u hu F q, inner_add_right]

theorem norm_smallCrossOuter_le {δ : ℝ} (hδ : 0 ≤ δ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖smallCrossOuter δ u F p q‖ ≤ ((3 / 2 : ℝ) * (2 * Real.pi) * δ) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
  unfold smallCrossOuter
  split_ifs with hp
  · have hd : ‖differenceCLM (q, p) (coefficientCross (fourierCurl u p.1) (fourierCurl u p.2))‖ ≤
        δ * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) := hp
    have he : tripleFrequency (q, p) = pairShift p q := by simp [tripleFrequency, pairShift, add_assoc]
    apply (norm_outerTest_le_output u F (q, p)).trans
    rw [he]
    calc
      _ ≤ ((3 / 2 : ℝ) * ((2 * Real.pi) * ‖frequencyVec q‖) *
          (δ * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖))) *
          ‖outputCoefficient F (pairShift p q)‖ := by
        gcongr
        exact norm_curlCoefficientCLM_le q
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem norm_nearOppositeLeft_le {η : ℝ} (hη : 0 ≤ η) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖nearOppositeLeft η u F p q‖ ≤ (36 * (2 * Real.pi) * η) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
  unfold nearOppositeLeft
  split_ifs with hp
  · have he : tripleFrequency (p.1, (q, p.2)) = pairShift p q := by
      simp [tripleFrequency, pairShift, add_assoc, add_left_comm]
    have hn := hp.2.2
    apply (norm_leftTest_le_pair_output u F (p.1, (q, p.2)) hp.1 hp.2.1).trans
    rw [he]
    calc
      _ ≤ (36 * (2 * Real.pi) * (η * ‖frequencyVec q‖) *
          ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
        gcongr
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem norm_selectedTerm_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (u : FourierVelocity) (F : H) (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖selectedTerm δ η u F p q‖ ≤ (54 * (2 * Real.pi) * sectorFactor δ η) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
  have h : ‖selectedTerm δ η u F p q‖ ≤ ‖smallCrossOuter δ u F p q‖ +
      2 * ‖nearOppositeLeft η u F p q‖ := by
    simpa only [selectedTerm, norm_neg, norm_smul, Real.norm_ofNat] using
      norm_sub_le (-smallCrossOuter δ u F p q) ((2 : ℝ) • nearOppositeLeft η u F p q)
  apply h.trans
  have ho := norm_smallCrossOuter_le hδ u F p q
  have hl := norm_nearOppositeLeft_le hη u F p q
  unfold sectorFactor
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSectors
