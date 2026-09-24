import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityTestedStrainKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularRadialWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularStrainIntegral

/-!
# Signed two-point work of the actual angular correction

The corrected gradient has a scalar radial coefficient and a transverse
part. The former retains the familiar cross-product exchange cancellation;
the latter contributes the complete polarized pairing, including both
endpoint terms. The actual strain is reconstructed from the same retained
vorticity. The full subgrid source is unchanged. Neither pair integral is
assigned a sign or a uniform time budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AngularStrainTwoPointWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis PolarizedCrossKernel EuclideanCrossProduct
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality PancakePeriodicCoherentSplit
open LocalLowDiffusionBudget LocalVorticityEighthMoment FourierFiniteSupport
open FiniteAngularSourceWork FiniteAngularInviscidWork FiniteAngularRadialWork
open VorticityStretchingKernel VorticityTestedStrainKernel LocalAngularCurlBudget
open PancakeLocalInfiniteVelocity PancakeFilteredStrainDynamics FilteredAngularStrainIntegral
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def radialCoefficient (κ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 - (24 / κ) * ‖angularCurl u x‖ ^ 2

theorem correctedGradient_eq_radial_sub_transverse (κ : ℝ) (u : FourierVelocity) (x : T3) :
    correctedGradient κ u x = radialCoefficient κ u x • fullVorticity u x -
      (3 / κ) • transverseGradient u x := by
  unfold correctedGradient radialCoefficient transverseGradient AngularCurlDecomposition.transverseGradient
    angularGradient angularCurl
  module

theorem continuous_radialCoefficient (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : Continuous (radialCoefficient κ u) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hH := AngularCurlDecomposition.continuous_angularCurl _ _ hw
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
  exact (hw.norm.pow 6).sub ((hH.norm.pow 2).const_mul _)

theorem continuous_transverseGradient (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : Continuous (transverseGradient u) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hH := AngularCurlDecomposition.continuous_angularCurl _ _ hw
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
  exact (continuous_angularGradient P u hs).sub (((hH.norm.pow 2).const_mul 8).smul hw)

def radialPairIntegral (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, ⟪cross (fullVorticity u x) (fullVorticity u y),
    kernel P (x - y) (radialCoefficient κ u x • fullVorticity u x -
      radialCoefficient κ u y • fullVorticity u y)⟫

def transversePairIntegral (P : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, pairedTest (kernel P (x - y))
    (fullVorticity u x) (fullVorticity u y) (transverseGradient u x) (transverseGradient u y)

/-- The transverse correction is not merely a test-vector increment. -/
theorem pairedTest_correctedGradient (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity) (x y : T3) :
    pairedTest (kernel P (x - y)) (fullVorticity u x) (fullVorticity u y)
      (correctedGradient κ u x) (correctedGradient κ u y) =
    2 * ⟪cross (fullVorticity u x) (fullVorticity u y),
      kernel P (x - y) (radialCoefficient κ u x • fullVorticity u x -
        radialCoefficient κ u y • fullVorticity u y)⟫ -
      (3 / κ) * pairedTest (kernel P (x - y)) (fullVorticity u x) (fullVorticity u y)
        (transverseGradient u x) (transverseGradient u y) := by
  rw [correctedGradient_eq_radial_sub_transverse, correctedGradient_eq_radial_sub_transverse,
    pairedTest_radial_sub_smul]

theorem pairedWork_correctedGradient (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    pairedWork P u (correctedGradient κ u) =
      radialPairIntegral κ P u / 2 - (3 / (4 * κ)) * transversePairIntegral P u := by
  have hw := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hr := (continuous_radialCoefficient κ P u hs).smul hw
  have ht := continuous_transverseGradient P u hs
  have hH : Continuous (fun z : T3 × T3 ↦ kernel P (z.1 - z.2)) :=
    (continuous_kernel P).comp (continuous_fst.sub continuous_snd)
  have ha : Continuous (fun z : T3 × T3 ↦ fullVorticity u z.1) := hw.comp continuous_fst
  have hb : Continuous (fun z : T3 × T3 ↦ fullVorticity u z.2) := hw.comp continuous_snd
  have hR : Integrable (fun z : T3 × T3 ↦ ⟪cross (fullVorticity u z.1) (fullVorticity u z.2),
      kernel P (z.1 - z.2) (radialCoefficient κ u z.1 • fullVorticity u z.1 -
        radialCoefficient κ u z.2 • fullVorticity u z.2)⟫) ((volume : Measure T3).prod volume) :=
    ((SignedCrossKernel.continuous_cross.comp (ha.prodMk hb)).inner
      (hH.clm_apply ((hr.comp continuous_fst).sub (hr.comp continuous_snd)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hT : Integrable (fun z : T3 × T3 ↦ pairedTest (kernel P (z.1 - z.2))
      (fullVorticity u z.1) (fullVorticity u z.2) (transverseGradient u z.1) (transverseGradient u z.2))
      ((volume : Measure T3).prod volume) :=
    (continuous_pairedTest _ _ _ _ _ hH ha hb (ht.comp continuous_fst)
      (ht.comp continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun z : T3 × T3 ↦ pairedTest (kernel P (z.1 - z.2))
      (fullVorticity u z.1) (fullVorticity u z.2) (correctedGradient κ u z.1) (correctedGradient κ u z.2))
      ((volume : Measure T3).prod volume) :=
    (continuous_pairedTest _ _ _ _ _ hH ha hb
      ((continuous_correctedGradient κ P u hs).comp continuous_fst)
      ((continuous_correctedGradient κ P u hs).comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold pairedWork radialPairIntegral transversePairIntegral
  rw [← integral_prod _ hJ, ← integral_prod _ hR, ← integral_prod _ hT]
  simp_rw [pairedTest_correctedGradient]
  rw [integral_sub (hR.const_mul 2) (hT.const_mul (3 / κ)), integral_const_mul, integral_const_mul]
  ring

/-- Exact self-coupled strain work; there is no independent imposed strain. -/
theorem strainWork_eq_pairs (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    stretching u - (3 / κ) * angularStrainWork u =
      radialPairIntegral κ P u / 2 - (3 / (4 * κ)) * transversePairIntegral P u := by
  rw [← integral_correctedGradient_strain κ P u hs]
  exact (fullWork_eq_pair_of_supported P u hs hr hd _
    (continuous_correctedGradient κ P u hs)).trans (pairedWork_correctedGradient κ P u hs)

/-- The signed source in the transport-paid energy inequality retains the
entire subgrid pairing, including outputs outside the retained support. -/
theorem strainSubgridWork_solution_eq_pairs {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (hχr : ∀ q, χ (-q) = conj (χ q)) (t : ℝ) :
    strainSubgridWork κ χ (s.coefficients t) =
      radialPairIntegral κ P (filteredVelocity χ (s.coefficients t)) / 2 -
        (3 / (4 * κ)) * transversePairIntegral P (filteredVelocity χ (s.coefficients t)) +
        fullSubgridWork κ χ (s.coefficients t) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hd (q : Wavevector) : modeDot q (filteredVelocity χ (s.coefficients t) q) = 0 := by
    simp only [filteredVelocity, modeDot_smul, s.transverse t, mul_zero]
  unfold strainSubgridWork
  rw [strainWork_eq_pairs κ P _ hs
    (PancakeSpatialStrainEvolution.filteredVelocity_conjugate χ _ hχr (s.reality t)) hd]

end Mettapedia.FluidDynamics.NavierStokes.AngularStrainTwoPointWork
