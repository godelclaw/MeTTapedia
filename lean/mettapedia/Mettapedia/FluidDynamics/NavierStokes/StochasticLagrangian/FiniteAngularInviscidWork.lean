import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularSourceBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionSourceSplit

/-!
# Signed strain and deformation in the complete angular source

The actual inviscid vorticity equation is paired with the constructed
angular variational gradient. Scalar transport cancels and the deformation
commutator is retained with its exact sign. The full subgrid pairing keeps
all outputs, including those cancelling the resolved RHS outside the filter.
No sign or initial-data estimate for the combined source is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularInviscidWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation
open PancakeBlockReality PancakeFilteredStrainDynamics PancakeSobolevFiberEnvelope
open PancakeLocalInfiniteVelocity InfiniteFilteredEquation
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open LocalAlignmentForcing LocalJointDiffusionBudget
open LocalProjectionTransport SpatialVorticityInviscidRate FourierFiniteSupport
open FiniteAngularSourceWork FiniteAngularTransport FilteredAngularSourceBalance

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def angularStrainWork (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪angularGradient u x, fullStrainOperator u x (fullVorticity u x)⟫

def fullSubgridWork (κ : ℝ) (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪correctedGradient κ (filteredVelocity χ u) x, fullVorticity (subgridForce χ u) x⟫

theorem integral_correctedGradient_strain (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, ⟪correctedGradient κ u x, fullStrainOperator u x (fullVorticity u x)⟫) =
      stretching u - (3 / κ) * angularStrainWork u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hS := (continuous_fullStrainOperator u (summable_fourierMoment P u hs 1)).clm_apply ha
  have hiA : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫) :=
    ((ha.norm.pow 6).mul (ha.inner hS)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiJ : Integrable (fun x : T3 ↦ ⟪angularGradient u x, fullStrainOperator u x (fullVorticity u x)⟫) :=
    ((continuous_angularGradient P u hs).inner hS).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [integral_sub hiA (hiJ.const_mul _), integral_const_mul]
  rfl

theorem integral_correctedGradient_inviscidRHS (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪correctedGradient κ u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫) =
      stretching u - (3 / κ) * angularStrainWork u + (3 / κ) * deformationIntegral u u := by
  have hm := summable_fourierMoment P u hs 3
  have hJ := continuous_correctedGradient κ P u hs
  have ht := LocalProjectionInviscidWork.continuous_transportVorticity u u
  have hv := continuous_fullVorticity _ (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hm)
  have hiR : Integrable (fun x : T3 ↦ ⟪correctedGradient κ u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫) :=
    (hJ.inner hv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiT : Integrable (fun x : T3 ↦ ⟪correctedGradient κ u x, transportVorticity u u x⟫) :=
    (hJ.inner ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x : T3, ⟪correctedGradient κ u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫ +
      ⟪correctedGradient κ u x, transportVorticity u u x⟫) =
      ∫ x : T3, ⟪correctedGradient κ u x, fullStrainOperator u x (fullVorticity u x)⟫ := by
    simp only [← inner_add_right, fullVorticity_inviscidRHS u hm hd hr]
  rw [integral_add hiR hiT, integral_correctedGradient_transport κ P P u u hs hs hd,
    integral_correctedGradient_strain κ P u hs] at he
  linarith only [he]

theorem fullSubgridWork_eq_sub (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    fullSubgridWork κ χ u = sourceWork κ χ u -
      ∫ x : T3, ⟪correctedGradient κ (filteredVelocity χ u) x,
        fullVorticity (infiniteVelocityRHS 0 (filteredVelocity χ u)) x⟫ := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hm (v : FourierVelocity) (m : ℕ) := summable_fourierMoment P _ (hs v) m
  have hJ := continuous_correctedGradient κ P _ (hs u)
  have hf := continuous_fullVorticity _ (hm (infiniteVelocityRHS 0 u) 1)
  have hv := VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 _ (hm u 3)
  have hiF : Integrable (fun x : T3 ↦ ⟪correctedGradient κ (filteredVelocity χ u) x,
      fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 u)) x⟫) :=
    (hJ.inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (fun x : T3 ↦ ⟪correctedGradient κ (filteredVelocity χ u) x,
      fullVorticity (infiniteVelocityRHS 0 (filteredVelocity χ u)) x⟫) :=
    (hJ.inner (continuous_fullVorticity _ hv)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold fullSubgridWork
  rw [FilteredProjectionSourceSplit.subgridForce_eq_sub χ C hχ u hu]
  simp_rw [CurlEigenfieldDefect.fullVorticity_sub _ _ (hm _ 1) hv, inner_sub_right]
  exact integral_sub hiF hiG

/-- This is a signed identity, not separate bounds on its four terms. -/
theorem sourceWork_eq_strain_deformation_subgrid (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    sourceWork κ χ u = stretching (filteredVelocity χ u) -
      (3 / κ) * angularStrainWork (filteredVelocity χ u) +
      (3 / κ) * deformationIntegral (filteredVelocity χ u) (filteredVelocity χ u) + fullSubgridWork κ χ u := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hdχ (q : Wavevector) : modeDot q (filteredVelocity χ u q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, hd q, mul_zero]
  rw [fullSubgridWork_eq_sub κ P χ hcut C hχ u hu,
    integral_correctedGradient_inviscidRHS κ P _ hs hdχ
      (PancakeSpatialStrainEvolution.filteredVelocity_conjugate χ u hχr hr)]
  ring

theorem sourceWork_solution_eq {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sourceWork κ χ (s.coefficients t) = stretching (filteredVelocity χ (s.coefficients t)) -
      (3 / κ) * angularStrainWork (filteredVelocity χ (s.coefficients t)) +
      (3 / κ) * deformationIntegral (filteredVelocity χ (s.coefficients t)) (filteredVelocity χ (s.coefficients t)) +
      fullSubgridWork κ χ (s.coefficients t) :=
  sourceWork_eq_strain_deformation_subgrid κ P χ hcut C hχ hχr _
    (s.summable_convection t ht) (s.transverse t) (s.reality t)

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularInviscidWork
