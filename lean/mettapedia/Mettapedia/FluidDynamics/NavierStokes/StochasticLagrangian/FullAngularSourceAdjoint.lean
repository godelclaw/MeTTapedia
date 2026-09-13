import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityFilterAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVelocityRHSReality
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteLowStrainWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityTestedStrainKernel

/-!
# Full nonlinear source tested by the adjoint-filtered angular gradient

The resolved and complete subgrid sources are combined before transferring
the filter. The resulting velocity, vorticity, strain and transport are
unrestricted fields. The strain pairing has its actual polarized two-point
representation. Its Fourier limit is a fixed-snapshot identity, not a
cutoff-uniform estimate or a bound near an existence endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullAngularSourceAdjoint

open scoped RealInnerProductSpace ComplexConjugate Topology
open Filter MeasureTheory
open PeriodicFourierTriad PancakeBlockReality PancakePeriodicCoherentSplit
open PancakeGalerkinKineticEnergy PancakeCurlOutputTail PancakeCoefficientLimitEquation
open PancakeHigherDerivativeMoments PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalAlignmentForcing LocalProjectionTransport
open FiniteAngularSourceWork FiniteAngularTransport FilteredAngularSourceBalance
open FiniteLowStrainWork FilteredAngularStrainIntegral VorticityFilterAdjoint
open FullVelocityRHSReality VelocityRHSMoments SpatialVorticityInviscidRate
open VorticityTestedStrainKernel

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def adjointTest (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : T3 → R3 :=
  realFilter P (fun q ↦ conj (χ q)) (correctedGradient κ (filteredVelocity χ u))

theorem continuous_adjointTest (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : Continuous (adjointTest κ P χ u) :=
  continuous_realFilter P _ _

theorem sourceWork_eq_full_pairing (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    sourceWork κ χ u = ∫ x : T3,
      ⟪adjointTest κ P χ u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫ :=
  integral_inner_filteredVorticity_eq_adjoint P χ hcut _
    (summable_fourierMoment_infiniteVelocityRHS 1 0 u hu)
    (infiniteVelocityRHS_conjugate 0 u hr) _
    (continuous_correctedGradient κ P _ (fun q hq ↦ by simp [filteredVelocity, hcut q hq]))

/-- One full nonlinear pairing; no absolute values or termwise bounds. -/
theorem sourceWork_eq_full_nonlinearity (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hd : ∀ q, modeDot q (u q) = 0) :
    sourceWork κ χ u = ∫ x : T3, ⟪adjointTest κ P χ u x,
      fullStrainOperator u x (fullVorticity u x) - transportVorticity u u x⟫ := by
  rw [sourceWork_eq_full_pairing κ P χ hcut u hu hr]
  congr 1
  funext x
  rw [eq_sub_iff_add_eq.mpr (fullVorticity_inviscidRHS u hu hd hr x)]

def fullTransportWork (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪adjointTest κ P χ u x, transportVorticity u u x⟫

theorem sourceWork_eq_fullWork_sub_transport (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hd : ∀ q, modeDot q (u q) = 0) :
    sourceWork κ χ u = fullWork u (adjointTest κ P χ u) - fullTransportWork κ P χ u := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hA := continuous_adjointTest κ P χ u
  have hS := (continuous_fullStrainOperator u hu1).clm_apply (continuous_fullVorticity u hu1)
  have hiS : Integrable (fun x : T3 ↦
      ⟪adjointTest κ P χ u x, fullStrainOperator u x (fullVorticity u x)⟫) :=
    (hA.inner hS).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiT : Integrable (fun x : T3 ↦ ⟪adjointTest κ P χ u x, transportVorticity u u x⟫) :=
    (hA.inner (LocalProjectionInviscidWork.continuous_transportVorticity u u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [sourceWork_eq_full_nonlinearity κ P χ hcut u hu hr hd]
  simp only [inner_sub_right]
  exact integral_sub hiS hiT

def fullResidualWork (κ : ℝ) (P Q : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ :=
  fullWork u (adjointTest κ P χ u) - fullTransportWork κ P χ u -
    (3 / κ) * deformationIntegral (filteredVelocity χ u) (filteredVelocity χ u) -
    lowStrainWork κ Q u (filteredVelocity χ u)

/-- Both former residual channels now use one full-source representation. -/
theorem residualStrainSubgridWork_eq_fullResidualWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    residualStrainSubgridWork κ Q χ (s.coefficients t) =
      fullResidualWork κ P Q χ (s.coefficients t) := by
  have hsplit := strainSubgridWork_eq_low_add_residual κ P Q χ hcut (s.coefficients t)
  rw [strainSubgridWork_solution_eq s κ P χ hcut C hχ hχr t ht,
    sourceWork_eq_fullWork_sub_transport κ P χ hcut _ hu (s.reality t) (s.transverse t)] at hsplit
  unfold fullResidualWork
  linarith only [hsplit]

def pairedResidualWork (modes : Finset Wavevector) (κ : ℝ) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  pairedWork modes u (adjointTest κ P χ u) - fullTransportWork κ P χ u -
    (3 / κ) * deformationIntegral (filteredVelocity χ u) (filteredVelocity χ u) -
    lowStrainWork κ Q u (filteredVelocity χ u)

theorem tendsto_pairedResidualWork (κ : ℝ) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hd : ∀ q, modeDot q (u q) = 0) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedResidualWork modes κ P Q χ u)
      atTop (𝓝 (fullResidualWork κ P Q χ u)) :=
  (((tendsto_pairedWork u hu hr hd _ (continuous_adjointTest κ P χ u)).sub
    tendsto_const_nhds).sub tendsto_const_nhds).sub tendsto_const_nhds

end Mettapedia.FluidDynamics.NavierStokes.FullAngularSourceAdjoint
