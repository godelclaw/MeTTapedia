import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialDiffusionBudget
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# A constructed measurable material energy rate

The material rate is the derivative of the actual spectral energy along
a straight space-time path with the instantaneous fluid velocity. Its
joint measurability follows from continuity with parameters, rather than
from a measurable eigenvector selection. Differentiability and agreement
with the physical material equation are separate statements.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMeasurableMaterialRate

open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakePhysicalSpectralDefect
open PancakeDyadicDirectionEvolution PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy
open PancakeFourierPressureStrain PancakePhysicalViscousSplit PancakeMaterialDiffusionBudget
open PancakeRegularizedDiffusion PancakeSpectralFiniteDifference PancakeTopEigenvalueDerivative
open PancakeLowDiffusionBudget PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

section Parametric

variable {P : Type*} [TopologicalSpace P]

theorem continuous_parametric_reconstruction (modes : Finset Wavevector) (u : P → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ finiteFourierReconstruction modes (u z.1) z.2) := by
  refine continuous_pi (fun i ↦ ?_)
  simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro q hq
  exact ((UnitAddTorus.mFourier q).continuous.comp continuous_snd).mul ((hu q hq i).comp continuous_fst)

theorem continuous_parametric_strain (modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : P → FourierVelocity) (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ spatialStrain modes (filteredVelocity chi (u z.1)) z.2) := by
  apply Continuous.subtype_mk
  apply realMatrixOperatorCLM.continuous.comp
  refine continuous_pi (fun a ↦ continuous_pi (fun b ↦ ?_))
  simp only [matrixReconstruction_apply]
  apply continuous_finsetSum
  intro q hq
  have ha := (hu q hq a).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  have hb := (hu q hq b).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  simp only [strainCoeff, gradientCoeff, filteredVelocity,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem continuous_parametric_regularizedEnergy (modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : P → FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ physicalRegularizedEnergy chi modes (u z.1) delta z.2) := by
  have hS := continuous_parametric_strain modes chi u hu
  have hw := continuous_parametric_spatialVorticity modes u hu
  have hL := lipschitzWith_topEigenvalue.continuous.comp hS
  have hO := continuous_subtype_val.comp hS
  simp only [physicalRegularizedEnergy, regularizedEnergy, regularizedGap,
    sub_apply, smul_apply, one_apply_eq_self]
  exact hw.inner (((hL.add continuous_const).smul hw).sub (hO.clm_apply hw))

end Parametric

def spatialVelocity (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (finiteFourierReconstruction modes (filteredVelocity chi u) x)

def materialShift (v : R3) (h : ℝ) : T3 := torusPoint (fun i ↦ h * v i)

def frozenMaterialEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  physicalRegularizedEnergy chi modes (u (t + h)) delta
    (x + materialShift (spatialVelocity chi modes (u t) x) h)

def frozenMaterialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta t : ℝ) (x : T3) : ℝ :=
  deriv (frozenMaterialEnergy chi modes u delta t x) 0

/-- Differentiability of the actual largest eigenvalue along the same
instantaneous material path used by frozenMaterialEnergy. -/
def MaterialSpectralDifferentiable (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : Prop :=
  DifferentiableAt ℝ (fun h ↦ topEigenvalue
    (spatialStrain modes (filteredVelocity chi (u (t + h)))
      (x + materialShift (spatialVelocity chi modes (u t) x) h))) 0

theorem continuous_parametric_spatialVelocity (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun z : ℝ × T3 ↦ spatialVelocity chi modes (u z.1) z.2) := by
  apply complexRealPartEuclideanCLM.continuous.comp
  exact continuous_parametric_reconstruction modes (fun t ↦ filteredVelocity chi (u t))
    (fun q hq i ↦ continuous_const.mul (hu q hq i))

theorem continuous_frozenMaterialEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun z : (ℝ × T3) × ℝ ↦ frozenMaterialEnergy chi modes u delta z.1.1 z.1.2 z.2) := by
  have hv : Continuous (fun z : (ℝ × T3) × ℝ ↦ spatialVelocity chi modes (u z.1.1) z.1.2) :=
    (continuous_parametric_spatialVelocity chi modes u hu).comp
    (continuous_fst : Continuous (fun z : (ℝ × T3) × ℝ ↦ z.1))
  have hs : Continuous (fun z : (ℝ × T3) × ℝ ↦
      z.1.2 + materialShift (spatialVelocity chi modes (u z.1.1) z.1.2) z.2) := by
    apply Continuous.add continuous_fst.snd
    apply continuous_pi
    intro i
    change Continuous (fun z : (ℝ × T3) × ℝ ↦
      ((z.2 * spatialVelocity chi modes (u z.1.1) z.1.2 i : ℝ) : UnitAddCircle))
    have hvi : Continuous (fun z : (ℝ × T3) × ℝ ↦ spatialVelocity chi modes (u z.1.1) z.1.2 i) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hv
    exact continuous_quot_mk.comp (continuous_snd.mul hvi)
  have ht : Continuous (fun z : (ℝ × T3) × ℝ ↦ z.1.1 + z.2) := continuous_fst.fst.add continuous_snd
  have he := (continuous_parametric_regularizedEnergy modes chi u delta hu).comp (ht.prodMk hs)
  change Continuous (fun z : (ℝ × T3) × ℝ ↦ physicalRegularizedEnergy chi modes (u (z.1.1 + z.2)) delta
    (z.1.2 + materialShift (spatialVelocity chi modes (u z.1.1) z.1.2) z.2))
  exact he

theorem measurable_deriv_at_zero {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] (f : P → ℝ → ℝ) (hf : Continuous f.uncurry) :
    Measurable (fun p ↦ deriv (f p) (0 : ℝ)) := by
  have hm : Measurable (fun z : P × ℝ ↦ deriv (f z.1) z.2) := measurable_deriv_with_param hf
  exact hm.comp (show Measurable (fun p : P ↦ (p, (0 : ℝ))) from measurable_id.prodMk measurable_const)

/-- A genuine measurable space-time scalar, built without choosing a
measurable eigenframe. As usual deriv is zero at nondifferentiability
points; agreement with the physical rate must therefore be proved. -/
theorem measurable_frozenMaterialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Measurable (fun z : ℝ × T3 ↦ frozenMaterialRate chi modes u delta z.1 z.2) := by
  change Measurable (fun z : ℝ × T3 ↦ deriv (frozenMaterialEnergy chi modes u delta z.1 z.2) (0 : ℝ))
  exact measurable_deriv_at_zero (fun z : ℝ × T3 ↦ frozenMaterialEnergy chi modes u delta z.1 z.2)
    (continuous_frozenMaterialEnergy chi modes u delta hu)

theorem torusPoint_surjective : Function.Surjective torusPoint := by
  intro x
  choose r hr using fun i : Fin 3 ↦ Quotient.exists_rep (x i)
  exact ⟨r, funext hr⟩

theorem torusPoint_line (r : Fin 3 → ℝ) (v : R3) (h : ℝ) :
    torusPoint (fun i ↦ r i + h * v i) = torusPoint r + materialShift v h := by
  ext i
  simp [torusPoint, materialShift]

end Mettapedia.FluidDynamics.NavierStokes.PancakeMeasurableMaterialRate
