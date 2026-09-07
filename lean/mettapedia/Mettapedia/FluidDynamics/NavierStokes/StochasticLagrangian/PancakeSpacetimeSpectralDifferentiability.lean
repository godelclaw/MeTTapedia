import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrozenMaterialDerivative
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Spacetime spectral differentiability without an eigenvalue gap

The largest eigenvalue of a C¹ symmetric operator field is differentiable
almost everywhere in real spacetime. Finite Fourier strain supplies the
C¹ field explicitly. At each such point every frozen material direction
has a derivative, including at spectral collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpacetimeSpectralDifferentiability

open scoped Topology Matrix.Norms.Elementwise
open MeasureTheory Filter Set
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierMaterialPaths
open PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeFourierPressureStrain PancakeMeasurableMaterialRate PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "X3" => Fin 3 → ℝ
local notation "ST" => ℝ × X3

local instance : Measure.IsAddHaarMeasure (volume : Measure ST) :=
  inferInstanceAs (Measure.IsAddHaarMeasure
    ((volume : Measure ℝ).prod (volume : Measure X3)))

/-- Compact-ball exhaustion upgrades Rademacher to the largest eigenvalue
of a C¹ operator field; no globally bounded spacetime derivative is needed. -/
theorem ae_differentiableAt_topEigenvalue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (S : E → SymmetricStrain) (hS : ContDiff ℝ 1 (fun z ↦ (S z).1)) :
    ∀ᵐ z ∂mu, DifferentiableAt ℝ (fun y ↦ topEigenvalue (S y)) z := by
  have hball : ∀ n : ℕ, ∀ᵐ z ∂mu, z ∈ Metric.ball (0 : E) (n + 1 : ℝ) →
      DifferentiableAt ℝ (fun y ↦ topEigenvalue (S y)) z := by
    intro n
    obtain ⟨C, hC⟩ := hS.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall (0 : E) (n + 1 : ℝ)) (isCompact_closedBall (0 : E) (n + 1 : ℝ))
    have hCS : LipschitzOnWith C S (Metric.closedBall (0 : E) (n + 1 : ℝ)) := hC
    have hL := lipschitzWith_topEigenvalue.comp_lipschitzOnWith hCS
    filter_upwards [hL.ae_differentiableWithinAt_of_mem (μ := mu)] with z hz hzb
    exact (hz (Metric.ball_subset_closedBall hzb)).differentiableAt
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hzb) Metric.ball_subset_closedBall)
  filter_upwards [ae_all_iff.mpr hball] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  apply hz n
  simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (by norm_num : (n : ℝ) < n + 1)

theorem contDiff_real_character (q : Wavevector) :
    ContDiff ℝ 1 (fun z : ST ↦ UnitAddTorus.mFourier q (torusPoint z.2)) := by
  simp only [mFourier_torusPoint, realModeDot]
  have hr : ContDiff ℝ 1 (fun z : ST ↦ ∑ i, (q i : ℝ) * z.2 i) := by fun_prop
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hr)).cexp

theorem contDiff_real_strain (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    ContDiff ℝ 1 (fun z : ST ↦
      (spatialStrain modes (filteredVelocity chi (u z.1)) (torusPoint z.2)).1) := by
  apply realMatrixOperatorCLM.contDiff.comp
  refine contDiff_pi.mpr (fun a ↦ contDiff_pi.mpr (fun b ↦ ?_))
  simp only [matrixReconstruction_apply]
  apply ContDiff.sum
  intro q hq
  have ha := (hu q hq a).comp (contDiff_fst : ContDiff ℝ 1 (fun z : ST ↦ z.1))
  have hb := (hu q hq b).comp (contDiff_fst : ContDiff ℝ 1 (fun z : ST ↦ z.1))
  have hphase := contDiff_real_character q
  simp only [strainCoeff, gradientCoeff, filteredVelocity,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem materialSpectralDifferentiable_of_real_fderiv
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (z : ST)
    (h : DifferentiableAt ℝ (fun y : ST ↦ topEigenvalue
      (spatialStrain modes (filteredVelocity chi (u y.1)) (torusPoint y.2))) z) :
    MaterialSpectralDifferentiable chi modes u z.1 (torusPoint z.2) := by
  let v := spatialVelocity chi modes (u z.1) (torusPoint z.2)
  let path : ℝ → ST := fun h ↦ (z.1 + h, fun i ↦ z.2 i + h * v i)
  have hp : DifferentiableAt ℝ path 0 := by dsimp [path]; fun_prop
  have hp0 : path 0 = z := by simp [path]
  have h' : DifferentiableAt ℝ (fun y : ST ↦ topEigenvalue
      (spatialStrain modes (filteredVelocity chi (u y.1)) (torusPoint y.2))) (path 0) := hp0 ▸ h
  have hh := h'.comp 0 hp
  simpa only [Function.comp_def, path, torusPoint_line, v, MaterialSpectralDifferentiable] using hh

theorem ae_real_materialSpectralDifferentiable
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    ∀ᵐ z : ST, MaterialSpectralDifferentiable chi modes u z.1 (torusPoint z.2) := by
  have h := ae_differentiableAt_topEigenvalue (volume : Measure ST)
    (fun z : ST ↦ spatialStrain modes (filteredVelocity chi (u z.1)) (torusPoint z.2))
    (contDiff_real_strain chi modes u hu)
  exact h.mono (fun z hz ↦ materialSpectralDifferentiable_of_real_fderiv chi modes u z hz)

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpacetimeSpectralDifferentiability
