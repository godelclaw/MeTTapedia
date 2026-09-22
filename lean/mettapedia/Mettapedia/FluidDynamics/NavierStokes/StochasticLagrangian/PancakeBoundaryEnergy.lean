import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticProjectionLocalization

/-!
# Energy of the actual localization boundary field

The retained and exterior real reconstructions are orthogonal on a
negation-closed retained set. The exterior field therefore costs no more
than the actual localized energy. For the quadratic Fourier family,
nonnegative coverage controls the sum of these costs without a cell count.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryEnergy

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeFiniteFourierLocalization PancakeLocalizedProjectionBoundary PancakeRealFourierProjection
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open PancakeLowDiffusionBudget PancakePressureAnisotropyBudget PancakeGalerkinKineticEnergy
open PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localizedRetainedField (cutoff modes : Finset Wavevector) (c : Wavevector → ℂ)
    (w : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x)

theorem continuous_localizedRetainedField (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) : Continuous (localizedRetainedField cutoff modes c w) :=
  complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)

theorem integral_retained_boundary_inner_zero (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪localizedRetainedField cutoff modes c w x, localizedBoundaryField cutoff modes c w x⟫) = 0 := by
  exact integral_constant_operator_disjoint_neg_closed modes (finiteCutoffOutputModes cutoff modes \ modes)
    (finiteCutoffConvolutionCoeff cutoff modes c w) (finiteCutoffConvolutionCoeff cutoff modes c w) 1
    (Finset.disjoint_left.mpr (fun q hq ho ↦ (Finset.mem_sdiff.mp ho).2 hq)) hs

theorem integral_localized_energy_split (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hc : ∀ x : T3, (finiteScalarFourierReconstruction cutoff c x).im = 0)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ‖(finiteScalarFourierReconstruction cutoff c x).re •
      complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2) =
      (∫ x : T3, ‖localizedRetainedField cutoff modes c w x‖ ^ 2) +
      ∫ x : T3, ‖localizedBoundaryField cutoff modes c w x‖ ^ 2 := by
  have hR := continuous_localizedRetainedField cutoff modes c w
  have hB := continuous_localizedBoundaryField cutoff modes c w
  have hI : Continuous (fun x : T3 ↦ ⟪localizedRetainedField cutoff modes c w x,
      localizedBoundaryField cutoff modes c w x⟫) := hR.inner hB
  have hRs := (hR.norm.pow 2).integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hBs := (hB.norm.pow 2).integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  change Integrable (fun x : T3 ↦ ‖localizedRetainedField cutoff modes c w x‖ ^ 2) at hRs
  change Integrable (fun x : T3 ↦ ‖localizedBoundaryField cutoff modes c w x‖ ^ 2) at hBs
  have hIs := hI.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have he : ∀ x : T3, ‖(finiteScalarFourierReconstruction cutoff c x).re •
      complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 =
      (‖localizedRetainedField cutoff modes c w x‖ ^ 2 +
        2 * ⟪localizedRetainedField cutoff modes c w x, localizedBoundaryField cutoff modes c w x⟫) +
      ‖localizedBoundaryField cutoff modes c w x‖ ^ 2 := by
    intro x
    rw [real_localized_split cutoff modes c w x (hc x)]
    exact norm_add_sq_real _ _
  have hRI : Integrable (fun x : T3 ↦ ‖localizedRetainedField cutoff modes c w x‖ ^ 2 +
      2 * ⟪localizedRetainedField cutoff modes c w x, localizedBoundaryField cutoff modes c w x⟫) :=
    hRs.add (hIs.const_mul 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_add hRI hBs,
    integral_add hRs (hIs.const_mul 2), integral_const_mul,
    integral_retained_boundary_inner_zero cutoff modes c w hs, mul_zero, add_zero]

theorem integral_boundary_energy_le_localized (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hc : ∀ x : T3, (finiteScalarFourierReconstruction cutoff c x).im = 0)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ‖localizedBoundaryField cutoff modes c w x‖ ^ 2) ≤
      ∫ x : T3, (finiteScalarFourierReconstruction cutoff c x).re ^ 2 *
        ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 := by
  have h := integral_localized_energy_split cutoff modes c w hc hs
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hn : 0 ≤ ∫ x : T3, ‖localizedRetainedField cutoff modes c w x‖ ^ 2 :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  linarith

theorem integral_quadratic_boundary_energy_le (c : FourierCoeff (Fin 3))
    (modes : Finset Wavevector) (w : FourierVelocity) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ‖quadraticBoundaryField c modes w x‖ ^ 2) ≤
      ∫ x : T3, quadraticWeight c x ^ 2 *
        ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 := by
  have h := integral_boundary_energy_le_localized (quadraticFourierCoeff c).support modes
    (quadraticFourierCoeff c) w (fun x ↦ by rw [scalarReconstruction_quadratic]; rfl) hs
  simpa only [scalarReconstruction_quadratic, Complex.ofReal_re, quadraticBoundaryField] using h

theorem sum_nonnegative_sq_le_coverage_sq {ι : Type*} [Fintype ι] (rho : ι → ℝ)
    (C : ℝ) (hr : ∀ i, 0 ≤ rho i) (hC : ∑ i : ι, rho i ≤ C) :
    ∑ i : ι, rho i ^ 2 ≤ C ^ 2 := by
  have hsum : 0 ≤ ∑ i : ι, rho i := Finset.sum_nonneg (fun i _ ↦ hr i)
  have hi : ∀ i, rho i ≤ ∑ j : ι, rho j := fun i ↦
    Finset.single_le_sum (fun j _ ↦ hr j) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i : ι, rho i * (∑ j : ι, rho j) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hi i) (hr i)
    _ = (∑ i : ι, rho i) ^ 2 := by rw [← Finset.sum_mul, pow_two]
    _ ≤ C ^ 2 := by nlinarith

theorem sum_quadratic_boundary_energy_le_coverage {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes : Finset Wavevector) (w : FourierVelocity)
    (C : ℝ) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∑ i : ι, ∫ x : T3, ‖quadraticBoundaryField (c i) modes w x‖ ^ 2) ≤
      C ^ 2 * ∫ x : T3, ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 := by
  have hw : Continuous (fun x : T3 ↦ complexRealPartEuclidean (finiteFourierReconstruction modes w x)) :=
    complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)
  have hi : ∀ i : ι, Integrable (fun x : T3 ↦ quadraticWeight (c i) x ^ 2 *
      ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2) := fun i ↦
    (((continuous_quadraticWeight (c i)).pow 2).mul (hw.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∑ i : ι, ∫ x : T3, quadraticWeight (c i) x ^ 2 *
        ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ integral_quadratic_boundary_energy_le (c i) modes w hs)
    _ = ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x ^ 2 *
        ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 :=
      (integral_finsetSum _ (fun i _ ↦ hi i)).symm
    _ ≤ ∫ x : T3, C ^ 2 * ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 := by
      apply integral_mono (integrable_finsetSum _ (fun i _ ↦ hi i))
        (((hw.norm.pow 2).const_mul (C ^ 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro x
      dsimp only
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_nonnegative_sq_le_coverage_sq (fun i ↦ quadraticWeight (c i) x) C
          (fun i ↦ Complex.normSq_nonneg _) (hC x)) (sq_nonneg _)
    _ = _ := integral_const_mul _ _

theorem integral_real_reconstruction_energy_le (modes : Finset Wavevector) (w : FourierVelocity) :
    (∫ x : T3, ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2) ≤ fullEnergy modes w := by
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : T3 ↦ sq_nonneg
    ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖))
    (((continuous_coefficientReconstruction modes w).norm.pow 2).integrable_of_hasCompactSupport (μ := volume)
      (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall (fun x : T3 ↦ norm_realPart_sq_le (finiteFourierReconstruction modes w x)))
  change (∫ x : T3, ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2) ≤
    ∫ x : T3, ‖coefficientVec (finiteFourierReconstruction modes w x)‖ ^ 2 at h
  rw [integral_norm_coefficientReconstruction_sq] at h
  exact h

theorem sum_quadratic_boundary_energy_le_coefficients {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes : Finset Wavevector) (w : FourierVelocity)
    (C : ℝ) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∑ i : ι, ∫ x : T3, ‖quadraticBoundaryField (c i) modes w x‖ ^ 2) ≤
      C ^ 2 * fullEnergy modes w :=
  (sum_quadratic_boundary_energy_le_coverage c modes w C hs hC).trans
    (mul_le_mul_of_nonneg_left (integral_real_reconstruction_energy_le modes w) (sq_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryEnergy
