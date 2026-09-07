import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevAbsoluteTail

/-!
# Jointly continuous spatial reconstruction from the local Sobolev budget

The Fourier series is summed in bounded continuous functions of time and
space. Uniformly small finite tails, rather than a summable sequence of
individual time-supremum bounds, prove summability in that Banach space.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevSpaceTime

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeSobolevAbsoluteTail PancakeSobolevVelocityRate
open PancakePhysicalFourierDerivative PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl

local notation "T3" => UnitAddTorus (Fin 3)
abbrev SpaceTime (T : ℝ) := Set.Icc (0 : ℝ) T × T3

def modeSpaceTime {T : ℝ} (a : CoefficientLimit T) (k : Wavevector) (i : Fin 3) :
    BoundedContinuousFunction (SpaceTime T) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ UnitAddTorus.mFourier k z.2 * a k i z.1, by fun_prop⟩

theorem modeSpaceTime_apply {T : ℝ} (a : CoefficientLimit T) (k : Wavevector)
    (i : Fin 3) (z : SpaceTime T) :
    modeSpaceTime a k i z = UnitAddTorus.mFourier k z.2 * a k i z.1 := rfl

theorem norm_sum_modeSpaceTime_le {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (F M : Finset Wavevector) (h : Disjoint M F) (i : Fin 3) :
    ‖∑ k ∈ M, modeSpaceTime a k i‖ ≤ tailAllowance B F := by
  apply (BoundedContinuousFunction.norm_le (tailAllowance_nonneg B F)).mpr
  intro z
  simp only [BoundedContinuousFunction.sum_apply, modeSpaceTime_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ M, amplitude (limitField a z.1) k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, norm_character, one_mul]
      exact PiLp.norm_apply_le (coefficientVec (limitField a z.1 k)) i
    _ ≤ tailAllowance B F := sum_amplitude_le_tail _ B (hB z.1) F M h

theorem summable_modeSpaceTime {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B) (i : Fin 3) :
    Summable (fun k ↦ modeSpaceTime a k i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨F, hF⟩ := exists_small_tailAllowance B ε hε
  exact ⟨F, fun M hM ↦ (norm_sum_modeSpaceTime_le a B hB F M hM i).trans_lt hF⟩

def spatialPath {T : ℝ} (a : CoefficientLimit T) (i : Fin 3) :
    BoundedContinuousFunction (SpaceTime T) ℂ :=
  ∑' k, modeSpaceTime a k i

theorem norm_spatialPath_sub_sum_le {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (F : Finset Wavevector) (i : Fin 3) :
    ‖spatialPath a i - ∑ k ∈ F, modeSpaceTime a k i‖ ≤ tailAllowance B F := by
  have ht := ((summable_modeSpaceTime a B hB i).hasSum.sub_const
    (∑ k ∈ F, modeSpaceTime a k i)).norm
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop F] with M hM
  rw [← Finset.sum_sdiff hM]
  simp only [add_sub_cancel_right]
  exact norm_sum_modeSpaceTime_le a B hB F (M \ F) Finset.sdiff_disjoint i

theorem spatialPath_apply {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (i : Fin 3) (z : SpaceTime T) :
    spatialPath a i z = ∑' k, UnitAddTorus.mFourier k z.2 * a k i z.1 := by
  have he := (BoundedContinuousFunction.evalCLM ℂ z).map_tsum
    (summable_modeSpaceTime a B hB i)
  simpa only [spatialPath, BoundedContinuousFunction.evalCLM_apply, modeSpaceTime_apply] using he

theorem spatialPath_eq_fullFourierField {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (i : Fin 3) (z : SpaceTime T) :
    spatialPath a i z = fullFourierField id (limitField a z.1) z.2 i := by
  rw [spatialPath_apply a B hB, fullFourierField_component id _
    (PancakeSobolevAbsoluteTail.summable_norm_coefficients _ B (hB z.1))]
  rfl

/-- Convergence in the joint uniform norm on the entire closed time-space cylinder. -/
theorem tendstoUniformly_spatialPath {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B) (i : Fin 3) :
    TendstoUniformly
      (fun F : Finset Wavevector ↦ fun z : SpaceTime T ↦
        ∑ k ∈ F, UnitAddTorus.mFourier k z.2 * a k i z.1)
      (spatialPath a i) atTop := by
  have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (summable_modeSpaceTime a B hB i).hasSum
  change TendstoUniformly (fun F z ↦ (∑ k ∈ F, modeSpaceTime a k i) z)
    (spatialPath a i) atTop at h
  simpa only [BoundedContinuousFunction.sum_apply, modeSpaceTime_apply] using h

theorem continuous_fullFourierField {T : ℝ} (a : CoefficientLimit T)
    (B : ℝ) (hB : ∀ t F, sobolevEnergy F (limitField a t) ≤ B) :
    Continuous (fun z : SpaceTime T ↦ fullFourierField id (limitField a z.1) z.2) := by
  apply continuous_pi
  intro i
  have he : (fun z : SpaceTime T ↦ fullFourierField id (limitField a z.1) z.2 i) =
      fun z ↦ spatialPath a i z :=
    funext (fun z ↦ (spatialPath_eq_fullFourierField a B hB i z).symm)
  rw [he]
  exact (spatialPath a i).continuous

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevSpaceTime
