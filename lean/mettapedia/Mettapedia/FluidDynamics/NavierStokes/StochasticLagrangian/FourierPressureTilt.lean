import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureCommutator

/-!
# The direct pressure action transverse to the leading line

The complete commutator also sees motion inside the transverse plane.
The direct transverse action is more selective: each pressure mode has
the angular factor `⟪q,e⟫` as well as its transverse wavevector. Vanishing
longitudinal frequencies is an explicit hypothesis, not a consequence of
vorticity alignment at one spatial point.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureTilt

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierMaterialPaths
open PancakeAnisotropyDepletion PancakeSpectralDefectEvolution PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity SpectralSourceCommutator
open LocalPressureCommutator FourierPressureCommutator

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem filteredPressure_apply_eq_sum (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (e : R3) :
    filteredPressureOperator chi outputs u x e = ∑ q ∈ outputs,
      (pressureModeAmplitude chi u q x * ⟪realFrequency q, e⟫) • realFrequency q := by
  rw [filteredPressureOperator_eq_sum]
  simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]

theorem transverse_filteredPressure_eq_sum (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (e : R3) :
    lineRemainder e (filteredPressureOperator chi outputs u x e) = ∑ q ∈ outputs,
      (pressureModeAmplitude chi u q x * ⟪realFrequency q, e⟫) • lineRemainder e (realFrequency q) := by
  rw [filteredPressure_apply_eq_sum, lineRemainder_sum]
  simp only [lineRemainder_smul]

theorem norm_transverse_filteredPressure_le (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (e : R3) :
    ‖lineRemainder e (filteredPressureOperator chi outputs u x e)‖ ≤ ∑ q ∈ outputs,
      |pressureModeAmplitude chi u q x| * |⟪realFrequency q, e⟫| * ‖lineRemainder e (realFrequency q)‖ := by
  rw [transverse_filteredPressure_eq_sum]
  convert norm_sum_le outputs (fun q ↦
    (pressureModeAmplitude chi u q x * ⟪realFrequency q, e⟫) • lineRemainder e (realFrequency q)) using 1
  simp only [norm_smul, Real.norm_eq_abs, abs_mul]

theorem filteredPressure_symmetric (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (v w : R3) :
    ⟪filteredPressureOperator chi outputs u x v, w⟫ =
      ⟪v, filteredPressureOperator chi outputs u x w⟫ := by
  rw [filteredPressure_apply_eq_sum, filteredPressure_apply_eq_sum]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro q _
  rw [real_inner_comm v (realFrequency q)]
  ring

theorem filteredPressure_apply_eq_zero_of_perpendicular
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) (e : R3)
    (hp : ∀ q ∈ outputs, pressureModeAmplitude chi u q x ≠ 0 → ⟪realFrequency q, e⟫ = 0) :
    filteredPressureOperator chi outputs u x e = 0 := by
  rw [filteredPressure_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hz : pressureModeAmplitude chi u q x = 0
  · rw [hz, zero_mul, zero_smul]
  · rw [hp q hq hz, mul_zero, zero_smul]

theorem abs_pressureAnisotropy_le_transverse (S : SymmetricStrain)
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) (w : R3) :
    let H := filteredPressureOperator chi outputs u x
    let e := topVector S
    let m := lineRemainder e w
    |remainderAnisotropy H e w| ≤ 2 * ‖H‖ * ‖m‖ ^ 2 +
      2 * ‖w‖ * ‖m‖ * ‖lineRemainder e (H e)‖ := by
  dsimp only
  have hs : (filteredPressureOperator chi outputs u x).adjoint =
      filteredPressureOperator chi outputs u x :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      (filteredPressure_symmetric chi outputs u x)).symm
  have h := abs_anisotropy_le_transverse S (filteredPressureOperator chi outputs u x) w
  rw [hs] at h
  nlinarith only [h]

theorem abs_pressureAnisotropy_le_quadratic_of_perpendicular
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) (e w : R3)
    (hp : ∀ q ∈ outputs, pressureModeAmplitude chi u q x ≠ 0 → ⟪realFrequency q, e⟫ = 0) :
    |remainderAnisotropy (filteredPressureOperator chi outputs u x) e w| ≤
      ‖filteredPressureOperator chi outputs u x‖ * ‖lineRemainder e w‖ ^ 2 := by
  let H := filteredPressureOperator chi outputs u x
  have hHe : H e = 0 := filteredPressure_apply_eq_zero_of_perpendicular chi outputs u x e hp
  have hs (v z : R3) : ⟪H v, z⟫ = ⟪v, H z⟫ := filteredPressure_symmetric chi outputs u x v z
  have hm : H (lineRemainder e w) = H w := by
    simp only [lineRemainder, map_sub, map_smul, hHe, smul_zero, sub_zero]
  have hi : ⟪lineRemainder e w, H (lineRemainder e w)⟫ = ⟪w, H w⟫ := by
    rw [hm]
    simp only [lineRemainder, inner_sub_left, real_inner_smul_left,
      ← hs e w, hHe, inner_zero_left, mul_zero, sub_zero]
  change |⟪e, H e⟫ * ‖w‖ ^ 2 - ⟪w, H w⟫| ≤ _
  rw [hHe, inner_zero_right, zero_mul, zero_sub, abs_neg, ← hi]
  calc
    _ ≤ ‖lineRemainder e w‖ * ‖H (lineRemainder e w)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖lineRemainder e w‖ * (‖H‖ * ‖lineRemainder e w‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureTilt
