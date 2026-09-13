import Mettapedia.Analysis.QuadraticProjectionFrame
import Mettapedia.Analysis.UnitTorusContinuousRate

/-!
# Transfer from fixed scalar projections to vector-weighted integrals

All projection inequalities are aggregated using one fixed frame. The
transfer constant is selected before the fields, so it cannot depend on
their amplitudes, oscillations, or a Fourier support. The exponents on the
target and source may differ.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusProjectionFrameEnergy

open scoped RealInnerProductSpace
open MeasureTheory QuadraticProjectionFrame
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integrable_projection_product (m n : ℕ) (a z : T → R3)
    (ha : Continuous a) (hz : Continuous z) (k : Fin 5) :
    Integrable (fun x : T ↦ (⟪direction k, a x⟫ ^ 2) ^ m * (⟪direction k, z x⟫ ^ 2) ^ n) :=
  (by fun_prop : Continuous (fun x : T ↦
    (⟪direction k, a x⟫ ^ 2) ^ m * (⟪direction k, z x⟫ ^ 2) ^ n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integrable_moment (m n : ℕ) (a z : T → R3)
    (ha : Continuous a) (hz : Continuous z) : Integrable (fun x : T ↦ moment m n (a x) (z x)) :=
  ((continuous_moment m n).comp (ha.prodMk hz)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_norm_product (m n : ℕ) (a z : T → R3)
    (ha : Continuous a) (hz : Continuous z) :
    Integrable (fun x : T ↦ ‖a x‖ ^ (2 * m) * ‖z x‖ ^ (2 * n)) :=
  ((ha.norm.pow _).mul (hz.norm.pow _)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_moment_le (m n p q : ℕ) (a v z : T → R3)
    (ha : Continuous a) (hv : Continuous v) (hz : Continuous z) (K : ℝ)
    (hK : ∀ k : Fin 5,
      (∫ x : T, (⟪direction k, a x⟫ ^ 2) ^ m * (⟪direction k, z x⟫ ^ 2) ^ n) ≤
        K * ∫ x : T, (⟪direction k, a x⟫ ^ 2) ^ p * (⟪direction k, v x⟫ ^ 2) ^ q) :
    (∫ x : T, moment m n (a x) (z x)) ≤ K * ∫ x : T, moment p q (a x) (v x) := by
  unfold moment
  rw [integral_finsetSum _ (fun k _ ↦ integrable_projection_product m n a z ha hz k),
    integral_finsetSum _ (fun k _ ↦ integrable_projection_product p q a v ha hv k), Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ ↦ hK k)

/-- The constant is universal for the fixed exponents and frame. -/
theorem exists_transfer_constant (m n p q : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ L : ℝ, 0 < L ∧ ∀ a v z : T → R3,
      Continuous a → Continuous v → Continuous z → ∀ K : ℝ, 0 ≤ K →
      (∀ k : Fin 5,
        (∫ x : T, (⟪direction k, a x⟫ ^ 2) ^ m * (⟪direction k, z x⟫ ^ 2) ^ n) ≤
          K * ∫ x : T, (⟪direction k, a x⟫ ^ 2) ^ p * (⟪direction k, v x⟫ ^ 2) ^ q) →
      (∫ x : T, ‖a x‖ ^ (2 * m) * ‖z x‖ ^ (2 * n)) ≤
        L * K * ∫ x : T, ‖a x‖ ^ (2 * p) * ‖v x‖ ^ (2 * q) := by
  obtain ⟨c, hc, hclower⟩ := exists_lower_bound m n hm hn
  refine ⟨weight p q / c, div_pos (weight_pos p q) hc, ?_⟩
  intro a v z ha hv hz K hK hproj
  have hlow : c * (∫ x : T, ‖a x‖ ^ (2 * m) * ‖z x‖ ^ (2 * n)) ≤
      ∫ x : T, moment m n (a x) (z x) := by
    rw [← integral_const_mul]
    apply integral_mono ((integrable_norm_product m n a z ha hz).const_mul c)
      (integrable_moment m n a z ha hz)
    intro x
    simpa only [mul_assoc] using hclower (a x) (z x)
  have hmid := integral_moment_le m n p q a v z ha hv hz K hproj
  have hup : (∫ x : T, moment p q (a x) (v x)) ≤
      weight p q * ∫ x : T, ‖a x‖ ^ (2 * p) * ‖v x‖ ^ (2 * q) := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_moment p q a v ha hv)
      ((integrable_norm_product p q a v ha hv).const_mul (weight p q))
    intro x
    simpa only [mul_assoc] using moment_le p q (a x) (v x)
  have h := hlow.trans (hmid.trans (mul_le_mul_of_nonneg_left hup hK))
  calc
    _ ≤ (K * weight p q * ∫ x : T, ‖a x‖ ^ (2 * p) * ‖v x‖ ^ (2 * q)) / c := by
      apply (le_div_iff₀ hc).mpr
      nlinarith only [h]
    _ = _ := by ring

end Mettapedia.Analysis.UnitTorusProjectionFrameEnergy
