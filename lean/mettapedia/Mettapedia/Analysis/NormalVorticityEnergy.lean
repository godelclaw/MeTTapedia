import Mettapedia.Analysis.RadialPancakeCoherence
import Mettapedia.Analysis.ODE.AbsolutelyContinuousComparison

/-!
# Normal vorticity per unit separation

Normalize the separation, not the vorticity. The scalar remains defined at
zero vorticity, and no high power of the vorticity is included in its energy.
For a compressive strain direction its evolution is dissipative up to an
explicit geometric forcing. This differs from a transported covector normal.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.NormalVorticityEnergy

open MeasureTheory Set
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def component (a h : R3) : ℝ := ⟪h, a⟫ / ‖h‖

def energy (a h : R3) : ℝ := (component a h) ^ 2

theorem energy_eq (a h : R3) : energy a h = ⟪h, a⟫ ^ 2 / ‖h‖ ^ 2 := by
  simp only [energy, component, div_pow]

theorem energy_nonneg (a h : R3) : 0 ≤ energy a h := sq_nonneg _

theorem component_single (a : R3) (i : Fin 3) :
    component a (EuclideanSpace.single i 1) = a i := by
  simp [component, EuclideanSpace.inner_single_left]

/-- Controlling every normal component includes controlling the full vector. -/
theorem sum_energy_axes (a : R3) :
    (∑ i : Fin 3, energy a (EuclideanSpace.single i 1)) = ‖a‖ ^ 2 := by
  simp only [energy, component_single, EuclideanSpace.real_norm_sq_eq]

theorem abs_component_mul_norm (a h : R3) : |component a h| * ‖h‖ = |⟪h, a⟫| := by
  by_cases hh : h = 0
  · simp [component, hh]
  · rw [component, abs_div, abs_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hh)]

def rate (a h va vh : R3) : ℝ :=
  (⟪vh, a⟫ + ⟪h, va⟫) / ‖h‖ - component a h * ⟪h, vh⟫ / ‖h‖ ^ 2

theorem hasDerivAt_component {a h : ℝ → R3} {va vh : R3} {t : ℝ}
    (ha : HasDerivAt a va t) (hh : HasDerivAt h vh t) (hne : h t ≠ 0) :
    HasDerivAt (fun s ↦ component (a s) (h s)) (rate (a t) (h t) va vh) t := by
  have hn : HasDerivAt (fun s ↦ ‖h s‖) (⟪h t, vh⟫ / ‖h t‖) t :=
    hasDerivWithinAt_univ.mp (ODE.hasDerivWithinAt_norm_of_ne_zero
      (hh.hasDerivWithinAt (s := univ)) hne)
  have hd := (hh.inner ℝ ha).div hn (norm_ne_zero_iff.mpr hne)
  apply hd.congr_deriv
  simp only [component, rate]
  field_simp [norm_ne_zero_iff.mpr hne]
  ring

/-- The numerator of the normalized forcing. The last term removes the
change in the length of the separation. -/
def forcingNumerator (a h r ra rh : R3) : ℝ :=
  2 * ⟪r, a⟫ + ⟪rh, a⟫ + ⟪h, ra⟫ -
    ⟪h, a⟫ * (⟪h, r⟫ + ⟪h, rh⟫) / ‖h‖ ^ 2

theorem rate_eq_strain_add_forcing (A : Op) (a h r ra rh : R3) (σ : ℝ)
    (hh : h ≠ 0)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫) :
    rate a h (A a + ra) (A h + rh) =
      σ * component a h + forcingNumerator a h r ra rh / ‖h‖ := by
  have hn : ⟪h, A h⟫ = σ * ‖h‖ ^ 2 + ⟪h, r⟫ := by
    have he := hA h
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at he
    linarith only [he, real_inner_comm (A h) h, real_inner_comm r h]
  unfold rate
  rw [RadialPancakeCoherence.normalPairRate_eq A a h r ra rh σ hA]
  simp only [inner_add_right, hn, component, forcingNumerator]
  field_simp [norm_ne_zero_iff.mpr hh]
  ring

theorem forcingNumerator_of_orthogonal (a h r ra rh : R3) (hr : ⟪h, r⟫ = 0) :
    forcingNumerator a h r ra rh =
      2 * ⟪r, a⟫ + ⟪rh, a⟫ + ⟪h, ra⟫ - ⟪h, a⟫ * ⟪h, rh⟫ / ‖h‖ ^ 2 := by
  simp only [forcingNumerator, hr, zero_add]

theorem square_rate_le (σ κ z f : ℝ) (hκ : 0 < κ) (hσ : σ ≤ -κ) :
    2 * z * (σ * z + f) ≤ -κ * z ^ 2 + f ^ 2 / κ := by
  have hs := mul_le_mul_of_nonneg_right hσ (sq_nonneg z)
  apply (mul_le_mul_iff_of_pos_right hκ).mp
  have he : (-κ * z ^ 2 + f ^ 2 / κ) * κ = -κ ^ 2 * z ^ 2 + f ^ 2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (κ * z - f), mul_le_mul_of_nonneg_left hs hκ.le]

/-- A normal component with nonpositive strain is bounded by its initial
value and the actual normalized forcing, without an exponential strain cost. -/
theorem abs_le_initial_add_integral {z f σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hz : AbsolutelyContinuousOnInterval z a b) (hf : IntervalIntegrable f volume a b)
    (hode : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt z (σ t * z t + f t) t)
    (hσ : ∀ t ∈ uIcc a b, σ t ≤ 0) :
    |z b| ≤ |z a| + ∫ t in a..b, |f t| := by
  let A (t : ℝ) : ℝ →L[ℝ] ℝ := σ t • ContinuousLinearMap.id ℝ ℝ
  have hA (t : ℝ) (ht : t ∈ uIcc a b) (x : ℝ) : ⟪x, A t x⟫ ≤ 0 := by
    simp only [A, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, RCLike.inner_apply, conj_trivial]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (hσ t ht) (sq_nonneg x)]
  simpa only [Real.norm_eq_abs] using ODE.norm_le_initial_add_integral_of_ae_dissipative
    A hab hz hf hode hA

end Mettapedia.Analysis.NormalVorticityEnergy
