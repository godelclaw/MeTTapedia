import Mettapedia.Analysis.WeightedCurlHelicity

/-!
# Helicity absorption retaining amplitude-direction coherence

Project vorticity onto the gradient of its squared amplitude before
applying Young's inequality. The resulting cost vanishes when these are
perpendicular, even if curl helicity is nonzero. The quotient is defined
as zero at a zero amplitude gradient. It is measurable, but continuity
there is not asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.LongitudinalHelicityBudget

open WeightedCurlHelicity
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def amplitudeGradientSquare (a : R3) (D : Fin 3 → R3) : ℝ :=
  ∑ j : Fin 3, ⟪a, D j⟫ ^ 2

def longitudinalAmplitude (a : R3) (D : Fin 3 → R3) : ℝ :=
  ∑ j : Fin 3, a j * ⟪a, D j⟫

/-- Squared helicity weighted by the squared component of vorticity
along its amplitude gradient, rather than by its entire squared norm. -/
def directionalHelicityDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 4 * longitudinalAmplitude a D ^ 2 /
    amplitudeGradientSquare a D * helicity a D ^ 2

theorem amplitudeGradientSquare_nonneg (a : R3) (D : Fin 3 → R3) :
    0 ≤ amplitudeGradientSquare a D := by unfold amplitudeGradientSquare; positivity

theorem longitudinalAmplitude_sq_le (a : R3) (D : Fin 3 → R3) :
    longitudinalAmplitude a D ^ 2 ≤ ‖a‖ ^ 2 * amplitudeGradientSquare a D := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin 3 ↦ a j) (fun j ↦ ⟪a, D j⟫)
  simpa only [longitudinalAmplitude, amplitudeGradientSquare,
    EuclideanSpace.real_norm_sq_eq] using h

theorem longitudinalAmplitude_eq_zero_of_amplitudeGradientSquare_eq_zero
    (a : R3) (D : Fin 3 → R3) (h : amplitudeGradientSquare a D = 0) :
    longitudinalAmplitude a D = 0 := by
  have hc := longitudinalAmplitude_sq_le a D
  rw [h, mul_zero] at hc
  nlinarith only [hc, sq_nonneg (longitudinalAmplitude a D)]

theorem directionalHelicityDensity_nonneg (a : R3) (D : Fin 3 → R3) :
    0 ≤ directionalHelicityDensity a D := by
  unfold directionalHelicityDensity
  exact mul_nonneg (div_nonneg (by positivity) (amplitudeGradientSquare_nonneg a D))
    (sq_nonneg _)

theorem directionalHelicityDensity_le (a : R3) (D : Fin 3 → R3) :
    directionalHelicityDensity a D ≤ helicityDensity a D := by
  by_cases hb : amplitudeGradientSquare a D = 0
  · simp only [directionalHelicityDensity, hb, div_zero, zero_mul]
    unfold helicityDensity
    positivity
  · have hb' := lt_of_le_of_ne (amplitudeGradientSquare_nonneg a D) (Ne.symm hb)
    have hc : longitudinalAmplitude a D ^ 2 / amplitudeGradientSquare a D ≤ ‖a‖ ^ 2 :=
      (div_le_iff₀ hb').mpr (longitudinalAmplitude_sq_le a D)
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ ‖a‖ ^ 4)) (sq_nonneg (helicity a D))
    simpa only [directionalHelicityDensity, helicityDensity, mul_div_assoc,
      ← pow_add] using h

theorem directionalHelicityDensity_eq_zero_of_longitudinalAmplitude_eq_zero
    (a : R3) (D : Fin 3 → R3) (h : longitudinalAmplitude a D = 0) :
    directionalHelicityDensity a D = 0 := by
  simp [directionalHelicityDensity, h]

/-- If the amplitude gradient is normal to a plane, only the vorticity
component normal to that plane is charged. The normal-gradient hypothesis
is explicit; membership in a strain eigenplane alone does not supply it. -/
theorem directionalHelicityDensity_le_normal_component (a n : R3)
    (D : Fin 3 → R3) (c : ℝ) (hn : ‖n‖ = 1)
    (hgrad : ∀ j, ⟪a, D j⟫ = c * n j) :
    directionalHelicityDensity a D ≤ ‖a‖ ^ 4 * ⟪a, n⟫ ^ 2 * helicity a D ^ 2 := by
  have hA : longitudinalAmplitude a D = c * ⟪a, n⟫ := by
    simp only [longitudinalAmplitude, hgrad, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, Fin.sum_univ_three]
    ring
  have hB : amplitudeGradientSquare a D = c ^ 2 := by
    simp only [amplitudeGradientSquare, hgrad, mul_pow, ← Finset.mul_sum,
      ← EuclideanSpace.real_norm_sq_eq, hn, one_pow, mul_one]
  by_cases hc : c = 0
  · simp only [directionalHelicityDensity, hA, hc, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_div]
    positivity
  · rw [directionalHelicityDensity, hA, hB]
    apply le_of_eq
    field_simp

/-- The exact product relation preserves the longitudinal projection. -/
theorem longitudinalDefect_sq (a : R3) (D : Fin 3 → R3) :
    longitudinalDefect a D ^ 2 = radialDensity a D * directionalHelicityDensity a D := by
  by_cases hb : amplitudeGradientSquare a D = 0
  · have ha := longitudinalAmplitude_eq_zero_of_amplitudeGradientSquare_eq_zero a D hb
    change (‖a‖ ^ 4 * longitudinalAmplitude a D * helicity a D) ^ 2 = _
    simp [ha, directionalHelicityDensity]
  · change (‖a‖ ^ 4 * longitudinalAmplitude a D * helicity a D) ^ 2 =
      (‖a‖ ^ 4 * amplitudeGradientSquare a D) * directionalHelicityDensity a D
    unfold directionalHelicityDensity
    field_simp

theorem abs_longitudinalDefect_le (a : R3) (D : Fin 3 → R3)
    (η : ℝ) (hη : 0 < η) :
    |longitudinalDefect a D| ≤ η * radialDensity a D +
      directionalHelicityDensity a D / (4 * η) := by
  have hprod := longitudinalDefect_sq a D
  have hr : 0 ≤ radialDensity a D := by unfold radialDensity; positivity
  have hh := directionalHelicityDensity_nonneg a D
  have he : (η * radialDensity a D + directionalHelicityDensity a D / (4 * η)) * (4 * η) =
      4 * η ^ 2 * radialDensity a D + directionalHelicityDensity a D := by field_simp
  by_cases hr0 : radialDensity a D = 0
  · have hd0 : longitudinalDefect a D = 0 := by rw [hr0, zero_mul] at hprod; nlinarith [sq_nonneg (longitudinalDefect a D)]
    rw [hd0, abs_zero, hr0, mul_zero, zero_add]
    positivity
  · have hrp := lt_of_le_of_ne hr (Ne.symm hr0)
    apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * η by positivity)).mp
    rw [he]
    apply (mul_le_mul_iff_of_pos_right hrp).mp
    have hs := sq_nonneg (2 * η * radialDensity a D - |longitudinalDefect a D|)
    simp only [sub_sq, sq_abs] at hs
    nlinarith only [hs, hprod]

theorem measurable_directionalHelicityDensity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Measurable (fun x ↦ directionalHelicityDensity (a x) (fun j ↦ D j x)) := by
  have hA : Continuous (fun x ↦ longitudinalAmplitude (a x) (fun j ↦ D j x)) :=
    continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp ha).mul (ha.inner (hD j)))
  have hB : Continuous (fun x ↦ amplitudeGradientSquare (a x) (fun j ↦ D j x)) :=
    continuous_finsetSum _ (fun j _ ↦ (ha.inner (hD j)).pow 2)
  exact (((ha.norm.pow 4).mul (hA.pow 2)).measurable.div hB.measurable).mul
    ((continuous_helicity a D ha hD).pow 2).measurable

end Mettapedia.Analysis.LongitudinalHelicityBudget
