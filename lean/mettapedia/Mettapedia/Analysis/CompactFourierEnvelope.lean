import Mettapedia.Analysis.CompactSchwartzFamily

/-!
# A common integrable envelope for a compact Fourier family

Uniform decay constructs one nonnegative continuous majorant for every
parameter, with a prescribed spatial moment. This is stronger than a
uniform bound on the individual kernel integrals.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactFourierEnvelope

open MeasureTheory MeasureTheory.Measure Set CompactSchwartzFamily
open scoped FourierTransform SchwartzMap ContDiff

variable {E : Type*} [NormedAddCommGroup E]

def polynomialTail (p : ℕ) (x : E) : ℝ := (1 + ‖x‖) ^ (-(p : ℝ))

theorem polynomialTail_nonneg (p : ℕ) (x : E) : 0 ≤ polynomialTail p x := by
  unfold polynomialTail
  positivity

theorem continuous_polynomialTail (p : ℕ) : Continuous (polynomialTail (E := E) p) := by
  unfold polynomialTail
  exact (continuous_const.add continuous_norm).rpow_const
    (fun x ↦ Or.inl (ne_of_gt (show 0 < (1 : ℝ) + ‖x‖ by positivity)))

theorem pow_mul_polynomialTail_le (m p : ℕ) (x : E) :
    ‖x‖ ^ m * polynomialTail (m + p) x ≤ polynomialTail p x := by
  calc
    _ ≤ (1 + ‖x‖) ^ m * polynomialTail (m + p) x := by
      apply mul_le_mul_of_nonneg_right _ (polynomialTail_nonneg _ _)
      gcongr
      linarith only [norm_nonneg x]
    _ = _ := by
      unfold polynomialTail
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
      congr 1
      push_cast
      ring

theorem polynomialTail_add_le (m p : ℕ) (x : E) :
    polynomialTail (m + p) x ≤ polynomialTail p x := by
  unfold polynomialTail
  apply Real.rpow_le_rpow_of_exponent_le (by linarith only [norm_nonneg x])
  push_cast
  linarith only [Nat.cast_nonneg (α := ℝ) m]

variable [MeasurableSpace E] [BorelSpace E]

theorem integrable_moment_polynomialTail (μ : Measure E) [μ.HasTemperateGrowth] (m : ℕ) :
    Integrable (fun x : E ↦ ‖x‖ ^ m * polynomialTail (m + μ.integrablePower) x) μ := by
  apply (integrable_pow_neg_integrablePower μ).mono'
    ((continuous_norm.pow m).mul (continuous_polynomialTail _)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖‖x‖ ^ m * polynomialTail (m + μ.integrablePower) x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (polynomialTail_nonneg _ _))]
  exact pow_mul_polynomialTail_le _ _ _

theorem integrable_polynomialTail_add (μ : Measure E) [μ.HasTemperateGrowth] (m : ℕ) :
    Integrable (polynomialTail (E := E) (m + μ.integrablePower)) μ := by
  apply (integrable_pow_neg_integrablePower μ).mono' (continuous_polynomialTail _).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (polynomialTail_nonneg _ _)]
  exact polynomialTail_add_le _ _ _

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)

theorem exists_uniform_fourierInv_envelope (S : T → 𝓢(X, ℂ))
    (hS : ContDiff ℝ ∞ (fun z : T × X ↦ S z.1 z.2))
    (A : Set T) (hA : IsCompact A) (L : Set X) (hL : IsCompact L)
    (hs : ∀ t, tsupport (S t) ⊆ L) (m : ℕ) :
    ∃ H : X → ℝ, (∀ x, 0 ≤ H x) ∧ Continuous H ∧ Integrable H ∧
      Integrable (fun x ↦ ‖x‖ ^ m * H x) ∧
      ∀ t ∈ A, ∀ x, ‖(𝓕⁻ (S t)) x‖ ≤ H x := by
  let n := m + (volume : Measure X).integrablePower
  obtain ⟨C0, hC0, hb0⟩ := exists_uniform_fourierInv_decay S hS A hA L hL hs 0
  obtain ⟨Cn, hCn, hbn⟩ := exists_uniform_fourierInv_decay S hS A hA L hL hs n
  let D : ℝ := 2 ^ n * (C0 + Cn)
  refine ⟨fun x ↦ D * polynomialTail n x,
    fun x ↦ mul_nonneg (show 0 ≤ D by dsimp [D]; positivity) (polynomialTail_nonneg _ _),
    continuous_const.mul (continuous_polynomialTail n),
    (integrable_polynomialTail_add volume m).const_mul D, ?_, ?_⟩
  · simpa only [mul_left_comm] using (integrable_moment_polynomialTail volume m).const_mul D
  · intro t ht x
    simpa only [pow_zero, one_mul, zero_add, D, polynomialTail] using
      pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := n) (norm_nonneg x)
        (norm_nonneg ((𝓕⁻ (S t)) x)) (by simpa using hb0 t ht x) (by simpa using hbn t ht x)

end Mettapedia.Analysis.CompactFourierEnvelope
