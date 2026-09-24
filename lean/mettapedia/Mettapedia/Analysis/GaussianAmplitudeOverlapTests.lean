import Mettapedia.Analysis.RootPartitionTwoPointEnergy

/-! Normalization, separated centres, and zero-vorticity checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianAmplitudeOverlapTests

open FiniteExponentialWeights GaussianPartitionEnergy RootPartitionEnergy RadialSquareRoot

example (s : Fin 2 → ℝ) : amplitudeOverlap s s = 1 := amplitudeOverlap_self s

/-- The two endpoints favor opposite centres, yet their product is bounded
by the uniform midpoint weight. -/
example : gaussianAmplitude (![-1, 1] : Fin 2 → ℝ) 1 (-1) 0 *
    gaussianAmplitude (![-1, 1] : Fin 2 → ℝ) 1 1 0 ≤ 1 / 2 := by
  have hm : weight (score (![-1, 1] : Fin 2 → ℝ) 1 0) 0 = 1 / 2 := by
    norm_num [weight, partition, score, Fin.sum_univ_two]
    field_simp
    norm_num
  have h := gaussianAmplitude_mul_le_midpoint_weight (![-1, 1] : Fin 2 → ℝ) 1 (-1) 1 0
  norm_num at h
  exact h.trans_eq hm

example {ι F : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (center : ι → F) (tau : ℝ) (x : F) :
    twoPointDistanceMoment center tau x x = 3 * distanceMoment center tau x := by
  have hx : (1 / 2 : ℝ) • (x + x) = x := by module
  rw [twoPointDistanceMoment, hx, sub_self, norm_zero]
  ring

example : twoPointDistanceMoment (![-1, 1] : Fin 2 → ℝ) 1 (-1) 1 ≤ 4 + 3 * Real.log 2 := by
  have h := twoPointDistanceMoment_le (![-1, 1] : Fin 2 → ℝ) 1 (by norm_num) (-1) 1 0
  norm_num at h
  exact h

/-- No division by the differentiated vorticity norm is needed at its zero. -/
example {ι E F : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (center : ι → F) (tau : ℝ) {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F}
    {w : ℝ → E} {wd : E} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (hw : HasDerivAt w wd t)
    (hzero : w t = 0) (bz : ℝ) (z : F) (wz : E) :
    ‖wz‖ ^ 2 * (∑ i, (rootAmplitude center tau bz z i * Real.sqrt ‖wz‖) ^ 2 *
      ‖deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i • radialSqrt (w s)) t‖ ^ 2) = 0 := by
  have h := sum_twoPoint_rootVorticity_deriv_sq_le center tau hb hx hw bz z wz
  simp only [hzero, norm_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_mul, add_zero] at h
  exact le_antisymm h (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))))

end Mettapedia.Analysis.GaussianAmplitudeOverlapTests
