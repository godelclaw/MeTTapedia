import Mettapedia.Analysis.AnnularRieszDecay
import Mettapedia.Analysis.SchwartzDyadicDecay

/-! Dimension-sharp, cutoff-independent singularity bound for the actual annular Riesz kernels. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AnnularRieszKernel

open SchwartzDyadicDecay
open scoped SchwartzMap

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def singularityBound (i j : Fin d) : ℝ := dimensionBound (kernel i j)

theorem singularityBound_nonneg (i j : Fin d) : 0 ≤ singularityBound i j :=
  dimensionBound_nonneg _

theorem dimension_pow_mul_norm_partialKernel_le (i j : Fin d) (N : ℕ) (x : Rd) :
    ‖x‖ ^ d * ‖partialKernel i j N x‖ ≤ singularityBound i j := by
  have hd : 0 < Module.finrank ℝ Rd := by
    rw [finrank_euclideanSpace_fin]
    exact Nat.zero_lt_of_lt i.isLt
  have h := pow_mul_norm_sum_dilate_le (kernel i j) hd (1 / 2) (by norm_num) N x
  simpa only [finrank_euclideanSpace_fin, singularityBound, partialKernel,
    sum_apply, dyadicKernel, scale, div_eq_mul_inv, one_mul] using h

end Mettapedia.Analysis.AnnularRieszKernel
