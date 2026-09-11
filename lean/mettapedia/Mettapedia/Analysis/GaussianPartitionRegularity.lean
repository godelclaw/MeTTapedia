import Mettapedia.Analysis.NormScaledGaussianPartition
import Mettapedia.Analysis.LocallyLipschitz

/-!
# Regularity of Gaussian square partitions

The normalized factors are smooth; multiplying by the norm gives locally
Lipschitz amplitudes, including at zero. This regularity is separate from
the estimates for Lean's total derivative at zero-amplitude points.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionEnergy

open FiniteExponentialWeights
open scoped ContDiff

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

theorem contDiff_gaussianAmplitude (center : ι → E) (tau : ℝ) (i : ι) (n : ℕ∞ω) :
    ContDiff ℝ n (fun x ↦ gaussianAmplitude center tau x i) := by
  have hs (j : ι) : ContDiff ℝ n (fun x ↦ score center tau x j) :=
    (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).neg).div_const tau
  have hZ : ContDiff ℝ n (fun x ↦ partition (score center tau x)) :=
    ContDiff.sum (fun j _ ↦ (hs j).exp)
  exact ((hs i).div_const 2).exp.div
    (hZ.sqrt (fun _ ↦ ne_of_gt (partition_pos _)))
    (fun _ ↦ ne_of_gt (Real.sqrt_pos.mpr (partition_pos _)))

theorem locallyLipschitz_normScaledAmplitude (center : ι → E) (tau : ℝ) (i : ι) :
    LocallyLipschitz (fun x ↦ normScaledAmplitude center tau x i) :=
  lipschitzWith_one_norm.locallyLipschitz.mul_algebra
    (contDiff_gaussianAmplitude center tau i 1).locallyLipschitz

end Mettapedia.Analysis.GaussianPartitionEnergy
