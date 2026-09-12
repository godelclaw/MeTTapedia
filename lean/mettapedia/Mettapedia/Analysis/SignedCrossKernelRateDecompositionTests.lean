import Mettapedia.Analysis.SignedCrossKernelRateDecomposition
import Mettapedia.Analysis.SignedCrossKernelEvolutionTests

/-!
# Channel tests for the signed material rate

Simultaneous radial decay need not decrease a signed source. The explicit
algebraic test below does not assert a self-consistent NS solution or a
failure of an integrated diffusion estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernelRateDecompositionTests

open SignedCrossKernel SignedCrossKernelEvolutionTests

theorem negative_kernel_source : pairedStretch 6 (-H) a b = -144 / 125 := by
  simp only [pairedStretch, neg_apply, inner_neg_right]
  change -(pairedStretch 6 H a b) = _
  rw [source_value]
  ring

theorem radial_decay_rate_positive :
    highAmplitudeEndpointRate 2 (1 / 2) (-H) a b (-a) (-b) = 144 / 25 := by
  have he := pairedEndpointRate_smul 2 (-H) (-1) a b a b
  simp only [neg_one_smul, pairedEndpointRate_self] at he
  have hw : highAmplitudeWeightRate (1 / 2) a b (-a) (-b) = -1 / 2 := by
    norm_num [highAmplitudeWeightRate, endpoint_norms.1, endpoint_norms.2]
  rw [highAmplitudeEndpointRate, hw, he]
  norm_num [lowAmplitudeWeight, endpoint_norms.1, endpoint_norms.2, negative_kernel_source]

end Mettapedia.Analysis.SignedCrossKernelRateDecompositionTests
