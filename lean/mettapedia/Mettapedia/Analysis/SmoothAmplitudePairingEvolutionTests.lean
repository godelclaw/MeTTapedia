import Mettapedia.Analysis.SmoothAmplitudePairingEvolution
import Mettapedia.Analysis.SignedCrossKernelCurvatureSignTests

/-!
# Signed curvature survives smooth amplitude retention

Positive rank-one kernels still give either curvature sign at equal
endpoint values with different gradients. These algebraic examples are
not self-consistent vorticity fields or claims about their spatial means.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudePairingEvolutionTests

open SmoothAmplitudePairing SmoothAmplitudeCutoff SignedCrossKernelCurvatureSignTests

theorem retained_curvature_value (c : ℝ) :
    retainedPairCurvature 1 1 (kernel c) direction direction increment 0 = -c / 2 := by
  rw [retainedPairCurvature_same_value, curvature_value]
  norm_num [pairWeight, retainedWeight, direction_norm]
  ring

theorem retained_curvature_both_signs :
    retainedPairCurvature 1 1 (kernel 1) direction direction increment 0 < 0 ∧
      0 < retainedPairCurvature 1 1 (kernel (-1)) direction direction increment 0 := by
  rw [retained_curvature_value, retained_curvature_value]
  norm_num

theorem hasDerivAt_retainedRate_test (c : ℝ) :
    HasDerivAt (fun t : ℝ ↦ retainedEndpointRate 2 1 (kernel c)
      (direction + t • increment) direction increment 0) (-c / 2) 0 := by
  have ha : HasDerivAt (fun t : ℝ ↦ direction + t • increment) increment 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const increment).const_add direction
  have h := hasDerivAt_retainedEndpointRate 1 1 (by norm_num) (kernel c) ha
    (hasDerivAt_const 0 direction) (hasDerivAt_const 0 increment) (hasDerivAt_const 0 (0 : EuclideanSpace ℝ (Fin 3)))
  simp only [zero_smul, add_zero, retained_curvature_value] at h
  apply h.congr_deriv
  simp [retainedEndpointRate, pairRate, retainedRate, SignedCrossKernel.pairedEndpointRate,
    RadialPower.evenRadialRate]

end Mettapedia.Analysis.SmoothAmplitudePairingEvolutionTests
