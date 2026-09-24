import Mettapedia.Analysis.SignedCrossKernelCurvature
import Mettapedia.Analysis.SignedCrossKernelEvolutionTests

/-! # Exact homogeneity check of the paired-source curvature -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernelCurvatureTests

open SignedCrossKernel SignedCrossKernelEvolutionTests RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem curvature_radial_value : pairedCurvature 1 H a b a b = 10368 / 125 := by
  have h₁ (v : R3) (hv : ‖v‖ = 1) : evenRadialRate 2 v v = (7 : ℝ) • v := by
    norm_num [evenRadialRate, hv]
    module
  have h₂ (v : R3) (hv : ‖v‖ = 1) : evenRadialCurvature 1 v v = (42 : ℝ) • v := by
    norm_num [evenRadialCurvature, hv]
    module
  have he : pairedCurvature 1 H a b a b = 72 * pairedStretch 6 H a b := by
    simp only [pairedCurvature, h₁ a endpoint_norms.1, h₁ b endpoint_norms.2,
      h₂ a endpoint_norms.1, h₂ b endpoint_norms.2, pairedStretch,
      radialPower, endpoint_norms.1, endpoint_norms.2, one_pow, one_smul,
      ← smul_sub, map_smul, real_inner_smul_right, inner_add_left]
    ring
  rw [he, source_value]
  norm_num

end Mettapedia.Analysis.SignedCrossKernelCurvatureTests
