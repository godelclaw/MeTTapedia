import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairConvolution

/-! Cancelling-frequency and hypothesis-sensitivity tests for real pressure pairs. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignmentAudit

open scoped RealInnerProductSpace
open Mettapedia.Analysis.EuclideanCrossProduct
open PancakeAnisotropyDepletion PressureTiltSymbol CoherentPressurePair PressurePairMisalignment
open PressurePairConvolution FourierPressureCommutator

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def vec3 (a b c : ℝ) : E3 := WithLp.toLp 2 ![a, b, c]

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

@[simp] private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

example (e k w v : E3) : tiltPair e k (-k) w v = 0 := by
  simp [tiltPair, tiltSymbol_zero]

example (e p w v : E3) : tiltPair e 0 p w v = 0 := by
  simp [tiltPair, tracePair]

/-- The output angle remains 45 degrees at every input scale. -/
example (n : ℝ) :
    tiltSymbol (vec3 0 0 1) (vec3 n 0 1 + vec3 (-n) 1 0) = vec3 0 (1 / 2) 0 := by
  ext j
  fin_cases j <;> norm_num [tiltSymbol, lineRemainder, vec3, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- Nevertheless the coherent pressure pair decays quadratically with n. -/
example (n : ℝ) :
    tiltPair (vec3 0 0 1) (vec3 n 0 1) (vec3 (-n) 1 0) (vec3 0 0 1) (vec3 0 0 1) =
      vec3 0 (-n ^ 2 / (2 * (n ^ 2 + 1) ^ 2)) 0 := by
  ext j
  fin_cases j <;> norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply,
    vec3, EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  field_simp

/-- Perfect alignment alone is insufficient: this first input is not divergence-free. -/
example :
    lineRemainder (vec3 0 0 1) (vec3 0 0 1) = 0 ∧
      ⟪vec3 1 0 1, vec3 0 0 1⟫ = 1 ∧
      tiltPair (vec3 0 0 1) (vec3 1 0 1) (vec3 (-1) 1 0) (vec3 0 0 1) (vec3 0 0 1) ≠ 0 := by
  constructor
  · ext j
    fin_cases j <;> norm_num [lineRemainder, vec3, PiLp.inner_apply, RCLike.inner_apply,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  constructor
  · norm_num [vec3, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  · intro h
    have hj := congrArg (fun v : E3 ↦ v 1) h
    norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply, vec3,
      EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three] at hj

/-- A genuinely divergence-free pair has the explicit nonzero transverse output. -/
example :
    ⟪vec3 1 0 1, vec3 (-1) 0 1⟫ = 0 ∧
      ⟪vec3 (-1) 1 0, vec3 0 0 1⟫ = 0 ∧
      tiltPair (vec3 0 0 1) (vec3 1 0 1) (vec3 (-1) 1 0) (vec3 (-1) 0 1) (vec3 0 0 1) =
        vec3 0 (-1 / 4) 0 := by
  constructor
  · norm_num [vec3, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  constructor
  · norm_num [vec3, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  · ext j
    fin_cases j <;> norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply,
      vec3, EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The localization defect charges a longitudinal mode even with perfect direction alignment. -/
example : localizationDefect (vec3 0 0 1) ![0, 0, 1] (vec3 0 0 1) = 1 / 2 := by
  have he : ‖vec3 0 0 1‖ = 1 := by
    have h := norm_vec3_sq 0 0 1
    nlinarith only [h, norm_nonneg (vec3 0 0 1)]
  have hk : realFrequency ![0, 0, 1] = vec3 0 0 1 := by
    ext j
    fin_cases j <;> norm_num [realFrequency, vec3]
  rw [localizationDefect, hk]
  have hz : lineRemainder (vec3 0 0 1) (vec3 0 0 1) = 0 := by
    simp [lineRemainder, he]
  rw [hz, norm_zero, real_inner_self_eq_norm_sq, he]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignmentAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.tracePair_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.tiltPair_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.tracePair_coherent
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.norm_tiltSymbol_mul_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.norm_tiltPair_coherent
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.abs_triple_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.norm_tiltPair_coherent_le_of_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.CoherentPressurePair.norm_tiltPair_coherent_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.abs_tracePair_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.norm_tiltPair_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.tiltPair_add_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.tiltPair_add_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.tiltPair_smul_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.tiltPair_smul_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.longitudinal_mul_amplitude_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.longitudinal_mul_amplitude_le_add_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.tiltPair_decomposition
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.norm_tiltPair_le_misalignment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment.norm_tiltPair_le_misalignment_add_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution.localizationDefect_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution.sum_norm_pairConvolution_sq_le_with_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution.sum_norm_pairConvolution_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution.pairConvolution_eq_zero_of_aligned
