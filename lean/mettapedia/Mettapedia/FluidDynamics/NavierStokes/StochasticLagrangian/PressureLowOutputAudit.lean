import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputKernel

/-! Boundary, non-vacuity, and ratio-uniformity regressions for pressure kernels. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputAudit

open Mettapedia.Analysis.SmoothAnnulus Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCoordinates PressureLowOutputCutoff PressureLowOutputSymbol
open PressureLowOutputKernel
open scoped RealInnerProductSpace FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

private def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a, b, c]

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- The cutoff retains the full target annuli, including the largest small ratio. -/
example (k q : R3) (hk0 : 1 ≤ ‖k‖) (hk1 : ‖k‖ ≤ 2)
    (hq0 : 1 ≤ ‖q‖) (hq1 : ‖q‖ ≤ 2) :
    retained (1 / 2) (k, q) = 1 ∧ ratio (1 / 2) = 1 / 256 := by
  constructor
  · rw [retained, parameterCutoff_eq_one (1 / 2) (by constructor <;> norm_num)]
    simp [cutoff_eq_one k hk0 hk1, cutoff_eq_one q hq0 hq1]
  · norm_num [ratio]

/-- Exactly cancelling frequencies are included in the factorization. -/
example (e k q w v : R3) :
    CoherentPressurePair.tiltPair e k ((0 : ℝ) • q - k) w v = 0 := by
  rw [tiltPair_eq_lowOutput]
  simp

/-- Receiver collisions outside the retained support do not create a singular denominator. -/
example : receiverDenominator 0 (0, 0) = 1 := by
  simp [receiverDenominator, receiver, jointBuffer, buffer_zero]

/-- The normalized limiting symbol is nonzero even though the retained zero-ratio kernel vanishes. -/
example : entry 0 (vec3 1 0 0) (vec3 0 0 1) (vec3 0 0 1) 1
    (vec3 1 0 0, vec3 1 1 0) = -1 / 2 := by
  have hk : ‖vec3 1 0 0‖ = 1 := by
    have h := norm_vec3_sq 1 0 0
    nlinarith [norm_nonneg (vec3 1 0 0)]
  have hq0 : 1 ≤ ‖vec3 1 1 0‖ := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hq1 : ‖vec3 1 1 0‖ ≤ 2 := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hck := cutoff_eq_one (vec3 1 0 0) (by rw [hk]) (by rw [hk]; norm_num)
  have hcq := cutoff_eq_one (vec3 1 1 0) hq0 hq1
  have hr : retained 0 (vec3 1 0 0, vec3 1 1 0) = 1 := by
    simp [retained, hck, hcq, parameterCutoff_eq_one 0 (by constructor <;> norm_num)]
  have hd := receiverDenominator_eq_of_retained_ne_zero 0
    (vec3 1 0 0, vec3 1 1 0) (by rw [hr]; norm_num)
  simp only [entry, hr, one_mul, hd,
    denominator_eq_norm_sq _ (by rw [hck]; norm_num),
    denominator_eq_norm_sq _ (by rw [hcq]; norm_num)]
  norm_num [receiver, ratio, cross, cross_apply, vec3, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The inverse-transform construction has the actual retained pressure as its Fourier transform. -/
example (t : ℝ) (e w v : R3) (i : Fin 3) (x : E6) :
    (𝓕 (retainedKernel (t, e) w v i)) x =
      ((retained t (pairEquiv x) * CoherentPressurePair.tiltPair e
        (pairEquiv x).1 (receiver t (pairEquiv x)) w v i : ℝ) : ℂ) :=
  fourier_retainedKernel (t, e) w v i x

/-- The uniform first-moment bound includes every coordinate entry. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
    ∀ i j l : Fin 3,
    (∫ x : E6, ‖x‖ * ‖retainedKernel (t, e)
      (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t) ^ 2 * C := by
  simpa using exists_uniform_basis_moment 1

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.isCompact_parameterSet
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.mem_parameterSet
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.fourier_kernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.exists_uniform_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.exists_uniform_mass_and_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.fourier_retainedKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.moment_retainedKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.exists_uniform_retained_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.retainedKernel_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel.exists_uniform_basis_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.entry_eq_pressure
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.contDiff_entry
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.tsupport_entry_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.symbol_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.contDiff_symbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.isCompact_commonSupport
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol.tsupport_symbol_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates.tracePair_eq_lowOutput
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates.tiltSymbol_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates.tiltPair_eq_lowOutput
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.parameterBuffer_eq_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.parameterCutoff_eq_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.jointBuffer_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.jointBuffer_le_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.receiver_ne_zero_of_jointBuffer_ne_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.receiverDenominator_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.buffers_eq_one_of_retained_ne_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.receiverDenominator_eq_of_retained_ne_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.contDiff_receiver
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.contDiff_retained
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.contDiff_jointBuffer
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.contDiff_receiverDenominator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff.tsupport_retained_subset
