import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierRelaxation

/-!
# Hidden-mode compatibility and signed physical-time history

For a static Fourier filter, the unresolved modes of the existing infinite
coefficient solution have their own unforced equation. Any force ascribed
to the resolved field is exactly the existing, pressure-corrected subgrid
force of the full field. Conversely, matching that force and satisfying the
hidden equation reconstructs the full unforced coefficient equation.

The final identity retains complex phases in the physical-time Duhamel
history, including the hidden initial datum and all nonlinear parents.
It takes no absolute values. These are exact identities, not a bound on
repeated renewal, a construction of hidden modes for prescribed forcing,
or a whole-space embedding of a forced singular solution. No spatial
smoothness beyond the stated coefficient solution class is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredHistory

open Set MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity
open PancakeSobolevFiberEnvelope InfiniteFilteredEquation FourierRelaxation

/-- The complement is retained as a field, rather than replaced by a free load. -/
def hiddenVelocity (chi : Wavevector → ℂ) (u : FourierVelocity) : FourierVelocity :=
  u - filteredVelocity chi u

theorem hiddenVelocity_apply (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) : hiddenVelocity chi u q = (1 - chi q) • u q := by
  ext i
  simp only [hiddenVelocity, filteredVelocity, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Every hidden coefficient obeys the projection of the full unforced RHS.
It cannot be chosen independently to supply a desired resolved forcing. -/
theorem hasDerivAt_hidden_coefficients
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T)
    (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ hiddenVelocity chi (s.coefficients τ) q i)
      ((1 - chi q) * infiniteVelocityRHS nu (s.coefficients t) q i) t := by
  simpa only [hiddenVelocity_apply, Pi.smul_apply, smul_eq_mul] using
    (s.equation t ht q i).const_mul (1 - chi q)

/-- Uniqueness of the derivative forces any claimed resolved load to equal
the genuine all-input subgrid force, including its Leray pressure correction. -/
theorem forcing_eq_subgrid
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3)
    (forcing : ℂ)
    (hf : HasDerivAt (fun τ ↦ filteredVelocity chi (s.coefficients τ) q i)
      (infiniteVelocityRHS nu (filteredVelocity chi (s.coefficients t)) q i + forcing) t) :
    forcing = subgridForce chi (s.coefficients t) q i := by
  have he := hf.unique (hasDerivAt_filtered_coefficients s chi C hchi t ht q i)
  exact add_left_cancel he

/-- A converse at the actual infinite-coefficient equation: the target's
forcing must match the reconstructed subgrid stress, and the complement
must satisfy its own evolution. Neither condition alone supplies a lift. -/
theorem reconstructs_unforced_coefficient
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (v w : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) (i : Fin 3)
    (hfilter : filteredVelocity chi (v t + w t) = v t)
    (hsum : ∀ j, Summable (fun k ↦ outputFiber q (v t + w t) k j))
    (forcing : ℂ)
    (hv : HasDerivAt (fun τ ↦ v τ q i)
      (infiniteVelocityRHS nu (v t) q i + forcing) t)
    (hw : HasDerivAt (fun τ ↦ w τ q i)
      ((1 - chi q) * infiniteVelocityRHS nu (v t + w t) q i) t)
    (hg : forcing = subgridForce chi (v t + w t) q i) :
    HasDerivAt (fun τ ↦ (v τ + w τ) q i)
      (infiniteVelocityRHS nu (v t + w t) q i) t := by
  have he := congrFun
    (filtered_infiniteVelocityRHS chi (v t + w t) C hchi nu q hsum) i
  rw [hfilter] at he
  change chi q * infiniteVelocityRHS nu (v t + w t) q i =
    infiniteVelocityRHS nu (v t) q i + subgridForce chi (v t + w t) q i at he
  apply (hv.add hw).congr_deriv
  rw [hg, ← he]
  ring

section SignedHistory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The signed integrating-factor identity. This is the equality underlying
the existing norm estimate; the source's direction and cancellation remain. -/
theorem exp_weighted_history {f g : ℝ → E} {l H : ℝ}
    (hf : ContinuousOn f (Icc 0 H)) (hg : ContinuousOn g (Icc 0 H))
    (hd : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt f (-(l • f t) + g t) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    Real.exp (l * t) • f t =
      f 0 + ∫ τ in (0 : ℝ)..t, Real.exp (l * τ) • g τ := by
  have hF : ∀ τ ∈ Ioo (0 : ℝ) t, HasDerivAt (fun τ ↦ Real.exp (l * τ) • f τ)
      (Real.exp (l * τ) • g τ) τ := by
    intro τ hτ
    refine ((hasDerivAt_exp_mul l τ).smul
      (hd τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)).congr_deriv ?_
    rw [smul_add, smul_neg, smul_smul]
    abel
  have hec : Continuous (fun τ : ℝ ↦ Real.exp (l * τ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcont : ContinuousOn (fun τ ↦ Real.exp (l * τ) • f τ) (Icc 0 t) :=
    hec.continuousOn.smul (hf.mono (Icc_subset_Icc le_rfl ht.2))
  have hint : IntervalIntegrable (fun τ ↦ Real.exp (l * τ) • g τ) volume 0 t :=
    (hec.continuousOn.smul (hg.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hF hint
  have he' := sub_eq_iff_eq_add.mp he.symm
  simpa only [mul_zero, Real.exp_zero, one_smul, add_comm] using he'

end SignedHistory

/-- All nonlinear parents enter the signed history of an actual coefficient.
The damping is the unit-torus rate `4π²ν|q|²`, not an auxiliary heat clock. -/
theorem mode_history (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (q : Wavevector) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Real.exp (damping nu q * t) • s.coefficients t q = u₀ q +
      ∫ τ in (0 : ℝ)..t, Real.exp (damping nu q * τ) • nonlinear (s.coefficients τ) q := by
  have he := exp_weighted_history
    (continuousOn_pi.mpr fun i ↦ (s.continuous q i).continuousOn)
    (continuousOn_nonlinear s hB q)
    (fun τ hτ ↦ by
      rw [← infiniteVelocityRHS_eq]
      exact hasDerivAt_pi.mpr fun i ↦ s.equation τ hτ q i) ht
  simpa only [s.initial] using he

/-- The unresolved initial data and the generated nonlinear history both
survive elimination. No fresh initial resource is introduced at later times. -/
theorem hidden_mode_history (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (chi : Wavevector → ℂ) (q : Wavevector) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Real.exp (damping nu q * t) • hiddenVelocity chi (s.coefficients t) q =
      hiddenVelocity chi u₀ q + (1 - chi q) •
        (∫ τ in (0 : ℝ)..t, Real.exp (damping nu q * τ) • nonlinear (s.coefficients τ) q) := by
  rw [hiddenVelocity_apply, smul_comm, mode_history s hB q ht, smul_add,
    hiddenVelocity_apply]

end Mettapedia.FluidDynamics.NavierStokes.FilteredHistory
