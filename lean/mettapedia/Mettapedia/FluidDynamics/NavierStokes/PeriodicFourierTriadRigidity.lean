import Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierTriad

/-!
# A sharp no-go test for static Fourier-flux rigidity

This module tests the weakest natural amplitude-independent coercive estimate
suggested by the exact triad calculation: can viscosity control the instantaneous
outward flux through a fixed Fourier cutoff by the quadratic dissipation on the
receiving modes, uniformly over real divergence-free trigonometric polynomials?

The answer is no.  The convection flux is cubic under amplitude scaling, whereas
the viscous quadratic form is quadratic.  The exact six-mode field from
`PeriodicFourierTriad` has strictly positive outward flux, so its real amplitude
multiples give an explicit counterexample at every positive viscosity and every
finite nonnegative proposed constant.  This rules out this *static pointwise*
rigidity mechanism; it does not rule out time-integrated, scale-dependent, or
critical-norm cascade controls.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PeriodicFourierTriad

open scoped BigOperators ComplexConjugate

@[simp] private theorem int010_third :
    (![(0 : ℤ), 1, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

@[simp] private theorem int0Neg10_third :
    (![(0 : ℤ), -1, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

/-- Real amplitude scaling of a Fourier velocity field. -/
def realScale (lambda : ℝ) (u : FourierVelocity) : FourierVelocity :=
  fun m i => (lambda : ℂ) * u m i

/-- Real scaling preserves exact Fourier support. -/
theorem realScale_eq_zero_of_eq_zero
    (lambda : ℝ) (u : FourierVelocity) (m : Wavevector)
    (hu : u m = 0) :
    realScale lambda u m = 0 := by
  ext i
  simp [realScale, hu]

/-- Real scaling preserves conjugate symmetry. -/
theorem realScale_reality
    (lambda : ℝ) (u : FourierVelocity)
    (hu : ∀ m, u (-m) = fun i => conj (u m i)) (m : Wavevector) :
    realScale lambda u (-m) = fun i => conj (realScale lambda u m i) := by
  ext i
  rw [realScale, realScale, hu m]
  simp

/-- Real scaling preserves the divergence-free Fourier constraint. -/
theorem modeDot_realScale
    (lambda : ℝ) (u : FourierVelocity) (m : Wavevector) :
    modeDot m (realScale lambda u m) =
      (lambda : ℂ) * modeDot m (u m) := by
  unfold modeDot realScale
  calc
    (∑ i : Fin 3, (m i : ℂ) * ((lambda : ℂ) * u m i)) =
        ∑ i : Fin 3, (lambda : ℂ) * ((m i : ℂ) * u m i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (lambda : ℂ) * ∑ i : Fin 3, (m i : ℂ) * u m i := by
      rw [Finset.mul_sum]

/-- The exact triad's cutoff flux is cubic in its real amplitude. -/
theorem realScale_triad_cutoffFlux (lambda : ℝ) :
    outwardFlux triadSupport (lowModes triadSupport 1)
      (realScale lambda triadVelocity) = 4 * lambda ^ 3 := by
  rw [triad_lowModes_one]
  norm_num [outwardFlux, nonlinearEnergyRate, coefficientHermitian,
    projectedNonlinearity, convectionConvolution, orderedConvection,
    lerayMode, modeSquare, modeDot, realScale,
    triadSupport, triadVelocity, p, q, k, a, b, c,
    Fin.sum_univ_succ, Complex.I_mul_I]
  ring_nf

/-- The exact triad's high-mode viscous form is quadratic in amplitude. -/
theorem realScale_triad_high_viscousQuadratic (lambda : ℝ) :
    viscousQuadratic {k, -k} (realScale lambda triadVelocity) =
      8 * lambda ^ 2 := by
  norm_num [viscousQuadratic, coefficientEnergy, modeSquareNat, realScale,
    triadVelocity, p, q, k, c, Fin.sum_univ_succ, Complex.normSq_apply]
  ring

/-- The proposed weakest static rigidity statement on the exact support: a
single amplitude-independent constant makes viscosity dominate every positive
instantaneous cutoff flux among supported, real, divergence-free fields.

The support is a genuine closed subset of `ℤ³`; quantifying over fields on this
support is therefore quantifying over exact trigonometric polynomials, not over
an unrelated coefficient ODE. -/
def PointwiseViscousFluxRigidity (C nu : ℝ) : Prop :=
  ∀ u : FourierVelocity,
    (∀ m, m ∉ triadSupport → u m = 0) →
    (∀ m, u (-m) = fun i => conj (u m i)) →
    (∀ m ∈ triadSupport, modeDot m (u m) = 0) →
    outwardFlux triadSupport (lowModes triadSupport 1) u ≤
      C * nu * viscousQuadratic {k, -k} u

/-- Every real amplitude multiple of the witness remains an admissible exact
trigonometric polynomial for `PointwiseViscousFluxRigidity`. -/
theorem realScale_triad_admissible (lambda : ℝ) :
    (∀ m, m ∉ triadSupport → realScale lambda triadVelocity m = 0) ∧
    (∀ m, realScale lambda triadVelocity (-m) =
      fun i => conj (realScale lambda triadVelocity m i)) ∧
    (∀ m ∈ triadSupport,
      modeDot m (realScale lambda triadVelocity m) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    exact realScale_eq_zero_of_eq_zero lambda triadVelocity m
      (triadVelocity_eq_zero_of_not_mem hm)
  · exact realScale_reality lambda triadVelocity triadVelocity_reality
  · intro m hm
    rw [modeDot_realScale, triadVelocity_divergenceFree hm, mul_zero]

/-- **No-go verdict.** At every positive viscosity, no finite nonnegative
amplitude-independent constant can establish the proposed static pointwise
viscous control of cutoff flux, even on one exact closed Fourier triad. -/
theorem no_pointwiseViscousFluxRigidity
    (C nu : ℝ) (hC : 0 ≤ C) (hnu : 0 < nu) :
    ¬ PointwiseViscousFluxRigidity C nu := by
  intro hrigid
  let lambda : ℝ := 2 * C * nu + 1
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  obtain ⟨hsupport, hreality, hdiv⟩ := realScale_triad_admissible lambda
  have hbound := hrigid (realScale lambda triadVelocity)
    hsupport hreality hdiv
  rw [realScale_triad_cutoffFlux,
    realScale_triad_high_viscousQuadratic] at hbound
  have hscale : 2 * C * nu < lambda := by
    dsimp [lambda]
    linarith
  nlinarith [sq_pos_of_pos hlambda]

end PeriodicFourierTriad
end NavierStokes
end FluidDynamics
end Mettapedia
