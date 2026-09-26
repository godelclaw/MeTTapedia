import NavierStokes.PrimaryPulseBounds

/-!
# The seeds of the pulses in the forced breakdown are smaller than every power

In the breakdown construction for the forced problem, each primary pulse is
the solution of a linear amplitude equation started, at the beginning of its
slot `[0, L]`, from the seed `P(0) e₁`. Here `P` is the reference envelope
`exp ∫_{L/2}^v rate`, normalized to one at the midpoint of the slot. Its rate
`λ/√(1+s²) - λ(1+s²)/(1+u²)^{3/2}` is a coupling proportional to the sine of the
angle between the pulse wavevector `(1, s)` and the shear gradient, minus a
viscous damping proportional to `1 + s²`, and the tilt `s` grows linearly
through the slot.

The imported Gaussian bounds of the envelope give, at the start of the slot,

```text
exp(-u·maxSlope·L/8) ≤ P(0) ≤ exp(-u·minSlope·L/8),
```

so the pulse is amplified from its seed to its midpoint by at least
`exp(u·minSlope·L/8)`. Once the slot length exceeds a multiple of
`log(1/Q)`, the seed is below `Q^N`: the construction's slots have length of
order `log²(1/Q)` in a band of scale `Q`, so its seeds are smaller than every
power of the band scale. The imported construction is used as proved; nothing
in it is reimplemented.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.OpenAIPulseSeeds

open Set
open _root_.NavierStokes.PrimaryPulseBounds _root_.NavierStokes.GaussianEnvelope

/-- **The seed of a pulse is a Gaussian tail.** -/
theorem seed_bounds {lam u L : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) :
    Real.exp (-(u * referenceMaxSlope lam u) * L / 8) ≤ referenceP lam u L 0 ∧
      referenceP lam u L 0 ≤ Real.exp (-(u * referenceMinSlope lam u) * L / 8) := by
  have h := reference_gaussian_bounds hlam hu hL (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
  have e1 : -(u * referenceMaxSlope lam u) * (0 - L / 2) ^ 2 / (2 * L) =
      -(u * referenceMaxSlope lam u) * L / 8 := by
    field_simp
    ring
  have e2 : -(u * referenceMinSlope lam u) * (0 - L / 2) ^ 2 / (2 * L) =
      -(u * referenceMinSlope lam u) * L / 8 := by
    field_simp
    ring
  rw [e1, e2] at h
  exact h

/-- The envelope equals one at the midpoint of the slot. -/
theorem referenceP_midpoint (lam u L : ℝ) : referenceP lam u L (L / 2) = 1 := by
  simp [referenceP, envelope]

/-- **The amplification from seed to midpoint is exponential in the slot
length.** -/
theorem amplification_ge {lam u L : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) :
    Real.exp (u * referenceMinSlope lam u * L / 8) ≤
      referenceP lam u L (L / 2) / referenceP lam u L 0 := by
  rw [referenceP_midpoint, le_div_iff₀ (referenceP_pos lam u L 0)]
  have h := (seed_bounds hlam hu hL).2
  calc Real.exp (u * referenceMinSlope lam u * L / 8) * referenceP lam u L 0
      ≤ Real.exp (u * referenceMinSlope lam u * L / 8) *
          Real.exp (-(u * referenceMinSlope lam u) * L / 8) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by
        rw [← Real.exp_add]
        simp only [neg_mul, neg_div, add_neg_cancel, Real.exp_zero]

/-- **Seeds below every power of the scale.** For a scale `0 < Q < 1` and an
exponent `N ≥ 0`, once the slot length is at least
`8 N log(1/Q) / (u·minSlope)` the seed is at most `Q^N`. -/
theorem seed_le_rpow {lam u L Q N : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L)
    (hQ0 : 0 < Q) (hL' : 8 * N * Real.log (1 / Q) / (u * referenceMinSlope lam u) ≤ L) :
    referenceP lam u L 0 ≤ Q ^ N := by
  have hm : 0 < u * referenceMinSlope lam u := mul_pos hu (referenceMinSlope_pos hlam hu)
  refine (seed_bounds hlam hu hL).2.trans ?_
  rw [Real.rpow_def_of_pos hQ0]
  apply Real.exp_le_exp.mpr
  rw [div_le_iff₀ hm] at hL'
  have hlog : Real.log (1 / Q) = -Real.log Q := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hL'
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.OpenAIPulseSeeds
