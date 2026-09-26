import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierShearAlignment

/-!
# Seed kinematics in a shear: tilted debris seeds only debris, except by echoes

A disturbance carried by a shear is amplified around the moment its
wavevector crosses the direction orthogonal to the flow, and it decays once
the shear has tilted it past that moment. On the lattice of the periodic
shearing box, a mode `k` with streamwise component `k₀ ≠ 0` crosses at the
shear count

```text
τ(k) = k₁ / k₀,
```

and `n` shear periods lower it by `n`: `τ(Aₙ k) = τ(k) - n`. A mode with
`τ(k) ≤ 0` has passed its amplification window: it is debris.

The nonlinearity creates the mode `p + r` from the modes `p` and `r`, and the
crossing count of the product is the barycentre of the inputs' crossing
counts, weighted by their streamwise components:

```text
τ(p + r) = (p₀ τ(p) + r₀ τ(r)) / (p₀ + r₀).
```

When `p₀` and `r₀` have the same sign the weights are positive, so the product
crosses no later than the later input. Debris combined with debris gives
debris. Only an echo, a pair with streamwise components of opposite signs,
can extrapolate to a fresh mode that is still to cross, and an echo of two
pieces of debris has opposite cross-stream components, so the fresh mode is
no finer along the shear gradient than the finer input: debris cannot seed
finer amplifiable structure along the gradient. By the shear alignment, after `n` shear periods such a pair has an angle whose sine is at
most `8 |p × r| / |n|`, so by the sine law its coupling falls like `1 / |n|`.
The unforced flow can therefore seed a new amplification only through echoes
of debris that the shear keeps silencing.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSeedKinematics

open PeriodicFourierTriad FourierShearAlignment

/-- The shear count at which the mode `k` crosses the direction orthogonal to
the flow. -/
def crossing (k : Wavevector) : ℝ := (k 1 : ℝ) / (k 0 : ℝ)

/-- **Shearing lowers the crossing count by the number of periods.** -/
theorem crossing_shearMap (n : ℤ) {k : Wavevector} (hk : k 0 ≠ 0) :
    crossing (shearMap n k) = crossing k - n := by
  have hk' : (k 0 : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold crossing
  simp only [shearMap, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_sub, Int.cast_mul]
  field_simp

/-- A mode and its conjugate partner cross together. -/
theorem crossing_neg (k : Wavevector) : crossing (-k) = crossing k := by
  unfold crossing
  simp only [Pi.neg_apply, Int.cast_neg]
  rw [neg_div_neg_eq]

/-- **The crossing count of a product is the barycentre of the inputs'.** -/
theorem crossing_add {p r : Wavevector} (hp : p 0 ≠ 0) (hr : r 0 ≠ 0) :
    crossing (p + r) =
      ((p 0 : ℝ) * crossing p + (r 0 : ℝ) * crossing r) / ((p 0 : ℝ) + (r 0 : ℝ)) := by
  have hp' : (p 0 : ℝ) ≠ 0 := by exact_mod_cast hp
  have hr' : (r 0 : ℝ) ≠ 0 := by exact_mod_cast hr
  unfold crossing
  simp only [Pi.add_apply, Int.cast_add]
  congr 1
  field_simp

/-- **Debris seeds only debris.** Two modes whose streamwise components have
the same sign and which both cross no later than `T` produce a mode that
crosses no later than `T`. -/
theorem crossing_add_le {p r : Wavevector} (hs : 0 < p 0 * r 0) {T : ℝ}
    (hpT : crossing p ≤ T) (hrT : crossing r ≤ T) : crossing (p + r) ≤ T := by
  have hp : p 0 ≠ 0 := fun h ↦ by simp [h] at hs
  have hr : r 0 ≠ 0 := fun h ↦ by simp [h] at hs
  have hs' : (0 : ℝ) < (p 0 : ℝ) * (r 0 : ℝ) := by exact_mod_cast hs
  rcases lt_or_gt_of_ne (show (p 0 : ℝ) ≠ 0 by exact_mod_cast hp) with hneg | hpos
  · -- both components negative
    have hrneg : (r 0 : ℝ) < 0 := by
      by_contra h
      push Not at h
      nlinarith
    have hsum : (p 0 : ℝ) + (r 0 : ℝ) < 0 := by linarith
    rw [crossing_add hp hr, div_le_iff_of_neg hsum]
    nlinarith
  · have hrpos : (0 : ℝ) < (r 0 : ℝ) := by
      by_contra h
      push Not at h
      nlinarith
    have hsum : (0 : ℝ) < (p 0 : ℝ) + (r 0 : ℝ) := by linarith
    rw [crossing_add hp hr, div_le_iff₀ hsum]
    nlinarith

theorem abs_add_le_max_of_mul_nonpos {a b : ℝ} (h : a * b ≤ 0) : |a + b| ≤ max |a| |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · have h0 : a * b = 0 := le_antisymm h (mul_nonneg ha hb)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rw [h1, zero_add]
      exact le_max_right _ _
    · rw [h1, add_zero]
      exact le_max_left _ _
  · have h1 : a ≤ max |a| |b| := (le_abs_self a).trans (le_max_left _ _)
    have h2 : -b ≤ max |a| |b| := (neg_le_abs b).trans (le_max_right _ _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h1 : -a ≤ max |a| |b| := (neg_le_abs a).trans (le_max_left _ _)
    have h2 : b ≤ max |a| |b| := (le_abs_self b).trans (le_max_right _ _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h0 : a * b = 0 := le_antisymm h (mul_nonneg_of_nonpos_of_nonpos ha hb)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rw [h1, zero_add]
      exact le_max_right _ _
    · rw [h1, add_zero]
      exact le_max_left _ _

/-- **Fresh seeds from debris are coarser along the shear gradient.** If two
modes have both passed their crossing and their product is still to cross,
the product's cross-stream component is at most the larger of the inputs'. -/
theorem fresh_of_debris_coarser {p r : Wavevector} (hp : p 0 ≠ 0) (hr : r 0 ≠ 0)
    (hτp : crossing p ≤ 0) (hτr : crossing r ≤ 0) (hfresh : 0 < crossing (p + r)) :
    |(((p + r) 1 : ℤ) : ℝ)| ≤ max |(p 1 : ℝ)| |(r 1 : ℝ)| := by
  have hs : p 0 * r 0 < 0 := by
    rcases lt_trichotomy (p 0 * r 0) 0 with h | h | h
    · exact h
    · exact absurd h (mul_ne_zero hp hr)
    · have := crossing_add_le h hτp hτr
      linarith
  have hs' : (p 0 : ℝ) * (r 0 : ℝ) < 0 := by exact_mod_cast hs
  have hp' : (p 0 : ℝ) ≠ 0 := by exact_mod_cast hp
  have hr' : (r 0 : ℝ) ≠ 0 := by exact_mod_cast hr
  have hp1 : (p 1 : ℝ) = (p 0 : ℝ) * crossing p := by
    unfold crossing
    field_simp
  have hr1 : (r 1 : ℝ) = (r 0 : ℝ) * crossing r := by
    unfold crossing
    field_simp
  have h2 : 0 ≤ crossing p * crossing r := mul_nonneg_of_nonpos_of_nonpos hτp hτr
  have hmul : (p 1 : ℝ) * (r 1 : ℝ) ≤ 0 := by
    rw [hp1, hr1]
    nlinarith
  have e : (((p + r) 1 : ℤ) : ℝ) = (p 1 : ℝ) + (r 1 : ℝ) := by
    simp only [Pi.add_apply, Int.cast_add]
  rw [e]
  exact abs_add_le_max_of_mul_nonpos hmul

/-- **Echoes can extrapolate.** Two pieces of debris, crossing at `-1/3` and
`-1`, combine through an echo into a mode that crosses at `1`, still to be
amplified. -/
theorem exists_echo : ∃ p r : Wavevector, crossing p ≤ 0 ∧ crossing r ≤ 0 ∧
    0 < crossing (p - r) := by
  refine ⟨![3, -1, 0], ![2, -2, 0], ?_, ?_, ?_⟩ <;>
    norm_num [crossing]

end Mettapedia.FluidDynamics.NavierStokes.FourierSeedKinematics
