import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTriadSineLaw

/-!
# Shear alignment: sheared modes become collinear and stop stretching one another

A uniform shear, with velocity along the first coordinate varying along the
second, tilts every wavevector of a disturbance it advects. On the lattice of
the periodic shearing box, `n` shear periods map a wavevector `k` to

```text
Aₙ k = (k₀, k₁ - n k₀, k₂).
```

The cross product of two sheared wavevectors is `(c₀ + n c₁, c₁, c₂)` with
`c = p × r`, so it grows at most linearly in `n`, while a sheared wavevector
with nonzero streamwise component `k₀` grows at least like `|n| |k₀|`. The
sine of the angle between two such modes therefore decays like `1 / |n|`:

```text
sin∠(Aₙ p, Aₙ r) ≤ (1 + |n|) |p × r| / ((|n| |p₀| - |p|) (|n| |r₀| - |r|)),
```

and once `|n| ≥ 2 |p|, 2 |r|` it is at most `8 |p × r| / |n|`. With the triad
sine law, the pair stretching between the sheared modes decays at the same
rate. A shear flattens the disturbance it advects into layers whose normal is
the direction of the shear gradient, and the layers stop stretching one
another. This depletes the disturbances carried by a shear, not the shear
flow that carries them.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierShearAlignment

open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeInfinitePressureCoefficients
open PancakePeriodicVorticityEquation
open FourierTriadSineLaw

/-- `n` periods of the lattice shear. -/
def shearMap (n : ℤ) (k : Wavevector) : Wavevector := ![k 0, k 1 - n * k 0, k 2]

theorem norm_frequencyVec_sq_three (k : Wavevector) :
    ‖frequencyVec k‖ ^ 2 = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2 := by
  rw [norm_frequencyVec_sq, Fin.sum_univ_three]

theorem abs_coord_le_norm (k : Wavevector) (i : Fin 3) : |(k i : ℝ)| ≤ ‖frequencyVec k‖ := by
  have h := norm_frequencyVec_sq_three k
  have hsq : (k i : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ^ 2 := by
    rw [h]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  rw [← sq_abs] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq

/-- The cross product of two sheared wavevectors. -/
theorem wavevectorCross_shearMap (n : ℤ) (p r : Wavevector) :
    wavevectorCross (shearMap n p) (shearMap n r) =
      ![wavevectorCross p r 0 + n * wavevectorCross p r 1, wavevectorCross p r 1,
        wavevectorCross p r 2] := by
  ext i
  fin_cases i <;> simp [wavevectorCross, shearMap] <;> ring

/-- The cross product of sheared wavevectors grows at most linearly. -/
theorem norm_cross_shearMap_le (n : ℤ) (p r : Wavevector) :
    ‖frequencyVec (wavevectorCross (shearMap n p) (shearMap n r))‖ ≤
      (1 + |(n : ℝ)|) * ‖frequencyVec (wavevectorCross p r)‖ := by
  have h1 : ‖frequencyVec (wavevectorCross (shearMap n p) (shearMap n r))‖ ^ 2 =
      ((wavevectorCross p r 0 : ℝ) + (n : ℝ) * (wavevectorCross p r 1 : ℝ)) ^ 2 +
        (wavevectorCross p r 1 : ℝ) ^ 2 + (wavevectorCross p r 2 : ℝ) ^ 2 := by
    rw [norm_frequencyVec_sq_three, wavevectorCross_shearMap]
    simp
  have h2 := norm_frequencyVec_sq_three (wavevectorCross p r)
  set x := (wavevectorCross p r 0 : ℝ) with hx
  set y := (wavevectorCross p r 1 : ℝ) with hy
  set z := (wavevectorCross p r 2 : ℝ) with hz
  set N := |(n : ℝ)| with hN
  have hN0 : 0 ≤ N := abs_nonneg _
  have hny : (n : ℝ) ^ 2 * y ^ 2 = N ^ 2 * y ^ 2 := by rw [hN, sq_abs]
  have f1 : (n : ℝ) * x * y ≤ N * (|x| * |y|) := by
    calc (n : ℝ) * x * y ≤ |(n : ℝ) * x * y| := le_abs_self _
      _ = N * (|x| * |y|) := by rw [abs_mul, abs_mul, mul_assoc]
  have f2 : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have f3 := mul_le_mul_of_nonneg_left f2 hN0
  have hsq : ‖frequencyVec (wavevectorCross (shearMap n p) (shearMap n r))‖ ^ 2 ≤
      ((1 + N) * ‖frequencyVec (wavevectorCross p r)‖) ^ 2 := by
    rw [h1, mul_pow, h2]
    nlinarith [mul_nonneg hN0 (sq_nonneg x), mul_nonneg hN0 (sq_nonneg y),
      mul_nonneg hN0 (sq_nonneg z), mul_nonneg (sq_nonneg N) (sq_nonneg x),
      mul_nonneg (sq_nonneg N) (sq_nonneg z)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- A sheared wavevector grows at least like `|n| |k₀|`. -/
theorem sub_le_norm_shearMap (n : ℤ) (k : Wavevector) :
    |(n : ℝ)| * |(k 0 : ℝ)| - ‖frequencyVec k‖ ≤ ‖frequencyVec (shearMap n k)‖ := by
  have h := abs_coord_le_norm (shearMap n k) 1
  have e : ((shearMap n k 1 : ℤ) : ℝ) = (k 1 : ℝ) - (n : ℝ) * (k 0 : ℝ) := by
    simp [shearMap]
  rw [e] at h
  have h1 := abs_coord_le_norm k 1
  have h2 : |(n : ℝ)| * |(k 0 : ℝ)| ≤ |(k 1 : ℝ) - (n : ℝ) * (k 0 : ℝ)| + |(k 1 : ℝ)| := by
    rw [← abs_mul]
    calc |(n : ℝ) * (k 0 : ℝ)| = |(k 1 : ℝ) - ((k 1 : ℝ) - (n : ℝ) * (k 0 : ℝ))| := by ring_nf
      _ ≤ |(k 1 : ℝ)| + |(k 1 : ℝ) - (n : ℝ) * (k 0 : ℝ)| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

/-- **Sheared modes become collinear.** -/
theorem sine_shearMap_le (n : ℤ) (p r : Wavevector)
    (hp : ‖frequencyVec p‖ < |(n : ℝ)| * |(p 0 : ℝ)|)
    (hr : ‖frequencyVec r‖ < |(n : ℝ)| * |(r 0 : ℝ)|) :
    sine (shearMap n p) (shearMap n r) ≤
      (1 + |(n : ℝ)|) * ‖frequencyVec (wavevectorCross p r)‖ /
        ((|(n : ℝ)| * |(p 0 : ℝ)| - ‖frequencyVec p‖) * (|(n : ℝ)| * |(r 0 : ℝ)| - ‖frequencyVec r‖)) := by
  unfold sine
  have hP := sub_le_norm_shearMap n p
  have hR := sub_le_norm_shearMap n r
  have hP0 : 0 < |(n : ℝ)| * |(p 0 : ℝ)| - ‖frequencyVec p‖ := by linarith
  have hR0 : 0 < |(n : ℝ)| * |(r 0 : ℝ)| - ‖frequencyVec r‖ := by linarith
  exact div_le_div₀ (by positivity) (norm_cross_shearMap_le n p r) (by positivity)
    (mul_le_mul hP hR hR0.le (hP0.le.trans hP))

/-- **The shear arrow: the sine decays like `1 / |n|`.** For modes with nonzero
streamwise components and `|n| ≥ 2 |p|, 2 |r|`, the sine of the angle between
the sheared modes is at most `8 |p × r| / |n|`. -/
theorem sine_shearMap_le_div (n : ℤ) {p r : Wavevector} (hp0 : p 0 ≠ 0) (hr0 : r 0 ≠ 0)
    (hpn : 2 * ‖frequencyVec p‖ ≤ |(n : ℝ)|) (hrn : 2 * ‖frequencyVec r‖ ≤ |(n : ℝ)|) :
    sine (shearMap n p) (shearMap n r) ≤ 8 * ‖frequencyVec (wavevectorCross p r)‖ / |(n : ℝ)| := by
  have hp : p ≠ 0 := fun h ↦ hp0 (by rw [h]; rfl)
  have hr : r ≠ 0 := fun h ↦ hr0 (by rw [h]; rfl)
  have hP := one_le_norm_frequencyVec hp
  have hR := one_le_norm_frequencyVec hr
  have hpa : (1 : ℝ) ≤ |(p 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |p 0| := Int.one_le_abs hp0
    exact_mod_cast this
  have hra : (1 : ℝ) ≤ |(r 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |r 0| := Int.one_le_abs hr0
    exact_mod_cast this
  have hn : 2 ≤ |(n : ℝ)| := by linarith
  have hn0 : 0 < |(n : ℝ)| := by linarith
  have hC := norm_nonneg (frequencyVec (wavevectorCross p r))
  have hP2 : |(n : ℝ)| / 2 ≤ |(n : ℝ)| * |(p 0 : ℝ)| - ‖frequencyVec p‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hpa hn0.le]
  have hR2 : |(n : ℝ)| / 2 ≤ |(n : ℝ)| * |(r 0 : ℝ)| - ‖frequencyVec r‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hra hn0.le]
  have hpl : ‖frequencyVec p‖ < |(n : ℝ)| * |(p 0 : ℝ)| := by linarith
  have hrl : ‖frequencyVec r‖ < |(n : ℝ)| * |(r 0 : ℝ)| := by linarith
  refine (sine_shearMap_le n p r hpl hrl).trans ?_
  have hden : |(n : ℝ)| / 2 * (|(n : ℝ)| / 2) ≤
      (|(n : ℝ)| * |(p 0 : ℝ)| - ‖frequencyVec p‖) * (|(n : ℝ)| * |(r 0 : ℝ)| - ‖frequencyVec r‖) :=
    mul_le_mul hP2 hR2 (by positivity) (by linarith)
  calc (1 + |(n : ℝ)|) * ‖frequencyVec (wavevectorCross p r)‖ /
        ((|(n : ℝ)| * |(p 0 : ℝ)| - ‖frequencyVec p‖) * (|(n : ℝ)| * |(r 0 : ℝ)| - ‖frequencyVec r‖))
      ≤ (1 + |(n : ℝ)|) * ‖frequencyVec (wavevectorCross p r)‖ / (|(n : ℝ)| / 2 * (|(n : ℝ)| / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ 8 * ‖frequencyVec (wavevectorCross p r)‖ / |(n : ℝ)| := by
        rw [div_le_div_iff₀ (by positivity) hn0]
        nlinarith [mul_nonneg hC hn0.le]

/-- **Sheared layers stop stretching one another.** For transverse
coefficients at the sheared modes, the pair stretching is at most
`16 |p × r| / |n|` times the product of the coefficients. -/
theorem norm_pair_stretch_shearMap_le (n : ℤ) {p r : Wavevector} (hp0 : p 0 ≠ 0) (hr0 : r 0 ≠ 0)
    (hpn : 2 * ‖frequencyVec p‖ ≤ |(n : ℝ)|) (hrn : 2 * ‖frequencyVec r‖ ≤ |(n : ℝ)|)
    {a b : VelocityCoefficient} (hpa : modeDot (shearMap n p) a = 0)
    (hrb : modeDot (shearMap n r) b = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp (shearMap n p) a b +
        unitTorusStrainStretchAmp (shearMap n r) b a)‖ ≤
      16 * ‖frequencyVec (wavevectorCross p r)‖ / |(n : ℝ)| * ‖coefficientVec a‖ *
        ‖coefficientVec b‖ := by
  have hsp : shearMap n p ≠ 0 := fun h ↦ hp0 (by
    have := congrFun h 0
    simpa [shearMap] using this)
  have hsr : shearMap n r ≠ 0 := fun h ↦ hr0 (by
    have := congrFun h 0
    simpa [shearMap] using this)
  have h := norm_pair_stretch_le_sine hsp hsr hpa hrb
  have hs := sine_shearMap_le_div n hp0 hr0 hpn hrn
  have hA := norm_nonneg (coefficientVec a)
  have hB := norm_nonneg (coefficientVec b)
  calc _ ≤ 2 * sine (shearMap n p) (shearMap n r) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := h
    _ ≤ 2 * (8 * ‖frequencyVec (wavevectorCross p r)‖ / |(n : ℝ)|) * ‖coefficientVec a‖ *
          ‖coefficientVec b‖ := by gcongr
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.FourierShearAlignment
