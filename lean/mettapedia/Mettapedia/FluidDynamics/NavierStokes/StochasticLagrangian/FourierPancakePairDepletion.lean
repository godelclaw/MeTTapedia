import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCoherentDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierShellFeeding

/-!
# Pancake pair depletion by transversality alone

The stretching of a pair of modes `p`, `r` of the vorticity, symmetrized over
the pair, is `(ω_p · ∇) u_r + (ω_r · ∇) u_p`: the antisymmetric parts of the
two velocity gradients cancel between the two orders of the pair. Since a
vorticity coefficient is transverse to its own wavevector, `ω_p · r` is the
component of `ω_p` along the part of `r` orthogonal to `p`, so the pair
stretching is bounded by the sine of the angle between `p` and `r`. In the
pancake cone about the third axis, of squared aperture `d`, every such pair
is therefore depleted by the aperture:

```text
‖S(u_p) ω_r + S(u_r) ω_p‖ ≤ 8 (√d₁ + √d₂) ‖ω_p‖ ‖ω_r‖.
```

No coherent projection is needed: a flat pancake does not stretch itself,
whatever the in-plane directions of its vorticity. Over the cone, the
pancake stretching feeding the shells above `2^(Q+1)` is at most the
aperture times the pancake Reynolds number `M_P / (ν 4^(Q+1))` times the
pancake mass `M_P`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPancakePairDepletion

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch PancakeIndexedFourierMoments
open PancakeInfinitePressureCoefficients PancakeSameSectorDissipation PancakeLowPressureBudget
open PancakeIncomingLowSourceEnergy FourierTimeRegularity PancakeGalerkinKineticEnergy
open FourierCoherentDepletion FourierVorticitySource FourierRelaxation FourierShellFeeding

section Algebra

/-- The triple product `u × (v × w) = (u·w) v - (u·v) w`. -/
theorem cross_cross (u v w : VelocityCoefficient) :
    coefficientCross u (coefficientCross v w) =
      coefficientDot u w • v - coefficientDot u v • w := by
  ext i
  fin_cases i <;> simp [coefficientCross, coefficientDot, Fin.sum_univ_three] <;> ring

theorem cross_anticomm (u v : VelocityCoefficient) :
    coefficientCross u v = -coefficientCross v u := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem coefficientDot_comm (u v : VelocityCoefficient) :
    coefficientDot u v = coefficientDot v u := by
  simp only [coefficientDot]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

theorem coefficientDot_wavevector_left (k : Wavevector) (v : VelocityCoefficient) :
    coefficientDot (wavevectorCoefficient k) v = modeDot k v := rfl

theorem coefficientDot_wavevector_right (k : Wavevector) (v : VelocityCoefficient) :
    coefficientDot v (wavevectorCoefficient k) = modeDot k v := by
  rw [coefficientDot_comm]
  rfl

theorem coefficientDot_wavevector_self (k : Wavevector) :
    coefficientDot (wavevectorCoefficient k) (wavevectorCoefficient k) = modeSquare k := rfl

/-- The curl of the Biot–Savart velocity of a transverse coefficient returns
the coefficient: `p × u_p = (2πi)⁻¹ ω_p`. -/
theorem wavevector_cross_biotSavart {p : Wavevector} (hp : p ≠ 0) {a : VelocityCoefficient}
    (hpa : modeDot p a = 0) :
    coefficientCross (wavevectorCoefficient p) (unitTorusBiotSavartAmp p a) =
      unitTorusDerivativePhase⁻¹ • a := by
  have hms : modeSquare p ≠ 0 :=
    modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hp)
  have h1 : coefficientDot (wavevectorCoefficient p) a = 0 := hpa
  unfold unitTorusBiotSavartAmp complexBiotSavartAmp
  rw [coefficientCross_smul_right, coefficientCross_smul_right, cross_cross, h1,
    coefficientDot_wavevector_self]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, zero_mul, zero_sub, mul_neg, neg_mul,
    neg_neg]
  field_simp

/-- The strain of a transverse source acting on a receiver, as the convective
form plus half a Lamb term: `S(u_p) b = ½ b × ω_p + (b · ∇) u_p`. -/
theorem stretch_eq_convective {p : Wavevector} (hp : p ≠ 0) {a : VelocityCoefficient}
    (hpa : modeDot p a = 0) (b : VelocityCoefficient) :
    unitTorusStrainStretchAmp p a b =
      (1 / 2 : ℂ) • coefficientCross b a +
        (unitTorusDerivativePhase * modeDot p b) • unitTorusBiotSavartAmp p a := by
  have hinv : unitTorusDerivativePhase * unitTorusDerivativePhase⁻¹ = 1 :=
    mul_inv_cancel₀ unitTorusDerivativePhase_ne_zero
  have e := cross_cross b (wavevectorCoefficient p) (unitTorusBiotSavartAmp p a)
  rw [wavevector_cross_biotSavart hp hpa, coefficientCross_smul_right,
    coefficientDot_comm b (unitTorusBiotSavartAmp p a), coefficientDot_wavevector_right] at e
  unfold unitTorusStrainStretchAmp
  ext i
  have ei := congrFun e i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at ei ⊢
  linear_combination (-(1 / 2 : ℂ) * unitTorusDerivativePhase) * ei +
    ((1 / 2 : ℂ) * coefficientCross b a i) * hinv

/-- **The pair-symmetrized stretching is the convective form.** For transverse
`a` at `p` and `b` at `r`, `S(u_p) b + S(u_r) a = (a · ∇) u_r + (b · ∇) u_p`. -/
theorem pair_stretch_eq {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0) {a b : VelocityCoefficient}
    (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a =
      (unitTorusDerivativePhase * modeDot r a) • unitTorusBiotSavartAmp r b +
        (unitTorusDerivativePhase * modeDot p b) • unitTorusBiotSavartAmp p a := by
  rw [stretch_eq_convective hp hpa b, stretch_eq_convective hr hrb a, cross_anticomm a b]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end Algebra

section Norms

/-- The Biot–Savart bound `‖u_r‖ ≤ ‖b‖ / (2π|r|)` for any coefficient `b`. -/
theorem norm_biotSavart_le {r : Wavevector} (hr : r ≠ 0) (b : VelocityCoefficient) :
    ‖coefficientVec (unitTorusBiotSavartAmp r b)‖ ≤
      ‖coefficientVec b‖ / (2 * Real.pi * ‖frequencyVec r‖) := by
  have hn := one_le_norm_frequencyVec hr
  have hn0 : 0 < ‖frequencyVec r‖ := by linarith
  unfold unitTorusBiotSavartAmp complexBiotSavartAmp
  rw [norm_cv_smul, norm_cv_smul, norm_neg, norm_inv, norm_derivativePhase, norm_div, norm_one,
    FourierTimeRegularity.norm_modeSquare]
  have h := norm_cross_le r b
  have hkne : ‖frequencyVec r‖ ≠ 0 := hn0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [le_div_iff₀ (by positivity)]
  calc (2 * Real.pi)⁻¹ * (1 / ‖frequencyVec r‖ ^ 2 *
        ‖coefficientVec (coefficientCross (wavevectorCoefficient r) b)‖) *
        (2 * Real.pi * ‖frequencyVec r‖)
      ≤ (2 * Real.pi)⁻¹ * (1 / ‖frequencyVec r‖ ^ 2 *
          (‖frequencyVec r‖ * ‖coefficientVec b‖)) * (2 * Real.pi * ‖frequencyVec r‖) := by
        gcongr
    _ = ‖coefficientVec b‖ := by
        field_simp

theorem norm_intCast_mul (n : ℤ) (z : ℂ) : ‖(n : ℂ) * z‖ = |(n : ℝ)| * ‖z‖ := by
  rw [norm_mul, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

/-- The cone bounds on the coordinates: in the cone of squared aperture `d`,
the in-plane coordinates are at most `√d |k|` and the axial one is at least
`|k| / 2` when `d ≤ 1/4`. -/
theorem cone_coord_le {d : ℝ} {k : Wavevector} (hc : InCone d k) (hk : k ≠ 0) :
    0 ≤ d ∧ |(k 0 : ℝ)| ≤ Real.sqrt d * ‖frequencyVec k‖ ∧
      |(k 1 : ℝ)| ≤ Real.sqrt d * ‖frequencyVec k‖ ∧ |(k 2 : ℝ)| ≤ ‖frequencyVec k‖ := by
  have hc' : (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 ≤ d * ‖frequencyVec k‖ ^ 2 := hc
  have hsq := norm_frequencyVec_sq k
  rw [Fin.sum_univ_three] at hsq
  have hn := one_le_norm_frequencyVec hk
  have hn0 : 0 < ‖frequencyVec k‖ := by linarith
  have hd : 0 ≤ d := by
    have h1 : 0 ≤ d * ‖frequencyVec k‖ ^ 2 := le_trans (by positivity) hc'
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  have hsd : Real.sqrt (d * ‖frequencyVec k‖ ^ 2) = Real.sqrt d * ‖frequencyVec k‖ := by
    rw [Real.sqrt_mul hd, Real.sqrt_sq hn0.le]
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [← hsd]
    exact Real.abs_le_sqrt (by linarith [sq_nonneg (k 1 : ℝ)])
  · rw [← hsd]
    exact Real.abs_le_sqrt (by linarith [sq_nonneg (k 0 : ℝ)])
  · rw [← Real.sqrt_sq hn0.le]
    exact Real.abs_le_sqrt (by linarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)])

theorem half_norm_le_axial {d : ℝ} {k : Wavevector} (hc : InCone d k) (hd : d ≤ 1 / 4) :
    ‖frequencyVec k‖ / 2 ≤ |(k 2 : ℝ)| := by
  have hc' : (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 ≤ d * ‖frequencyVec k‖ ^ 2 := hc
  have hsq := norm_frequencyVec_sq k
  rw [Fin.sum_univ_three] at hsq
  have hn := norm_nonneg (frequencyVec k)
  have h : (‖frequencyVec k‖ / 2) ^ 2 ≤ |(k 2 : ℝ)| ^ 2 := by
    rw [sq_abs]
    have : d * ‖frequencyVec k‖ ^ 2 ≤ 1 / 4 * ‖frequencyVec k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    nlinarith
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp h

/-- **The transverse cone bound.** For `a` transverse to `p` and both `p`, `r`
in the pancake cones, `|r · a|` is at most `4 (√d₁ + √d₂) |r| ‖a‖`. -/
theorem norm_modeDot_le_of_cone {p r : Wavevector} {d₁ d₂ : ℝ} (hc₁ : InCone d₁ p)
    (hc₂ : InCone d₂ r) (hd₁ : d₁ ≤ 1 / 4) (hp : p ≠ 0) (hr : r ≠ 0) (a : VelocityCoefficient)
    (hpa : modeDot p a = 0) :
    ‖modeDot r a‖ ≤ 4 * (Real.sqrt d₁ + Real.sqrt d₂) * ‖frequencyVec r‖ * ‖coefficientVec a‖ := by
  obtain ⟨hd₁0, hp0, hp1, hp2⟩ := cone_coord_le hc₁ hp
  obtain ⟨hd₂0, hr0, hr1, hr2⟩ := cone_coord_le hc₂ hr
  have hax := half_norm_le_axial hc₁ hd₁
  have hP := one_le_norm_frequencyVec hp
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  have hR := norm_nonneg (frequencyVec r)
  have hA := norm_nonneg (coefficientVec a)
  have ha : ∀ i, ‖a i‖ ≤ ‖coefficientVec a‖ := fun i ↦ PiLp.norm_apply_le (coefficientVec a) i
  set s₁ := Real.sqrt d₁ with hs₁
  set s₂ := Real.sqrt d₂ with hs₂
  have hs₁0 : 0 ≤ s₁ := Real.sqrt_nonneg _
  have hs₂0 : 0 ≤ s₂ := Real.sqrt_nonneg _
  -- the axial coordinate times the dot product
  have hid : (p 2 : ℂ) * modeDot r a =
      ((p 2 * r 0 - r 2 * p 0 : ℤ) : ℂ) * a 0 + ((p 2 * r 1 - r 2 * p 1 : ℤ) : ℂ) * a 1 := by
    simp only [modeDot, Fin.sum_univ_three] at hpa ⊢
    push_cast
    linear_combination (r 2 : ℂ) * hpa
  have hcoef : ∀ (x y z w : ℤ), |((x * y - z * w : ℤ) : ℝ)| ≤
      |(x : ℝ)| * |(y : ℝ)| + |(z : ℝ)| * |(w : ℝ)| := by
    intro x y z w
    push_cast
    exact (abs_sub _ _).trans (by rw [abs_mul, abs_mul])
  have hc0 : |((p 2 * r 0 - r 2 * p 0 : ℤ) : ℝ)| ≤ ‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂) := by
    refine (hcoef _ _ _ _).trans ?_
    calc |(p 2 : ℝ)| * |(r 0 : ℝ)| + |(r 2 : ℝ)| * |(p 0 : ℝ)|
        ≤ ‖frequencyVec p‖ * (s₂ * ‖frequencyVec r‖) + ‖frequencyVec r‖ * (s₁ * ‖frequencyVec p‖) :=
          add_le_add (mul_le_mul hp2 hr0 (abs_nonneg _) hP0.le)
            (mul_le_mul hr2 hp0 (abs_nonneg _) hR)
      _ = _ := by ring
  have hc1 : |((p 2 * r 1 - r 2 * p 1 : ℤ) : ℝ)| ≤ ‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂) := by
    refine (hcoef _ _ _ _).trans ?_
    calc |(p 2 : ℝ)| * |(r 1 : ℝ)| + |(r 2 : ℝ)| * |(p 1 : ℝ)|
        ≤ ‖frequencyVec p‖ * (s₂ * ‖frequencyVec r‖) + ‖frequencyVec r‖ * (s₁ * ‖frequencyVec p‖) :=
          add_le_add (mul_le_mul hp2 hr1 (abs_nonneg _) hP0.le)
            (mul_le_mul hr2 hp1 (abs_nonneg _) hR)
      _ = _ := by ring
  have hprod : |(p 2 : ℝ)| * ‖modeDot r a‖ ≤
      2 * (‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂)) * ‖coefficientVec a‖ := by
    rw [← norm_intCast_mul, hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_intCast_mul, norm_intCast_mul]
    have hcs : 0 ≤ ‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂) := by positivity
    calc |((p 2 * r 0 - r 2 * p 0 : ℤ) : ℝ)| * ‖a 0‖ + |((p 2 * r 1 - r 2 * p 1 : ℤ) : ℝ)| * ‖a 1‖
        ≤ ‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂) * ‖coefficientVec a‖ +
          ‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂) * ‖coefficientVec a‖ :=
          add_le_add (mul_le_mul hc0 (ha 0) (norm_nonneg _) hcs)
            (mul_le_mul hc1 (ha 1) (norm_nonneg _) hcs)
      _ = _ := by ring
  have hM := norm_nonneg (modeDot r a)
  have h2 : ‖frequencyVec p‖ / 2 * ‖modeDot r a‖ ≤
      ‖frequencyVec p‖ / 2 * (4 * (s₁ + s₂) * ‖frequencyVec r‖ * ‖coefficientVec a‖) := by
    calc ‖frequencyVec p‖ / 2 * ‖modeDot r a‖ ≤ |(p 2 : ℝ)| * ‖modeDot r a‖ :=
          mul_le_mul_of_nonneg_right hax hM
      _ ≤ 2 * (‖frequencyVec p‖ * ‖frequencyVec r‖ * (s₁ + s₂)) * ‖coefficientVec a‖ := hprod
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- **Pancake pair depletion by transversality.** For `p`, `r` in the cones of
squared apertures `d₁`, `d₂` at most `1/4` and transverse coefficients `a` at
`p`, `b` at `r`, the pair-symmetrized stretching is at most
`8 (√d₁ + √d₂) ‖a‖ ‖b‖`. -/
theorem norm_pair_stretch_le {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0) {d₁ d₂ : ℝ}
    (hc₁ : InCone d₁ p) (hc₂ : InCone d₂ r) (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4)
    {a b : VelocityCoefficient} (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)‖ ≤
      8 * (Real.sqrt d₁ + Real.sqrt d₂) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  rw [pair_stretch_eq hp hr hpa hrb]
  refine (norm_cv_add_le _ _).trans ?_
  rw [norm_cv_smul, norm_cv_smul, norm_mul, norm_mul, norm_derivativePhase]
  have hR := one_le_norm_frequencyVec hr
  have hP := one_le_norm_frequencyVec hp
  have hRne : ‖frequencyVec r‖ ≠ 0 := by positivity
  have hPne : ‖frequencyVec p‖ ≠ 0 := by positivity
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 := norm_biotSavart_le hr b
  have h2 := norm_biotSavart_le hp a
  have h3 := norm_modeDot_le_of_cone hc₁ hc₂ hd₁ hp hr a hpa
  have h4 := norm_modeDot_le_of_cone hc₂ hc₁ hd₂ hr hp b hrb
  have hA := norm_nonneg (coefficientVec a)
  have hB := norm_nonneg (coefficientVec b)
  have hs : 0 ≤ Real.sqrt d₁ + Real.sqrt d₂ := by positivity
  have t1 : 2 * Real.pi * ‖modeDot r a‖ * ‖coefficientVec (unitTorusBiotSavartAmp r b)‖ ≤
      4 * (Real.sqrt d₁ + Real.sqrt d₂) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
    calc 2 * Real.pi * ‖modeDot r a‖ * ‖coefficientVec (unitTorusBiotSavartAmp r b)‖
        ≤ 2 * Real.pi * (4 * (Real.sqrt d₁ + Real.sqrt d₂) * ‖frequencyVec r‖ * ‖coefficientVec a‖) *
            (‖coefficientVec b‖ / (2 * Real.pi * ‖frequencyVec r‖)) := by
          gcongr
      _ = _ := by
          field_simp
  have t2 : 2 * Real.pi * ‖modeDot p b‖ * ‖coefficientVec (unitTorusBiotSavartAmp p a)‖ ≤
      4 * (Real.sqrt d₂ + Real.sqrt d₁) * ‖coefficientVec b‖ * ‖coefficientVec a‖ := by
    calc 2 * Real.pi * ‖modeDot p b‖ * ‖coefficientVec (unitTorusBiotSavartAmp p a)‖
        ≤ 2 * Real.pi * (4 * (Real.sqrt d₂ + Real.sqrt d₁) * ‖frequencyVec p‖ * ‖coefficientVec b‖) *
            (‖coefficientVec a‖ / (2 * Real.pi * ‖frequencyVec p‖)) := by
          gcongr
      _ = _ := by
          field_simp
  linarith

end Norms

section Sums

variable (u : FourierVelocity)

/-- The pancake stretching of the cone modes `P` at the output `k`: the
stretching over all pairs `(p, k - p)` of modes of `P`. -/
def pancakeStretch (P : Finset Wavevector) (k : Wavevector) : VelocityCoefficient :=
  ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
    unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p))

/-- The vorticity Wiener mass of the modes `P`. -/
def pancakeMass (P : Finset Wavevector) : ℝ := ∑ p ∈ P, curlMass u p

theorem pancakeMass_nonneg (P : Finset Wavevector) : 0 ≤ pancakeMass u P :=
  Finset.sum_nonneg fun p _ ↦ curlMass_nonneg u p

theorem mem_pairs_iff (P : Finset Wavevector) (k p : Wavevector) :
    k - p ∈ P.filter (fun p ↦ k - p ∈ P) ↔ p ∈ P.filter (fun p ↦ k - p ∈ P) := by
  simp only [Finset.mem_filter, sub_sub_cancel]
  exact and_comm

/-- The pancake stretching in the reversed pair order. -/
theorem pancakeStretch_symm (P : Finset Wavevector) (k : Wavevector) :
    pancakeStretch u P k = ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
      unitTorusStrainStretchAmp (k - p) (fourierCurl u (k - p)) (fourierCurl u p) := by
  unfold pancakeStretch
  refine Finset.sum_nbij' (fun p ↦ k - p) (fun p ↦ k - p) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_pairs_iff P k p).mpr hp
  · intro p hp
    exact (mem_pairs_iff P k p).mpr hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

theorem two_smul_pancakeStretch (P : Finset Wavevector) (k : Wavevector) :
    (2 : ℂ) • pancakeStretch u P k = ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
      (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p)) +
        unitTorusStrainStretchAmp (k - p) (fourierCurl u (k - p)) (fourierCurl u p)) := by
  rw [Finset.sum_add_distrib, ← pancakeStretch_symm, two_smul]
  rfl

/-- **The pointwise pancake bound.** -/
theorem norm_pancakeStretch_le (P : Finset Wavevector) {d : ℝ} (hP0 : (0 : Wavevector) ∉ P)
    (hP : ∀ p ∈ P, InCone d p) (hd : d ≤ 1 / 4) (k : Wavevector) :
    ‖coefficientVec (pancakeStretch u P k)‖ ≤
      8 * Real.sqrt d * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), curlMass u p * curlMass u (k - p) := by
  have h2 : ‖coefficientVec ((2 : ℂ) • pancakeStretch u P k)‖ =
      2 * ‖coefficientVec (pancakeStretch u P k)‖ := by
    rw [norm_cv_smul]
    norm_num
  have hle : ‖coefficientVec ((2 : ℂ) • pancakeStretch u P k)‖ ≤
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        8 * (Real.sqrt d + Real.sqrt d) * curlMass u p * curlMass u (k - p) := by
    rw [two_smul_pancakeStretch, PancakeFixedOutputVelocityBound.coefficientVec_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    obtain ⟨hpP, hkpP⟩ := Finset.mem_filter.mp hp
    exact norm_pair_stretch_le (fun h ↦ hP0 (h ▸ hpP)) (fun h ↦ hP0 (h ▸ hkpP)) (hP p hpP)
      (hP _ hkpP) hd hd (fourierCurl_transverse p u) (fourierCurl_transverse (k - p) u)
  rw [h2] at hle
  have : ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
      8 * (Real.sqrt d + Real.sqrt d) * curlMass u p * curlMass u (k - p) =
      2 * (8 * Real.sqrt d * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), curlMass u p * curlMass u (k - p)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  linarith

/-- **The pancake stretching over any set of outputs is bounded by the
aperture times the square of the pancake mass.** -/
theorem sum_norm_pancakeStretch_le (P K : Finset Wavevector) {d : ℝ}
    (hP0 : (0 : Wavevector) ∉ P) (hP : ∀ p ∈ P, InCone d p) (hd : d ≤ 1 / 4) :
    ∑ k ∈ K, ‖coefficientVec (pancakeStretch u P k)‖ ≤
      8 * Real.sqrt d * pancakeMass u P * pancakeMass u P := by
  refine (Finset.sum_le_sum fun k _ ↦ norm_pancakeStretch_le u P hP0 hP hd k).trans ?_
  set m : Wavevector → ℝ := fun p ↦ curlMass u p with hm
  set c := 8 * Real.sqrt d with hc
  have hc0 : 0 ≤ c := by positivity
  have hm0 : ∀ p, 0 ≤ m p := fun p ↦ curlMass_nonneg u p
  have hswap : ∑ k ∈ K, c * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), m p * m (k - p) =
      ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), c * m p * m (k - p) := by
    simp only [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> ring
  have hinner : ∀ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), c * m p * m (k - p) ≤
      ∑ r ∈ P, c * m p * m r := by
    intro p _
    have hinj : Set.InjOn (fun k ↦ k - p) ↑(K.filter (fun k ↦ k - p ∈ P)) :=
      fun _ _ _ _ h ↦ sub_left_injective h
    rw [← Finset.sum_image (f := fun r ↦ c * m p * m r) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ ↦
      mul_nonneg (mul_nonneg hc0 (hm0 p)) (hm0 r)
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact (Finset.mem_filter.mp hk).2
  calc ∑ k ∈ K, c * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), m p * m (k - p)
      = ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), c * m p * m (k - p) := hswap
    _ ≤ ∑ p ∈ P, ∑ r ∈ P, c * m p * m r := Finset.sum_le_sum hinner
    _ = c * pancakeMass u P * pancakeMass u P := by
        unfold pancakeMass
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ ↦ mul_assoc _ _ _

theorem sharpWeight_le_of_high {nu : ℝ} (hnu : 0 < nu) {Q : ℕ} {k : Wavevector}
    (hk : 4 ^ (Q + 1) ≤ modeSquareNat k) :
    sharpWeight nu k ≤ 3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) := by
  unfold sharpWeight damping
  have h : ((4 : ℝ) ^ (Q + 1)) ≤ ‖frequencyVec k‖ ^ 2 := by
    rw [← modeSquareNat_cast]
    exact_mod_cast hk
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (mul_le_mul_of_nonneg_left h (by positivity))

/-- **The pancake feeding of the shells above `2^(Q+1)`.** With the sharp
relaxation weight, the pancake stretching of the cone modes `P` at outputs
above `2^(Q+1)` is at most `3 / (4π²ν 4^(Q+1))` times the aperture bound: the
aperture times the pancake Reynolds number times the pancake mass. -/
theorem sum_sharp_pancakeStretch_le {nu : ℝ} (hnu : 0 < nu) (Q : ℕ) (P K : Finset Wavevector)
    {d : ℝ} (hP0 : (0 : Wavevector) ∉ P) (hP : ∀ p ∈ P, InCone d p) (hd : d ≤ 1 / 4)
    (hK : ∀ k ∈ K, 4 ^ (Q + 1) ≤ modeSquareNat k) :
    ∑ k ∈ K, sharpWeight nu k * ‖coefficientVec (pancakeStretch u P k)‖ ≤
      3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) *
        (8 * Real.sqrt d * pancakeMass u P * pancakeMass u P) := by
  calc ∑ k ∈ K, sharpWeight nu k * ‖coefficientVec (pancakeStretch u P k)‖
      ≤ ∑ k ∈ K, 3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) *
          ‖coefficientVec (pancakeStretch u P k)‖ :=
        Finset.sum_le_sum fun k hk ↦
          mul_le_mul_of_nonneg_right (sharpWeight_le_of_high hnu (hK k hk)) (norm_nonneg _)
    _ = 3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) *
          ∑ k ∈ K, ‖coefficientVec (pancakeStretch u P k)‖ := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact sum_norm_pancakeStretch_le u P K hP0 hP hd

end Sums

end Mettapedia.FluidDynamics.NavierStokes.FourierPancakePairDepletion
