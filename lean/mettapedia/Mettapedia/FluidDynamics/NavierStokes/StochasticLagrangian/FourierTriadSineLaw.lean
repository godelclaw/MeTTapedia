import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPancakePairDepletion

/-!
# The triad sine law: collinear wavevectors do not interact

The pancake depletion needs no axis. For two vorticity modes `p`, `r`, the
nonlinear coupling of the vorticity equation is bounded by the sine of the
angle between the two wavevectors, `sin ∠(p, r) = |p × r| / (|p| |r|)`:

```text
‖S(u_p) ω_r + S(u_r) ω_p‖ ≤ 2 sin ∠(p, r) ‖ω_p‖ ‖ω_r‖,
‖(u_p · ∇) ω_r‖           ≤ sin ∠(p, r) (|r| / |p|) ‖ω_p‖ ‖ω_r‖.
```

The first is the pair-symmetrized stretching, and uses only that each
vorticity coefficient is transverse to its wavevector: `r · ω_p` sees only the
part of `r` orthogonal to `p`, whose length is `|p × r| / |p|`. The second is
the transport, and holds for any coefficient: `u_p · r` is the triple product
`ω_p · (r × p) / |p|²` up to the Fourier phase. Collinear wavevectors do not
interact at all; this is the exact algebraic reason why plane-parallel flows
solve the heat equation, and why a flat vortex layer cannot amplify itself.

Summed over the pairs of a finite set of modes whose angles have sine at most
`σ`, the stretching at any set of outputs is at most `σ` times the square of
the vorticity Wiener mass of the set. The cone bound of the pancake pair
depletion is the special case of pairs inside one narrow cone; here the
depletion is by the relative angle of each pair, whatever the directions.

The same bound holds for the momentum flux of the velocity equation: the
term `(q · u_p) u_r` that a transverse velocity mode `p` contributes at the
output `q` is at most `sin ∠(p, q) |q| ‖u_p‖ ‖u_r‖`, and vanishes when `p` and
`q` are collinear. A disturbance whose wavevector has been tilted onto the
wavevector of a mean-flow mode exerts no stress on that mode.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTriadSineLaw

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch PancakeIndexedFourierMoments
open PancakeInfinitePressureCoefficients PancakeSameSectorDissipation PancakeLowPressureBudget
open PancakeIncomingLowSourceEnergy PancakeGalerkinKineticEnergy
open FourierVorticitySource FourierRelaxation FourierShellFeeding FourierPancakePairDepletion

section Cross

/-- The cross product of two integer wavevectors. -/
def wavevectorCross (p r : Wavevector) : Wavevector :=
  ![p 1 * r 2 - p 2 * r 1, p 2 * r 0 - p 0 * r 2, p 0 * r 1 - p 1 * r 0]

/-- The sine of the angle between two wavevectors, `|p × r| / (|p| |r|)`. -/
def sine (p r : Wavevector) : ℝ :=
  ‖frequencyVec (wavevectorCross p r)‖ / (‖frequencyVec p‖ * ‖frequencyVec r‖)

theorem sine_nonneg (p r : Wavevector) : 0 ≤ sine p r := by
  unfold sine
  positivity

theorem wavevectorCoefficient_cross (p r : Wavevector) :
    wavevectorCoefficient (wavevectorCross p r) =
      coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r) := by
  ext i
  fin_cases i <;> simp [wavevectorCoefficient, wavevectorCross, coefficientCross]

theorem wavevectorCross_swap (p r : Wavevector) : wavevectorCross r p = -wavevectorCross p r := by
  ext i
  fin_cases i <;> simp [wavevectorCross] <;> ring

theorem norm_frequencyVec_neg (k : Wavevector) : ‖frequencyVec (-k)‖ = ‖frequencyVec k‖ := by
  have h : frequencyVec (-k) = -frequencyVec k := by
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  rw [h, norm_neg]

theorem norm_cross_swap (p r : Wavevector) :
    ‖frequencyVec (wavevectorCross r p)‖ = ‖frequencyVec (wavevectorCross p r)‖ := by
  rw [wavevectorCross_swap, norm_frequencyVec_neg]

theorem sine_comm (p r : Wavevector) : sine r p = sine p r := by
  unfold sine
  rw [norm_cross_swap, mul_comm]

theorem norm_frequencyVec_cross_le (p r : Wavevector) :
    ‖frequencyVec (wavevectorCross p r)‖ ≤ ‖frequencyVec p‖ * ‖frequencyVec r‖ := by
  have h := norm_cross_le p (wavevectorCoefficient r)
  rwa [← wavevectorCoefficient_cross] at h

/-- The double cross product of a transverse coefficient:
`((p × r) × p) · a = |p|² (r · a)` when `p · a = 0`. -/
theorem modeDot_doubleCross (p r : Wavevector) (a : VelocityCoefficient) (hpa : modeDot p a = 0) :
    modeDot (wavevectorCross (wavevectorCross p r) p) a = modeSquare p * modeDot r a := by
  simp only [modeDot, modeSquare, wavevectorCross, Fin.sum_univ_three] at hpa ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Int.cast_sub, Int.cast_mul]
  linear_combination (-((r 0 : ℂ) * p 0 + (r 1 : ℂ) * p 1 + (r 2 : ℂ) * p 2)) * hpa

/-- **The transverse sine bound.** For `a` transverse to `p`,
`|p| |r · a| ≤ |p × r| ‖a‖`. -/
theorem norm_modeDot_le_sine {p : Wavevector} (hp : p ≠ 0) (r : Wavevector)
    {a : VelocityCoefficient} (hpa : modeDot p a = 0) :
    ‖frequencyVec p‖ * ‖modeDot r a‖ ≤ ‖frequencyVec (wavevectorCross p r)‖ * ‖coefficientVec a‖ := by
  have hP := one_le_norm_frequencyVec hp
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  have h1 := norm_modeDot_le (wavevectorCross (wavevectorCross p r) p) a
  rw [modeDot_doubleCross p r a hpa, norm_mul, FourierTimeRegularity.norm_modeSquare] at h1
  have h2 := norm_frequencyVec_cross_le (wavevectorCross p r) p
  have hA := norm_nonneg (coefficientVec a)
  have h3 : ‖frequencyVec p‖ * (‖frequencyVec p‖ * ‖modeDot r a‖) ≤
      ‖frequencyVec p‖ * (‖frequencyVec (wavevectorCross p r)‖ * ‖coefficientVec a‖) := by
    calc ‖frequencyVec p‖ * (‖frequencyVec p‖ * ‖modeDot r a‖)
        = ‖frequencyVec p‖ ^ 2 * ‖modeDot r a‖ := by ring
      _ ≤ ‖frequencyVec (wavevectorCross (wavevectorCross p r) p)‖ * ‖coefficientVec a‖ := h1
      _ ≤ ‖frequencyVec (wavevectorCross p r)‖ * ‖frequencyVec p‖ * ‖coefficientVec a‖ :=
          mul_le_mul_of_nonneg_right h2 hA
      _ = ‖frequencyVec p‖ * (‖frequencyVec (wavevectorCross p r)‖ * ‖coefficientVec a‖) := by ring
  exact le_of_mul_le_mul_left h3 hP0

/-- The triple product `r · (p × a) = (r × p) · a`. -/
theorem modeDot_cross (p r : Wavevector) (a : VelocityCoefficient) :
    modeDot r (coefficientCross (wavevectorCoefficient p) a) = modeDot (wavevectorCross r p) a := by
  simp only [modeDot, coefficientCross, wavevectorCoefficient, wavevectorCross, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Int.cast_sub, Int.cast_mul]
  ring

end Cross

section Laws

/-- **The sine law for the pair stretching.** For transverse coefficients `a`
at `p` and `b` at `r`, the pair-symmetrized stretching is at most
`2 sin ∠(p, r) ‖a‖ ‖b‖`. -/
theorem norm_pair_stretch_le_sine {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    {a b : VelocityCoefficient} (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)‖ ≤
      2 * sine p r * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  rw [pair_stretch_eq hp hr hpa hrb]
  refine (norm_cv_add_le _ _).trans ?_
  rw [norm_cv_smul, norm_cv_smul, norm_mul, norm_mul, norm_derivativePhase]
  have hR := one_le_norm_frequencyVec hr
  have hP := one_le_norm_frequencyVec hp
  have hR0 : 0 < ‖frequencyVec r‖ := by linarith
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpi := Real.pi_pos
  have hA := norm_nonneg (coefficientVec a)
  have hB := norm_nonneg (coefficientVec b)
  set X := ‖frequencyVec (wavevectorCross p r)‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  -- the two dot products
  have hra : ‖modeDot r a‖ ≤ X * ‖coefficientVec a‖ / ‖frequencyVec p‖ := by
    rw [le_div_iff₀ hP0, mul_comm]
    exact norm_modeDot_le_sine hp r hpa
  have hpb : ‖modeDot p b‖ ≤ X * ‖coefficientVec b‖ / ‖frequencyVec r‖ := by
    rw [le_div_iff₀ hR0, mul_comm]
    have h := norm_modeDot_le_sine hr p hrb
    rwa [norm_cross_swap] at h
  have h1 := norm_biotSavart_le hr b
  have h2 := norm_biotSavart_le hp a
  have t1 : 2 * Real.pi * ‖modeDot r a‖ * ‖coefficientVec (unitTorusBiotSavartAmp r b)‖ ≤
      X / (‖frequencyVec p‖ * ‖frequencyVec r‖) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
    calc 2 * Real.pi * ‖modeDot r a‖ * ‖coefficientVec (unitTorusBiotSavartAmp r b)‖
        ≤ 2 * Real.pi * (X * ‖coefficientVec a‖ / ‖frequencyVec p‖) *
            (‖coefficientVec b‖ / (2 * Real.pi * ‖frequencyVec r‖)) := by
          gcongr
      _ = _ := by
          field_simp
  have t2 : 2 * Real.pi * ‖modeDot p b‖ * ‖coefficientVec (unitTorusBiotSavartAmp p a)‖ ≤
      X / (‖frequencyVec p‖ * ‖frequencyVec r‖) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
    calc 2 * Real.pi * ‖modeDot p b‖ * ‖coefficientVec (unitTorusBiotSavartAmp p a)‖
        ≤ 2 * Real.pi * (X * ‖coefficientVec b‖ / ‖frequencyVec r‖) *
            (‖coefficientVec a‖ / (2 * Real.pi * ‖frequencyVec p‖)) := by
          gcongr
      _ = _ := by
          field_simp
  have e : 2 * sine p r * ‖coefficientVec a‖ * ‖coefficientVec b‖ =
      X / (‖frequencyVec p‖ * ‖frequencyVec r‖) * ‖coefficientVec a‖ * ‖coefficientVec b‖ +
        X / (‖frequencyVec p‖ * ‖frequencyVec r‖) * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
    unfold sine
    ring
  rw [e]
  exact add_le_add t1 t2

/-- **The sine law for the transport.** For any coefficients `a` at `p` and
`b`, the transport `-(u_p · ∇) b` at the receiver `r` is at most
`|p × r| / |p|² ‖a‖ ‖b‖`, that is `sin ∠(p, r) (|r| / |p|) ‖a‖ ‖b‖`. -/
theorem norm_transport_le_sine {p : Wavevector} (hp : p ≠ 0) (r : Wavevector)
    (a b : VelocityCoefficient) :
    ‖coefficientVec (unitTorusNegativeTransportAmp p r a b)‖ ≤
      ‖frequencyVec (wavevectorCross p r)‖ / ‖frequencyVec p‖ ^ 2 *
        ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  have hP := one_le_norm_frequencyVec hp
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  rw [unitTorusNegativeTransportAmp_eq, norm_cv_smul]
  unfold complexBiotSavartAmp
  rw [PancakePeriodicCoherentSplit.modeDot_smul, norm_mul, modeDot_cross, norm_div, norm_one,
    FourierTimeRegularity.norm_modeSquare]
  have h := norm_modeDot_le (wavevectorCross r p) a
  rw [norm_cross_swap] at h
  have hB := norm_nonneg (coefficientVec b)
  calc 1 / ‖frequencyVec p‖ ^ 2 * ‖modeDot (wavevectorCross r p) a‖ * ‖coefficientVec b‖
      ≤ 1 / ‖frequencyVec p‖ ^ 2 * (‖frequencyVec (wavevectorCross p r)‖ * ‖coefficientVec a‖) *
          ‖coefficientVec b‖ := by
        gcongr
    _ = _ := by ring

/-- **Collinear wavevectors do not stretch each other.** -/
theorem pair_stretch_eq_zero_of_collinear {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    (hc : wavevectorCross p r = 0) {a b : VelocityCoefficient} (hpa : modeDot p a = 0)
    (hrb : modeDot r b = 0) :
    unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a = 0 := by
  have h := norm_pair_stretch_le_sine hp hr hpa hrb
  have hz : frequencyVec (0 : Wavevector) = 0 := by
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  have hs : sine p r = 0 := by
    unfold sine
    rw [hc, hz, norm_zero, zero_div]
  rw [hs] at h
  have h0 : ‖coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)‖ = 0 :=
    le_antisymm (by simpa using h) (norm_nonneg _)
  have h1 := norm_eq_zero.mp h0
  have h2 : (EuclideanSpace.equiv (Fin 3) ℂ)
      (coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)) = 0 := by
    rw [h1, map_zero]
  exact h2

/-- **Collinear wavevectors do not transport each other.** -/
theorem transport_eq_zero_of_collinear {p r : Wavevector} (hc : wavevectorCross p r = 0)
    (a b : VelocityCoefficient) : unitTorusNegativeTransportAmp p r a b = 0 := by
  rw [unitTorusNegativeTransportAmp_eq]
  unfold complexBiotSavartAmp
  rw [PancakePeriodicCoherentSplit.modeDot_smul, modeDot_cross, wavevectorCross_swap, hc, neg_zero]
  have : modeDot 0 a = 0 := by simp [modeDot]
  rw [this, mul_zero, zero_smul]

/-- **The sine law for the momentum flux.** For `a` transverse to `p`, the
term `(q · a) b` at the output `q` is at most `sin ∠(p, q) |q| ‖a‖ ‖b‖`. -/
theorem norm_stressTerm_le_sine {p : Wavevector} (hp : p ≠ 0) (q : Wavevector)
    {a : VelocityCoefficient} (hpa : modeDot p a = 0) (b : VelocityCoefficient) :
    ‖coefficientVec (modeDot q a • b)‖ ≤
      sine p q * ‖frequencyVec q‖ * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  have hP := one_le_norm_frequencyVec hp
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  have hA := norm_nonneg (coefficientVec a)
  have hB := norm_nonneg (coefficientVec b)
  rw [norm_cv_smul]
  rcases eq_or_ne q 0 with rfl | hq
  · have : modeDot 0 a = 0 := by simp [modeDot]
    rw [this, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sine_nonneg p 0) (norm_nonneg _)) hA) hB
  have hQ := one_le_norm_frequencyVec hq
  have hQ0 : 0 < ‖frequencyVec q‖ := by linarith
  have h := norm_modeDot_le_sine hp q hpa
  have e : sine p q * ‖frequencyVec q‖ = ‖frequencyVec (wavevectorCross p q)‖ / ‖frequencyVec p‖ := by
    unfold sine
    field_simp
  have hq' : ‖modeDot q a‖ ≤ ‖frequencyVec (wavevectorCross p q)‖ / ‖frequencyVec p‖ *
      ‖coefficientVec a‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hP0, mul_comm]
    exact h
  calc ‖modeDot q a‖ * ‖coefficientVec b‖
      ≤ ‖frequencyVec (wavevectorCross p q)‖ / ‖frequencyVec p‖ * ‖coefficientVec a‖ *
          ‖coefficientVec b‖ := mul_le_mul_of_nonneg_right hq' hB
    _ = _ := by rw [← e]

/-- **A mode collinear with the output exerts no stress there.** -/
theorem stressTerm_eq_zero_of_collinear {p q : Wavevector} (hp : p ≠ 0)
    (hc : wavevectorCross p q = 0) {a : VelocityCoefficient} (hpa : modeDot p a = 0)
    (b : VelocityCoefficient) : modeDot q a • b = 0 := by
  have hP := one_le_norm_frequencyVec hp
  have hP0 : 0 < ‖frequencyVec p‖ := by linarith
  have hz : frequencyVec (0 : Wavevector) = 0 := by
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  have h := norm_modeDot_le_sine hp q hpa
  rw [hc, hz, norm_zero, zero_mul] at h
  have h0 : ‖modeDot q a‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h hP0) (norm_nonneg _)
  rw [norm_eq_zero.mp h0, zero_smul]

end Laws

section Sums

variable (u : FourierVelocity)

/-- The stretching at the output `k` over the near-collinear pairs of modes
of `P`: the pairs `(p, k - p)` of `P` whose angle has sine at most `σ`. -/
def collinearStretch (σ : ℝ) (P : Finset Wavevector) (k : Wavevector) : VelocityCoefficient :=
  ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
    unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p))

theorem mem_collinearPairs_iff (σ : ℝ) (P : Finset Wavevector) (k p : Wavevector) :
    k - p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ) ↔
      p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ) := by
  simp only [Finset.mem_filter, sub_sub_cancel]
  rw [sine_comm]
  tauto

theorem two_smul_collinearStretch (σ : ℝ) (P : Finset Wavevector) (k : Wavevector) :
    (2 : ℂ) • collinearStretch u σ P k = ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
      (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p)) +
        unitTorusStrainStretchAmp (k - p) (fourierCurl u (k - p)) (fourierCurl u p)) := by
  have hsymm : collinearStretch u σ P k =
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
        unitTorusStrainStretchAmp (k - p) (fourierCurl u (k - p)) (fourierCurl u p) := by
    unfold collinearStretch
    refine Finset.sum_nbij' (fun p ↦ k - p) (fun p ↦ k - p) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      exact (mem_collinearPairs_iff σ P k p).mpr hp
    · intro p hp
      exact (mem_collinearPairs_iff σ P k p).mpr hp
    · intro p _
      simp
    · intro p _
      simp
    · intro p _
      simp
  rw [Finset.sum_add_distrib, two_smul]
  congr 1

/-- **The pointwise near-collinear bound.** -/
theorem norm_collinearStretch_le (σ : ℝ) (P : Finset Wavevector) (hP0 : (0 : Wavevector) ∉ P)
    (k : Wavevector) :
    ‖coefficientVec (collinearStretch u σ P k)‖ ≤
      σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
        curlMass u p * curlMass u (k - p) := by
  have h2 : ‖coefficientVec ((2 : ℂ) • collinearStretch u σ P k)‖ =
      2 * ‖coefficientVec (collinearStretch u σ P k)‖ := by
    rw [norm_cv_smul]
    norm_num
  have hle : ‖coefficientVec ((2 : ℂ) • collinearStretch u σ P k)‖ ≤
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
        2 * σ * curlMass u p * curlMass u (k - p) := by
    rw [two_smul_collinearStretch, PancakeFixedOutputVelocityBound.coefficientVec_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    have hp' := Finset.mem_filter.mp hp
    have hpP := hp'.1
    have hkpP := hp'.2.1
    have hσ := hp'.2.2
    have hb := norm_pair_stretch_le_sine (fun h ↦ hP0 (h ▸ hpP)) (fun h ↦ hP0 (h ▸ hkpP))
      (fourierCurl_transverse p u) (fourierCurl_transverse (k - p) u)
    have hA := curlMass_nonneg u p
    have hB := curlMass_nonneg u (k - p)
    calc _ ≤ 2 * sine p (k - p) * curlMass u p * curlMass u (k - p) := hb
      _ ≤ 2 * σ * curlMass u p * curlMass u (k - p) := by
          gcongr
  rw [h2] at hle
  have e : ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
      2 * σ * curlMass u p * curlMass u (k - p) =
      2 * (σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
        curlMass u p * curlMass u (k - p)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  linarith

/-- **The near-collinear stretching over any set of outputs is at most `σ`
times the square of the vorticity Wiener mass of the modes.** -/
theorem sum_norm_collinearStretch_le {σ : ℝ} (hσ : 0 ≤ σ) (P K : Finset Wavevector)
    (hP0 : (0 : Wavevector) ∉ P) :
    ∑ k ∈ K, ‖coefficientVec (collinearStretch u σ P k)‖ ≤
      σ * pancakeMass u P * pancakeMass u P := by
  refine (Finset.sum_le_sum fun k _ ↦ norm_collinearStretch_le u σ P hP0 k).trans ?_
  set m : Wavevector → ℝ := fun p ↦ curlMass u p with hm
  have hm0 : ∀ p, 0 ≤ m p := fun p ↦ curlMass_nonneg u p
  have hdrop : ∀ k ∈ K, σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P ∧ sine p (k - p) ≤ σ),
      m p * m (k - p) ≤ σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), m p * m (k - p) := by
    intro k _
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ ↦
      mul_nonneg (hm0 p) (hm0 (k - p))) hσ
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  refine (Finset.sum_le_sum hdrop).trans ?_
  have hswap : ∑ k ∈ K, σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), m p * m (k - p) =
      ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), σ * m p * m (k - p) := by
    simp only [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> ring
  have hinner : ∀ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), σ * m p * m (k - p) ≤
      ∑ r ∈ P, σ * m p * m r := by
    intro p _
    have hinj : Set.InjOn (fun k ↦ k - p) ↑(K.filter (fun k ↦ k - p ∈ P)) :=
      fun _ _ _ _ h ↦ sub_left_injective h
    rw [← Finset.sum_image (f := fun r ↦ σ * m p * m r) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ ↦
      mul_nonneg (mul_nonneg hσ (hm0 p)) (hm0 r)
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact (Finset.mem_filter.mp hk).2
  calc ∑ k ∈ K, σ * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), m p * m (k - p)
      = ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ P), σ * m p * m (k - p) := hswap
    _ ≤ ∑ p ∈ P, ∑ r ∈ P, σ * m p * m r := Finset.sum_le_sum hinner
    _ = σ * pancakeMass u P * pancakeMass u P := by
        unfold pancakeMass
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ ↦ mul_assoc _ _ _

/-- **The near-collinear feeding of the shells above `2^(Q+1)`.** With the
sharp relaxation weight, the near-collinear stretching of the modes `P` at
outputs above `2^(Q+1)` is at most `3σ / (4π²ν 4^(Q+1))` times the square of
their vorticity Wiener mass. -/
theorem sum_sharp_collinearStretch_le {nu : ℝ} (hnu : 0 < nu) (Q : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (P K : Finset Wavevector) (hP0 : (0 : Wavevector) ∉ P)
    (hK : ∀ k ∈ K, 4 ^ (Q + 1) ≤ modeSquareNat k) :
    ∑ k ∈ K, sharpWeight nu k * ‖coefficientVec (collinearStretch u σ P k)‖ ≤
      3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) * (σ * pancakeMass u P * pancakeMass u P) := by
  calc ∑ k ∈ K, sharpWeight nu k * ‖coefficientVec (collinearStretch u σ P k)‖
      ≤ ∑ k ∈ K, 3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) *
          ‖coefficientVec (collinearStretch u σ P k)‖ :=
        Finset.sum_le_sum fun k hk ↦
          mul_le_mul_of_nonneg_right (sharpWeight_le_of_high hnu (hK k hk)) (norm_nonneg _)
    _ = 3 / (4 * Real.pi ^ 2 * nu * 4 ^ (Q + 1)) *
          ∑ k ∈ K, ‖coefficientVec (collinearStretch u σ P k)‖ := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact sum_norm_collinearStretch_le u hσ P K hP0

end Sums

end Mettapedia.FluidDynamics.NavierStokes.FourierTriadSineLaw
