import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialEquation

/-!
# The mean velocity by a Galilean change of frame

The Fourier solutions have zero mean. A velocity with constant mean `m` is
obtained by a Galilean change of frame: if `w` solves the equations with zero
mean, then `v(x, t) = m + w(x - t m, t)` solves them with mean `m`. On the
coefficients this multiplies the `q`-th mode by the phase
`exp(-2π i ⟨q, m⟩ t)` and adds `m` at the zero mode:

```text
c̃_q(t) = exp(-2π i ⟨q, m⟩ t) c_q(t) + δ_{q0} m.
```

The convection of `c̃` is the phased convection of `c` plus the transport by
the mean, `conv_q(c̃) = e_q conv_q(c) + ⟨q, m⟩ c̃_q`, and the phase derivative
cancels the transport term, so `c̃` is again a Fourier solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierGalilean

open scoped BigOperators Topology ComplexConjugate
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open PancakeBlockReality PancakeCoefficientLimitEquation PancakeTransverseEnergyFreezing
open FourierTimeRegularity FourierPhysicalFields FourierSpatialCalculus FourierOfficialEquation

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section Phase

variable (m : ℝ³)

/-- The complexified mean velocity. -/
def meanCoeff : VelocityCoefficient := fun i ↦ (m i : ℂ)

/-- A coefficient field supported on the zero mode. -/
def single0 (v : VelocityCoefficient) : FourierVelocity := Pi.single 0 v

@[simp] theorem single0_zero (v : VelocityCoefficient) : single0 v 0 = v := Pi.single_eq_same _ _

theorem single0_of_ne (v : VelocityCoefficient) {q : Wavevector} (hq : q ≠ 0) : single0 v q = 0 :=
  Pi.single_eq_of_ne hq _

/-- The Galilean phase `exp(-2π i ⟨q, m⟩ t)`. -/
def galileanPhase (t : ℝ) (q : Wavevector) : ℂ := phaseFun (-(modeFunctional q m * t))

theorem norm_galileanPhase (t : ℝ) (q : Wavevector) : ‖galileanPhase m t q‖ = 1 :=
  norm_phaseFun _

theorem galileanPhase_add (t : ℝ) (p q : Wavevector) :
    galileanPhase m t (p + q) = galileanPhase m t p * galileanPhase m t q := by
  rw [galileanPhase, galileanPhase, galileanPhase, ← phaseFun_add, modeFunctional_add]
  congr 1
  ring

theorem galileanPhase_mul_sub (t : ℝ) (p q : Wavevector) :
    galileanPhase m t p * galileanPhase m t (q - p) = galileanPhase m t q := by
  rw [← galileanPhase_add, add_sub_cancel]

theorem conj_galileanPhase (t : ℝ) (q : Wavevector) :
    conj (galileanPhase m t q) = galileanPhase m t (-q) := by
  rw [galileanPhase, galileanPhase, conj_phaseFun, modeFunctional_neg]
  congr 1
  ring

theorem galileanPhase_time_zero (q : Wavevector) : galileanPhase m 0 q = 1 := by
  simp [galileanPhase, phaseFun]

theorem modeFunctional_zero (x : ℝ³) : modeFunctional 0 x = 0 := by
  simp [modeFunctional]

theorem galileanPhase_mode_zero (t : ℝ) : galileanPhase m t 0 = 1 := by
  simp [galileanPhase, modeFunctional_zero, phaseFun]

theorem hasDerivAt_galileanPhase (t : ℝ) (q : Wavevector) :
    HasDerivAt (fun τ ↦ galileanPhase m τ q)
      (-(unitTorusDerivativePhase * (modeFunctional q m : ℂ)) * galileanPhase m t q) t := by
  have h1 : HasDerivAt (fun τ : ℝ ↦ unitTorusDerivativePhase * ((-(modeFunctional q m * τ) : ℝ) : ℂ))
      (unitTorusDerivativePhase * ((-(modeFunctional q m * 1) : ℝ) : ℂ)) t :=
    (((hasDerivAt_id t).const_mul (modeFunctional q m)).neg.ofReal_comp).const_mul _
  have h2 := h1.cexp
  simp only [mul_one] at h2
  have e : (fun τ ↦ galileanPhase m τ q) =
      fun τ : ℝ ↦ Complex.exp (unitTorusDerivativePhase * ((-(modeFunctional q m * τ) : ℝ) : ℂ)) :=
    rfl
  rw [e]
  convert h2 using 1
  rw [galileanPhase, phaseFun]
  push_cast
  ring

theorem modeDot_meanCoeff (q : Wavevector) :
    modeDot q (meanCoeff m) = (modeFunctional q m : ℂ) := by
  rw [modeFunctional_apply, realModeDot, modeDot, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [meanCoeff]

theorem coefficientConjugate_meanCoeff : coefficientConjugate (meanCoeff m) = meanCoeff m := by
  ext i
  simp [coefficientConjugate, meanCoeff]

/-- The transport speed of the mean vanishes on the zero mode. -/
theorem modeFunctional_mul_single (q : Wavevector) (v : VelocityCoefficient) :
    (modeFunctional q m : ℂ) • single0 v q = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp [modeFunctional_zero]
  · simp [single0_of_ne _ hq]

end Phase

section Frame

variable (m : ℝ³) (c : ℝ → FourierVelocity)

/-- The Galilean change of frame with mean velocity `m`. -/
def galilean : ℝ → FourierVelocity :=
  fun t q ↦ galileanPhase m t q • c t q + single0 (meanCoeff m) q

theorem galilean_time_zero : galilean m c 0 = c 0 + single0 (meanCoeff m) := by
  funext q
  simp [galilean, galileanPhase_time_zero]

variable {m c}

theorem fourierMoment_single_le (v : VelocityCoefficient) (n : ℕ) (k : Wavevector) :
    fourierMoment n (single0 v) k ≤ ‖coefficientVec v‖ := by
  unfold fourierMoment
  by_cases hk : k = 0
  · subst hk
    have h0 : frequencyVec 0 = 0 := by
      ext i
      simp [frequencyVec, coefficientVec, wavevectorCoefficient]
    simp [h0]
  · have h0 : coefficientVec (single0 v k) = 0 := by
      rw [single0_of_ne _ hk]
      rfl
    rw [h0, norm_zero, mul_zero]
    exact norm_nonneg _

theorem fourierMoment_galilean_le (n : ℕ) (t : ℝ) (k : Wavevector) :
    fourierMoment n (galilean m c t) k ≤ fourierMoment n (c t) k + ‖coefficientVec (meanCoeff m)‖ := by
  have e : coefficientVec (galilean m c t k) = galileanPhase m t k • coefficientVec (c t k) +
      coefficientVec (single0 (meanCoeff m) k) := rfl
  have h1 := fourierMoment_single_le (meanCoeff m) n k
  unfold fourierMoment at h1 ⊢
  rw [e]
  calc (1 + ‖frequencyVec k‖) ^ n * ‖galileanPhase m t k • coefficientVec (c t k) +
        coefficientVec (single0 (meanCoeff m) k)‖
      ≤ (1 + ‖frequencyVec k‖) ^ n * (‖coefficientVec (c t k)‖ +
          ‖coefficientVec (single0 (meanCoeff m) k)‖) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_galileanPhase, one_mul]
    _ = (1 + ‖frequencyVec k‖) ^ n * ‖coefficientVec (c t k)‖ + (1 + ‖frequencyVec k‖) ^ n *
          ‖coefficientVec (single0 (meanCoeff m) k)‖ := by ring
    _ ≤ _ := by gcongr

theorem rapidOn_galilean {s : Set ℝ} (hc : RapidOn c s) : RapidOn (galilean m c) s := by
  intro n
  obtain ⟨C, hC⟩ := hc n
  exact ⟨C + ‖coefficientVec (meanCoeff m)‖, fun t ht k ↦
    (fourierMoment_galilean_le n t k).trans (by linarith [hC t ht k])⟩

theorem rapid_galilean {t : ℝ} (hc : Rapid (c t)) : Rapid (galilean m c t) := by
  intro n
  obtain ⟨C, hC⟩ := hc n
  exact ⟨C + ‖coefficientVec (meanCoeff m)‖, fun k ↦
    (fourierMoment_galilean_le n t k).trans (by linarith [hC k])⟩

theorem galilean_reality (hr : ∀ t q, c t (-q) = coefficientConjugate (c t q)) (t : ℝ)
    (q : Wavevector) : galilean m c t (-q) = coefficientConjugate (galilean m c t q) := by
  ext i
  have hs : single0 (meanCoeff m) (-q) i =
      conj (single0 (meanCoeff m) q i) := by
    by_cases hq : q = 0
    · subst hq
      simp [meanCoeff]
    · have hq' : -q ≠ 0 := neg_ne_zero.mpr hq
      simp [single0_of_ne _ hq, single0_of_ne _ hq']
  simp only [galilean, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coefficientConjugate, hr t q,
    map_add, map_mul, conj_galileanPhase, hs]

theorem galilean_transverse {t : ℝ} (htr : ∀ q, modeDot q (c t q) = 0) (q : Wavevector) :
    modeDot q (galilean m c t q) = 0 := by
  have e : galilean m c t q = galileanPhase m t q • c t q +
      single0 (meanCoeff m) q := rfl
  rw [e]
  simp only [modeDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin 3, (q i : ℂ) * (galileanPhase m t q * c t q i) =
      galileanPhase m t q * modeDot q (c t q) := by
    rw [modeDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h1, htr, mul_zero, zero_add]
  by_cases hq : q = 0
  · subst hq
    simp
  · simp [single0_of_ne _ hq]

theorem galilean_zero_mode {t : ℝ} (hz : c t 0 = 0) : galilean m c t 0 = meanCoeff m := by
  simp [galilean, hz]

theorem galilean_of_ne {t : ℝ} {q : Wavevector} (hq : q ≠ 0) :
    galilean m c t q = galileanPhase m t q • c t q := by
  simp [galilean, single0_of_ne _ hq]

/-- **The convection in the moving frame.** -/
theorem infiniteConvection_galilean {t : ℝ} (hc : Rapid (c t)) (hz : c t 0 = 0)
    (htr : ∀ q, modeDot q (c t q) = 0) (q : Wavevector) :
    infiniteConvection (galilean m c t) q = galileanPhase m t q • infiniteConvection (c t) q +
      (modeFunctional q m : ℂ) • galilean m c t q := by
  have hg := rapid_galilean (m := m) hc
  have hq : galilean m c t q = galileanPhase m t q • c t q +
      single0 (meanCoeff m) q := rfl
  have hterm : ∀ p, modeDot q (galilean m c t p) • galilean m c t (q - p) =
      galileanPhase m t q • (modeDot q (c t p) • c t (q - p)) +
        single0 ((modeFunctional q m : ℂ) • (galileanPhase m t q • c t q)) p := by
    intro p
    by_cases hp : p = 0
    · subst hp
      rw [galilean_zero_mode hz, modeDot_meanCoeff, sub_zero, single0_zero, hz, hq, smul_add,
        modeFunctional_mul_single, add_zero]
      simp [modeDot]
    · rw [galilean_of_ne hp, modeDot_smul, single0_of_ne _ hp, add_zero]
      by_cases hqp : q - p = 0
      · have hpq : q = p := sub_eq_zero.mp hqp
        subst hpq
        simp [htr]
      · rw [galilean_of_ne hqp, smul_smul, smul_smul, ← galileanPhase_mul_sub m t p q]
        congr 1
        ring
  rw [infiniteConvection_eq hg, infiniteConvection_eq hc]
  simp only [hterm]
  have hs0 : Summable (single0 ((modeFunctional q m : ℂ) • (galileanPhase m t q • c t q))) :=
    (hasSum_pi_single (0 : Wavevector) _).summable
  have ht0 : ∑' p, single0 ((modeFunctional q m : ℂ) • (galileanPhase m t q • c t q)) p =
      (modeFunctional q m : ℂ) • (galileanPhase m t q • c t q) := tsum_pi_single _ _
  rw [Summable.tsum_add ((summable_convTerm hc q).const_smul (galileanPhase m t q)) hs0,
    tsum_const_smul'', ht0, hq, smul_add, modeFunctional_mul_single, add_zero]

theorem lerayMode_of_transverse (q : Wavevector) (v : VelocityCoefficient) (hv : modeDot q v = 0) :
    lerayMode q v = v := by
  unfold lerayMode
  split_ifs
  · rfl
  · ext i
    simp [hv]

theorem modeSquare_smul_single (q : Wavevector) (v : VelocityCoefficient) :
    modeSquare q • single0 v q = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp [modeSquare]
  · simp [single0_of_ne _ hq]

/-- **The right-hand side in the moving frame.** -/
theorem rhs_galilean {t : ℝ} (hc : Rapid (c t)) (hz : c t 0 = 0)
    (htr : ∀ q, modeDot q (c t q) = 0) (nu : ℝ) (q : Wavevector) :
    infiniteVelocityRHS nu (galilean m c t) q =
      galileanPhase m t q • infiniteVelocityRHS nu (c t) q -
        (unitTorusDerivativePhase * (modeFunctional q m : ℂ)) • galilean m c t q := by
  have hgt := galilean_transverse (m := m) htr q
  have hq : galilean m c t q = galileanPhase m t q • c t q +
      single0 (meanCoeff m) q := rfl
  have hv : ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • galilean m c t q =
      galileanPhase m t q • (((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • c t q) := by
    rw [hq]
    ext i
    have h0 := congrFun (modeSquare_smul_single q (meanCoeff m)) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 ⊢
    linear_combination ((nu : ℂ) * unitTorusDerivativePhase ^ 2) * h0
  unfold infiniteVelocityRHS unitTorusViscousVorticityCoeff
  rw [infiniteConvection_galilean hc hz htr q, smul_add, lerayMode_add]
  simp only [smul_smul, FourierSymmetry.lerayMode_smul]
  rw [lerayMode_of_transverse q _ hgt, hv]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The moving frame preserves the equation.** -/
theorem hasDerivAt_galilean {nu : ℝ} (h : FourierSolution nu c) (hz : ∀ t, c t 0 = 0) {t : ℝ}
    (ht : 0 < t) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ galilean m c τ q i) (infiniteVelocityRHS nu (galilean m c t) q i) t := by
  have hd := ((hasDerivAt_galileanPhase m t q).mul (h.equation t ht q i)).add_const
    (single0 (meanCoeff m) q i)
  have hδ : (unitTorusDerivativePhase * (modeFunctional q m : ℂ)) *
      single0 (meanCoeff m) q i = 0 := by
    have h0 := congrFun (modeFunctional_mul_single m q (meanCoeff m)) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [mul_assoc, h0, mul_zero]
  have e1 : infiniteVelocityRHS nu (galilean m c t) q i =
      -(unitTorusDerivativePhase * (modeFunctional q m : ℂ)) * galileanPhase m t q * c t q i +
        galileanPhase m t q * infiniteVelocityRHS nu (c t) q i := by
    rw [rhs_galilean (h.rapidAt ht.le) (hz t) (h.transverse t) nu q]
    have hq : galilean m c t q = galileanPhase m t q • c t q + single0 (meanCoeff m) q := rfl
    rw [hq]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-1 : ℂ) * hδ
  rw [e1]
  exact hd

/-- **Galilean invariance of the Fourier solutions.** -/
theorem fourierSolution_galilean {nu : ℝ} (h : FourierSolution nu c) (hz : ∀ t, c t 0 = 0)
    (m : ℝ³) : FourierSolution nu (galilean m c) where
  continuous k i := by
    have hp : Continuous (fun τ ↦ galileanPhase m τ k) :=
      contDiff_phaseFun.continuous.comp (by fun_prop)
    exact (hp.mul (h.continuous k i)).add continuous_const
  rapid S hS := rapidOn_galilean (h.rapid S hS)
  reality := galilean_reality h.reality
  transverse t q := galilean_transverse (h.transverse t) q
  equation t ht q i := hasDerivAt_galilean h hz ht q i

theorem rapid_single (v : VelocityCoefficient) : Rapid (single0 v) :=
  fun n ↦ ⟨‖coefficientVec v‖, fun k ↦ fourierMoment_single_le v n k⟩

theorem character_zero (x : ℝ³) : character 0 x = 1 := by
  simp [character, modeFunctional_zero, phaseFun]

theorem field_single (v : VelocityCoefficient) (x : ℝ³) :
    field (single0 v) x = v := by
  unfold field
  rw [tsum_eq_single 0 fun k hk ↦ by simp [single0_of_ne _ hk]]
  simp [character_zero]

/-- The initial velocity in the moving frame is the mean plus the initial
velocity of the zero-mean solution. -/
theorem physVelocity_galilean_zero (hc : Rapid (c 0)) (x : ℝ³) :
    physVelocity (galilean m c) x 0 = m + physVelocity c x 0 := by
  have hm : complexRealPartEuclideanCLM (meanCoeff m) = m := by
    ext i
    rw [realPart_apply]
    simp [meanCoeff]
  rw [physVelocity_eq, physVelocity_eq, galilean_time_zero, realField, realField,
    field_add hc (rapid_single _), map_add, field_single, hm, add_comm]

end Frame

end Mettapedia.FluidDynamics.NavierStokes.FourierGalilean
