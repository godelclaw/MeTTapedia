import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticitySource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRealCoherentPairEstimate

/-!
# Coherent pair depletion of the periodic stretching amplitude

The coherent pair estimate of the route was proved in a real three-vector
model: two direction-coherent modes inside pancake cones of squared apertures
`d₁, d₂ ≤ 1/4` stretch each other with squared normalized coefficient at most
`6 (d₁ + d₂)`. This module transports it to the actual periodic amplitudes
acting on the coherent components of complex lattice coefficients:

```text
|S(u_p^c) ω_r^c| ≤ √(6 (d₁ + d₂)) |ω_p^c| |ω_r^c|,
```

where `ω^c` is the coherent component of the lattice split (the projection on
the Leray image of the reference direction). The bridge is the
complexification of the real model: the periodic coherent mode is the Leray
image of the reference, hence a real multiple of the model's coherent
polarization, and the complex stretching amplitude of real vectors is the
complexified model amplitude. Summed over the pairs of two finite mode sets
in cones, the coherent–coherent stretching is bounded by the aperture gain
times the product of the Wiener norms of the coherent components.

This is the kinematic depletion on actual coefficients. It is not a
dynamical estimate: the Wiener norms on the right are those of the solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierCoherentDepletion

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open PancakeInfinitePressureCoefficients

section Complexification

/-- The complexification of a real three-vector of the model. -/
def toCoeff (v : PancakeRealCoherentPairEstimate.RealVec3) : VelocityCoefficient :=
  ![(v.1 : ℂ), (v.2.1 : ℂ), (v.2.2 : ℂ)]

/-- The real three-vector of a wavevector. -/
def toReal (k : Wavevector) : PancakeRealCoherentPairEstimate.RealVec3 :=
  ((k 0 : ℝ), (k 1 : ℝ), (k 2 : ℝ))

theorem toCoeff_wavevector (k : Wavevector) : toCoeff (toReal k) = wavevectorCoefficient k := by
  ext i
  fin_cases i <;> simp [toCoeff, toReal, wavevectorCoefficient]

theorem normSq_toReal (k : Wavevector) :
    PancakeRealCoherentPairEstimate.normSq (toReal k) = ‖frequencyVec k‖ ^ 2 := by
  rw [norm_frequencyVec_sq, Fin.sum_univ_three]
  simp [PancakeRealCoherentPairEstimate.normSq, PancakeRealCoherentPairEstimate.dot, toReal, sq]

theorem modeSquare_eq_normSq (k : Wavevector) :
    modeSquare k = ((PancakeRealCoherentPairEstimate.normSq (toReal k) : ℝ) : ℂ) := by
  simp [modeSquare, PancakeRealCoherentPairEstimate.normSq, PancakeRealCoherentPairEstimate.dot,
    toReal, Fin.sum_univ_three]

theorem norm_cv_toCoeff (v : PancakeRealCoherentPairEstimate.RealVec3) :
    ‖coefficientVec (toCoeff v)‖ = Real.sqrt (PancakeRealCoherentPairEstimate.normSq v) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [toCoeff, coefficientVec, PancakeRealCoherentPairEstimate.normSq,
    PancakeRealCoherentPairEstimate.dot, Fin.sum_univ_three, sq]
  try ring

theorem norm_cv_neg (v : VelocityCoefficient) : ‖coefficientVec (-v)‖ = ‖coefficientVec v‖ := by
  have e : coefficientVec (-v) = -coefficientVec v := rfl
  rw [e, norm_neg]

theorem normSq_nonneg' (v : PancakeRealCoherentPairEstimate.RealVec3) :
    0 ≤ PancakeRealCoherentPairEstimate.normSq v :=
  PancakeRealCoherentPairEstimate.normSq_nonneg v

theorem toCoeff_smul (c : ℝ) (v : PancakeRealCoherentPairEstimate.RealVec3) :
    toCoeff (PancakeRealCoherentPairEstimate.smul c v) = (c : ℂ) • toCoeff v := by
  ext i
  fin_cases i <;> simp [toCoeff, PancakeRealCoherentPairEstimate.smul]

theorem toCoeff_add (v w : PancakeRealCoherentPairEstimate.RealVec3) :
    toCoeff (PancakeRealCoherentPairEstimate.add v w) = toCoeff v + toCoeff w := by
  ext i
  fin_cases i <;> simp [toCoeff, PancakeRealCoherentPairEstimate.add]

theorem coefficientDot_toCoeff (v w : PancakeRealCoherentPairEstimate.RealVec3) :
    coefficientDot (toCoeff v) (toCoeff w) = ((PancakeRealCoherentPairEstimate.dot v w : ℝ) : ℂ) := by
  simp [coefficientDot, toCoeff, PancakeRealCoherentPairEstimate.dot, Fin.sum_univ_three]

theorem modeDot_toCoeff (k : Wavevector) (w : PancakeRealCoherentPairEstimate.RealVec3) :
    modeDot k (toCoeff w) = ((PancakeRealCoherentPairEstimate.dot (toReal k) w : ℝ) : ℂ) := by
  simp [modeDot, toCoeff, toReal, PancakeRealCoherentPairEstimate.dot, Fin.sum_univ_three]

theorem cross_toCoeff (v w : PancakeRealCoherentPairEstimate.RealVec3) :
    coefficientCross (toCoeff v) (toCoeff w) = toCoeff (PancakeRealCoherentPairEstimate.cross v w) := by
  ext i
  fin_cases i <;> simp [coefficientCross, toCoeff, PancakeRealCoherentPairEstimate.cross]

theorem complexBiotSavartAmp_toCoeff (k : Wavevector) (w : PancakeRealCoherentPairEstimate.RealVec3) :
    complexBiotSavartAmp k (toCoeff w) =
      toCoeff (PancakeRealCoherentPairEstimate.biotSavartAmp (toReal k) w) := by
  unfold complexBiotSavartAmp PancakeRealCoherentPairEstimate.biotSavartAmp
  rw [← toCoeff_wavevector, cross_toCoeff, toCoeff_smul, modeSquare_eq_normSq]
  push_cast
  rfl

/-- The complex stretching amplitude of real vectors is the complexified model amplitude. -/
theorem complexStretchAmp_toCoeff (k : Wavevector) (w₁ w₂ : PancakeRealCoherentPairEstimate.RealVec3) :
    complexStretchAmp k (toCoeff w₁) (toCoeff w₂) =
      toCoeff (PancakeRealCoherentPairEstimate.stretchAmp (toReal k) w₁ w₂) := by
  simp only [complexStretchAmp, PancakeRealCoherentPairEstimate.stretchAmp]
  rw [complexBiotSavartAmp_toCoeff, coefficientDot_toCoeff, modeDot_toCoeff, toCoeff_smul,
    toCoeff_add, toCoeff_smul, toCoeff_smul, toCoeff_wavevector]
  push_cast
  rfl

/-- The periodic coherent mode is the model's coherent polarization scaled by `|k|⁻²`. -/
theorem periodicCoherentMode_eq (k : Wavevector) (hk : k ≠ 0) :
    periodicCoherentMode k =
      (1 / modeSquare k) • toCoeff (PancakeRealCoherentPairEstimate.coherentW (toReal k)) := by
  have hks : modeSquare k ≠ 0 := modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hk)
  have hn : ((PancakeRealCoherentPairEstimate.normSq (toReal k) : ℝ) : ℂ) ≠ 0 := by
    rw [← modeSquare_eq_normSq]
    exact hks
  have e : modeDot k referenceCoefficient = (k 0 : ℂ) := by
    simp [modeDot, referenceCoefficient, Fin.sum_univ_three]
  unfold periodicCoherentMode lerayMode
  rw [dite_eq_right hks, e, modeSquare_eq_normSq]
  simp only [PancakeRealCoherentPairEstimate.coherentW, PancakeRealCoherentPairEstimate.add,
    PancakeRealCoherentPairEstimate.smul, PancakeRealCoherentPairEstimate.dot,
    PancakeRealCoherentPairEstimate.ex]
  generalize hN : PancakeRealCoherentPairEstimate.normSq (toReal k) = N at hn ⊢
  ext i
  fin_cases i <;>
    simp [toCoeff, toReal, referenceCoefficient] <;>
    field_simp <;>
    ring

theorem coherentComponent_eq (k : Wavevector) (hk : k ≠ 0) (w : VelocityCoefficient) :
    coherentComponent k w = (coherentScalar k w / modeSquare k) •
      toCoeff (PancakeRealCoherentPairEstimate.coherentW (toReal k)) := by
  unfold coherentComponent
  rw [periodicCoherentMode_eq k hk, smul_smul]
  congr 1
  ring

theorem complexStretchAmp_smul_smul (k : Wavevector) (a b : ℂ) (w₁ w₂ : VelocityCoefficient) :
    complexStretchAmp k (a • w₁) (b • w₂) = (a * b) • complexStretchAmp k w₁ w₂ := by
  simp only [complexStretchAmp, complexBiotSavartAmp_smul, coefficientDot_smul_left,
    coefficientDot_smul_right, modeDot_smul]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

end Complexification

section Pair

/-- The pancake cone of squared aperture `d` about the third axis. -/
def InCone (d : ℝ) (k : Wavevector) : Prop :=
  (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 ≤ d * ‖frequencyVec k‖ ^ 2

theorem inCone_toReal {d : ℝ} {k : Wavevector} (h : InCone d k) :
    (toReal k).1 ^ 2 + (toReal k).2.1 ^ 2 ≤ d * PancakeRealCoherentPairEstimate.normSq (toReal k) := by
  rw [normSq_toReal]
  exact h

/-- **Coherent pair depletion for the periodic stretching amplitude.** -/
theorem norm_stretch_coherent_le {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0) {d₁ d₂ : ℝ}
    (hc₁ : InCone d₁ p) (hc₂ : InCone d₂ r) (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4)
    (w₁ w₂ : VelocityCoefficient) :
    ‖coefficientVec (unitTorusStrainStretchAmp p (coherentComponent p w₁)
        (coherentComponent r w₂))‖ ≤
      Real.sqrt (6 * (d₁ + d₂)) * ‖coefficientVec (coherentComponent p w₁)‖ *
        ‖coefficientVec (coherentComponent r w₂)‖ := by
  have hkp : PancakeRealCoherentPairEstimate.normSq (toReal p) ≠ 0 := by
    rw [normSq_toReal]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (frequencyVec_ne_zero hp))
  have hkr : PancakeRealCoherentPairEstimate.normSq (toReal r) ≠ 0 := by
    rw [normSq_toReal]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (frequencyVec_ne_zero hr))
  have hmodel := PancakeRealCoherentPairEstimate.normSq_stretchAmp_coherent_le (toReal p) (toReal r)
    d₁ d₂ hkp hkr (inCone_toReal hc₁) (inCone_toReal hc₂) hd₁ hd₂
  set a : ℂ := coherentScalar p w₁ / modeSquare p
  set b : ℂ := coherentScalar r w₂ / modeSquare r
  set W₁ := PancakeRealCoherentPairEstimate.coherentW (toReal p)
  set W₂ := PancakeRealCoherentPairEstimate.coherentW (toReal r)
  have e : unitTorusStrainStretchAmp p (coherentComponent p w₁) (coherentComponent r w₂) =
      -((a * b) • toCoeff (PancakeRealCoherentPairEstimate.stretchAmp (toReal p) W₁ W₂)) := by
    rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp, coherentComponent_eq p hp,
      coherentComponent_eq r hr, complexStretchAmp_smul_smul, complexStretchAmp_toCoeff]
  have hn1 : ‖coefficientVec (coherentComponent p w₁)‖ = ‖a‖ * Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₁) := by
    rw [coherentComponent_eq p hp, FourierVorticitySource.norm_cv_smul, norm_cv_toCoeff]
  have hn2 : ‖coefficientVec (coherentComponent r w₂)‖ = ‖b‖ * Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₂) := by
    rw [coherentComponent_eq r hr, FourierVorticitySource.norm_cv_smul, norm_cv_toCoeff]
  have hd0 : 0 ≤ 6 * (d₁ + d₂) := by
    have h1 : 0 ≤ d₁ * PancakeRealCoherentPairEstimate.normSq (toReal p) :=
      le_trans (by positivity) (inCone_toReal hc₁)
    have h2 : 0 ≤ d₂ * PancakeRealCoherentPairEstimate.normSq (toReal r) :=
      le_trans (by positivity) (inCone_toReal hc₂)
    have hp0 : 0 < PancakeRealCoherentPairEstimate.normSq (toReal p) :=
      lt_of_le_of_ne (normSq_nonneg' _) (Ne.symm hkp)
    have hr0 : 0 < PancakeRealCoherentPairEstimate.normSq (toReal r) :=
      lt_of_le_of_ne (normSq_nonneg' _) (Ne.symm hkr)
    have := nonneg_of_mul_nonneg_left h1 hp0
    have := nonneg_of_mul_nonneg_left h2 hr0
    linarith
  rw [e, norm_cv_neg, FourierVorticitySource.norm_cv_smul, norm_cv_toCoeff, norm_mul, hn1, hn2]
  have hsq : Real.sqrt (PancakeRealCoherentPairEstimate.normSq
      (PancakeRealCoherentPairEstimate.stretchAmp (toReal p) W₁ W₂)) ≤
      Real.sqrt (6 * (d₁ + d₂)) * Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₁) *
        Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₂) := by
    rw [← Real.sqrt_mul hd0, ← Real.sqrt_mul (mul_nonneg hd0 (normSq_nonneg' _))]
    exact Real.sqrt_le_sqrt hmodel
  calc ‖a‖ * ‖b‖ * Real.sqrt (PancakeRealCoherentPairEstimate.normSq
        (PancakeRealCoherentPairEstimate.stretchAmp (toReal p) W₁ W₂))
      ≤ ‖a‖ * ‖b‖ * (Real.sqrt (6 * (d₁ + d₂)) *
          Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₁) *
          Real.sqrt (PancakeRealCoherentPairEstimate.normSq W₂)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end Pair

section Sums

variable {u : FourierVelocity}

/-- The coherent–coherent stretching of the sources `P` onto the receivers `R`
at output `k`. -/
def coherentStretch (ω : FourierVelocity) (P R : Finset Wavevector) (k : Wavevector) :
    VelocityCoefficient :=
  ∑ p ∈ P.filter (fun p ↦ k - p ∈ R),
    unitTorusStrainStretchAmp p (coherentComponent p (ω p)) (coherentComponent (k - p) (ω (k - p)))

/-- The Wiener norm of the coherent components over a finite set. -/
def coherentMass (ω : FourierVelocity) (S : Finset Wavevector) : ℝ :=
  ∑ p ∈ S, ‖coefficientVec (coherentComponent p (ω p))‖

theorem coherentMass_nonneg (ω : FourierVelocity) (S : Finset Wavevector) : 0 ≤ coherentMass ω S :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- **The coherent–coherent stretching over any set of outputs is bounded by
the aperture gain times the product of the coherent Wiener norms.** -/
theorem sum_norm_coherentStretch_le (ω : FourierVelocity) (P R K : Finset Wavevector) {d₁ d₂ : ℝ}
    (hP0 : (0 : Wavevector) ∉ P) (hR0 : (0 : Wavevector) ∉ R)
    (hP : ∀ p ∈ P, InCone d₁ p) (hR : ∀ r ∈ R, InCone d₂ r) (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    ∑ k ∈ K, ‖coefficientVec (coherentStretch ω P R k)‖ ≤
      Real.sqrt (6 * (d₁ + d₂)) * coherentMass ω P * coherentMass ω R := by
  -- the pair bound
  have hpair : ∀ p ∈ P, ∀ r ∈ R, ‖coefficientVec (unitTorusStrainStretchAmp p
      (coherentComponent p (ω p)) (coherentComponent r (ω r)))‖ ≤
      Real.sqrt (6 * (d₁ + d₂)) * ‖coefficientVec (coherentComponent p (ω p))‖ *
        ‖coefficientVec (coherentComponent r (ω r))‖ := fun p hp r hr ↦
    norm_stretch_coherent_le (fun h ↦ hP0 (h ▸ hp)) (fun h ↦ hR0 (h ▸ hr)) (hP p hp)
      (hR r hr) hd₁ hd₂ (ω p) (ω r)
  -- pointwise, the triangle inequality
  have hpt : ∀ k ∈ K, ‖coefficientVec (coherentStretch ω P R k)‖ ≤
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ R), Real.sqrt (6 * (d₁ + d₂)) *
        ‖coefficientVec (coherentComponent p (ω p))‖ *
          ‖coefficientVec (coherentComponent (k - p) (ω (k - p)))‖ := by
    intro k _
    unfold coherentStretch
    rw [PancakeFixedOutputVelocityBound.coefficientVec_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    have hp' := Finset.mem_filter.mp hp
    exact hpair p hp'.1 (k - p) hp'.2
  refine (Finset.sum_le_sum hpt).trans ?_
  set m : Wavevector → ℝ := fun p ↦ ‖coefficientVec (coherentComponent p (ω p))‖ with hm
  set c := Real.sqrt (6 * (d₁ + d₂)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hm0 : ∀ p, 0 ≤ m p := fun p ↦ norm_nonneg _
  -- swap the sums and drop the output constraint
  have hswap : ∑ k ∈ K, ∑ p ∈ P.filter (fun p ↦ k - p ∈ R), c * m p * m (k - p) =
      ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ R), c * m p * m (k - p) := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  have hinner : ∀ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ R), c * m p * m (k - p) ≤
      ∑ r ∈ R, c * m p * m r := by
    intro p _
    have hinj : Set.InjOn (fun k ↦ k - p) ↑(K.filter (fun k ↦ k - p ∈ R)) :=
      fun _ _ _ _ h ↦ sub_left_injective h
    rw [← Finset.sum_image (f := fun r ↦ c * m p * m r) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ ↦ by positivity
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact (Finset.mem_filter.mp hk).2
  calc ∑ k ∈ K, ∑ p ∈ P.filter (fun p ↦ k - p ∈ R), c * m p * m (k - p)
      = ∑ p ∈ P, ∑ k ∈ K.filter (fun k ↦ k - p ∈ R), c * m p * m (k - p) := hswap
    _ ≤ ∑ p ∈ P, ∑ r ∈ R, c * m p * m r := Finset.sum_le_sum hinner
    _ = c * coherentMass ω P * coherentMass ω R := by
        unfold coherentMass
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        ring

end Sums

end Mettapedia.FluidDynamics.NavierStokes.FourierCoherentDepletion
