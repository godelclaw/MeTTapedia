import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierRegularityEquivalence

/-!
# Translation and reflection symmetry of the Fourier solutions

A translation of the torus in the third coordinate multiplies each Fourier
coefficient by the phase `exp(2π i k₂ a)`; the reflection `x₂ ↦ -x₂` sends the
coefficient at `k` to `D u_{Rk}`, where `R` and `D` flip the third
coordinate. The infinite right-hand side is equivariant under both, and every
energy functional is invariant, so each maps tame solutions to tame
solutions. With uniqueness, data invariant under a symmetry have solutions
invariant under it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSymmetry

open scoped BigOperators ComplexConjugate
open Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeBlockReality PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open FourierContinuation FourierTameContinuation FourierUniqueness

section Linear

theorem modeDot_smul (k : Wavevector) (c : ℂ) (v : VelocityCoefficient) :
    modeDot k (c • v) = c * modeDot k v := by
  simp only [modeDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem lerayMode_smul (k : Wavevector) (c : ℂ) (v : VelocityCoefficient) :
    lerayMode k (c • v) = c • lerayMode k v := by
  unfold lerayMode
  split_ifs
  · rfl
  · ext i
    simp only [Pi.smul_apply, smul_eq_mul, modeDot_smul]
    ring

theorem amplitude_smul_of_norm_one (u : FourierVelocity) (c : Wavevector → ℂ)
    (hc : ∀ k, ‖c k‖ = 1) : amplitude (fun k ↦ c k • u k) = amplitude u := by
  funext k
  change ‖coefficientVec (c k • u k)‖ = ‖coefficientVec (u k)‖
  have h : coefficientVec (c k • u k) = c k • coefficientVec (u k) := rfl
  rw [h, norm_smul, hc k, one_mul]

end Linear

section Translation

/-- The phase of the translation by `a` in the third coordinate. -/
def zPhase (a : ℝ) (k : Wavevector) : ℂ :=
  Complex.exp (((2 * Real.pi * (k 2 : ℝ) * a : ℝ) : ℂ) * Complex.I)

theorem norm_zPhase (a : ℝ) (k : Wavevector) : ‖zPhase a k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem zPhase_add (a : ℝ) (p q : Wavevector) :
    zPhase a (p + q) = zPhase a p * zPhase a q := by
  unfold zPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  push_cast
  ring

theorem zPhase_zero (a : ℝ) : zPhase a 0 = 1 := by
  simp [zPhase]

theorem zPhase_neg (a : ℝ) (k : Wavevector) : zPhase a (-k) = conj (zPhase a k) := by
  unfold zPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [Pi.neg_apply, Int.cast_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem zPhase_eq_one_of (a : ℝ) {k : Wavevector} (hk : k 2 = 0) : zPhase a k = 1 := by
  simp [zPhase, hk]

theorem zPhase_half (k : Wavevector) (hk : k 2 ≠ 0) : zPhase (1 / (2 * (k 2 : ℝ))) k = -1 := by
  have hk' : ((k 2 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold zPhase
  have e : (2 * Real.pi * (k 2 : ℝ) * (1 / (2 * (k 2 : ℝ))) : ℝ) = Real.pi := by
    field_simp
  rw [e]
  exact Complex.exp_pi_mul_I

/-- The translation of a Fourier field by `a` in the third coordinate. -/
def shiftZ (a : ℝ) (u : FourierVelocity) : FourierVelocity := fun k ↦ zPhase a k • u k

theorem amplitude_shiftZ (a : ℝ) (u : FourierVelocity) : amplitude (shiftZ a u) = amplitude u :=
  amplitude_smul_of_norm_one u (zPhase a) (norm_zPhase a)

theorem velocityEnergy_shiftZ (a : ℝ) (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy m F (shiftZ a u) = velocityEnergy m F u := by
  simp only [velocityEnergy, amplitude_shiftZ]

theorem velocityDissipation_shiftZ (a : ℝ) (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    velocityDissipation m F (shiftZ a u) = velocityDissipation m F u := by
  simp only [velocityDissipation, amplitude_shiftZ]

theorem sobolevEnergy_shiftZ (a : ℝ) (F : Finset Wavevector) (u : FourierVelocity) :
    sobolevEnergy F (shiftZ a u) = sobolevEnergy F u := by
  simp only [sobolevEnergy, amplitude_shiftZ]

theorem infiniteConvection_shiftZ (a : ℝ) (u : FourierVelocity) (k : Wavevector) :
    infiniteConvection (shiftZ a u) k = zPhase a k • infiniteConvection u k := by
  funext i
  simp only [infiniteConvection, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  simp only [outputFiber, shiftZ, modeDot_smul, Pi.smul_apply, smul_eq_mul]
  have h : zPhase a p * zPhase a (k - p) = zPhase a k := by
    rw [← zPhase_add, add_sub_cancel]
  rw [← h]
  ring

theorem infiniteVelocityRHS_shiftZ (nu a : ℝ) (u : FourierVelocity) (k : Wavevector) :
    infiniteVelocityRHS nu (shiftZ a u) k = zPhase a k • infiniteVelocityRHS nu u k := by
  simp only [infiniteVelocityRHS, infiniteConvection_shiftZ, smul_comm (-unitTorusDerivativePhase)
    (zPhase a k), lerayMode_smul, unitTorusViscousVorticityCoeff, shiftZ, smul_add]
  congr 1
  exact smul_comm _ _ _

theorem shiftZ_reality (a : ℝ) {u : FourierVelocity}
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) :
    shiftZ a u (-k) = coefficientConjugate (shiftZ a u k) := by
  ext i
  simp only [shiftZ, hr k, zPhase_neg, coefficientConjugate, Pi.smul_apply, smul_eq_mul, map_mul]

/-- The translated tame solution, for data invariant under the translation. -/
def TameSolutionOn.shiftZ {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (a : ℝ) (h : FourierSymmetry.shiftZ a u₀ = u₀) :
    TameSolutionOn nu m u₀ T where
  coefficients := fun t ↦ FourierSymmetry.shiftZ a (c.coefficients t)
  continuous := fun q i ↦ continuous_const.mul (c.continuous q i)
  initial := by
    rw [c.initial, h]
  reality := fun t q ↦ shiftZ_reality a (c.reality t) q
  transverse := fun t q ↦ by
    simp only [FourierSymmetry.shiftZ, modeDot_smul, c.transverse t q, mul_zero]
  zero := fun t ↦ by simp [FourierSymmetry.shiftZ, c.zero t]
  sobolev_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.sobolev_local S hS
    exact ⟨B, fun t ht F ↦ by rw [sobolevEnergy_shiftZ]; exact hB t ht F⟩
  equation := fun t ht q i ↦ by
    have h := (c.equation t ht q i).const_mul (zPhase a q)
    rw [infiniteVelocityRHS_shiftZ]
    exact h
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local S hS
    exact ⟨B, fun t ht F ↦ by rw [velocityEnergy_shiftZ]; exact hB t ht F⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local S hS
    exact ⟨X, fun G ↦ by simp only [velocityDissipation_shiftZ]; exact hX G⟩

/-- **Translation invariance.** A tame solution with translation-invariant data is
translation invariant. -/
theorem shiftZ_coefficients_eq {m : ℕ} (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu) {u₀ : FourierVelocity}
    {T : ℝ} (c : TameSolutionOn nu m u₀ T) (a : ℝ) (h : shiftZ a u₀ = u₀) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : shiftZ a (c.coefficients t) = c.coefficients t :=
  FourierUniqueness.TameSolutionOn.coefficients_eq hm hnu (TameSolutionOn.shiftZ c a h) c t ht

end Translation

section Reflection

/-- The reflection of a wavevector in its third coordinate. -/
def reflectVec (k : Wavevector) : Wavevector := ![k 0, k 1, -k 2]

/-- The reflection of a coefficient in its third component. -/
def reflectCoeff (v : VelocityCoefficient) : VelocityCoefficient := ![v 0, v 1, -v 2]

@[simp] theorem reflectVec_zero_apply (k : Wavevector) : reflectVec k 0 = k 0 := rfl
@[simp] theorem reflectVec_one_apply (k : Wavevector) : reflectVec k 1 = k 1 := rfl
@[simp] theorem reflectVec_two_apply (k : Wavevector) : reflectVec k 2 = -k 2 := rfl
@[simp] theorem reflectCoeff_zero_apply (v : VelocityCoefficient) : reflectCoeff v 0 = v 0 := rfl
@[simp] theorem reflectCoeff_one_apply (v : VelocityCoefficient) : reflectCoeff v 1 = v 1 := rfl
@[simp] theorem reflectCoeff_two_apply (v : VelocityCoefficient) : reflectCoeff v 2 = -v 2 := rfl

theorem reflectVec_reflectVec (k : Wavevector) : reflectVec (reflectVec k) = k := by
  funext i
  fin_cases i <;> simp

theorem reflectVec_sub (p q : Wavevector) : reflectVec (p - q) = reflectVec p - reflectVec q := by
  funext i
  fin_cases i <;> simp
  ring

theorem reflectVec_neg (k : Wavevector) : reflectVec (-k) = -reflectVec k := by
  funext i
  fin_cases i <;> simp

theorem reflectVec_zero : reflectVec 0 = 0 := by
  funext i
  fin_cases i <;> simp

/-- The reflection as an involutive equivalence. -/
def reflectEquiv : Wavevector ≃ Wavevector where
  toFun := reflectVec
  invFun := reflectVec
  left_inv := reflectVec_reflectVec
  right_inv := reflectVec_reflectVec

theorem reflectVec_injective : Function.Injective reflectVec := reflectEquiv.injective

theorem modeDot_reflectCoeff (k : Wavevector) (v : VelocityCoefficient) :
    modeDot k (reflectCoeff v) = modeDot (reflectVec k) v := by
  simp only [modeDot, Fin.sum_univ_three, reflectCoeff_zero_apply, reflectCoeff_one_apply,
    reflectCoeff_two_apply, reflectVec_zero_apply, reflectVec_one_apply, reflectVec_two_apply]
  push_cast
  ring

theorem modeSquare_reflectVec (k : Wavevector) : modeSquare (reflectVec k) = modeSquare k := by
  simp only [modeSquare, Fin.sum_univ_three, reflectVec_zero_apply, reflectVec_one_apply,
    reflectVec_two_apply]
  push_cast
  ring

theorem norm_frequencyVec_reflectVec (k : Wavevector) :
    ‖frequencyVec (reflectVec k)‖ = ‖frequencyVec k‖ := by
  have h : ‖frequencyVec (reflectVec k)‖ ^ 2 = ‖frequencyVec k‖ ^ 2 := by
    rw [norm_frequencyVec_sq, norm_frequencyVec_sq]
    simp only [Fin.sum_univ_three, reflectVec_zero_apply, reflectVec_one_apply,
      reflectVec_two_apply]
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem reflectCoeff_add (v w : VelocityCoefficient) :
    reflectCoeff (v + w) = reflectCoeff v + reflectCoeff w := by
  funext i
  fin_cases i <;> simp
  ring

theorem reflectCoeff_smul (c : ℂ) (v : VelocityCoefficient) :
    reflectCoeff (c • v) = c • reflectCoeff v := by
  funext i
  fin_cases i <;> simp

theorem coefficientEnergy_reflectCoeff (v : VelocityCoefficient) :
    coefficientEnergy (reflectCoeff v) = coefficientEnergy v := by
  simp [coefficientEnergy, Fin.sum_univ_three]

/-- The reflection of a Fourier field in the third coordinate. -/
def reflectZ (u : FourierVelocity) : FourierVelocity := fun k ↦ reflectCoeff (u (reflectVec k))

theorem amplitude_reflectZ (u : FourierVelocity) (k : Wavevector) :
    amplitude (reflectZ u) k = amplitude u (reflectVec k) := by
  change ‖coefficientVec (reflectCoeff (u (reflectVec k)))‖ = ‖coefficientVec (u (reflectVec k))‖
  rw [← Real.sqrt_sq (norm_nonneg (coefficientVec (reflectCoeff _))),
    ← Real.sqrt_sq (norm_nonneg (coefficientVec (u (reflectVec k)))),
    norm_coefficientVec_sq, norm_coefficientVec_sq, coefficientEnergy_reflectCoeff]

theorem orderWeight_reflectVec (m : ℕ) (k : Wavevector) :
    orderWeight m (reflectVec k) = orderWeight m k := by
  simp only [orderWeight, norm_frequencyVec_reflectVec]

theorem weight_reflectVec (k : Wavevector) : weight (reflectVec k) = weight k := by
  simp only [weight, norm_frequencyVec_reflectVec]

theorem velocityEnergy_reflectZ (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy m F (reflectZ u) = velocityEnergy m (F.image reflectVec) u := by
  unfold velocityEnergy orderEnergy
  rw [Finset.sum_image (fun x _ y _ h ↦ reflectVec_injective h)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [amplitude_reflectZ, orderWeight_reflectVec]

theorem velocityDissipation_reflectZ (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    velocityDissipation m F (reflectZ u) = velocityDissipation m (F.image reflectVec) u := by
  unfold velocityDissipation orderDissipation orderEnergy
  rw [Finset.sum_image (fun x _ y _ h ↦ reflectVec_injective h)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [amplitude_reflectZ, orderWeight_reflectVec, norm_frequencyVec_reflectVec]

theorem sobolevEnergy_reflectZ (F : Finset Wavevector) (u : FourierVelocity) :
    sobolevEnergy F (reflectZ u) = sobolevEnergy (F.image reflectVec) u := by
  unfold sobolevEnergy energy
  rw [Finset.sum_image (fun x _ y _ h ↦ reflectVec_injective h)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [amplitude_reflectZ, weight_reflectVec]

theorem outputFiber_reflectZ (u : FourierVelocity) (k p : Wavevector) (i : Fin 3) :
    outputFiber k (reflectZ u) p i =
      reflectCoeff (fun j ↦ outputFiber (reflectVec k) u (reflectVec p) j) i := by
  simp only [outputFiber, reflectZ, modeDot_reflectCoeff, reflectVec_sub]
  fin_cases i <;> simp

theorem infiniteConvection_reflectZ (u : FourierVelocity) (k : Wavevector) :
    infiniteConvection (reflectZ u) k = reflectCoeff (infiniteConvection u (reflectVec k)) := by
  have hre (i : Fin 3) : (∑' p, outputFiber (reflectVec k) u (reflectVec p) i) =
      infiniteConvection u (reflectVec k) i :=
    reflectEquiv.tsum_eq (fun p ↦ outputFiber (reflectVec k) u p i)
  funext i
  have hL : infiniteConvection (reflectZ u) k i =
      ∑' p, reflectCoeff (fun j ↦ outputFiber (reflectVec k) u (reflectVec p) j) i := by
    simp only [infiniteConvection, outputFiber_reflectZ]
  rw [hL]
  fin_cases i
  · simpa using hre 0
  · simpa using hre 1
  · simp only [Fin.reduceFinMk, Fin.isValue, reflectCoeff_two_apply, tsum_neg]
    rw [hre 2]

theorem lerayMode_reflectCoeff (k : Wavevector) (v : VelocityCoefficient) :
    lerayMode k (reflectCoeff v) = reflectCoeff (lerayMode (reflectVec k) v) := by
  unfold lerayMode
  rw [modeSquare_reflectVec]
  split_ifs
  · rfl
  · funext i
    rw [modeDot_reflectCoeff]
    fin_cases i <;> simp
    ring

theorem infiniteVelocityRHS_reflectZ (nu : ℝ) (u : FourierVelocity) (k : Wavevector) :
    infiniteVelocityRHS nu (reflectZ u) k = reflectCoeff (infiniteVelocityRHS nu u (reflectVec k)) := by
  simp only [infiniteVelocityRHS, infiniteConvection_reflectZ, ← reflectCoeff_smul,
    lerayMode_reflectCoeff, reflectCoeff_add, unitTorusViscousVorticityCoeff, reflectZ,
    modeSquare_reflectVec]

theorem reflectZ_reality {u : FourierVelocity}
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) :
    reflectZ u (-k) = coefficientConjugate (reflectZ u k) := by
  ext i
  simp only [reflectZ, reflectVec_neg, hr]
  fin_cases i <;> simp [coefficientConjugate]

/-- The reflected tame solution, for data invariant under the reflection. -/
def TameSolutionOn.reflectZ {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (h : FourierSymmetry.reflectZ u₀ = u₀) :
    TameSolutionOn nu m u₀ T where
  coefficients := fun t ↦ FourierSymmetry.reflectZ (c.coefficients t)
  continuous := fun q i ↦ by
    fin_cases i
    · exact c.continuous (reflectVec q) 0
    · exact c.continuous (reflectVec q) 1
    · exact (c.continuous (reflectVec q) 2).neg
  initial := by
    rw [c.initial, h]
  reality := fun t q ↦ reflectZ_reality (c.reality t) q
  transverse := fun t q ↦ by
    simp only [FourierSymmetry.reflectZ, modeDot_reflectCoeff, c.transverse t (reflectVec q)]
  zero := fun t ↦ by
    simp only [FourierSymmetry.reflectZ, reflectVec_zero, c.zero t]
    funext i
    fin_cases i <;> simp
  sobolev_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.sobolev_local S hS
    exact ⟨B, fun t ht F ↦ by rw [sobolevEnergy_reflectZ]; exact hB t ht _⟩
  equation := fun t ht q i ↦ by
    rw [infiniteVelocityRHS_reflectZ]
    fin_cases i
    · exact c.equation t ht (reflectVec q) 0
    · exact c.equation t ht (reflectVec q) 1
    · exact (c.equation t ht (reflectVec q) 2).neg
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local S hS
    exact ⟨B, fun t ht F ↦ by rw [velocityEnergy_reflectZ]; exact hB t ht _⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local S hS
    exact ⟨X, fun G ↦ by simp only [velocityDissipation_reflectZ]; exact hX _⟩

/-- **Reflection invariance.** A tame solution with reflection-invariant data is
reflection invariant. -/
theorem reflectZ_coefficients_eq {m : ℕ} (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu) {u₀ : FourierVelocity}
    {T : ℝ} (c : TameSolutionOn nu m u₀ T) (h : reflectZ u₀ = u₀) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : reflectZ (c.coefficients t) = c.coefficients t :=
  FourierUniqueness.TameSolutionOn.coefficients_eq hm hnu (TameSolutionOn.reflectZ c h) c t ht

end Reflection

end Mettapedia.FluidDynamics.NavierStokes.FourierSymmetry
