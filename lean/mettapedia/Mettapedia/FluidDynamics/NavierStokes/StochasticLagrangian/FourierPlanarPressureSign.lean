import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierAxialLeraySource

/-!
# A planar Fourier family with pressure terms of one sign

The amplitude `i(-k₂,k₁,0)/L` is transverse and has no axial component.
On symmetric finite support it represents a real velocity. Every pressure
numerator interaction is a nonnegative squared planar area. This is an
instantaneous calculation, with no assertion about later Fourier phases.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureSign

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
  PancakeFourierPressureStrain PancakeLowPressureBudget PancakeFrequencyProjectorCommutator
  PancakeViscousMisalignmentAbsorption FourierSingleConeStretch FourierAxialLeraySource
  PancakeCoefficientLimitEquation

def axis : Fin 3 → ℝ := ![0, 0, 1]

def planarArea (p q : Wavevector) : ℝ :=
  (p 0 : ℝ) * (q 1 : ℝ) - (p 1 : ℝ) * (q 0 : ℝ)

def planarAmplitude (L : ℝ) (k : Wavevector) : VelocityCoefficient :=
  (Complex.I / (L : ℂ)) • ![-(k 1 : ℂ), (k 0 : ℂ), 0]

def velocity (P : Finset Wavevector) (L : ℝ) : FourierVelocity :=
  fun k ↦ if k ∈ P then planarAmplitude L k else 0

theorem modeDot_planarAmplitude (L : ℝ) (p q : Wavevector) :
    modeDot q (planarAmplitude L p) =
      (Complex.I / (L : ℂ)) * (planarArea p q : ℂ) := by
  rw [planarAmplitude, modeDot_smul]
  congr 1
  simp [modeDot, planarArea, Fin.sum_univ_three]
  ring

theorem planarAmplitude_transverse (L : ℝ) (k : Wavevector) :
    modeDot k (planarAmplitude L k) = 0 := by
  rw [modeDot_planarAmplitude]
  simp [planarArea, mul_comm]

theorem planarAmplitude_reality (L : ℝ) (k : Wavevector) :
    planarAmplitude L (-k) = fun i ↦ conj (planarAmplitude L k i) := by
  ext i
  fin_cases i <;> simp [planarAmplitude] <;> ring

theorem planarAmplitude_energy (L : ℝ) (k : Wavevector) :
    coefficientEnergy (planarAmplitude L k) = ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) / L ^ 2 := by
  rw [planarAmplitude, coefficientEnergy_smul]
  simp [coefficientEnergy, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem velocity_supported (P : Finset Wavevector) (L : ℝ) (k : Wavevector) (hk : k ∉ P) :
    velocity P L k = 0 := by simp [velocity, hk]

theorem velocity_transverse (P : Finset Wavevector) (L : ℝ) (k : Wavevector) :
    modeDot k (velocity P L k) = 0 := by
  unfold velocity
  split_ifs
  · exact planarAmplitude_transverse L k
  · simp [modeDot]

theorem velocity_planar (P : Finset Wavevector) (L : ℝ) (k : Wavevector) :
    coefficientDot (velocity P L k) (axisCoefficient axis) = 0 := by
  unfold velocity
  split_ifs <;> simp [coefficientDot, axisCoefficient, axis, planarAmplitude, Fin.sum_univ_three]

theorem velocity_reality (P : Finset Wavevector) (L : ℝ)
    (hP : ∀ k, -k ∈ P ↔ k ∈ P) (k : Wavevector) :
    velocity P L (-k) = fun i ↦ conj (velocity P L k i) := by
  simp only [velocity, hP]
  split_ifs
  · exact planarAmplitude_reality L k
  · ext i; simp

theorem fullEnergy_eq (P : Finset Wavevector) (L : ℝ) :
    fullEnergy P (velocity P L) =
      ∑ k ∈ P, ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) / L ^ 2 := by
  unfold fullEnergy
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp only [velocity, hk, ite_true, planarAmplitude_energy]

theorem planarArea_other_parent (p r : Wavevector) :
    planarArea r (p + r) = -planarArea p (p + r) := by
  simp [planarArea]
  ring

/-- No phase cancellation occurs in the pressure numerator of this family. -/
theorem pressure_pair_eq_square (L : ℝ) (p r : Wavevector) :
    modeDot (p + r) (planarAmplitude L p) * modeDot (p + r) (planarAmplitude L r) =
      ((planarArea p (p + r) ^ 2 / L ^ 2 : ℝ) : ℂ) := by
  rw [modeDot_planarAmplitude, modeDot_planarAmplitude, planarArea_other_parent]
  push_cast
  calc
    _ = -(Complex.I ^ 2) * ((planarArea p (p + r) : ℂ) ^ 2 / (L : ℂ) ^ 2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

def areaSum (P : Finset Wavevector) (L : ℝ) (q : Wavevector) : ℝ :=
  ∑ pr ∈ interactionPairs P q, planarArea pr.1 q ^ 2 / L ^ 2

theorem areaSum_nonneg (P : Finset Wavevector) (L : ℝ) (q : Wavevector) :
    0 ≤ areaSum P L q := by
  exact Finset.sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- A selected set of large interactions gives a lower bound because every other term is nonnegative. -/
theorem areaSum_ge_subset (P : Finset Wavevector) (L : ℝ) (q : Wavevector)
    (S : Finset (Wavevector × Wavevector)) (hS : S ⊆ interactionPairs P q)
    (B : ℝ) (hB : ∀ pr ∈ S, B ≤ planarArea pr.1 q ^ 2 / L ^ 2) :
    (S.card : ℝ) * B ≤ areaSum P L q := by
  calc
    _ = ∑ _pr ∈ S, B := by simp
    _ ≤ ∑ pr ∈ S, planarArea pr.1 q ^ 2 / L ^ 2 := Finset.sum_le_sum hB
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun _ _ _ ↦ div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem pressure_numerator_eq (P : Finset Wavevector) (L : ℝ) (q : Wavevector) :
    modeDot q (convectionConvolution P (velocity P L) q) = (areaSum P L q : ℂ) := by
  rw [pressure_numerator_output_pair P (velocity P L) q (fun k _ ↦ velocity_transverse P L k)]
  simp only [areaSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun pr hpr ↦ ?_
  obtain ⟨hm, hq⟩ := Finset.mem_filter.mp hpr
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hm
  simp only [velocity, hp, hr, ite_true]
  simpa only [hq] using pressure_pair_eq_square L pr.1 pr.2

/-- The axial pressure has one common imaginary phase at each output. -/
theorem axialPressureSource_eq (P : Finset Wavevector) (L : ℝ) (q : Wavevector) :
    axialPressureSource axis P (velocity P L) q =
      Complex.I * ((2 * Real.pi * (q 2 : ℝ) * areaSum P L q /
        ‖frequencyVec q‖ ^ 2 : ℝ) : ℂ) := by
  rw [axialPressureSource, pressureCoeff, pressure_numerator_eq, modeSquare_eq_norm_sq]
  have hd : modeDot q (axisCoefficient axis) = (q 2 : ℂ) := by
    simp [modeDot, axisCoefficient, axis, Fin.sum_univ_three]
  rw [hd]
  simp only [unitTorusDerivativePhase]
  push_cast
  ring

theorem axialPressureSource_im (P : Finset Wavevector) (L : ℝ) (q : Wavevector) :
    (axialPressureSource axis P (velocity P L) q).im =
      2 * Real.pi * (q 2 : ℝ) * areaSum P L q / ‖frequencyVec q‖ ^ 2 := by
  rw [axialPressureSource_eq]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]

theorem axialPressureSource_im_nonneg (P : Finset Wavevector) (L : ℝ) (q : Wavevector)
    (hq : 0 ≤ q 2) : 0 ≤ (axialPressureSource axis P (velocity P L) q).im := by
  rw [axialPressureSource_im]
  have hq' : (0 : ℝ) ≤ q 2 := by exact_mod_cast hq
  have hs := areaSum_nonneg P L q
  positivity

/-- A lower bound on selected squared areas gives a lower bound on the actual axial pressure force. -/
theorem axialPressureSource_lower (P : Finset Wavevector) (L : ℝ) (q : Wavevector)
    (hq : 0 ≤ q 2) (S : Finset (Wavevector × Wavevector))
    (hS : S ⊆ interactionPairs P q) (B : ℝ)
    (hB : ∀ pr ∈ S, B ≤ planarArea pr.1 q ^ 2 / L ^ 2) :
    (2 * Real.pi * (q 2 : ℝ) / ‖frequencyVec q‖ ^ 2) * ((S.card : ℝ) * B) ≤
      ‖axialPressureSource axis P (velocity P L) q‖ := by
  have hq' : (0 : ℝ) ≤ q 2 := by exact_mod_cast hq
  have h := mul_le_mul_of_nonneg_left (areaSum_ge_subset P L q S hS B hB)
    (by positivity : 0 ≤ 2 * Real.pi * (q 2 : ℝ) / ‖frequencyVec q‖ ^ 2)
  refine h.trans ?_
  calc
    _ = (axialPressureSource axis P (velocity P L) q).im := by
      rw [axialPressureSource_im]
      ring
    _ ≤ _ := Complex.im_le_norm _

theorem axialTransportSource_zero (P : Finset Wavevector) (L : ℝ) (q : Wavevector) :
    axialTransportSource axis P (velocity P L) q = 0 := by
  rw [axialTransportSource_eq_pairs axis P (velocity P L) q
    (fun k _ ↦ velocity_transverse P L k)]
  apply Finset.sum_eq_zero
  intro pr _
  simp [axialTransportPair, velocity_planar]

/-- At this datum the actual infinite unforced axial derivative equals the pressure source. -/
theorem infinite_rhs_axial (P : Finset Wavevector) (L ν : ℝ) (q : Wavevector)
    (hP : ∀ k ∈ P, frequencyVec k ≠ 0) :
    coefficientDot (infiniteVelocityRHS ν (velocity P L) q) (axisCoefficient axis) =
      axialPressureSource axis P (velocity P L) q := by
  rw [axial_infiniteVelocityRHS axis P (velocity P L) ν q (velocity_supported P L) hP
    (fun k _ ↦ velocity_transverse P L k), axialTransportSource_zero, velocity_planar]
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureSign
