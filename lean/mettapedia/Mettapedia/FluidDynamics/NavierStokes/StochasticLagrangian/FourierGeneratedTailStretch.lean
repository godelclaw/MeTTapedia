import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarPressureSign

/-!
# Positive self-stretching in a generated Fourier tail

Six initially planar Fourier coefficients, all at squared frequency eleven,
generate an eight-mode tail above squared frequency sixteen. The complete
projected convection of that tail has positive enstrophy production.

All convolution inputs are retained. This is an exact calculation of the
unforced vector field and the first generated tail, not a closed finite-mode
evolution, a Taylor remainder estimate, or a cumulative stretching bound.
`projectedNonlinearity` omits the common unit-torus factor `2π`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierGeneratedTailStretch

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit
  PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
  PancakeCoefficientLimitEquation InfiniteFilteredEquation PancakeFrequencyProjectorCommutator

def modeP : Wavevector := ![3, 1, 1]
def modeQ : Wavevector := ![1, 3, 1]
def modeR : Wavevector := ![1, -1, 3]

def parents : Finset Wavevector := {modeP, -modeP, modeQ, -modeQ, modeR, -modeR}

def initialVelocity : FourierVelocity := FourierPlanarPressureSign.velocity parents 2

def modeA : Wavevector := ![4, 4, 2]
def modeB : Wavevector := ![4, 0, 4]
def modeC : Wavevector := ![2, 2, 4]
def modeD : Wavevector := ![0, 4, -2]
def modeE : Wavevector := ![2, 2, -2]

def sourceModes : Finset Wavevector :=
  {modeA, -modeA, modeB, -modeB, modeC, -modeC, modeD, -modeD, modeE, -modeE}

def tailModes : Finset Wavevector := {modeA, -modeA, modeB, -modeB, modeC, -modeC, modeD, -modeD}

def av : VelocityCoefficient := Complex.I • ![-4 / 9, -4 / 9, 16 / 9]
def bv : VelocityCoefficient := Complex.I • ![-1, 2, 1]
def cv : VelocityCoefficient := Complex.I • ![-10 / 3, 2 / 3, 4 / 3]
def dv : VelocityCoefficient := Complex.I • ![2, -2 / 5, -4 / 5]
def ev : VelocityCoefficient := Complex.I • ![4 / 3, -8 / 3, -4 / 3]

def sourceVelocity : FourierVelocity := fun k ↦
  if k = modeA then av else if k = -modeA then -av
  else if k = modeB then bv else if k = -modeB then -bv
  else if k = modeC then cv else if k = -modeC then -cv
  else if k = modeD then dv else if k = -modeD then -dv
  else if k = modeE then ev else if k = -modeE then -ev else 0

def tailVelocity : FourierVelocity := fun k ↦
  if k = modeA then av else if k = -modeA then -av
  else if k = modeB then bv else if k = -modeB then -bv
  else if k = modeC then cv else if k = -modeC then -cv
  else if k = modeD then dv else if k = -modeD then -dv else 0

theorem initial_transverse (k : Wavevector) : modeDot k (initialVelocity k) = 0 :=
  FourierPlanarPressureSign.velocity_transverse parents 2 k

theorem parents_symmetric (k : Wavevector) : -k ∈ parents ↔ k ∈ parents := by
  simp only [parents, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg,
    neg_neg]
  tauto

theorem initial_reality (k : Wavevector) :
    initialVelocity (-k) = fun i ↦ conj (initialVelocity k i) :=
  FourierPlanarPressureSign.velocity_reality parents 2 parents_symmetric k

theorem initial_supported (k : Wavevector) (hk : k ∉ parents) :
    initialVelocity k = 0 :=
  FourierPlanarPressureSign.velocity_supported parents 2 k hk

theorem parent_square (k : Wavevector) (hk : k ∈ parents) : modeSquareNat k = 11 := by
  simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The entire initial high-frequency tail is zero. -/
theorem initial_tail_zero (k : Wavevector) (hk : 16 ≤ modeSquareNat k) :
    initialVelocity k = 0 := by
  apply initial_supported
  intro hm
  rw [parent_square k hm] at hk
  omega

private def pairModes : Finset Wavevector :=
  {0, modeP + modeP, -(modeP + modeP), modeQ + modeQ, -(modeQ + modeQ),
    modeR + modeR, -(modeR + modeR), modeA, -modeA, modeB, -modeB, modeC, -modeC,
    modeD, -modeD, modeE, -modeE, modeP - modeQ, -(modeP - modeQ)}

private theorem pair_mem (j l : Wavevector) (hj : j ∈ parents) (hl : l ∈ parents) :
    j + l ∈ pairModes := by
  simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hj hl
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem source_supported (k : Wavevector) (hk : k ∉ sourceModes) :
    sourceVelocity k = 0 := by
  simp only [sourceModes, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [sourceVelocity, hk]

set_option maxHeartbeats 4000000 in
/-- Complete source, including the lower output and all zero outputs. -/
theorem complete_source (k : Wavevector) :
    projectedNonlinearity parents initialVelocity k = sourceVelocity k := by
  by_cases hk : k ∈ pairModes
  · simp only [pairModes, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ext i <;> fin_cases i <;>
      norm_num [projectedNonlinearity, convectionConvolution, orderedConvection,
        lerayMode, modeSquare, modeDot, parents, initialVelocity,
        FourierPlanarPressureSign.velocity, FourierPlanarPressureSign.planarAmplitude,
        sourceVelocity, modeP, modeQ, modeR, modeA, modeB, modeC, modeD, modeE, av, bv, cv, dv, ev,
        Fin.sum_univ_three, Matrix.cons_val_two, ite_apply, funext_iff, Fin.forall_fin_succ] <;> ring_nf <;> norm_num
  · have hc : convectionConvolution parents initialVelocity k = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply Finset.sum_eq_zero
      intro l hl
      have hn : j + l ≠ k := fun he ↦ hk (he ▸ pair_mem j l hj hl)
      simp [hn]
    have hs : k ∉ sourceModes := by
      intro hm
      exact hk ((by decide : sourceModes ⊆ pairModes) hm)
    rw [source_supported k hs, projectedNonlinearity, hc]
    ext i
    by_cases hz : modeSquare k = 0 <;> simp [lerayMode, modeDot, hz]

theorem source_tail (k : Wavevector) :
    (if 16 ≤ modeSquareNat k then sourceVelocity k else 0) = tailVelocity k := by
  by_cases hk : k ∈ sourceModes
  · simp only [sourceModes, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [sourceVelocity, tailVelocity, modeSquareNat, modeA, modeB, modeC, modeD, modeE,
        Fin.sum_univ_three, Matrix.cons_val_two, ite_apply, funext_iff, Fin.forall_fin_succ]
  · have ht : tailVelocity k = 0 := by
      simp only [sourceModes, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [tailVelocity, hk]
    simp [source_supported k hk, ht]

/-- The whole high-frequency part of the nonlinearity is the stated tail. -/
theorem generated_tail (k : Wavevector) :
    (if 16 ≤ modeSquareNat k then projectedNonlinearity parents initialVelocity k else 0) =
      tailVelocity k := by
  rw [complete_source, source_tail]

theorem parents_nonzero (k : Wavevector) (hk : k ∈ parents) : k ≠ 0 := by
  intro hz
  have h := parent_square k hk
  subst k
  norm_num [modeSquareNat] at h

/-- At every output the actual unforced vector field creates exactly this tail,
with no viscous contribution because the initial tail is empty. -/
theorem actual_generated_tail (ν : ℝ) (k : Wavevector) :
    (if 16 ≤ modeSquareNat k then infiniteVelocityRHS ν initialVelocity k else 0) =
      (2 * (Real.pi : ℂ)) • tailVelocity k := by
  have hn : ∀ j ∈ parents, frequencyVec j ≠ 0 :=
    fun j hj ↦ frequencyVec_ne_zero (parents_nonzero j hj)
  have ht : ∀ j ∈ parents, modeDot j (initialVelocity j) = 0 :=
    fun j _ ↦ initial_transverse j
  rw [infiniteVelocityRHS_eq_finite parents initialVelocity initial_supported hn ht,
    velocityRHS_eq_projectedNonlinearity parents initialVelocity hn ht]
  rw [← generated_tail]
  split_ifs with hk
  · simp [unitTorusViscousVorticityCoeff, initial_tail_zero k hk]
  · simp

theorem tail_supported (k : Wavevector) (hk : k ∉ tailModes) : tailVelocity k = 0 := by
  simp only [tailModes, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [tailVelocity, hk]

theorem tail_transverse (k : Wavevector) : modeDot k (tailVelocity k) = 0 := by
  by_cases hk : k ∈ tailModes
  · simp only [tailModes, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [tailVelocity, modeDot, modeA, modeB, modeC, modeD,
        av, bv, cv, dv, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
        funext_iff, Fin.forall_fin_succ] <;> ring
  · simp [tail_supported k hk, modeDot]

theorem tail_reality (k : Wavevector) :
    tailVelocity (-k) = fun i ↦ conj (tailVelocity k i) := by
  by_cases hk : k ∈ tailModes
  · simp only [tailModes, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ext i <;> fin_cases i <;>
      norm_num [tailVelocity, modeA, modeB, modeC, modeD, av, bv, cv, dv,
        Matrix.cons_val_two, ite_apply, funext_iff, Fin.forall_fin_succ, map_ofNat]
  · have hs : -k ∈ tailModes ↔ k ∈ tailModes := by
      simp only [tailModes, Finset.mem_insert, Finset.mem_singleton,
        neg_eq_iff_eq_neg, neg_neg]
      tauto
    rw [tail_supported k hk, tail_supported (-k) (fun h ↦ hk (hs.mp h))]
    ext i
    simp

/-- The tail's complete finite-input convolution is also the nonlinear part
of the actual infinite equation, without any projection of its outputs. -/
theorem actual_tail_source (ν : ℝ) (k : Wavevector) :
    infiniteVelocityRHS ν tailVelocity k - unitTorusViscousVorticityCoeff ν tailVelocity k =
      (2 * (Real.pi : ℂ)) • projectedNonlinearity tailModes tailVelocity k := by
  have hn : ∀ j ∈ tailModes, frequencyVec j ≠ 0 := by
    intro j hj
    apply frequencyVec_ne_zero
    intro hz
    exact (by decide : (0 : Wavevector) ∉ tailModes) (hz ▸ hj)
  have ht : ∀ j ∈ tailModes, modeDot j (tailVelocity j) = 0 :=
    fun j _ ↦ tail_transverse j
  rw [infiniteVelocityRHS_eq_finite tailModes tailVelocity tail_supported hn ht,
    velocityRHS_eq_projectedNonlinearity tailModes tailVelocity hn ht]
  exact add_sub_cancel_right _ _

/-- Coefficients of the complete nonlinear source at its receiving modes.
This does not set its other outputs to zero. -/
def tailSourceAtReceiver : FourierVelocity := fun k ↦
  if k = modeA then (-9 / 5 : ℂ) • av else if k = -modeA then (9 / 5 : ℂ) • av
  else if k = modeB then (32 / 15 : ℂ) • bv else if k = -modeB then (-32 / 15 : ℂ) • bv
  else if k = modeD then (-4 / 3 : ℂ) • dv else if k = -modeD then (4 / 3 : ℂ) • dv else 0

private def tailConvectionAtReceiver : FourierVelocity := fun k ↦
  if k = modeA then ![-36 / 5, -36 / 5, 0]
  else if k = -modeA then ![36 / 5, 36 / 5, 0]
  else if k = modeB then ![128 / 15, -64 / 15, 64 / 15]
  else if k = -modeB then ![-128 / 15, 64 / 15, -64 / 15]
  else if k = modeD then ![8 / 3, -40 / 3, 16 / 3]
  else if k = -modeD then ![-8 / 3, 40 / 3, -16 / 3] else 0

set_option maxHeartbeats 4000000 in
private theorem tail_convection_on_receivers (k : Wavevector) (hk : k ∈ tailModes) :
    convectionConvolution tailModes tailVelocity k = tailConvectionAtReceiver k := by
  simp only [tailModes, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    ext i <;> fin_cases i <;>
    norm_num [convectionConvolution, orderedConvection, modeDot,
      tailModes, tailVelocity, tailConvectionAtReceiver, modeA, modeB, modeC, modeD,
      av, bv, cv, dv, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
      funext_iff, Fin.forall_fin_succ] <;>
    ring_nf <;> norm_num

theorem tail_source_on_receivers (k : Wavevector) (hk : k ∈ tailModes) :
    projectedNonlinearity tailModes tailVelocity k = tailSourceAtReceiver k := by
  rw [projectedNonlinearity, tail_convection_on_receivers k hk]
  simp only [tailModes, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    ext i <;> fin_cases i <;>
    norm_num [lerayMode, modeSquare, modeDot, tailConvectionAtReceiver, tailSourceAtReceiver,
      modeA, modeB, modeC, modeD, av, bv, dv, Fin.sum_univ_three,
      Matrix.cons_val_two, ite_apply, funext_iff, Fin.forall_fin_succ] <;>
    ring_nf

/-- Positive signed enstrophy production, with the common derivative factors omitted. -/
theorem tail_self_production :
    (∑ k ∈ tailModes, (modeSquareNat k : ℝ) *
      (coefficientHermitian (tailVelocity k)
        (projectedNonlinearity tailModes tailVelocity k)).re) = 512 / 5 := by
  have he : (∑ k ∈ tailModes, (modeSquareNat k : ℝ) *
      (coefficientHermitian (tailVelocity k)
        (projectedNonlinearity tailModes tailVelocity k)).re) =
      ∑ k ∈ tailModes, (modeSquareNat k : ℝ) *
        (coefficientHermitian (tailVelocity k) (tailSourceAtReceiver k)).re := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [tail_source_on_receivers k hk]
  rw [he]
  norm_num [tailModes, tailVelocity, tailSourceAtReceiver, coefficientHermitian,
    modeSquareNat, modeA, modeB, modeC, modeD, av, bv, cv, dv, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem tail_gradient_energy :
    (∑ k ∈ tailModes, (modeSquareNat k : ℝ) * coefficientEnergy (tailVelocity k)) =
      1472 := by
  norm_num [tailModes, tailVelocity, coefficientEnergy, Complex.normSq_apply,
    modeSquareNat, modeA, modeB, modeC, modeD, av, bv, cv, dv, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem tail_laplacian_energy :
    (∑ k ∈ tailModes, (modeSquareNat k : ℝ) ^ 2 * coefficientEnergy (tailVelocity k)) =
      40704 := by
  norm_num [tailModes, tailVelocity, coefficientEnergy, Complex.normSq_apply,
    modeSquareNat, modeA, modeB, modeC, modeD, av, bv, cv, dv, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

end Mettapedia.FluidDynamics.NavierStokes.FourierGeneratedTailStretch
