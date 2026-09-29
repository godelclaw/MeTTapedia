import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBoundaryResponse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A pressure response cone and its rotation/dissipation certificate

For a radial swirl pair, centred at opposite points on its axis, the
initial pressure Hessian at the centre is `c E (I-3 n nᵀ)`, where
`c=3/(2πL⁵)` and `E` is the pair's kinetic energy. Three orthogonal pairs
therefore synthesize every trace-free diagonal tensor with nonnegative
energies; a rotation gives the corresponding symmetric tensor.

The companion analytic calculation gives a stronger constraint on the
first time derivative when a radial core is also present and all remote
pairs share a radial shape and radius. For the pressure excess over the
isolated core it is `-γ H + β(HB-BH)`, with `γ>0` supplied by viscosity
and `B` skew. The rotation term has zero quadratic work. An explicit
unequal-width example shows why the common decay rate matters.

This file proves the response-cone algebra and a robust matrix production
certificate with an explicit error. It does not construct NS solutions or
assert that radial packet geometry is invariant. The first physical time
jet, and the failure of invariance, are stated analytically in the lab.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SwirlPressureHistory

open scoped BigOperators
open Matrix MeasureTheory

def packetEnergy (c a : ℝ) (lam : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (a - lam i) / (3 * c)

theorem packetEnergy_nonneg (c a : ℝ) (lam : Fin 3 → ℝ) (hc : 0 < c)
    (ha : ∀ i, lam i ≤ a) (i : Fin 3) : 0 ≤ packetEnergy c a lam i := by
  exact div_nonneg (sub_nonneg.mpr (ha i)) (by positivity)

theorem sum_packetEnergy (c a : ℝ) (lam : Fin 3 → ℝ) (hc : c ≠ 0)
    (hlam : ∑ i, lam i = 0) : ∑ i, packetEnergy c a lam i = a / c := by
  simp only [Fin.sum_univ_three] at hlam ⊢
  dsimp [packetEnergy]
  field_simp
  nlinarith only [hlam]

/-- The response in an orthonormal packet-axis frame. -/
def diagonalResponse (c : ℝ) (energy : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun i ↦ c * ((∑ j, energy j) - 3 * energy i)

theorem diagonalResponse_packetEnergy (c a : ℝ) (lam : Fin 3 → ℝ) (hc : c ≠ 0)
    (hlam : ∑ i, lam i = 0) :
    diagonalResponse c (packetEnergy c a lam) = Matrix.diagonal lam := by
  unfold diagonalResponse
  congr 1
  funext i
  rw [sum_packetEnergy c a lam hc hlam]
  dsimp [packetEnergy]
  field_simp
  ring

/-- An upper spectral cap is a nonnegative energy allocation, not a sign
restriction on the trace-free pressure tensor. -/
theorem pressure_cone_certificate (c a : ℝ) (lam : Fin 3 → ℝ) (hc : 0 < c)
    (hlam : ∑ i, lam i = 0) (ha : ∀ i, lam i ≤ a) :
    ∃ energy : Fin 3 → ℝ, (∀ i, 0 ≤ energy i) ∧
      (∑ i, energy i) = a / c ∧ diagonalResponse c energy = Matrix.diagonal lam :=
  ⟨packetEnergy c a lam, packetEnergy_nonneg c a lam hc ha,
    sum_packetEnergy c a lam hc.ne' hlam, diagonalResponse_packetEnergy c a lam hc.ne' hlam⟩

variable {ι : Type*} [Fintype ι]

def pair (H K : Matrix ι ι ℝ) : ℝ := Matrix.trace (H.transpose * K)

def energy (H : Matrix ι ι ℝ) : ℝ := pair H H

theorem pair_eq_sum (H K : Matrix ι ι ℝ) :
    pair H K = ∑ i, ∑ j, H i j * K i j := by
  change (∑ i, ∑ j, H j i * K j i) = ∑ i, ∑ j, H i j * K i j
  exact Finset.sum_comm

theorem energy_eq_sum (H : Matrix ι ι ℝ) : energy H = ∑ i, ∑ j, (H i j) ^ 2 := by
  simp only [energy, pair_eq_sum, sq]

theorem energy_nonneg (H : Matrix ι ι ℝ) : 0 ≤ energy H := by
  rw [energy_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _

theorem pair_add_right (H K L : Matrix ι ι ℝ) : pair H (K + L) = pair H K + pair H L := by
  simp only [pair, Matrix.mul_add, Matrix.trace_add]

theorem pair_smul_right (a : ℝ) (H K : Matrix ι ι ℝ) : pair H (a • K) = a * pair H K := by
  simp only [pair, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- At a symmetric tensor the commutator does no quadratic work. Skewness
of `B` additionally preserves symmetry under this rate, as in the fluid test. -/
theorem pair_commutator_zero (H B : Matrix ι ι ℝ) (hH : H.IsSymm) :
    pair H (H * B - B * H) = 0 := by
  unfold pair
  rw [hH.eq, Matrix.mul_sub, Matrix.trace_sub]
  have h : Matrix.trace (H * (B * H)) = Matrix.trace (H * (H * B)) := by
    rw [Matrix.trace_mul_cycle' H B H]
  rw [h, sub_self]

/-- Two orthogonal pressure parents with weights one and one quarter. -/
def unequalResponse : Matrix (Fin 3) (Fin 3) ℝ := diagonalResponse 1 ![1, 1/4, 0]

/-- The parents decay at rates `γ` and `100γ`. This is their summed
rate, not damping at a single common rate. -/
def unequalHeatRate (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonalResponse 1 ![-γ, -25*γ, 0]

/-- Loss of cancellation makes the combined squared norm increase under
two individually decaying parent responses. -/
theorem unequal_decay_production (γ : ℝ) :
    2 * pair unequalResponse (unequalHeatRate γ) = (129/2) * γ := by
  norm_num [pair_eq_sum, unequalResponse, unequalHeatRate, diagonalResponse,
    Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.cons_val_two]
  ring

theorem unequal_decay_production_pos (γ : ℝ) (hγ : 0 < γ) :
    0 < 2 * pair unequalResponse (unequalHeatRate γ) := by
  rw [unequal_decay_production]
  positivity

def rate (γ β : ℝ) (H B defect : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (-γ) • H + β • (H * B - B * H) + defect

theorem production_eq (γ β : ℝ) (H B defect : Matrix ι ι ℝ) (hH : H.IsSymm) :
    2 * pair H (rate γ β H B defect) = -2 * γ * energy H + 2 * pair H defect := by
  simp only [rate, pair_add_right, pair_smul_right, pair_commutator_zero H B hH,
    mul_zero, add_zero, energy]
  ring

theorem defect_young (γ : ℝ) (hγ : 0 < γ) (H defect : Matrix ι ι ℝ) :
    2 * pair H defect ≤ γ * energy H + energy defect / γ := by
  have h : 0 ≤ ∑ i, ∑ j, (γ * H i j - defect i j) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have he : (∑ i, ∑ j, (γ * H i j - defect i j) ^ 2) =
      γ ^ 2 * energy H - 2 * γ * pair H defect + energy defect := by
    calc
      _ = ∑ i, ∑ j, (γ ^ 2 * (H i j) ^ 2 -
          (2 * γ) * (H i j * defect i j) + (defect i j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [energy_eq_sum, pair_eq_sum, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he] at h
  have hd : energy defect / γ * γ = energy defect := div_mul_cancel₀ _ hγ.ne'
  apply (mul_le_mul_iff_right₀ hγ).mp
  nlinarith only [h, hd]

/-- A candidate reserve pays pressure amplification through the actual
geometry defect. No estimate for that defect is assumed to follow from NS. -/
theorem production_le (γ β : ℝ) (H B defect : Matrix ι ι ℝ)
    (hγ : 0 < γ) (hH : H.IsSymm) :
    2 * pair H (rate γ β H B defect) + γ * energy H ≤ energy defect / γ := by
  rw [production_eq γ β H B defect hH]
  have h := defect_young γ hγ H defect
  linarith

theorem production_zero_defect (γ β : ℝ) (H B : Matrix ι ι ℝ) (hH : H.IsSymm) :
    2 * pair H (rate γ β H B 0) = -2 * γ * energy H := by
  rw [production_eq γ β H B 0 hH]
  simp [pair]

/-- The matrix certificate is the actual derivative of the squared norm
when every component follows the stated rate. -/
theorem hasDerivAt_energy (H : ℝ → Matrix ι ι ℝ) (V : Matrix ι ι ℝ) (t : ℝ)
    (hd : ∀ i j, HasDerivAt (fun s ↦ H s i j) (V i j) t) :
    HasDerivAt (fun s ↦ energy (H s)) (2 * pair (H t) V) t := by
  have h := HasDerivAt.sum fun i (_ : i ∈ Finset.univ) ↦
    HasDerivAt.sum fun j (_ : j ∈ Finset.univ) ↦ (hd i j).pow 2
  convert! h using 1
  · funext s
    simp only [energy_eq_sum, Finset.sum_apply, Pi.pow_apply]
  · simp only [pair_eq_sum, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_assoc, Finset.mul_sum]

/-- An interval reserve for a symmetric pressure history with an explicit
defect. This theorem requires the physical rate and integrability; it does
not bound the defect generated by a general Navier--Stokes evolution. -/
theorem interval_reserve (γ : ℝ) (hγ : 0 < γ) (a b : ℝ) (hab : a ≤ b)
    (H B defect : ℝ → Matrix ι ι ℝ) (β : ℝ → ℝ)
    (hH : ∀ t ∈ Set.Icc a b, (H t).IsSymm)
    (hd : ∀ t ∈ Set.Icc a b, ∀ i j,
      HasDerivAt (fun s ↦ H s i j) (rate γ (β t) (H t) (B t) (defect t) i j) t)
    (hiH : IntervalIntegrable (fun t ↦ energy (H t)) volume a b)
    (hiD : IntervalIntegrable (fun t ↦ energy (defect t)) volume a b)
    (hiP : IntervalIntegrable
      (fun t ↦ 2 * pair (H t) (rate γ (β t) (H t) (B t) (defect t))) volume a b) :
    energy (H b) + γ * (∫ t in a..b, energy (H t)) ≤
      energy (H a) + (∫ t in a..b, energy (defect t)) / γ := by
  have heq : (∫ t in a..b, 2 * pair (H t)
      (rate γ (β t) (H t) (B t) (defect t))) = energy (H b) - energy (H a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hiP
    intro t ht
    exact hasDerivAt_energy H _ t (hd t (by simpa [Set.uIcc_of_le hab] using ht))
  have hbound := intervalIntegral.integral_mono_on hab
    (hiP.add (hiH.const_mul γ)) (hiD.div_const γ) (fun t ht ↦
      production_le γ (β t) (H t) (B t) (defect t) hγ (hH t ht))
  rw [intervalIntegral.integral_add hiP (hiH.const_mul γ), heq,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hbound
  linarith

theorem interval_cost_le (γ : ℝ) (hγ : 0 < γ) (a b : ℝ) (hab : a ≤ b)
    (H B defect : ℝ → Matrix ι ι ℝ) (β : ℝ → ℝ)
    (hH : ∀ t ∈ Set.Icc a b, (H t).IsSymm)
    (hd : ∀ t ∈ Set.Icc a b, ∀ i j,
      HasDerivAt (fun s ↦ H s i j) (rate γ (β t) (H t) (B t) (defect t) i j) t)
    (hiH : IntervalIntegrable (fun t ↦ energy (H t)) volume a b)
    (hiD : IntervalIntegrable (fun t ↦ energy (defect t)) volume a b)
    (hiP : IntervalIntegrable
      (fun t ↦ 2 * pair (H t) (rate γ (β t) (H t) (B t) (defect t))) volume a b) :
    γ * (∫ t in a..b, energy (H t)) ≤
      energy (H a) + (∫ t in a..b, energy (defect t)) / γ := by
  have h := interval_reserve γ hγ a b hab H B defect β hH hd hiH hiD hiP
  have hn := energy_nonneg (H b)
  linarith

end Mettapedia.FluidDynamics.NavierStokes.SwirlPressureHistory
