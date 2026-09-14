import MettapediaNS.RieszDoubleCommutator
import NavierStokes.R3.PressureFunctionals
import NavierStokes.R3.ComparisonFiniteEnergy

/-!
# Signed first and second pressure localization differences

The source is the actual velocity tensor, not the test field. Localizing
both velocity inputs gives a second difference minus twice a first
commutator. Only the second difference has the `L¹` source / `L²` test
bound. The first commutator remains explicit.

All pressure pairings and Riesz operators are the upstream constructions.
The weighted velocity is not asserted to remain divergence-free.
-/

noncomputable section

open Set MeasureTheory
open NavierStokesR3.ProblemStatement NavierStokesR3.Comparison
open NavierStokesR3.PressureFunctionals
open Mettapedia.Analysis.RieszDoubleCommutator
open scoped ENNReal

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationDifference

/-- The output/test cutoff minus the one-source cutoff. -/
def firstDifference (i j : Fin 3) (φ g : Space → ℝ) (ψ ψh : ComplexTest) : ℂ :=
  pressurePair i j g ψh - pressurePair i j (fun x => φ x ^ 2 * g x) ψ

/-- The second difference uses the full, singly weighted, and doubly
weighted tensor sources, with coefficients `1, -2, 1`. -/
def secondDifference (i j : Fin 3) (φ g : Space → ℝ) (ψ ψh ψhh : ComplexTest) : ℂ :=
  pressurePair i j g ψhh - 2 * pressurePair i j (fun x => φ x ^ 2 * g x) ψh +
    pressurePair i j (fun x => φ x ^ 4 * g x) ψ

/-- Multiplying each velocity input by `φ²` multiplies its tensor by `φ⁴`.
The comparison output is multiplied by the same `φ⁴`. -/
def localizationDefect (i j : Fin 3) (φ g : Space → ℝ) (ψ ψhh : ComplexTest) : ℂ :=
  pressurePair i j (fun x => φ x ^ 4 * g x) ψ - pressurePair i j g ψhh

theorem localizationDefect_eq_second_sub_first (i j : Fin 3)
    (φ g : Space → ℝ) (ψ ψh ψhh : ComplexTest) :
    localizationDefect i j φ g ψ ψhh =
      secondDifference i j φ g ψ ψh ψhh - 2 * firstDifference i j φ g ψh ψhh := by
  unfold localizationDefect secondDifference firstDifference
  ring

private theorem integrable_cutoff_source {φ g : Space → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hg : Integrable g) (n : ℕ) : Integrable (fun x => φ x ^ n * g x) := by
  apply hg.bdd_mul (hφm.pow_const n).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hφ x).1 n)]
  exact pow_le_one₀ (hφ x).1 (hφ x).2

/-- The first difference is the imported operator's actual commutator
pairing. Bounded cutoffs let an `L¹` source suffice for this identity. -/
theorem firstDifference_eq_integral (i j : Fin 3) {φ g : Space → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hg : Integrable g)
    (ψ ψh : ComplexTest) :
    firstDifference i j φ g ψ ψh =
      ∫ x, g x • (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x) := by
  have h₁ := integrable_l1_riesz_pair hg i j ψh
  have h₂ := integrable_l1_riesz_pair (integrable_cutoff_source hφm hφ hg 2) i j ψ
  rw [firstDifference, pressurePair, pressurePair, ← integral_sub h₁ h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem secondDifference_eq_integral (i j : Fin 3) {φ g : Space → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hg : Integrable g)
    (ψ ψh ψhh : ComplexTest) :
    secondDifference i j φ g ψ ψh ψhh = ∫ x, g x •
      (rieszTest i j ψhh x - (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) +
        φ x ^ 4 • rieszTest i j ψ x) := by
  have h₀ := integrable_l1_riesz_pair hg i j ψhh
  have h₁ := integrable_l1_riesz_pair (integrable_cutoff_source hφm hφ hg 2) i j ψh
  have h₂ := integrable_l1_riesz_pair (integrable_cutoff_source hφm hφ hg 4) i j ψ
  have hc : Integrable (fun x => (2 : ℂ) * ((φ x ^ 2 * g x : ℝ) * rieszTest i j ψh x)) :=
    h₁.const_mul 2
  have hs : Integrable (fun x => (g x : ℂ) * rieszTest i j ψhh x -
      (2 : ℂ) * ((φ x ^ 2 * g x : ℝ) * rieszTest i j ψh x)) := h₀.sub hc
  rw [secondDifference, pressurePair, pressurePair, pressurePair,
    ← integral_const_mul, ← integral_sub h₀ hc, ← integral_add hs h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- The second pressure difference retains two cutoff differences, while
allowing an arbitrary integrable tensor coefficient. -/
theorem norm_secondDifference_le (i j : Fin 3) {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (hg : Integrable g)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖secondDifference i j φ g ψ ψh ψhh‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 1 g * comparisonLpNorm 2 (fun x => ψ x) := by
  let C := (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
    comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
    R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 2 (fun x => ψ x)
  rw [secondDifference_eq_integral i j hφm hφ hg]
  calc
    _ ≤ ∫ x, ‖g x‖ * C := norm_integral_le_of_norm_le (hg.norm.mul_const C)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (norm_riesz_double_commutator_le i j hR hφm hφ hLip ψ ψh ψhh hψh hψhh x)
          (norm_nonneg _))
    _ = _ := by
      rw [integral_mul_const, ← NavierStokesR3.PairedKernelBound.lpNorm_one_eq_integral_norm
        hg.aestronglyMeasurable]
      dsimp [C]
      ring

/-- The first-order remainder is kept separate and uses the upstream
single-commutator estimate with its own `L⁴` test norm. -/
theorem norm_firstDifference_le (i j : Fin 3) {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (hg : Integrable g)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x) :
    ‖firstDifference i j φ g ψ ψh‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 (fun x => ψ x) := by
  rw [firstDifference_eq_integral i j hφm hφ hg]
  exact riesz_commutator_pair_bound i j hR hφm hφ hLip hg ψ ψh hψh (ψ.memLp 4)

/-- The source bound is the imported finite-energy tensor bound, applied
with zero comparison velocity. No source derivative or `L³` norm is used. -/
theorem velocityTensor_integrable_and_lpNorm_le {u : Space → Space}
    (hu : MemLp u 2 volume) (i j : Fin 3) :
    Integrable (fun x => u x i * u x j) ∧
      comparisonLpNorm 1 (fun x => u x i * u x j) ≤ l2Sq u := by
  have he : tensorDiff (fun z => u z.2) (fun _ => 0) 0 i j =
      (fun x => u x i * u x j) := by
    funext x
    simp [tensorDiff]
  have hi := tensorDiff_integrable (u := fun z => u z.2) (v := fun _ => 0) (t := 0)
    hu MemLp.zero' i j
  rw [he] at hi
  refine ⟨hi, ?_⟩
  rw [NavierStokesR3.PairedKernelBound.lpNorm_one_eq_integral_norm hi.aestronglyMeasurable]
  have hb := tensorDiff_norm_integral_le (u := fun z => u z.2) (v := fun _ => 0) (t := 0)
    hu MemLp.zero' i j
  simpa only [he, l2Sq, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero, add_zero] using hb

/-- Actual velocity-tensor specialization: the second-difference source is
paid by kinetic energy, independently of every velocity derivative. -/
theorem norm_secondDifference_velocityTensor_le (i j : Fin 3)
    {φ : Space → ℝ} {u : Space → Space} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (hu : MemLp u 2 volume)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖secondDifference i j φ (fun x => u x i * u x j) ψ ψh ψhh‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * l2Sq u * comparisonLpNorm 2 (fun x => ψ x) := by
  obtain ⟨hi, hb⟩ := velocityTensor_integrable_and_lpNorm_le hu i j
  have hC : 0 ≤ (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
      comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
      R ^ (-(3 / 2) : ℝ) := by
    apply mul_nonneg _ (Real.rpow_nonneg hR.le _)
    exact mul_nonneg (mul_nonneg heatKernelTimeConstant_pos.le (sq_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  exact (norm_secondDifference_le i j hR hφm hφ hLip hi ψ ψh ψhh hψh hψhh).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) ENNReal.toReal_nonneg)

/-- The doubly localized tensor is literally the tensor of the cut-off
velocity. This is not a claim that the cut-off velocity is solenoidal. -/
theorem localizationDefect_velocityTensor (i j : Fin 3) (φ : Space → ℝ)
    (u : Space → Space) (ψ ψhh : ComplexTest) :
    localizationDefect i j φ (fun x => u x i * u x j) ψ ψhh =
      pressurePair i j (fun x => (φ x ^ 2 • u x) i * (φ x ^ 2 • u x) j) ψ -
        pressurePair i j (fun x => u x i * u x j) ψhh := by
  unfold localizationDefect
  congr 2
  funext x
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- Complete localization bound: the second-order `L²` term and the remaining
first-order `L⁴` term are both present. No first commutator is set to zero. -/
theorem norm_localizationDefect_le (i j : Fin 3) {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (hg : Integrable g)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖localizationDefect i j φ g ψ ψhh‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 1 g * comparisonLpNorm 2 (fun x => ψ x) +
      2 * ((rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 (fun x => ψh x)) := by
  rw [localizationDefect_eq_second_sub_first]
  have h₂ := norm_secondDifference_le i j hR hφm hφ hLip hg ψ ψh ψhh hψh hψhh
  have h₁ := norm_firstDifference_le i j hR hφm hφ hLip hg ψh ψhh hψhh
  calc
    _ ≤ ‖secondDifference i j φ g ψ ψh ψhh‖ + ‖(2 : ℂ) * firstDifference i j φ g ψh ψhh‖ :=
      norm_sub_le _ _
    _ = ‖secondDifference i j φ g ψ ψh ψhh‖ + 2 * ‖firstDifference i j φ g ψh ψhh‖ := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    _ ≤ _ := add_le_add h₂ (mul_le_mul_of_nonneg_left h₁ (by norm_num))

end Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationDifference
