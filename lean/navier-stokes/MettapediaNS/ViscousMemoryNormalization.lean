import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Coercivity after normalization by viscous memory

The analytic candidate divides the pressure/strain envelope by
`det(I+C/η)^(1/3)`. This denominator is at most `1+tr C/(3η)`. This file proves
the resulting scalar coercivity and integrability statements, including
the infinite-volume argument that avoids integrating a constant.

It also certifies the traceless matrix cost and the exact logarithmic
change of drift. The matrix determinant evolution, its stochastic
identification, and the conditional NS continuation argument are analytic
in the companion lab. No uniform bound on the normalized envelope or its
remaining pressure/history source is assumed to have been established.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryNormalization

open MeasureTheory

/-- With `x=|ω|²`, `k x²≤Y`, and `h≤1+c`, an upper bound on `Y/h`
permits vorticity to concentrate only together with retained memory. -/
theorem normalized_quartic (x Y h c k B : ℝ)
    (hk : 0 < k) (hh : 0 < h) (hB : 0 ≤ B)
    (hY : k * x ^ 2 ≤ Y) (hm : h ≤ 1 + c) (hb : Y / h ≤ B) :
    x ^ 2 ≤ (B / k) * (1 + c) := by
  have he : Y ≤ B * h := (div_le_iff₀ hh).1 hb
  have ht := mul_le_mul_of_nonneg_left hm hB
  have hl : x ^ 2 ≤ B * (1 + c) / k := (le_div_iff₀ hk).2 (by
    nlinarith only [hY, he, ht])
  calc
    _ ≤ B * (1 + c) / k := hl
    _ = _ := by ring

/-- The low-amplitude part is paid by enstrophy and the high-amplitude
part by memory mass. No finite-volume hypothesis occurs. -/
theorem quartic_split (x c M : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (h : x ^ 2 ≤ M * (1 + c)) :
    x ^ 2 ≤ Real.sqrt (2 * M) * x + 2 * M * c := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * M by positivity)
  have hn := Real.sqrt_nonneg (2 * M)
  by_cases hx' : x ≤ Real.sqrt (2 * M)
  · nlinarith [mul_nonneg hx (sub_nonneg.mpr hx'), mul_nonneg hM hc]
  · have ht : 2 * M ≤ x ^ 2 := by nlinarith
    nlinarith [mul_nonneg hn hx]

/-- The analytic whole-space application uses `x=|ω|²` and
`c=tr C/(3η)`. Their integrals are finite on every smooth prefix. -/
theorem integrable_quartic_of_memory {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (x c : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hx : Integrable x μ) (hc : Integrable c μ)
    (hx0 : ∀ z, 0 ≤ x z) (hc0 : ∀ z, 0 ≤ c z)
    (h : ∀ z, x z ^ 2 ≤ M * (1 + c z)) :
    Integrable (fun z ↦ x z ^ 2) μ ∧
      (∫ z, x z ^ 2 ∂μ) ≤
        Real.sqrt (2 * M) * (∫ z, x z ∂μ) + 2 * M * (∫ z, c z ∂μ) := by
  have hb : Integrable (fun z ↦ Real.sqrt (2 * M) * x z + 2 * M * c z) μ :=
    (hx.const_mul _).add (hc.const_mul _)
  have hpoint (z : α) := quartic_split (x z) (c z) M (hx0 z) (hc0 z) hM (h z)
  have hp : Integrable (fun z ↦ x z ^ 2) μ := hb.mono'
    (hx.aestronglyMeasurable.pow 2) (ae_of_all μ (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint z))
  refine ⟨hp, ?_⟩
  have hi := integral_mono hp hb hpoint
  simpa only [integral_add (hx.const_mul _) (hc.const_mul _), integral_const_mul] using hi

/-- The shape cost is the squared norm after subtracting the isotropic
part. In the matrix application `A=H^(-1/2) C_j H^(-1/2)`. -/
theorem shape_identity (A : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, A i j ^ 2) - (∑ i, A i i) ^ 2 / 3 =
      ∑ i, ∑ j, (A i j - if i = j then (∑ k, A k k) / 3 else 0) ^ 2 := by
  simp [Fin.sum_univ_succ]
  ring

theorem shape_nonneg (A : Fin 3 → Fin 3 → ℝ) :
    0 ≤ (∑ i, ∑ j, A i j ^ 2) - (∑ i, A i i) ^ 2 / 3 := by
  rw [shape_identity]
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

/-- Exact change from `log Y` to `log Y-ψ-κt`. The new spatial drift
is `u-2ν∇ψ`. Reversing time gives the auxiliary sampling drift
`-u+2ν∇ψ`; no corresponding force is applied to the fluid. -/
theorem logarithmic_change (ν κ Dl Dψ : ℝ) (gl gψ : Fin 3 → ℝ) :
    Dl - Dψ - κ - 2 * ν * (∑ i, gψ i * (gl i - gψ i)) -
        ν * (∑ i, (gl i - gψ i) ^ 2) =
      (Dl - ν * (∑ i, gl i ^ 2)) - κ -
        (Dψ - ν * (∑ i, gψ i ^ 2)) := by
  simp [Fin.sum_univ_succ]
  ring

end Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryNormalization
