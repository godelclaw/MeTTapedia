import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A complete viscous three-parent coefficient history

The exact Fourier lab `labs/paired_stretching_history.py` computes the
sixth amplitude coefficient of full cyclic stretching minus the three
complete two-parent histories. The scalar formula below is nonpositive
throughout its viscous history. Its enstrophy and dissipation differences
obey the complete signed balance; the enstrophy difference later becomes
positive even though the stretching difference remains nonpositive.

These theorems certify the explicit scalar functions. Their identification
with continuous NS amplitude derivatives is analytic, not a theorem in this
module. No remainder bound, arbitrary-data reserve or global regularity
conclusion follows from a single amplitude coefficient. In particular the
next coefficient has a positive integrated stretching contribution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PairCycleHistory

open Set MeasureTheory

def heat (t : ℝ) : ℝ := Real.exp (-2 * t)

def rateShape (t : ℝ) : ℝ := 1 - 2 * t + (2 * t ^ 2 - 1) * heat t

def sixthStretch (t : ℝ) : ℝ := (3 / 32 : ℝ) * heat t ^ 2 * rateShape t

def sixthEnstrophy (t : ℝ) : ℝ :=
  (9 / 256 : ℝ) * heat t +
    (3 * t / 16 - 3 * t ^ 2 / 8) * heat t ^ 2 +
    (-9 / 256 - 21 * t / 64 - 9 * t ^ 2 / 32) * heat t ^ 3

def sixthDissipation (t : ℝ) : ℝ :=
  (9 / 256 : ℝ) * heat t +
    (9 * t / 16 - 3 * t ^ 2 / 4) * heat t ^ 2 +
    (-9 / 256 - 45 * t / 64 - 21 * t ^ 2 / 32) * heat t ^ 3

def sixthPrimitive (t : ℝ) : ℝ :=
  (-5 / 2304 : ℝ) +
    (3 * t / 64 - 3 / 256) * heat t ^ 2 +
    (1 / 72 - t / 96 - t ^ 2 / 32) * heat t ^ 3

theorem heat_pos (t : ℝ) : 0 < heat t := Real.exp_pos _

theorem heat_derivative (t : ℝ) : HasDerivAt heat (-2 * heat t) t := by
  apply (((hasDerivAt_id t).const_mul (-2)).exp).congr_deriv
  dsimp [heat]
  ring

theorem rateShape_derivative (t : ℝ) :
    HasDerivAt rateShape (-2 + 2 * heat t * (1 + 2 * t - 2 * t ^ 2)) t := by
  have h := ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 2)).add
    (((((hasDerivAt_id t).pow 2).const_mul 2).sub_const 1).mul (heat_derivative t))
  apply h.congr_deriv
  dsimp
  norm_num; ring

theorem rateShape_rate_nonpos (t : ℝ) :
    -2 + 2 * heat t * (1 + 2 * t - 2 * t ^ 2) ≤ 0 := by
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * t)) (heat_pos t).le
  have he : heat t * Real.exp (2 * t) = 1 := by
    rw [heat, ← Real.exp_add]
    norm_num
  rw [he] at hm
  have hs := mul_nonneg (heat_pos t).le (sq_nonneg t)
  nlinarith only [hm, hs]

theorem rateShape_antitone : Antitone rateShape :=
  antitone_of_hasDerivAt_nonpos rateShape_derivative rateShape_rate_nonpos

theorem rateShape_nonpos (t : ℝ) (ht : 0 ≤ t) : rateShape t ≤ 0 := by
  have h := rateShape_antitone ht
  simpa [rateShape, heat] using h

theorem sixthStretch_nonpos (t : ℝ) (ht : 0 ≤ t) : sixthStretch t ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (sq_nonneg (heat t))) (rateShape_nonpos t ht)

theorem sixthPrimitive_derivative (t : ℝ) :
    HasDerivAt sixthPrimitive (sixthStretch t) t := by
  have h1 := (((hasDerivAt_id t).const_mul 3).div_const 64).sub_const (3 / 256)
  have h2 := ((hasDerivAt_const t (1 / 72)).sub
    ((hasDerivAt_id t).div_const 96)).sub (((hasDerivAt_id t).pow 2).div_const 32)
  have h := ((hasDerivAt_const t (-5 / 2304)).add
    (h1.mul ((heat_derivative t).pow 2))).add (h2.mul ((heat_derivative t).pow 3))
  apply h.congr_deriv
  dsimp [sixthStretch, rateShape]
  norm_num; ring

theorem sixthPrimitive_zero : sixthPrimitive 0 = 0 := by
  norm_num [sixthPrimitive, heat]

theorem sixthPrimitive_antitone : AntitoneOn sixthPrimitive (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t _ ↦ (sixthPrimitive_derivative t).continuousAt.continuousWithinAt)
    (f' := sixthStretch)
  · intro t ht
    exact (sixthPrimitive_derivative t).hasDerivWithinAt
  · intro t ht
    exact sixthStretch_nonpos t (interior_subset ht)

theorem sixthPrimitive_nonpos (t : ℝ) (ht : 0 ≤ t) : sixthPrimitive t ≤ 0 := by
  have h := sixthPrimitive_antitone (show (0 : ℝ) ∈ Ici 0 from by simp) ht ht
  simpa only [sixthPrimitive_zero] using h

/-- Complete intervals use the same primitive on both sides of a seam. -/
theorem sixth_integral (s t : ℝ) (hst : s ≤ t) :
    (∫ r in s..t, sixthStretch r) = sixthPrimitive t - sixthPrimitive s := by
  have hc : Continuous sixthPrimitive :=
    continuous_iff_continuousAt.mpr (fun r ↦ (sixthPrimitive_derivative r).continuousAt)
  have hg : Continuous sixthStretch := by unfold sixthStretch rateShape heat; fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hc.continuousOn
    (fun r _ ↦ sixthPrimitive_derivative r) (hg.intervalIntegrable s t)

theorem sixth_interval_payment (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    2 * (∫ r in s..t, sixthStretch r) ≤ 0 := by
  rw [sixth_integral s t hst]
  have h := sixthPrimitive_antitone hs (hs.trans hst) hst
  linarith only [h]

theorem sixth_enstrophy_derivative (t : ℝ) :
    HasDerivAt sixthEnstrophy (2 * sixthStretch t - 2 * sixthDissipation t) t := by
  have h1 := (((hasDerivAt_id t).const_mul 3).div_const 16).sub
    ((((hasDerivAt_id t).pow 2).const_mul 3).div_const 8)
  have h2 := ((hasDerivAt_const t (-9 / 256)).sub
    (((hasDerivAt_id t).const_mul 21).div_const 64)).sub
      ((((hasDerivAt_id t).pow 2).const_mul 9).div_const 32)
  have h := (((heat_derivative t).const_mul (9 / 256)).add
    (h1.mul ((heat_derivative t).pow 2))).add (h2.mul ((heat_derivative t).pow 3))
  apply h.congr_deriv
  dsimp [sixthStretch, sixthDissipation, rateShape]
  norm_num; ring

theorem sixth_enstrophy_zero : sixthEnstrophy 0 = 0 := by
  norm_num [sixthEnstrophy, heat]

/-- Dissipation is a difference between complete histories, so its sign
cannot be borrowed from the nonnegativity of each history's dissipation. -/
theorem sixth_viscous_ledger (t : ℝ) :
    deriv sixthEnstrophy t + 2 * sixthDissipation t = 2 * sixthStretch t := by
  rw [(sixth_enstrophy_derivative t).deriv]
  ring

private theorem exp_four_ge_forty : (40 : ℝ) ≤ Real.exp 4 := by
  have hbase : (9 / 8 : ℝ) ≤ Real.exp (1 / 8) := by
    linarith only [Real.add_one_le_exp (1 / 8 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 8) hbase 32
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow ⊢
  linarith only [hpow]

/-- Nonpositive stretching does not order the complete enstrophy
histories: their signed diffusion difference changes the comparison. -/
theorem sixth_enstrophy_at_two_pos : 0 < sixthEnstrophy 2 := by
  have hx : 0 < Real.exp (-4) := Real.exp_pos _
  have he : Real.exp 4 * Real.exp (-4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_right exp_four_ge_forty hx.le
  rw [he] at hm
  have hb : Real.exp (-4) ≤ (1 / 40 : ℝ) := by linarith only [hm]
  have hs : Real.exp (-4) ^ 2 ≤ (1 / 1600 : ℝ) := by
    nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hb)]
  have hp : 0 < (9 / 256 : ℝ) - 9 / 8 * Real.exp (-4) -
      465 / 256 * Real.exp (-4) ^ 2 := by
    nlinarith only [hb, hs]
  have hid : sixthEnstrophy 2 = Real.exp (-4) *
      ((9 / 256 : ℝ) - 9 / 8 * Real.exp (-4) - 465 / 256 * Real.exp (-4) ^ 2) := by
    norm_num [sixthEnstrophy, heat]
    ring
  rw [hid]
  exact mul_pos hx hp

end Mettapedia.FluidDynamics.NavierStokes.PairCycleHistory
