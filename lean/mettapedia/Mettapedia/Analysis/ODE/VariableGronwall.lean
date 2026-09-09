/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI, NavierStokesAndEuler, Euler/OrdinaryVariableGronwall.lean.
Upstream revision: 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538.
Modified by MeTTapedia contributors: arbitrary finite interval, direct
interval integrals, and no construction-specific path or stability imports.
See LICENSES/Apache-2.0.txt at the repository root.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Ring

/-!
# Gronwall comparison with a continuous variable coefficient

The integrating factor is the exponential of the actual coefficient integral.
Continuity is needed only on the closed interval, and derivatives only on
its interior. Neither the coefficient nor the compared function needs to
be nonnegative. This scalar statement is independent of any PDE.
-/

namespace Mettapedia.Analysis.ODE

open Set
open scoped Topology

/-- A scalar differential inequality with variable growth integrates to the
exponential of that growth's interval integral. -/
theorem le_initial_mul_exp_integral_of_deriv_le_mul {a b : ℝ} {x x' g : ℝ → ℝ}
    (hx : ContinuousOn x (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ioo a b, x' t ≤ g t * x t) :
    ∀ t ∈ Icc a b, x t ≤ x a * Real.exp (∫ s in a..t, g s) := by
  by_cases hab : a ≤ b
  · let G : ℝ → ℝ := fun t ↦ g (projIcc a b hab t)
    have hcG : Continuous G := hg.restrict.comp continuous_projIcc
    have hG (t : ℝ) (ht : t ∈ Icc a b) : G t = g t := by
      simp only [G, projIcc_of_mem hab ht]
    let I : ℝ → ℝ := fun t ↦ ∫ s in a..t, G s
    have hI (t : ℝ) : HasDerivAt I (G t) t :=
      intervalIntegral.integral_hasDerivAt_right (hcG.intervalIntegrable a t)
        (hcG.stronglyMeasurableAtFilter _ _) hcG.continuousAt
    have hcI : Continuous I := continuous_iff_continuousAt.mpr fun t ↦ (hI t).continuousAt
    let y : ℝ → ℝ := fun t ↦ x t * Real.exp (-I t)
    let y' : ℝ → ℝ := fun t ↦ Real.exp (-I t) * (x' t - G t * x t)
    have hcy : ContinuousOn y (Icc a b) := hx.mul (Real.continuous_exp.comp hcI.neg).continuousOn
    have hdy (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivWithinAt y (y' t) (Icc a b) t := by
      convert! (hder t ht).mul (hI t).neg.exp.hasDerivWithinAt using 1
      dsimp [y']
      ring
    have hnonpos (t : ℝ) (ht : t ∈ Ioo a b) : y' t ≤ 0 := by
      dsimp [y']
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      rw [hG t (Ioo_subset_Icc_self ht)]
      exact sub_nonpos.mpr (hbound t ht)
    have hy : AntitoneOn y (Icc a b) := antitoneOn_of_hasDerivWithinAt_nonpos (f' := y')
      (convex_Icc a b) hcy
      (fun t ht ↦ (hdy t (by simpa only [interior_Icc] using ht)).mono interior_subset)
      (by simpa only [interior_Icc] using hnonpos)
    intro t ht
    have hyt := hy ⟨le_rfl, hab⟩ ht ht.1
    have hIa : I a = 0 := intervalIntegral.integral_same
    have hint : I t = ∫ s in a..t, g s := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      exact hG r ⟨hr.1, hr.2.trans ht.2⟩
    have hcancel : (x a * Real.exp (I t)) * Real.exp (-I t) = x a := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [← hint]
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (-I t))).mp
    rw [hcancel]
    simpa only [y, hIa, neg_zero, Real.exp_zero, mul_one] using hyt
  · intro t ht
    exact (hab (ht.1.trans ht.2)).elim

end Mettapedia.Analysis.ODE
