import Mettapedia.Analysis.ODE.QuadraticFormBound
import Mettapedia.Analysis.ODE.VariableGronwall
import Mettapedia.Analysis.LogarithmicScaleBound

/-! Regression examples for the analysis estimates. -/

open Set Mettapedia.Analysis Mettapedia.Analysis.ODE

-- A forced solution crosses zero inside the interval.
example : ∀ t ∈ Icc (0 : ℝ) 1, |t - 1 / 2| ≤ 1 / 2 + t := by
  have h := norm_le_initial_add_integral_of_dissipative
    (a := 0) (b := 1) (u := fun t : ℝ ↦ t - 1 / 2) (f := fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) (continuous_id.sub continuous_const).continuousOn
    continuous_const
    (fun t _ ↦ by simpa using ((hasDerivAt_id t).sub_const (1 / 2)).hasDerivWithinAt)
    (by simp)
  simpa using h

-- Variable Gronwall permits a negative growth coefficient without a sign
-- hypothesis on the compared function.
example {x x' : ℝ → ℝ} (hx : ContinuousOn x (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt x (x' t) (Icc (0 : ℝ) 1) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, x' t ≤ -x t) :
    ∀ t ∈ Icc (0 : ℝ) 1, x t ≤ x 0 * Real.exp (-t) := by
  have h := le_initial_mul_exp_integral_of_deriv_le_mul
    (g := fun _ ↦ -1) hx continuousOn_const hd (by simpa using hb)
  simpa using h

-- The scale estimate is not restricted to the source's quarter-power decay.
example {X C L W H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ C * (L + W * (-Real.log ε) + ε ^ (2 : ℝ) * H)) :
    X ≤ C * (L + W * (Real.log (Real.exp 1 + H) / 2) + 1) :=
  le_logarithmic_of_le_scale_bound hC hH (by norm_num) h

#print axioms Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_dissipative
#print axioms Mettapedia.Analysis.ODE.norm_div_le_initial_add_integral
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_integral_on
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_of_source_le
#print axioms Mettapedia.Analysis.ODE.le_initial_mul_exp_integral_of_deriv_le_mul
#print axioms Mettapedia.Analysis.exists_scale_rpow_mul_le_one
#print axioms Mettapedia.Analysis.le_logarithmic_of_le_scale_bound
#print axioms Mettapedia.Analysis.le_four_mul_logarithmic_of_le_quarter_scale_bound
