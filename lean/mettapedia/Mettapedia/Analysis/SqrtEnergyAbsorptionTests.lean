import Mettapedia.Analysis.SqrtEnergyAbsorption
import Mathlib.Tactic.NormNum

/-! Sharpness and the necessity of positive absorption weight. -/

example : (4 : ℝ) * Real.sqrt 1 = 2 * 1 + 4 ^ 2 / (4 * 2) := by norm_num

example : ¬ ((0 : ℝ) * Real.sqrt 1 ≤ (-1) * 1 + 0 ^ 2 / (4 * (-1))) := by norm_num

#print axioms Mettapedia.Analysis.SqrtEnergyAbsorption.mul_sqrt_le
