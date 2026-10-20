import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

/-!
# Stability of nonlinear PLN deduction

The four readouts remain distinct. With both middle marginals at least a
positive margin below one, perturbations of AB, BC and C have gain at most the
inverse margin; the B perturbation has a conservative inverse-square gain.
The Lipschitz theorem uses the supremum metric and can supply the gain required
by world-model approximation composition. Readout errors do not measure the
failure of screening off; that is a separate semantic term.
-/

open scoped NNReal

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons.DeductionStability

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

private theorem unit_difference {x y : ℝ} (xUnit : x ∈ Set.Icc (0 : ℝ) 1)
    (yUnit : y ∈ Set.Icc (0 : ℝ) 1) : |x-y| ≤ 1 := by
  exact abs_le.mpr ⟨by linarith [xUnit.1, yUnit.2], by linarith [xUnit.2, yUnit.1]⟩

/-- Exact change of the deduction value when this coordinate alone changes. -/
theorem antecedent_difference (x x' y b c : ℝ) (notFull : b ≠ 1) :
    plnDeductionStrength x y b c - plnDeductionStrength x' y b c =
      (x-x')*(y-c)/(1-b) := by
  have denominator : 1-b ≠ 0 := sub_ne_zero.mpr (Ne.symm notFull)
  unfold plnDeductionStrength
  field_simp
  ring

/-- Exact change of the deduction value when this coordinate alone changes. -/
theorem link_difference (x y y' b c : ℝ) (notFull : b ≠ 1) :
    plnDeductionStrength x y b c - plnDeductionStrength x y' b c =
      (y-y')*(x-b)/(1-b) := by
  have denominator : 1-b ≠ 0 := sub_ne_zero.mpr (Ne.symm notFull)
  unfold plnDeductionStrength
  field_simp
  ring

/-- Exact change of the deduction value when this coordinate alone changes. -/
theorem target_difference (x y b c c' : ℝ) (notFull : b ≠ 1) :
    plnDeductionStrength x y b c - plnDeductionStrength x y b c' =
      (c-c')*(1-x)/(1-b) := by
  have denominator : 1-b ≠ 0 := sub_ne_zero.mpr (Ne.symm notFull)
  unfold plnDeductionStrength
  field_simp
  ring

/-- Exact change of the deduction value when this coordinate alone changes. -/
theorem middle_difference (x y b b' c : ℝ) (notFull : b ≠ 1) (notFull' : b' ≠ 1) :
    plnDeductionStrength x y b c - plnDeductionStrength x y b' c =
      (b-b')*(1-x)*(c-y)/((1-b)*(1-b')) := by
  have denominator : 1-b ≠ 0 := sub_ne_zero.mpr (Ne.symm notFull)
  have denominator' : 1-b' ≠ 0 := sub_ne_zero.mpr (Ne.symm notFull')
  unfold plnDeductionStrength
  field_simp
  ring

private theorem quotient_bound {error coefficient denominator margin : ℝ}
    (coefficientBound : |coefficient| ≤ 1) (positive : 0 < margin)
    (separation : margin ≤ denominator) :
    |error * coefficient / denominator| ≤ |error| / margin := by
  have denominatorPos := positive.trans_le separation
  rw [abs_div, abs_mul, abs_of_pos denominatorPos]
  calc
    _ ≤ |error| / denominator := div_le_div_of_nonneg_right
      (by nlinarith [abs_nonneg error]) denominatorPos.le
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg error) positive separation

/-- Four probability readouts; compatibility with a joint law is an additional property. -/
structure PremiseValues where
  ab : Set.Icc (0 : ℝ) 1
  bc : Set.Icc (0 : ℝ) 1
  b : Set.Icc (0 : ℝ) 1
  c : Set.Icc (0 : ℝ) 1

/-- The existing nonlinear PLN deduction formula evaluated on the four readouts. -/
noncomputable def estimate (input : PremiseValues) : ℝ :=
  plnDeductionStrength input.ab input.bc input.b input.c

/-- A coordinate-wise perturbation budget with the denominator margin retained. -/
noncomputable def perturbationBudget (margin : ℝ) (first second : PremiseValues) : ℝ :=
  (|((first.ab : ℝ) - second.ab)| + |((first.bc : ℝ) - second.bc)| +
    |((first.c : ℝ) - second.c)|) / margin +
      |((first.b : ℝ) - second.b)| / margin^2

/-- The stability budget is nonnegative on its supported margin domain. -/
theorem perturbationBudget_nonneg (margin : ℝ) (positive : 0 < margin)
    (first second : PremiseValues) : 0 ≤ perturbationBudget margin first second := by
  unfold perturbationBudget
  positivity

@[simp] theorem perturbationBudget_self (margin : ℝ) (input : PremiseValues) :
    perturbationBudget margin input input = 0 := by
  simp [perturbationBudget]

/-- A conservative input-error bound when both middle marginals are separated from one. -/
theorem estimate_stable (first second : PremiseValues) (margin : ℝ) (positive : 0 < margin)
    (firstSeparated : margin ≤ 1-(first.b : ℝ))
    (secondSeparated : margin ≤ 1-(second.b : ℝ)) :
    |estimate first - estimate second| ≤ perturbationBudget margin first second := by
  have bPos := positive.trans_le firstSeparated
  have bPos' := positive.trans_le secondSeparated
  have notFull : (first.b : ℝ) ≠ 1 := by linarith
  have notFull' : (second.b : ℝ) ≠ 1 := by linarith
  have step₁ : |plnDeductionStrength first.ab first.bc first.b first.c -
      plnDeductionStrength second.ab first.bc first.b first.c| ≤
        |((first.ab : ℝ)-second.ab)| / margin := by
    rw [antecedent_difference _ _ _ _ _ notFull]
    exact quotient_bound (unit_difference first.bc.property first.c.property) positive firstSeparated
  have step₂ : |plnDeductionStrength second.ab first.bc first.b first.c -
      plnDeductionStrength second.ab second.bc first.b first.c| ≤
        |((first.bc : ℝ)-second.bc)| / margin := by
    rw [link_difference _ _ _ _ _ notFull]
    exact quotient_bound (unit_difference second.ab.property first.b.property) positive firstSeparated
  have step₃ : |plnDeductionStrength second.ab second.bc first.b first.c -
      plnDeductionStrength second.ab second.bc first.b second.c| ≤
        |((first.c : ℝ)-second.c)| / margin := by
    rw [target_difference _ _ _ _ _ notFull]
    have coefficient : |1-(second.ab : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr second.ab.property.2)]
      linarith [second.ab.property.1]
    exact quotient_bound coefficient positive firstSeparated
  have step₄ : |plnDeductionStrength second.ab second.bc first.b second.c -
      plnDeductionStrength second.ab second.bc second.b second.c| ≤
        |((first.b : ℝ)-second.b)| / margin^2 := by
    rw [middle_difference _ _ _ _ _ notFull notFull']
    have coefficient : |(1-(second.ab : ℝ))*((second.c : ℝ)-second.bc)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr second.ab.property.2)]
      have difference := unit_difference second.c.property second.bc.property
      nlinarith [abs_nonneg ((second.c : ℝ)-second.bc), second.ab.property.1, second.ab.property.2]
    have separation : margin^2 ≤ (1-(first.b : ℝ))*(1-(second.b : ℝ)) := by
      nlinarith [mul_le_mul firstSeparated secondSeparated positive.le bPos.le]
    rw [mul_assoc]
    exact quotient_bound coefficient (sq_pos_of_pos positive) separation
  have triangle₁ := abs_sub_le (estimate first)
    (plnDeductionStrength second.ab first.bc first.b first.c) (estimate second)
  have triangle₂ := abs_sub_le (plnDeductionStrength second.ab first.bc first.b first.c)
    (plnDeductionStrength second.ab second.bc first.b first.c) (estimate second)
  have triangle₃ := abs_sub_le (plnDeductionStrength second.ab second.bc first.b first.c)
    (plnDeductionStrength second.ab second.bc first.b second.c) (estimate second)
  unfold estimate at *
  unfold perturbationBudget
  rw [add_div, add_div]
  linarith

/-- Four probability readouts in the order AB, BC, B, C, with a declared
margin separating the middle marginal from one. -/
abbrev SeparatedPremises (margin : ℝ) :=
  {values : Fin 4 → ℝ // (∀ i, values i ∈ Set.Icc (0 : ℝ) 1) ∧ margin ≤ 1-values 2}

/-- Interpret the ordered coordinate vector as named premise values. -/
noncomputable def profile {margin : ℝ} (input : SeparatedPremises margin) : PremiseValues where
  ab := ⟨input.val 0, input.property.1 0⟩
  bc := ⟨input.val 1, input.property.1 1⟩
  b := ⟨input.val 2, input.property.1 2⟩
  c := ⟨input.val 3, input.property.1 3⟩

/-- Gain for the supremum metric on the four readout coordinates. -/
noncomputable def gain (margin : ℝ≥0) : ℝ≥0 := 3/margin + 1/margin^2

/-- The stability law in the form consumed by `ApproximationMap.comp`. -/
theorem estimate_lipschitz (margin : ℝ) (positive : 0 < margin) :
    LipschitzWith (gain ⟨margin, positive.le⟩) (fun input : SeparatedPremises margin => estimate (profile input)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have coordinate (index : Fin 4) : |first.val index - second.val index| ≤ dist first second := by
    exact dist_le_pi_dist first.val second.val index
  have summed : |first.val 0 - second.val 0| + |first.val 1 - second.val 1| +
      |first.val 3 - second.val 3| ≤ 3 * dist first second := by
    linarith [coordinate 0, coordinate 1, coordinate 3]
  have firstBound := estimate_stable (profile first) (profile second) margin positive
    first.property.2 second.property.2
  change |estimate (profile first) - estimate (profile second)| ≤ _
  refine firstBound.trans ?_
  change (|first.val 0 - second.val 0| + |first.val 1 - second.val 1| +
    |first.val 3 - second.val 3|) / margin + |first.val 2 - second.val 2| / margin^2 ≤ _
  calc
    _ ≤ (3 * dist first second)/margin + dist first second / margin^2 :=
      add_le_add (div_le_div_of_nonneg_right summed positive.le)
        (div_le_div_of_nonneg_right (coordinate 2) (sq_nonneg margin))
    _ = _ := by change _ = (3/margin + 1/margin^2)*dist first second; ring

end Mettapedia.PLN.Comparisons.DeductionStability
