import Mettapedia.GSLT.Scope.MonoidalConversionRates
import Mathlib.Tactic.FinCases

/-!
# Positive common measures and an actual three-edge obstruction

The balanced triangle exchanges with rates two, three and one sixth. Its
common measure prices the vertices at six, three and one. Changing the last
rate to two makes a closed walk yield eight and prevents every common measure
and log potential. Reversible transport uses the inverse rate on a backward
edge.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ConversionRates.Controls

open Graph

noncomputable section

inductive Triangle : Fin 3 → Fin 3 → Type where
  | first : Triangle 0 1
  | second : Triangle 1 2
  | third : Triangle 2 0

def balancedRate : {source target : Fin 3} → Triangle source target → ℝ
  | _, _, .first => 2
  | _, _, .second => 3
  | _, _, .third => 1 / 6

abbrev balanced : Graph (Fin 3) where
  Edge := Triangle
  rate := balancedRate
  positive edge := by cases edge <;> norm_num [balancedRate]

def value (token : Fin 3) : ℝ := if token.val = 0 then 6 else if token.val = 1 then 3 else 1

def commonValue : balanced.Valuation where
  price := value
  positive token := by fin_cases token <;> norm_num [value]
  respects edge := by cases edge <;> norm_num [balancedRate, value]

def triangleConnected : ∀ token : Fin 3, Trunc (balanced.Walk 0 token) :=
  Fin.cases (Trunc.mk (.nil 0))
    (Fin.cases (Trunc.mk (.forward .first (.nil 1)))
      (Fin.cases (Trunc.mk (.forward .first (.forward .second (.nil 2)))) (fun token => Fin.elim0 token)))

def cycle : balanced.Walk 0 0 := .forward .first (.forward .second (.forward .third (.nil 0)))

theorem cycle_yield_one : balanced.yield cycle = 1 := by
  norm_num [Graph.yield, cycle, balancedRate]

theorem all_cycles_are_balanced : balanced.NoArbitrage := Valuation.noArbitrage balanced commonValue

theorem canonical_unit_prices :
    (balanced.valuationOfNoArbitrage all_cycles_are_balanced triangleConnected).price =
      (Valuation.rescale balanced commonValue (1 / 6) (by norm_num)).price := by
  have same := Valuation.unique_at_root balanced triangleConnected
    (balanced.valuationOfNoArbitrage all_cycles_are_balanced triangleConnected)
    (Valuation.rescale balanced commonValue (1 / 6) (by norm_num)) (by
      rw [reconstructed_root_is_one]
      norm_num [Valuation.rescale, commonValue, value])
  exact congrArg Valuation.price same

def badRate : {source target : Fin 3} → Triangle source target → ℝ := fun _ => 2

abbrev bad : Graph (Fin 3) where
  Edge := Triangle
  rate := badRate
  positive _ := by norm_num [badRate]

def badCycle : bad.Walk 0 0 := .forward .first (.forward .second (.forward .third (.nil 0)))

theorem actual_cycle_yields_eight : bad.yield badCycle = 8 := by
  norm_num [Graph.yield, badCycle, badRate]

theorem cycle_prevents_a_common_measure : ¬ Nonempty bad.Valuation := by
  rintro ⟨valuation⟩
  have unitYield := Valuation.noArbitrage bad valuation badCycle
  rw [actual_cycle_yields_eight] at unitYield
  norm_num at unitYield

theorem cycle_prevents_a_log_potential : ¬ Nonempty bad.Potential := by
  rintro ⟨potential⟩
  exact cycle_prevents_a_common_measure ⟨Potential.toValuation bad potential⟩

theorem reverse_transport_is_not_an_extra_positive_rate :
    balanced.yield (.backward Triangle.third (.nil 2) : balanced.Walk 0 2) = 6 := by
  norm_num [Graph.yield, balancedRate]

end

end Mettapedia.GSLT.Scope.ConversionRates.Controls
