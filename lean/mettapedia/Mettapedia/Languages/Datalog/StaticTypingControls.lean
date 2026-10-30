import Mettapedia.Languages.Datalog.StaticTyping

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.StaticTyping.Controls

private def signature : Signature
  | ["Edge"] => some [.symbol, .symbol]
  | ["Reach"] => some [.symbol, .symbol]
  | ["Count"] => some [.number]
  | ["Unsigned"] => some [.unsigned]
  | ["Float"] => some [.floating]
  | _ => none

private def context : VariableTypes
  | "X" | "Y" => some .symbol
  | "N" => some .number
  | _ => none

private def edge (first second : Argument) : Atom := ⟨["Edge"], [first, second]⟩
private def reach (first second : Argument) : Atom := ⟨["Reach"], [first, second]⟩
private def x : Argument := .var "X"
private def y : Argument := .var "Y"

private def guarded : Clause :=
  ⟨reach x y, [.atom (edge x y), .comparison ⟨.different, x, .literal (.symbol "blocked")⟩]⟩

theorem primitive_types_and_bounds :
    checkFact signature ⟨["Count"], [.number (-(2 ^ 63))]⟩ = true ∧
    checkFact signature ⟨["Count"], [.number (2 ^ 63 - 1)]⟩ = true ∧
    checkFact signature ⟨["Unsigned"], [.unsigned (2 ^ 64 - 1)]⟩ = true ∧
    checkFact signature ⟨["Float"], [.floating 0x8000000000000000]⟩ = true ∧
    checkFact signature ⟨["Count"], [.number (2 ^ 63)]⟩ = false ∧
    checkFact signature ⟨["Count"], [.number (-(2 ^ 63) - 1)]⟩ = false ∧
    checkFact signature ⟨["Unsigned"], [.unsigned (2 ^ 64)]⟩ = false ∧
    checkFact signature ⟨["Count"], [.symbol "1"]⟩ = false ∧
    checkFact signature ⟨["Missing"], []⟩ = false ∧
    checkFact signature ⟨["Count"], []⟩ = false ∧
    checkFact signature ⟨["Count"], [.number 1, .number 2]⟩ = false := by
  decide +kernel

theorem clause_separating_controls :
    checkClause signature context guarded = true ∧
    checkClause signature context ⟨reach x (.literal (.symbol "a")),
      [.atom (edge x .anonymous)]⟩ = true ∧
    checkClause signature context ⟨reach x y, [.atom (edge x (.var "N"))]⟩ = false ∧
    checkClause signature context ⟨reach x y, [.atom (edge x (.var "Unknown"))]⟩ = false ∧
    checkClause signature context ⟨reach x y, [.atom (edge x .anonymous)]⟩ = false ∧
    checkClause signature context ⟨reach x y, [.atom (edge x y),
      .comparison ⟨.less, x, .literal (.number 2)⟩]⟩ = false ∧
    checkClause signature context ⟨reach x y, [.atom (edge x y),
      .comparison ⟨.equal, x, .anonymous⟩]⟩ = false ∧
    checkClause signature context ⟨reach x y, [.atom (edge x y),
      .comparison ⟨.equal, .var "N", .literal (.number 1)⟩]⟩ = false ∧
    checkClause signature context ⟨reach .anonymous y, [.atom (edge x y)]⟩ = false := by
  decide +kernel

/-- Static acceptance does not decide whether a well-typed guard succeeds. -/
theorem static_acceptance_does_not_execute_comparisons :
    checkComparison context ⟨.less, .literal (.number 2), .literal (.number 1)⟩ = true ∧
    checkComparison context ⟨.equal, .literal (.floating 0),
      .literal (.floating 0x8000000000000000)⟩ = true := by
  decide +kernel

#print axioms primitive_types_and_bounds
#print axioms clause_separating_controls
#print axioms static_acceptance_does_not_execute_comparisons

end Mettapedia.Languages.Datalog.StaticTyping.Controls
