import Mettapedia.OSLF.NativeTypes.Structural.SpatialSplitReadout

open Mettapedia.OSLF.Framework

/-!
# Generated propositional judgments with executable decomposition

Propositional questions compose the actual root, positional and spatial
readouts. Components are executed in their derived carriers with the same
snapshot and permissions. A component formula requiring a further unsupported
search, including a modal atom, remains unknown.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

def readGeneratedFormula (request : Request) (state : State request) (componentBudget : Nat) :
    Formula → Option Bool
  | .top => some true
  | .bottom => some false
  | .atom _ => none
  | .conj first second => readBinary Bool.and
      (readGeneratedFormula request state componentBudget first)
      (readGeneratedFormula request state componentBudget second)
  | .disj first second => readBinary Bool.or
      (readGeneratedFormula request state componentBudget first)
      (readGeneratedFormula request state componentBudget second)
  | .imp first second => readBinary (fun left right => !left || right)
      (readGeneratedFormula request state componentBudget first)
      (readGeneratedFormula request state componentBudget second)
  | .neg formula => readNegation (readGeneratedFormula request state componentBudget formula)
  | .root index => readFrontierFormula request state (.root index)
  | .split index first second => readFrontierSplit request state index first second componentBudget
  | .spatial index first second => readFrontierSpatial request state index first second componentBudget

theorem readGeneratedFormula_sound {request : Request} {state : State request}
    (admitted : Admitted request) (atom : TypeExpr → Nat → Pattern → Prop)
    (componentBudget : Nat) (formula : Formula) :
    ReadoutCorrect (readGeneratedFormula request state componentBudget formula)
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request) atom request.expected formula request.root) := by
  induction formula with
  | top => simp [ReadoutCorrect, readGeneratedFormula, Holds]
  | bottom => simp [ReadoutCorrect, readGeneratedFormula, Holds]
  | atom index => simp [ReadoutCorrect, readGeneratedFormula]
  | conj first second left right => exact readBinary_conjunction_sound left right
  | disj first second left right => exact readBinary_disjunction_sound left right
  | imp first second left right => exact readBinary_implication_sound left right
  | neg formula inner => exact readNegation_sound inner
  | root index => exact readFrontierFormula_sound admitted atom (.root index)
  | split index first second _ _ =>
      exact readFrontierSplit_sound admitted atom index first second componentBudget
  | spatial index first second _ _ =>
      exact readFrontierSpatial_sound admitted atom index first second componentBudget

theorem checked_split_true_iff {request : Request} {state : State request}
    (admitted : Admitted request) {index : Nat} {declaration : GrammarRule}
    (lookup : request.plan.snapshot.language.terms[index]? = some declaration)
    (atom : TypeExpr → Nat → Pattern → Prop) (shape : BinaryShape)
    (first second : Formula) (budget : Nat)
    (checked : splitCoverage request state declaration shape first second budget = true) :
    readSplitCases request state declaration shape first second budget = some true ↔
      SplitHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request request.expected) ⟨index, declaration⟩
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.firstSort first)
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.secondSort second) request.root := by
  have sound := readSplitCases_sound (state := state) admitted lookup atom shape first second budget
  constructor
  · intro read
    exact (sound true read).mp rfl
  · intro holds
    obtain ⟨answer, read⟩ := checked_split_conclusive checked
    have positive := (sound answer read).mpr holds
    simpa only [positive] using read

theorem checked_spatial_true_iff {request : Request} {state : State request}
    (admitted : Admitted request) {index : Nat} {declaration : GrammarRule}
    (lookup : request.plan.snapshot.language.terms[index]? = some declaration)
    (expected : request.expected = .base declaration.category) {shape : SpatialShape}
    (shapeChecked : spatialShape? request.plan.snapshot.language declaration = some shape)
    (atom : TypeExpr → Nat → Pattern → Prop) (first second : Formula) (budget : Nat)
    (checked : spatialCoverage request state first second budget = true) :
    readSpatialCases request state first second budget = some true ↔
      SpatialHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request request.expected) ⟨index, declaration⟩
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected first)
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected second) request.root := by
  have sound := readSpatialCases_sound (state := state) admitted lookup expected shapeChecked
    atom first second budget
  constructor
  · intro read
    exact (sound true read).mp rfl
  · intro holds
    obtain ⟨answer, read⟩ := checked_spatial_conclusive checked
    have positive := (sound answer read).mpr holds
    simpa only [positive] using read

end Mettapedia.OSLF.NativeTypes.Structural
