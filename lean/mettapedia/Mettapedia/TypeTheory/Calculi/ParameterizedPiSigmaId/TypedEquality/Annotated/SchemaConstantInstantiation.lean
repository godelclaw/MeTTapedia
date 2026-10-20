import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas

/-!
# Constant interpretations through annotated schemas and their premises

A constant interpretation may replace names inside an instance's arguments.
When it fixes the schema templates and their inferred variable/equation types,
the result is another instance of the same schema, with precisely the mapped
required evidence. Root stability alone would not supply that premise law.

The resulting self-interpretation additionally checks original constant values
and their complete declared types. No search, new evaluator or computation
admission is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Annotated

variable {Head : Type}

theorem patternPremises_instConsts_of_fixed
    (declared : DeclName → Option (CTm Head 0)) (interpret : DeclName → CTm Head 0)
    {arity scope : Nat} (left : Tm Head arity) (assignment : CSub Head arity scope)
    (knowledge : ∀ index type, patternKnowledge declared none left index = some type →
      type.instConsts interpret = type)
    (equations : ∀ equation ∈ patternEquations declared none left,
      equation.1.instConsts interpret = equation.1 ∧
      equation.2.1.instConsts interpret = equation.2.1 ∧
      equation.2.2.instConsts interpret = equation.2.2) :
    (patternPremises declared left assignment).map (CPremise.instConsts interpret) =
      patternPremises declared left (fun index => (assignment index).instConsts interpret) := by
  unfold patternPremises
  rw [List.map_append, List.map_filterMap, List.map_map]
  congr 1
  · refine List.filterMap_congr fun index _ => ?_
    cases found : patternKnowledge declared none left index with
    | none => rfl
    | some type =>
        simp only [Option.map_some, CPremise.instConsts,
          CTm.instConsts_subst, knowledge index type found]
  · refine List.map_congr_left fun equation member => ?_
    obtain ⟨first, second, type⟩ := equations equation member
    simp only [Function.comp_apply, CPremise.instConsts, CTm.instConsts_subst,
      first, second, type]

/-- Support obligations for a fixed schema family under a constant
interpretation. Instance arguments themselves need not be fixed. -/
structure SchemaConstantsFixed (declared : DeclName → Option (CTm Head 0))
    (family : AlgebraicSchema.SchemaFamily Head) (interpret : DeclName → CTm Head 0) : Prop where
  left : ∀ {arity : Nat} {left right : Tm Head arity}, family left right →
    (elabLeft declared left).instConsts interpret = elabLeft declared left
  right : ∀ {arity : Nat} {left right : Tm Head arity}, family left right →
    (elabRight declared left right).instConsts interpret = elabRight declared left right
  knowledge : ∀ {arity : Nat} {left right : Tm Head arity}, family left right →
    ∀ index type, patternKnowledge declared none left index = some type →
      type.instConsts interpret = type
  equations : ∀ {arity : Nat} {left right : Tm Head arity}, family left right →
    ∀ equation ∈ patternEquations declared none left,
      equation.1.instConsts interpret = equation.1 ∧
      equation.2.1.instConsts interpret = equation.2.1 ∧
      equation.2.2.instConsts interpret = equation.2.2

theorem SchemaConstantsFixed.root {declared : DeclName → Option (CTm Head 0)}
    {family : AlgebraicSchema.SchemaFamily Head} {interpret : DeclName → CTm Head 0}
    (fixed : SchemaConstantsFixed declared family interpret) {n : Nat} {left right : CTm Head n}
    (step : (elaboratedComputation declared family).step left right) :
    (elaboratedComputation declared family).step
      (left.instConsts interpret) (right.instConsts interpret) := by
  cases step with
  | instantiate elaborated assignment =>
      obtain ⟨L, R, selected, rfl, rfl⟩ := elaborated
      rw [CTm.instConsts_subst, CTm.instConsts_subst, fixed.left selected, fixed.right selected]
      exact .instantiate ⟨L, R, selected, rfl, rfl⟩ _

theorem SchemaConstantsFixed.requires {declared : DeclName → Option (CTm Head 0)}
    {family : AlgebraicSchema.SchemaFamily Head} {interpret : DeclName → CTm Head 0}
    (fixed : SchemaConstantsFixed declared family interpret) {n : Nat} {left right : CTm Head n}
    {premises : List (CPremise Head n)}
    (required : (elaboratedComputation declared family).requires left right premises) :
    (elaboratedComputation declared family).requires
      (left.instConsts interpret) (right.instConsts interpret)
      (premises.map (CPremise.instConsts interpret)) := by
  cases required with
  | instantiate selected assignment =>
      rw [CTm.instConsts_subst, CTm.instConsts_subst, fixed.left selected, fixed.right selected,
        patternPremises_instConsts_of_fixed _ _ _ _ (fixed.knowledge selected) (fixed.equations selected)]
      exact .instantiate selected _

/-- The maintained rule-instance interface retains constant formation,
root computation and the entire required-premise map. -/
theorem ChurchRules.ofSchemas_constInstance {R : Rules Head}
    (family : AlgebraicSchema.SchemaFamily Head) (presentation : Presents R.computation family)
    (interpret : DeclName → CTm Head 0)
    (names : ∀ {name : DeclName} {type : CTm Head 0},
      (ChurchRules.ofSchemas R family presentation).constantType name = some type →
        interpret name = .const name)
    (types : ∀ {name : DeclName} {type : CTm Head 0},
      (ChurchRules.ofSchemas R family presentation).constantType name = some type →
        type.instConsts interpret = type)
    (schemas : SchemaConstantsFixed
      (ChurchRules.ofSchemas R family presentation).constantType family interpret) :
    ConstInstance (ChurchRules.ofSchemas R family presentation)
      (ChurchRules.ofSchemas R family presentation) interpret where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  typed := by
    intro name type level declared typed isUniverse
    rw [types declared] at typed ⊢
    rw [names declared]
    simpa only [CTm.liftClosed_zero] using CDerivable.const (Γ := .nil) declared typed isUniverse
  steps := schemas.root
  requires := fun _ required => schemas.requires required

end TypedEquality.Annotated
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
