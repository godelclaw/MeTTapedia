import Mettapedia.Languages.HOLLight.MeTTa.TypeSubstitution
import Mettapedia.Languages.HOLLight.DefinitionAdapters

/-!
# Contextual representations of the existing shared HOL terms

The authored library retains a type on each positional occurrence. Shared HOL
syntax stores that type in the context instead. This module reconstructs the
annotation from that context, and proves that closed checked replacements have
the same representation beneath additional binders. A missing context entry is
represented explicitly by `None`; it is never assigned an invented carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Representation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open TypeSubstitution (nameAtom typeAtom)
open Mettapedia.Languages.OpenTheory.SignatureFormation
open DefinitionAdapters

mutual
  /-- Faithfulness of a chosen operator representation lifts to all finite
  simple types, retaining complete variable names and operator identities. -/
  theorem typeAtom_injective (operators : TypeOp → Atom)
      (faithful : Function.Injective operators) (left right : Ty)
      (same : typeAtom operators left = typeAtom operators right) : left = right := by
    cases left with
    | var name =>
        cases right with
        | var other =>
            simp only [typeAtom, Atom.expression.injEq, List.cons.injEq,
              true_and] at same
            exact congrArg Ty.var (TypeSubstitution.nameAtom_injective same.1)
        | op _ _ => simp [typeAtom] at same
    | op operator arguments =>
        cases right with
        | var _ => simp [typeAtom] at same
        | op other values =>
            simp only [typeAtom, Atom.expression.injEq, List.cons.injEq,
              true_and] at same
            have operatorSame := faithful same.1
            have argumentsSame := typesAtom_injective operators faithful arguments values same.2.1
            subst other
            subst values
            rfl
  termination_by sizeOf left

  private theorem typesAtom_injective (operators : TypeOp → Atom)
      (faithful : Function.Injective operators) (left right : List Ty)
      (same : Premises.keys (left.map (typeAtom operators)) =
        Premises.keys (right.map (typeAtom operators))) : left = right := by
    cases left with
    | nil =>
        cases right <;> simp [Premises.keys] at same ⊢
    | cons first rest =>
        cases right with
        | nil => simp [Premises.keys] at same
        | cons value values =>
            simp only [List.map_cons, Premises.keys, Atom.expression.injEq,
              List.cons.injEq, true_and] at same
            have firstSame := typeAtom_injective operators faithful first value same.1
            have restSame := typesAtom_injective operators faithful rest values same.2.1
            subst value
            subst values
            rfl
  termination_by sizeOf left
end

/-- The payload for a free variable includes both its name and its type. -/
def variableAtom (operators : TypeOp → Atom) (sourceVar : SourceVar) : Atom :=
  .expression [.symbol "HOL:Free", nameAtom sourceVar.name, typeAtom operators sourceVar.ty]

theorem variableAtom_injective (operators : TypeOp → Atom)
    (faithful : Function.Injective operators) : Function.Injective (variableAtom operators) := by
  intro left right same
  rcases left with ⟨leftName, leftType⟩
  rcases right with ⟨rightName, rightType⟩
  simp only [variableAtom, Atom.expression.injEq, List.cons.injEq,
    true_and] at same
  have names := TypeSubstitution.nameAtom_injective same.1
  have types := typeAtom_injective operators faithful leftType rightType same.2.1
  subst rightName
  subst rightType
  rfl

def registeredOperatorAtom (operator : TypeOp) : Atom :=
  nameAtom (sourceOperatorName (operatorName operator))

@[simp] theorem registered_function_atom : registeredOperatorAtom TypeOp.function =
    .grounded (.string "fun") := by
  simp [registeredOperatorAtom, operatorName, TypeOp.function, sourceOperatorName]

@[simp] theorem registered_boolean_atom : registeredOperatorAtom TypeOp.bool =
    .grounded (.string "bool") := by decide

mutual
  /-- Registered declarations, rather than arbitrary printed raw symbols,
  supply the identity needed to reflect equality of encoded simple types. -/
  theorem registered_typeAtom_injective (context : TheoryContext) (left right : Ty)
      (leftFormed : TypeFormed context.signature left)
      (rightFormed : TypeFormed context.signature right)
      (same : typeAtom registeredOperatorAtom left = typeAtom registeredOperatorAtom right) : left = right := by
    cases left with
    | var name =>
        cases right with
        | var other =>
            simp only [typeAtom, Atom.expression.injEq, List.cons.injEq,
              true_and] at same
            exact congrArg Ty.var (TypeSubstitution.nameAtom_injective same.1)
        | op _ _ => simp [typeAtom] at same
    | op operator arguments =>
        cases right with
        | var _ => simp [typeAtom] at same
        | op other values =>
            simp only [TypeFormed] at leftFormed rightFormed
            simp only [typeAtom, Atom.expression.injEq, List.cons.injEq,
              true_and] at same
            have names := sourceOperatorName_injective
              (TypeSubstitution.nameAtom_injective same.1)
            have operatorSame := context.uniqueTypeNames _ _ _ _ leftFormed.1 rightFormed.1 names
            have argumentsSame := registered_typesAtom_injective context arguments values
              leftFormed.2 rightFormed.2 same.2.1
            subst other
            subst values
            rfl
  termination_by sizeOf left

  private theorem registered_typesAtom_injective (context : TheoryContext) (left right : List Ty)
      (leftFormed : ∀ type ∈ left, TypeFormed context.signature type)
      (rightFormed : ∀ type ∈ right, TypeFormed context.signature type)
      (same : Premises.keys (left.map (typeAtom registeredOperatorAtom)) =
        Premises.keys (right.map (typeAtom registeredOperatorAtom))) : left = right := by
    cases left with
    | nil => cases right <;> simp [Premises.keys] at same ⊢
    | cons first rest =>
        cases right with
        | nil => simp [Premises.keys] at same
        | cons value values =>
            simp only [List.map_cons, Premises.keys, Atom.expression.injEq,
              List.cons.injEq, true_and] at same
            have firstSame := registered_typeAtom_injective context first value
              (leftFormed first (by simp)) (rightFormed value (by simp)) same.1
            have restSame := registered_typesAtom_injective context rest values
              (fun type member => leftFormed type (by simp [member]))
              (fun type member => rightFormed type (by simp [member])) same.2.1
            subst value
            subst values
            rfl
  termination_by sizeOf left
end

theorem registered_variableAtom_eq_iff (context : TheoryContext) (left right : SourceVar)
    (leftFormed : TypeFormed context.signature left.ty)
    (rightFormed : TypeFormed context.signature right.ty) :
    variableAtom registeredOperatorAtom left = variableAtom registeredOperatorAtom right ↔ left = right := by
  constructor
  · intro same
    rcases left with ⟨leftName, leftType⟩
    rcases right with ⟨rightName, rightType⟩
    simp only [variableAtom, Atom.expression.injEq, List.cons.injEq,
      true_and] at same
    have names := TypeSubstitution.nameAtom_injective same.1
    have types := registered_typeAtom_injective context leftType rightType leftFormed rightFormed same.2.1
    subst rightName
    subst rightType
    rfl
  · rintro rfl
    rfl

/-- The source binder carries the same typed identity before positional
elaboration; only the syntax constructor differs from a free occurrence. -/
def sourceVariableAtom (operators : TypeOp → Atom) (sourceVar : SourceVar) : Atom :=
  .expression [.symbol "Var", nameAtom sourceVar.name, typeAtom operators sourceVar.ty]

theorem registered_sourceVariableAtom_eq_iff (context : TheoryContext) (left right : SourceVar)
    (leftFormed : TypeFormed context.signature left.ty)
    (rightFormed : TypeFormed context.signature right.ty) :
    sourceVariableAtom registeredOperatorAtom left = sourceVariableAtom registeredOperatorAtom right ↔
      left = right := by
  simpa only [sourceVariableAtom, variableAtom, Atom.expression.injEq, List.cons.injEq,
    true_and] using registered_variableAtom_eq_iff context left right leftFormed rightFormed

/-- Reconstruct only the annotations available in the actual binder context.
Operator and constant payloads are retained, not interpreted or admitted here. -/
def termAtom (operators : TypeOp → Atom) (constants : Const → Atom)
    (context : List Ty) : DBTerm → Atom
  | .const constant type => .expression [.symbol "HOL:C", constants constant, typeAtom operators type]
  | .free sourceVar => variableAtom operators sourceVar
  | .bound index => .expression [.symbol "HOL:Bound", .grounded (.int index),
      ((context[index]?).map (typeAtom operators)).getD (.symbol "None")]
  | .app function argument => .expression [.symbol "HOL:App",
      termAtom operators constants context function, termAtom operators constants context argument]
  | .abs domain body => .expression [.symbol "HOL:Lam", typeAtom operators domain,
      termAtom operators constants (domain :: context) body]
termination_by term => sizeOf term

/-- Retained theorem data keeps the conclusion, ordered hypotheses,
dependencies and origin. This constructor supplies no admission by itself. -/
@[simp] def theoremAtom (constants : Const → Atom) (context : List Ty)
    (conclusion : DBTerm) (hypotheses dependencies : List Atom) (origin : Atom) : Atom :=
  .expression [.symbol "HOL:Thm", Premises.keys hypotheses,
    termAtom registeredOperatorAtom constants context conclusion, Premises.keys dependencies, origin]

/-- A checked term does not acquire different positional annotations when
additional binders are placed outside its existing context. -/
theorem termAtom_append_context (operators : TypeOp → Atom) (constants : Const → Atom)
    {term : DBTerm} {context : List Ty} {type : Ty}
    (checked : term.inferType context = some type) (suffix : List Ty) :
    termAtom operators constants (context ++ suffix) term =
      termAtom operators constants context term := by
  induction term generalizing context type with
  | const => simp only [termAtom]
  | free => simp only [termAtom]
  | bound index =>
      simp only [DBTerm.inferType] at checked
      obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp checked
      simp only [termAtom, List.getElem?_append_left inRange]
  | app function argument functionIH argumentIH =>
      simp only [DBTerm.inferType] at checked
      cases functionType : function.inferType context with
      | none => simp [functionType] at checked
      | some domain =>
          cases argumentType : argument.inferType context with
          | none => simp [functionType, argumentType] at checked
          | some valueType =>
              simp only [termAtom, functionIH functionType, argumentIH argumentType]
  | abs domain body bodyIH =>
      simp only [DBTerm.inferType] at checked
      cases bodyType : body.inferType (domain :: context) with
      | none => simp [bodyType] at checked
      | some codomain =>
          have bodySame := bodyIH bodyType
          simpa only [termAtom, List.cons_append] using congrArg
            (fun value => Atom.expression [.symbol "HOL:Lam", typeAtom operators domain, value]) bodySame

/-- This is the capture boundary needed by authored term substitution: a stored
checked replacement keeps all its free occurrences beneath any binder context. -/
theorem checked_replacement_context_independent (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CheckedSourceTerm) (context : List Ty) :
    termAtom operators constants context replacement.canonical.term =
      termAtom operators constants [] replacement.canonical.term := by
  simpa using termAtom_append_context operators constants replacement.canonical.checked context

end Mettapedia.Languages.HOLLight.MeTTa.Representation
