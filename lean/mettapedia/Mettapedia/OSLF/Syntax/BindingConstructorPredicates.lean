import Mettapedia.OSLF.Syntax.FreeBindingClone

/-!
# Constructor predicates in substitution-compatible binding models

A structural predicate is an image of the actual binding operation, rather
than a test of a chosen representative's outer constructor. Each argument
has its own predicate in its declared binder context. A receipt retains all
arguments and their certificates. Semantic substitution transports the
complete receipt, including the environment lifted beneath each binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingConstructorPredicates

open FreeBindingTerms BindingSubstitutionAlgebra

universe u

variable {S : Signature} (A : BindingCloneAlgebra.Algebra.{u} S)

/-- A context-indexed predicate stable under arbitrary semantic substitution. -/
structure Predicate (sort : S.Srt) where
  holds : {Γ : Ctx S} → A.substitution.Carrier Γ sort → Prop
  substitute : ∀ {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (value : A.substitution.Carrier Γ sort),
    holds value → holds (A.substitution.substitute env value)

/-- The always-admitted argument predicate. -/
def top (sort : S.Srt) : Predicate A sort where
  holds := fun _ => True
  substitute := by intros; trivial

/-- Independent predicates for the ordered arguments of a binding operation. -/
inductive Arguments : List (List S.Srt × S.Srt) → Type u where
  | nil : Arguments []
  | cons {binders : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} :
      Predicate A sort → Arguments rest → Arguments ((binders, sort) :: rest)

variable {A}

/-- Read every argument certificate in its exact binder-extended context. -/
def Arguments.Holds : {arity : List (List S.Srt × S.Srt)} →
    Arguments A arity → {Γ : Ctx S} →
      FamilyArgs S A.substitution.Carrier arity Γ → Prop
  | _, .nil, _, .nil => True
  | _, .cons head tail, _, .cons value rest => head.holds value ∧ tail.Holds rest

/-- Argument predicates remain true after lifting the actual environment
past each argument's declared binders. -/
theorem Arguments.substitute : ∀ {arity : List (List S.Srt × S.Srt)}
    (inputs : Arguments A arity) {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (values : FamilyArgs S A.substitution.Carrier arity Γ),
    inputs.Holds values → inputs.Holds (A.substitution.substituteArgs env values)
  | _, .nil, _, _, _, .nil, _ => trivial
  | _, .cons head tail, _, _, env,
      .cons (bs := binders) value rest, admitted => by
      change head.holds value ∧ tail.Holds rest at admitted
      change head.holds (A.substitution.substitute
        (A.substitution.liftEnvironment env binders) value) ∧
          tail.Holds (A.substitution.substituteArgs env rest)
      exact ⟨head.substitute (A.substitution.liftEnvironment env binders) value admitted.1,
        tail.substitute env rest admitted.2⟩

variable (A)

/-- A structural receipt retains the complete ordered argument vector,
its certificates and the actual operation's result. -/
structure Receipt {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator))
    (value : A.substitution.Carrier Γ sort) where
  arguments : FamilyArgs S A.substitution.Carrier (S.arity operator) Γ
  admitted : inputs.Holds arguments
  output : A.operation operator arguments = value

variable {A}

/-- Substitution transports an actual receipt; its result equation follows
from the binding model's earned operation/substitution compatibility. -/
def Receipt.substitute {Γ Δ : Ctx S} {sort : S.Srt} {operator : S.Op sort}
    {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (receipt : Receipt A operator inputs value) :
    Receipt A operator inputs (A.substitution.substitute env value) where
  arguments := A.substitution.substituteArgs env receipt.arguments
  admitted := inputs.substitute env receipt.arguments receipt.admitted
  output := (A.operation_substitute env operator receipt.arguments).symm.trans
    (congrArg (A.substitution.substitute env) receipt.output)

variable (A)

/-- The image predicate forgets the receipt only when a proposition is wanted. -/
def image {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) : Predicate A sort where
  holds := fun value => Nonempty (Receipt A operator inputs value)
  substitute := by
    rintro Γ Δ env value ⟨receipt⟩
    exact ⟨receipt.substitute env⟩

/-- An admitted complete argument vector supplies a structural receipt. -/
def introduce {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator))
    (arguments : FamilyArgs S A.substitution.Carrier (S.arity operator) Γ)
    (admitted : inputs.Holds arguments) :
    Receipt A operator inputs (A.operation operator arguments) where
  arguments := arguments
  admitted := admitted
  output := rfl

/-- Image membership has the expected existential readout, including the
independently supplied argument predicates. -/
theorem image_iff {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator))
    (value : A.substitution.Carrier Γ sort) :
    (image A operator inputs).holds value ↔
      ∃ arguments, inputs.Holds arguments ∧ A.operation operator arguments = value := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.arguments, receipt.admitted, receipt.output⟩
  · rintro ⟨arguments, admitted, output⟩
    exact ⟨⟨arguments, admitted, output⟩⟩

variable {A}

/-- An image consumer receives the entire supplied argument vector. -/
def Receipt.eliminate {Γ : Ctx S} {sort : S.Srt} {operator : S.Op sort}
    {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort} {Result : Type u}
    (read : ∀ arguments : FamilyArgs S A.substitution.Carrier (S.arity operator) Γ,
      inputs.Holds arguments → A.operation operator arguments = value → Result)
    (receipt : Receipt A operator inputs value) : Result :=
  read receipt.arguments receipt.admitted receipt.output

/-- The transported receipt's argument readout is the complete semantic
substitution vector, rather than a chosen result representative. -/
theorem Receipt.substitute_arguments {Γ Δ : Ctx S} {sort : S.Srt}
    {operator : S.Op sort} {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (receipt : Receipt A operator inputs value) :
    (receipt.substitute env).arguments =
      A.substitution.substituteArgs env receipt.arguments := rfl

end Mettapedia.OSLF.Binding.BindingConstructorPredicates
