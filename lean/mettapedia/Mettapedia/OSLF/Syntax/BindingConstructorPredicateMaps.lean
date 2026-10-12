import Mettapedia.OSLF.Syntax.BindingConstructorPredicates
import Mettapedia.OSLF.Syntax.BindingOperationPresheaf

/-!
# Interpretation and coherence of binding constructor receipts

Binding-clone maps transport the actual constructor arguments and their
certificates. Image membership is preserved. Reflection additionally needs
argument lifting and value injectivity; it is not inferred from object
coverage. The receipt substitution laws reuse the full binder-sensitive
argument substitution laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingConstructorPredicates

open FreeBindingTerms BindingSubstitutionAlgebra

universe u

variable {S : Signature} {A B : BindingCloneAlgebra.Algebra.{u} S}

/-- Pull back a native predicate along the complete clone interpretation. -/
def pullback {sort : S.Srt} (mapping : FreeBindingClone.Hom A B)
    (predicate : Predicate B sort) : Predicate A sort where
  holds := fun value => predicate.holds (mapping.raw.map value)
  substitute := by
    intro Γ Δ env value admitted
    simpa only [mapping.map_substitute] using
      predicate.substitute (fun sort position => mapping.raw.map (env sort position))
        (mapping.raw.map value) admitted

/-- Interpret every independent argument predicate at its own sort. -/
def Arguments.pullback (mapping : FreeBindingClone.Hom A B) :
    {arity : List (List S.Srt × S.Srt)} → Arguments B arity → Arguments A arity
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons (BindingConstructorPredicates.pullback mapping head) (tail.pullback mapping)

/-- Reading the pulled-back input family agrees with mapping the complete
ordered vector, including all binder-extended heads. -/
theorem Arguments.holds_pullback (mapping : FreeBindingClone.Hom A B) :
    ∀ {arity : List (List S.Srt × S.Srt)} (inputs : Arguments B arity)
      {Γ : Ctx S} (values : FamilyArgs S A.substitution.Carrier arity Γ),
      (inputs.pullback mapping).Holds values ↔
        inputs.Holds (FamilyArgs.map mapping.raw.map values)
  | _, .nil, _, .nil => Iff.rfl
  | _, .cons head tail, _, .cons value rest => by
      change (head.holds (mapping.raw.map value) ∧
        (tail.pullback mapping).Holds rest) ↔
          (head.holds (mapping.raw.map value) ∧
            tail.Holds (FamilyArgs.map mapping.raw.map rest))
      exact and_congr Iff.rfl (tail.holds_pullback mapping rest)

/-- Interpretation retains the entire supplied source argument receipt. -/
def Receipt.map {Γ : Ctx S} {sort : S.Srt} {operator : S.Op sort}
    {inputs : Arguments B (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (mapping : FreeBindingClone.Hom A B)
    (receipt : Receipt A operator (inputs.pullback mapping) value) :
    Receipt B operator inputs (mapping.raw.map value) where
  arguments := FamilyArgs.map mapping.raw.map receipt.arguments
  admitted := (inputs.holds_pullback mapping receipt.arguments).mp receipt.admitted
  output := (mapping.raw.map_operation operator receipt.arguments).symm.trans
    (congrArg mapping.raw.map receipt.output)

theorem image_preserved {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (mapping : FreeBindingClone.Hom A B)
    (inputs : Arguments B (S.arity operator))
    (value : A.substitution.Carrier Γ sort) :
    (image A operator (inputs.pullback mapping)).holds value →
      (image B operator inputs).holds (mapping.raw.map value) := by
  rintro ⟨receipt⟩
  exact ⟨receipt.map mapping⟩

/-- Componentwise value surjectivity lifts complete binding argument
vectors, rather than only the final result carrier. -/
theorem arguments_surjective (mapping : FreeBindingClone.Hom A B)
    (surjective : ∀ (Γ : Ctx S) (sort : S.Srt), Function.Surjective
      (fun value : A.substitution.Carrier Γ sort => mapping.raw.map value)) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S},
      Function.Surjective (fun values : FamilyArgs S A.substitution.Carrier arity Γ =>
        FamilyArgs.map mapping.raw.map values)
  | _, _, .nil => ⟨.nil, rfl⟩
  | _, _, .cons head tail => by
      obtain ⟨sourceHead, headEq⟩ := surjective _ _ head
      obtain ⟨sourceTail, tailEq⟩ := arguments_surjective mapping surjective tail
      exact ⟨.cons sourceHead sourceTail, congrArg₂ FamilyArgs.cons headEq tailEq⟩

/-- A faithful value map with complete argument lifting reflects the
independently formed target constructor image. -/
theorem image_reflected {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (mapping : FreeBindingClone.Hom A B)
    (injective : Function.Injective
      (fun value : A.substitution.Carrier Γ sort => mapping.raw.map value))
    (lift : Function.Surjective
      (fun values : FamilyArgs S A.substitution.Carrier (S.arity operator) Γ =>
        FamilyArgs.map mapping.raw.map values))
    (inputs : Arguments B (S.arity operator))
    (value : A.substitution.Carrier Γ sort) :
    (image A operator (inputs.pullback mapping)).holds value ↔
      (image B operator inputs).holds (mapping.raw.map value) := by
  constructor
  · exact image_preserved operator mapping inputs value
  · rintro ⟨receipt⟩
    obtain ⟨arguments, argumentEq⟩ := lift receipt.arguments
    refine ⟨⟨arguments, ?_, ?_⟩⟩
    · apply (inputs.holds_pullback mapping arguments).mpr
      exact (congrArg (fun values : FamilyArgs S B.substitution.Carrier
        (S.arity operator) Γ => inputs.Holds values) argumentEq).symm ▸ receipt.admitted
    · apply injective
      exact (mapping.raw.map_operation operator arguments).trans
        ((congrArg (fun values : FamilyArgs S B.substitution.Carrier
          (S.arity operator) Γ => B.operation operator values) argumentEq).trans receipt.output)

/-- Equality of outputs only changes the result index; the argument
receipt remains intact. -/
def Receipt.retype {Γ : Ctx S} {sort : S.Srt} {operator : S.Op sort}
    {inputs : Arguments A (S.arity operator)}
    {first second : A.substitution.Carrier Γ sort}
    (receipt : Receipt A operator inputs first) (equal : first = second) :
    Receipt A operator inputs second where
  arguments := receipt.arguments
  admitted := receipt.admitted
  output := receipt.output.trans equal

@[ext] theorem Receipt.ext {Γ : Ctx S} {sort : S.Srt} {operator : S.Op sort}
    {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    {first second : Receipt A operator inputs value}
    (arguments : first.arguments = second.arguments) : first = second := by
  cases first
  cases second
  cases arguments
  rfl

/-- Identity substitution preserves the complete receipt after the earned
result identity is applied. -/
theorem Receipt.substitute_identity {Γ : Ctx S} {sort : S.Srt}
    {operator : S.Op sort} {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (receipt : Receipt A operator inputs value) :
    (receipt.substitute (fun _ position => A.substitution.injectVar position)).retype
        (A.substitution.substitute_identity value) = receipt := by
  apply Receipt.ext
  exact BindingOperationPresheaf.substituteArgs_identity A.substitution receipt.arguments

/-- Successive substitutions compose on the whole receipt, with each
binding argument kept in its proper extended context. -/
theorem Receipt.substitute_comp {Γ Δ Θ : Ctx S} {sort : S.Srt}
    {operator : S.Op sort} {inputs : Arguments A (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (first : Environment S A.substitution.Carrier Γ Δ)
    (second : Environment S A.substitution.Carrier Δ Θ)
    (receipt : Receipt A operator inputs value) :
    ((receipt.substitute first).substitute second).retype
        (A.substitution.substitute_comp first second value) =
      receipt.substitute (fun sort position =>
        A.substitution.substitute second (first sort position)) := by
  apply Receipt.ext
  exact BindingOperationPresheaf.substituteArgs_comp
    A.substitution first second receipt.arguments

/-- Interpreting and then substituting agrees on the complete argument
readout with substituting and then interpreting. -/
theorem Receipt.map_substitute_arguments {Γ Δ : Ctx S} {sort : S.Srt}
    {operator : S.Op sort} {inputs : Arguments B (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (mapping : FreeBindingClone.Hom A B)
    (env : Environment S A.substitution.Carrier Γ Δ)
    (receipt : Receipt A operator (inputs.pullback mapping) value) :
    ((receipt.substitute env).map mapping).arguments =
      ((receipt.map mapping).substitute
        (fun sort position => mapping.raw.map (env sort position))).arguments :=
  BindingOperationPresheaf.map_substituteArgs mapping env receipt.arguments

/-- The complete dependent receipt commutes with interpretation and
substitution after the earned result comparison is applied. -/
theorem Receipt.map_substitute {Γ Δ : Ctx S} {sort : S.Srt}
    {operator : S.Op sort} {inputs : Arguments B (S.arity operator)}
    {value : A.substitution.Carrier Γ sort}
    (mapping : FreeBindingClone.Hom A B)
    (env : Environment S A.substitution.Carrier Γ Δ)
    (receipt : Receipt A operator (inputs.pullback mapping) value) :
    ((receipt.substitute env).map mapping).retype (mapping.map_substitute env value) =
      (receipt.map mapping).substitute
        (fun sort position => mapping.raw.map (env sort position)) := by
  apply Receipt.ext
  exact receipt.map_substitute_arguments mapping env

end Mettapedia.OSLF.Binding.BindingConstructorPredicates
