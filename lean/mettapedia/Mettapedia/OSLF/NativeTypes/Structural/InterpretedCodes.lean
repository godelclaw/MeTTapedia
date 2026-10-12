import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
import Mettapedia.OSLF.NativeTypes.Instances.Local.Structural

open Mettapedia.OSLF.Framework

/-!
# Generated constructor codes in an independently interpreted equation model

The signature, constructor indices, ordered carriers and sort slots come from
the generated output. An equation model interprets that syntax; it does not
replace the language presentation or change its catalogues. Object-carrier
interpretation excludes pending schema operations from constructor inhabitants.

The legacy bounded-equation engine has its own comparison contract. It agrees
with this interpretation only after primitive equation and carrier comparisons
are earned. The equation-free comparison below discharges both obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.Structural (ConstructorValue)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes (SortInterpretation)

abbrev Equations := TypeExpr → Setoid Pattern

abbrev Introduction (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) :=
  ConstructorValue generated.snapshot.language generated.snapshot.free bound
    (structuralDeclaration generated index)

def argument {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length}
    (value : Introduction generated bound index)
    (position : Fin (structuralDeclaration generated index).params.length) : Pattern :=
  value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)

/-- This is the constructor image in the independently chosen equation model,
with actual input sort masks. No search result appears in the definition. -/
def meaning {generated : Generated} {bound : List TypeExpr}
    (equations : Equations) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) (term : Pattern) : Prop :=
  model.sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) term ∧
    isObjectPattern term = true ∧
    ∃ value : Introduction generated bound index,
      isObjectPattern value.pattern = true ∧
      (equations (.base (structuralDeclaration generated index).category)).r term value.pattern ∧
      ∀ position,
        model.sortDomain (structuralDeclaration generated index).params[position].typeExpr
            (structuralInputSort generated index position) (argument value position) ∧
          (inputs position).meaning (argument value position)

def structuralCode {generated : Generated} {bound : List TypeExpr}
    (equations : Equations) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) :
    TypeCode generated.plan bound (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) where
  meaning := meaning equations model index inputs
  bounded term inhabited := model.carrierBounded _ _ term inhabited.1

theorem introduction {generated : Generated} {bound : List TypeExpr}
    (equations : Equations) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (value : Introduction generated bound index)
    (object : isObjectPattern value.pattern = true)
    (output : model.sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) value.pattern)
    (arguments : ∀ position,
      model.sortDomain (structuralDeclaration generated index).params[position].typeExpr
          (structuralInputSort generated index position) (argument value position) ∧
        (inputs position).meaning (argument value position)) :
    (structuralCode equations model index inputs).meaning value.pattern :=
  ⟨output, object, value, object, (equations _).iseqv.refl _, arguments⟩

/-- Equality with the existing generated code follows from comparisons of
primitive equation classes and the object carrier, not a supplied equality of
the completed structural predicates. -/
theorem legacy_compatibility {generated : Generated} {bound : List TypeExpr}
    (equations : Equations) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) (object : isObjectPattern term = true)
    (equationComparison : ∀ value : Introduction generated bound index,
      (equations (.base (structuralDeclaration generated index).category)).r term value.pattern ↔
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
          (.base (structuralDeclaration generated index).category)) term value.pattern)
    (objectPreservation : ∀ value : Introduction generated bound index,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
        (.base (structuralDeclaration generated index).category)) term value.pattern →
      isObjectPattern value.pattern = true) :
    (structuralCode equations model index inputs).meaning term ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode model index inputs).meaning term := by
  rw [Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structural_image_exact]
  constructor
  · rintro ⟨sorted, _, value, valueObject, related, arguments⟩
    exact ⟨sorted, model.carrierBounded _ _ term sorted,
      value, (equationComparison value).mp related, arguments⟩
  · rintro ⟨sorted, _, value, related, arguments⟩
    exact ⟨sorted, object, value, objectPreservation value related,
      (equationComparison value).mpr related, arguments⟩

@[instance_reducible]
def freeEquations : Equations := fun _ => ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- Every equation-free authored language discharges the primitive comparison,
for all generated constructors and all ambient contexts. -/
theorem free_compatibility {generated : Generated} {bound : List TypeExpr}
    (empty : generated.plan.equations = []) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) (object : isObjectPattern term = true) :
    (structuralCode freeEquations model index inputs).meaning term ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode model index inputs).meaning term := by
  apply legacy_compatibility freeEquations model index inputs term object
  · intro value
    exact (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq empty bound _ term value.pattern).symm
  · intro value related
    have same := (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq empty bound _ term value.pattern).mp related
    exact same ▸ object

#print axioms legacy_compatibility
#print axioms free_compatibility

end Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes
