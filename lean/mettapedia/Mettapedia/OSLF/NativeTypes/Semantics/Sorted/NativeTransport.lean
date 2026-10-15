import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Laws

open Mettapedia.OSLF.Framework

/-!
# Equation and code-substitution transport of sort-relative native meanings

Finite classifier stability and semantic model stability are different laws.
This module derives native equation transport from actual equation receipts,
the chosen model's subobject transport and the native leaf comparisons.
Substitution replaces actual classified code expressions and proves their
recursive native meanings agree with the substituted leaf environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (Code LeafCodes ClassifiedCode leafCarriers leafSorts meaning)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
open ModalHypercube (HSort)

theorem native_conversion_carrier {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {carrier : TypeExpr} {first second : Pattern}
    (conversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound carrier) first second) :
    HasType plan.snapshot.language plan.snapshot.free bound first carrier ↔
      HasType plan.snapshot.language plan.snapshot.free bound second carrier := by
  induction conversion with
  | rel first second equation =>
      have both := Mettapedia.OSLF.NativeTypes.Modal.Equations.equation_sorted equation
      have firstTyped := (GeneralPlanEnvironment.typing_iff plan bound carrier first).mp both.1
      have secondTyped := (GeneralPlanEnvironment.typing_iff plan bound carrier second).mp both.2
      exact ⟨fun _ => secondTyped.1, fun _ => firstTyped.1⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem raw_constructor_equation_invariant {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length}
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.StructuralInputs generated bound index) {first second : Pattern}
    (conversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
      (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated index).category)) first second) :
    (Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index inputs).meaning first ↔
      (Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index inputs).meaning second := by
  constructor
  · rintro ⟨typed, value, equivalent, arguments⟩
    exact ⟨(native_conversion_carrier conversion).mp typed,
      value, .trans second first value.pattern (.symm first second conversion) equivalent, arguments⟩
  · rintro ⟨typed, value, equivalent, arguments⟩
    exact ⟨(native_conversion_carrier conversion).mpr typed,
      value, .trans first second value.pattern conversion equivalent, arguments⟩

theorem structural_equation_invariant {generated : Generated} {bound : List TypeExpr}
    (interpretation : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.SortInterpretation generated bound)
    {index : Fin generated.snapshot.language.terms.length}
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.StructuralInputs generated bound index) {first second : Pattern}
    (conversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
      (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated index).category)) first second)
    (domainTransport : interpretation.sortDomain (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated index).category)
        (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index) first ↔
      interpretation.sortDomain (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated index).category)
        (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index) second) :
    (structuralCode interpretation index inputs).meaning first ↔
      (structuralCode interpretation index inputs).meaning second :=
  and_congr domainTransport
    (raw_constructor_equation_invariant (restrictStructuralInputs interpretation inputs) conversion)

/-- Semantic leaves carry their own earned native equation comparisons.
Those comparisons and actual constructor witnesses imply whole-code transport. -/
theorem source_meaning_equation_invariant {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language} {carrier : TypeExpr}
    (formed : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Carries (leafCarriers leaves) expression carrier)
    (leavesTransport : ∀ index first second,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound (leafCarriers leaves index)) first second →
      ((leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning second))
    {first second : Pattern}
    (conversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound carrier) first second) :
    meaning generated bound leaves expression first ↔ meaning generated bound leaves expression second := by
  cases formed with
  | variableCode index => exact leavesTransport index first second conversion
  | constructor index arguments children =>
      constructor
      · rintro ⟨typed, value, equivalent, arguments⟩
        exact ⟨(native_conversion_carrier conversion).mp typed,
          value, .trans second first value.pattern (.symm first second conversion) equivalent, arguments⟩
      · rintro ⟨typed, value, equivalent, arguments⟩
        exact ⟨(native_conversion_carrier conversion).mpr typed,
          value, .trans first second value.pattern conversion equivalent, arguments⟩

theorem classified_equation_invariant {generated : Generated} {bound : List TypeExpr}
    (interpretation : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.SortInterpretation generated bound)
    {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    (formedCode : ClassifiedCode generated bound leaves carrier sort)
    (leavesTransport : ∀ index first second,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound (leafCarriers leaves index)) first second →
      ((leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning second))
    {first second : Pattern}
    (conversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound carrier) first second)
    (domainTransport : interpretation.sortDomain carrier sort first ↔ interpretation.sortDomain carrier sort second) :
    (restrictCode interpretation formedCode.code).meaning first ↔
      (restrictCode interpretation formedCode.code).meaning second := by
  apply and_congr domainTransport
  rw [formedCode.meaningComparison first, formedCode.meaningComparison second]
  exact source_meaning_equation_invariant formedCode.carrierFormation leavesTransport conversion

def replacementLeaves {generated : Generated} {bound : List TypeExpr}
    (sourceLeaves targetLeaves : LeafCodes generated bound)
    (replacements : (index : Nat) → ClassifiedCode generated bound targetLeaves
      (leafCarriers sourceLeaves index) (leafSorts sourceLeaves index)) : LeafCodes generated bound :=
  fun index => ⟨leafCarriers sourceLeaves index, leafSorts sourceLeaves index, (replacements index).code⟩

theorem code_substitution_meaning {generated : Generated} {bound : List TypeExpr}
    (sourceLeaves targetLeaves : LeafCodes generated bound)
    (replacements : (index : Nat) → ClassifiedCode generated bound targetLeaves
      (leafCarriers sourceLeaves index) (leafSorts sourceLeaves index))
    (expression : Code generated.snapshot.language) (term : Pattern) :
    meaning generated bound targetLeaves
        (expression.substitute (fun index => (replacements index).expression)) term ↔
      meaning generated bound (replacementLeaves sourceLeaves targetLeaves replacements) expression term := by
  induction expression generalizing term with
  | variableCode index => exact ((replacements index).meaningComparison term).symm
  | constructor index arguments ih =>
      change (_ ∧ ∃ value, _ ∧ ∀ position, _) ↔ (_ ∧ ∃ value, _ ∧ ∀ position, _)
      constructor
      · rintro ⟨typed, value, conversion, inputs⟩
        exact ⟨typed, value, conversion, fun position => (ih position _).mp (inputs position)⟩
      · rintro ⟨typed, value, conversion, inputs⟩
        exact ⟨typed, value, conversion, fun position => (ih position _).mpr (inputs position)⟩

/-- The replacement codes' carrier and kind proofs justify formation of the
actual substituted syntax. No completeness or stability predicate is supplied. -/
def substituteClassified {generated : Generated} {bound : List TypeExpr}
    {sourceLeaves targetLeaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    (formedCode : ClassifiedCode generated bound sourceLeaves carrier sort)
    (replacements : (index : Nat) → ClassifiedCode generated bound targetLeaves
      (leafCarriers sourceLeaves index) (leafSorts sourceLeaves index)) :
    ClassifiedCode generated bound targetLeaves carrier sort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classify
    (formedCode.expression.substitute (fun index => (replacements index).expression))
    (formedCode.carrierFormation.substitute (fun index => (replacements index).expression)
      (fun index => (replacements index).carrierFormation))
    (formedCode.universeFormation.substitute (fun index => (replacements index).expression)
      (fun index => (replacements index).universeFormation))

theorem substituted_classified_readout {generated : Generated} {bound : List TypeExpr}
    (interpretation : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.SortInterpretation generated bound)
    {sourceLeaves targetLeaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    (formedCode : ClassifiedCode generated bound sourceLeaves carrier sort)
    (replacements : (index : Nat) → ClassifiedCode generated bound targetLeaves
      (leafCarriers sourceLeaves index) (leafSorts sourceLeaves index)) (term : Pattern) :
    (restrictCode interpretation (substituteClassified formedCode replacements).code).meaning term ↔
      interpretation.sortDomain carrier sort term ∧
        meaning generated bound (replacementLeaves sourceLeaves targetLeaves replacements) formedCode.expression term := by
  apply and_congr Iff.rfl
  rw [(substituteClassified formedCode replacements).meaningComparison term]
  exact code_substitution_meaning sourceLeaves targetLeaves replacements formedCode.expression term

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport
