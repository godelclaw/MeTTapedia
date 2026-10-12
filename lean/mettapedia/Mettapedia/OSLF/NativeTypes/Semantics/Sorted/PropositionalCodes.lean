import Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes

open Mettapedia.OSLF.Framework

/-!
# Propositional interpretation relative to actual sort subobjects

Universe formation of code formedCode and the interpretation of a program-sort
subobject are separate constructions. This module interprets the generated
propositional formedCode in any carrier-bounded sort interpretation. Top and
complement are relative to that actual subobject. They do not silently range
over every operational term of the carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes leafCarriers leafSorts)
open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes (Expression Formed rawMeaning Refusal)
open ModalHypercube (HSort)

/-- This is interpretation data for a chosen native model, not a replacement
for the computed equation-center or connective-admission checks. -/
structure SortInterpretation (generated : Generated) (bound : List TypeExpr) where
  sortDomain : TypeExpr → HSort → Pattern → Prop
  carrierBounded : ∀ carrier sort term, sortDomain carrier sort term →
    HasType generated.snapshot.language generated.snapshot.free bound term carrier

def meaning {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (expression : Expression) (term : Pattern) : Prop :=
  interpretation.sortDomain carrier sort term ∧ rawMeaning leaves expression term

structure ClassifiedCode (generated : Generated) (bound : List TypeExpr)
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) where
  expression : Expression
  formation : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
    carrier sort expression
  code : TypeCode generated.plan bound carrier sort
  readout : ∀ term, code.meaning term ↔ meaning interpretation leaves carrier sort expression term

def interpretCode {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort}
    (formedCode : Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.ClassifiedCode generated bound leaves carrier sort) :
    ClassifiedCode generated bound interpretation leaves carrier sort where
  expression := formedCode.expression
  formation := formedCode.formation
  code := {
    meaning := meaning interpretation leaves carrier sort formedCode.expression
    bounded := fun term inhabited => interpretation.carrierBounded carrier sort term inhabited.1}
  readout _ := Iff.rfl

def compile (generated : Generated) (bound : List TypeExpr)
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    Except Refusal (ClassifiedCode generated bound interpretation leaves carrier sort) :=
  (Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.compilePropositionalCode generated bound leaves carrier sort expression).map
    (interpretCode interpretation)

theorem formation_complete (generated : Generated) (bound : List TypeExpr)
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
      carrier sort expression) :
    ∃ output, compile generated bound interpretation leaves carrier sort expression = .ok output ∧
      output.expression = expression := by
  obtain ⟨formedCode, checked, expressionEqual⟩ :=
    Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.generated_propositional_formation_complete
      generated bound leaves carrier sort expression formed
  exact ⟨interpretCode interpretation formedCode, by simp [compile, checked, Except.map], expressionEqual⟩

theorem formation_sound {generated : Generated} {bound : List TypeExpr}
    {interpretation : SortInterpretation generated bound} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    {output : ClassifiedCode generated bound interpretation leaves carrier sort}
    (checked : compile generated bound interpretation leaves carrier sort expression = .ok output) :
    output.expression = expression ∧
      Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression := by
  unfold compile at checked
  cases result : Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.compilePropositionalCode generated bound leaves
      carrier sort expression with
  | error refusal => simp [result, Except.map] at checked
  | ok formedCode =>
      simp only [result, Except.map, Except.ok.injEq] at checked
      subst output
      exact Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.generated_propositional_formation_sound result

theorem readout_exact {generated : Generated} {bound : List TypeExpr}
    {interpretation : SortInterpretation generated bound} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    {output : ClassifiedCode generated bound interpretation leaves carrier sort}
    (checked : compile generated bound interpretation leaves carrier sort expression = .ok output)
    (term : Pattern) : output.code.meaning term ↔
      interpretation.sortDomain carrier sort term ∧ rawMeaning leaves expression term := by
  rw [output.readout term, (formation_sound checked).1]
  rfl

theorem top_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (term : Pattern) :
    meaning interpretation leaves carrier sort .top term ↔ interpretation.sortDomain carrier sort term := by
  simp [meaning, rawMeaning]

theorem conjunction_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (first second : Expression) (term : Pattern) :
    meaning interpretation leaves carrier sort (.conjunction first second) term ↔
      meaning interpretation leaves carrier sort first term ∧ meaning interpretation leaves carrier sort second term := by
  simp [meaning, rawMeaning, and_left_comm, and_assoc]

theorem disjunction_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (first second : Expression) (term : Pattern) :
    meaning interpretation leaves carrier sort (.disjunction first second) term ↔
      meaning interpretation leaves carrier sort first term ∨ meaning interpretation leaves carrier sort second term := by
  simp [meaning, rawMeaning, and_or_left]

theorem implication_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (first second : Expression) (term : Pattern) :
    meaning interpretation leaves carrier sort (.implication first second) term ↔
      interpretation.sortDomain carrier sort term ∧
        (meaning interpretation leaves carrier sort first term →
          meaning interpretation leaves carrier sort second term) := by
  constructor
  · intro inhabited
    exact ⟨inhabited.1, fun first => ⟨inhabited.1, inhabited.2 first.2⟩⟩
  · intro inhabited
    exact ⟨inhabited.1, fun first => (inhabited.2 ⟨inhabited.1, first⟩).2⟩

theorem complement_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (inner : Expression) (term : Pattern) :
    meaning interpretation leaves carrier sort (.negation inner) term ↔
      interpretation.sortDomain carrier sort term ∧ ¬ meaning interpretation leaves carrier sort inner term := by
  constructor
  · intro inhabited
    exact ⟨inhabited.1, fun inside => inhabited.2 inside.2⟩
  · intro inhabited
    exact ⟨inhabited.1, fun inside => inhabited.2 ⟨inhabited.1, inside⟩⟩

theorem bottom_uninhabited {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (term : Pattern) :
    ¬ meaning interpretation leaves carrier sort .bottom term := by
  simp [meaning, rawMeaning]

theorem inhabitant_has_requested_sort {generated : Generated} {bound : List TypeExpr}
    {interpretation : SortInterpretation generated bound} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort}
    (output : ClassifiedCode generated bound interpretation leaves carrier sort) {term : Pattern}
    (inhabited : output.code.meaning term) : interpretation.sortDomain carrier sort term :=
  ((output.readout term).mp inhabited).1

theorem leaves_preserved {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (index : Nat)
    (bounded : ∀ term, (leaves index).2.2.meaning term → interpretation.sortDomain carrier sort term)
    (term : Pattern) : meaning interpretation leaves carrier sort (.leaf index) term ↔
      (leaves index).2.2.meaning term :=
  ⟨fun inhabited => inhabited.2, fun inhabited => ⟨bounded term inhabited, inhabited⟩⟩

/-- Logical closure preserves independently earned interpretation transport.
These are model-satisfaction conditions on the input leaves and sort subobject,
not an assumption that the generated expression itself is invariant. -/
theorem raw_meaning_transport {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) (equivalence : Pattern → Pattern → Prop)
    (leafTransport : ∀ index first second, equivalence first second →
      ((leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning second))
    (expression : Expression) (first second : Pattern) (related : equivalence first second) :
    rawMeaning leaves expression first ↔ rawMeaning leaves expression second := by
  induction expression with
  | leaf index => exact leafTransport index first second related
  | top => rfl
  | bottom => rfl
  | conjunction left right ihLeft ihRight => exact and_congr ihLeft ihRight
  | disjunction left right ihLeft ihRight => exact or_congr ihLeft ihRight
  | implication left right ihLeft ihRight => exact imp_congr ihLeft ihRight
  | negation inner ih => exact not_congr ih

theorem generated_readout_transport {generated : Generated} {bound : List TypeExpr}
    {interpretation : SortInterpretation generated bound} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    {output : ClassifiedCode generated bound interpretation leaves carrier sort}
    (checked : compile generated bound interpretation leaves carrier sort expression = .ok output)
    (equivalence : Pattern → Pattern → Prop)
    (sortTransport : ∀ first second, equivalence first second →
      (interpretation.sortDomain carrier sort first ↔ interpretation.sortDomain carrier sort second))
    (leafTransport : ∀ index first second, equivalence first second →
      ((leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning second))
    (first second : Pattern) (related : equivalence first second) :
    output.code.meaning first ↔ output.code.meaning second := by
  rw [readout_exact checked first, readout_exact checked second]
  exact and_congr (sortTransport first second related)
    (raw_meaning_transport leaves equivalence leafTransport expression first second related)

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes
