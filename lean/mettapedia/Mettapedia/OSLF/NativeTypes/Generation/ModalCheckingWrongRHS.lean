import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingIsolation

open Mettapedia.OSLF.Framework

/-!
# Every query budget respects the specified beta contractum

Changing the hidden body assignment gives a properly typed RHS that is not
the actual source's beta result. Independent occurrence coverage rules that
RHS out. The public query cannot certify it at any execution or conversion
budget; this conclusion does not rely on a false continuation predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingWrongRHS

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls (schema parameters actual_parameters relyCodes computed_schema_shape)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated source argument term)

def wrongAssignment : ScopedRuleMatching.Assignment :=
  [("A", ⟨[], 0, argument⟩), ("B", ⟨[term], 0, argument⟩)]

theorem wrong_filling : schema.fill? wrongAssignment source = some source := by
  simp only [Schema.fill?, computed_schema_shape.1, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?]

theorem actual_wrong_rhs : schema.rhs? wrongAssignment = some argument := by
  simp only [Schema.rhs?, Schema.operation, computed_schema_shape.2.2.2.2.2.2,
    computed_schema_shape.2.1]
  cbv

def continuationCode (assignment : ScopedRuleMatching.Assignment) :
    TypeCode generated.plan schema.bound schema.programCarrier parameters.output where
  meaning target :=
    checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
      schema.bound schema.programCarrier target = true ∧
    ScopedRuleMatching.lookup assignment "A" = some ⟨[], 0, argument⟩
  bounded _ valid := (checkOpenPatternWellSorted_sound valid.1).1

def codes : ModalInstanceCodes generated schema :=
  ⟨parameters, actual_parameters, relyCodes, continuationCode⟩

def decisions : ModalInstanceDecisions codes where
  rely name _ := by
    have absent := name.property
    simp only [computed_schema_shape.2.2.2.2.2.1, List.not_mem_nil] at absent
  continuation assignment target := by
    change Decidable (checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
      schema.bound schema.programCarrier target = true ∧
      ScopedRuleMatching.lookup assignment "A" = some ⟨[], 0, argument⟩)
    infer_instance

theorem wrong_rhs_continuation_is_true : (codes.inputs.2 wrongAssignment).meaning argument := by
  change checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    schema.bound schema.programCarrier argument = true ∧ _
  rw [computed_schema_shape.2.1, computed_schema_shape.2.2.2.2.1]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  decide +kernel

theorem no_wrong_outcome (B : Continuation) :
    ¬ Nonempty (Outcome schema source wrongAssignment B) := by
  rintro ⟨outcome⟩
  have sourceSame := Option.some.inj (outcome.filling.symm.trans wrong_filling)
  have targetSame := Option.some.inj (outcome.rhs.symm.trans actual_wrong_rhs)
  have step : (GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier).Step
      outcome.source outcome.target :=
    ⟨outcome.receipt.representative, outcome.receipt.firing,
      outcome.valid.1.equivalent, outcome.valid.2, outcome.targetConversion⟩
  rw [sourceSame, targetSame, computed_schema_shape.2.1,
    computed_schema_shape.2.2.2.2.1] at step
  exact Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingIsolation.wrong_beta_rhs_independently_excluded step

/-- Exhaustion cannot make a wrong specific RHS true, even if both it and
its continuation are well formed. The retained independent step contract
rules it out for every pair of actual search budgets. -/
theorem every_budget_respects_specific_rhs (budget conversionBudget : Nat)
    (result : ModalInstanceRun codes wrongAssignment source)
    (computed : generated.checkModalInstance schema codes decisions wrongAssignment source budget conversionBudget = .ok result) :
    result.result ≠ .decided true := by
  intro positive
  exact no_wrong_outcome codes.continuation
    (generated_modal_instance_positive_sound computed positive)

end Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingWrongRHS
