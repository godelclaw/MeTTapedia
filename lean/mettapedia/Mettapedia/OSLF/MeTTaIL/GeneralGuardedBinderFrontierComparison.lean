import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion

/-!
# Exhaustive execution of the original guarded binder language

The consumer retains the original grammar, both consume declarations and
both extrusion orientations. Its complete receipt and equation-class laws
hold for every typed object source and every caller binder context. The
reference judgments use licensed typed occurrences and independent scoped
matching and premises; they do not use frontier enumeration membership.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierComparison

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open EquationFrontierBinderProfile GeneralGuardedBinderExecution
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem actual_source_admitted {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) :
    GeneralOccurrenceFrontier.Admitted (request allowed bound expected source) :=
  arbitrary_source_admitted typed object typed.isWellScopedAt

theorem whole_original_frontier_complete {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) :
    GeneralOccurrenceFrontier.complete (request allowed bound expected source)
      (GeneralOccurrenceFrontier.finish _ (actual_source_admitted typed object)) = true :=
  GeneralOccurrenceFrontier.compiled_total_finish_complete
    (GeneralExecutionTotalAdmission.guarded_compilation_total allowed) typed object

theorem whole_original_frontier_certificate {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) :
    GeneralOccurrenceFrontier.checkCertificate (request allowed bound expected source)
      (GeneralOccurrenceFrontier.finish _ (actual_source_admitted typed object)) = true :=
  GeneralOccurrenceFrontier.compiled_total_finish_certificate
    (GeneralExecutionTotalAdmission.guarded_compilation_total allowed) typed object

theorem whole_original_successor_classes {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) (target : Pattern) :
    Quotient.mk (Relation.EqvGen.setoid
      (GeneralOccurrenceSemantics.Equation (plan allowed) bound expected)) target ∈
      GeneralOccurrenceFrontier.targetClasses (request allowed bound expected source)
        (GeneralOccurrenceFrontier.finish _ (actual_source_admitted typed object)) ↔
      (GeneralOccurrenceSemantics.gslt (plan allowed) bound expected).Step
        source.eraseBinderMetadata target :=
  GeneralOccurrenceFrontier.certified_targetClasses (actual_source_admitted typed object)
    (whole_original_frontier_certificate typed object) target

theorem whole_original_physical_firing_coverage {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) (representative : Pattern)
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation (plan allowed) bound expected)
      source.eraseBinderMetadata representative)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (plan allowed) bound expected representative) :
    ∃ answer ∈ (GeneralOccurrenceFrontier.finish (request allowed bound expected source)
      (actual_source_admitted typed object)).answers,
      answer.val.representative = representative ∧ answer.val.firing = receipt :=
  GeneralOccurrenceFrontier.certified_physical_occurrence (actual_source_admitted typed object)
    (whole_original_frontier_certificate typed object) representative related receipt valid

theorem whole_original_actual_run_completes {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) :
    let query := request allowed bound expected source
    ∃ fuel,
      GeneralOccurrenceFrontier.complete query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true ∧
      GeneralOccurrenceFrontier.checkCertificate query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true := by
  obtain ⟨fuel, actual⟩ := GeneralOccurrenceFrontier.finish_actual_run _ (actual_source_admitted typed object)
  refine ⟨fuel, ?_, ?_⟩
  · rw [actual]
    exact whole_original_frontier_complete typed object
  · rw [actual]
    exact whole_original_frontier_certificate typed object

#print axioms whole_original_frontier_complete
#print axioms whole_original_successor_classes
#print axioms whole_original_physical_firing_coverage

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierComparison
