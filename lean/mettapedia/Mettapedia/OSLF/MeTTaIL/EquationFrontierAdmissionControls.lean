import Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

/-!+# Sorting, capture and incompleteness controls for equation frontiers

The capture control starts from a genuinely typed object term. Its independent
component refers to the name it would cross, so the declared extrusion must
reject that capture. The sorting controls separately reject a wrong captured
sort and a wrong source sort. Unsupported logical premises and query shapes
are retained by the actual executor and parked by the resumable queue.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierAdmissionControls

open Syntax Engine ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationFrontierBinderProfile

/-- Both components use the locally restricted name. The right component
cannot be extruded under its declared empty dependency telescope. -/
def capturingSource : Pattern := nu (pair (cell 0) (cell 0))

theorem capturingSource_typed :
    HasType language FreeTypeContext.empty [] capturingSource .proc := by
  exact nu_typed [] _ (pair_typed [.name] _ _
    (cell_typed 0 ⟨0, by decide⟩) (cell_typed 0 ⟨0, by decide⟩))

theorem capturingSource_checked :
    checkOpenPatternWellSorted language FreeTypeContext.empty [] .proc
      capturingSource = true := by
  decide +kernel

theorem dependent_Q_capture_rejected :
    ConditionalEquationExecution.applyAt (provider [.permit]) language FreeTypeContext.empty [] .proc
      0 extrusionEquation .forward capturingSource = ⟨[], []⟩ := by
  decide +kernel

theorem capturingSource_has_no_admitted_equation_instance
    (receipt : ConditionalEquationExecution.EquationReceipt) :
    ¬ ConditionalEquationExecution.EquationInstance (provider [.permit]) language
      FreeTypeContext.empty [] .proc 0 extrusionEquation .forward capturingSource receipt := by
  intro hinstance
  have supported : ∀ spec,
      (ScopedEquationExecution.orientedRule extrusionEquation .forward).bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 extrusionEquation.premises = true := by
    intro spec declared
    simp only [ScopedEquationExecution.orientedRule, extrusionEquation] at declared
    cases declared
    decide +kernel
  have present := ConditionalEquationExecution.applyAt_complete (provider [.permit]) language
    FreeTypeContext.empty [] .proc 0 extrusionEquation .forward capturingSource receipt
    supported hinstance
  rw [dependent_Q_capture_rejected] at present
  simp at present

def illSortedAssignment : Assignment :=
  [("P", ⟨[.name], 0, cell 0⟩), ("Q", ⟨[], 0, Token.pattern .permit⟩)]

theorem Q_name_is_not_declared_process :
    ConditionalEquationExecution.checkAssignment language FreeTypeContext.empty [] consumeRule
      (consumeRule.bindings.getD ⟨[], []⟩) illSortedAssignment = false := by
  decide +kernel

theorem illSortedAssignment_not_typed :
    ¬ ConditionalEquationExecution.AssignmentTyped language FreeTypeContext.empty [] consumeRule
      (consumeRule.bindings.getD ⟨[], []⟩) illSortedAssignment := by
  intro typed
  have objects : ConditionalEquationExecution.AssignmentObjects illSortedAssignment := by
    intro name value member
    simp [illSortedAssignment] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide +kernel
  have checked := ConditionalEquationExecution.checkAssignment_complete typed objects
  rw [Q_name_is_not_declared_process] at checked
  contradiction

def illSortedSource : Pattern := pair (nu (cell 0)) (Token.pattern .permit)

theorem illSortedSource_well_scoped : illSortedSource.isWellScoped = true := by
  decide +kernel

theorem illSortedSource_rejected :
    ConditionalEquationExecution.applyRuleAtOutcome (provider [.permit]) language FreeTypeContext.empty [] .proc
      consumeRule illSortedSource = ⟨[], [.sourceRejected]⟩ := by
  decide +kernel

theorem illSortedSource_not_typed :
    ¬ HasType language FreeTypeContext.empty [] illSortedSource .proc := by
  intro typed
  have objects : isObjectPattern illSortedSource = true := by decide +kernel
  have checked := checkHasType_complete_of_object typed objects
  have rejected : checkHasType language FreeTypeContext.empty [] illSortedSource .proc = false := by
    decide +kernel
  rw [rejected] at checked
  contradiction

def exposedSource : Pattern := pair (nu (cell 0)) (guard .permit)

def unsupportedQuantifier : Premise :=
  .forAll "name" "Name" (.relationQuery "allow" [.fvar "Q"])

def unsupportedRule : RewriteRule :=
  { consumeRule with premises := [unsupportedQuantifier] }

theorem unsupported_quantifier_retained :
    ConditionalEquationExecution.applyRuleAtOutcome (provider [.permit]) language FreeTypeContext.empty [] .proc
      unsupportedRule exposedSource =
      ⟨[], [.unsupportedPremise 0 unsupportedQuantifier,
        .unsupportedPremise 0 unsupportedQuantifier]⟩ := by
  decide +kernel

def structuralQueryArguments : List Pattern := [guard .permit]

def structuralQueryRule : RewriteRule :=
  { consumeRule with premises := [.relationQuery "allow" structuralQueryArguments] }

theorem structural_query_arguments_retained :
    ConditionalEquationExecution.applyRuleAtOutcome (provider [.permit]) language FreeTypeContext.empty [] .proc
      structuralQueryRule exposedSource =
      ⟨[], [.unsupportedQueryArguments 0 structuralQueryArguments,
        .unsupportedQueryArguments 0 structuralQueryArguments]⟩ := by
  decide +kernel

/-- This control snapshot enables one unsupported authored rule. Its empty
equation family is explicit; the unresolved rule remains operationally enabled. -/
def unsupportedLanguage : LanguageDef :=
  { language with equations := [], rewrites := [unsupportedRule] }

def unsupportedModel :=
  ContextualAuthoredEquationExecution.model (provider [.permit]) unsupportedLanguage FreeTypeContext.empty [] .proc
    [.hole] (ContextualAuthoredEquationExecution.rootSites unsupportedLanguage FreeTypeContext.empty [] .proc [.hole])

def unsupportedSnapshot := Framework.ResumableEquationOccurrenceFrontier.run unsupportedModel 1 (Framework.ResumableEquationOccurrenceFrontier.initial exposedSource)

theorem unsupported_queue_retains_obligations :
    unsupportedSnapshot.parked.length = 2 := by
  decide +kernel

theorem unsupported_queue_has_no_completeness :
    unsupportedSnapshot.receipts = [] ∧ Framework.ResumableEquationOccurrenceFrontier.quiescent unsupportedSnapshot = false := by
  decide +kernel

def structuralQueryLanguage : LanguageDef :=
  { language with equations := [], rewrites := [structuralQueryRule] }

def structuralQueryModel :=
  ContextualAuthoredEquationExecution.model (provider [.permit]) structuralQueryLanguage FreeTypeContext.empty [] .proc
    [.hole] (ContextualAuthoredEquationExecution.rootSites structuralQueryLanguage FreeTypeContext.empty [] .proc [.hole])

def structuralQuerySnapshot :=
  Framework.ResumableEquationOccurrenceFrontier.run structuralQueryModel 1 (Framework.ResumableEquationOccurrenceFrontier.initial exposedSource)

theorem structural_query_queue_retains_obligations :
    structuralQuerySnapshot.parked.length = 2 := by
  decide +kernel

theorem structural_query_queue_has_no_completeness :
    structuralQuerySnapshot.receipts = [] ∧
      Framework.ResumableEquationOccurrenceFrontier.quiescent structuralQuerySnapshot = false := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.EquationFrontierAdmissionControls
