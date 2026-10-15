import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileRuntime
import Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSearch

/-!
# Actual occurrence-search batches for the binder family

These equations calculate the batches consumed by the generic resumable
search. Both authored rule indices and all successful provider occurrences
remain present; equation receipts carry their orientation separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open Syntax Engine RuleBinding ScopedRuleMatching
open ScopedEquationExecution (Orientation orientedRule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open ConditionalEquationExecution

def expectedEquationReceipts (allowed : List Token) (ambient : Nat)
    (source : State ambient) (equationIndex : Nat) (orientation : Orientation) :
    List EquationReceipt :=
  if source.phase = equationSourcePhase orientation then
    (expectedReceipts allowed ambient source.name source.key
      (equationTargetPhase orientation)).map fun receipt =>
        { toReceipt := receipt, equationIndex, orientation }
  else []

def expectedRuleReceipts (allowed : List Token) (ambient : Nat)
    (source : State ambient) : List Receipt :=
  if source.phase = .exposed then
    expectedReceipts allowed ambient source.name source.key .finished else []

theorem applyAt_family (allowed : List Token) (ambient : Nat)
    (source : State ambient) (equationIndex : Nat) (orientation : Orientation) :
    applyAt (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      .proc equationIndex extrusionEquation orientation source.pattern =
        ⟨expectedEquationReceipts allowed ambient source equationIndex orientation, []⟩ := by
  by_cases active : source.phase = equationSourcePhase orientation <;>
    simp [applyAt, extrusion_outcome_family, expectedEquationReceipts, active]

theorem consume_rename_outcome (allowed : List Token) (ambient : Nat)
    (source : State ambient) (name : String) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc { consumeRule with name := name } source.pattern =
        applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
          (ambientContext ambient) .proc consumeRule source.pattern := by
  rcases source with ⟨phase, index, token⟩
  cases phase <;>
    simp only [applyRuleAtOutcome, state_open_checked, if_true]
  all_goals dsimp only [consumeRule, State.pattern, pair, nu, done,
    admittedFor, occurrenceDeclared,
    occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?, receiptsFor,
    matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith, captureWith?,
    arguments?, declarationPending, checkAssignment, runQueries, typedQueryResults,
    queryPending, finishTyped?, reduct?, instantiateAt?, instantiateWith?,
    instantiateArgsWith?]
  all_goals simp only [matchAtWith, matchArgsAtWith, instantiateWith?,
    instantiateArgsWith?, captureWith?, arguments?, occurrenceDeclared, sitePattern?]
  all_goals rfl

theorem language_equations : language.equations = [extrusionEquation] := rfl

theorem language_rewrites : language.rewrites =
    [consumeRule, { consumeRule with name := "consume-guard-again" }] := rfl

theorem equationBatch_family (allowed : List Token) (ambient : Nat)
    (source : State ambient) :
    AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern =
        ⟨(expectedEquationReceipts allowed ambient source 0 .forward).map
            (fun receipt => (receipt, receipt.target)) ++
          (expectedEquationReceipts allowed ambient source 0 .reverse).map
            (fun receipt => (receipt, receipt.target)), []⟩ := by
  simp [AuthoredEquationOccurrenceSearch.equationBatch,
    AuthoredEquationOccurrenceSearch.equationCases,
    AuthoredEquationOccurrenceSearch.orientations, language_equations, applyAt_family]

theorem firingBatch_family (allowed : List Token) (ambient : Nat)
    (source : State ambient) :
    AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern =
        ⟨(expectedRuleReceipts allowed ambient source).map
            (fun receipt => (⟨receipt, 0⟩, receipt.target)) ++
          (expectedRuleReceipts allowed ambient source).map
            (fun receipt => (⟨receipt, 1⟩, receipt.target)), []⟩ := by
  simp [AuthoredEquationOccurrenceSearch.firingBatch, language_rewrites,
    consume_rename_outcome, consume_outcome_family, expectedRuleReceipts]

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
