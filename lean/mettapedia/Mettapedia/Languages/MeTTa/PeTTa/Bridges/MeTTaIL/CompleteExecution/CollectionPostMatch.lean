import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource

/-!
# Shared continuation operations in the common runtime

The post-match service keeps the same clauses and argument demand when loaded
beside the canonical search, chronological search and generic driver. Its
existing execution theorems therefore transfer without another continuation
implementation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionPostMatch

open SpaceSemantics (Program)
open Eval BridgeKit WireKit

def retained (head : String) : Bool :=
  !(["gslt:laws:", "gslt:canon:", "gslt:collection-search:",
    "gslt:search:", "gslt:runner:", "gslt:explore:", "gslt:collection-root:"].any
      fun prefixName => prefixName.isPrefixOf head)

theorem closed : ProgramClosed retained CollectionMatcherBackendExecution.library.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

private theorem laws_equations :
    lawsSource.program.equations.filter (fun row => retained row.head) = [] := by decide +kernel
private theorem canonical_equations :
    canonicalSource.program.equations.filter (fun row => retained row.head) = [] := by decide +kernel
private theorem logged_equations :
    CollectionLoggedSearchExecution.source.program.equations.filter (fun row => retained row.head) = [] := by
  decide +kernel

private theorem laws_declarations :
    lawsSource.program.declarations.filter (retainedCallDeclaration retained) = [] := by decide +kernel
private theorem canonical_declarations :
    canonicalSource.program.declarations.filter (retainedCallDeclaration retained) = [] := by decide +kernel
private theorem logged_declarations :
    CollectionLoggedSearchExecution.source.program.declarations.filter
      (retainedCallDeclaration retained) = [] := by decide +kernel

theorem agreement : ProgramAgreementOn retained CollectionMatcherBackendExecution.library.runtime
    collectionBaseLibrary.runtime := by
  apply programAgreementOn_of_retained_rows
  all_goals
    simp only [CollectionMatcherBackendExecution.library,
      CollectionMatcherBackendExecution.collectionBaseLibrary,
      CollectionMatcherBackendExecution.collectionBaseSource,
      collectionBaseLibrary, collectionSupportProgram,
      canonicalLibrary, lawsLibrary, Library.runtime, SpaceSemantics.Program.append,
      List.filter_append, laws_equations, canonical_equations, logged_equations,
      laws_declarations, canonical_declarations, logged_declarations,
      List.nil_append, List.append_assoc]

syntax "postmatch_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(postmatch_lifted% [$names,*] $fact) =>
      `(runner_from_base% [$names,*] (BridgeKit.transport_call closed agreement (by decide +kernel) (by decide)
        (by decide +kernel) (by decide) [$names,*] (by decide) (by rfl)
        (by decide +kernel) $fact))

/-- Source authority and source free-name coverage suffice to start the
native continuation from a raw receipt. Neither a provisional reduct nor
an independently supplied capture-readiness assertion is required. -/
theorem begin_match_returns (state : Effects.State)
    (plan : OSLF.MeTTaIL.GeneralExecutionAdmission.Plan)
    (certificate : OSLF.MeTTaIL.CollectionExecutionAdmission.Certificate plan)
    (source : OSLF.MeTTaIL.Syntax.Pattern) (depth : Nat)
    (type : OSLF.MeTTaIL.Syntax.TypeExpr) (ordinal : Nat)
    (query : OSLF.MeTTaIL.ScopedCollectionMachine.Request)
    (receipt : OSLF.MeTTaIL.ScopedCollectionMachine.Receipt)
    (authority : OSLF.MeTTaIL.CollectionMatcherBackend.MatchAuthority
      plan certificate source ordinal query receipt)
    (typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).language
      (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).free [] type source)
    (footprint : List String)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-backend:begin-match"
        [environmentValue (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan)
            ((OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.typeTerm type),
          number ordinal, encoded (ScopedCollectionExecution.requestTerm query),
          encoded (ScopedCollectionExecution.receiptTerm receipt)])
      state (encoded (DescentCodec.stateTerm
        (OSLF.MeTTaIL.CollectionMatcherBackend.startMatch
          plan certificate source depth type ordinal query receipt authority typed))) := by
  have native := CollectionMatcherBackendExecution.begin_match_returns state
    (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan) footprint depth type ordinal
    query receipt authority.ready authority.fixed authority.valid authority.declared
    authority.specified authority.admitted (authority.source_typed typed)
    (authority.captures_free_within footprint inside)
  exact postmatch_lifted% ["environment", "depth", "type", "index", "query", "receipt"] native

/-- The common runtime starts the shared typed/premise continuation with
authority recovered from an actual chronological source publication. -/
theorem begin_logged_returns (state : Effects.State)
    (plan : OSLF.MeTTaIL.GeneralExecutionAdmission.Plan)
    (certificate : OSLF.MeTTaIL.CollectionExecutionAdmission.Certificate plan)
    (source : OSLF.MeTTaIL.Syntax.Pattern) (fuel depth : Nat)
    (type : OSLF.MeTTaIL.Syntax.TypeExpr)
    (firing : OSLF.MeTTaIL.CollectionPlanMachine.Firing)
    (published : firing ∈ (OSLF.MeTTaIL.CollectionLoggedSearch.run
      plan certificate source fuel).state.log)
    (typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).language
      (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).free [] type source)
    (footprint : List String)
    (covered : ∀ answer ∈ OSLF.MeTTaIL.CollectionMatcherBackend.rootAnswers firing
        (OSLF.MeTTaIL.CollectionMatcherBackend.logged_publication_authority
          plan certificate source fuel published).ready,
      OSLF.MeTTaIL.ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:collection-backend:begin"
        [environmentValue (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan)
            ((OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.typeTerm type),
          encoded (CollectionPlanExecution.planFiringTerm firing)])
      state (encoded (DescentCodec.stateTerm
        (OSLF.MeTTaIL.CollectionMatcherBackend.startLoggedPublished
          plan certificate source fuel depth type firing published typed))) := by
  let authority := OSLF.MeTTaIL.CollectionMatcherBackend.logged_publication_authority
    plan certificate source fuel published
  have native := CollectionMatcherBackendExecution.begin_returns state
    (OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan) footprint depth type firing
    authority.ready authority.fixed authority.valid authority.declared authority.specified
    authority.admitted (authority.source_typed typed) covered
  exact postmatch_lifted% ["environment", "depth", "type", "firing"] native

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionPostMatch
