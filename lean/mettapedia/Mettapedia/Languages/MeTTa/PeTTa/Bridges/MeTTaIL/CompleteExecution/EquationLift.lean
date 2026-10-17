import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.EquationLanes

/-!
# The premises of an equation lane, and their receipts

A lane deepens over its equation's premises at its capture: `(PremisesFamily context premises
captured limit)`, with the premise limit as its bound and premise outcomes as payloads.
`gslt:equations:lift` finishes an outcome as `GeneralEquationJobs.finish`: both assignments
checked, the right side instantiated, the erased reduct accepted at the site, and the filled
term well sorted.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding DerivedContexts GeneralTypedSites
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open RuleInstantiationExecution.GeneralExecution (matcherRequestTerm matcherStateTerm matcherAnswerTerm)

/-- A premise outcome, as the descent machine's premise-list answer writes it. -/
def outcomeTerm (outcome : Complete.EquationJob.Outcome) : Term :=
  .application "PremisesAnswer" [assignmentTerm outcome.completed,
    PremiseOperationsExecution.GeneralExecution.eventsTerm outcome.history]

def decodeOutcome? : Term → Option Complete.EquationJob.Outcome
  | .application "PremisesAnswer" [completed, history] => do
      pure ⟨← ScopedRuleJobReadoutExecution.decodeAssignment? completed,
        ← ScopedRuleJobReadoutExecution.decodeEvents? history⟩
  | _ => none

theorem decodeOutcome?_outcomeTerm (outcome : Complete.EquationJob.Outcome) :
    decodeOutcome? (outcomeTerm outcome) = some outcome := by
  obtain ⟨completed, history⟩ := outcome
  simp [outcomeTerm, decodeOutcome?, assignmentTerm]

theorem outcomeTerm_injective : Function.Injective outcomeTerm := by
  intro first second same
  have decoded := congrArg decodeOutcome? same
  simpa only [decodeOutcome?_outcomeTerm, Option.some.injEq] using decoded

variable (plan : GeneralExecutionAdmission.Plan)

/-- The data of a lane's premise deepening. -/
def premisesFamilyTerm (lane : Complete.EquationJob.Lane) : Term :=
  .application "PremisesFamily" [PremiseOperationsExecution.GeneralExecution.contextTerm (lane.job.context plan),
    encodeList InferenceCettaWire.AuthoredRule.premiseTerm lane.job.equation.rule.premises,
    assignmentTerm lane.answer.assignment,
    encodeOption Term.natural (Complete.EquationJob.premisesBound plan lane.job lane.answer.assignment)]

theorem premises_goal_returns (lane : Complete.EquationJob.Lane) (state : State) (depth : Nat) :
    PureReturns runtime [] state (apply "gslt:deep:goal" [encoded (premisesFamilyTerm plan lane), number depth]) state
      (encoded (goalTerm ((Complete.EquationJob.family plan lane).goal depth))) := by
  metta_call complete_checked
  metta_eval unfolding [premisesFamilyTerm, goalTerm]

theorem premises_bounded_returns (lane : Complete.EquationJob.Lane) (state : State) (depth : Nat) :
    PureReturns runtime [] state (apply "gslt:deep:bounded" [encoded (premisesFamilyTerm plan lane), number depth]) state
      (Effects.boolean (match (Complete.EquationJob.family plan lane).bound with
        | some limit => decide (limit ≤ depth)
        | none => false)) := by
  rw [show (Complete.EquationJob.family plan lane).bound =
      Complete.EquationJob.premisesBound plan lane.job lane.answer.assignment from rfl]
  cases bounded : Complete.EquationJob.premisesBound plan lane.job lane.answer.assignment
  · metta_call complete_checked
    metta_eval unfolding [premisesFamilyTerm, bounded]
  · metta_call complete_checked
    metta_eval unfolding [premisesFamilyTerm, bounded]

/-- A lane's premise deepening, as MeTTa data. -/
def premisesWire (lane : Complete.EquationJob.Lane) : FamilyWire (Complete.EquationJob.family plan lane) where
  term := premisesFamilyTerm plan lane
  payload := outcomeTerm
  injective := outcomeTerm_injective
  answer result := by cases result; rfl
  goal := premises_goal_returns plan lane
  bounded := premises_bounded_returns plan lane

@[metta_head "gslt:equations:family"]
theorem equations_family_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (lane : Complete.EquationJob.Lane)
    (declared : (lane.job.equation, lane.job.planPosition) ∈ plan.equations.zipIdx) :
    PureReturns runtime [] state
      (apply "gslt:equations:family" [planValue plan table bound expected, encoded (laneTerm lane)])
      state (encoded (premisesFamilyTerm plan lane)) := by
  have context := equations_context_returns plan state table bound expected lane.job
  have limit := equations_limit_returns state plan table bound expected lane.job.equation lane.job.planPosition
    declared lane.answer.assignment
  rw [equationLimit_eq] at limit
  complete_eval [context, limit]
    unfolding [laneTerm, equationJobTerm, matcher_answer_term', InferenceCettaWire.AuthoredRule.rewriteTerm,
      premisesFamilyTerm]

/-- `gslt:rule:scope-reduct` without a reflective operation is `reduct?`. -/
theorem scoped_reduct_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-reduct" [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, assignmentValue assignment])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm (reduct? rule spec ambient assignment))) := by
  have instantiated : PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-instantiate-at"
        [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
         encoded (InferenceCettaWire.AuthoredRule.siteTerm .right), encoded (encodeList Term.natural []), number 0,
         assignmentValue assignment, encoded (InferenceCettaWire.encodePattern rule.right)])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (instantiateAt? rule spec ambient .right [] 0 assignment rule.right))) := by
    metta_bound ["operation", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "pattern"]
    exact transport scopedMachine_closed scopedMachine_agreement (by decide +kernel)
      (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.instantiate_returns _
        state rule spec ambient .right [] 0 assignment rule.right
        [.var "operation", .var "rule", .var "spec", .var "ambient", .var "site", .var "path", .var "depth",
          .var "assignment", .var "pattern"]
        (by metta_reads))
  metta_call scoped_checked
  metta_eval [instantiated] with scoped_checked
    unfolding [InferenceCettaWire.AuthoredRule.rewriteTerm, InferenceCettaWire.AuthoredRule.siteTerm, reduct?]

theorem complete_reduct_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) :
    PureReturns runtime [] state
      (apply "gslt:rule:scope-reduct" [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, assignmentValue assignment])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm (reduct? rule spec ambient assignment))) := by
  metta_raise ["operation", "rule", "spec", "ambient", "assignment"]
    (scoped_reduct_returns state rule spec ambient assignment)

/-- `gslt:rule:site-replacement-represented`, in the complete machine's runtime. -/
theorem complete_represented_returns (state : State) (language : LanguageDef) (context : OneHoleContext)
    (frames : List TypingFrame) (target : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:rule:site-replacement-represented"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms), contextValue context,
         encoded (encodeList ScopedRuleJobReadoutExecution.typingFrameTerm frames), patternValue target])
      state (Effects.boolean
        (Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.replacementRepresentations? language context frames target)) := by
  metta_from_readout ["declarations", "context", "frames", "target"]
    (ScopedRuleJobReadoutExecution.replacement_representations_returns state language context frames target)

/-- An equation receipt as MeTTa data. -/
def equationReceiptTerm (receipt : GeneralEquationJobs.Receipt) : Term :=
  .application "EquationReceipt" [equationJobTerm receipt.job,
    PremiseOperationsExecution.GeneralExecution.traceTerm receipt.matcherTrace, assignmentTerm receipt.captured,
    assignmentTerm receipt.completed, PremiseOperationsExecution.GeneralExecution.eventsTerm receipt.premiseHistory,
    InferenceCettaWire.encodePattern receipt.rawReduct, InferenceCettaWire.encodePattern receipt.target]

/-- What `gslt:equations:lift` needs about a lane and an outcome. -/
structure LiftScope (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (footprint : List String)
    (lane : Complete.EquationJob.Lane) (outcome : Complete.EquationJob.Outcome) : Prop where
  context : ∀ name ∈ Mettapedia.OSLF.Framework.DisplayedContextProfile.externalFreeFvarNames lane.job.site.context,
    name ∈ footprint
  captured : assignmentFreeWithin footprint lane.answer.assignment
  completed : assignmentFreeWithin footprint outcome.completed
  reduct : ∀ raw, reduct? lane.job.equation.rule lane.job.equation.binding.spec lane.job.site.focusBound.length
    outcome.completed = some raw → ∀ name ∈ raw.freeFvarNames, name ∈ footprint

syntax "lift_eval" " [" term,* "]" " unfolding" " [" term,* "]" : tactic
macro_rules
  | `(tactic| lift_eval [$facts,*] unfolding [$extra,*]) => `(tactic|
      complete_eval [$facts,*]
        unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
          PremiseOperationsExecution.DeclarationTyping.declarationsTerm, laneTerm, equationJobTerm,
          ScopedRuleJobReadoutExecution.siteTerm, matcher_answer_term', outcomeTerm, equationReceiptTerm,
          MatchAutomataBindingExecution.patternOptionTerm, patternValue, contextValue,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm, $extra,*])

@[metta_head "gslt:equations:lift"]
theorem equations_lift_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) (lane : Complete.EquationJob.Lane) (outcome : Complete.EquationJob.Outcome)
    (scope : LiftScope bound expected source footprint lane outcome) :
    PureReturns runtime [] state
      (apply "gslt:equations:lift" [planValue plan table bound expected, encoded (laneTerm lane),
        encoded (outcomeTerm outcome)])
      state (encoded (encodeOption equationReceiptTerm (Complete.EquationJob.lift plan bound expected lane outcome))) := by
  subst tabled
  obtain ⟨job, answer⟩ := lane
  obtain ⟨completed, history⟩ := outcome
  have capturedCheck := complete_check_assignment_returns state (GeneralPlanEnvironment.environment plan).language
    (plan.snapshot.free.entriesOn footprint) job.site.focusBound job.equation.rule job.equation.binding.spec
    answer.assignment
  have completedCheck := complete_check_assignment_returns state (GeneralPlanEnvironment.environment plan).language
    (plan.snapshot.free.entriesOn footprint) job.site.focusBound job.equation.rule job.equation.binding.spec completed
  have capturedSnapshot := ConditionalEquationExecution.checkAssignment_snapshot (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free job.site.focusBound job.equation.rule job.equation.binding.spec answer.assignment footprint
    (ConditionalEquationExecution.assignment_free_names_covered footprint _ scope.captured)
  have completedSnapshot := ConditionalEquationExecution.checkAssignment_snapshot (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free job.site.focusBound job.equation.rule job.equation.binding.spec completed footprint
    (ConditionalEquationExecution.assignment_free_names_covered footprint _ scope.completed)
  have ambient := complete_length_returns InferenceCettaWire.AuthoredRule.typeTerm state job.site.focusBound
  have reduced := complete_reduct_returns state job.equation.rule job.equation.binding.spec job.site.focusBound.length
    completed
  simp only [Complete.EquationJob.lift, GeneralEquationJobs.finish]
  by_cases first : checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) answer.assignment = true
  · have capturedTrue : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
        (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
        job.equation.binding.spec answer.assignment = true := by rw [capturedSnapshot]; exact first
    by_cases second : checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) completed = true
    · have completedTrue : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
          (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
          job.equation.binding.spec completed = true := by rw [completedSnapshot]; exact second
      cases instantiated : reduct? job.equation.rule job.equation.binding.spec job.site.focusBound.length completed with
      | none =>
        have erased := erase_returns state (.bvar 0)
        have represented := complete_represented_returns state (GeneralPlanEnvironment.environment plan).language job.site.context
          job.site.typingFrames (.bvar 0)
        have sortedLocal := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
          job.site.focusBound job.site.focusType (.bvar 0)
        have filled := complete_fill_returns state job.site.context (.bvar 0)
        have erasedFilled := erase_returns state (.bvar 0)
        have sortedTarget := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
          bound expected (.bvar 0)
        simp only [first, second, Bool.and_self, ↓reduceIte]
        lift_eval [capturedCheck, completedCheck, ambient, reduced] unfolding [capturedTrue, completedTrue, instantiated]
      | some raw =>
        have localWithin : ∀ name ∈ raw.eraseBinderMetadata.freeFvarNames, name ∈ footprint := by
          rw [freeFvarNames_erase]; exact scope.reduct raw instantiated
        have targetWithin : ∀ name ∈ (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata.freeFvarNames,
            name ∈ footprint := by
          rw [freeFvarNames_erase]
          intro name member
          rcases (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mp member with
            outside | inside
          · exact scope.context name outside
          · exact localWithin name inside
        have erased := erase_returns state raw
        have represented := complete_represented_returns state (GeneralPlanEnvironment.environment plan).language job.site.context
          job.site.typingFrames raw.eraseBinderMetadata
        have sortedLocal := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
          job.site.focusBound job.site.focusType raw.eraseBinderMetadata
        rw [Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot _ _ _ _ _ footprint localWithin]
          at sortedLocal
        have filled := complete_fill_returns state job.site.context raw.eraseBinderMetadata
        have erasedFilled := erase_returns state (job.site.context.fill raw.eraseBinderMetadata)
        have sortedTarget := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
          bound expected (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata
        rw [Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot _ _ _ _ _ footprint targetWithin]
          at sortedTarget
        simp only [first, second, Bool.and_self, ↓reduceIte, GeneralEquationJobs.acceptable]
        simp only [SiteData.acceptsReplacementRepresentation]
        cases r : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.replacementRepresentations?
            (GeneralPlanEnvironment.environment plan).language job.site.context job.site.typingFrames
            raw.eraseBinderMetadata
        · lift_eval [capturedCheck, completedCheck, ambient, reduced, erased, represented] unfolding [capturedTrue, completedTrue, instantiated, r, SiteData.acceptsReplacementRepresentation]
        · cases t : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free job.site.focusBound
              job.site.focusType raw.eraseBinderMetadata
          · lift_eval [capturedCheck, completedCheck, ambient, reduced, erased, represented, sortedLocal] unfolding [capturedTrue, completedTrue, instantiated, r, t, SiteData.acceptsReplacementRepresentation]
          · cases u : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
                (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata
            · lift_eval [capturedCheck, completedCheck, ambient, reduced, erased, represented, sortedLocal, filled, erasedFilled, sortedTarget] unfolding [capturedTrue, completedTrue, instantiated, r, t, u, SiteData.acceptsReplacementRepresentation]
            · lift_eval [capturedCheck, completedCheck, ambient, reduced, erased, represented, sortedLocal, filled, erasedFilled, sortedTarget] unfolding [capturedTrue, completedTrue, instantiated, r, t, u, SiteData.acceptsReplacementRepresentation]
    · have completedFalse : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
          (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
          job.equation.binding.spec completed = false := by
        rw [completedSnapshot]; exact Bool.eq_false_iff.mpr second
      have erased := erase_returns state (.bvar 0)
      have represented := complete_represented_returns state (GeneralPlanEnvironment.environment plan).language job.site.context
        job.site.typingFrames (.bvar 0)
      have sortedLocal := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
        job.site.focusBound job.site.focusType (.bvar 0)
      have filled := complete_fill_returns state job.site.context (.bvar 0)
      have erasedFilled := erase_returns state (.bvar 0)
      have sortedTarget := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
        bound expected (.bvar 0)
      simp only [first, Bool.eq_false_iff.mpr second, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      lift_eval [capturedCheck, completedCheck] unfolding [capturedTrue, completedFalse]
  · have capturedFalse : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
        (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
        job.equation.binding.spec answer.assignment = false := by
      rw [capturedSnapshot]; exact Bool.eq_false_iff.mpr first
    have erased := erase_returns state (.bvar 0)
    have represented := complete_represented_returns state (GeneralPlanEnvironment.environment plan).language job.site.context
      job.site.typingFrames (.bvar 0)
    have sortedLocal := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
      job.site.focusBound job.site.focusType (.bvar 0)
    have filled := complete_fill_returns state job.site.context (.bvar 0)
    have erasedFilled := erase_returns state (.bvar 0)
    have sortedTarget := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language (plan.snapshot.free.entriesOn footprint)
      bound expected (.bvar 0)
    simp only [Bool.eq_false_iff.mpr first, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    lift_eval [capturedCheck] unfolding [capturedFalse]

@[metta_head "gslt:equations:lane-limits"]
theorem lane_limits_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : ∀ lanes : List Complete.EquationJob.Lane,
      (∀ lane ∈ lanes, (lane.job.equation, lane.job.planPosition) ∈ plan.equations.zipIdx) →
      PureReturns runtime [] state
        (apply "gslt:equations:lane-limits" [planValue plan table bound expected, encoded (encodeList laneTerm lanes)])
        state (encoded (encodeList (encodeOption Term.natural)
          (lanes.map fun lane => Complete.EquationJob.premisesBound plan lane.job lane.answer.assignment)))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | lane :: rest, declared => by
    have limit := equations_limit_returns state plan table bound expected lane.job.equation lane.job.planPosition
      (declared lane (by simp)) lane.answer.assignment
    rw [equationLimit_eq] at limit
    have later := lane_limits_returns state table bound expected rest (fun other member => declared other (by simp [member]))
    complete_eval [limit, later] unfolding [encodeList, laneTerm, equationJobTerm, matcher_answer_term']

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
