import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralRhoOrigins

/-!
# Original COMM through the general typed occurrence frontier

The selected source companion preserves the original COMM patterns. Actual
frontier jobs retain the input body and collection choices under typed input
and parallel contexts. Structural equation closure and canonical channel
equivalence are outside this selected profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho.FrontierControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralScopedMatchMachine

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def receivedBody : Pattern := .apply "PDrop" [.bvar 0]
def outerBody : Pattern := .apply "PDrop" [.bvar 1]
def rootSource : Pattern := source channel receivedBody zero []
def rootTarget : Pattern := .collection .hashBag [zero] none
def inputSource : Pattern := input channel (source (.bvar 0) outerBody zero [])
def inputTarget : Pattern := input channel (.collection .hashBag [.apply "PDrop" [.bvar 0]] none)
def parallelSource : Pattern := .collection .hashBag [zero, rootSource] none
def parallelTarget : Pattern := .collection .hashBag [zero, rootTarget] none
def duplicates : Pattern := duplicateSource channel receivedBody zero
def duplicateTarget : Pattern := .collection .hashBag [zero, input channel receivedBody] none

def runtimePlan : GeneralExecutionAdmission.Plan where
  snapshot := snapshot
  permissions := permissions
  rules := [declaration]
  equations := []
  obligations := []

theorem runtime_plan_actual : plan = runtimePlan := by
  have rules := compiled_rules
  have equations := compilation_has_no_equations
  have obligations := List.isEmpty_iff.mp compilation_complete
  change (GeneralExecutionAdmission.compile snapshot permissions).obligations = [] at obligations
  dsimp only [GeneralExecutionAdmission.compile] at obligations
  unfold plan GeneralExecutionAdmission.compile at rules equations ⊢
  simp only at rules equations
  rw [rules, equations, obligations]
  rfl

def actualRequest (pattern : Pattern) : GeneralOccurrenceFrontier.Request :=
  .fromSnapshot snapshot permissions [] (.base "Proc") pattern

def literalRequest (pattern : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan, [], .base "Proc", pattern⟩

theorem actual_request (pattern : Pattern) : actualRequest pattern = literalRequest pattern := by
  change (⟨plan, [], .base "Proc", pattern⟩ : GeneralOccurrenceFrontier.Request) = literalRequest pattern
  rw [runtime_plan_actual]
  rfl

theorem literal_start {pattern : Pattern}
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (checked : checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") pattern = true) :
    GeneralOccurrenceFrontier.start (literalRequest pattern) =
      { agenda := [.visit ⟨pattern, [], by
          rw [show (literalRequest pattern).root = pattern from
            Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
          exact .nil pattern⟩, .universe] } := by
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root, literalRequest,
    Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
  change (if checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") pattern then _ else _) = _
  rw [checked]
  rfl

structure Readout where
  declarationIndex : Nat
  address : List Nat
  binders : List TypeExpr
  matcherTrace : List BagChoice
  sourceBody : Option Pattern
  target : Pattern
  deriving Repr, DecidableEq

def rawReadout (receipt : GeneralOccurrenceSemantics.Receipt) : Readout :=
  ⟨receipt.firing.job.declaration.declarationIndex, receipt.firing.job.site.address,
    receipt.firing.job.site.focusBound, receipt.firing.matcherTrace,
    (ScopedRuleMatching.lookup receipt.firing.captured "p").map RuleBinding.ContextualValue.body,
    receipt.target⟩

def readouts (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) : List Readout :=
  ((GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).answers.map Subtype.val).map rawReadout

def phase {query : GeneralOccurrenceFrontier.Request} : GeneralOccurrenceFrontier.Task query → String
  | .visit _ => "visit"
  | .incoming _ _ => "incoming"
  | .universe => "universe"
  | .scanUniverse _ => "scan-universe"
  | .rule _ => "rule"
  | .equation _ => "equation"

def headPhase (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) : Option String :=
  (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).agenda.head?.map phase

theorem actual_received_drop :
    readouts (actualRequest rootSource) 40 =
      [⟨0, [], [], commTrace, some receivedBody, rootTarget⟩] := by
  rw [actual_request]
  unfold readouts
  rw [literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem actual_input_context_and_outer_name :
    readouts (actualRequest inputSource) 60 =
      [⟨0, [1, 0], [.base "Name"], commTrace, some outerBody, inputTarget⟩] := by
  rw [actual_request]
  unfold readouts
  rw [literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem actual_parallel_context :
    readouts (actualRequest parallelSource) 60 =
      [⟨0, [1], [], commTrace, some receivedBody, parallelTarget⟩] := by
  rw [actual_request]
  unfold readouts
  rw [literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem actual_duplicate_bag_origins :
    readouts (actualRequest duplicates) 75 =
      [⟨0, [], [], firstInputTrace, some receivedBody, duplicateTarget⟩,
       ⟨0, [], [], secondInputTrace, some receivedBody, duplicateTarget⟩] := by
  rw [actual_request]
  unfold readouts
  rw [literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

def matcherPending (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) : Bool :=
  match (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).agenda with
  | .rule frame :: _ =>
      match frame.state.agenda with
      | .root root :: _ =>
          match root.state.agenda with
          | .rootMatch matched :: _ => !matched.state.agenda.isEmpty
          | _ => false
      | _ => false
  | _ => false

theorem pause_inside_actual_matching :
    readouts (actualRequest rootSource) 5 = [] ∧
      matcherPending (actualRequest rootSource) 5 = true := by
  rw [actual_request]
  unfold readouts matcherPending
  rw [literal_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem whole_state_resume :
    GeneralOccurrenceFrontier.run (actualRequest rootSource) 35
      (GeneralOccurrenceFrontier.run (actualRequest rootSource) 5
        (GeneralOccurrenceFrontier.start (actualRequest rootSource))) =
      GeneralOccurrenceFrontier.run (actualRequest rootSource) 40
        (GeneralOccurrenceFrontier.start (actualRequest rootSource)) :=
  (GeneralOccurrenceFrontier.run_add _ 5 35 _).symm

theorem controls_are_pre_saturation :
    headPhase (actualRequest rootSource) 40 = some "rule" ∧
    headPhase (actualRequest inputSource) 60 = some "rule" ∧
    headPhase (actualRequest parallelSource) 60 = some "rule" ∧
    headPhase (actualRequest duplicates) 75 = some "rule" := by
  repeat' apply And.intro
  all_goals
    rw [actual_request]
    unfold headPhase
    rw [literal_start (by decide +kernel) (by decide +kernel)]
    decide +kernel

theorem ill_typed_channel_rejected :
    (GeneralOccurrenceFrontier.start (actualRequest (source zero receivedBody zero []))).unresolved =
      [.sourceRejected] := by
  rw [actual_request]
  have rejected : checkOpenPatternWellSorted
      (literalRequest (source zero receivedBody zero [])).plan.snapshot.language
      (literalRequest (source zero receivedBody zero [])).plan.snapshot.free
      (literalRequest (source zero receivedBody zero [])).bound
      (literalRequest (source zero receivedBody zero [])).expected
      (literalRequest (source zero receivedBody zero [])).root = false := by
    change checkOpenPatternWellSorted language snapshot.free [] (.base "Proc")
      (source zero receivedBody zero []).eraseBinderMetadata = false
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)]
    decide +kernel
  unfold GeneralOccurrenceFrontier.start
  rw [rejected]
  rfl

#print axioms actual_received_drop
#print axioms actual_input_context_and_outer_name
#print axioms actual_parallel_context
#print axioms actual_duplicate_bag_origins
#print axioms pause_inside_actual_matching
#print axioms whole_state_resume

end Mettapedia.OSLF.MeTTaIL.GeneralRho.FrontierControls
