import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.EquationLift
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesReady

/-!
# Steps modulo equations: lanes and their events

`gslt:classes:*` runs `Complete.Classes`. A representative of the source's class runs rule lanes,
forward equation lanes and backward lanes at its predecessor candidates; newly published payloads
of a lane become events: firings of rule lanes, members discovered by equation lanes. The plan's
free-type table is the snapshot on a footprint that lists every declared name.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding DerivedContexts GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope Declared OutcomeWithin FiringWithin KeyReady ClassReady)
open GeneralOccurrenceSemantics (Conversion)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

def conversionTerm : Conversion → Term
  | .forward receipt => .application "ForwardConversion" [equationReceiptTerm receipt]
  | .reverse receipt => .application "ReverseConversion" [equationReceiptTerm receipt]

def repTerm (rep : Complete.Classes.Rep) : Term :=
  .application "ClassRep" [InferenceCettaWire.encodePattern rep.pattern, encodeList conversionTerm rep.conversions,
    .natural rep.born]

def keyTerm : Complete.Classes.Key → Term
  | .rule rep job => .application "RuleKey" [repTerm rep, ScopedRuleJobReadoutExecution.jobTerm job]
  | .forward rep lane => .application "ForwardKey" [repTerm rep, laneTerm lane]
  | .backward rep candidate lane =>
      .application "BackwardKey" [repTerm rep, InferenceCettaWire.encodePattern candidate, laneTerm lane]

def classReceiptTerm (receipt : GeneralOccurrenceSemantics.Receipt) : Term :=
  .application "ClassReceipt" [InferenceCettaWire.encodePattern receipt.representative,
    encodeList conversionTerm receipt.conversions, ScopedRuleJobReadoutExecution.receiptTerm receipt.firing]

def eventTerm : Complete.Classes.Event → Term
  | .firing receipt => .application "FiringEvent" [classReceiptTerm receipt]
  | .discovery pattern conversions =>
      .application "DiscoveryEvent" [InferenceCettaWire.encodePattern pattern, encodeList conversionTerm conversions]

variable (plan : GeneralExecutionAdmission.Plan)

/-- How a lane's deepening is written. -/
def wireOf : (key : Complete.Classes.Key) → FamilyWire (Complete.Classes.family plan key)
  | .rule _ job => rootWire (Complete.Step.request plan job)
  | .forward _ lane => premisesWire plan lane
  | .backward _ _ lane => premisesWire plan lane

def classEntryTerm (entry : Complete.Classes.Entry plan) : Term :=
  .application "ClassEntry" [keyTerm entry.1, deepStateTerm (wireOf plan entry.1) entry.2]

def classStateTerm (state : Complete.Classes.State plan) : Term :=
  .application "ClassState" [.natural state.round, encodeList repTerm state.reps,
    encodeList (classEntryTerm plan) state.entries, encodeList classReceiptTerm state.log]

/-- A lane's key is licensed at its representative or candidate. -/
def KeyLicensed (bound : List TypeExpr) (expected : TypeExpr) : Complete.Classes.Key → Prop
  | .rule rep job => job.Valid plan bound expected rep.pattern
  | .forward rep lane => lane ∈ Complete.EquationJob.lanes plan bound expected rep.pattern
  | .backward _ candidate lane => lane ∈ Complete.EquationJob.lanes plan bound expected candidate

theorem lane_declared {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {lane : Complete.EquationJob.Lane} (member : lane ∈ Complete.EquationJob.lanes plan bound expected source) :
    (lane.job.equation, lane.job.planPosition) ∈ plan.equations.zipIdx :=
  (Complete.Footprint.lane_licensed member).1

@[metta_head "gslt:classes:family"]
theorem classes_family_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (key : Complete.Classes.Key) (licensed : KeyLicensed plan bound expected key) :
    PureReturns runtime [] state
      (apply "gslt:classes:family" [planValue plan table bound expected, encoded (keyTerm key)])
      state (encoded (wireOf plan key).term) := by
  cases key with
  | rule rep job =>
    have family := step_family_returns plan state job
    complete_eval [family] unfolding [keyTerm, wireOf, rootWire, planValue, CompletePlanWire.planTerm, admittedValue]
  | forward rep lane =>
    have family := equations_family_returns plan state table bound expected lane (lane_declared plan licensed)
    complete_eval [family] unfolding [keyTerm, wireOf, premisesWire]
  | backward rep candidate lane =>
    have family := equations_family_returns plan state table bound expected lane (lane_declared plan licensed)
    complete_eval [family] unfolding [keyTerm, wireOf, premisesWire]

@[metta_head "gslt:classes:firing-events"]
theorem firing_events_returns (state : State) (pattern : Pattern) (conversions : List Conversion) :
    ∀ receipts : List GeneralRuleJobs.Receipt,
      PureReturns runtime [] state
        (apply "gslt:classes:firing-events" [patternValue pattern, encoded (encodeList conversionTerm conversions),
          encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts)])
        state (encoded (encodeList eventTerm (receipts.map fun firing => .firing ⟨pattern, conversions, firing⟩)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | receipt :: rest => by
    have later := firing_events_returns state pattern conversions rest
    complete_eval [later] unfolding [encodeList, eventTerm, classReceiptTerm, patternValue]

theorem encodePattern_injective : Function.Injective InferenceCettaWire.encodePattern := by
  intro first second same
  have decoded := congrArg InferenceCettaWire.decodePattern same
  simpa using decoded

theorem lift_scope_of_lane {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) {source : Pattern} {lane : Complete.EquationJob.Lane}
    (member : lane ∈ Complete.EquationJob.lanes plan bound expected source) {outcome : Complete.EquationJob.Outcome}
    (within : OutcomeWithin footprint outcome) :
    LiftScope bound expected source footprint lane outcome where
  context := Complete.Footprint.context_within (Complete.Footprint.lane_licensed member).2
    (Complete.Footprint.lane_source_within scope.declared member)
  captured := Complete.Footprint.lane_answer_within scope.declared member
  completed := within
  reduct _ reduced := Complete.Footprint.reduct_within scope member within reduced

@[metta_head "gslt:classes:forward-events"]
theorem forward_events_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (source : Pattern) (lane : Complete.EquationJob.Lane)
    (member : lane ∈ Complete.EquationJob.lanes plan bound expected source) (conversions : List Conversion) :
    ∀ payloads : List Complete.EquationJob.Outcome, (∀ payload ∈ payloads, OutcomeWithin footprint payload) →
      PureReturns runtime [] state
        (apply "gslt:classes:forward-events" [planValue plan table bound expected,
          encoded (encodeList conversionTerm conversions), encoded (laneTerm lane), encoded (encodeList outcomeTerm payloads)])
        state (encoded (encodeList eventTerm
          ((payloads.filterMap (Complete.EquationJob.lift plan bound expected lane)).map fun receipt =>
            .discovery receipt.target (conversions ++ [.forward receipt]))))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | payload :: rest, within => by
    have lifted := equations_lift_returns plan state table bound expected footprint tabled source lane payload
      (lift_scope_of_lane plan scope member (within payload (by simp)))
    have later := forward_events_returns state table bound expected footprint tabled scope source lane member
      conversions rest (fun other inside => within other (by simp [inside]))
    cases result : Complete.EquationJob.lift plan bound expected lane payload with
    | none =>
      rw [List.filterMap_cons_none result]
      complete_eval [lifted, later] unfolding [encodeList, result]
    | some receipt =>
      rw [List.filterMap_cons_some result]
      have path := complete_append_returns conversionTerm state conversions [.forward receipt]
      complete_eval [lifted, later, path]
        unfolding [encodeList, result, equationReceiptTerm, eventTerm, conversionTerm, List.map_cons]

theorem pattern_equal_returns (program : SpaceSemantics.Program) (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : State) (left right : Atom) (first second : Pattern)
    (leftReturns : PureReturns program caller state left state (patternValue first))
    (rightReturns : PureReturns program caller state right state (patternValue second)) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (first == second)) := by
  have compared := term_equal_returns program caller state left right _ _ leftReturns rightReturns
  have same : decide (InferenceCettaWire.encodePattern first = InferenceCettaWire.encodePattern second) =
      (first == second) := by
    by_cases equal : first = second
    · subst equal; simp [BEq.beq]
    · have different : InferenceCettaWire.encodePattern first ≠ InferenceCettaWire.encodePattern second :=
        fun same => equal (encodePattern_injective same)
      simp [BEq.beq, equal, different]
  rwa [same] at compared

@[metta_head "gslt:classes:backward-events"]
theorem backward_events_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (pattern candidate : Pattern) (lane : Complete.EquationJob.Lane)
    (member : lane ∈ Complete.EquationJob.lanes plan bound expected candidate) (conversions : List Conversion) :
    ∀ payloads : List Complete.EquationJob.Outcome, (∀ payload ∈ payloads, OutcomeWithin footprint payload) →
      PureReturns runtime [] state
        (apply "gslt:classes:backward-events" [planValue plan table bound expected, patternValue pattern,
          encoded (encodeList conversionTerm conversions), patternValue candidate, encoded (laneTerm lane),
          encoded (encodeList outcomeTerm payloads)])
        state (encoded (encodeList eventTerm
          (((payloads.filterMap (Complete.EquationJob.lift plan bound expected lane)).filter fun receipt =>
            receipt.target == pattern).map fun receipt => .discovery candidate (conversions ++ [.reverse receipt]))))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | payload :: rest, within => by
    have lifted := equations_lift_returns plan state table bound expected footprint tabled candidate lane payload
      (lift_scope_of_lane plan scope member (within payload (by simp)))
    have later := backward_events_returns state table bound expected footprint tabled scope pattern candidate lane
      member conversions rest (fun other inside => within other (by simp [inside]))
    cases result : Complete.EquationJob.lift plan bound expected lane payload with
    | none =>
      rw [List.filterMap_cons_none result]
      complete_eval [lifted, later] unfolding [encodeList, result]
    | some receipt =>
      rw [List.filterMap_cons_some result]
      by_cases same : (receipt.target == pattern) = true
      · rw [List.filter_cons_of_pos (p := fun receipt : GeneralEquationJobs.Receipt => receipt.target == pattern) same]
        have path := complete_append_returns conversionTerm state conversions [.reverse receipt]
        metta_call complete_checked
        metta_eval [lifted, later, path] with complete_checked
          unfolding [encodeList, result, equationReceiptTerm, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
            Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
        have equal : InferenceCettaWire.encodePattern receipt.target = InferenceCettaWire.encodePattern pattern :=
          congrArg InferenceCettaWire.encodePattern (beq_iff_eq.mp same)
        all_goals
          rw [if_pos equal]
          metta_eval [path] with complete_checked
            unfolding [encodeList, eventTerm, conversionTerm, equationReceiptTerm, List.map_cons, patternValue,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
              Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
      · rw [List.filter_cons_of_neg (p := fun receipt : GeneralEquationJobs.Receipt => receipt.target == pattern) same]
        metta_call complete_checked
        metta_eval [lifted, later] with complete_checked
          unfolding [encodeList, result, equationReceiptTerm, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
            Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
        have different : InferenceCettaWire.encodePattern receipt.target ≠ InferenceCettaWire.encodePattern pattern :=
          fun equal => same (beq_iff_eq.mpr (encodePattern_injective equal))
        all_goals
          rw [if_neg different]
          metta_eval [later] with complete_checked
            unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
              Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
