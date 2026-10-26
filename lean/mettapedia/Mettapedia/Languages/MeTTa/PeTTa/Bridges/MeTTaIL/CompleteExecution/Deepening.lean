import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Lists
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentExpand

/-!
# Deepening in the complete machine

`gslt:deep:*` runs `Complete.Deep` for a family given as MeTTa data: the scheduled search at the
current depth, the payloads published before it, and on a drained, uncertified level a fresh
level one deeper. A `FamilyWire` says how a family is written: its data, how its goal at each
depth and its depth bound are read from that data, and an injective encoding of its payloads,
since the MeTTa de-duplicates payloads by comparing their encodings.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

/-- `gslt:automata:member` is list membership of wire terms. -/
theorem scoped_member_returns (state : State) (value : Term) : ∀ values : List Term,
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:automata:member" [encoded value, encoded (encodeList id values)]) state
      (Effects.boolean (decide (value ∈ values)))
  | [] => by
    metta_call scoped_checked
    metta_eval unfolding [encodeList]
  | other :: rest => by
    have later := scoped_member_returns state value rest
    by_cases same : value = other
    · subst same
      metta_call scoped_checked
      metta_eval [later] with scoped_checked unfolding [encodeList, List.mem_cons_self, decide_true]
    · metta_call scoped_checked
      metta_eval [later] with scoped_checked unfolding [encodeList, same, List.mem_cons, false_or]

/-- `gslt:automata:member` on an injective encoding is membership. -/
theorem complete_member_returns {α : Type} [DecidableEq α] (encoder : α → Term)
    (injective : Function.Injective encoder) (state : State) (value : α) (values : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:member" [encoded (encoder value), encoded (encodeList encoder values)]) state
      (Effects.boolean (decide (value ∈ values))) := by
  have raised : PureReturns runtime [] state
      (apply "gslt:automata:member" [encoded (encoder value), encoded (encodeList id (values.map encoder))]) state
      (Effects.boolean (decide (encoder value ∈ values.map encoder))) := by
    exact scoped_member_returns state (encoder value) (values.map encoder)
  have member : (encoder value ∈ values.map encoder) ↔ value ∈ values := by
    constructor
    · intro found
      obtain ⟨other, mem, equal⟩ := List.mem_map.mp found
      rwa [injective equal] at mem
    · exact List.mem_map_of_mem
  simpa [CettaWire.encodeList_map, member] using raised

/-- How a deepening family is written for the MeTTa. -/
structure FamilyWire (family : Complete.Deep.Family) where
  term : Term
  payload : family.Payload → Term
  injective : Function.Injective payload
  answer : ∀ {depth : Nat} (result : Result family.environment (family.goal depth)),
    answerTerm result = payload (family.read result)
  goal : ∀ (state : State) (depth : Nat),
    PureReturns runtime [] state (apply "gslt:deep:goal" [encoded term, number depth]) state
      (encoded (goalTerm (family.goal depth)))
  bounded : ∀ (state : State) (depth : Nat),
    PureReturns runtime [] state (apply "gslt:deep:bounded" [encoded term, number depth]) state
      (Effects.boolean (match family.bound with
        | some limit => decide (limit ≤ depth)
        | none => false))

variable {family : Complete.Deep.Family} (wire : FamilyWire family)

/-- A deepening state as MeTTa data: `(DeepState depth level published)`. -/
def deepStateTerm (search : Complete.Deep.State family) : Term :=
  .application "DeepState" [.natural search.depth, stateTerm search.level, encodeList wire.payload search.published]

theorem complete_descent_start_returns (state : State) (environment : Environment) (goal : Goal) :
    PureReturns runtime [] state (apply "gslt:descent:start" [goalValue goal]) state
      (descentStateValue (StructuralDescent.Scheduled.start environment goal)) := by
  exact descent_start_returns state environment goal

@[metta_head "gslt:deep:level-start"]
theorem deep_level_start_returns (state : State) (depth : Nat) (published : List family.Payload) :
    PureReturns runtime [] state
      (apply "gslt:deep:level-start" [encoded wire.term, number depth, encoded (encodeList wire.payload published)])
      state (encoded (deepStateTerm wire (Complete.Deep.levelStart family depth published))) := by
  metta_call_in completeProof_checked using completeProof_agreement
  metta_eval [wire.goal state depth,
      complete_descent_start_returns state family.environment (family.goal depth)] with completeProof_checked in completeProof_agreement
    unfolding [deepStateTerm, Complete.Deep.levelStart, goalValue, descentStateValue]

@[metta_head "gslt:deep:start"]
theorem deep_start_returns (state : State) :
    PureReturns runtime [] state (apply "gslt:deep:start" [encoded wire.term]) state
      (encoded (deepStateTerm wire (Complete.Deep.start family))) := by
  metta_call_in completeProof_checked using completeProof_agreement
  metta_eval [deep_level_start_returns wire state 0 []] with completeProof_checked in completeProof_agreement
    unfolding [Complete.Deep.start, encodeList]

@[metta_head "gslt:deep:fresh"]
theorem deep_fresh_returns (state : State) (published : List family.Payload) : ∀ answers : List family.Payload,
    PureReturns runtime [] state
      (apply "gslt:deep:fresh" [encoded (encodeList wire.payload published), encoded (encodeList wire.payload answers)])
      state (encoded (encodeList wire.payload (Complete.Deep.fresh family published answers)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [encodeList, Complete.Deep.fresh]
  | answer :: rest => by
    have later := deep_fresh_returns state published rest
    have member := complete_member_returns wire.payload wire.injective state answer published
    by_cases found : answer ∈ published
    · rw [show Complete.Deep.fresh family published (answer :: rest) = Complete.Deep.fresh family published rest by
        simp [Complete.Deep.fresh, found]]
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [later, member] with completeProof_checked in completeProof_agreement unfolding [encodeList, found]
    · rw [show Complete.Deep.fresh family published (answer :: rest) =
          answer :: Complete.Deep.fresh family published rest by simp [Complete.Deep.fresh, found]]
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [later, member] with completeProof_checked in completeProof_agreement unfolding [encodeList, found]

theorem answers_payloads {depth : Nat} (results : List (Result family.environment (family.goal depth))) :
    encodeList answerTerm results = encodeList wire.payload (results.map family.read) := by
  induction results with
  | nil => rfl
  | cons result rest ih => simp [encodeList, ih, wire.answer result]

theorem complete_payloads_returns (state : State) {environment : Environment} {goal : Goal}
    (results : List (Result environment goal)) :
    PureReturns runtime [] state (apply "gslt:descent:payloads" [encoded (encodeList resultTerm results)])
      state (encoded (encodeList answerTerm results)) := by
  exact descent_payloads_returns state results

theorem complete_cut_returns (state : State) (obligations : List Obligation) :
    PureReturns runtime [] state (apply "gslt:descent:cut" [obligationsValue obligations]) state
      (Effects.boolean (obligations.any Complete.Deep.isCut)) := by
  exact descent_cut_returns state obligations

@[metta_head "gslt:deep:publication"]
theorem deep_publication_returns (state : State) (search : Complete.Deep.State family) :
    PureReturns runtime [] state (apply "gslt:deep:publication" [encoded (deepStateTerm wire search)]) state
      (encoded (encodeList wire.payload search.publication)) := by
  obtain ⟨depth, ⟨agenda, answers, unresolved, work⟩, published⟩ := search
  have payloads := complete_payloads_returns state answers
  rw [answers_payloads wire answers] at payloads
  have fresh := deep_fresh_returns wire state published (answers.map family.read)
  have joined := automata_append_returns wire.payload state published
    (Complete.Deep.fresh family published (answers.map family.read))
  metta_call_in completeProof_checked using completeProof_agreement
  metta_eval [payloads, fresh, joined] with completeProof_checked in completeProof_agreement
    unfolding [deepStateTerm, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, Complete.Deep.State.publication]

@[metta_head "gslt:deep:certified"]
theorem deep_certified_returns (state : State) (search : Complete.Deep.State family) :
    PureReturns runtime [] state
      (apply "gslt:deep:certified" [encoded wire.term, encoded (deepStateTerm wire search)]) state
      (Effects.boolean (Complete.Deep.certified family search)) := by
  obtain ⟨depth, ⟨agenda, answers, unresolved, work⟩, published⟩ := search
  have cut := complete_cut_returns state unresolved
  have bounded := wire.bounded state depth
  cases cutting : unresolved.any Complete.Deep.isCut
  · metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [cut] with completeProof_checked in completeProof_agreement
      unfolding [deepStateTerm, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, obligationsValue, cutting,
        Complete.Deep.certified]
  · metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [cut, bounded] with completeProof_checked in completeProof_agreement
      unfolding [deepStateTerm, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, obligationsValue, cutting,
        Complete.Deep.certified]

@[metta_head "gslt:deep:drained"]
theorem deep_drained_returns (state : State) (search : Complete.Deep.State family) :
    PureReturns runtime [] state (apply "gslt:deep:drained" [encoded (deepStateTerm wire search)]) state
      (Effects.boolean search.level.agenda.isEmpty) := by
  obtain ⟨depth, ⟨agenda, answers, unresolved, work⟩, published⟩ := search
  cases agenda <;>
  · metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [deepStateTerm, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, encodeList]

@[metta_head "gslt:deep:complete"]
theorem deep_complete_returns (state : State) (search : Complete.Deep.State family) :
    PureReturns runtime [] state
      (apply "gslt:deep:complete" [encoded wire.term, encoded (deepStateTerm wire search)]) state
      (Effects.boolean search.complete) := by
  have drained := deep_drained_returns wire state search
  have certified := deep_certified_returns wire state search
  cases empty : search.level.agenda.isEmpty
  · metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [drained] with completeProof_checked in completeProof_agreement unfolding [empty, Complete.Deep.State.complete]
  · metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [drained, certified] with completeProof_checked in completeProof_agreement unfolding [empty, Complete.Deep.State.complete]

/-- **`gslt:deep:tick` is `Deep.tick`**, given what `gslt:descent:tick` returns on the level. -/
@[metta_head "gslt:deep:tick"]
theorem deep_tick_returns (state : State) (environmentData : Atom) (search : Complete.Deep.State family)
    (ticked : PureReturns runtime [] state (apply "gslt:descent:tick" [environmentData, descentStateValue search.level])
      state (descentStateValue (StructuralDescent.Scheduled.tick family.environment (family.goal search.depth)
        search.level))) :
    PureReturns runtime [] state
      (apply "gslt:deep:tick" [environmentData, encoded wire.term, encoded (deepStateTerm wire search)]) state
      (encoded (deepStateTerm wire (Complete.Deep.tick family search))) := by
  have drained := deep_drained_returns wire state search
  have certified := deep_certified_returns wire state search
  have publication := deep_publication_returns wire state search
  have started := deep_level_start_returns wire state (search.depth + 1) search.publication
  cases empty : search.level.agenda.isEmpty
  · have steady : Complete.Deep.tick family search =
        { search with
          level := (StructuralDescent.Scheduled.tick family.environment (family.goal search.depth) search.level) } := by
      simp [Complete.Deep.tick, Complete.Deep.deepens, empty]
    rw [steady]
    obtain ⟨depth, level, published⟩ := search
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [drained, ticked] with completeProof_checked in completeProof_agreement unfolding [empty, deepStateTerm, descentStateValue]
  · cases checked : Complete.Deep.certified family search
    · have deeper : Complete.Deep.tick family search =
          Complete.Deep.levelStart family (search.depth + 1) search.publication := by
        simp [Complete.Deep.tick, Complete.Deep.deepens, empty, checked]
      rw [deeper]
      obtain ⟨depth, level, published⟩ := search
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [drained, certified, publication, started] with completeProof_checked in completeProof_agreement
        unfolding [empty, checked, deepStateTerm]
    · have kept : Complete.Deep.tick family search = search := by
        obtain ⟨depth, ⟨agenda, answers, unresolved, work⟩, published⟩ := search
        cases agenda with
        | nil => simp [Complete.Deep.tick, Complete.Deep.deepens, StructuralDescent.Scheduled.tick, Scheduler.tick, checked]
        | cons first rest => simp at empty
      rw [kept]
      obtain ⟨depth, level, published⟩ := search
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [drained, certified] with completeProof_checked in completeProof_agreement unfolding [empty, checked, deepStateTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.scoped_member_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_member_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deepStateTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_descent_start_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_level_start_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_start_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_fresh_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.answers_payloads

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_payloads_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_cut_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_publication_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_certified_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_drained_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_complete_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.deep_tick_returns
