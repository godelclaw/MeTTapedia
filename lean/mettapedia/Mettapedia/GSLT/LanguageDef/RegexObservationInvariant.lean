import Mettapedia.GSLT.LanguageDef.RegexObservationTransport

/-!
# Invariants of intrinsic observation and retained capture slots

An invariant of ordinary control actions survives the finite priority-word
expansion and the selected trace. An absent capture-write instruction therefore
preserves its slot through ordinary execution and recursively nested assertions.
This applies to declared groups erased by counted lowering as well as to other
reserved layout slots.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexObservationInvariant

open Mettapedia.Computability.RegularLanguages
open RegexDependentObservation
open RegexObservationTrace (ObservedAction)
open RegexObservationKernel

def Expanded {α : Type} (property : α → Prop) {bound : Nat} :
    RegexObservationTrace.State α bound → Prop
  | .main state | .spool state _ => property state
  | .dead => True

theorem expanded_targets_preserve {α : Type} [Fintype α]
    (step : α → ObservedAction α) (property : α → Prop)
    (closed : ∀ first last, last ∈ RegexRankedObservation.actionTargets (step first) →
      property first → property last)
    (first last : RegexObservationTrace.State α (RegexObservationTrace.maxWord step))
    (edge : last ∈ RegexRankedObservation.nodeTargets (RegexObservationTrace.graph step first)) :
    Expanded property first → Expanded property last := by
  intro valid
  cases first with
  | dead => simp [RegexObservationTrace.graph, RegexRankedObservation.nodeTargets] at edge
  | main state =>
      cases operation : step state with
      | accept | dead =>
          simp [RegexObservationTrace.graph, operation, RegexRankedObservation.nodeTargets] at edge
      | next target bits =>
          simp [RegexObservationTrace.graph, operation, RegexRankedObservation.nodeTargets] at edge
          subst last
          exact valid
      | branch left right =>
          simp [RegexObservationTrace.graph, operation, RegexRankedObservation.nodeTargets] at edge
          rcases edge with rfl | rfl
          · exact closed state left (by simp [operation, RegexRankedObservation.actionTargets]) valid
          · exact closed state right (by simp [operation, RegexRankedObservation.actionTargets]) valid
  | spool origin index =>
      cases operation : step origin with
      | accept | dead | branch _ _ =>
          simp [RegexObservationTrace.graph, operation, RegexRankedObservation.nodeTargets] at edge
      | next target bits =>
          simp only [RegexObservationTrace.graph, operation] at edge
          split at edge
          · split at edge <;>
              simp only [RegexRankedObservation.nodeTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
            all_goals rcases edge with rfl | rfl <;> first | exact valid | trivial
          · simp only [RegexRankedObservation.nodeTargets, List.mem_singleton] at edge
            subst last
            exact closed origin target (by simp [operation, RegexRankedObservation.actionTargets]) valid

theorem graph_edges_preserve {α : Type}
    (graph : α → RegexTaggedGraph.Node α Unit Unit Unit) (property : α → Prop)
    (closed : ∀ first last, last ∈ RegexRankedObservation.nodeTargets (graph first) →
      property first → property last)
    (first last : RegexTaggedGraph.Thread α 0)
    (edge : last ∈ RegexTaggedGraph.edges graph probe first) :
    property first.point.1 → property last.point.1 := by
  intro valid
  cases operation : graph first.point.1 with
  | accept tag | dead => simp [RegexTaggedGraph.edges, operation] at edge
  | jump next | save slot next =>
      simp [RegexTaggedGraph.edges, operation] at edge
      subst last
      exact closed _ next (by simp [operation, RegexRankedObservation.nodeTargets]) valid
  | choice left right =>
      simp [RegexTaggedGraph.edges, operation] at edge
      rcases edge with rfl | rfl
      · exact closed _ left (by simp [operation, RegexRankedObservation.nodeTargets]) valid
      · exact closed _ right (by simp [operation, RegexRankedObservation.nodeTargets]) valid
  | consume contains next =>
      simp [RegexTaggedGraph.edges, operation, probe] at edge
  | assertion holds next =>
      simp [RegexTaggedGraph.edges, operation, probe] at edge

theorem selected_trace_preserves {α : Type} [Fintype α]
    (step : α → ObservedAction α) (property : α → Prop)
    (closed : ∀ first last, last ∈ RegexRankedObservation.actionTargets (step first) →
      property first → property last)
    (eligible : α → Bool) (first : α)
    (last : RegexTaggedGraph.Thread (RegexObservationTrace.State α (RegexObservationTrace.maxWord step)) 0)
    (selected : RegexSelectionCorrespondence.LeastSimple (RegexObservationTrace.graph step) probe
      (fun thread => RegexObservationTrace.mainEligible step eligible thread.point)
      (RegexObservationTrace.initial step first) last) (valid : property first) :
    Expanded property last.point.1 := by
  obtain ⟨bits, points, tag, trace, _, _⟩ := selected
  have path := trace.sound.1
  clear trace
  have start : Expanded property (RegexObservationTrace.initial step first).point.1 := valid
  induction path with
  | refl => exact start
  | tail path edge ih =>
      exact graph_edges_preserve _ (Expanded property)
        (expanded_targets_preserve step property closed) _ _ edge ih

theorem complete_preserves {states groups length : Nat}
    (code : Fin states → Instruction states groups) (root : Fin states)
    (step : Licensed code length root → ObservedAction (Licensed code length root))
    (property : Licensed code length root → Prop)
    (closed : ∀ first last, last ∈ RegexRankedObservation.actionTargets (step first) →
      property first → property last)
    (eligible : Configuration states groups length → Bool)
    (first : Licensed code length root) (winner : Winner states groups length)
    (valid : property first)
    (returned : RegexObservationKernel.complete code root step eligible first = some winner) :
    ∃ last : Licensed code length root, winner.configuration = last.val ∧ property last := by
  unfold RegexObservationKernel.complete at returned
  split at returned
  · contradiction
  · rename_i exhausted
    exact False.elim (RegexObservationTrace.run_ne_incomplete step _ first exhausted)
  · rename_i last tag result
    cases tag
    have checked := (RegexObservationTrace.run_selected_iff step _ first last).mp result
    have selected := checked.1
    obtain ⟨terminalState, terminalLocation⟩ := RegexObservationTrace.terminal_is_main step last checked.2
    have preserved := selected_trace_preserves step property closed _ first last selected valid
    split at returned
    · rename_i configuration location
      simp only [Option.some.injEq] at returned
      refine ⟨configuration, ?_, ?_⟩
      · exact congrArg Winner.configuration returned.symm
      · simpa [location, Expanded] using preserved
    · rename_i origin index location
      rw [location] at terminalLocation
      contradiction
    · rename_i location
      rw [location] at terminalLocation
      contradiction

/-- The slot is never written, including inside observation bodies. Reads do
not need to be excluded: they inspect rather than mutate capture contents. -/
def Unwritten {states groups : Nat} (code : Fin states → Instruction states groups)
    (slot : Fin groups) : Prop :=
  ∀ pc, match code pc with
    | .open group _ | .close group _ => group ≠ slot
    | _ => True

def PreservesSlot {states groups length : Nat} (slot : Fin groups)
    (observation : Observation states groups length) : Prop :=
  ∀ direction eligible position captures winner,
    observation direction eligible position captures = some winner →
      winner.configuration.captures slot = captures slot

theorem localWinner_preserves_slot {states groups length : Nat}
    (slot : Fin groups) (recurse : Observation states groups length)
    (preserved : PreservesSlot slot recurse) (kind : LookKind)
    (caller : Configuration states groups length) (winner : Winner states groups length)
    (selected : localWinner recurse kind caller = some winner) :
    winner.configuration.captures slot = caller.captures slot := by
  cases kind with
  | ahead | notAhead | reverseBehind | reverseNotBehind =>
      exact preserved _ _ _ _ _ selected
  | behind | notBehind =>
      have member := best_present _ winner selected
      obtain ⟨position, _, returned⟩ := List.mem_filterMap.mp member
      exact preserved _ _ position _ _ returned

theorem observed_preserves_slot {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (slot : Fin groups)
    (unwritten : Unwritten code slot)
    (body : LookKind → Fin states → Configuration states groups length → Option (Winner states groups length))
    (bodyPreserved : ∀ kind entry caller winner, body kind entry caller = some winner →
      winner.configuration.captures slot = caller.captures slot)
    (first last : Configuration states groups length)
    (edge : last ∈ RegexRankedObservation.actionTargets
      (RegexObservationTrace.observedAction interpretation input direction code body first)) :
    last.captures slot = first.captures slot := by
  have noWrite := unwritten first.pc
  cases instruction : code first.pc with
  | accept | dead =>
      simp [RegexObservationTrace.observedAction, action, instruction,
        RegexRankedObservation.actionTargets] at edge
  | jump next | branch left right =>
      simp_all [RegexObservationTrace.observedAction, action, RegexRankedObservation.actionTargets]
      all_goals rcases edge with rfl | rfl <;> rfl
  | «open» group next =>
      simp only [instruction] at noWrite
      simp only [RegexObservationTrace.observedAction, instruction, action,
        RegexRankedObservation.actionTargets, List.mem_singleton] at edge
      subst last
      simp [openCapture, Ne.symm noWrite]
  | close group next =>
      simp only [instruction] at noWrite
      simp only [RegexObservationTrace.observedAction, instruction, action,
        RegexRankedObservation.actionTargets, List.mem_singleton] at edge
      subst last
      exact close_other _ _ _ _ (Ne.symm noWrite)
  | consume contains next =>
      cases read : consumed input direction first.position <;>
        cases moved : advance direction first.position
      all_goals simp only [RegexObservationTrace.observedAction, instruction, action, read, moved] at edge
      all_goals try split_ifs at edge
      all_goals simp_all [RegexRankedObservation.actionTargets]
  | assertion holds next =>
      cases allowed : holds first.position <;>
        simp_all [RegexObservationTrace.observedAction, action, RegexRankedObservation.actionTargets]
  | backref group comparison next =>
      cases recalled : backreference interpretation input direction comparison first.captures group first.position <;>
        simp_all [RegexObservationTrace.observedAction, action, RegexRankedObservation.actionTargets]
  | look kind entry next =>
      cases negative : kind.negative <;> cases selected : body kind entry first
      all_goals simp only [RegexObservationTrace.observedAction, instruction, RegexObservationTrace.observedLook,
        negative, selected, RegexRankedObservation.actionTargets, List.mem_singleton, List.not_mem_nil] at edge
      all_goals subst last
      · exact bodyPreserved _ _ _ _ selected
      · rfl

theorem control_preserves_slot {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (slot : Fin groups)
    (unwritten : Unwritten code slot) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length)
    (recursive : ∀ entry call, PreservesSlot slot (recurse entry call))
    (first : Licensed code length root) (last : Configuration states groups length)
    (edge : last ∈ RegexRankedObservation.actionTargets
      (controlAction interpretation input direction code root recurse first)) :
    last.captures slot = first.val.captures slot := by
  unfold controlAction at edge
  split at edge
  · rename_i kind entry next instruction
    let licensed : DirectBodyCall code entry root :=
      ⟨first.val.pc, kind, next, first.property, instruction⟩
    change last ∈ RegexRankedObservation.actionTargets
      (RegexObservationTrace.observedLook kind first.val
        (localWinner (recurse entry licensed) kind first.val) next) at edge
    have localPreserved := localWinner_preserves_slot slot
      (recurse entry licensed) (recursive entry licensed) kind first.val
    cases negative : kind.negative <;>
      cases selected : localWinner (recurse entry licensed) kind first.val
    all_goals simp only [RegexObservationTrace.observedLook, negative, selected,
      RegexRankedObservation.actionTargets, List.mem_singleton, List.not_mem_nil] at edge
    all_goals subst last
    · exact localPreserved _ selected
    · rfl
  all_goals
    exact observed_preserves_slot interpretation input direction code slot unwritten
      (fun _ _ _ => none) (by intros; contradiction) first.val last edge

theorem liftAction_preserves {states groups length : Nat}
    {code : Fin states → Instruction states groups} {root : Fin states}
    (operation : ObservedAction (Configuration states groups length))
    (licensed : ∀ target ∈ RegexRankedObservation.actionTargets operation, OrdinaryReach code root target.pc)
    (first last : Licensed code length root) (property : Configuration states groups length → Prop)
    (closed : ∀ target ∈ RegexRankedObservation.actionTargets operation, property first.val → property target)
    (edge : last ∈ RegexRankedObservation.actionTargets (liftAction operation licensed)) :
    property first.val → property last.val := by
  cases operation <;> simp_all [liftAction, RegexRankedObservation.actionTargets]
  all_goals rcases edge with rfl | rfl <;> simp_all

theorem layer_preserves_slot {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (slot : Fin groups)
    (unwritten : Unwritten code slot) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length)
    (recursive : ∀ entry call, PreservesSlot slot (recurse entry call)) :
    PreservesSlot slot (layer interpretation input code root recurse) := by
  intro direction eligible position captures winner returned
  let first : Licensed code length root := ⟨⟨root, position, captures⟩, .refl⟩
  let step := fun state => liftAction (controlAction interpretation input direction code root recurse state)
    (control_targets interpretation input direction code root recurse state)
  have closed : ∀ source target, target ∈ RegexRankedObservation.actionTargets (step source) →
      source.val.captures slot = captures slot → target.val.captures slot = captures slot := by
    intro source target edge valid
    exact liftAction_preserves _ _ source target (fun state => state.captures slot = captures slot)
      (by intro last lastEdge same
          exact (control_preserves_slot interpretation input direction code slot unwritten root
            recurse recursive source last lastEdge).trans same) edge valid
  obtain ⟨last, equal, valid⟩ := complete_preserves code root step
    (fun state => state.val.captures slot = captures slot) closed eligible first winner rfl returned
  simpa [equal] using valid

/-- Complete canonical execution retains every slot that has no capture-write
instruction anywhere in the graph. Nested observations are handled by genuine
well-founded induction on the intrinsic body-call relation. -/
theorem evaluate_preserves_slot {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (certificate : Certificate code)
    (slot : Fin groups) (unwritten : Unwritten code slot) (root : Fin states) :
    PreservesSlot slot (evaluate interpretation input code certificate root) := by
  induction root using (calls_wellFounded certificate).induction with
  | h root ih =>
      rw [evaluate_equation]
      exact layer_preserves_slot interpretation input code slot unwritten root _ ih

theorem unused_unmatched_remains_unmatched {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (certificate : Certificate code)
    (slot : Fin groups) (unwritten : Unwritten code slot) (root : Fin states)
    (direction : Direction) (eligible : Configuration states groups length → Bool)
    (position : Fin (length + 1)) (captures : Captures groups length)
    (initially : captures slot = .unmatched) (winner : Winner states groups length)
    (returned : evaluate interpretation input code certificate root direction eligible position captures = some winner) :
    winner.configuration.captures slot = .unmatched :=
  (evaluate_preserves_slot interpretation input code certificate slot unwritten root
    direction eligible position captures winner returned).trans initially

namespace Controls

private def observationCode (pc : Fin 3) : Instruction 3 1 :=
  if pc = 0 then .look .ahead 1 2 else .accept

private def observationCertificate : Certificate observationCode where
  rank := fun pc => if pc = 0 then 1 else 0
  ordinary := by
    intro pc next edge
    by_cases initial : pc = 0
    · subst pc
      simp [observationCode, ordinaryTargets] at edge
      subst next
      decide
    · simp [observationCode, initial, ordinaryTargets] at edge
  body := by
    intro pc kind entry next equation
    by_cases initial : pc = 0
    · subst pc
      simp only [observationCode] at equation
      obtain ⟨rfl, rfl, rfl⟩ := equation
      decide
    · simp [observationCode, initial] at equation

private theorem observationCode_unwritten : Unwritten observationCode 0 := by
  intro pc
  by_cases initial : pc = 0 <;> simp [observationCode, initial]

theorem nested_observation_retains_reserved_unmatched_slot {length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (direction : Direction) (eligible : Configuration 3 1 length → Bool)
    (position : Fin (length + 1)) (winner : Winner 3 1 length)
    (returned : evaluate interpretation input observationCode observationCertificate 0
      direction eligible position (fun _ => .unmatched) = some winner) :
    winner.configuration.captures 0 = .unmatched :=
  unused_unmatched_remains_unmatched interpretation input observationCode observationCertificate
    0 observationCode_unwritten 0 direction eligible position (fun _ => .unmatched) rfl winner returned

private def readOnlyCode (pc : Fin 2) : Instruction 2 1 :=
  if pc = 0 then .backref 0 .exact 1 else .accept

private def readOnlyCertificate : Certificate readOnlyCode where
  rank := fun _ => 0
  ordinary := by intros; exact le_refl 0
  body := by
    intro pc kind entry next equation
    by_cases initial : pc = 0 <;> simp [readOnlyCode, initial] at equation

private theorem readOnlyCode_unwritten : Unwritten readOnlyCode 0 := by
  intro pc
  by_cases initial : pc = 0 <;> simp [readOnlyCode, initial]

theorem reading_capture_does_not_destroy_its_retained_value {length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (direction : Direction) (eligible : Configuration 2 1 length → Bool)
    (position first last : Fin (length + 1)) (winner : Winner 2 1 length)
    (returned : evaluate interpretation input readOnlyCode readOnlyCertificate 0
      direction eligible position (fun _ => .closed first last) = some winner) :
    winner.configuration.captures 0 = .closed first last :=
  evaluate_preserves_slot interpretation input readOnlyCode readOnlyCertificate 0
    readOnlyCode_unwritten 0 direction eligible position _ winner returned

theorem capture_writer_does_not_satisfy_unused_slot_premise :
    ¬ Unwritten (fun _ : Fin 1 => (Instruction.open 0 0 : Instruction 1 1)) 0 := by
  intro unwritten
  exact unwritten 0 rfl

end Controls

end Mettapedia.GSLT.LanguageDef.RegexObservationInvariant
