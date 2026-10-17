import Mettapedia.GSLT.LanguageDef.RegexSourceCorrespondence
import Mettapedia.Computability.RegularLanguages.RegexUniformFutures
import Mettapedia.Computability.RegularLanguages.RegexPublicSearch

/-!
# Capture boundaries and public observations

A fragment's emitted control flow can leave its owned region only through its
supplied continuation. Capture bodies therefore have their closing save as a
postdominator on completed executions. The public adapter reserves group zero
for the selected whole span, independently of user capture slots.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.CaptureObservation

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open OrderedGraphSearch (Point Probe successor)
open RegexSelectionCorrespondence (Action)

/-- A structural occurrence of a source fragment in the whole pattern. -/
inductive Fragment (whole : Pattern) : Pattern → Address → Address → Prop
  | root : Fragment whole whole .ending .root
  | seqLeft {first second continuation occurrence} : Fragment whole (.seq first second) continuation occurrence →
      Fragment whole first (.right occurrence) (.left occurrence)
  | seqRight {first second continuation occurrence} : Fragment whole (.seq first second) continuation occurrence →
      Fragment whole second continuation (.right occurrence)
  | altLeft {first second continuation occurrence} : Fragment whole (.alt first second) continuation occurrence →
      Fragment whole first continuation (.left occurrence)
  | altRight {first second continuation occurrence} : Fragment whole (.alt first second) continuation occurrence →
      Fragment whole second continuation (.right occurrence)
  | optional {body greedy continuation occurrence} : Fragment whole (.optional body greedy) continuation occurrence →
      Fragment whole body continuation (.body occurrence)
  | star {body greedy continuation occurrence} : Fragment whole (.star body greedy) continuation occurrence →
      Fragment whole body (.loop occurrence) (.body occurrence)
  | plus {body greedy continuation occurrence} : Fragment whole (.plus body greedy) continuation occurrence →
      Fragment whole body (.loop occurrence) (.body occurrence)
  | capture {group body continuation occurrence} : Fragment whole (.capture group body) continuation occurrence →
      Fragment whole body (.close occurrence) (.body occurrence)

theorem Fragment.rows {whole pattern : Pattern} {continuation occurrence : Address}
    (fragment : Fragment whole pattern continuation occurrence) :
    ∀ row ∈ emit pattern continuation occurrence, row ∈ (compile whole).rows := by
  induction fragment with
  | root => intro row member; simp [compile, member]
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih =>
      intro row member
      apply ih
      simp [emit, member]
  | optional _ ih | star _ ih | plus _ ih | capture _ ih =>
      intro row member
      apply ih
      simp [emit, member]

theorem Fragment.within {whole pattern : Pattern} {continuation occurrence : Address}
    (fragment : Fragment whole pattern continuation occurrence) : Within .root occurrence := by
  induction fragment with
  | root => exact .refl _
  | seqLeft _ ih | altLeft _ ih => exact .left ih
  | seqRight _ ih | altRight _ ih => exact .right ih
  | optional _ ih | star _ ih | plus _ ih | capture _ ih => exact .body ih

def Region (pattern : Pattern) (continuation occurrence pc : Address) : Prop :=
  pc ∈ (emit pattern continuation occurrence).map Instruction.address

theorem Fragment.region_not_ending {whole pattern : Pattern} {continuation occurrence pc : Address}
    (fragment : Fragment whole pattern continuation occurrence) (member : Region pattern continuation occurrence pc) :
    pc ≠ .ending := by
  obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
  have inside := fragment.within.trans (emit_owned pattern continuation occurrence row rowMember)
  rw [same] at inside
  intro ended
  rw [ended] at inside
  cases inside

theorem Fragment.authorizes {whole pattern : Pattern} {continuation occurrence pc : Address}
    {operation : Source.Operation} (fragment : Fragment whole pattern continuation occurrence)
    (source : Source.At pattern continuation occurrence pc operation) : Source.Authorizes whole pc operation := by
  obtain ⟨row, member, same, interpreted⟩ := source.emitted
  exact (Source.authorizes_iff_compiled whole pc operation).mpr
    ⟨row, fragment.rows row member, same, interpreted⟩

def targets : Source.Operation → List Address
  | .accept _ | .dead => []
  | .jump target | .consume _ target | .assertion _ target | .save _ target => [target]
  | .choice first second => [first, second]

theorem targets_nodeOf (row : Instruction) : targets (Graph.nodeOf row id) = row.targets := by
  cases row <;> rfl

theorem perform_next_target {length : Nat} (probe : Probe Graph.CharacterClass String length)
    (operation : Source.Operation) (first target : Thread Address length)
    (step : Source.perform probe operation first = .next target) : target.point.1 ∈ targets operation := by
  cases operation <;> simp only [Source.perform] at step
  all_goals try { cases step }
  case jump next => cases step; simp [targets, Thread.at]
  case save slot next => cases step; simp [targets, Thread.saved, Thread.at]
  case consume class_ next =>
    split at step
    · cases advance : successor first.point.2 with
      | none => simp [advance] at step
      | some position => simp only [advance, Action.next.injEq] at step; subst target; simp [targets]
    · cases step
  case assertion assertion_ next =>
    split at step
    · cases step; simp [targets, Thread.at]
    · cases step

theorem perform_branch_targets {length : Nat} (probe : Probe Graph.CharacterClass String length)
    (operation : Source.Operation) (first left right : Thread Address length)
    (step : Source.perform probe operation first = .branch left right) :
    left.point.1 ∈ targets operation ∧ right.point.1 ∈ targets operation := by
  cases operation <;> simp only [Source.perform] at step
  all_goals try { cases step }
  case choice one two => cases step; simp [targets, Thread.branch, Thread.at]
  case consume class_ next =>
    split at step
    · cases advance : successor first.point.2 <;> simp [advance] at step
    · cases step
  case assertion assertion_ next => split at step <;> cases step

theorem Fragment.target_closed {whole pattern : Pattern} {continuation occurrence pc target : Address}
    {operation : Source.Operation} (fragment : Fragment whole pattern continuation occurrence)
    (member : Region pattern continuation occurrence pc) (authorized : Source.Authorizes whole pc operation)
    (edge : target ∈ targets operation) :
    target = continuation ∨ Region pattern continuation occurrence target := by
  obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
  have rowAuthorized : Source.Authorizes whole pc (Graph.nodeOf row id) :=
    (Source.authorizes_iff_compiled whole pc (Graph.nodeOf row id)).mpr
      ⟨row, fragment.rows row rowMember, same, rfl⟩
  have interpreted := Source.authorizes_unique whole pc operation (Graph.nodeOf row id) authorized rowAuthorized
  rw [interpreted, targets_nodeOf] at edge
  exact Graph.emit_targets_defined_or_continuation pattern continuation occurrence row rowMember target edge

theorem at_not_accept {pattern : Pattern} {continuation occurrence pc : Address}
    {operation : Source.Operation} (source : Source.At pattern continuation occurrence pc operation) :
    operation ≠ .accept () := by
  induction source <;> simp_all [Source.ordered]
  all_goals split <;> simp

theorem accepts_only_ending {pattern : Pattern} {pc : Address}
    (source : Source.Authorizes pattern pc (.accept ())) : pc = .ending := by
  cases source with
  | finish => rfl
  | inside operation => exact False.elim (at_not_accept operation rfl)

theorem perform_accept_operation {length : Nat} (probe : Probe Graph.CharacterClass String length)
    (operation : Source.Operation) (thread : Thread Address length)
    (step : Source.perform probe operation thread = .accept ()) : operation = .accept () := by
  cases operation <;> simp only [Source.perform] at step
  all_goals try { cases step }
  case accept tag => cases tag; rfl
  case consume class_ next =>
    split at step
    · cases advance : successor thread.point.2 <;> simp [advance] at step
    · cases step
  case assertion assertion_ next => split at step <;> cases step

theorem SourceTrace_first_mem {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread Address length} {code : List Bool} {points : List (Point Address length)}
    (trace : Source.Trace pattern probe eligible first code points last) : first.point ∈ points := by
  cases trace <;> simp

/-- A completed execution beginning inside an actual source fragment must
visit its continuation. It cannot jump to a different enclosing region. -/
theorem Fragment.continuation_visited {whole pattern : Pattern} {continuation occurrence : Address}
    (fragment : Fragment whole pattern continuation occurrence) {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread Address length} {code : List Bool} {points : List (Point Address length)}
    (trace : Source.Trace whole probe eligible first code points last)
    (inside : Region pattern continuation occurrence first.point.1) :
    ∃ point ∈ points, point.1 = continuation := by
  induction trace with
  | done acted allowed =>
      obtain ⟨operation, authorized, performed⟩ := acted
      have ended := accepts_only_ending (perform_accept_operation probe operation _ performed ▸ authorized)
      exact False.elim (fragment.region_not_ending inside ended)
  | @next first target code points last acted trace ih =>
      obtain ⟨operation, authorized, performed⟩ := acted
      rcases fragment.target_closed inside authorized (perform_next_target probe operation first target performed) with same | member
      · exact ⟨target.point, by simp [SourceTrace_first_mem trace], same⟩
      · obtain ⟨point, member, same⟩ := ih member
        exact ⟨point, by simp [member], same⟩
  | @left first left right code points last acted trace ih =>
      obtain ⟨operation, authorized, performed⟩ := acted
      have edges := perform_branch_targets probe operation first left right performed
      rcases fragment.target_closed inside authorized edges.1 with same | member
      · exact ⟨left.point, by simp [SourceTrace_first_mem trace], same⟩
      · obtain ⟨point, member, same⟩ := ih member
        exact ⟨point, by simp [member], same⟩
  | @right first left right code points last acted trace ih =>
      obtain ⟨operation, authorized, performed⟩ := acted
      have edges := perform_branch_targets probe operation first left right performed
      rcases fragment.target_closed inside authorized edges.2 with same | member
      · exact ⟨right.point, by simp [SourceTrace_first_mem trace], same⟩
      · obtain ⟨point, member, same⟩ := ih member
        exact ⟨point, by simp [member], same⟩

theorem open_fragment {pattern : Pattern} {continuation occurrence pc : Address}
    {operation : Source.Operation} (source : Source.At pattern continuation occurrence pc operation) :
    ∀ (whole : Pattern) (_fragment : Fragment whole pattern continuation occurrence) (group : Nat) (target : Address),
      operation = .save (2 * group) target →
        ∃ body outer base, Fragment whole (.capture group body) outer base ∧ pc = base ∧ target = .body base := by
  induction source with
  | zero | epsilon | literal | any | class_ | assertion | seqEntry | altEntry | plusEntry =>
      intros; contradiction
  | optionalEntry body greedy continuation occurrence | starEntry body greedy continuation occurrence | starRepeat body greedy continuation occurrence | plusRepeat body greedy continuation occurrence =>
      intro whole _fragment group target same
      cases greedy <;> simp [Source.ordered] at same
  | seqLeft _ ih =>
      intro whole fragment group target same
      exact ih whole (.seqLeft fragment) group target same
  | seqRight _ ih =>
      intro whole fragment group target same
      exact ih whole (.seqRight fragment) group target same
  | altLeft _ ih =>
      intro whole fragment group target same
      exact ih whole (.altLeft fragment) group target same
  | altRight _ ih =>
      intro whole fragment group target same
      exact ih whole (.altRight fragment) group target same
  | optionalBody _ ih =>
      intro whole fragment group target same
      exact ih whole (.optional fragment) group target same
  | starBody _ ih =>
      intro whole fragment group target same
      exact ih whole (.star fragment) group target same
  | plusBody _ ih =>
      intro whole fragment group target same
      exact ih whole (.plus fragment) group target same
  | captureBody _ ih =>
      intro whole fragment group target same
      exact ih whole (.capture fragment) group target same
  | captureEntry original body continuation occurrence =>
      intro whole fragment group target same
      simp only [Graph.captureSlot, Node.save.injEq] at same
      have equal : original = group := by omega
      subst original
      exact ⟨body, continuation, occurrence, fragment, rfl, same.2.symm⟩
  | captureClose original body continuation occurrence =>
      intro whole fragment group target same
      simp only [Graph.captureSlot, Node.save.injEq] at same
      omega

theorem authorized_open_fragment {whole : Pattern} {pc target : Address} {group : Nat}
    (authorized : Source.Authorizes whole pc (.save (2 * group) target)) :
    ∃ body outer base, Fragment whole (.capture group body) outer base ∧ pc = base ∧ target = .body base := by
  cases authorized with
  | inside source => exact open_fragment source whole .root group target rfl

/-- Every completed suffix after an opening save visits that occurrence's
closing save. This remains true with nullable loops and reused group IDs. -/
theorem close_visited_after_open {whole : Pattern} {pc target : Address} {group : Nat}
    (authorized : Source.Authorizes whole pc (.save (2 * group) target)) {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread Address length} {code : List Bool} {points : List (Point Address length)}
    (trace : Source.Trace whole probe eligible first code points last) (entered : first.point.1 = target) :
    ∃ point ∈ points, ∃ after, Source.Authorizes whole point.1 (.save (2 * group + 1) after) := by
  obtain ⟨body, outer, base, occurrence, _, targetSame⟩ := authorized_open_fragment authorized
  have inside : Region body (.close base) (.body base) first.point.1 := by
    rw [entered, targetSame]
    exact Graph.emit_entry_present body (.close base) (.body base)
  obtain ⟨point, member, exited⟩ := (Fragment.capture occurrence).continuation_visited trace inside
  refine ⟨point, member, outer, ?_⟩
  rw [exited]
  exact occurrence.authorizes (Source.At.captureClose group body outer base)

theorem edge_position {State Class Assertion Tag : Type} {length : Nat}
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (first after : Thread State length) (edge : after ∈ edges graph probe first) :
    first.point.2.val ≤ after.point.2.val := by
  cases node : graph first.point.1 <;> simp only [edges, node] at edge
  all_goals try { simp at edge }
  all_goals try { simp only [List.mem_singleton] at edge; subst after; exact le_rfl }
  case choice left right =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at edge
    rcases edge with same | same <;> subst after <;> exact le_rfl
  case consume class_ next =>
    split at edge
    · cases advance : successor first.point.2 with
      | none => simp [advance] at edge
      | some position =>
          simp only [advance, List.mem_singleton] at edge
          subst after
          have moved := OrderedGraphSearch.successor_advances advance
          dsimp
          omega
    · simp at edge
  case assertion assertion_ next =>
    split at edge
    · simp only [List.mem_singleton] at edge
      subst after
      exact le_rfl
    · simp at edge

theorem trace_positions_after {State Class Assertion Tag : Type} {length : Nat}
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Thread State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : RegexSelectionCorrespondence.Trace graph probe eligible first code points last tag) :
    ∀ point ∈ points, first.point.2.val ≤ point.2.val := by
  induction trace with
  | done accepted allowed =>
      intro point member
      simp only [List.mem_singleton] at member
      subst point
      exact le_rfl
  | @next first target code points last tag step trace ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact le_rfl
      · exact (edge_position graph probe first target
          (RegexSelectionCorrespondence.action_next_edge graph probe first target step).1).trans (ih point member)
  | @left first left right code points last tag step trace ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact le_rfl
      · exact (edge_position graph probe first left
          (RegexSelectionCorrespondence.action_branch_edges graph probe first left right step).1).trans (ih point member)
  | @right first left right code points last tag step trace ih =>
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact le_rfl
      · exact (edge_position graph probe first right
          (RegexSelectionCorrespondence.action_branch_edges graph probe first left right step).2.1).trans (ih point member)

/-- The continuation postdominator yields a real later save event in the
actual compiled graph's execution log, not just a matching source label. -/
theorem compiled_open_has_later_finish {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first after last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)}
    (group : Nat) (target : Graph.Owned (compile pattern))
    (node : Source.compiledGraph pattern first.point.1 = .save (2 * group) target)
    (step : RegexSelectionCorrespondence.action (Source.compiledGraph pattern) probe first = .next after)
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) after code points last ()) :
    ∃ event ∈ RegexUniformFutures.events (Source.compiledGraph pattern) points,
      event.slot = 2 * group + 1 ∧ first.point.2.val ≤ event.position.val := by
  have authorized : Source.Authorizes pattern first.point.1.val (.save (2 * group) target.val) := by
    have actual := Source.checkedGraph_source pattern first.point.1
    change Source.Authorizes pattern first.point.1.val
      (Graph.mapNode Subtype.val (Source.compiledGraph pattern first.point.1)) at actual
    simpa only [node, Graph.mapNode] using actual
  have sourceTrace := Source.compiled_trace_source trace
  have afterSame : after = first.saved target (2 * group) := by
    simpa [RegexSelectionCorrespondence.action, node] using step.symm
  obtain ⟨point, member, closeAddress, closeAuthorized⟩ := close_visited_after_open authorized sourceTrace (by
    simp [afterSame, Source.view, Source.mapThread, Thread.saved, Thread.at])
  obtain ⟨actual, actualMember, same⟩ := List.mem_map.mp member
  have authorizedActual := Source.checkedGraph_source pattern actual.1
  have instruction : Graph.mapNode Subtype.val (Source.compiledGraph pattern actual.1) =
      .save (2 * group + 1) closeAddress := by
    apply Source.authorizes_unique pattern actual.1.val _ _ authorizedActual
    have pcSame : actual.1.val = point.1 := congrArg Prod.fst same
    simpa only [← pcSame] using closeAuthorized
  have finishEvent : ⟨2 * group + 1, actual.2⟩ ∈
      RegexUniformFutures.eventAt (Source.compiledGraph pattern) actual := by
    cases observed : Source.compiledGraph pattern actual.1 <;> simp [observed, Graph.mapNode] at instruction
    rename_i slot next
    obtain ⟨sameSlot, _⟩ := instruction
    simp [RegexUniformFutures.eventAt, observed, sameSlot]
  refine ⟨⟨2 * group + 1, actual.2⟩,
    List.mem_flatMap.mpr ⟨actual, actualMember, finishEvent⟩, rfl, ?_⟩
  have positions := trace_positions_after trace actual actualMember
  simpa [afterSame, Thread.saved, Thread.at] using positions

open RegexUniformFutures (CaptureEvent events eventAt lastWrite replay)

/-- Every opening occurrence in the log has a later closing occurrence for
the same group, at a position no earlier than the opening. -/
inductive Closed {length : Nat} : List (CaptureEvent length) → Prop
  | nil : Closed []
  | cons {event later} : Closed later →
      (∀ group, event.slot = 2 * group →
        ∃ closing ∈ later, closing.slot = 2 * group + 1 ∧ event.position.val ≤ closing.position.val) →
      Closed (event :: later)

theorem compiled_events_closed {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)} {tag : Unit}
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last tag) : Closed (events (Source.compiledGraph pattern) points) := by
  induction trace with
  | done accepted allowed =>
      simpa [events, RegexUniformFutures.action_accept_no_event _ _ _ _ accepted] using (Closed.nil (length := length))
  | @next first after code points last tag step trace ih =>
      cases tag
      rw [RegexUniformFutures.events_cons]
      cases node : Source.compiledGraph pattern first.point.1
      all_goals try { simpa [eventAt, node] using ih }
      rename_i slot target
      simp only [eventAt, node, List.singleton_append]
      apply Closed.cons ih
      intro group same
      dsimp at same
      subst slot
      exact compiled_open_has_later_finish group target node step trace
  | left step trace ih =>
      have noEvent := (RegexUniformFutures.action_branch_data _ _ step).1
      simpa [RegexUniformFutures.events_cons, noEvent] using ih
  | right step trace ih =>
      have noEvent := (RegexUniformFutures.action_branch_data _ _ step).1
      simpa [RegexUniformFutures.events_cons, noEvent] using ih

theorem events_positions_after {State Class Assertion Tag : Type} {length : Nat}
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Thread State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : RegexSelectionCorrespondence.Trace graph probe eligible first code points last tag) :
    ∀ event ∈ events graph points, first.point.2.val ≤ event.position.val := by
  intro event member
  obtain ⟨point, pointMember, eventMember⟩ := List.mem_flatMap.mp member
  have same : event.position = point.2 := by
    cases node : graph point.1 <;> simp only [eventAt, node] at eventMember
    all_goals try { simp at eventMember }
    simp only [List.mem_singleton] at eventMember
    subst event
    rfl
  rw [same]
  exact trace_positions_after trace point pointMember

theorem events_positions_ordered {State Class Assertion Tag : Type} {length : Nat}
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Thread State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : RegexSelectionCorrespondence.Trace graph probe eligible first code points last tag) :
    (events graph points).Pairwise (fun first second => first.position.val ≤ second.position.val) := by
  induction trace with
  | done accepted allowed => simp [events, RegexUniformFutures.action_accept_no_event _ _ _ _ accepted]
  | @next first after code points last tag step trace ih =>
      rw [RegexUniformFutures.events_cons]
      cases node : graph first.point.1
      all_goals try { simpa [eventAt, node] using ih }
      rename_i slot target
      simp only [eventAt, node, List.singleton_append, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro event member
      exact (edge_position graph probe first after
        (RegexSelectionCorrespondence.action_next_edge graph probe first after step).1).trans
          (events_positions_after trace event member)
  | left step trace ih =>
      have noEvent := (RegexUniformFutures.action_branch_data _ _ step).1
      simpa [RegexUniformFutures.events_cons, noEvent] using ih
  | right step trace ih =>
      have noEvent := (RegexUniformFutures.action_branch_data _ _ step).1
      simpa [RegexUniformFutures.events_cons, noEvent] using ih

theorem lastWrite_mem {length : Nat} (log : List (CaptureEvent length)) (slot : Nat)
    (position : Fin (length + 1)) (written : lastWrite log slot = some position) :
    ∃ event ∈ log, event.slot = slot ∧ event.position = position := by
  induction log with
  | nil => simp [lastWrite] at written
  | cons event later ih =>
      cases latest : lastWrite later slot with
      | some found =>
          simp [lastWrite, latest] at written
          subst found
          obtain ⟨found, member, same⟩ := ih latest
          exact ⟨found, by simp [member], same⟩
      | none =>
          by_cases same : event.slot = slot
          · simp [lastWrite, latest, same] at written
            exact ⟨event, by simp, same, written⟩
          · simp [lastWrite, latest, same] at written

theorem lastWrite_max {length : Nat} (log : List (CaptureEvent length))
    (ordered : log.Pairwise (fun first second => first.position.val ≤ second.position.val)) :
    ∀ event ∈ log, ∀ slot, event.slot = slot →
      ∃ position, lastWrite log slot = some position ∧ event.position.val ≤ position.val := by
  induction log with
  | nil => simp
  | cons head later ih =>
      obtain ⟨before, ordered⟩ := List.pairwise_cons.mp ordered
      intro event member slot sameSlot
      rcases List.mem_cons.mp member with same | member
      · subst event
        cases latest : lastWrite later slot with
        | none => exact ⟨head.position, by simp [lastWrite, latest, sameSlot], le_rfl⟩
        | some position =>
            obtain ⟨found, member, _, same⟩ := lastWrite_mem later slot position latest
            exact ⟨position, by simp [lastWrite, latest], same ▸ before found member⟩
      · obtain ⟨position, latest, after⟩ := ih ordered event member slot sameSlot
        exact ⟨position, by simp [lastWrite, latest], after⟩

theorem Closed.finish_exists {length : Nat} {log : List (CaptureEvent length)} (closed : Closed log) :
    ∀ event ∈ log, ∀ group, event.slot = 2 * group →
      ∃ closing ∈ log, closing.slot = 2 * group + 1 ∧ event.position.val ≤ closing.position.val := by
  induction closed with
  | nil => simp
  | @cons head later closed paired ih =>
      intro event member group sameSlot
      rcases List.mem_cons.mp member with same | member
      · subst event
        obtain ⟨closing, member, same, bound⟩ := paired group sameSlot
        exact ⟨closing, by simp [member], same, bound⟩
      · obtain ⟨closing, member, same, bound⟩ := ih event member group sameSlot
        exact ⟨closing, by simp [member], same, bound⟩

/-- A completed capture has a closing boundary at or after its latest open.
The theorem derives this from real event order and closing postdomination. -/
theorem closed_replay_pair {length : Nat} (log : List (CaptureEvent length)) (closed : Closed log)
    (ordered : log.Pairwise (fun first second => first.position.val ≤ second.position.val))
    (initial : Registers length) (group : Nat) (empty : initial (2 * group) = none)
    (position : Fin (length + 1)) (opened : replay log initial (2 * group) = some position) :
    ∃ closing, replay log initial (2 * group + 1) = some closing ∧ position.val ≤ closing.val := by
  have latest : lastWrite log (2 * group) = some position := by
    simpa [RegexUniformFutures.replay_slot, empty] using opened
  obtain ⟨event, member, sameSlot, samePosition⟩ := lastWrite_mem log (2 * group) position latest
  obtain ⟨closing, closingMember, closingSlot, after⟩ := closed.finish_exists event member group sameSlot
  obtain ⟨final, finalWrite, finalAfter⟩ := lastWrite_max log ordered closing closingMember (2 * group + 1) closingSlot
  refine ⟨final, ?_, ?_⟩
  · simp [RegexUniformFutures.replay_slot, finalWrite]
  · rw [samePosition] at after
    exact after.trans finalAfter

open RegexMatchObservations (Span Observation)

/-- Missing endpoints denote nonparticipation. An inverted pair is not
filtered out or silently repaired by this adapter. -/
def captureSpan {length : Nat} (registers : Registers length) (group : Nat) : Option Span :=
  match registers (2 * group), registers (2 * group + 1) with
  | some first, some last => some ⟨first.val, last.val⟩
  | _, _ => none

theorem compiled_captureSpan_valid {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)}
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last ())
    (group : Nat) (empty : first.registers (2 * group) = none) :
    ∀ span, captureSpan last.registers group = some span → span.Valid length := by
  intro span participated
  have replayed := RegexUniformFutures.Trace.capture_replay trace
  cases opened : last.registers (2 * group) with
  | none => simp [captureSpan, opened] at participated
  | some position =>
      have openedReplay : replay (events (Source.compiledGraph pattern) points) first.registers (2 * group) = some position := by
        rw [← replayed]
        exact opened
      obtain ⟨closing, closed, ordered⟩ := closed_replay_pair
        (events (Source.compiledGraph pattern) points) (compiled_events_closed trace)
        (events_positions_ordered trace) first.registers group empty position openedReplay
      have closingValue : last.registers (2 * group + 1) = some closing := by
        rw [replayed]
        exact closed
      simp only [captureSpan, opened, closingValue, Option.some.injEq] at participated
      subst span
      exact ⟨ordered, Nat.lt_succ_iff.mp closing.isLt⟩

theorem trace_last_mem {State Class Assertion Tag : Type} {length : Nat}
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Thread State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : RegexSelectionCorrespondence.Trace graph probe eligible first code points last tag) :
    last.point ∈ points := by
  induction trace with
  | done _ _ => simp
  | next _ _ ih | left _ _ ih | right _ _ ih => simp [ih]

/-- Group zero is the whole selected span and is not read from user registers.
Native constructed-pattern admission separately excludes user group zero. -/
def observe {State : Type} {length : Nat} (start : Fin (length + 1))
    (last : Thread State length) (groupCount : Nat) : Observation :=
  let whole : Span := ⟨start.val, last.point.2.val⟩
  ⟨whole, (List.range groupCount).map (fun group =>
    if group = 0 then some whole else captureSpan last.registers group), last.choices⟩

theorem observe_layout_length {State : Type} {length : Nat} (start : Fin (length + 1))
    (last : Thread State length) (groupCount : Nat) : (observe start last groupCount).captures.length = groupCount := by
  simp [observe]

theorem observe_group_zero {State : Type} {length : Nat} (start : Fin (length + 1))
    (last : Thread State length) (groupCount : Nat) (present : 0 < groupCount) :
    (observe start last groupCount).captures[0]? = some (some ⟨start.val, last.point.2.val⟩) := by
  cases groupCount with
  | zero => omega
  | succ count => simp [observe, List.range_succ_eq_map]

theorem compiled_observation_valid {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)}
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last ())
    (initialUserEmpty : ∀ group, 0 < group → first.registers (2 * group) = none)
    (groupCount : Nat) : (observe first.point.2 last groupCount).Valid length := by
  have wholeValid : (⟨first.point.2.val, last.point.2.val⟩ : Span).Valid length :=
    ⟨trace_positions_after trace last.point (trace_last_mem trace), Nat.lt_succ_iff.mp last.point.2.isLt⟩
  refine ⟨wholeValid, ?_⟩
  intro capture member span same
  obtain ⟨group, _, equal⟩ := List.mem_map.mp member
  have actual := equal.trans same
  by_cases zero : group = 0
  · simp only [zero, ↓reduceIte, Option.some.injEq] at actual
    rw [← actual]
    exact wholeValid
  · have participated : captureSpan last.registers group = some span := by simpa [zero] using actual
    exact compiled_captureSpan_valid trace group (initialUserEmpty group (by omega)) span participated

/-- This is the native whole-match initial convention, not a source capture
declaration. Interior capture registers start unresolved. -/
def initialRegisters {length : Nat} (start : Fin (length + 1)) : Registers length :=
  write (fun _ => none) 0 start

theorem initialRegisters_user_empty {length : Nat} (start : Fin (length + 1)) (group : Nat)
    (positive : 0 < group) : initialRegisters start (2 * group) = none := by
  simp [initialRegisters, write, show 2 * group ≠ 0 by omega]

/-- Actual compiled executions from the native-style initial snapshot have
valid scalar spans without checking, dropping, or sorting their endpoints. -/
theorem native_style_observation_valid {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)}
    (initial : first.registers = initialRegisters first.point.2)
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last ()) (groupCount : Nat) :
    (observe first.point.2 last groupCount).Valid length := by
  apply compiled_observation_valid trace
  intro group positive
  rw [initial]
  exact initialRegisters_user_empty first.point.2 group positive

theorem native_style_byte_observation_valid {pattern : Pattern} {input : List Char}
    {probe : Probe Graph.CharacterClass String input.length} {eligible : Thread Address input.length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) input.length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) input.length)}
    (initial : first.registers = initialRegisters first.point.2)
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last ()) (groupCount : Nat) :
    (RegexPublicSearch.byteObservation input (observe first.point.2 last groupCount)).Valid (utf8Length input) :=
  RegexPublicSearch.byteObservation_valid input _ (native_style_observation_valid initial trace groupCount)

theorem at_save_group {pattern : Pattern} {continuation occurrence pc : Address} {operation : Source.Operation}
    (source : Source.At pattern continuation occurrence pc operation) :
    ∀ slot target, operation = .save slot target →
      ∃ group ∈ captureGroups pattern, slot = 2 * group ∨ slot = 2 * group + 1 := by
  induction source with
  | zero | epsilon | literal | any | class_ | assertion | seqEntry | altEntry | plusEntry =>
      intros; contradiction
  | optionalEntry body greedy continuation occurrence | starEntry body greedy continuation occurrence | starRepeat body greedy continuation occurrence | plusRepeat body greedy continuation occurrence =>
      intro slot target same
      cases greedy <;> simp [Source.ordered] at same
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih =>
      intro slot target same
      obtain ⟨group, member, same⟩ := ih slot target same
      exact ⟨group, by simp [captureGroups, member], same⟩
  | optionalBody _ ih | starBody _ ih | plusBody _ ih => exact ih
  | captureBody _ ih =>
      intro slot target same
      obtain ⟨group, member, same⟩ := ih slot target same
      exact ⟨group, by simp [captureGroups, member], same⟩
  | captureEntry group body continuation occurrence =>
      intro slot target same
      simp only [Node.save.injEq, Graph.captureSlot] at same
      exact ⟨group, by simp [captureGroups], Or.inl same.1.symm⟩
  | captureClose group body continuation occurrence =>
      intro slot target same
      simp only [Node.save.injEq, Graph.captureSlot] at same
      exact ⟨group, by simp [captureGroups], Or.inr same.1.symm⟩

/-- The positive-ID admission condition is the semantic counterpart of the
native pattern/SAVE-row checks reserving group zero. It is not a new GSLT
constructor restriction: the native library's whole-match profile uses it. -/
def PositiveGroups (pattern : Pattern) : Prop := ∀ group ∈ captureGroups pattern, 0 < group

theorem source_saves_user_slots {pattern : Pattern} (positive : PositiveGroups pattern)
    {pc target : Address} {slot : Nat} (source : Source.Authorizes pattern pc (.save slot target)) : 2 ≤ slot := by
  cases source with
  | inside source =>
      obtain ⟨group, member, same | same⟩ := at_save_group source slot target rfl
      · have greater := positive group member; omega
      · have greater := positive group member; omega

theorem compiled_events_user_slots {pattern : Pattern} {length : Nat} (positive : PositiveGroups pattern)
    (points : List (Point (Graph.Owned (compile pattern)) length)) :
    ∀ event ∈ events (Source.compiledGraph pattern) points, 2 ≤ event.slot := by
  intro event member
  obtain ⟨point, _, eventMember⟩ := List.mem_flatMap.mp member
  have authorized := Source.checkedGraph_source pattern point.1
  change Source.Authorizes pattern point.1.val (Graph.mapNode Subtype.val (Source.compiledGraph pattern point.1)) at authorized
  cases node : Source.compiledGraph pattern point.1 <;> simp only [eventAt, node] at eventMember
  all_goals try { simp at eventMember }
  simp only [List.mem_singleton] at eventMember
  subst event
  exact source_saves_user_slots positive (by simpa [node, Graph.mapNode] using authorized)

theorem compiled_whole_slots_untouched {pattern : Pattern} {length : Nat} (positive : PositiveGroups pattern)
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread (Graph.Owned (compile pattern)) length}
    {code : List Bool} {points : List (Point (Graph.Owned (compile pattern)) length)}
    (trace : RegexSelectionCorrespondence.Trace (Source.compiledGraph pattern) probe
      (eligible ∘ Source.view) first code points last ()) :
    last.registers 0 = first.registers 0 ∧ last.registers 1 = first.registers 1 := by
  rw [RegexUniformFutures.Trace.capture_replay trace]
  constructor
  all_goals
    apply RegexUniformFutures.replay_untouched
    intro event member
    have bound := compiled_events_user_slots positive points event member
    omega

namespace Controls

private def initial (pattern : Pattern) (length : Nat) : Thread (Graph.Owned (compile pattern)) length :=
  ⟨(⟨.root, by simpa [compile] using Graph.compile_entry_owned pattern⟩, 0), initialRegisters 0, []⟩

private def summary (pattern : Pattern) (length : Nat) (groupCount : Nat) :
    Option (Span × List (Option Span)) :=
  let probe : Probe Graph.CharacterClass String length := ⟨fun _ position => position.val < length, fun _ _ => false⟩
  match RegexMemoizedSearch.taggedSearch (Source.compiledGraph pattern) probe (fun _ => true) 100 (initial pattern length) with
  | .found last _ =>
      let observation := observe 0 last groupCount
      some (observation.span, observation.captures)
  | _ => none

theorem completed_empty_capture_is_participating :
    summary (.capture 1 .epsilon) 0 2 = some (⟨0, 0⟩, [some ⟨0, 0⟩, some ⟨0, 0⟩]) := by decide

theorem skipped_capture_is_not_an_empty_capture :
    summary (.optional (.capture 1 .epsilon) false) 0 2 = some (⟨0, 0⟩, [some ⟨0, 0⟩, none]) := by decide

theorem repeated_capture_uses_its_latest_paired_boundaries :
    summary (.plus (.capture 1 (.literal 97)) true) 2 2 =
      some (⟨0, 2⟩, [some ⟨0, 2⟩, some ⟨1, 2⟩]) := by decide

/-- The adapter does not repair invalid registers from arbitrary machines;
the source well-bracketing theorem is what excludes this case. -/
theorem arbitrary_registers_can_have_inverted_spans :
    let registers : Registers 2 := write (write (fun _ => none) 2 2) 3 1
    captureSpan registers 1 = some ⟨2, 1⟩ ∧ ¬ (⟨2, 1⟩ : Span).Valid 2 := by
  simp [captureSpan, write, Span.Valid]

theorem user_group_zero_fails_positive_id_admission : ¬ PositiveGroups (.capture 0 .epsilon) := by
  simp [PositiveGroups, captureGroups]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection.CaptureObservation
