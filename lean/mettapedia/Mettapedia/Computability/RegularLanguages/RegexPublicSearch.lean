import Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch
import Mettapedia.Computability.RegularLanguages.RegexIteration
import Mathlib.Data.List.FinRange

/-!
# Selected regex search across original-input starting positions

The semantic relation chooses the earliest admitted start, then the least
simple accepting execution at that start. The executable reference scans
original-input entries using the proved memoized graph search; it does not
slice the haystack or reset assertions. Its theorem is independent of the
native optimization that injects starts into one Pike frontier.

Full coverage is a terminal restriction on traces, before minimization.
The UTF-8 observation map retains participation and every capture boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPublicSearch

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe)

universe u v w z

section OrderedStarts

variable {Start : Type u} {Value : Type v} {Tag : Type w}

/-- The prefix contains no authorized answer, rather than merely no answer
returned by an implementation. Equal list elements retain their occurrences. -/
def First (accepts : Start → Value → Tag → Prop) (starts : List Start)
    (start : Start) (value : Value) (tag : Tag) : Prop :=
  ∃ before after, starts = before ++ start :: after ∧
    (∀ earlier ∈ before, ¬ ∃ answer label, accepts earlier answer label) ∧
    accepts start value tag

/-- An unfinished earlier attempt blocks later starts. A found earlier result
does not execute or depend on lower-priority attempts. -/
def scan (attempt : Start → RegexPikeVM.Result Value Tag) :
    List Start → RegexPikeVM.Result (Start × Value) Tag
  | [] => .finished none
  | start :: rest =>
      match attempt start with
      | .incomplete => .incomplete
      | .finished none => scan attempt rest
      | .finished (some (value, tag)) => .finished (some ((start, value), tag))

theorem first_cons (accepts : Start → Value → Tag → Prop) (head : Start)
    (rest : List Start) (start : Start) (value : Value) (tag : Tag) :
    First accepts (head :: rest) start value tag ↔
      (head = start ∧ accepts head value tag) ∨
      ((¬ ∃ answer label, accepts head answer label) ∧ First accepts rest start value tag) := by
  constructor
  · rintro ⟨before, after, same, absent, accepted⟩
    cases before with
    | nil =>
        have equal : head = start := by simpa using congrArg List.head? same
        exact Or.inl ⟨equal, equal ▸ accepted⟩
    | cons first before =>
        have equal : head = first := by simpa using congrArg List.head? same
        subst first
        refine Or.inr ⟨absent head (by simp), before, after, ?_, ?_, accepted⟩
        · simpa using congrArg List.tail same
        · intro earlier member
          exact absent earlier (by simp [member])
  · rintro (⟨same, accepted⟩ | ⟨absent, before, after, same, absentBefore, accepted⟩)
    · subst start
      exact ⟨[], rest, rfl, by simp, accepted⟩
    · refine ⟨head :: before, after, by simp [same], ?_, accepted⟩
      intro earlier member
      rcases List.mem_cons.mp member with same | member
      · simpa [same] using absent
      · exact absentBefore earlier member

/-- A compositional, two-sided theorem for an actual short-circuiting scan.
Its local contracts may be supplied by an independently justified realization. -/
theorem scan_found_iff (attempt : Start → RegexPikeVM.Result Value Tag)
    (accepts : Start → Value → Tag → Prop)
    (found : ∀ start value tag,
      attempt start = .finished (some (value, tag)) ↔ accepts start value tag)
    (absent : ∀ start, attempt start = .finished none ↔ ¬ ∃ value tag, accepts start value tag)
    (starts : List Start) (start : Start) (value : Value) (tag : Tag) :
    scan attempt starts = .finished (some ((start, value), tag)) ↔
      First accepts starts start value tag := by
  induction starts with
  | nil => simp [scan, First]
  | cons head rest ih =>
      rw [first_cons]
      cases result : attempt head with
      | incomplete =>
          have noAnswer : ∀ answer label, ¬ accepts head answer label := by
            intro answer label accepted
            have := (found head answer label).mpr accepted
            simp [result] at this
          have notAbsent : ¬ (¬ ∃ answer label, accepts head answer label) := by
            intro missing
            have := (absent head).mpr missing
            simp [result] at this
          exact False.elim (notAbsent (by rintro ⟨answer, label, accepted⟩; exact noAnswer answer label accepted))
      | finished selected =>
          cases selected with
          | none =>
              have missing := (absent head).mp result
              have noAnswer : ¬ accepts head value tag := by
                intro accepted; exact missing ⟨value, tag, accepted⟩
              simp [scan, result, missing, noAnswer, ih]
          | some pair =>
              obtain ⟨selected, label⟩ := pair
              have accepted := (found head selected label).mp result
              have notAbsent : ¬ (¬ ∃ answer label, accepts head answer label) := by
                intro missing; exact missing ⟨selected, label, accepted⟩
              have exactAnswer : accepts head value tag ↔ selected = value ∧ label = tag := by
                rw [← found head value tag, result]
                simp
              simp [scan, result, notAbsent, exactAnswer, and_assoc]

theorem scan_absent_iff (attempt : Start → RegexPikeVM.Result Value Tag)
    (accepts : Start → Value → Tag → Prop)
    (absent : ∀ start, attempt start = .finished none ↔ ¬ ∃ value tag, accepts start value tag)
    (starts : List Start) :
    scan attempt starts = .finished none ↔
      ∀ start ∈ starts, ¬ ∃ value tag, accepts start value tag := by
  induction starts with
  | nil => simp [scan]
  | cons start rest ih =>
      cases result : attempt start with
      | incomplete =>
          have notAbsent : ¬ (¬ ∃ value tag, accepts start value tag) := by
            intro missing
            have := (absent start).mpr missing
            simp [result] at this
          constructor
          · intro impossible; simp [scan, result] at impossible
          · intro all
            exact False.elim (notAbsent (all start (by simp)))
      | finished selected =>
          cases selected with
          | none =>
              rw [scan, result]
              rw [ih]
              constructor
              · intro all value member
                rcases List.mem_cons.mp member with same | member
                · subst value; exact (absent start).mp result
                · exact all value member
              · intro all value member
                exact all value (List.mem_cons_of_mem start member)
          | some pair =>
              have notAbsent : ¬ (¬ ∃ value tag, accepts start value tag) := by
                intro missing
                have := (absent start).mpr missing
                simp [result] at this
              constructor
              · intro impossible; simp [scan, result] at impossible
              · intro all
                exact False.elim (notAbsent (all start (by simp)))

theorem scan_ne_incomplete (attempt : Start → RegexPikeVM.Result Value Tag)
    (complete : ∀ start, attempt start ≠ .incomplete) (starts : List Start) :
    scan attempt starts ≠ .incomplete := by
  induction starts with
  | nil => simp [scan]
  | cons start rest ih =>
      cases result : attempt start with
      | incomplete => exact False.elim (complete start result)
      | finished selected => cases selected <;> simp [scan, result, ih]

end OrderedStarts

/-- On increasing original-input positions, the list-order specification is
exactly minimum successful start; preferred captures are chosen only inside
that start's independent selected execution. -/
theorem first_iff_minimal {length : Nat} {Value : Type u} {Tag : Type v}
    (accepts : Fin (length + 1) → Value → Tag → Prop)
    (starts : List (Fin (length + 1)))
    (ordered : starts.Pairwise (fun first second => first.val < second.val))
    (position : Fin (length + 1)) (value : Value) (tag : Tag) :
    First accepts starts position value tag ↔
      position ∈ starts ∧ accepts position value tag ∧
        ∀ earlier ∈ starts, earlier.val < position.val → ¬ ∃ answer label, accepts earlier answer label := by
  constructor
  · rintro ⟨before, after, same, missing, accepted⟩
    refine ⟨by simp [same], accepted, ?_⟩
    intro earlier member less
    rw [same] at member ordered
    have afterOrdered := (List.pairwise_append.mp ordered).2.1
    rcases List.mem_append.mp member with member | member
    · exact missing earlier member
    · rcases List.mem_cons.mp member with equal | member
      · subst earlier; omega
      · have greater := List.rel_of_pairwise_cons afterOrdered member
        omega
  · rintro ⟨member, accepted, missing⟩
    obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
    refine ⟨before, after, same, ?_, accepted⟩
    intro earlier member
    rw [same] at ordered
    have less := (List.pairwise_append.mp ordered).2.2 earlier member position (by simp)
    exact missing earlier (by simp [same, member]) less

/-- Entries enumerate scalar boundaries, including the final empty-match
position, while retaining the original input's assertion interpretation. -/
def positions (length minimum : Nat) : List (Fin (length + 1)) :=
  (List.finRange (length + 1)).filter (fun position => minimum ≤ position.val)

theorem mem_positions {length minimum : Nat} (position : Fin (length + 1)) :
    position ∈ positions length minimum ↔ minimum ≤ position.val := by
  simp [positions]

theorem positions_ordered (length minimum : Nat) :
    (positions length minimum).Pairwise (fun first second => first.val < second.val) := by
  apply List.Pairwise.filter
  rw [List.pairwise_iff_getElem]
  intro first second firstBound secondBound less
  simpa using less

section GraphSearch

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def entry (state : State) (position : Fin (length + 1)) : Thread State length :=
  ⟨(state, position), fun _ => none, []⟩

/-- Enough fuel is proved separately. Neither this wrapper nor the reference
installs a default native execution ceiling. -/
def anchored [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (fuel : Nat) (first : Thread State length) : RegexPikeVM.Result (Thread State length) Tag :=
  match RegexMemoizedSearch.taggedSearch graph probe eligible fuel first with
  | .incomplete => .incomplete
  | .absent _ => .finished none
  | .found last tag => .finished (some (last, tag))

def AcceptsAt (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (state : State) (position : Fin (length + 1)) (last : Thread State length) (tag : Tag) : Prop :=
  LeastSimple graph probe (fun thread => eligible thread.point) (entry state position) last ∧
    RegexPikeVM.terminal graph last = some tag

theorem anchored_found_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first last : Thread State length) (tag : Tag)
    (fuel : Nat) (enough : Fintype.card (Point State length) + 1 < fuel) :
    anchored graph probe eligible fuel first = .finished (some (last, tag)) ↔
      LeastSimple graph probe (fun thread => eligible thread.point) first last ∧
        RegexPikeVM.terminal graph last = some tag := by
  rw [← RegexMemoizedSearch.taggedSearch_leastSimple graph probe eligible first last tag fuel enough]
  cases result : RegexMemoizedSearch.taggedSearch graph probe eligible fuel first <;> simp [anchored, result]

theorem anchored_absent_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length)
    (fuel : Nat) (enough : Fintype.card (Point State length) + 1 < fuel) :
    anchored graph probe eligible fuel first = .finished none ↔
      ¬ ∃ last tag, LeastSimple graph probe (fun thread => eligible thread.point) first last ∧
        RegexPikeVM.terminal graph last = some tag := by
  have complete := RegexMemoizedSearch.taggedSearch_ne_incomplete graph probe eligible first fuel enough
  constructor
  · intro absent ⟨last, tag, least⟩
    have found := (anchored_found_iff graph probe eligible first last tag fuel enough).mpr least
    rw [absent] at found
    cases found
  · intro missing
    cases result : RegexMemoizedSearch.taggedSearch graph probe eligible fuel first with
    | incomplete => exact False.elim (complete result)
    | absent after => simp [anchored, result]
    | found last tag =>
        have least := (RegexMemoizedSearch.taggedSearch_leastSimple graph probe eligible first last tag
          fuel enough).mp result
        exact False.elim (missing ⟨last, tag, least⟩)

/-- The starts are supplied in priority order, not in backend discovery order.
The original probe is retained at every entry, including assertion context. -/
def search [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (state : State) (fuel : Nat) (starts : List (Fin (length + 1))) :
    RegexPikeVM.Result (Fin (length + 1) × Thread State length) Tag :=
  scan (fun position => anchored graph probe eligible fuel (entry state position)) starts

/-- Exact selected-capture correspondence for earliest-start search. Every
capture register is retained in `last`; no endpoint-only quotient is taken. -/
theorem search_found_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel)
    (starts : List (Fin (length + 1))) (position : Fin (length + 1))
    (last : Thread State length) (tag : Tag) :
    search graph probe eligible state fuel starts = .finished (some ((position, last), tag)) ↔
      First (AcceptsAt graph probe eligible state) starts position last tag := by
  apply scan_found_iff
  · intro start answer label
    exact anchored_found_iff graph probe eligible (entry state start) answer label fuel enough
  · intro start
    exact anchored_absent_iff graph probe eligible (entry state start) fuel enough

/-- Completed no-match excludes all finite accepting paths at every admitted
start, not only simple paths retained by the selected observer. -/
theorem search_absent_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel)
    (starts : List (Fin (length + 1))) :
    search graph probe eligible state fuel starts = .finished none ↔
      ∀ position ∈ starts, ¬ ∃ code points last tag,
        Trace graph probe (fun thread => eligible thread.point) (entry state position) code points last tag := by
  unfold search
  have localAbsent : ∀ position,
      anchored graph probe eligible fuel (entry state position) = .finished none ↔
        ¬ ∃ last tag, ∃ code points,
          Trace graph probe (fun thread => eligible thread.point) (entry state position) code points last tag := by
    intro position
    have raw := RegexMemoizedSearch.taggedSearch_absent_iff graph probe eligible
      (entry state position) fuel enough
    have wrapper : anchored graph probe eligible fuel (entry state position) = .finished none ↔
        ∃ after, RegexMemoizedSearch.taggedSearch graph probe eligible fuel
          (entry state position) = .absent after := by
      cases result : RegexMemoizedSearch.taggedSearch graph probe eligible fuel (entry state position) <;>
        simp [anchored, result]
    rw [wrapper, raw]
    constructor <;> intro missing witness <;> apply missing
    · obtain ⟨last, tag, code, points, trace⟩ := witness
      exact ⟨code, points, last, tag, trace⟩
    · obtain ⟨code, points, last, tag, trace⟩ := witness
      exact ⟨last, tag, code, points, trace⟩
  rw [scan_absent_iff _ (fun position last tag => ∃ code points,
    Trace graph probe (fun thread => eligible thread.point) (entry state position) code points last tag)
    localAbsent]
  constructor <;> intro missing position member witness <;> apply missing position member
  · obtain ⟨code, points, last, tag, trace⟩ := witness
    exact ⟨last, tag, code, points, trace⟩
  · obtain ⟨last, tag, code, points, trace⟩ := witness
    exact ⟨code, points, last, tag, trace⟩

theorem search_minimum_start [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel) (minimum : Nat)
    (position : Fin (length + 1)) (last : Thread State length) (tag : Tag) :
    search graph probe eligible state fuel (positions length minimum) =
        .finished (some ((position, last), tag)) ↔
      minimum ≤ position.val ∧ AcceptsAt graph probe eligible state position last tag ∧
        ∀ earlier : Fin (length + 1), minimum ≤ earlier.val → earlier.val < position.val →
          ¬ ∃ answer label, AcceptsAt graph probe eligible state earlier answer label := by
  rw [search_found_iff graph probe eligible state fuel enough,
    first_iff_minimal _ _ (positions_ordered length minimum)]
  simp only [mem_positions]

/-- Restricting eligibility affects only completed terminals. The same
actions, path code, capture updates and point history are retained. -/
theorem trace_restrict_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible extra : Thread State length → Bool)
    (first last : Thread State length) (code : List Bool) (points : List (Point State length)) (tag : Tag) :
    Trace graph probe (fun thread => eligible thread && extra thread) first code points last tag ↔
      Trace graph probe eligible first code points last tag ∧ extra last = true := by
  constructor
  · intro trace
    induction trace with
    | done accepted allowed =>
        obtain ⟨allowed, extra⟩ := Bool.and_eq_true_iff.mp allowed
        exact ⟨.done accepted allowed, extra⟩
    | next step _ ih => exact ⟨.next step ih.1, ih.2⟩
    | left step _ ih => exact ⟨.left step ih.1, ih.2⟩
    | right step _ ih => exact ⟨.right step ih.1, ih.2⟩
  · rintro ⟨trace, allowed⟩
    induction trace with
    | done accepted eligible => exact .done accepted (Bool.and_eq_true_iff.mpr ⟨eligible, allowed⟩)
    | next step _ ih => exact .next step (ih allowed)
    | left step _ ih => exact .left step (ih allowed)
    | right step _ ih => exact .right step (ih allowed)

/-- Full coverage changes the set of eligible paths before taking its
minimum, including when the preferred prefix is shorter than the input. -/
theorem least_restricted_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible extra : Thread State length → Bool)
    (first last : Thread State length) :
    LeastSimple graph probe (fun thread => eligible thread && extra thread) first last ↔
      ∃ code points tag, Trace graph probe eligible first code points last tag ∧
        extra last = true ∧ Simple points ∧
        ∀ otherCode otherPoints otherLast otherTag,
          Trace graph probe eligible first otherCode otherPoints otherLast otherTag →
          extra otherLast = true → Simple otherPoints →
            code = otherCode ∨ RegexMatchObservations.HigherPriority code otherCode := by
  constructor
  · rintro ⟨code, points, tag, trace, simple, least⟩
    obtain ⟨trace, allowed⟩ := (trace_restrict_iff graph probe eligible extra first last code points tag).mp trace
    refine ⟨code, points, tag, trace, allowed, simple, ?_⟩
    intro otherCode otherPoints otherLast otherTag trace allowed simple
    exact least _ _ _ _ ((trace_restrict_iff graph probe eligible extra first otherLast
      otherCode otherPoints otherTag).mpr ⟨trace, allowed⟩) simple
  · rintro ⟨code, points, tag, trace, allowed, simple, least⟩
    refine ⟨code, points, tag,
      (trace_restrict_iff graph probe eligible extra first last code points tag).mpr ⟨trace, allowed⟩,
      simple, ?_⟩
    intro otherCode otherPoints otherLast otherTag trace simple
    obtain ⟨trace, allowed⟩ := (trace_restrict_iff graph probe eligible extra first otherLast
      otherCode otherPoints otherTag).mp trace
    exact least _ _ _ _ trace allowed simple

end GraphSearch

section ByteObservation

open RegexMatchObservations (Observation Span)

def byteObservation (input : List Char) (observation : Observation) : Observation :=
  ⟨RegexIteration.byteSpan input observation.span,
    observation.captures.map (Option.map (RegexIteration.byteSpan input)), observation.priority⟩

theorem byteObservation_valid (input : List Char) (observation : Observation)
    (valid : observation.Valid input.length) :
    (byteObservation input observation).Valid (utf8Length input) := by
  refine ⟨RegexIteration.byteSpan_valid input observation.span valid.1, ?_⟩
  intro capture member span present
  obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
  have transformed : source.map (RegexIteration.byteSpan input) = some span := equal.trans present
  cases source with
  | none => simp at transformed
  | some source =>
      have equal := Option.some.inj transformed
      rw [← equal]
      exact RegexIteration.byteSpan_valid input source (valid.2 _ sourceMember _ rfl)

theorem byteSpan_injective (input : List Char) (first second : Span)
    (firstValid : first.Valid input.length) (secondValid : second.Valid input.length)
    (same : RegexIteration.byteSpan input first = RegexIteration.byteSpan input second) :
    first = second := by
  have starts : first.start = second.start := byteOffset_injective input
    (firstValid.1.trans firstValid.2) (secondValid.1.trans secondValid.2)
    (congrArg Span.start same)
  have stops : first.stop = second.stop := byteOffset_injective input firstValid.2 secondValid.2
    (congrArg Span.stop same)
  cases first; cases second; simp_all

theorem byteCaptures_injective (input : List Char) (first second : List (Option Span))
    (firstValid : ∀ capture ∈ first, ∀ span, capture = some span → span.Valid input.length)
    (secondValid : ∀ capture ∈ second, ∀ span, capture = some span → span.Valid input.length)
    (same : first.map (Option.map (RegexIteration.byteSpan input)) =
      second.map (Option.map (RegexIteration.byteSpan input))) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons first rest ih =>
      cases second with
      | nil => simp at same
      | cons second tail =>
          simp only [List.map_cons, List.cons.injEq] at same
          have head : first = second := by
            cases first with
            | none => cases second <;> simp_all
            | some first =>
                cases second with
                | none => simp at same
                | some second =>
                    apply congrArg some
                    exact byteSpan_injective input first second
                      (firstValid _ (by simp) _ rfl) (secondValid _ (by simp) _ rfl)
                      (Option.some.inj same.1)
          have tails := ih tail
            (fun capture member => firstValid capture (List.mem_cons_of_mem _ member))
            (fun capture member => secondValid capture (List.mem_cons_of_mem _ member)) same.2
          simp [head, tails]

/-- The public byte observation is faithful on valid observations: it cannot
identify different scalar captures, participation states, or priority paths. -/
theorem byteObservation_injective (input : List Char) (first second : Observation)
    (firstValid : first.Valid input.length) (secondValid : second.Valid input.length)
    (same : byteObservation input first = byteObservation input second) : first = second := by
  have spans := byteSpan_injective input first.span second.span firstValid.1 secondValid.1
    (congrArg Observation.span same)
  have captures := byteCaptures_injective input first.captures second.captures firstValid.2 secondValid.2
    (congrArg Observation.captures same)
  have priority : first.priority = second.priority := by
    simpa only [byteObservation] using congrArg Observation.priority same
  cases first; cases second; simp_all

end ByteObservation

namespace Controls

private def probe (input : List Nat) : Probe Nat Unit input.length :=
  ⟨fun wanted position => input[position.val]? == some wanted, fun _ position => position.val == 0⟩

private def alternatives : Fin 6 → Node (Fin 6) Nat Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 3
  | 1 => .consume 97 2
  | 2 => .accept ()
  | 3 => .consume 97 4
  | 4 => .consume 98 5
  | _ => .accept ()

private def summary {State : Type} {Tag : Type} {length : Nat} :
    RegexPikeVM.Result (Fin (length + 1) × Thread State length) Tag →
      Option (Nat × Nat × List Bool × List (Option Nat))
  | .incomplete | .finished none => none
  | .finished (some ((start, last), _)) => some
      (start.val, last.point.2.val, last.choices, [last.registers 0 |>.map Fin.val, last.registers 1 |>.map Fin.val])

theorem earliest_start_precedes_later_full_match :
    summary (search alternatives (probe [97, 98]) (fun _ => true) 0 30 (positions 2 0)) =
      some (0, 1, [false], [none, none]) := by decide

theorem full_match_restricts_before_selecting :
    summary (search alternatives (probe [97, 98]) (fun point => point.2.val == 2) 0 30 [0]) =
      some (0, 2, [true], [none, none]) := by decide

private def captured : Fin 4 → Node (Fin 4) Nat Unit Unit := fun state =>
  match state.val with
  | 0 => .save 0 1
  | 1 => .consume 955 2
  | 2 => .save 1 3
  | _ => .accept ()

theorem later_start_retains_original_capture_coordinates :
    summary (search captured (probe [97, 955, 98]) (fun _ => true) 0 30 (positions 3 0)) =
      some (1, 2, [], [some 1, some 2]) := by decide

theorem byte_transport_retains_empty_and_unmatched_capture :
    byteObservation "aλb".toList ⟨⟨1, 2⟩, [none, some ⟨1, 1⟩, some ⟨1, 2⟩], [false]⟩ =
      ⟨⟨1, 3⟩, [none, some ⟨1, 1⟩, some ⟨1, 3⟩], [false]⟩ := by decide

private def beginning : Fin 2 → Node (Fin 2) Nat Unit Unit := fun state =>
  if state.val = 0 then .assertion () 1 else .accept ()

/-- A suffix may not replace the original haystack when assertions inspect
absolute position. The two computations have genuinely different meanings. -/
theorem slicing_changes_beginning_assertion :
    summary (search beginning (probe [97, 98]) (fun _ => true) 0 20 [1]) = none ∧
      summary (search beginning (probe [98]) (fun _ => true) 0 20 [0]) =
        some (0, 0, [], [none, none]) := by decide

theorem pending_earlier_start_is_not_skipped :
    scan (fun position : Bool => if position then .finished (some (7, ())) else .incomplete)
        [false, true] = .incomplete := by rfl

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPublicSearch
