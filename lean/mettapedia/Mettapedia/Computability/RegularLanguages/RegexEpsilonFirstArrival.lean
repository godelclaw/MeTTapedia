import Mettapedia.Computability.RegularLanguages.RegexPikeCoverage
import Mettapedia.Computability.RegularLanguages.RegexPikePrefix
import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Epsilon first arrivals and memoized depth-first search

The complete closure may explore beyond its first eligible terminal. Its
first eligible emitted snapshot nevertheless agrees with the short-circuiting
recursive search, including capture registers and branch history.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexEpsilonFirstArrival

open RegexTaggedGraph RegexSelectionCorrespondence RegexClosureComposition

universe u v w

section Generic

variable {Value : Type u} {Key : Type v} {Tag : Type w} [DecidableEq Key]

def accepts (step : Value → Action Value Tag) (value : Value) : Option Tag :=
  match step value with
  | .accept tag => some tag
  | _ => none

def finish (seen : Finset Key) : Option (Value × Tag) → RegexMemoizedSearch.Result Value Tag Key
  | none => .absent seen
  | some (value, tag) => .found value tag

/-- A finite closure and a short-circuiting search compute the same first
eligible terminal. The closure's final memo is relevant only when no terminal
was selected. Later exploration never changes an earlier selected snapshot. -/
theorem search_of_closure [Fintype Key]
    (key : Value → Key) (step : Value → Action Value Tag) (eligible : Key → Bool) (fuel : Nat) :
    ∀ (seen : Finset Key) (first : Value) (output : List Value) (final : Finset Key),
      Closure key (fun value => RegexMemoizedSearch.actionChildren (step value))
        (fun value => (accepts step value).isSome) [first] seen output final →
      Fintype.card Key - seen.card + 1 < fuel →
      RegexMemoizedSearch.search key step eligible fuel seen first =
        finish final (RegexPikeVM.candidates (accepts step) (fun value => eligible (key value)) output).2 := by
  induction fuel with
  | zero => intro seen first output final closed enough; omega
  | succ fuel ih =>
      intro seen first output final closed enough
      cases closed with
      | skip visited tail =>
          cases tail
          simp [RegexMemoizedSearch.search, visited, RegexPikeVM.candidates, finish]
      | @visit _ _ _ later final fresh tail =>
          have childEnough : Fintype.card Key - (insert (key first) seen).card + 1 < fuel := by
            have bounded := Finset.card_le_univ (insert (key first) seen)
            rw [Finset.card_insert_of_notMem fresh] at bounded ⊢
            omega
          cases next : step first with
          | accept tag =>
              simp only [next, RegexMemoizedSearch.actionChildren, List.nil_append] at tail
              cases tail
              cases allowed : eligible (key first) <;>
                simp [RegexMemoizedSearch.search, fresh, next, allowed, accepts,
                  RegexPikeVM.candidates, finish]
          | dead =>
              simp only [next, RegexMemoizedSearch.actionChildren, List.nil_append] at tail
              cases tail
              simp [RegexMemoizedSearch.search, fresh, next, accepts, RegexPikeVM.candidates, finish]
          | next target =>
              simp only [next, RegexMemoizedSearch.actionChildren, List.append_nil] at tail
              have targetRun := ih (insert (key first) seen) target later final tail childEnough
              simpa [RegexMemoizedSearch.search, fresh, next, accepts] using targetRun
          | branch left right =>
              simp only [next, RegexMemoizedSearch.actionChildren, List.append_nil] at tail
              obtain ⟨before, middle, after, leftClosed, rightClosed, outputSame⟩ :=
                tail.split [left] [right] rfl
              have leftRun := ih (insert (key first) seen) left before middle leftClosed childEnough
              have rightEnough : Fintype.card Key - middle.card + 1 < fuel := by
                have included := Finset.card_le_card leftClosed.seen_mono
                omega
              have rightRun := ih middle right after final rightClosed rightEnough
              rw [outputSame]
              simp only [accepts, next, Option.isSome, Bool.false_eq_true, ↓reduceIte]
              rw [RegexPikePrefix.candidates_append]
              cases picked : RegexPikeVM.candidates (accepts step)
                  (fun value => eligible (key value)) before with
              | mk active candidate =>
                  cases candidate with
                  | none =>
                      simpa [RegexMemoizedSearch.search, fresh, next, leftRun, picked, finish,
                        RegexPikePrefix.appendCandidates] using rightRun
                  | some winner =>
                      simp [RegexMemoizedSearch.search, fresh, next, leftRun, picked, finish,
                        RegexPikePrefix.appendCandidates]

end Generic

section Graph

open OrderedGraphSearch (Point Probe)

universe z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- A phase ends at the first original frontier instruction. The frontier
state is its tag; all original epsilon decisions and capture writes remain. -/
def phaseGraph (graph : State → Node State Class Assertion Tag) (state : State) :
    Node State Class Assertion State :=
  match graph state with
  | .accept _ | .consume _ _ => .accept state
  | .dead => .dead
  | .jump target => .jump target
  | .save slot target => .save slot target
  | .choice left right => .choice left right
  | .assertion assertion_ target => .assertion assertion_ target

theorem phase_children (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) :
    RegexMemoizedSearch.actionChildren (action (phaseGraph graph) probe first) =
      epsilonChildren graph probe first := by
  cases node : graph first.point.1 with
  | accept _ | consume _ _ | dead | jump _ | choice _ _ | save _ _ =>
      simp [action, phaseGraph, node, RegexMemoizedSearch.actionChildren, epsilonChildren, edges]
  | assertion assertion_ target =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [action, phaseGraph, node, RegexMemoizedSearch.actionChildren, epsilonChildren, edges, holds]

theorem phase_emits (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) :
    (accepts (action (phaseGraph graph) probe) first).isSome = isFrontier (graph first.point.1) := by
  cases node : graph first.point.1 with
  | accept _ | consume _ _ | dead | jump _ | choice _ _ | save _ _ =>
      simp [action, phaseGraph, node, accepts, isFrontier]
  | assertion assertion_ target =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [action, phaseGraph, node, accepts, isFrontier, holds]

theorem phase_accepts (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) :
    accepts (action (phaseGraph graph) probe) first = RegexPikeVM.terminal (phaseGraph graph) first := by
  cases node : graph first.point.1 with
  | accept _ | consume _ _ | dead | jump _ | choice _ _ | save _ _ =>
      simp [action, phaseGraph, node, accepts, RegexPikeVM.terminal]
  | assertion assertion_ target =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [action, phaseGraph, node, accepts, RegexPikeVM.terminal, holds]

/-- The actual emitted representative selected by any point-based frontier
predicate is exactly the independently least simple accepting epsilon path,
including its literal register snapshot. -/
theorem selected_frontier_leastSimple [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first owner : Thread State length)
    (output : List (Thread State length)) (final : Finset State) (dfsFuel : Nat)
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      [first] ∅ output final)
    (selected : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => eligible thread.point) output).2 = some (owner, owner.point.1))
    (enough : Fintype.card (Point State length) + 1 < dfsFuel) :
    LeastSimple (phaseGraph graph) probe (fun thread => eligible thread.point) first owner := by
  have pointClosed := same_position_rekey graph probe first.point.2 closed (by
    intro thread member
    have equal : thread = first := List.mem_singleton.mp member
    rw [equal])
  simp only [Finset.image_empty] at pointClosed
  have converted : Closure Thread.point
      (fun thread => RegexMemoizedSearch.actionChildren (action (phaseGraph graph) probe thread))
      (fun thread => (accepts (action (phaseGraph graph) probe) thread).isSome)
      [first] ∅ output (final.image (fun state => (state, first.point.2))) := by
    simpa only [phase_children, phase_emits] using pointClosed
  have outcome := search_of_closure Thread.point (action (phaseGraph graph) probe) eligible dfsFuel
    ∅ first output _ converted (by simpa using enough)
  have acceptsEq : accepts (action (phaseGraph graph) probe) =
      RegexPikeVM.terminal (phaseGraph graph) := funext (phase_accepts graph probe)
  rw [acceptsEq, selected] at outcome
  have found : RegexMemoizedSearch.taggedSearch (phaseGraph graph) probe eligible dfsFuel first =
      .found owner owner.point.1 := outcome
  exact ((RegexMemoizedSearch.taggedSearch_leastSimple (phaseGraph graph) probe eligible first owner
    owner.point.1 dfsFuel enough).mp found).1

theorem phase_frontier_accept (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length)
    (frontier : isFrontier (graph first.point.1) = true) :
    action (phaseGraph graph) probe first = .accept first.point.1 := by
  cases node : graph first.point.1 <;> simp_all [isFrontier, action, phaseGraph]

theorem phase_next_not_frontier (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (step : action (phaseGraph graph) probe first = .next target) :
    isFrontier (graph first.point.1) = false := by
  cases node : graph first.point.1 <;> simp_all [isFrontier, action, phaseGraph]

theorem phase_branch_not_frontier (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first left right : Thread State length)
    (step : action (phaseGraph graph) probe first = .branch left right) :
    isFrontier (graph first.point.1) = false := by
  cases node : graph first.point.1 <;> simp_all [isFrontier, action, phaseGraph]

theorem phase_nonfrontier_next_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (notFrontier : isFrontier (graph first.point.1) = false) :
    action (phaseGraph graph) probe first = .next target ↔ action graph probe first = .next target := by
  cases node : graph first.point.1 with
  | accept _ | consume _ _ => simp [isFrontier, node] at notFrontier
  | dead | jump _ | save _ _ | choice _ _ =>
      simp [action, phaseGraph, node]
  | assertion assertion_ next =>
      cases holds : probe.holds assertion_ first.point.2 <;> simp [action, phaseGraph, node, holds]

theorem phase_nonfrontier_branch_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first left right : Thread State length)
    (notFrontier : isFrontier (graph first.point.1) = false) :
    action (phaseGraph graph) probe first = .branch left right ↔
      action graph probe first = .branch left right := by
  cases node : graph first.point.1 with
  | accept _ | consume _ _ => simp [isFrontier, node] at notFrontier
  | dead | jump _ | save _ _ | choice _ _ => simp [action, phaseGraph, node]
  | assertion assertion_ next =>
      cases holds : probe.holds assertion_ first.point.2 <;> simp [action, phaseGraph, node, holds]

/-- An epsilon arrival is an original-graph history that stops at its first
frontier node. It is specified without running either closure or DFS. -/
def EpsilonArrival (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length)
    (code : List Bool) (points : List (Point State length)) (last : Thread State length) : Prop :=
  RegexPikeSelection.Prefix graph probe first code points last ∧
    (∀ point ∈ points, isFrontier (graph point.1) = false) ∧ isFrontier (graph last.point.1) = true

theorem phase_trace_arrival {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : State}
    (trace : Trace (phaseGraph graph) probe eligible first code points last tag) :
    ∃ before, points = before ++ [last.point] ∧ EpsilonArrival graph probe first code before last := by
  induction trace with
  | @done first tag step _ =>
      have terminal := action_accept_terminal (phaseGraph graph) probe _ _ step
      have frontier : isFrontier (graph first.point.1) = true := by
        cases node : graph first.point.1 <;> simp_all [RegexPikeVM.terminal, phaseGraph, isFrontier]
      exact ⟨[], rfl, .nil _, by simp, frontier⟩
  | next step _ ih =>
      obtain ⟨before, pointsSame, history, earlier, frontier⟩ := ih
      have notFrontier := phase_next_not_frontier graph probe _ _ step
      refine ⟨_ :: before, by simp [pointsSame], .next
        ((phase_nonfrontier_next_iff graph probe _ _ notFrontier).mp step) history, ?_, frontier⟩
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact notFrontier
      · exact earlier point member
  | left step _ ih =>
      obtain ⟨before, pointsSame, history, earlier, frontier⟩ := ih
      have notFrontier := phase_branch_not_frontier graph probe _ _ _ step
      refine ⟨_ :: before, by simp [pointsSame], .left
        ((phase_nonfrontier_branch_iff graph probe _ _ _ notFrontier).mp step) history, ?_, frontier⟩
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact notFrontier
      · exact earlier point member
  | right step _ ih =>
      obtain ⟨before, pointsSame, history, earlier, frontier⟩ := ih
      have notFrontier := phase_branch_not_frontier graph probe _ _ _ step
      refine ⟨_ :: before, by simp [pointsSame], .right
        ((phase_nonfrontier_branch_iff graph probe _ _ _ notFrontier).mp step) history, ?_, frontier⟩
      intro point member
      rcases List.mem_cons.mp member with same | member
      · subst point; exact notFrontier
      · exact earlier point member

theorem arrival_phase_trace {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)}
    (arrival : EpsilonArrival graph probe first code points last) (allowed : eligible last = true) :
    Trace (phaseGraph graph) probe eligible first code (points ++ [last.point]) last last.point.1 := by
  obtain ⟨history, earlier, frontier⟩ := arrival
  induction history with
  | nil => exact .done (phase_frontier_accept graph probe _ frontier) allowed
  | @next first target code points last step _ ih =>
      have notFrontier := earlier first.point (by simp)
      apply Trace.next ((phase_nonfrontier_next_iff graph probe _ _ notFrontier).mpr step)
      exact ih allowed (fun point member => earlier point (by simp [member])) frontier
  | @left first left right code points last step _ ih =>
      have notFrontier := earlier first.point (by simp)
      apply Trace.left ((phase_nonfrontier_branch_iff graph probe _ _ _ notFrontier).mpr step)
      exact ih allowed (fun point member => earlier point (by simp [member])) frontier
  | @right first left right code points last step _ ih =>
      have notFrontier := earlier first.point (by simp)
      apply Trace.right ((phase_nonfrontier_branch_iff graph probe _ _ _ notFrontier).mpr step)
      exact ih allowed (fun point member => earlier point (by simp [member])) frontier

/-- The selected frontier representative is least among independently
specified original-graph epsilon arrivals, not just paths in the transformed
phase graph. Capture snapshots and all branch choices are retained literally. -/
theorem selected_frontier_leastArrival [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first owner : Thread State length)
    (output : List (Thread State length)) (final : Finset State) (dfsFuel : Nat)
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      [first] ∅ output final)
    (selected : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => eligible thread.point) output).2 = some (owner, owner.point.1))
    (enough : Fintype.card (Point State length) + 1 < dfsFuel) :
    ∃ code before, EpsilonArrival graph probe first code before owner ∧
      Simple (before ++ [owner.point]) ∧
      ∀ otherCode otherPoints other,
        EpsilonArrival graph probe first otherCode otherPoints other →
        Simple (otherPoints ++ [other.point]) → eligible other.point = true →
          code = otherCode ∨ RegexMatchObservations.HigherPriority code otherCode := by
  obtain ⟨code, points, tag, trace, simple, minimal⟩ :=
    selected_frontier_leastSimple graph probe eligible first owner output final dfsFuel closed selected enough
  obtain ⟨before, same, arrival⟩ := phase_trace_arrival trace
  refine ⟨code, before, arrival, same ▸ simple, ?_⟩
  intro otherCode otherPoints other otherArrival otherSimple otherAllowed
  exact minimal otherCode (otherPoints ++ [other.point]) other other.point.1
    (arrival_phase_trace otherArrival otherAllowed) otherSimple

theorem close_first_arrival_least [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first owner : Thread State length)
    (output : List (Thread State length)) (closureFuel : Nat)
    (closed : close graph probe closureFuel [first] = some output)
    (selected : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => eligible thread.point) output).2 = some (owner, owner.point.1)) :
    ∃ code before, EpsilonArrival graph probe first code before owner ∧
      Simple (before ++ [owner.point]) ∧
      ∀ otherCode otherPoints other,
        EpsilonArrival graph probe first otherCode otherPoints other →
        Simple (otherPoints ++ [other.point]) → eligible other.point = true →
          code = otherCode ∨ RegexMatchObservations.HigherPriority code otherCode := by
  obtain ⟨final, derivation⟩ := firstVisits_derivation closureFuel [first] ∅ output closed
  exact selected_frontier_leastArrival graph probe eligible first owner output final
    (Fintype.card (Point State length) + 2) derivation selected (by omega)

/-- Multiple roots retain their order: the selected snapshot comes from the
earliest root with an eligible path, and is the independently least simple
path for that root. The memo invariant concerns a completed target search;
it is not an assertion that suspended Pike futures are dead. -/
theorem roots_selected [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (pending : List (Thread State length)) :
    ∀ (seen : Finset (Point State length)) (output : List (Thread State length))
      (final : Finset (Point State length)) (owner : Thread State length) (tag : Tag),
      Closure Thread.point
        (fun thread => RegexMemoizedSearch.actionChildren (action graph probe thread))
        (fun thread => (accepts (action graph probe) thread).isSome)
        pending seen output final →
      RegexMemoizedSearch.Safe (RegexMemoizedSearch.children graph probe)
        (RegexMemoizedSearch.goal graph eligible) ∅ seen →
      (RegexPikeVM.candidates (accepts (action graph probe))
        (fun thread => eligible thread.point) output).2 = some (owner, tag) →
      ∃ before root after, pending = before ++ root :: after ∧
        LeastSimple graph probe (fun thread => eligible thread.point) root owner ∧
        ∀ earlier ∈ before, ¬ ∃ code points last tag,
          Trace graph probe (fun thread => eligible thread.point) earlier code points last tag := by
  induction pending with
  | nil =>
      intro seen output final owner tag closed _ selected
      cases closed
      simp [RegexPikeVM.candidates] at selected
  | cons first rest ih =>
      intro seen output final owner tag closed safe selected
      obtain ⟨before, middle, after, left, right, sameOutput⟩ := closed.split [first] rest rfl
      let fuel := Fintype.card (Point State length) + 2
      have enough : Fintype.card (Point State length) - seen.card + 1 < fuel := by
        dsimp [fuel]; omega
      have computed := search_of_closure Thread.point (action graph probe) eligible fuel
        seen first before middle left enough
      have checked := RegexMemoizedSearch.search_contract graph probe eligible fuel seen ∅ first
        (by simp) safe enough
      rw [sameOutput, RegexPikePrefix.candidates_append] at selected
      cases picked : RegexPikeVM.candidates (accepts (action graph probe))
          (fun thread => eligible thread.point) before with
      | mk active candidate =>
          cases candidate with
          | some winner =>
              simp only [picked, RegexPikePrefix.appendCandidates, Option.some.injEq] at selected
              have sameWinner : winner = (owner, tag) := selected
              subst winner
              rw [computed] at checked
              simp only [picked, finish, RegexMemoizedSearch.Contract] at checked
              exact ⟨[], first, rest, rfl, RegexMemoizedSearch.leastAvoiding_empty checked, by simp⟩
          | none =>
              simp only [picked, RegexPikePrefix.appendCandidates] at selected
              rw [computed] at checked
              simp only [picked, finish, RegexMemoizedSearch.Contract] at checked
              obtain ⟨earlierRoots, root, laterRoots, rootsSame, least, deadEarlier⟩ :=
                ih middle after final owner tag right checked.2.1 selected
              refine ⟨first :: earlierRoots, root, laterRoots, by simp [rootsSame], least, ?_⟩
              intro earlier member
              rcases List.mem_cons.mp member with equal | member
              · subst earlier
                rintro ⟨code, points, last, someTag, trace⟩
                exact checked.2.2 (RegexMemoizedSearch.trace_reaches trace ∅ (by simp [RegexMemoizedSearch.Avoids]))
              · exact deadEarlier earlier member

/-- The ordered multi-root first-arrival theorem for actual epsilon closure.
Each earlier root is excluded by independent finite epsilon-path semantics. -/
theorem closed_roots_first_arrival [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (pending : List (Thread State length))
    (position : Fin (length + 1)) (output : List (Thread State length)) (final : Finset State)
    (owner : Thread State length)
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      pending ∅ output final)
    (samePosition : ∀ thread ∈ pending, thread.point.2 = position)
    (selected : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => eligible thread.point) output).2 = some (owner, owner.point.1)) :
    ∃ before root after, pending = before ++ root :: after ∧
      LeastSimple (phaseGraph graph) probe (fun thread => eligible thread.point) root owner ∧
      ∀ earlier ∈ before, ¬ ∃ code points last tag,
        Trace (phaseGraph graph) probe (fun thread => eligible thread.point) earlier code points last tag := by
  have pointClosed := same_position_rekey graph probe position closed samePosition
  simp only [Finset.image_empty] at pointClosed
  have converted : Closure Thread.point
      (fun thread => RegexMemoizedSearch.actionChildren (action (phaseGraph graph) probe thread))
      (fun thread => (accepts (action (phaseGraph graph) probe) thread).isSome)
      pending ∅ output (final.image (fun state => (state, position))) := by
    simpa only [phase_children, phase_emits] using pointClosed
  have acceptsEq : accepts (action (phaseGraph graph) probe) =
      RegexPikeVM.terminal (phaseGraph graph) := funext (phase_accepts graph probe)
  apply roots_selected (phaseGraph graph) probe eligible pending ∅ output _ owner owner.point.1
    converted (by simp [RegexMemoizedSearch.Safe])
  simpa only [acceptsEq] using selected

end Graph

namespace Controls

private def probe : OrderedGraphSearch.Probe Unit Unit 1 :=
  ⟨fun _ position => position.val < 1, fun _ _ => false⟩

private def graph : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 3
  | 1 => .save 0 2
  | 2 => .consume () 4
  | 3 => .save 1 2
  | _ => .accept ()

private def initial : Thread (Fin 5) 1 := ⟨(0, 0), fun _ => none, []⟩
private def preferred : Thread (Fin 5) 1 := (initial.branch 1 false).saved 2 0
private def discarded : Thread (Fin 5) 1 := (initial.branch 3 true).saved 2 1

private theorem preferred_least :
    LeastSimple (phaseGraph graph) probe (fun _ => true) initial preferred := by
  have closed : close graph probe 20 [initial] = some [preferred] := rfl
  obtain ⟨final, derivation⟩ := firstVisits_derivation 20 [initial] ∅ [preferred] closed
  exact selected_frontier_leastSimple graph probe (fun _ => true) initial preferred
    [preferred] final 13 derivation rfl (by decide)

theorem ordered_first_arrival_retains_the_exact_preferred_capture :
    LeastSimple (phaseGraph graph) probe (fun _ => true) initial preferred ∧
      preferred.registers 0 = some 0 ∧ preferred.registers 1 = none := by
  exact ⟨preferred_least, rfl, rfl⟩

private def guarded : Fin 3 → Node (Fin 3) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .assertion () 1
  | 1 => .consume () 2
  | _ => .accept ()

theorem failed_assertion_does_not_create_an_epsilon_arrival :
    close guarded probe 12 [⟨(0, 0), fun _ => none, []⟩] = some [] ∧
      phaseGraph guarded 0 = .assertion () 1 := by
  exact ⟨rfl, rfl⟩

/-- Recognition and endpoint equality do not identify the selected capture
snapshot. Only the preferred arrival satisfies the least-path specification. -/
theorem equal_frontier_points_do_not_make_capture_arrivals_interchangeable :
    preferred.point = discarded.point ∧ preferred.registers 0 ≠ discarded.registers 0 ∧
      ¬ LeastSimple (phaseGraph graph) probe (fun _ => true) initial discarded := by
  refine ⟨rfl, by decide, ?_⟩
  intro discardedLeast
  have equal := leastSimple_unique (phaseGraph graph) probe (fun _ => true)
    initial preferred discarded preferred_least discardedLeast
  have registers := congrArg (fun thread => thread.registers 0) equal
  cases registers

end Controls

#print axioms search_of_closure
#print axioms selected_frontier_leastSimple
#print axioms phase_trace_arrival
#print axioms arrival_phase_trace
#print axioms close_first_arrival_least
#print axioms Controls.equal_frontier_points_do_not_make_capture_arrivals_interchangeable

end Mettapedia.Computability.RegularLanguages.RegexEpsilonFirstArrival
