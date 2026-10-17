import Mettapedia.Computability.RegularLanguages.RegexClosureComposition
import Mettapedia.Computability.RegularLanguages.RegexUniformFutures

/-!
# Coverage of complete Pike executions

Visited epsilon points are represented by actual expanded snapshots, not by
failed futures. The closure's finite derivation records those representatives;
point-uniform futures then transfer accepting suffixes to retained snapshots.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeCoverage

open RegexTaggedGraph RegexSelectionCorrespondence RegexClosureComposition
open OrderedGraphSearch (Point Probe)

universe u v w z

section Closure

variable {Value : Type u} {Key : Type v} [DecidableEq Key]
    {key : Value → Key} {children : Value → List Value} {emit : Value → Bool}

/-- Every newly visited key has a representative whose children were covered
and whose emitted occurrence, if any, is retained literally in the output. -/
theorem closure_covers {pending seen output final}
    (closed : Closure key children emit pending seen output final) :
    ∀ point ∈ final, point ∈ seen ∨ ∃ value,
      key value = point ∧ (∀ child ∈ children value, key child ∈ final) ∧
        (emit value = true → value ∈ output) := by
  induction closed with
  | nil => intro point member; exact Or.inl member
  | skip _ _ ih => exact ih
  | @visit first rest seen later final fresh tail ih =>
      intro point member
      rcases ih point member with initial | represented
      · rcases Finset.mem_insert.mp initial with same | initial
        · subst point
          refine Or.inr ⟨first, rfl, ?_, ?_⟩
          · intro child member
            exact tail.roots_seen child (List.mem_append_left _ member)
          · intro emitted; simp [emitted]
        · exact Or.inl initial
      · obtain ⟨value, same, childrenSeen, emitted⟩ := represented
        refine Or.inr ⟨value, same, childrenSeen, ?_⟩
        intro emits
        have member := emitted emits
        cases emit first <;> simp [member]

end Closure

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem point_closure_expands [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    {pending output : List (Thread State length)} {final : Finset (Point State length)}
    (closed : Closure Thread.point (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) pending ∅ output final)
    (first target : Thread State length) (visited : first.point ∈ final)
    (edge : target ∈ epsilonChildren graph probe first) : target.point ∈ final := by
  rcases closure_covers closed first.point visited with impossible | ⟨owner, same, childrenSeen, _⟩
  · simp at impossible
  · have member : target.point ∈ (epsilonChildren graph probe first).map Thread.point :=
      List.mem_map.mpr ⟨target, edge, rfl⟩
    rw [epsilonChildren_erase graph probe first, ← same,
      ← epsilonChildren_erase graph probe owner] at member
    obtain ⟨child, childMember, equal⟩ := List.mem_map.mp member
    exact equal ▸ childrenSeen child childMember

theorem point_closure_emits [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    {pending output : List (Thread State length)} {final : Finset (Point State length)}
    (closed : Closure Thread.point (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) pending ∅ output final)
    (first : Thread State length) (visited : first.point ∈ final)
    (frontier : isFrontier (graph first.point.1) = true) :
    ∃ owner ∈ output, owner.point = first.point := by
  rcases closure_covers closed first.point visited with impossible | ⟨owner, same, _, emitted⟩
  · simp at impossible
  · exact ⟨owner, emitted (by simpa [same] using frontier), same⟩

theorem nonfrontier_edge_is_epsilon (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (notFrontier : isFrontier (graph first.point.1) ≠ true)
    (edge : target ∈ edges graph probe first) : target ∈ epsilonChildren graph probe first := by
  cases node : graph first.point.1 <;> simp_all [isFrontier, epsilonChildren]

/-- An arbitrary finite accepting path through covered epsilon points reaches
a retained frontier snapshot with an accepting suffix. -/
theorem trace_hits_frontier [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool)
    {pending output : List (Thread State length)} {final : Finset (Point State length)}
    (closed : Closure Thread.point (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) pending ∅ output final)
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag) :
    first.point ∈ final →
      ∃ owner ∈ output, ∃ suffix suffixPoints after,
        Trace graph probe (fun thread => eligible thread.point) owner suffix suffixPoints after tag := by
  induction trace with
  | @done first tag step allowed =>
      intro visited
      have frontier : isFrontier (graph first.point.1) = true := by
        have terminal := action_accept_terminal graph probe first tag step
        cases node : graph first.point.1 <;> simp_all [RegexPikeVM.terminal, isFrontier]
      obtain ⟨owner, member, same⟩ := point_closure_emits graph probe closed first visited frontier
      obtain ⟨after, transferred, _⟩ :=
        RegexUniformFutures.Trace.transfer (Trace.done step allowed) owner same
      exact ⟨owner, member, [], [first.point], after, transferred⟩
  | @next first target code points last tag step tail ih =>
      intro visited
      by_cases frontier : isFrontier (graph first.point.1) = true
      · obtain ⟨owner, member, same⟩ := point_closure_emits graph probe closed first visited frontier
        obtain ⟨after, transferred, _⟩ := RegexUniformFutures.Trace.transfer (Trace.next step tail) owner same
        exact ⟨owner, member, code, first.point :: points, after, transferred⟩
      · apply ih
        exact point_closure_expands graph probe closed first target visited
          (nonfrontier_edge_is_epsilon graph probe first target frontier (action_next_edge _ _ _ _ step).1)
  | @left first left right code points last tag step tail ih =>
      intro visited
      by_cases frontier : isFrontier (graph first.point.1) = true
      · obtain ⟨owner, member, same⟩ := point_closure_emits graph probe closed first visited frontier
        obtain ⟨after, transferred, _⟩ := RegexUniformFutures.Trace.transfer (Trace.left step tail) owner same
        exact ⟨owner, member, false :: code, first.point :: points, after, transferred⟩
      · apply ih
        exact point_closure_expands graph probe closed first left visited
          (nonfrontier_edge_is_epsilon graph probe first left frontier (action_branch_edges _ _ _ _ _ step).1)
  | @right first left right code points last tag step tail ih =>
      intro visited
      by_cases frontier : isFrontier (graph first.point.1) = true
      · obtain ⟨owner, member, same⟩ := point_closure_emits graph probe closed first visited frontier
        obtain ⟨after, transferred, _⟩ := RegexUniformFutures.Trace.transfer (Trace.right step tail) owner same
        exact ⟨owner, member, true :: code, first.point :: points, after, transferred⟩
      · apply ih
        exact point_closure_expands graph probe closed first right visited
          (nonfrontier_edge_is_epsilon graph probe first right frontier (action_branch_edges _ _ _ _ _ step).2.1)

theorem candidates_none_rejects {Value : Type u} {Tag : Type v}
    (accepts : Value → Option Tag) (eligible : Value → Bool) (frontier : List Value)
    (absent : (RegexPikeVM.candidates accepts eligible frontier).2 = none) :
    ∀ value ∈ frontier, ∀ tag, accepts value = some tag → eligible value = false := by
  induction frontier with
  | nil => simp
  | cons first rest ih =>
      intro value member tag accepted
      cases firstAccepted : accepts first with
      | none =>
          simp only [RegexPikeVM.candidates, firstAccepted] at absent
          rcases List.mem_cons.mp member with same | member
          · subst value; simp [firstAccepted] at accepted
          · exact ih absent value member tag accepted
      | some firstTag =>
          cases allowed : eligible first with
          | true => simp [RegexPikeVM.candidates, firstAccepted, allowed] at absent
          | false =>
              simp only [RegexPikeVM.candidates, firstAccepted, allowed, Bool.false_eq_true,
                ↓reduceIte] at absent
              rcases List.mem_cons.mp member with same | member
              · subst value; exact allowed
              · exact ih absent value member tag accepted

theorem candidates_none_active {Value : Type u} {Tag : Type v}
    (accepts : Value → Option Tag) (eligible : Value → Bool) (frontier : List Value)
    (absent : (RegexPikeVM.candidates accepts eligible frontier).2 = none) :
    ∀ value ∈ frontier, accepts value = none →
      value ∈ (RegexPikeVM.candidates accepts eligible frontier).1 := by
  induction frontier with
  | nil => simp
  | cons first rest ih =>
      intro value member notAccepted
      cases firstAccepted : accepts first with
      | none =>
          simp only [RegexPikeVM.candidates, firstAccepted] at absent ⊢
          rcases List.mem_cons.mp member with same | member
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (ih absent value member notAccepted))
      | some firstTag =>
          cases allowed : eligible first with
          | true => simp [RegexPikeVM.candidates, firstAccepted, allowed] at absent
          | false =>
              simp only [RegexPikeVM.candidates, firstAccepted, allowed, Bool.false_eq_true,
                ↓reduceIte] at absent ⊢
              rcases List.mem_cons.mp member with same | member
              · subst value; simp [firstAccepted] at notAccepted
              · exact ih absent value member notAccepted

theorem consume_action_not_branch (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first left right : Thread State length)
    (class_ : Class) (target : State) (node : graph first.point.1 = .consume class_ target) :
    action graph probe first ≠ .branch left right := by
  intro step
  simp only [action, node] at step
  split at step
  · cases advanced : OrderedGraphSearch.successor first.point.2 <;> simp [advanced] at step
  · cases step

/-- A successful suffix from an emitted site either accepts at that site or
has a genuine consuming successor with a successful suffix. -/
theorem trace_frontier_elim (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (frontier : isFrontier (graph first.point.1) = true)
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag) :
    (RegexPikeVM.terminal graph first = some tag ∧ eligible first.point = true) ∨
      ∃ target, RegexPikeVM.terminal graph first = none ∧ target ∈ edges graph probe first ∧
        ∃ suffix suffixPoints after,
          Trace graph probe (fun thread => eligible thread.point) target suffix suffixPoints after tag := by
  cases node : graph first.point.1 with
  | dead | jump _ | save _ _ | choice _ _ | assertion _ _ => simp [isFrontier, node] at frontier
  | accept accepted =>
      cases trace with
      | done step allowed => exact Or.inl ⟨action_accept_terminal _ _ _ _ step, allowed⟩
      | next step _ => simp [action, node] at step
      | left step _ => simp [action, node] at step
      | right step _ => simp [action, node] at step
  | consume class_ next =>
      cases trace with
      | done step _ =>
          have terminal := action_accept_terminal _ _ _ _ step
          simp [RegexPikeVM.terminal, node] at terminal
      | @next _ target suffix suffixPoints after _ step tail =>
          exact Or.inr ⟨target, by simp [RegexPikeVM.terminal, node],
            (action_next_edge _ _ _ _ step).1, _, _, _, tail⟩
      | @left _ left right _ _ _ _ step _ =>
          exact False.elim (consume_action_not_branch _ _ _ left right class_ next node step)
      | @right _ left right _ _ _ _ step _ =>
          exact False.elim (consume_action_not_branch _ _ _ left right class_ next node step)

theorem option_or_eq_none {Value : Type u} (first second : Option Value)
    (absent : first.or second = none) : first = none ∧ second = none := by
  cases first <;> cases second <;> simp_all

/-- A completed empty result excludes every finite accepting trace from every
pending snapshot. Closure visits may cover suspended successful work, so the
proof uses emitted representatives rather than declaring visited points dead.
No simplicity restriction is imposed on the competing trace. -/
theorem execute_none_excludes_trace [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (closureFuel inputFuel : Nat) :
    ∀ (pending : List (Thread State length)) (previous : Option (Thread State length × Tag))
      (position : Fin (length + 1)),
      (∀ first ∈ pending, first.point.2 = position) →
      RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
        (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
        (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
        closureFuel inputFuel pending previous = .finished none →
      previous = none ∧ ∀ first ∈ pending, ∀ code points last tag,
        ¬ Trace graph probe (fun thread => eligible thread.point) first code points last tag := by
  induction inputFuel with
  | zero => intro pending previous position same finished; cases finished
  | succ fuel ih =>
      intro pending previous position same finished
      cases closed : firstVisits (fun thread : Thread State length => thread.point.1)
          (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
          closureFuel pending ∅ with
      | none => simp [RegexPikeVM.execute, closed] at finished
      | some frontier =>
          have frontierValid : ∀ thread ∈ frontier,
              thread.point.2 = position ∧ isFrontier (graph thread.point.1) = true := by
            apply firstVisits_sound (fun thread : Thread State length => thread.point.1)
              (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
              (fun thread => thread.point.2 = position) ?_ closureFuel pending ∅ frontier same closed
            intro source valid target edge
            exact (epsilonChildren_same_position graph probe source target edge).trans valid
          let active := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).1
          let candidate := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).2
          let advancing := active.flatMap (edges graph probe)
          have advancePosition : ∀ target ∈ advancing,
              target.point.2.val = position.val + 1 := by
            intro target member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have member := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier source sourceMember
            have valid := frontierValid source member.1
            have advances := (RegexPikeVM.active_consume_bounds graph probe source valid.2 member.2).2
              target edge
            simpa [valid.1] using advances
          simp only [RegexPikeVM.execute, closed] at finished
          change (if advancing.isEmpty then RegexPikeVM.Result.finished (candidate.or previous)
            else RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
              (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
              (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
              closureFuel fuel advancing (candidate.or previous)) = .finished none at finished
          have nextContract : candidate.or previous = none ∧
              ∀ target ∈ advancing, ∀ code points last tag,
                ¬ Trace graph probe (fun thread => eligible thread.point) target code points last tag := by
            cases empty : advancing.isEmpty with
            | true =>
                simp only [empty, ↓reduceIte, RegexPikeVM.Result.finished.injEq] at finished
                refine ⟨finished, ?_⟩
                have noTargets : advancing = [] := List.isEmpty_iff.mp empty
                simp [noTargets]
            | false =>
                simp only [empty, Bool.false_eq_true, ↓reduceIte] at finished
                have inhabited : advancing ≠ [] := by
                  intro noTargets
                  simp [noTargets] at empty
                obtain ⟨target, member⟩ := List.exists_mem_of_ne_nil advancing inhabited
                have synchronous : ∀ other ∈ advancing, other.point.2 = target.point.2 := by
                  intro other otherMember
                  apply Fin.ext
                  exact (advancePosition other otherMember).trans (advancePosition target member).symm
                exact ih advancing (candidate.or previous) target.point.2 synchronous finished
          have absent := option_or_eq_none candidate previous nextContract.1
          refine ⟨absent.2, ?_⟩
          intro first member code points last tag trace
          obtain ⟨pcFinal, derivation⟩ := firstVisits_derivation closureFuel pending ∅ frontier closed
          have pointClosed := same_position_rekey graph probe position derivation same
          simp only [Finset.image_empty] at pointClosed
          have visited := pointClosed.roots_seen first member
          obtain ⟨owner, ownerMember, suffix, suffixPoints, after, successful⟩ :=
            trace_hits_frontier graph probe eligible pointClosed trace visited
          rcases trace_frontier_elim graph probe eligible (frontierValid owner ownerMember).2 successful with
            accepted | ⟨target, notTerminal, edge, suffix, suffixPoints, after, tail⟩
          · have rejected := candidates_none_rejects (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier absent.1 owner ownerMember tag accepted.1
            simp [accepted.2] at rejected
          · have ownerActive := candidates_none_active (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier absent.1 owner ownerMember notTerminal
            have targetMember : target ∈ advancing :=
              List.mem_flatMap.mpr ⟨owner, ownerActive, edge⟩
            exact nextContract.2 target targetMember suffix suffixPoints after tag tail

theorem run_none_excludes_trace [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (closureFuel inputFuel : Nat)
    (first : Thread State length)
    (absent : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [first] = .finished none) :
    ∀ code points last tag,
      ¬ Trace graph probe (fun thread => eligible thread.point) first code points last tag := by
  apply (execute_none_excludes_trace graph probe eligible closureFuel inputFuel [first] none
    first.point.2 ?_ absent).2 first (by simp)
  intro thread member
  have equal : thread = first := List.mem_singleton.mp member
  rw [equal]

theorem actionChildren_eq_edges (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) :
    RegexMemoizedSearch.actionChildren (action graph probe first) = edges graph probe first := by
  cases node : graph first.point.1 with
  | accept _ | dead | jump _ | save _ _ | choice _ _ =>
      simp [action, RegexMemoizedSearch.actionChildren, edges, node]
  | consume class_ next =>
      cases contains : probe.contains class_ first.point.2 <;>
        simp only [action, edges, node, contains, Bool.false_eq_true, ↓reduceIte]
      · rfl
      · cases OrderedGraphSearch.successor first.point.2 <;> rfl
  | assertion assertion_ next =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [action, RegexMemoizedSearch.actionChildren, edges, node, holds]

/-- Every finite raw derivation reaching an eligible terminal has a trace
whose branch code and point observations are obtained from its actual edges. -/
theorem derives_has_trace (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    {first last : Thread State length} {tag : Tag}
    (derived : Derives graph probe first last)
    (terminal : RegexPikeVM.terminal graph last = some tag) (allowed : eligible last = true) :
    ∃ code points, Trace graph probe eligible first code points last tag := by
  unfold Derives at derived
  induction derived using Relation.ReflTransGen.head_induction_on with
  | refl =>
      have accepted : action graph probe last = .accept tag := by
        cases node : graph last.point.1 <;> simp [RegexPikeVM.terminal, node] at terminal
        cases terminal
        simp [action, node]
      exact ⟨[], [last.point], .done accepted allowed⟩
  | @head first target edge _ ih =>
      obtain ⟨code, points, trace⟩ := ih
      rw [← actionChildren_eq_edges graph probe first] at edge
      cases step : action graph probe first with
      | accept accepted => simp [step, RegexMemoizedSearch.actionChildren] at edge
      | dead => simp [step, RegexMemoizedSearch.actionChildren] at edge
      | next next =>
          simp only [step, RegexMemoizedSearch.actionChildren, List.mem_singleton] at edge
          subst target
          exact ⟨code, first.point :: points, .next step trace⟩
      | branch left right =>
          simp only [step, RegexMemoizedSearch.actionChildren, List.mem_cons, List.not_mem_nil,
            or_false] at edge
          rcases edge with same | same
          · subst target
            exact ⟨false :: code, first.point :: points, .left step trace⟩
          · subst target
            exact ⟨true :: code, first.point :: points, .right step trace⟩

theorem run_match_has_trace [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (closureFuel inputFuel : Nat)
    (first last : Thread State length) (tag : Tag)
    (selected : RegexPikeVM.run graph probe eligible closureFuel inputFuel [first] =
      .finished (some (last, tag))) :
    ∃ code points, Trace graph probe eligible first code points last tag := by
  obtain ⟨derived, terminal, allowed⟩ :=
    RegexPikeVM.run_match_sound graph probe eligible closureFuel inputFuel first last tag selected
  exact derives_has_trace graph probe eligible derived terminal allowed

/-- Adequate budgets turn the one-sided absence guarantee into equivalence.
The right-hand side ranges over all finite traces, including nullable cycles. -/
theorem run_none_iff_no_trace [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) (first : Thread State length) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      .finished none ↔
      ¬ ∃ code points last tag,
        Trace graph probe (fun thread => eligible thread.point) first code points last tag := by
  constructor
  · intro absent
    rintro ⟨code, points, last, tag, trace⟩
    exact run_none_excludes_trace graph probe eligible closureFuel inputFuel first absent
      code points last tag trace
  · intro noTrace
    cases result : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
        closureFuel inputFuel [first] with
    | incomplete =>
        exact False.elim (RegexPikeVM.run_ne_incomplete graph probe (fun thread => eligible thread.point)
          first closureFuel inputFuel closureEnough inputEnough result)
    | finished selected =>
        cases selected with
        | none => rfl
        | some pair =>
            obtain ⟨code, points, trace⟩ := run_match_has_trace graph probe
              (fun thread => eligible thread.point) closureFuel inputFuel first pair.1 pair.2 result
            exact False.elim (noTrace ⟨code, points, pair.1, pair.2, trace⟩)

/-- Pike and global memoized DFS agree on completed absence. This is not yet
the stronger equality of their selected capture snapshots. -/
theorem pike_dfs_absence_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel) (first : Thread State length) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      .finished none ↔
      ∃ after, RegexMemoizedSearch.taggedSearch graph probe eligible dfsFuel first = .absent after := by
  rw [run_none_iff_no_trace graph probe eligible closureFuel inputFuel closureEnough inputEnough,
    RegexMemoizedSearch.taggedSearch_absent_iff graph probe eligible first dfsFuel dfsEnough]

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {count : Nat} (state : Fin count) (length : Nat) : Thread (Fin count) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def nullable : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .choice 3 4
  | 3 => .jump 1
  | _ => .accept ()

private def cyclicLast : Thread (Fin 5) 0 :=
  (((((initial 0 0).branch 1 false).saved 2 0).branch 3 false).at 1).saved 2 0 |>.branch 4 true

/-- A nonsimple raw path still refutes a completed no-match, independently of
whether its capture history survives first-visit winner selection. -/
theorem even_a_cyclic_accepting_trace_refutes_completed_absence (closureFuel inputFuel : Nat) :
    RegexPikeVM.run nullable (probe 0) (fun _ => true) closureFuel inputFuel [initial 0 0] ≠
      .finished none := by
  have trace : Trace nullable (probe 0) (fun _ => true) (initial 0 0)
      [false, false, true] [(0, 0), (1, 0), (2, 0), (3, 0), (1, 0), (2, 0), (4, 0)] cyclicLast () :=
    .left rfl (.next rfl (.left rfl (.next rfl (.next rfl (.right rfl (.done rfl rfl))))))
  intro absent
  exact run_none_excludes_trace nullable (probe 0) (fun _ => true) closureFuel inputFuel
    (initial 0 0) absent _ _ _ _ trace

private def consuming : Fin 2 → Node (Fin 2) Unit Unit Unit := fun state =>
  if state = 0 then .consume () 1 else .accept ()

theorem closed_no_match_excludes_every_finite_trace :
    RegexPikeVM.run consuming (probe 0) (fun _ => true) 8 1 [initial 0 0] = .finished none ∧
      ¬ ∃ code points last tag,
        Trace consuming (probe 0) (fun _ => true) (initial 0 0) code points last tag := by
  have absent : RegexPikeVM.run consuming (probe 0) (fun _ => true) 8 1 [initial 0 0] =
      .finished none := rfl
  refine ⟨absent, ?_⟩
  exact (run_none_iff_no_trace consuming (probe 0) (fun _ => true) 8 1
    (by decide) (by decide) (initial 0 0)).mp absent

private def greedy : Fin 3 → Node (Fin 3) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 2
  | 1 => .consume () 0
  | _ => .accept ()

/-- A provisional empty acceptance is not a completed answer while a
higher-priority consuming future is unfinished. -/
theorem cutoff_after_a_candidate_is_not_completed_absence :
    RegexPikeVM.run greedy (probe 1) (fun _ => true) 12 1 [initial 0 1] = .incomplete ∧
      (∃ last, Trace greedy (probe 1) (fun _ => true) (initial 0 1) [true]
        [(0, 0), (2, 0)] last ()) ∧
      RegexPikeVM.run greedy (probe 1) (fun _ => true) 12 2 [initial 0 1] ≠ .incomplete := by
  refine ⟨rfl, ⟨(initial 0 1).branch 2 true, .right rfl (.done rfl rfl)⟩, ?_⟩
  exact RegexPikeVM.run_ne_incomplete greedy (probe 1) (fun _ => true) (initial 0 1)
    12 2 (by decide) (by decide)

end Controls

#print axioms closure_covers
#print axioms trace_hits_frontier
#print axioms execute_none_excludes_trace
#print axioms run_none_iff_no_trace
#print axioms pike_dfs_absence_iff
#print axioms Controls.cutoff_after_a_candidate_is_not_completed_absence

end Mettapedia.Computability.RegularLanguages.RegexPikeCoverage
