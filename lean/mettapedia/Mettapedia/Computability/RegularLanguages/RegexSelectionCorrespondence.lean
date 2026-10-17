import Mettapedia.Computability.RegularLanguages.RegexPikeVM
import Mathlib.Data.List.Lex

/-!+# Finite accepting paths and their observable priorities

Accepting paths below are specified by the actual graph instructions, not by
running the frontier executor. Their choice code is a suffix of the initial
thread's history. Point simplicity includes the accepting endpoint and uses
the pair of program counter and input position. It is deliberately different
from accepting only consumption-progressing repetition parses.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexSelectionCorrespondence

open RegexTaggedGraph
open OrderedGraphSearch (Point Probe successor)
open RegexMatchObservations (HigherPriority)

universe u v w z

inductive Action (α : Type u) (Tag : Type v) where
  | accept (tag : Tag)
  | dead
  | next (target : α)
  | branch (first second : α)

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- A single instruction's actual control action, including capture writes.
The independent path judgment can only use actions authorized by this graph. -/
def action (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (thread : Thread State length) : Action (Thread State length) Tag :=
  match graph thread.point.1 with
  | .accept tag => .accept tag
  | .dead => .dead
  | .jump target => .next (thread.at target)
  | .save slot target => .next (thread.saved target slot)
  | .choice first second => .branch (thread.branch first false) (thread.branch second true)
  | .consume class_ target =>
      if probe.contains class_ thread.point.2 then
        match successor thread.point.2 with
        | some position => .next { thread with point := (target, position) }
        | none => .dead
      else .dead
  | .assertion assertion_ target =>
      if probe.holds assertion_ thread.point.2 then .next (thread.at target) else .dead

inductive Trace (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool) :
    Thread State length → List Bool → List (Point State length) → Thread State length → Tag → Prop
  | done {first tag} : action graph probe first = .accept tag → eligible first = true →
      Trace graph probe eligible first [] [first.point] first tag
  | next {first target code points last tag} : action graph probe first = .next target →
      Trace graph probe eligible target code points last tag →
      Trace graph probe eligible first code (first.point :: points) last tag
  | left {first left right code points last tag} : action graph probe first = .branch left right →
      Trace graph probe eligible left code points last tag →
      Trace graph probe eligible first (false :: code) (first.point :: points) last tag
  | right {first left right code points last tag} : action graph probe first = .branch left right →
      Trace graph probe eligible right code points last tag →
      Trace graph probe eligible first (true :: code) (first.point :: points) last tag

def Simple (points : List (Point State length)) : Prop := points.Nodup

theorem action_next_edge (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target : Thread State length)
    (step : action graph probe first = .next target) :
    target ∈ edges graph probe first ∧ target.choices = first.choices := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step
  · cases step
  · cases step; simp [edges, node, Thread.at]
  · cases step
  · split at step
    · cases advanced : successor first.point.2 with
      | none => simp [advanced] at step
      | some position =>
          simp only [advanced, Action.next.injEq] at step
          subst target
          constructor
          · simp [edges, node, show probe.contains _ first.point.2 = true from by assumption, advanced]
          · rfl
    · cases step
  · split at step
    · cases step; simp [edges, node, by assumption, Thread.at]
    · cases step
  · cases step; simp [edges, node, Thread.saved, Thread.at]

theorem action_branch_edges (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first left right : Thread State length)
    (step : action graph probe first = .branch left right) :
    left ∈ edges graph probe first ∧ right ∈ edges graph probe first ∧
      left.choices = first.choices ++ [false] ∧ right.choices = first.choices ++ [true] := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step
  · cases step
  · cases step
  · cases step
    simp [edges, node, Thread.branch]
  · split at step
    · cases advanced : successor first.point.2 <;> simp [advanced] at step
    · cases step
  · split at step <;> cases step
  · cases step

theorem action_accept_terminal (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) (tag : Tag)
    (step : action graph probe first = .accept tag) : RegexPikeVM.terminal graph first = some tag := by
  cases node : graph first.point.1 <;> simp only [action, node] at step
  · cases step; simp [RegexPikeVM.terminal, node]
  · cases step
  · cases step
  · cases step
  · split at step
    · cases advanced : successor first.point.2 <;> simp [advanced] at step
    · cases step
  · split at step <;> cases step
  · cases step

theorem Trace.sound {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    Derives graph probe first last ∧ RegexPikeVM.terminal graph last = some tag ∧ eligible last = true := by
  induction trace with
  | done step allowed => exact ⟨.refl, action_accept_terminal _ _ _ _ step, allowed⟩
  | next step _ ih =>
      exact ⟨(Relation.ReflTransGen.single (action_next_edge _ _ _ _ step).1).trans ih.1, ih.2⟩
  | left step _ ih =>
      exact ⟨(Relation.ReflTransGen.single (action_branch_edges _ _ _ _ _ step).1).trans ih.1, ih.2⟩
  | right step _ ih =>
      exact ⟨(Relation.ReflTransGen.single (action_branch_edges _ _ _ _ _ step).2.1).trans ih.1, ih.2⟩

theorem Trace.choices {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    last.choices = first.choices ++ code := by
  induction trace with
  | done => simp
  | next step _ ih => simpa [(action_next_edge _ _ _ _ step).2] using ih
  | left step _ ih => simpa [(action_branch_edges _ _ _ _ _ step).2.2.1, List.append_assoc] using ih
  | right step _ ih => simpa [(action_branch_edges _ _ _ _ _ step).2.2.2, List.append_assoc] using ih

theorem Trace.nonempty {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) : points ≠ [] := by
  cases trace <;> simp

theorem Trace.simple_length_bound [Fintype State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Thread State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (_trace : Trace graph probe eligible first code points last tag) (simple : Simple points) :
    points.length ≤ Fintype.card State * (length + 1) := by
  simpa [Point, Fintype.card_prod] using List.Nodup.length_le_card simple

theorem Trace.code_length_lt {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) : code.length < points.length := by
  induction trace with
  | done => simp
  | next _ _ ih => simp only [List.length_cons]; omega
  | left _ _ ih => simp only [List.length_cons]; omega
  | right _ _ ih => simp only [List.length_cons]; omega

/-- Starting at the same graph thread, accepting choice codes are prefix-free.
In particular a code determines captures and the terminal, not just recognition.
Nullable cycles need not be ruled out for this finite-path theorem. -/
theorem Trace.prefix_free {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag) :
    ∀ {otherCode otherPoints otherLast otherTag},
      Trace graph probe eligible first otherCode otherPoints otherLast otherTag →
      (code <+: otherCode ∨ otherCode <+: code) →
      code = otherCode ∧ last = otherLast ∧ tag = otherTag := by
  induction trace with
  | done step allowed =>
      intro otherCode otherPoints otherLast otherTag other _
      cases other <;> simp_all
  | next step next ih =>
      intro otherCode otherPoints otherLast otherTag other comparable
      cases other <;> simp_all
      exact ih (by assumption) comparable
  | left step next ih =>
      intro otherCode otherPoints otherLast otherTag other comparable
      cases other <;> simp_all
      exact ih (by assumption) comparable
  | right step next ih =>
      intro otherCode otherPoints otherLast otherTag other comparable
      cases other <;> simp_all
      exact ih (by assumption) comparable

theorem higherPriority_irrefl (code : List Bool) : ¬ HigherPriority code code := by
  intro priority
  induction code with
  | nil => cases priority
  | cons bit code ih => cases priority with
    | «prefix» _ smaller => exact ih smaller

theorem higherPriority_asymm {first second : List Bool}
    (priority : HigherPriority first second) : ¬ HigherPriority second first := by
  induction priority with
  | branch left right => intro reverse; cases reverse
  | «prefix» bit priority ih =>
      intro reverse
      cases reverse with
      | «prefix» _ smaller => exact ih smaller

/-- An independently quantified least simple accepting path. It neither
defines nor presupposes which result a memoized executor returns. -/
def LeastSimple (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (first last : Thread State length) : Prop :=
  ∃ code points tag, Trace graph probe eligible first code points last tag ∧ Simple points ∧
    ∀ otherCode otherPoints otherLast otherTag,
      Trace graph probe eligible first otherCode otherPoints otherLast otherTag → Simple otherPoints →
        code = otherCode ∨ HigherPriority code otherCode

theorem leastSimple_unique (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (first left right : Thread State length)
    (leftLeast : LeastSimple graph probe eligible first left)
    (rightLeast : LeastSimple graph probe eligible first right) : left = right := by
  obtain ⟨leftCode, leftPoints, leftTag, leftTrace, leftSimple, leftMin⟩ := leftLeast
  obtain ⟨rightCode, rightPoints, rightTag, rightTrace, rightSimple, rightMin⟩ := rightLeast
  rcases leftMin _ _ _ _ rightTrace rightSimple with same | priority
  · exact (leftTrace.prefix_free rightTrace (Or.inl (by simp [same]))).2.1
  · rcases rightMin _ _ _ _ leftTrace leftSimple with same | reverse
    · exact False.elim (higherPriority_irrefl _ (same ▸ priority))
    · exact False.elim (higherPriority_asymm priority reverse)

/-- All finite choice codes up to a bound. This is an explicit finite carrier,
not an assumption that unrestricted lexicographic path order is well-founded. -/
def boundedCodes : Nat → Finset (List Bool)
  | 0 => {[]}
  | bound + 1 => insert []
      (((boundedCodes bound).image (false :: ·)) ∪ ((boundedCodes bound).image (true :: ·)))

theorem mem_boundedCodes (bound : Nat) (code : List Bool) :
    code ∈ boundedCodes bound ↔ code.length ≤ bound := by
  induction bound generalizing code with
  | zero => cases code <;> simp [boundedCodes]
  | succ bound ih =>
      cases code with
      | nil => simp [boundedCodes]
      | cons bit rest => cases bit <;> simp [boundedCodes, ih]

theorem lex_higher_or_prefix {first second : List Bool}
    (less : List.Lex (· < ·) first second) : HigherPriority first second ∨ first <+: second := by
  induction first generalizing second with
  | nil => exact Or.inr (by simp)
  | cons bit rest ih =>
      cases second with
      | nil => cases less
      | cons other tail =>
          cases less with
          | rel lower =>
              cases bit with
              | false =>
                  cases other with
                  | false => simp at lower
                  | true => exact Or.inl (HigherPriority.branch rest tail)
              | true =>
                  cases other with
                  | false => exact False.elim ((by decide : ¬ true < false) lower)
                  | true => exact False.elim ((by decide : ¬ true < true) lower)
          | cons equalTail =>
              rcases ih equalTail with priority | pref
              · exact Or.inl (.prefix _ priority)
              · exact Or.inr (by simpa using pref)

/-- On a finite graph/input, every inhabited simple accepting-path relation
has a unique least observable thread. The finite bound is earned by point
simplicity; it is not a bound imposed on the source regex language. -/
theorem leastSimple_exists [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (first : Thread State length)
    (inhabited : ∃ code points last tag,
      Trace graph probe eligible first code points last tag ∧ Simple points) :
    ∃ last, LeastSimple graph probe eligible first last := by
  classical
  let candidates := (boundedCodes (Fintype.card State * (length + 1))).filter
    (fun code => ∃ points last tag, Trace graph probe eligible first code points last tag ∧ Simple points)
  have candidateOf : ∀ code points last tag,
      Trace graph probe eligible first code points last tag → Simple points → code ∈ candidates := by
    intro code points last tag trace simple
    refine Finset.mem_filter.mpr ⟨?_, points, last, tag, trace, simple⟩
    apply (mem_boundedCodes _ _).mpr
    have small := trace.code_length_lt
    have bounded := trace.simple_length_bound simple
    omega
  have nonempty : candidates.Nonempty := by
    obtain ⟨code, points, last, tag, trace, simple⟩ := inhabited
    exact ⟨code, candidateOf _ _ _ _ trace simple⟩
  have member := Finset.min'_mem candidates nonempty
  obtain ⟨points, last, tag, trace, simple⟩ := (Finset.mem_filter.mp member).2
  refine ⟨last, candidates.min' nonempty, points, tag, trace, simple, ?_⟩
  intro otherCode otherPoints otherLast otherTag other otherSimple
  have order := Finset.min'_le candidates otherCode (candidateOf _ _ _ _ other otherSimple)
  rcases order.eq_or_lt with same | less
  · exact Or.inl same
  · rcases lex_higher_or_prefix less with priority | pref
    · exact Or.inr priority
    · have same := (trace.prefix_free other (Or.inl pref)).1
      exact False.elim (lt_irrefl _ (same ▸ less))

theorem leastSimple_exists_unique [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (first : Thread State length)
    (inhabited : ∃ code points last tag,
      Trace graph probe eligible first code points last tag ∧ Simple points) :
    ∃! last, LeastSimple graph probe eligible first last := by
  obtain ⟨last, least⟩ := leastSimple_exists graph probe eligible first inhabited
  exact ⟨last, least, fun other otherLeast => leastSimple_unique graph probe eligible first other last otherLeast least⟩

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {count : Nat} (state : Fin count) (length : Nat) : Thread (Fin count) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def observed {State : Type} {Tag : Type} {length : Nat} :
    RegexPikeVM.Result (Thread State length) Tag → Option (Nat × Option Nat × List Bool)
  | .incomplete | .finished none => none
  | .finished (some (thread, _)) =>
      some (thread.point.2.val, (thread.registers 0).map Fin.val, thread.choices)

private def nullableRotation : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .choice 3 4
  | 3 => .jump 1
  | _ => .accept ()

private def rotationLast : Thread (Fin 5) 0 :=
  (((initial 0 0).branch 1 false).saved 2 0).branch 4 true

theorem nullable_rotation_has_simple_accepting_path :
    Trace nullableRotation (probe 0) (fun _ => true) (initial 0 0)
      [false, true] [(0, 0), (1, 0), (2, 0), (4, 0)] rotationLast () ∧
      Simple ([(0, 0), (1, 0), (2, 0), (4, 0)] : List (Point (Fin 5) 0)) := by
  refine ⟨.left rfl (.next rfl (.right rfl (.done rfl rfl))), ?_⟩
  simp [Simple]

theorem nullable_rotation_selects_the_simple_exit :
    observed (RegexPikeVM.run nullableRotation (probe 0) (fun _ => true) 24 1 [initial 0 0]) =
      some (0, some 0, [false, true]) := by decide

private def consumingReentry : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .choice 3 4
  | 3 => .consume () 1
  | _ => .accept ()

theorem a_new_position_permits_reentry_and_overwrites_capture :
    observed (RegexPikeVM.run consumingReentry (probe 2) RegexPikeVM.atInputEnd 24 3 [initial 0 2]) =
      some (2, some 2, [false, false, false, true]) := by decide

theorem global_node_only_suppression_loses_a_real_full_match :
    let first : Thread (Fin 5) 2 := initial 0 2
    let eligible := fun thread =>
      (RegexPikeVM.terminal consumingReentry thread).isSome && RegexPikeVM.atInputEnd thread
    (firstVisits (fun thread => thread.point.1) (edges consumingReentry (probe 2)) eligible
      60 [first] ∅).map List.length = some 0 ∧
    (firstVisits (fun thread => thread.point) (edges consumingReentry (probe 2)) eligible
      60 [first] ∅).map List.length = some 1 := by decide

private def captureCollision : Fin 4 → Node (Fin 4) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 2
  | 1 => .save 0 3
  | 2 => .save 1 3
  | _ => .accept ()

private def captureEligible (thread : Thread (Fin 4) 0) : Bool := (thread.registers 1).isSome

/-- Control-independent instructions do not suffice when eligibility itself
inspects captures: ordinary first-visit merging can discard an eligible path. -/
theorem capture_dependent_eligibility_invalidates_general_completeness :
    let first : Thread (Fin 4) 0 := initial 0 0
    let last := (first.branch 2 true).saved 3 1
    Trace captureCollision (probe 0) captureEligible first [true]
      [(0, 0), (2, 0), (3, 0)] last () ∧
    Simple ([(0, 0), (2, 0), (3, 0)] : List (Point (Fin 4) 0)) ∧
    RegexPikeVM.run captureCollision (probe 0) captureEligible 20 1 [first] = .finished none := by
  refine ⟨.right rfl (.next rfl (.done rfl rfl)), ?_, ?_⟩
  · simp [Simple]
  · rfl

theorem capture_dependent_eligibility_can_hide_the_least_simple_path :
    ∃ last, LeastSimple captureCollision (probe 0) captureEligible (initial 0 0) last ∧
      RegexPikeVM.run captureCollision (probe 0) captureEligible 20 1 [initial 0 0] = .finished none := by
  have counterexample := capture_dependent_eligibility_invalidates_general_completeness
  obtain ⟨last, least⟩ := leastSimple_exists captureCollision (probe 0) captureEligible (initial 0 0)
    ⟨_, _, _, _, counterexample.1, counterexample.2.1⟩
  exact ⟨last, least, counterexample.2.2⟩

end Controls

#print axioms Trace.prefix_free
#print axioms leastSimple_unique
#print axioms leastSimple_exists_unique
#print axioms Controls.capture_dependent_eligibility_invalidates_general_completeness

end Mettapedia.Computability.RegularLanguages.RegexSelectionCorrespondence
