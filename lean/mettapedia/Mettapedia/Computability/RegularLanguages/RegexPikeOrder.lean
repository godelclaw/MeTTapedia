import Mettapedia.Computability.RegularLanguages.RegexPikeSimple

/-!
# Priority order of actual Pike frontiers

The first-visit closure preserves strict branch-code order. Epsilon expansion
can append choices, but cannot reverse a previously divergent decision. An
emitted frontier node has no epsilon children. These local facts suffice for
the actual closure's ordered output without any semantic selection premise.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeOrder

open RegexTaggedGraph RegexPikeSelection RegexPikeSimple
open RegexMatchObservations (HigherPriority)
open OrderedGraphSearch (Probe)

universe u v w z

section Scheduler

variable {Value : Type u} {Key : Type v} [DecidableEq Key]

theorem firstVisits_ordered (key : Value → Key) (children : Value → List Value)
    (emit : Value → Bool) (before : Value → Value → Prop)
    (childrenOrdered : ∀ current, (children current).Pairwise before)
    (lower : ∀ current next, next ∈ children current →
      ∀ other, before current other → before next other)
    (upper : ∀ current next, next ∈ children current →
      ∀ other, before other current → before other next)
    (frontier : ∀ current, emit current = true → children current = [])
    (fuel : Nat) :
    ∀ pending seen output, pending.Pairwise before →
      firstVisits key children emit fuel pending seen = some output → output.Pairwise before := by
  induction fuel with
  | zero => simp [firstVisits]
  | succ fuel ih =>
      intro pending seen output ordered closed
      cases pending with
      | nil => simp only [firstVisits, Option.some.injEq] at closed; subst output; simp
      | cons current rest =>
          have headOrder := (List.pairwise_cons.mp ordered).1
          have tailOrder := (List.pairwise_cons.mp ordered).2
          by_cases visited : key current ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte] at closed
            exact ih rest seen output tailOrder closed
          · simp only [firstVisits, visited, ↓reduceIte] at closed
            cases next : firstVisits key children emit fuel (children current ++ rest)
                (insert (key current) seen) with
            | none => simp [next] at closed
            | some later =>
                have scheduled : (children current ++ rest).Pairwise before := by
                  apply List.pairwise_append.mpr
                  refine ⟨childrenOrdered current, tailOrder, ?_⟩
                  intro child childMember other otherMember
                  exact lower current child childMember other (headOrder other otherMember)
                have laterOrder := ih _ _ later scheduled next
                simp only [next, Option.map_some, Option.some.injEq] at closed
                subst output
                cases emitted : emit current with
                | false => simpa [emitted] using laterOrder
                | true =>
                    have noChildren := frontier current emitted
                    have after : ∀ value ∈ later, before current value := by
                      apply fun value member =>
                        (firstVisits_sound key children emit (before current) ?_ fuel
                          (children current ++ rest) (insert (key current) seen) later ?_ next
                          value member).1
                      · intro source valid target edge
                        exact upper source target edge current valid
                      · simpa only [noChildren, List.nil_append] using headOrder
                    simpa [emitted] using List.pairwise_cons.mpr ⟨after, laterOrder⟩

end Scheduler

section CandidatePosition

variable {Value : Type u} {Tag' : Type v}

theorem candidates_active_ordered (accepts : Value → Option Tag')
    (eligible : Value → Bool) (before : Value → Value → Prop) (frontier : List Value)
    (ordered : frontier.Pairwise before) :
    (RegexPikeVM.candidates accepts eligible frontier).1.Pairwise before := by
  induction frontier with
  | nil => simp [RegexPikeVM.candidates]
  | cons first rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      cases accepted : accepts first with
      | some tag =>
          cases allowed : eligible first <;>
            simp [RegexPikeVM.candidates, accepted, allowed, ih tail]
      | none =>
          simp only [RegexPikeVM.candidates, accepted, List.pairwise_cons]
          exact ⟨fun value member => head value
            (RegexPikeVM.candidates_active_mem accepts eligible rest value member).1, ih tail⟩

/-- A nonterminal is retained unless a strictly earlier eligible terminal cuts
off its position. The premise concerns the actual ordered frontier. -/
theorem candidates_retains_active (accepts : Value → Option Tag')
    (eligible : Value → Bool) (before : Value → Value → Prop) (frontier : List Value)
    (reference : Value) (ordered : frontier.Pairwise before) (member : reference ∈ frontier)
    (nonterminal : accepts reference = none)
    (noEarlier : ∀ value ∈ frontier, ∀ tag, accepts value = some tag →
      eligible value = true → ¬before value reference) :
    reference ∈ (RegexPikeVM.candidates accepts eligible frontier).1 := by
  induction frontier with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      have tailNoEarlier : ∀ value ∈ rest, ∀ tag, accepts value = some tag →
          eligible value = true → ¬before value reference := by
        intro value member tag accepted allowed
        exact noEarlier value (List.mem_cons_of_mem _ member) tag accepted allowed
      rcases List.mem_cons.mp member with same | member
      · subst reference
        simp [RegexPikeVM.candidates, nonterminal]
      · cases accepted : accepts first with
        | none =>
            simp only [RegexPikeVM.candidates, accepted, List.mem_cons]
            exact Or.inr (ih tail member tailNoEarlier)
        | some tag =>
            cases allowed : eligible first with
            | false =>
                simpa [RegexPikeVM.candidates, accepted, allowed] using
                  ih tail member tailNoEarlier
            | true =>
                exact False.elim (noEarlier first (by simp) tag accepted allowed
                  (head reference member))

/-- An eligible terminal is selected unless a strictly earlier eligible
terminal has already been encountered. -/
theorem candidates_selects_reference (accepts : Value → Option Tag')
    (eligible : Value → Bool) (before : Value → Value → Prop) (frontier : List Value)
    (reference : Value) (tag : Tag') (ordered : frontier.Pairwise before)
    (member : reference ∈ frontier) (accepted : accepts reference = some tag)
    (allowed : eligible reference = true)
    (noEarlier : ∀ value ∈ frontier, ∀ found, accepts value = some found →
      eligible value = true → ¬before value reference) :
    (RegexPikeVM.candidates accepts eligible frontier).2 = some (reference, tag) := by
  induction frontier with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      have tailNoEarlier : ∀ value ∈ rest, ∀ found, accepts value = some found →
          eligible value = true → ¬before value reference := by
        intro value member found terminal permission
        exact noEarlier value (List.mem_cons_of_mem _ member) found terminal permission
      rcases List.mem_cons.mp member with same | member
      · subst reference
        simp [RegexPikeVM.candidates, accepted, allowed]
      · cases terminal : accepts first with
        | none =>
            simpa [RegexPikeVM.candidates, terminal] using ih tail member tailNoEarlier
        | some found =>
            cases permission : eligible first with
            | false =>
                simpa [RegexPikeVM.candidates, terminal, permission] using
                  ih tail member tailNoEarlier
            | true =>
                exact False.elim (noEarlier first (by simp) found terminal permission
                  (head reference member))

theorem candidates_active_before_selected (accepts : Value → Option Tag')
    (eligible : Value → Bool) (before : Value → Value → Prop) (frontier : List Value)
    (reference : Value) (tag : Tag') (ordered : frontier.Pairwise before)
    (selected : (RegexPikeVM.candidates accepts eligible frontier).2 = some (reference, tag)) :
    ∀ value ∈ (RegexPikeVM.candidates accepts eligible frontier).1, before value reference := by
  induction frontier with
  | nil => simp [RegexPikeVM.candidates] at selected
  | cons first rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      cases accepted : accepts first with
      | some found =>
          cases allowed : eligible first with
          | true => simp [RegexPikeVM.candidates, accepted, allowed]
          | false =>
              simp only [RegexPikeVM.candidates, accepted, allowed, Bool.false_eq_true,
                ↓reduceIte] at selected ⊢
              exact ih tail selected
      | none =>
          simp only [RegexPikeVM.candidates, accepted] at selected ⊢
          intro value member
          rcases List.mem_cons.mp member with same | member
          · subst value
            exact head reference
              (RegexPikeVM.candidates_selected_sound accepts eligible rest reference tag selected).1
          · exact ih tail selected value member

end CandidatePosition

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def Before (first second : Thread State length) : Prop := HigherPriority first.choices second.choices

theorem edge_choices_extension (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (current next : Thread State length)
    (edge : next ∈ edges graph probe current) :
    ∃ suffix, next.choices = current.choices ++ suffix := by
  obtain ⟨code, history⟩ := prefix_of_edge graph probe current next edge
  exact ⟨code, history.choices⟩

theorem epsilon_children_ordered (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (current : Thread State length) :
    (epsilonChildren graph probe current).Pairwise Before := by
  cases node : graph current.point.1 with
  | choice first second =>
      have ordered : Before (current.branch first false) (current.branch second true) :=
        priority_common_prefix current.choices (.branch [] [])
      simpa [epsilonChildren, node, edges] using ordered
  | assertion assertion_ next =>
      simp only [epsilonChildren, node, edges]
      split <;> simp
  | accept _ | consume _ _ | dead | jump _ | save _ _ => simp [epsilonChildren, node, edges]

theorem epsilon_extends_before (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (current next other : Thread State length)
    (edge : next ∈ epsilonChildren graph probe current) (before : Before current other) : Before next other := by
  obtain ⟨suffix, same⟩ := edge_choices_extension graph probe current next (epsilon_edge graph probe current next edge)
  dsimp only [Before] at *
  rw [same]
  simpa only [List.append_nil] using priority_append before suffix []

theorem epsilon_extends_after (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (current next other : Thread State length)
    (edge : next ∈ epsilonChildren graph probe current) (before : Before other current) : Before other next := by
  obtain ⟨suffix, same⟩ := edge_choices_extension graph probe current next (epsilon_edge graph probe current next edge)
  dsimp only [Before] at *
  rw [same]
  simpa only [List.append_nil] using priority_append before [] suffix

theorem close_ordered [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (fuel : Nat) (pending output : List (Thread State length))
    (ordered : pending.Pairwise Before) (closed : close graph probe fuel pending = some output) :
    output.Pairwise Before := by
  apply firstVisits_ordered (fun thread : Thread State length => thread.point.1)
    (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1)) Before
    (epsilon_children_ordered graph probe) ?_ ?_ ?_ fuel pending ∅ output ordered closed
  · intro current next edge other before
    exact epsilon_extends_before graph probe current next other edge before
  · intro current next edge other before
    exact epsilon_extends_after graph probe current next other edge before
  · intro current frontier
    cases node : graph current.point.1 <;> simp_all [isFrontier, epsilonChildren]

theorem consuming_edges_properties (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (current : Thread State length)
    (frontier : isFrontier (graph current.point.1) = true)
    (nonterminal : RegexPikeVM.terminal graph current = none) :
    (edges graph probe current).Pairwise Before ∧
      ∀ next ∈ edges graph probe current, next.choices = current.choices := by
  cases node : graph current.point.1 with
  | dead | jump _ | choice _ _ | assertion _ _ | save _ _ =>
      simp [isFrontier, node] at frontier
  | accept tag => simp [RegexPikeVM.terminal, node] at nonterminal
  | consume class_ next =>
      simp only [edges, node]
      split
      · cases OrderedGraphSearch.successor current.point.2 <;> simp
      · simp

theorem consume_ordered (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (active : List (Thread State length))
    (ordered : active.Pairwise Before)
    (valid : ∀ current ∈ active, isFrontier (graph current.point.1) = true ∧
      RegexPikeVM.terminal graph current = none) :
    (active.flatMap (edges graph probe)).Pairwise Before := by
  induction active with
  | nil => simp
  | cons current rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      have currentValid := valid current (by simp)
      have properties := consuming_edges_properties graph probe current currentValid.1 currentValid.2
      have tailValid : ∀ value ∈ rest, isFrontier (graph value.point.1) = true ∧
          RegexPikeVM.terminal graph value = none := by
        intro value member
        exact valid value (List.mem_cons_of_mem _ member)
      simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨properties.1, ih tail tailValid, ?_⟩
      intro first firstMember second secondMember
      obtain ⟨source, sourceMember, sourceEdge⟩ := List.mem_flatMap.mp secondMember
      have sourceValid := tailValid source sourceMember
      have sourceProperties := consuming_edges_properties graph probe source sourceValid.1 sourceValid.2
      dsimp only [Before]
      rw [properties.2 first firstMember, sourceProperties.2 second sourceEdge]
      exact head source sourceMember

theorem advancing_ordered [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (fuel : Nat)
    (pending frontier : List (Thread State length))
    (ordered : pending.Pairwise Before) (closed : close graph probe fuel pending = some frontier) :
    ((RegexPikeVM.candidates (RegexPikeVM.terminal graph) eligible frontier).1.flatMap
      (edges graph probe)).Pairwise Before := by
  apply consume_ordered graph probe _
    (candidates_active_ordered _ _ _ _ (close_ordered graph probe fuel pending frontier ordered closed))
  intro current member
  have active := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph) eligible frontier current member
  exact ⟨(firstVisits_sound (fun thread : Thread State length => thread.point.1)
    (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
    (fun _ => True) (by simp) fuel pending ∅ frontier (by simp) closed current active.1).2, active.2⟩

namespace Controls

private def accepts (value : Nat) : Option Nat := if value = 2 then some 7 else none

theorem earlier_consumers_remain_active :
    (RegexPikeVM.candidates accepts (fun _ => true) [0, 1, 2, 3]).1 = [0, 1] := by decide

theorem ineligible_terminal_does_not_cut_consumers :
    RegexPikeVM.candidates accepts (fun _ => false) [0, 2, 1] = ([0, 1], none) := by decide

theorem later_consumers_are_not_retained :
    3 ∉ (RegexPikeVM.candidates accepts (fun _ => true) [0, 1, 2, 3]).1 := by decide

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPikeOrder
