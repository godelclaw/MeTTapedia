import Mettapedia.GSLT.LanguageDef.RegexSelectionGraph
import Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence
import Mettapedia.GSLT.LanguageDef.RegexRelationEnumeration

/-!
# Finite literal-graph admission and exact ordered executions

An admission plan names the actual program counters and verifies their actual
instructions. Its interpretation is independent of Pike scheduling. Choices
retain order and duplicates, jumps are administrative, and no instruction can
write a capture. The explicit acyclicity condition concerns program counters,
not a default work bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexLiteralGraphPlan

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe successor)
open RegexMatchObservations (HigherPriority)
open RegexRelationEnumeration (Occurrence prepend)

universe u v

inductive Plan (State : Type u) where
  | fail (state : State)
  | accept (state : State)
  | jump (state : State) (child : Plan State)
  | scalar (state : State) (value : Nat) (child : Plan State)
  | branch (state : State) (first second : Plan State)

def root {State : Type u} : Plan State → State
  | .fail state | .accept state | .jump state _ | .scalar state _ _ | .branch state _ _ => state

def states {State : Type u} : Plan State → List State
  | .fail state | .accept state => [state]
  | .jump state child | .scalar state _ child => state :: states child
  | .branch state first second => state :: (states first ++ states second)

def Valid {State : Type u}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit) : Plan State → Prop
  | .fail state => graph state = .dead
  | .accept state => graph state = .accept ()
  | .jump state child => graph state = .jump (root child) ∧ Valid graph child
  | .scalar state value child => graph state = .consume (.scalar value) (root child) ∧ Valid graph child
  | .branch state first second =>
      graph state = .choice (root first) (root second) ∧ Valid graph first ∧ Valid graph second

def Acyclic {State : Type u} : Plan State → Prop
  | .fail _ | .accept _ => True
  | .jump state child | .scalar state _ child => state ∉ states child ∧ Acyclic child
  | .branch state first second =>
      state ∉ states first ∧ state ∉ states second ∧ Acyclic first ∧ Acyclic second

abbrev Answer (State : Type u) (length : Nat) := Occurrence (Thread State length) (Point State length)

def evaluate {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (first : Thread State length) :
    List (Answer State length) :=
  match plan with
  | .fail _ => []
  | .accept _ => if eligible first then [⟨first, [], [first.point]⟩] else []
  | .jump _ child =>
      (evaluate probe eligible child (first.at (root child))).map (prepend [] first.point)
  | .scalar _ value child =>
      if probe.contains (.scalar value) first.point.2 then
        match successor first.point.2 with
        | none => []
        | some position =>
            (evaluate probe eligible child {first with point := (root child, position)}).map
              (prepend [] first.point)
      else []
  | .branch _ left right =>
      (evaluate probe eligible left (first.branch (root left) false)).map (prepend [false] first.point) ++
      (evaluate probe eligible right (first.branch (root right) true)).map (prepend [true] first.point)
termination_by plan

theorem evaluate_sound {State : Type u} {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (first : Thread State length) (entry : first.point.1 = root plan) (answer : Answer State length)
    (present : answer ∈ evaluate probe eligible plan first) :
    Trace graph probe eligible first answer.choices answer.points answer.value () := by
  induction plan generalizing first answer with
  | fail state => simp [evaluate] at present
  | accept state =>
      cases allowed : eligible first
      · simp [evaluate, allowed] at present
      · simp [evaluate, allowed] at present
        subst answer
        have node : graph state = .accept () := valid
        exact .done (by simp [action, entry, root, node]) allowed
  | jump state child ih =>
      simp only [evaluate] at present
      obtain ⟨result, member, rfl⟩ := List.mem_map.mp present
      have next := ih valid.2 (first.at (root child)) rfl result member
      exact .next (by simp [action, entry, root, valid.1]) next
  | scalar state value child ih =>
      cases contains : probe.contains (.scalar value) first.point.2
      · simp [evaluate, contains] at present
      · cases advanced : successor first.point.2 with
        | none => simp [evaluate, contains, advanced] at present
        | some position =>
            simp only [evaluate, contains, ↓reduceIte, advanced, List.mem_map] at present
            obtain ⟨result, member, rfl⟩ := present
            have next := ih valid.2 {first with point := (root child, position)} rfl result member
            exact .next (by simp [action, entry, root, valid.1, contains, advanced]) next
  | branch state left right ihLeft ihRight =>
      simp only [evaluate] at present
      rcases List.mem_append.mp present with leftMember | rightMember
      · obtain ⟨result, member, rfl⟩ := List.mem_map.mp leftMember
        have next := ihLeft valid.2.1 (first.branch (root left) false) rfl result member
        exact .left (left := first.branch (root left) false)
          (right := first.branch (root right) true) (by simp [action, entry, root, valid.1]) next
      · obtain ⟨result, member, rfl⟩ := List.mem_map.mp rightMember
        have next := ihRight valid.2.2 (first.branch (root right) true) rfl result member
        exact .right (left := first.branch (root left) false)
          (right := first.branch (root right) true) (by simp [action, entry, root, valid.1]) next

theorem evaluate_complete {State : Type u} {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (first : Thread State length) (entry : first.point.1 = root plan)
    (bits : List Bool) (points : List (Point State length)) (last : Thread State length)
    (trace : Trace graph probe eligible first bits points last ()) :
    (⟨last, bits, points⟩ : Answer State length) ∈ evaluate probe eligible plan first := by
  induction plan generalizing first bits points last with
  | fail state =>
      have node : graph state = .dead := valid
      have operation : action graph probe first = .dead := by simp [action, entry, root, node]
      cases trace <;> simp_all
  | accept state =>
      have node : graph state = .accept () := valid
      have operation : action graph probe first = .accept () := by simp [action, entry, root, node]
      cases trace <;> simp_all [evaluate]
  | jump state child ih =>
      have operation : action graph probe first = .next (first.at (root child)) := by
        simp [action, entry, root, valid.1]
      cases trace with
      | done step allowed => simp [operation] at step
      | next step tail =>
          cases Action.next.inj (operation.symm.trans step)
          simp only [evaluate]
          exact List.mem_map.mpr ⟨_, ih valid.2 _ rfl _ _ _ tail, rfl⟩
      | left step tail => simp [operation] at step
      | right step tail => simp [operation] at step
  | scalar state value child ih =>
      have operation : action graph probe first =
          if probe.contains (.scalar value) first.point.2 then
            match successor first.point.2 with
            | none => .dead
            | some position => .next {first with point := (root child, position)}
          else .dead := by
        simp only [action, entry, root, valid.1]
        cases probe.contains (.scalar value) first.point.2 <;>
          cases successor first.point.2 <;> rfl
      cases contains : probe.contains (.scalar value) first.point.2
      · simp [contains] at operation
        cases trace <;> simp_all
      · cases advanced : successor first.point.2 with
        | none =>
            simp [contains, advanced] at operation
            cases trace <;> simp_all
        | some position =>
            simp only [contains, ↓reduceIte, advanced] at operation
            cases trace with
            | done step allowed => simp [operation] at step
            | next step tail =>
                cases Action.next.inj (operation.symm.trans step)
                simp only [evaluate, contains, ↓reduceIte, advanced, List.mem_map]
                exact ⟨_, ih valid.2 _ rfl _ _ _ tail, rfl⟩
            | left step tail => simp [operation] at step
            | right step tail => simp [operation] at step
  | branch state left right ihLeft ihRight =>
      have operation : action graph probe first =
          .branch (first.branch (root left) false) (first.branch (root right) true) := by
        simp [action, entry, root, valid.1]
      cases trace with
      | done step allowed => simp [operation] at step
      | next step tail => simp [operation] at step
      | left step tail =>
          obtain ⟨leftSame, rightSame⟩ := Action.branch.inj (operation.symm.trans step)
          cases leftSame
          cases rightSame
          simp only [evaluate]
          exact List.mem_append_left _ (List.mem_map.mpr
            ⟨_, ihLeft valid.2.1 _ rfl _ _ _ tail, rfl⟩)
      | right step tail =>
          obtain ⟨leftSame, rightSame⟩ := Action.branch.inj (operation.symm.trans step)
          cases leftSame
          cases rightSame
          simp only [evaluate]
          exact List.mem_append_right _ (List.mem_map.mpr
            ⟨_, ihRight valid.2.2 _ rfl _ _ _ tail, rfl⟩)

theorem evaluate_trace_iff {State : Type u} {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (first : Thread State length) (entry : first.point.1 = root plan) (answer : Answer State length) :
    answer ∈ evaluate probe eligible plan first ↔
      Trace graph probe eligible first answer.choices answer.points answer.value () := by
  constructor
  · exact evaluate_sound graph probe eligible plan valid first entry answer
  · exact evaluate_complete graph probe eligible plan valid first entry
      answer.choices answer.points answer.value

private theorem parent_simple {State : Type u} {length : Nat}
    (parent : State) (child : Plan State) (first : Thread State length)
    (entry : first.point.1 = parent) (fresh : parent ∉ states child)
    (answer : Answer State length)
    (supported : ∀ point ∈ answer.points, point.1 ∈ states child)
    (simple : answer.points.Nodup) : (first.point :: answer.points).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, simple⟩
  intro member
  exact fresh (entry ▸ supported first.point member)

theorem evaluate_properties {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (acyclic : Acyclic plan)
    (first : Thread State length) (entry : first.point.1 = root plan) (answer : Answer State length)
    (present : answer ∈ evaluate probe eligible plan first) :
    (∀ point ∈ answer.points, point.1 ∈ states plan) ∧ answer.points.Nodup ∧
      answer.value.registers = first.registers := by
  induction plan generalizing first answer with
  | fail state => simp [evaluate] at present
  | accept state =>
      cases allowed : eligible first
      · simp [evaluate, allowed] at present
      · simp [evaluate, allowed] at present
        subst answer
        refine ⟨?_, by simp, rfl⟩
        intro point member
        simp only [List.mem_singleton] at member
        subst point
        simpa [states, root] using entry
  | jump state child ih =>
      simp only [evaluate, List.mem_map] at present
      obtain ⟨result, member, rfl⟩ := present
      obtain ⟨support, simple, registers⟩ := ih acyclic.2 (first.at (root child)) rfl result member
      refine ⟨?_, parent_simple state child first entry acyclic.1 result support simple, registers⟩
      intro point member
      rcases List.mem_cons.mp member with rfl | member
      · simp [states, entry, root]
      · exact List.mem_cons_of_mem _ (support point member)
  | scalar state value child ih =>
      cases contains : probe.contains (.scalar value) first.point.2
      · simp [evaluate, contains] at present
      · cases advanced : successor first.point.2 with
        | none => simp [evaluate, contains, advanced] at present
        | some position =>
            simp only [evaluate, contains, ↓reduceIte, advanced, List.mem_map] at present
            obtain ⟨result, member, rfl⟩ := present
            obtain ⟨support, simple, registers⟩ :=
              ih acyclic.2 {first with point := (root child, position)} rfl result member
            refine ⟨?_, parent_simple state child first entry acyclic.1 result support simple, registers⟩
            intro point member
            rcases List.mem_cons.mp member with rfl | member
            · simp [states, entry, root]
            · exact List.mem_cons_of_mem _ (support point member)
  | branch state left right ihLeft ihRight =>
      simp only [evaluate, List.mem_append, List.mem_map] at present
      rcases present with ⟨result, member, rfl⟩ | ⟨result, member, rfl⟩
      · obtain ⟨support, simple, registers⟩ :=
          ihLeft acyclic.2.2.1 (first.branch (root left) false) rfl result member
        refine ⟨?_, parent_simple state left first entry acyclic.1 result support simple, registers⟩
        intro point member
        rcases List.mem_cons.mp member with rfl | member
        · simp [states, entry, root]
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (support point member))
      · obtain ⟨support, simple, registers⟩ :=
          ihRight acyclic.2.2.2 (first.branch (root right) true) rfl result member
        refine ⟨?_, parent_simple state right first entry acyclic.2.1 result support simple, registers⟩
        intro point member
        rcases List.mem_cons.mp member with rfl | member
        · simp [states, entry, root]
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (support point member))

private theorem prefixed_pairwise (bit : Bool) (codes : List (List Bool))
    (ordered : codes.Pairwise HigherPriority) :
    (codes.map (bit :: ·)).Pairwise HigherPriority := by
  rw [List.pairwise_map]
  exact ordered.imp (fun preferred => HigherPriority.prefix bit preferred)

private theorem branch_pairwise (left right : List (List Bool))
    (leftOrdered : left.Pairwise HigherPriority) (rightOrdered : right.Pairwise HigherPriority) :
    ((left.map (false :: ·)) ++ (right.map (true :: ·))).Pairwise HigherPriority := by
  rw [List.pairwise_append]
  refine ⟨prefixed_pairwise false left leftOrdered, prefixed_pairwise true right rightOrdered, ?_⟩
  intro first firstMember second secondMember
  obtain ⟨firstCode, _, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨secondCode, _, rfl⟩ := List.mem_map.mp secondMember
  exact .branch _ _

theorem evaluate_ordered {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (first : Thread State length) :
    ((evaluate probe eligible plan first).map Occurrence.choices).Pairwise HigherPriority := by
  induction plan generalizing first with
  | fail state => simp [evaluate]
  | accept state => cases allowed : eligible first <;> simp [evaluate, allowed]
  | jump state child ih =>
      simpa [evaluate, List.map_map, prepend, Function.comp_def] using ih (first.at (root child))
  | scalar state value child ih =>
      cases contains : probe.contains (.scalar value) first.point.2
      · simp [evaluate, contains]
      · cases advanced : successor first.point.2 with
        | none => simp [evaluate, contains, advanced]
        | some position =>
            simpa [evaluate, contains, advanced, List.map_map, prepend, Function.comp_def] using
              ih {first with point := (root child, position)}
  | branch state left right ihLeft ihRight =>
      simpa [evaluate, List.map_append, List.map_map, prepend, Function.comp_def] using
        branch_pairwise
          ((evaluate probe eligible left (first.branch (root left) false)).map Occurrence.choices)
          ((evaluate probe eligible right (first.branch (root right) true)).map Occurrence.choices)
          (ihLeft _) (ihRight _)

theorem evaluate_head_least {State : Type u} {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (acyclic : Acyclic plan) (first : Thread State length) (entry : first.point.1 = root plan)
    (answer : Answer State length) (rest : List (Answer State length))
    (selected : evaluate probe eligible plan first = answer :: rest) :
    LeastSimple graph probe eligible first answer.value := by
  have member : answer ∈ evaluate probe eligible plan first := by rw [selected]; simp
  refine ⟨answer.choices, answer.points, (),
    evaluate_sound graph probe eligible plan valid first entry answer member,
    (evaluate_properties probe eligible plan acyclic first entry answer member).2.1, ?_⟩
  intro code points last tag trace _
  cases tag
  have present := evaluate_complete graph probe eligible plan valid first entry code points last trace
  rw [selected] at present
  rcases List.mem_cons.mp present with same | later
  · exact Or.inl (congrArg Occurrence.choices same.symm)
  · have ordered := evaluate_ordered probe eligible plan first
    rw [selected] at ordered
    exact Or.inr ((List.pairwise_cons.mp ordered).1 _ (List.mem_map.mpr ⟨_, later, rfl⟩))

/-- A local instruction admission plus acyclicity earns the complete selected
thread, including its unchanged capture registers and exact priority history. -/
theorem pike_of_evaluate_head {State : Type u} [DecidableEq State] [Fintype State] {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Point State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (acyclic : Acyclic plan) (first : Thread State length) (entry : first.point.1 = root plan)
    (answer : Answer State length) (rest : List (Answer State length))
    (selected : evaluate probe (fun thread => eligible thread.point) plan first = answer :: rest)
    (closureFuel inputFuel : Nat) (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      .finished (some (answer.value, ())) := by
  have member : answer ∈ evaluate probe (fun thread => eligible thread.point) plan first := by
    rw [selected]; simp
  have trace := evaluate_sound graph probe (fun thread => eligible thread.point) plan valid first entry answer member
  exact (RegexPikeCorrespondence.run_leastSimple graph probe eligible first answer.value ()
    closureFuel inputFuel closureEnough inputEnough).mpr
      ⟨evaluate_head_least graph probe (fun thread => eligible thread.point) plan valid acyclic
        first entry answer rest selected, trace.sound.2.1⟩

end Mettapedia.GSLT.LanguageDef.RegexLiteralGraphPlan
