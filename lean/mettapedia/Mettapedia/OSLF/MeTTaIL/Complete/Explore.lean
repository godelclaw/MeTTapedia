import Mettapedia.OSLF.MeTTaIL.Complete.Classes

/-!
# Fair exploration of every run

The runner of `Machines.ResumableSearchRunner` follows one path: it commits the first published
receipt. A nondeterministic language needs every path. The explorer here keeps a node for every
state it has reached, each with its own retained search. A round gives every node's search one
more unit of work and turns each receipt it newly publishes into a child node, unless a node with
the child's state already exists: states are explored once, so a cycle of steps ends and a
finite reachable set is a finite explorer. No node waits for another, so a path whose first
branch never ends does not hide a later branch.

It is generic over any lawful resumable search.

- `node_chain`: every node's path is a chain of valid receipts from the source;
- `explored_target`: once a node exists, every receipt its search ever publishes yields a node;
- `explores_multistep`: for steps modulo equations, every state reachable by finitely many GSLT
  steps is explored, up to equality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Explore

open Mettapedia.Machines.ResumableSearchRunner (Search History)

variable {σ Run Receipt : Type} (S : Search σ Run Receipt)

/-- A reached state with its path, newest first, and its retained search. -/
structure Node (σ Run Receipt : Type) where
  state : σ
  receipts : List Receipt
  states : List σ
  born : Nat
  run : Run
  consumed : Nat

/-- The explorer: the round and every node. -/
structure Explorer (σ Run Receipt : Type) where
  round : Nat
  nodes : List (Node σ Run Receipt)

/-- One unit of work for a node, and the children of its newly published receipts. -/
def expand (round : Nat) (node : Node σ Run Receipt) : Node σ Run Receipt × List (Node σ Run Receipt) :=
  let next := S.resume node.run 1
  let published := S.publication next
  ({ node with run := next, consumed := published.length },
    (published.drop node.consumed).map fun receipt =>
      ⟨S.target receipt, receipt :: node.receipts, S.target receipt :: node.states, round + 1,
        S.run (S.target receipt) 0, 0⟩)

variable [DecidableEq σ]

/-- The children whose states are new: a child whose state is already `seen`, or is an earlier
child's, is dropped. -/
def fresh (seen : List σ) : List (Node σ Run Receipt) → List (Node σ Run Receipt)
  | [] => []
  | child :: rest => if child.state ∈ seen then fresh seen rest else child :: fresh (child.state :: seen) rest

theorem fresh_subset : ∀ (seen : List σ) (children : List (Node σ Run Receipt)),
    ∀ node ∈ fresh seen children, node ∈ children
  | _, [] => by simp [fresh]
  | seen, child :: rest => by
    intro node member
    simp only [fresh] at member
    split at member
    · exact List.mem_cons_of_mem _ (fresh_subset seen rest node member)
    · rcases List.mem_cons.mp member with rfl | inside
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (fresh_subset _ rest node inside)

/-- **Every dropped child has a witness**: its state was seen, or a kept child has it. -/
theorem fresh_cover : ∀ (seen : List σ) (children : List (Node σ Run Receipt)),
    ∀ child ∈ children, child.state ∈ seen ∨ ∃ node ∈ fresh seen children, node.state = child.state
  | _, [] => by simp
  | seen, first :: rest => by
    intro child member
    by_cases known : first.state ∈ seen
    · have dropped : fresh seen (first :: rest) = fresh seen rest := by simp [fresh, known]
      rw [dropped]
      rcases List.mem_cons.mp member with rfl | inside
      · exact .inl known
      · exact fresh_cover seen rest child inside
    · have kept : fresh seen (first :: rest) = first :: fresh (first.state :: seen) rest := by
        simp [fresh, known]
      rw [kept]
      rcases List.mem_cons.mp member with rfl | inside
      · exact .inr ⟨child, List.mem_cons_self, rfl⟩
      · rcases fresh_cover (first.state :: seen) rest child inside with old | ⟨node, present, same⟩
        · rcases List.mem_cons.mp old with same | earlier
          · exact .inr ⟨first, List.mem_cons_self, same.symm⟩
          · exact .inl earlier
        · exact .inr ⟨node, List.mem_cons_of_mem _ present, same⟩

/-- One round: every node gets one unit of work; children with new states join. -/
def step (explorer : Explorer σ Run Receipt) : Explorer σ Run Receipt :=
  let expanded := explorer.nodes.map (expand S explorer.round)
  let kept := expanded.map Prod.fst
  ⟨explorer.round + 1, kept ++ fresh (kept.map (·.state)) (expanded.flatMap Prod.snd)⟩

/-- The source as the only node. -/
def begin (source : σ) : Explorer σ Run Receipt := ⟨0, [⟨source, [], [source], 0, S.run source 0, 0⟩]⟩

/-- `work` rounds. -/
def explore (source : σ) : Nat → Explorer σ Run Receipt
  | 0 => begin S source
  | work + 1 => step S (explore source work)

/-- What every node of a reached explorer satisfies. -/
structure Good (source : σ) (explorer : Explorer σ Run Receipt) : Prop where
  born : ∀ node ∈ explorer.nodes, node.born ≤ explorer.round
  run : ∀ node ∈ explorer.nodes, node.run = S.run node.state (explorer.round - node.born)
  consumed : ∀ node ∈ explorer.nodes, node.consumed ≤ (S.publication node.run).length
  expanded : ∀ node ∈ explorer.nodes, node.born < explorer.round → node.consumed = (S.publication node.run).length
  path : ∀ node ∈ explorer.nodes, History S node.states node.receipts ∧ node.states.head? = some node.state ∧
    node.states.getLast? = some source
  children : ∀ node ∈ explorer.nodes, ∀ receipt ∈ (S.publication node.run).take node.consumed,
    ∃ child ∈ explorer.nodes, child.state = S.target receipt
  source : ∃ node ∈ explorer.nodes, node.state = source

variable {S}

omit [DecidableEq σ] in
theorem begin_good (source : σ) : Good S source (begin S source) where
  born node member := by simp [begin] at member; subst member; rfl
  run node member := by simp [begin] at member; subst member; rfl
  consumed node member := by simp [begin] at member; subst member; exact Nat.zero_le _
  expanded node member early := by simp [begin] at member; subst member; cases early
  path node member := by
    simp [begin] at member
    subst member
    exact ⟨.start source, rfl, rfl⟩
  children node member receipt published := by
    simp [begin] at member
    subst member
    simp at published
  source := ⟨⟨source, [], [source], 0, S.run source 0, 0⟩, by simp [begin], rfl⟩

theorem explore_round (source : σ) (work : Nat) : (explore S source work).round = work := by
  induction work with
  | zero => rfl
  | succ work ih => simp only [explore, step, ih]

theorem step_good (lawful : S.Lawful) {source : σ} {explorer : Explorer σ Run Receipt}
    (good : Good S source explorer) : Good S source (step S explorer) := by
  have memStep : ∀ node, node ∈ (step S explorer).nodes →
      (∃ old ∈ explorer.nodes, node = (expand S explorer.round old).1) ∨
        ∃ old ∈ explorer.nodes, node ∈ (expand S explorer.round old).2 := by
    intro node member
    simp only [step, List.mem_append, List.mem_map] at member
    rcases member with ⟨pair, ⟨old, present, rfl⟩, rfl⟩ | inside
    · exact .inl ⟨old, present, rfl⟩
    · obtain ⟨pair, listed, child⟩ := List.mem_flatMap.mp (fresh_subset _ _ node inside)
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp listed
      exact .inr ⟨old, present, child⟩
  have keptMem : ∀ old ∈ explorer.nodes, (expand S explorer.round old).1 ∈ (step S explorer).nodes := by
    intro old present
    simp only [step, List.mem_append, List.mem_map]
    exact .inl ⟨_, ⟨old, present, rfl⟩, rfl⟩
  have witnessed : ∀ old ∈ explorer.nodes, ∀ child ∈ (expand S explorer.round old).2,
      ∃ node ∈ (step S explorer).nodes, node.state = child.state := by
    intro old present child inside
    have listed : child ∈ (explorer.nodes.map (expand S explorer.round)).flatMap Prod.snd :=
      List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨old, present, rfl⟩, inside⟩
    rcases fresh_cover _ _ child listed with known | ⟨node, kept, same⟩
    · obtain ⟨node, keptNode, same⟩ := List.mem_map.mp known
      exact ⟨node, by simp only [step]; exact List.mem_append_left _ keptNode, same⟩
    · exact ⟨node, by simp only [step]; exact List.mem_append_right _ kept, same⟩
  have grown : ∀ old ∈ explorer.nodes,
      S.publication old.run <+: S.publication (S.resume old.run 1) := by
    intro old present
    rw [good.run old present, lawful.resume_run]
    exact lawful.publication_prefix _ _ _
  have childOf : ∀ old ∈ explorer.nodes, ∀ receipt ∈ S.publication (S.resume old.run 1),
      ∃ child ∈ (step S explorer).nodes, child.state = S.target receipt := by
    intro old present receipt published
    by_cases early : receipt ∈ (S.publication old.run).take old.consumed
    · obtain ⟨child, inNodes, same⟩ := good.children old present receipt early
      exact ⟨(expand S explorer.round child).1, keptMem child inNodes, by simp [expand, same]⟩
    · have later : receipt ∈ (S.publication (S.resume old.run 1)).drop old.consumed := by
        obtain ⟨tail, joined⟩ := grown old present
        have bounded := good.consumed old present
        rw [← joined] at published ⊢
        rw [← List.take_append_drop old.consumed (S.publication old.run ++ tail)] at published
        rcases List.mem_append.mp published with first | rest
        · rw [List.take_append_of_le_length bounded] at first
          exact absurd first early
        · exact rest
      exact witnessed old present _ (List.mem_map.mpr ⟨receipt, later, rfl⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro node member
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · exact Nat.le_succ_of_le (good.born old present)
    · obtain ⟨receipt, _, rfl⟩ := List.mem_map.mp inside
      exact Nat.le_refl _
  · intro node member
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · have bounded := good.born old present
      simp only [expand, step]
      rw [good.run old present, lawful.resume_run]
      congr 1
      omega
    · obtain ⟨receipt, _, rfl⟩ := List.mem_map.mp inside
      simp [step]
  · intro node member
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · exact Nat.le_refl _
    · obtain ⟨receipt, _, rfl⟩ := List.mem_map.mp inside
      exact Nat.zero_le _
  · intro node member _
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · rfl
    · obtain ⟨receipt, _, rfl⟩ := List.mem_map.mp inside
      simp [step] at *
  · intro node member
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · exact good.path old present
    · obtain ⟨receipt, published, rfl⟩ := List.mem_map.mp inside
      obtain ⟨history, head, last⟩ := good.path old present
      have valid : S.Valid old.state receipt := by
        apply lawful.sound old.state (explorer.round - old.born + 1)
        rw [← lawful.resume_run, ← good.run old present]
        exact List.mem_of_mem_drop published
      obtain ⟨state, states, listed⟩ : ∃ state states, old.states = state :: states := by
        cases equation : old.states with
        | nil => simp [equation] at head
        | cons state states => exact ⟨state, states, rfl⟩
      rw [listed] at history head last
      have same : state = old.state := by simpa using head
      subst same
      refine ⟨?_, rfl, ?_⟩
      · simp only [listed]
        exact .commit history valid
      · simp only [listed, List.getLast?_cons_cons]
        exact last
  · intro node member receipt published
    rcases memStep node member with ⟨old, present, rfl⟩ | ⟨old, present, inside⟩
    · simp only [expand] at published
      exact childOf old present receipt (List.mem_of_mem_take published)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp inside
      simp at published
  · obtain ⟨node, member, same⟩ := good.source
    exact ⟨(expand S explorer.round node).1, keptMem node member, by simp [expand, same]⟩

theorem explore_good (lawful : S.Lawful) (source : σ) : ∀ work, Good S source (explore S source work) := by
  intro work
  induction work with
  | zero => exact begin_good source
  | succ work ih => exact step_good lawful ih

/-- **Every node's path is a chain** of valid receipts from the source. -/
theorem node_chain (lawful : S.Lawful) (source : σ) (work : Nat) :
    ∀ node ∈ (explore S source work).nodes, History S node.states node.receipts ∧
      node.states.head? = some node.state ∧ node.states.getLast? = some source :=
  (explore_good lawful source work).path

/-- A state reached by the explorer after finitely many rounds. -/
def Explored (source state : σ) : Prop := ∃ work, ∃ node ∈ (explore S source work).nodes, node.state = state

theorem explored_source (source : σ) : Explored (S := S) source source :=
  ⟨0, ⟨source, [], [source], 0, S.run source 0, 0⟩, by simp [explore, begin], rfl⟩

theorem nodes_persist (source : σ) (work : Nat) :
    ∀ node ∈ (explore S source work).nodes, ∃ later ∈ (explore S source (work + 1)).nodes, later.state = node.state ∧
      later.born = node.born := by
  intro node member
  exact ⟨(expand S _ node).1, by
    simp only [explore, step, List.mem_append, List.mem_map]
    exact .inl ⟨_, ⟨node, member, rfl⟩, rfl⟩, rfl, rfl⟩

/-- **Every receipt a node's search ever publishes yields a node.** -/
theorem explored_target (lawful : S.Lawful) {source state : σ} (explored : Explored (S := S) source state)
    {work : Nat} {receipt : Receipt} (published : receipt ∈ S.publication (S.run state work)) :
    Explored (S := S) source (S.target receipt) := by
  obtain ⟨round, node, member, rfl⟩ := explored
  have keep : ∀ extra, ∃ later ∈ (explore S source (round + extra)).nodes,
      later.state = node.state ∧ later.born = node.born := by
    intro extra
    induction extra with
    | zero => exact ⟨node, member, rfl, rfl⟩
    | succ extra ih =>
      obtain ⟨later, inside, sameState, sameBorn⟩ := ih
      obtain ⟨next, inNext, nextState, nextBorn⟩ := nodes_persist source _ later inside
      exact ⟨next, by rw [← Nat.add_assoc]; exact inNext, nextState.trans sameState, nextBorn.trans sameBorn⟩
  have bornBound := (explore_good lawful source round).born node member
  rw [explore_round] at bornBound
  obtain ⟨later, inside, sameState, sameBorn⟩ := keep (work + 1)
  have good := explore_good lawful source (round + (work + 1))
  have expandedNow := good.expanded later inside (by rw [explore_round, sameBorn]; omega)
  have runNow := good.run later inside
  rw [explore_round, sameState, sameBorn] at runNow
  obtain ⟨more, total⟩ := Nat.exists_eq_add_of_le (show work ≤ round + (work + 1) - node.born by omega)
  have grows := lawful.publication_prefix node.state work more
  rw [← total, ← runNow] at grows
  have inPublication : receipt ∈ S.publication later.run := grows.subset published
  have inTaken : receipt ∈ (S.publication later.run).take later.consumed := by
    rw [expandedNow, List.take_length]
    exact inPublication
  obtain ⟨child, inNodes, same⟩ := good.children later inside receipt inTaken
  exact ⟨_, child, inNodes, same⟩

/-! ## Every reachable state, for steps modulo equations -/

section Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- **Every state reachable by finitely many GSLT steps is explored**, up to equality, for every
plan whose equations are balanced (every accepted compiled plan). -/
theorem explores_multistep (checked : Predecessors.equationsChecked plan = true) (source : Pattern)
    {target : Pattern} (reaches : (GeneralOccurrenceSemantics.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explored (S := Classes.search plan bound expected) source state ∧
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) state target := by
  suffices along : ∀ first last,
      (GeneralOccurrenceSemantics.gslt plan bound expected).MultiStep first last → ∀ state,
        Explored (S := Classes.search plan bound expected) source state →
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) state first →
        ∃ reached, Explored (S := Classes.search plan bound expected) source reached ∧
          Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) reached last from
    along source target reaches source (explored_source source) (.refl _)
  intro first last reaches
  induction reaches with
  | refl term => intro state explored equal; exact ⟨state, explored, equal⟩
  | @step first middle last stepped _ ih =>
    intro state explored equal
    obtain ⟨representative, receipt, before, valid, after⟩ := stepped
    have fromState : (GeneralOccurrenceSemantics.gslt plan bound expected).Step state middle :=
      ⟨representative, receipt, .trans _ _ _ equal before, valid, after⟩
    obtain ⟨work, published, member, related⟩ :=
      Classes.complete_in_limit plan bound expected state checked fromState
    have next := explored_target (Classes.search_lawful plan bound expected) explored (work := work) member
    exact ih published.target next related

end Classes

end Mettapedia.OSLF.MeTTaIL.Complete.Explore
