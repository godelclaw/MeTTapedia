import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensional
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# Native types of finite membership graphs, decided against hypersets

A finite membership graph lists, for each of its nodes, the nodes that are its members (`MembershipGraph`). Under
anti-foundation every node pictures exactly one hyperset, its decoration (`HSet.decorate`), and the graph may have
cycles: the node that is its own only member pictures Ω = {Ω}.

- **Hypersets as a native structure** (`hypersets`): steps go from a hyperset to its members, as in the membership
  language of hereditarily finite sets, and equality is equality of hypersets.
- **The finite structure of a graph** (`MembershipGraph.finite`): steps follow the edges, and two nodes are the same
  when they are bisimilar. Bisimilarity is the greatest fixed point of matching children on pairs of nodes, reached by
  as many rounds as there are pairs (`bisim`, exact by `bisim_iff`).
- **Decoration is a step morphism into the hypersets** (`decoration`): an edge is a membership, every member of a
  decoration is the decoration of a child, and nodes are the same exactly when they picture the same hyperset.
- **So a behavioural native type holds at a node exactly when it holds at the hyperset the node pictures**
  (`eval_iff_hyperset`), and the finite structure's evaluation decides it. Fixed points are reached by stages on the
  finite graph, with no well-foundedness: Ω descends forever and has no well-founded descent, the empty set the other
  way round (`omega_descends_forever`, `omega_not_wellFounded`).

The parts of a node are not nodes, so the graph structure has no splits, and separating formulas are outside the
transfer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.MaterialSets.Hypersets (HSet IsBisimulation Bisimilar)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings (memberLabel)

/-! ## Hypersets as a native structure -/

/-- **Hypersets as a native structure**: steps go from a hyperset to its members, and equality is equality of
hypersets. Hypersets are built by no constructor, bind nothing and carry no names; every hyperset is a `Set`. -/
def hypersets : NativeStructure HSet.{0} where
  step source label target := memberLabel label ∧ target ∈ source
  built _ _ _ := False
  split whole kind first second := kind = .hashSet ∧ ∀ z, z ∈ whole ↔ z ∈ first ∨ z ∈ second
  empty whole kind := kind = .hashSet ∧ ∀ z, z ∉ whole
  single whole kind member := kind = .hashSet ∧ ∀ z, z ∈ whole ↔ z = member
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ type := type = .base "Set"
  named _ _ := False
  same first second := first = second
  apply inner _ := inner

/-! ## Finite membership graphs -/

/-- **A finite membership graph**: for each node, the nodes that are its members. -/
structure MembershipGraph where
  size : ℕ
  children : Fin size → List (Fin size)

namespace MembershipGraph

variable (graph : MembershipGraph)

/-- `edge node child`: the child is a member of the node. -/
def edge (node child : Fin graph.size) : Prop := child ∈ graph.children node

/-- All pairs of nodes. -/
def pairs : List (Fin graph.size × Fin graph.size) :=
  (List.finRange graph.size).flatMap fun first => (List.finRange graph.size).map fun second => (first, second)

theorem mem_pairs (pair : Fin graph.size × Fin graph.size) : pair ∈ graph.pairs := by
  simp [pairs, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- One round of bisimilarity: each child of either node is matched by a related child of the other. -/
def bisimRound (related : Fin graph.size × Fin graph.size → Bool) (pair : Fin graph.size × Fin graph.size) : Bool :=
  (graph.children pair.1).all (fun first => (graph.children pair.2).any fun second => related (first, second)) &&
    (graph.children pair.2).all (fun second => (graph.children pair.1).any fun first => related (first, second))

/-- **Bisimilarity of nodes**: the greatest fixed point of matching children, reached by as many rounds as there are
pairs. -/
def bisim (first second : Fin graph.size) : Bool :=
  Listed.down graph.bisimRound graph.pairs.length (first, second)

theorem bisimRound_mono : ∀ smaller larger : Fin graph.size × Fin graph.size → Bool, Listed.Le smaller larger →
    Listed.Le (graph.bisimRound smaller) (graph.bisimRound larger) := by
  intro smaller larger le pair holds
  simp only [bisimRound, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at holds ⊢
  refine ⟨fun first member => ?_, fun second member => ?_⟩
  · obtain ⟨second, secondMember, related⟩ := holds.1 first member
    exact ⟨second, secondMember, le _ related⟩
  · obtain ⟨first, firstMember, related⟩ := holds.2 second member
    exact ⟨first, firstMember, le _ related⟩

theorem bisim_fixed :
    graph.bisimRound (Listed.down graph.bisimRound graph.pairs.length) = Listed.down graph.bisimRound graph.pairs.length :=
  Listed.down_stable graph.bisimRound_mono graph.mem_pairs

/-- **The decided bisimilarity is bisimilarity.** -/
theorem bisim_iff (first second : Fin graph.size) :
    graph.bisim first second = true ↔ Bisimilar graph.edge graph.edge first second := by
  constructor
  · intro related
    refine ⟨fun a b => graph.bisim a b = true, fun a b holds => ?_, related⟩
    have unfolded : graph.bisimRound (Listed.down graph.bisimRound graph.pairs.length) (a, b) = true := by
      rw [graph.bisim_fixed]
      exact holds
    simp only [bisimRound, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at unfolded
    exact ⟨fun a' edge => unfolded.1 a' edge, fun b' edge => (unfolded.2 b' edge).imp fun _ found => found⟩
  · rintro ⟨relation, isBisimulation, related⟩
    refine Listed.down_contains (invariant := {pair : Fin graph.size × Fin graph.size | relation pair.1 pair.2})
      (fun predicate contained pair inside => ?_)
      graph.pairs.length (first, second) related
    obtain ⟨forth, back⟩ := isBisimulation inside
    simp only [bisimRound, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
    refine ⟨fun a' edge => ?_, fun b' edge => ?_⟩
    · obtain ⟨b', edge', related'⟩ := forth a' edge
      exact ⟨b', edge', contained (a', b') related'⟩
    · obtain ⟨a', edge', related'⟩ := back b' edge
      exact ⟨a', edge', contained (a', b') related'⟩

/-- **The finite structure of a graph**: steps follow the edges, nodes are the same when bisimilar, and a node is
empty or a one-element set by its children. The parts of a node are not nodes, so it has no splits. -/
def finite : FiniteStructure (Fin graph.size) where
  elements := List.finRange graph.size
  complete := List.mem_finRange
  step source label target := decide (memberLabel label) && (graph.children source).contains target
  built _ _ _ := false
  split _ _ _ _ := false
  empty node kind := decide (kind = .hashSet) && (graph.children node).isEmpty
  single node kind member := decide (kind = .hashSet) && !(graph.children node).isEmpty &&
    (graph.children node).all fun child => graph.bisim child member
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed _ type := decide (type = .base "Set")
  named _ _ := false
  same := graph.bisim
  apply inner _ := inner

/-- **Decoration is a step morphism into the hypersets.** -/
noncomputable def decoration : StepMorphism graph.finite.native hypersets where
  map := HSet.decorate graph.edge
  step := by
    intro source label target stepped
    change (decide (memberLabel label) && (graph.children source).contains target) = true at stepped
    rw [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at stepped
    exact ⟨stepped.1, HSet.decorate_mem_decorate stepped.2⟩
  stepBack := by
    rintro source label _ ⟨labelled, member⟩
    obtain ⟨child, edge, rfl⟩ := HSet.mem_decorate.mp member
    refine ⟨child, ?_, rfl⟩
    change (decide (memberLabel label) && (graph.children source).contains child) = true
    rw [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
    exact ⟨labelled, edge⟩
  sameIff first second := by
    change graph.bisim first second = true ↔ HSet.decorate graph.edge first = HSet.decorate graph.edge second
    rw [graph.bisim_iff, HSet.decorate_eq_decorate_iff]
  namedIff _ _ := by
    change (false = true) ↔ False
    simp

/-- **A behavioural native type holds at a node exactly when it holds at the hyperset the node pictures**, and the
finite structure's evaluation decides it. -/
theorem eval_iff_hyperset {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    (node : Fin graph.size) :
    graph.finite.eval Fin.elim0 formula node = true ↔
      hypersets.sat Env.closed formula (HSet.decorate graph.edge node) :=
  (graph.finite.eval_iff formula Fin.elim0 node).trans
    (graph.decoration.sat_iff formula behavioural (fun index => index.elim0) node)

end MembershipGraph

/-! ## Ω, the empty set, and a repeated member -/

/-- One node that is its own only member: Ω = {Ω}. -/
abbrev omega : MembershipGraph := ⟨1, fun _ => [0]⟩

/-- One node with no members: the empty set. -/
abbrev emptyGraph : MembershipGraph := ⟨1, fun _ => []⟩

/-- Node `0` has the members `1` and `2`, each its own only member: {Ω, Ω} = {Ω}. Node `3` is empty. -/
abbrev twoOmegas : MembershipGraph := ⟨4, fun node => match node.val with
  | 0 => [1, 2]
  | 1 => [1]
  | 2 => [2]
  | _ => []⟩

/-- There is an infinite descent: `νX. ◇X`. -/
def descendsForever : Formula 0 := .nu (.possibly .any (.var 0))

/-- Every descent ends: `μX. □X`. -/
def wellFounded : Formula 0 := .mu (.necessarily .any (.var 0))

/-- At least `k` members. -/
def membersAtLeast (k : ℕ) : Formula 0 := .atLeast k .forward .any .top

theorem omega_decorate : HSet.decorate omega.edge 0 = HSet.quineAtom := by
  refine HSet.eq_quineAtom_of_eq_singleton (HSet.ext fun z => ?_)
  rw [HSet.mem_decorate, HSet.mem_singleton]
  constructor
  · rintro ⟨child, edge, rfl⟩
    have zero : child = 0 := List.mem_singleton.mp edge
    rw [zero]
  · intro same
    exact ⟨0, List.mem_singleton.mpr rfl, same.symm⟩

/-- **Ω descends forever.** -/
theorem omega_descends_forever : hypersets.sat Env.closed descendsForever HSet.quineAtom := by
  rw [← omega_decorate]
  exact (omega.eval_iff_hyperset (formula := descendsForever) rfl 0).mp (by decide)

/-- **Ω has no well-founded descent.** -/
theorem omega_not_wellFounded : ¬ hypersets.sat Env.closed wellFounded HSet.quineAtom := by
  rw [← omega_decorate]
  exact fun holds => absurd ((omega.eval_iff_hyperset (formula := wellFounded) rfl 0).mpr holds) (by decide)

/-- **The empty set is well founded and does not descend.** -/
theorem empty_wellFounded :
    hypersets.sat Env.closed wellFounded (HSet.decorate emptyGraph.edge 0) ∧
      ¬ hypersets.sat Env.closed descendsForever (HSet.decorate emptyGraph.edge 0) :=
  ⟨(emptyGraph.eval_iff_hyperset (formula := wellFounded) rfl 0).mp (by decide),
    fun holds => absurd ((emptyGraph.eval_iff_hyperset (formula := descendsForever) rfl 0).mpr holds) (by decide)⟩

/-- **{Ω, Ω} has one member, not two**: the two nodes picture the same hyperset. -/
theorem twoOmegas_one_member :
    hypersets.sat Env.closed (membersAtLeast 1) (HSet.decorate twoOmegas.edge 0) ∧
      ¬ hypersets.sat Env.closed (membersAtLeast 2) (HSet.decorate twoOmegas.edge 0) :=
  ⟨(twoOmegas.eval_iff_hyperset (formula := membersAtLeast 1) rfl 0).mp (by decide),
    fun holds => absurd ((twoOmegas.eval_iff_hyperset (formula := membersAtLeast 2) rfl 0).mpr holds) (by decide)⟩

/-- **Nodes picturing Ω are the same, and differ from the empty node.** -/
theorem twoOmegas_same :
    HSet.decorate twoOmegas.edge 1 = HSet.decorate twoOmegas.edge 2 ∧
      HSet.decorate twoOmegas.edge 1 ≠ HSet.decorate twoOmegas.edge 3 := by
  refine ⟨(twoOmegas.decoration.sameIff 1 2).mp (show twoOmegas.bisim 1 2 = true by decide), fun same => ?_⟩
  exact absurd ((twoOmegas.decoration.sameIff 1 3).mpr same) (show ¬ twoOmegas.bisim 1 3 = true by decide)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs
