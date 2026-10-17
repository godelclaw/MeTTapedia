import Mettapedia.GSLT.LanguageDef.RegexRankedObservation

/-!
# Decidable ordinary control reachability

The existing proved memoized graph search decides syntactic program-counter
reachability. Input guards are deliberately not consulted: this is the
ordinary control-flow overapproximation used to license observation calls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexOrdinaryReachability

open Mettapedia.Computability.RegularLanguages
open RegexDependentObservation

def Reach {states groups : Nat} (code : Fin states → Instruction states groups)
    (first last : Fin states) : Prop :=
  Relation.ReflTransGen (fun source target => target ∈ ordinaryTargets (code source)) first last

def graph {states groups : Nat} (code : Fin states → Instruction states groups)
    (target pc : Fin states) : RegexTaggedGraph.Node (Fin states) Unit Unit Unit :=
  if pc = target then .accept () else
    match code pc with
    | .accept | .dead => .dead
    | .branch first second => .choice first second
    | .jump next | .consume _ next | .assertion _ next | .open _ next | .close _ next |
      .backref _ _ next | .look _ _ next => .jump next

def initial {states : Nat} (first : Fin states) : RegexTaggedGraph.Thread (Fin states) 0 :=
  ⟨(first, 0), fun _ => none, []⟩

theorem children_exact {states groups : Nat} (code : Fin states → Instruction states groups)
    (target pc : Fin states) (different : pc ≠ target) :
    RegexMemoizedSearch.children (graph code target) probe (pc, 0) =
      (ordinaryTargets (code pc)).map (fun next => (next, (0 : Fin 1))) := by
  cases instruction : code pc <;>
    simp [RegexMemoizedSearch.children, OrderedGraphSearch.expand, graph, different,
      instruction, RegexTaggedGraph.eraseNode, ordinaryTargets]

theorem target_is_goal {states groups : Nat} (code : Fin states → Instruction states groups)
    (target : Fin states) :
    RegexMemoizedSearch.goal (graph code target) (fun _ => true) (target, (0 : Fin 1)) = true := by
  simp [RegexMemoizedSearch.goal, graph, RegexTaggedGraph.eraseNode, OrderedGraphSearch.acceptedTag]

theorem reach_authorizes_goal {states groups : Nat} (code : Fin states → Instruction states groups)
    {first target : Fin states} (path : Reach code first target) :
    RegexMemoizedSearch.Reaches (RegexMemoizedSearch.children (graph code target) probe)
      (RegexMemoizedSearch.goal (graph code target) (fun _ => true)) ∅ (first, 0) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .done (by simp) (target_is_goal code target)
  | @head first next edge path ih =>
      by_cases same : first = target
      · subst first
        exact .done (by simp) (target_is_goal code target)
      · exact .step (by simp)
          (by rw [children_exact code target first same]; exact List.mem_map.mpr ⟨next, edge, rfl⟩) ih

theorem graph_edge_authorized {states groups : Nat} (code : Fin states → Instruction states groups)
    (target : Fin states) (first last : RegexTaggedGraph.Thread (Fin states) 0)
    (edge : last ∈ RegexTaggedGraph.edges (graph code target) probe first) :
    last.point.1 ∈ ordinaryTargets (code first.point.1) := by
  by_cases same : first.point.1 = target
  · simp [RegexTaggedGraph.edges, graph, same] at edge
  · cases instruction : code first.point.1 <;>
      simp_all [RegexTaggedGraph.edges, graph, ordinaryTargets, RegexTaggedGraph.Thread.at,
        RegexTaggedGraph.Thread.branch]
    all_goals rcases edge with rfl | rfl <;> simp

theorem graph_terminal_is_target {states groups : Nat} (code : Fin states → Instruction states groups)
    (target : Fin states) (last : RegexTaggedGraph.Thread (Fin states) 0)
    (terminal : RegexPikeVM.terminal (graph code target) last = some ()) : last.point.1 = target := by
  by_contra different
  cases instruction : code last.point.1 <;>
    simp [RegexPikeVM.terminal, graph, different, instruction] at terminal

theorem derives_authorizes_reach {states groups : Nat} (code : Fin states → Instruction states groups)
    (target : Fin states) {first last : RegexTaggedGraph.Thread (Fin states) 0}
    (derived : RegexTaggedGraph.Derives (graph code target) probe first last) :
    Reach code first.point.1 last.point.1 := by
  induction derived with
  | refl => exact .refl
  | tail path edge ih => exact ih.tail (graph_edge_authorized code target _ _ edge)

theorem trace_authorizes_reach {states groups : Nat} (code : Fin states → Instruction states groups)
    (target : Fin states) {first last : RegexTaggedGraph.Thread (Fin states) 0}
    {bits : List Bool} {points : List (OrderedGraphSearch.Point (Fin states) 0)}
    (trace : RegexSelectionCorrespondence.Trace (graph code target) probe (fun _ => true)
      first bits points last ()) : Reach code first.point.1 target := by
  have reached := derives_authorizes_reach code target trace.sound.1
  rw [graph_terminal_is_target code target last trace.sound.2.1] at reached
  exact reached

def search {states groups : Nat} (code : Fin states → Instruction states groups)
    (first target : Fin states) :=
  RegexMemoizedSearch.taggedSearch (graph code target) probe (fun _ => true)
    (Fintype.card (OrderedGraphSearch.Point (Fin states) 0) + 2) (initial first)

def test {states groups : Nat} (code : Fin states → Instruction states groups)
    (first target : Fin states) : Bool :=
  match search code first target with
  | .found _ _ => true
  | _ => false

theorem test_iff {states groups : Nat} (code : Fin states → Instruction states groups)
    (first target : Fin states) : test code first target = true ↔ Reach code first target := by
  have checked := RegexMemoizedSearch.taggedSearch_contract (graph code target) probe (fun _ => true)
    (initial first) (Fintype.card (OrderedGraphSearch.Point (Fin states) 0) + 2) (by omega)
  change RegexMemoizedSearch.Contract (graph code target) probe (fun _ => true) ∅ ∅ (initial first)
    (search code first target) at checked
  constructor
  · intro found
    unfold test at found
    cases result : search code first target with
    | incomplete => simp [result] at found
    | absent seen => simp [result] at found
    | found last tag =>
        cases tag
        simp only [result, RegexMemoizedSearch.Contract] at checked
        obtain ⟨bits, points, trace, _, _, _⟩ := checked
        exact trace_authorizes_reach code target trace
  · intro reached
    cases result : search code first target with
    | incomplete => simp [result, RegexMemoizedSearch.Contract] at checked
    | absent seen =>
        simp only [result, RegexMemoizedSearch.Contract] at checked
        exact False.elim (checked.2.2 (reach_authorizes_goal code reached))
    | found last tag => simp [test, result]

def decidableReach {states groups : Nat} (code : Fin states → Instruction states groups)
    (first target : Fin states) : Decidable (Reach code first target) :=
  if found : test code first target = true then .isTrue ((test_iff code first target).mp found)
  else .isFalse (fun reached => found ((test_iff code first target).mpr reached))

namespace Controls

private def observation : Fin 3 → Instruction 3 0 := fun pc =>
  if pc.val = 0 then .look .ahead 2 1 else .dead

theorem ordinary_continuation_is_reachable : test observation 0 1 = true := by decide

theorem reflexive_control_reachability : test observation 2 2 = true := by decide

theorem observation_body_is_not_an_ordinary_successor : test observation 0 2 = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexOrdinaryReachability
