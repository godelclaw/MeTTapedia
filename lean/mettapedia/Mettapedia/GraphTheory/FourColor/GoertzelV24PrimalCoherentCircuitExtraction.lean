import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionPrimalCircuit
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A finite closed walk whose successive edges never immediately repeat
contains a cycle no longer than the walk. The proof restricts to the finite
subgraph traced by the walk: if that subgraph were acyclic, local
nonbacktracking would force the closed walk to be a path. -/
theorem exists_isCycle_length_le_edges_subset_of_edges_isChain_ne
    {start : V} (walk : G.Walk start start) (hpositive : 0 < walk.length)
    (hchain : walk.edges.IsChain (fun first second ↦ first ≠ second)) :
    ∃ (cycleStart : V) (cycle : G.Walk cycleStart cycleStart),
      cycle.IsCycle ∧ cycle.length ≤ walk.length ∧
        cycle.edges ⊆ walk.edges := by
  let traced := walk.toSubgraph
  let lifted := walk.mapToSubgraph
  have hliftedChain :
      lifted.edges.IsChain (fun first second ↦ first ≠ second) := by
    have hmappedChain :
        (lifted.edges.map (Sym2.map traced.hom)).IsChain
          (fun first second ↦ first ≠ second) := by
      have hedgeMap : lifted.edges.map (Sym2.map traced.hom) = walk.edges := by
        rw [← SimpleGraph.Walk.edges_map,
          walk.map_mapToSubgraph_hom]
        rfl
      rw [hedgeMap]
      exact hchain
    exact List.isChain_of_isChain_map (Sym2.map traced.hom)
      (fun first second hne heq ↦ hne (congrArg (Sym2.map traced.hom) heq))
      hmappedChain
  have hnotAcyclic : ¬traced.coe.IsAcyclic := by
    intro hacyclic
    have hliftedPath : lifted.IsPath :=
      (hacyclic.isPath_iff_isChain lifted).2 hliftedChain
    have hwalkPath : walk.IsPath := by
      have hmappedPath := SimpleGraph.Walk.map_isPath_of_injective
        SimpleGraph.Subgraph.hom_injective hliftedPath
      rw [walk.map_mapToSubgraph_hom] at hmappedPath
      exact hmappedPath
    have hnil : walk.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hwalkPath
    exact (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive) hnil
  simp only [SimpleGraph.IsAcyclic] at hnotAcyclic
  push Not at hnotAcyclic
  rcases hnotAcyclic with ⟨cycleStart, cycle, hcycle⟩
  let mappedCycle := cycle.map traced.hom
  have hmappedCycle : mappedCycle.IsCycle :=
    hcycle.map SimpleGraph.Subgraph.hom_injective
  have hedgeSubset : mappedCycle.edges ⊆ walk.edges := by
    intro edge hedge
    rw [SimpleGraph.Walk.edges_map] at hedge
    rcases List.mem_map.1 hedge with ⟨tracedEdge, htracedEdge, rfl⟩
    have hedgeSet := cycle.edges_subset_edgeSet htracedEdge
    rw [SimpleGraph.Subgraph.edgeSet_coe] at hedgeSet
    exact (walk.mem_edges_toSubgraph).1 hedgeSet
  have hsubperm : mappedCycle.edges.Subperm walk.edges :=
    List.subperm_of_subset hmappedCycle.isTrail.edges_nodup hedgeSubset
  refine ⟨cycleStart.1, mappedCycle, hmappedCycle, ?_, hedgeSubset⟩
  calc
    mappedCycle.length = mappedCycle.edges.length :=
      mappedCycle.length_edges.symm
    _ ≤ walk.edges.length := hsubperm.length_le
    _ = walk.length := walk.length_edges

/-- Length-only projection of the support-preserving cycle extraction. -/
theorem exists_isCycle_length_le_of_edges_isChain_ne
    {start : V} (walk : G.Walk start start) (hpositive : 0 < walk.length)
    (hchain : walk.edges.IsChain (fun first second ↦ first ≠ second)) :
    ∃ (cycleStart : V) (cycle : G.Walk cycleStart cycleStart),
      cycle.IsCycle ∧ cycle.length ≤ walk.length := by
  rcases walk.exists_isCycle_length_le_edges_subset_of_edges_isChain_ne
      hpositive hchain with
    ⟨cycleStart, cycle, hcycle, hlength, _⟩
  exact ⟨cycleStart, cycle, hcycle, hlength⟩

/-- The edge list of the canonical primal lift is locally nonrepeating,
because it is the mapped tail of a line-graph walk support. -/
theorem primalLift_edges_isChain_ne {edge : G.edgeSet}
    (lineWalk : G.lineGraph.Walk edge edge)
    (hpositive : 0 < lineWalk.length)
    (hcoherent : lineWalk.IsPrimalCoherentClosed) :
    (lineWalk.primalLift hpositive hcoherent).edges.IsChain
      (fun first second ↦ first ≠ second) := by
  rw [lineWalk.primalLift_edges_eq_map_tail_support hpositive hcoherent]
  apply List.isChain_map_of_isChain Subtype.val
    (fun (first second : G.edgeSet)
      (hadj : G.lineGraph.Adj first second) ↦
        Subtype.val_injective.ne hadj.ne)
  exact lineWalk.isChain_adj_support.tail

/-- Support-preserving primal cycle extraction: every output edge occurs
in the cyclic line-graph support that was lifted. -/
theorem exists_primal_isCycle_length_le_edges_subset_of_primalCoherentClosed
    {edge : G.edgeSet} (lineWalk : G.lineGraph.Walk edge edge)
    (hpositive : 0 < lineWalk.length)
    (hcoherent : lineWalk.IsPrimalCoherentClosed) :
    ∃ (cycleStart : V) (cycle : G.Walk cycleStart cycleStart),
      cycle.IsCycle ∧ cycle.length ≤ lineWalk.length ∧
        cycle.edges ⊆ lineWalk.support.tail.map Subtype.val := by
  rcases
      (lineWalk.primalLift hpositive hcoherent).exists_isCycle_length_le_edges_subset_of_edges_isChain_ne
        (by simpa only [lineWalk.primalLift_length hpositive hcoherent] using
          hpositive)
        (lineWalk.primalLift_edges_isChain_ne hpositive hcoherent) with
    ⟨cycleStart, cycle, hcycle, hlength, hsubset⟩
  exact ⟨cycleStart, cycle, hcycle,
    by
      simpa only [lineWalk.primalLift_length hpositive hcoherent] using
        hlength,
    by
      simpa only [lineWalk.primalLift_edges_eq_map_tail_support
        hpositive hcoherent] using hsubset⟩

/-- Every positive primal-coherent closed line-graph walk, even one with
repeated line vertices, contains a primal cycle no longer than itself. -/
theorem exists_primal_isCycle_length_le_of_primalCoherentClosed
    {edge : G.edgeSet} (lineWalk : G.lineGraph.Walk edge edge)
    (hpositive : 0 < lineWalk.length)
    (hcoherent : lineWalk.IsPrimalCoherentClosed) :
    ∃ (cycleStart : V) (cycle : G.Walk cycleStart cycleStart),
      cycle.IsCycle ∧ cycle.length ≤ lineWalk.length := by
  rcases
      lineWalk.exists_primal_isCycle_length_le_edges_subset_of_primalCoherentClosed
        hpositive hcoherent with
    ⟨cycleStart, cycle, hcycle, hlength, _⟩
  exact ⟨cycleStart, cycle, hcycle, hlength⟩

end SimpleGraph.Walk
