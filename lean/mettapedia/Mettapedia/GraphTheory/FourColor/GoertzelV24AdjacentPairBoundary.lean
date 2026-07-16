import Mettapedia.GraphTheory.FourColor.GoertzelV24FourDefectBoundary

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairBoundary

open SimpleGraph
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FourDefectBoundary

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Vertices retained after deleting an adjacent pair. -/
abbrev retainedVertexSet (first second : V) : Set V :=
  {vertex | vertex ≠ first ∧ vertex ≠ second}

/-- The induced graph remaining after deleting two vertices. -/
abbrev DeletedAdjacentPairGraph
    (G : SimpleGraph V) (first second : V) :
    SimpleGraph (retainedVertexSet first second) :=
  G.induce (retainedVertexSet first second)

/-- The four ordered ports around two adjacent cubic vertices. Ports `0,1`
are adjacent to `first`; ports `2,3` are adjacent to `second`. -/
structure AdjacentPairData (G : SimpleGraph V) where
  firstVertex : V
  secondVertex : V
  portVertex : Fin 4 → V
  centralAdjacent : G.Adj firstVertex secondVertex
  portInjective : Function.Injective portVertex
  portNeFirst : ∀ port, portVertex port ≠ firstVertex
  portNeSecond : ∀ port, portVertex port ≠ secondVertex
  firstNeighbors :
    G.neighborSet firstVertex =
      ({secondVertex, portVertex 0, portVertex 1} : Set V)
  secondNeighbors :
    G.neighborSet secondVertex =
      ({firstVertex, portVertex 2, portVertex 3} : Set V)

namespace AdjacentPairData

/-- Inclusion of retained vertices into the ambient carrier. -/
def retainedVertexEmbedding (data : AdjacentPairData G) :
    retainedVertexSet data.firstVertex data.secondVertex ↪ V :=
  Function.Embedding.subtype
    (fun x : V ↦ x ∈ retainedVertexSet data.firstVertex data.secondVertex)

/-- A port as a vertex of the graph with the adjacent central pair deleted. -/
def retainedPort (data : AdjacentPairData G) (port : Fin 4) :
    retainedVertexSet data.firstVertex data.secondVertex :=
  ⟨data.portVertex port, data.portNeFirst port, data.portNeSecond port⟩

/-- The canonical ordered four-defect boundary exposed by deleting the
adjacent central pair. -/
def degreeTwoBoundaryData (data : AdjacentPairData G) :
    DegreeTwoBoundaryData
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) 4 where
  defectVertex := data.retainedPort

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem retainedPort_injective (data : AdjacentPairData G) :
    Function.Injective data.retainedPort := by
  intro first second heq
  apply data.portInjective
  exact congrArg Subtype.val heq

/-- Neighbor finsets in the induced deletion are the ambient neighbor
finsets with the two deleted vertices erased. -/
theorem map_neighborFinset_deletedAdjacentPairGraph
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    (SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        vertex).map
          data.retainedVertexEmbedding =
      ((G.neighborFinset vertex.1).erase data.firstVertex).erase
        data.secondVertex := by
  calc
    (SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        vertex).map
          data.retainedVertexEmbedding =
        G.neighborFinset vertex.1 ∩
          (retainedVertexSet data.firstVertex data.secondVertex).toFinset := by
      simpa [retainedVertexEmbedding] using
        (SimpleGraph.map_neighborFinset_induce
          (G := G) (s := retainedVertexSet
            data.firstVertex data.secondVertex) vertex)
    _ = ((G.neighborFinset vertex.1).erase data.firstVertex).erase
        data.secondVertex := by
      ext other
      simp [retainedVertexSet, and_assoc, and_left_comm, and_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem port_pairwise_ne (data : AdjacentPairData G)
    {first second : Fin 4} (hne : first ≠ second) :
    data.portVertex first ≠ data.portVertex second := by
  intro heq
  exact hne (data.portInjective heq)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem first_adj_port_zero (data : AdjacentPairData G) :
    G.Adj data.firstVertex (data.portVertex 0) := by
  simpa using (show data.portVertex 0 ∈ G.neighborSet data.firstVertex by
    rw [data.firstNeighbors]
    simp)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem first_adj_port_one (data : AdjacentPairData G) :
    G.Adj data.firstVertex (data.portVertex 1) := by
  simpa using (show data.portVertex 1 ∈ G.neighborSet data.firstVertex by
    rw [data.firstNeighbors]
    simp)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem second_adj_port_two (data : AdjacentPairData G) :
    G.Adj data.secondVertex (data.portVertex 2) := by
  simpa using (show data.portVertex 2 ∈ G.neighborSet data.secondVertex by
    rw [data.secondNeighbors]
    simp)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem second_adj_port_three (data : AdjacentPairData G) :
    G.Adj data.secondVertex (data.portVertex 3) := by
  simpa using (show data.portVertex 3 ∈ G.neighborSet data.secondVertex by
    rw [data.secondNeighbors]
    simp)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem not_second_adj_port_zero (data : AdjacentPairData G) :
    ¬ G.Adj data.secondVertex (data.portVertex 0) := by
  intro hadj
  have hmem : data.portVertex 0 ∈ G.neighborSet data.secondVertex := hadj
  rw [data.secondNeighbors] at hmem
  simp [data.portNeFirst,
    port_pairwise_ne data (by decide : (0 : Fin 4) ≠ 2),
    port_pairwise_ne data (by decide : (0 : Fin 4) ≠ 3)] at hmem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem not_second_adj_port_one (data : AdjacentPairData G) :
    ¬ G.Adj data.secondVertex (data.portVertex 1) := by
  intro hadj
  have hmem : data.portVertex 1 ∈ G.neighborSet data.secondVertex := hadj
  rw [data.secondNeighbors] at hmem
  simp [data.portNeFirst,
    port_pairwise_ne data (by decide : (1 : Fin 4) ≠ 2),
    port_pairwise_ne data (by decide : (1 : Fin 4) ≠ 3)] at hmem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem not_first_adj_port_two (data : AdjacentPairData G) :
    ¬ G.Adj data.firstVertex (data.portVertex 2) := by
  intro hadj
  have hmem : data.portVertex 2 ∈ G.neighborSet data.firstVertex := hadj
  rw [data.firstNeighbors] at hmem
  simp [data.portNeSecond,
    port_pairwise_ne data (by decide : (2 : Fin 4) ≠ 0),
    port_pairwise_ne data (by decide : (2 : Fin 4) ≠ 1)] at hmem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem not_first_adj_port_three (data : AdjacentPairData G) :
    ¬ G.Adj data.firstVertex (data.portVertex 3) := by
  intro hadj
  have hmem : data.portVertex 3 ∈ G.neighborSet data.firstVertex := hadj
  rw [data.firstNeighbors] at hmem
  simp [data.portNeSecond,
    port_pairwise_ne data (by decide : (3 : Fin 4) ≠ 0),
    port_pairwise_ne data (by decide : (3 : Fin 4) ≠ 1)] at hmem

private theorem degree_deleted_port_eq_two
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (port : Fin 4) :
    (incidentEdgeFinset
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (data.retainedPort port)).card = 2 := by
  calc
    (incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort port)).card =
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).degree (data.retainedPort port) :=
      incidentEdgeFinset_card_eq_degree (data.retainedPort port)
    _ = (SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort port)).card :=
      (SimpleGraph.card_neighborFinset_eq_degree
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort port)).symm
    _ =
        ((SimpleGraph.neighborFinset
          (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (data.retainedPort port)).map
            data.retainedVertexEmbedding).card := by simp
    _ = (((G.neighborFinset (data.retainedPort port).1).erase
          data.firstVertex).erase data.secondVertex).card := by
      exact congrArg Finset.card
        (data.map_neighborFinset_deletedAdjacentPairGraph
          (data.retainedPort port))
    _ = (((G.neighborFinset (data.portVertex port)).erase
          data.firstVertex).erase data.secondVertex).card := rfl
    _ = 2 := by
      have hdegree : (G.neighborFinset (data.portVertex port)).card = 3 := by
        calc
          (G.neighborFinset (data.portVertex port)).card =
              G.degree (data.portVertex port) :=
            SimpleGraph.card_neighborFinset_eq_degree
              G (data.portVertex port)
          _ = (incidentEdgeFinset G (data.portVertex port)).card := by
            rw [incidentEdgeFinset_card_eq_degree]
          _ = 3 := hcubic (data.portVertex port)
      have hportCases :
          port = 0 ∨ port = 1 ∨ port = 2 ∨ port = 3 := by
        omega
      rcases hportCases with rfl | rfl | rfl | rfl
      · have hfirst : data.firstVertex ∈
            G.neighborFinset (data.portVertex 0) := by
          simpa using (first_adj_port_zero data).symm
        have hsecond : data.secondVertex ∉
            G.neighborFinset (data.portVertex 0) := by
          intro hmem
          apply not_second_adj_port_zero data
          exact (show G.Adj (data.portVertex 0) data.secondVertex by
            simpa using hmem).symm
        have hsecondAfter : data.secondVertex ∉
            (G.neighborFinset (data.portVertex 0)).erase data.firstVertex := by
          simp [hsecond]
        rw [Finset.erase_eq_self.mpr hsecondAfter,
          Finset.card_erase_of_mem hfirst, hdegree]
      · have hfirst : data.firstVertex ∈
            G.neighborFinset (data.portVertex 1) := by
          simpa using (first_adj_port_one data).symm
        have hsecond : data.secondVertex ∉
            G.neighborFinset (data.portVertex 1) := by
          intro hmem
          apply not_second_adj_port_one data
          exact (show G.Adj (data.portVertex 1) data.secondVertex by
            simpa using hmem).symm
        have hsecondAfter : data.secondVertex ∉
            (G.neighborFinset (data.portVertex 1)).erase data.firstVertex := by
          simp [hsecond]
        rw [Finset.erase_eq_self.mpr hsecondAfter,
          Finset.card_erase_of_mem hfirst, hdegree]
      · have hfirst : data.firstVertex ∉
            G.neighborFinset (data.portVertex 2) := by
          intro hmem
          apply not_first_adj_port_two data
          exact (show G.Adj (data.portVertex 2) data.firstVertex by
            simpa using hmem).symm
        have hsecond : data.secondVertex ∈
            G.neighborFinset (data.portVertex 2) := by
          simpa using (second_adj_port_two data).symm
        rw [Finset.erase_eq_self.mpr hfirst,
          Finset.card_erase_of_mem hsecond, hdegree]
      · have hfirst : data.firstVertex ∉
            G.neighborFinset (data.portVertex 3) := by
          intro hmem
          apply not_first_adj_port_three data
          exact (show G.Adj (data.portVertex 3) data.firstVertex by
            simpa using hmem).symm
        have hsecond : data.secondVertex ∈
            G.neighborFinset (data.portVertex 3) := by
          simpa using (second_adj_port_three data).symm
        rw [Finset.erase_eq_self.mpr hfirst,
          Finset.card_erase_of_mem hsecond, hdegree]

private theorem degree_deleted_nonport_eq_three
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex)
    (hvertex : ∀ port : Fin 4, vertex ≠ data.retainedPort port) :
    (incidentEdgeFinset
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      vertex).card = 3 := by
  have hnotPort : ∀ port : Fin 4, vertex.1 ≠ data.portVertex port := by
    intro port heq
    apply hvertex port
    apply Subtype.ext
    exact heq
  have hnotFirst : data.firstVertex ∉ G.neighborFinset vertex.1 := by
    intro hmem
    have hadj : G.Adj data.firstVertex vertex.1 := by
      exact (show G.Adj vertex.1 data.firstVertex by simpa using hmem).symm
    have : vertex.1 ∈ G.neighborSet data.firstVertex := hadj
    rw [data.firstNeighbors] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with hsecond | hzero | hone
    · exact vertex.2.2 hsecond
    · exact hnotPort 0 hzero
    · exact hnotPort 1 hone
  have hnotSecond : data.secondVertex ∉ G.neighborFinset vertex.1 := by
    intro hmem
    have hadj : G.Adj data.secondVertex vertex.1 := by
      exact (show G.Adj vertex.1 data.secondVertex by simpa using hmem).symm
    have : vertex.1 ∈ G.neighborSet data.secondVertex := hadj
    rw [data.secondNeighbors] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with hfirst | htwo | hthree
    · exact vertex.2.1 hfirst
    · exact hnotPort 2 htwo
    · exact hnotPort 3 hthree
  calc
    (incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        vertex).card =
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).degree vertex :=
      incidentEdgeFinset_card_eq_degree vertex
    _ = (SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        vertex).card :=
      (SimpleGraph.card_neighborFinset_eq_degree
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        vertex).symm
    _ =
        ((SimpleGraph.neighborFinset
          (G := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          vertex).map
            data.retainedVertexEmbedding).card := by simp
    _ = (((G.neighborFinset vertex.1).erase data.firstVertex).erase
          data.secondVertex).card := by
      rw [data.map_neighborFinset_deletedAdjacentPairGraph]
    _ = 3 := by
      simp [hnotFirst, hnotSecond]
      rw [← incidentEdgeFinset_card_eq_degree]
      exact hcubic vertex.1

/-- Deleting a named adjacent cubic pair exposes exactly the canonical
well-formed four-defect boundary. -/
theorem degreeTwoBoundaryData_wellFormed
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    data.degreeTwoBoundaryData.WellFormed := by
  exact ⟨data.retainedPort_injective,
    data.degree_deleted_port_eq_two hcubic,
    data.degree_deleted_nonport_eq_three hcubic⟩

/-- Every Tait coloring of the adjacent-pair deletion has one of the four
parity-permitted boundary types. -/
theorem deletedAdjacentPair_colorWord_classification
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    SquareBoundaryWord.AllEqual (data.degreeTwoBoundaryData.colorWord C) ∨
      SquareBoundaryWord.AdjacentPairs
        (data.degreeTwoBoundaryData.colorWord C) ∨
      SquareBoundaryWord.OppositePairs
        (data.degreeTwoBoundaryData.colorWord C) := by
  exact DegreeTwoBoundaryData.four_colorWord_classification
    data.degreeTwoBoundaryData
    (data.degreeTwoBoundaryData_wellFormed hcubic) C hC

/-- For the actual adjacent-pair deletion, the local two-vertex restoration
obstruction is exactly equality of the two request colors on each side. -/
theorem deletedAdjacentPair_not_exists_bridgeExtension_iff
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ((¬ ∃ bridge : Color,
        IsTwoVertexBridgeExtension
          (data.degreeTwoBoundaryData.colorWord C) bridge) ↔
      data.degreeTwoBoundaryData.colorWord C 0 =
        data.degreeTwoBoundaryData.colorWord C 1 ∧
      data.degreeTwoBoundaryData.colorWord C 2 =
        data.degreeTwoBoundaryData.colorWord C 3) := by
  exact DegreeTwoBoundaryData.not_exists_twoVertexBridgeExtension_iff
    data.degreeTwoBoundaryData
    (data.degreeTwoBoundaryData_wellFormed hcubic) C hC

end AdjacentPairData

end

end GoertzelV24AdjacentPairBoundary

end Mettapedia.GraphTheory.FourColor
