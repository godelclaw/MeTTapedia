import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareLineProfile

namespace Mettapedia.GraphTheory.FourColor

set_option maxHeartbeats 4000000

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- The ambient line graph restricted to edges carrying either tracked
color. Vertices remain on the original edge type. -/
def trackedEdgeGraph (C : E → Color) (a b : Color) : SimpleGraph E where
  Adj e f := RS.edgeAdjacencyGraph.Adj e f ∧
    IsTrackedColor a b (C e) ∧ IsTrackedColor a b (C f)
  symm := ⟨by
    intro e f h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro e h
    exact h.1.1 rfl⟩

namespace FacialSquareData

/-- Interpret the four portal nodes followed by the four internal line nodes
as the eight named edges of a facial square. -/
def lineEdge (Q : @FacialSquareData V E) (u : SquareLocalNode) : E :=
  if u = 0 then Q.outerW else
  if u = 1 then Q.outerX else
  if u = 2 then Q.outerY else
  if u = 3 then Q.outerZ else
  if u = 4 then Q.wx else
  if u = 5 then Q.xy else
  if u = 6 then Q.yz else Q.zw

/-- Computed injectivity predicate for the eight named local edges. -/
def LocalEdgesDistinct (Q : @FacialSquareData V E) : Prop :=
  Function.Injective Q.lineEdge

/-- The tracked exterior after deleting the four internal square-edge
vertices. The four outer edges remain as the gluing interface. -/
def exteriorTrackedEdgeGraph (Q : @FacialSquareData V E)
    (C : E → Color) (a b : Color) : SimpleGraph E where
  Adj e f := (RS.trackedEdgeGraph C a b).Adj e f ∧
    e ∉ Q.squareEdges ∧ f ∉ Q.squareEdges
  symm := ⟨by
    intro e f h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro e h
    exact h.1.1.1 rfl⟩

/-- The abstract eight-edge square line graph mapped onto its named ambient
rotation-system edges. -/
def localTrackedEdgeGraph (Q : @FacialSquareData V E)
    (C : E → Color) (a b : Color) : SimpleGraph E :=
  (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).map Q.lineEdge

end FacialSquareData

/-- Every adjacency in the abstract eight-edge square line graph maps to a
genuine adjacency of the named rotation-system edges. -/
theorem facialSquare_lineEdge_maps_adj
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) {u v : SquareLocalNode}
    (huv : (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).Adj u v) :
    RS.edgeAdjacencyGraph.Adj (Q.lineEdge u) (Q.lineEdge v) := by
  have hne (i j : SquareLocalNode) (hij : i ≠ j) :
      Q.lineEdge i ≠ Q.lineEdge j := hdist.ne hij
  have adj04 : RS.edgeAdjacencyGraph.Adj Q.outerW Q.wx :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 0 4 (by decide))
      (by rw [hQ.2.1]; simp) (by rw [hQ.2.1]; simp)
  have adj07 : RS.edgeAdjacencyGraph.Adj Q.outerW Q.zw :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 0 7 (by decide))
      (by rw [hQ.2.1]; simp) (by rw [hQ.2.1]; simp)
  have adj14 : RS.edgeAdjacencyGraph.Adj Q.outerX Q.wx :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 1 4 (by decide))
      (by rw [hQ.2.2.1]; simp) (by rw [hQ.2.2.1]; simp)
  have adj15 : RS.edgeAdjacencyGraph.Adj Q.outerX Q.xy :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 1 5 (by decide))
      (by rw [hQ.2.2.1]; simp) (by rw [hQ.2.2.1]; simp)
  have adj25 : RS.edgeAdjacencyGraph.Adj Q.outerY Q.xy :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 2 5 (by decide))
      (by rw [hQ.2.2.2.1]; simp) (by rw [hQ.2.2.2.1]; simp)
  have adj26 : RS.edgeAdjacencyGraph.Adj Q.outerY Q.yz :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 2 6 (by decide))
      (by rw [hQ.2.2.2.1]; simp) (by rw [hQ.2.2.2.1]; simp)
  have adj36 : RS.edgeAdjacencyGraph.Adj Q.outerZ Q.yz :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 3 6 (by decide))
      (by rw [hQ.2.2.2.2.1]; simp) (by rw [hQ.2.2.2.2.1]; simp)
  have adj37 : RS.edgeAdjacencyGraph.Adj Q.outerZ Q.zw :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 3 7 (by decide))
      (by rw [hQ.2.2.2.2.1]; simp) (by rw [hQ.2.2.2.2.1]; simp)
  have adj45 : RS.edgeAdjacencyGraph.Adj Q.wx Q.xy :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 4 5 (by decide))
      (by rw [hQ.2.2.1]; simp) (by rw [hQ.2.2.1]; simp)
  have adj56 : RS.edgeAdjacencyGraph.Adj Q.xy Q.yz :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 5 6 (by decide))
      (by rw [hQ.2.2.2.1]; simp) (by rw [hQ.2.2.2.1]; simp)
  have adj67 : RS.edgeAdjacencyGraph.Adj Q.yz Q.zw :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 6 7 (by decide))
      (by rw [hQ.2.2.2.2.1]; simp) (by rw [hQ.2.2.2.2.1]; simp)
  have adj74 : RS.edgeAdjacencyGraph.Adj Q.zw Q.wx :=
    RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      (by simpa [FacialSquareData.lineEdge] using hne 7 4 (by decide))
      (by rw [hQ.2.1]; simp) (by rw [hQ.2.1]; simp)
  fin_cases u <;> fin_cases v <;>
    simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
      SquareUndirectedEdge, squarePortalNode, squareCornerNode,
      FacialSquareData.boundaryWord,
      FacialSquareData.internalColoring, FacialSquareData.colorQuad] at huv
  all_goals
    first
    | simpa [FacialSquareData.lineEdge] using adj04
    | simpa [FacialSquareData.lineEdge] using adj04.symm
    | simpa [FacialSquareData.lineEdge] using adj07
    | simpa [FacialSquareData.lineEdge] using adj07.symm
    | simpa [FacialSquareData.lineEdge] using adj14
    | simpa [FacialSquareData.lineEdge] using adj14.symm
    | simpa [FacialSquareData.lineEdge] using adj15
    | simpa [FacialSquareData.lineEdge] using adj15.symm
    | simpa [FacialSquareData.lineEdge] using adj25
    | simpa [FacialSquareData.lineEdge] using adj25.symm
    | simpa [FacialSquareData.lineEdge] using adj26
    | simpa [FacialSquareData.lineEdge] using adj26.symm
    | simpa [FacialSquareData.lineEdge] using adj36
    | simpa [FacialSquareData.lineEdge] using adj36.symm
    | simpa [FacialSquareData.lineEdge] using adj37
    | simpa [FacialSquareData.lineEdge] using adj37.symm
    | simpa [FacialSquareData.lineEdge] using adj45
    | simpa [FacialSquareData.lineEdge] using adj45.symm
    | simpa [FacialSquareData.lineEdge] using adj56
    | simpa [FacialSquareData.lineEdge] using adj56.symm
    | simpa [FacialSquareData.lineEdge] using adj67
    | simpa [FacialSquareData.lineEdge] using adj67.symm
    | simpa [FacialSquareData.lineEdge] using adj74
    | simpa [FacialSquareData.lineEdge] using adj74.symm

/-- A mapped endpoint of a local line-graph adjacency carries one of the
tracked colors. -/
theorem facialSquare_lineEdge_tracked_left
    (Q : @FacialSquareData V E) (C : E → Color) (a b : Color)
    {u v : SquareLocalNode}
    (huv : (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).Adj u v) :
    IsTrackedColor a b (C (Q.lineEdge u)) := by
  fin_cases u <;> fin_cases v <;>
    simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
      SquareUndirectedEdge, squarePortalNode, squareCornerNode,
      FacialSquareData.lineEdge, FacialSquareData.boundaryWord,
      FacialSquareData.internalColoring, FacialSquareData.colorQuad] at huv ⊢ <;>
    aesop

/-- The mapped local square line graph is a subgraph of the full ambient
tracked-edge graph. -/
theorem facialSquare_localTrackedEdgeGraph_le
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) :
    Q.localTrackedEdgeGraph C a b ≤ RS.trackedEdgeGraph C a b := by
  intro e f hef
  rcases (SimpleGraph.map_adj' Q.lineEdge
    (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b) e f).mp hef with
    ⟨_ne, u, v, huv, rfl, rfl⟩
  refine ⟨facialSquare_lineEdge_maps_adj RS Q hQ hdist C a b huv, ?_, ?_⟩
  · exact facialSquare_lineEdge_tracked_left Q C a b huv
  · exact facialSquare_lineEdge_tracked_left Q C a b huv.symm

/-- Every ambient tracked adjacency incident to a square edge is realized in
the mapped local line graph. -/
theorem trackedEdgeGraph_adj_mem_local_of_left_mem_squareEdges
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (C : E → Color) (a b : Color) {e f : E}
    (hef : (RS.trackedEdgeGraph C a b).Adj e f)
    (he : e ∈ Q.squareEdges) :
    (Q.localTrackedEdgeGraph C a b).Adj e f := by
  have hends := RS.facialSquare_edgeEndpoints Q hQ
  rcases (RS.edgeAdjacencyGraph_adj_iff).mp hef.1 with
    ⟨hne, p, hpe, hpf⟩
  have hpfInc : f ∈ RS.incidentEdges p :=
    RS.mem_endpoints_iff_mem_incidentEdges.mp hpf
  simp only [FacialSquareData.squareEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [hends.1] at hpe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpe
    rcases hpe with rfl | rfl
    · rw [hQ.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 4, 0, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 4, 7, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
    · rw [hQ.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 4, 1, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 4, 5, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.1, hef.2.2⟩

  · rw [hends.2.1] at hpe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpe
    rcases hpe with rfl | rfl
    · rw [hQ.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 5, 1, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 5, 4, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
    · rw [hQ.2.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 5, 2, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 5, 6, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.1, hef.2.2⟩

  · rw [hends.2.2.1] at hpe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpe
    rcases hpe with rfl | rfl
    · rw [hQ.2.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 6, 2, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 6, 5, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
    · rw [hQ.2.2.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 6, 3, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 6, 7, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.1, hef.2.2⟩
  · rw [hends.2.2.2] at hpe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpe
    rcases hpe with rfl | rfl
    · rw [hQ.2.2.2.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 7, 3, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 7, 6, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
    · rw [hQ.2.1] at hpfInc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpfInc
      rcases hpfInc with rfl | rfl | rfl
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 7, 0, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.2, hef.2.1⟩
      · exact False.elim (hne rfl)
      · refine (SimpleGraph.map_adj' Q.lineEdge _ _ _).mpr
          ⟨hne, 7, 4, ?_, rfl, rfl⟩
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode,
          FacialSquareData.boundaryWord, FacialSquareData.internalColoring,
          FacialSquareData.colorQuad]
        exact ⟨hef.2.1, hef.2.2⟩

/-- Exact graph-level facial-square factorization. The full tracked-edge graph
is the supremum of the graph obtained by deleting the four internal square
edges and the mapped local eight-edge line graph. `LocalEdgesDistinct` is a
computed predicate on the named data, not a stored realization field. -/
theorem trackedEdgeGraph_eq_exterior_sup_facialSquareLocal
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) :
    RS.trackedEdgeGraph C a b =
      Q.exteriorTrackedEdgeGraph RS C a b ⊔ Q.localTrackedEdgeGraph C a b := by
  ext e f
  simp only [SimpleGraph.sup_adj]
  constructor
  · intro hef
    by_cases he : e ∈ Q.squareEdges
    · exact Or.inr
        (trackedEdgeGraph_adj_mem_local_of_left_mem_squareEdges RS Q hQ C a b hef he)
    · by_cases hf : f ∈ Q.squareEdges
      · exact Or.inr
          (trackedEdgeGraph_adj_mem_local_of_left_mem_squareEdges
            RS Q hQ C a b hef.symm hf).symm
      · exact Or.inl ⟨hef, he, hf⟩
  · rintro (hef | hef)
    · exact hef.1
    · exact facialSquare_localTrackedEdgeGraph_le RS Q hQ hdist C a b hef

end RotationSystem

end Mettapedia.GraphTheory.FourColor
