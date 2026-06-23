import Mettapedia.GraphTheory.PlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.FourColor.FaceIncidence

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- For a boundary-aware plane embedding, the generic ambient-face incidence count used in the
four-color route is exactly the embedding's own face-incidence count. -/
theorem planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    totalIncidenceCount emb.faceBoundary emb.faces e = emb.totalFaceIncidenceCount e :=
  rfl

theorem planeEmbeddingWithBoundary_totalIncidenceCount_eq_zero_of_not_mem_faceSupport
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet}
    (he : e ∉ emb.faceSupport) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 0 := by
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport he

theorem planeEmbeddingWithBoundary_totalIncidenceCount_pos
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    0 < totalIncidenceCount emb.faceBoundary emb.faces e := by
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_pos e

theorem planeEmbeddingWithBoundary_totalIncidenceCount_le_two
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2 := by
  intro e
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_le_two e

theorem planeEmbeddingWithBoundary_mem_interiorEdgeSupport_iff_totalFaceIncidenceCount_eq_two
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet} :
    e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ↔
      emb.totalFaceIncidenceCount e = 2 := by
  constructor
  · intro he
    rcases (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 he with ⟨_, hcount⟩
    simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using hcount
  · intro hcount
    refine (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).2 ?_
    exact ⟨by simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e,
      by simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using hcount⟩

/-- For a boundary-aware plane embedding, an edge with face-incidence count two has exactly two
ambient incident faces in the generic face-incidence model. -/
noncomputable def planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet}
    (hcount : emb.totalFaceIncidenceCount e = 2) :
    InteriorEdgeFacePair emb.faceBoundary emb.faces e :=
  interiorEdgeFacePairOfMem emb.faceBoundary emb.faces
    ((planeEmbeddingWithBoundary_mem_interiorEdgeSupport_iff_totalFaceIncidenceCount_eq_two emb).2
      hcount)

theorem planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount_interiorDualGraph_adj
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet}
    (hcount : emb.totalFaceIncidenceCount e = 2) :
    (interiorDualGraph emb.faceBoundary emb.faces).Adj
      (planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount emb hcount).left
      (planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount emb hcount).right :=
  (planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount emb hcount).interiorDualGraph_adj

theorem planeEmbeddingWithBoundary_sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_totalFaceIncidenceCount_eq_two
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    {e : G.edgeSet} (hcount : emb.totalFaceIncidenceCount e = 2) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique emb.faceBoundary emb.faces hunique
      (planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount emb hcount).interiorDualGraph_adj = e :=
  sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_interiorEdgeFacePair
    emb.faceBoundary emb.faces hunique
    (planeEmbeddingWithBoundaryInteriorEdgeFacePairOfCount emb hcount)

end Mettapedia.GraphTheory.FourColor
