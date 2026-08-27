import Mettapedia.GraphTheory.FourColor.FaceIncidence

/-!
# The interior-dual edge lookup, pointwise

Recovering a primal edge from an adjacency in the simple interior dual needs to
know that the two faces share only one interior edge.  The existing primitive
asks for that as a *global* hypothesis, `PairwiseUniqueSharedInteriorEdges` over
the whole face set, and then consumes it at a single pair.

That global form is not available where the corridor machinery uses it.  On an
opened annulus it is false: an independent literal rotation audit finds that all
twelve connected dodecahedral openings fail it, as does every one of the 4,120
connected normal-form openings through twenty-four vertices, and the two opened
faces of the dodecahedron share ten interior edges.  The audit and its
certificates are recorded under `results/fourcolor/`.

The failure is confined to the faces the opening splices.  Faces that survive
the opening intact still inherit uniqueness from the closed carrier, and that
transport is already proved.  So the repair is to stop asking for a global fact
at all: this file restates the lookup and its two characterising equations with
the *pointwise* premise they actually use, namely that the one pair in hand
shares at most one interior edge.

Nothing here is weaker than before.  The global hypothesis still implies the
pointwise one, and the final theorems record that the two lookups then agree, so
existing consumers can be migrated one at a time without changing any result.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InteriorDualPointwiseLookup

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

omit [DecidableEq F] in
/-- **The pointwise premise suffices.**  A dual adjacency together with the
single-pair bound already determines the primal edge. -/
theorem existsUnique_sharedInteriorEdge_of_adj_of_card_le_one
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {f g : AmbientFace allFaces}
    (hcard : (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1)
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    ∃! e, e ∈ sharedInteriorEdges faceBoundary allFaces f.1 g.1 := by
  rcases (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty faceBoundary allFaces).1 hfg with
    ⟨-, ⟨e, he⟩⟩
  exact ⟨e, he, fun e' he' => (Finset.card_le_one_iff.1 hcard) he' he⟩

/-- The canonical primal interior edge attached to a dual adjacency, asking only
that this one face pair shares at most one interior edge. -/
noncomputable def sharedInteriorEdgeOfAdj
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {f g : AmbientFace allFaces}
    (hcard : (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1)
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) : E :=
  Classical.choose <|
    existsUnique_sharedInteriorEdge_of_adj_of_card_le_one faceBoundary allFaces hcard hfg

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdj_mem
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {f g : AmbientFace allFaces}
    (hcard : (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1)
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdj faceBoundary allFaces hcard hfg ∈
      sharedInteriorEdges faceBoundary allFaces f.1 g.1 :=
  (Classical.choose_spec <|
    existsUnique_sharedInteriorEdge_of_adj_of_card_le_one faceBoundary allFaces hcard hfg).1

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdj_eq_of_mem
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {f g : AmbientFace allFaces}
    (hcard : (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1)
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g)
    {e : E} (he : e ∈ sharedInteriorEdges faceBoundary allFaces f.1 g.1) :
    sharedInteriorEdgeOfAdj faceBoundary allFaces hcard hfg = e :=
  (Finset.card_le_one_iff.1 hcard)
    (sharedInteriorEdgeOfAdj_mem faceBoundary allFaces hcard hfg) he

omit [DecidableEq F] in
/-- A packaged interior edge is recovered by the pointwise lookup. -/
theorem sharedInteriorEdgeOfAdj_eq_of_interiorEdgeFacePair_of_adj
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {e : E} (pair : InteriorEdgeFacePair faceBoundary allFaces e)
    (hcard : (sharedInteriorEdges faceBoundary allFaces pair.left.1 pair.right.1).card ≤ 1)
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj pair.left pair.right) :
    sharedInteriorEdgeOfAdj faceBoundary allFaces hcard hfg = e :=
  sharedInteriorEdgeOfAdj_eq_of_mem faceBoundary allFaces hcard hfg <|
    (mem_sharedInteriorEdges_iff faceBoundary allFaces).2
      ⟨pair.edge_interior, pair.edge_mem_left, pair.edge_mem_right⟩

omit [DecidableEq F] in
/-- The global hypothesis implies the pointwise one at every dual adjacency, so
the pointwise premise is genuinely weaker. -/
theorem card_le_one_of_pairwiseUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1 :=
  hunique f.1 f.2 g.1 g.2 ((interiorDualGraph_adj_iff faceBoundary allFaces).1 hfg).1

omit [DecidableEq F] in
/-- **Migration is safe.**  Where the global hypothesis is available the two
lookups select the same edge, so a consumer may be moved to the pointwise
premise without changing any downstream value. -/
theorem sharedInteriorEdgeOfAdj_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdj faceBoundary allFaces
        (card_le_one_of_pairwiseUnique faceBoundary allFaces hunique hfg) hfg =
      sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique hfg :=
  sharedInteriorEdgeOfAdj_eq_of_mem faceBoundary allFaces _ hfg
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
      faceBoundary allFaces hunique hfg)

omit [DecidableEq F] in
/-- The selected edge does not depend on which proof of the pointwise bound is
supplied, so a consumer may thread whichever local witness it has. -/
theorem sharedInteriorEdgeOfAdj_congr
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {f g : AmbientFace allFaces}
    (hcard hcard' : (sharedInteriorEdges faceBoundary allFaces f.1 g.1).card ≤ 1)
    (hfg hfg' : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdj faceBoundary allFaces hcard hfg =
      sharedInteriorEdgeOfAdj faceBoundary allFaces hcard' hfg' :=
  sharedInteriorEdgeOfAdj_eq_of_mem faceBoundary allFaces hcard hfg
    (sharedInteriorEdgeOfAdj_mem faceBoundary allFaces hcard' hfg')

end GoertzelV24InteriorDualPointwiseLookup

end Mettapedia.GraphTheory.FourColor
