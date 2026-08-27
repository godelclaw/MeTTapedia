import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer
import Mettapedia.GraphTheory.FourColor.GoertzelV24InteriorDualPointwiseLookup

/-!
# Face-intersection uniqueness on the annular carrier, restricted to interior faces

Global pairwise uniqueness of shared interior edges is **false** on an opened
annulus.  A literal rotation audit refutes it on every one of the twelve
connected dodecahedral openings and on all 4,120 connected normal-form openings
through thirty-four vertices; the certificate is
`results/fourcolor/v24_open_annulus_face_uniqueness_20_34.json`.

The certificate also localises the failure.  In the recorded witness the two
faces sharing ten interior edges are the two faces the opening splices -- the
named holes -- and not a pair of ordinary interior faces.  That is the expected
shape: an ordinary face of the annulus is an unaltered face of the closed map it
was cut from, while the holes are exactly the faces the cut created.

So the corridor machinery should not ask for uniqueness on the whole carrier.
This file records the restricted property it can legitimately use, over the
cellulation's own `interiorFaces`, and supplies the pointwise premise of the
interior-dual lookup from it.

The restricted property is strictly weaker, and the local layer already proves
its own faces qualify: `face_ne_innerHole_of_mem_interiorFaces` and
`face_ne_outerHole_of_mem_interiorFaces` are exactly the membership side
conditions, and they are already applied to the layer's two internal faces.

This file does not claim the restricted property is derivable inside
`FramedAnnularCellulation`.  That structure records a rotation system, two named
holes and an Euler count, and carries no link back to an ambient closed map, so
there is nothing there to transport uniqueness from.  The restricted property
has to arrive from wherever a cellulation is built out of the minimal
counterexample.  Stating it here is what lets a consumer ask for the weaker,
unrefuted fact instead of the stronger, refuted one.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularInteriorFaceUniqueness

open GoertzelV24FramedAnnularExcess
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation
open GoertzelV24InteriorDualPointwiseLookup

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Uniqueness restricted to interior faces.**  Two distinct faces of the
annular cellulation that are neither of its named holes share at most one
interior edge.

This is the honest replacement for the global hypothesis on this carrier: the
audit that refutes the global form does not touch this one, because its failing
pairs are hole pairs. -/
def InteriorPairwiseUniqueSharedInteriorEdges
    (cell : FramedAnnularCellulation G) : Prop :=
  ∀ f ∈ cell.interiorFaces, ∀ g ∈ cell.interiorFaces, f ≠ g →
    (sharedInteriorEdges
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem)) f g).card ≤ 1

/-- The refuted global hypothesis implies the restricted one, so nothing that
already builds on the global form is weakened by moving to this. -/
theorem interiorPairwiseUnique_of_pairwiseUnique
    (cell : FramedAnnularCellulation G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))) :
    InteriorPairwiseUniqueSharedInteriorEdges cell :=
  fun f _ g _ hfg => hunique f (Finset.mem_univ _) g (Finset.mem_univ _) hfg

/-- **The pointwise premise, from the restricted hypothesis.**  This is what the
interior-dual lookup actually consumes. -/
theorem card_le_one_of_interior
    (cell : FramedAnnularCellulation G)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges cell)
    {f g : AmbientFace (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))}
    (hf : f.1 ∈ cell.interiorFaces) (hg : g.1 ∈ cell.interiorFaces)
    (hfg : (interiorDualGraph
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))).Adj f g) :
    (sharedInteriorEdges
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem)) f.1 g.1).card ≤ 1 :=
  hinterior f.1 hf g.1 hg
    ((interiorDualGraph_adj_iff _ _).1 hfg).1

/-- **The interior-dual edge on an interior face pair.**  No global uniqueness
hypothesis is used anywhere: the premise is the restricted one, and the two
faces are required to be interior. -/
noncomputable def interiorFaceEdge
    (cell : FramedAnnularCellulation G)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges cell)
    {f g : AmbientFace (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))}
    (hf : f.1 ∈ cell.interiorFaces) (hg : g.1 ∈ cell.interiorFaces)
    (hfg : (interiorDualGraph
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))).Adj f g) :
    G.edgeSet :=
  sharedInteriorEdgeOfAdj _ _ (card_le_one_of_interior cell hinterior hf hg hfg) hfg

/-- The interior lookup is pinned by any explicit shared-edge witness.  This is
the shape every corridor call site already uses, so migrating a site amounts to
supplying the two interior-membership facts it has already proved. -/
theorem interiorFaceEdge_eq_of_mem
    (cell : FramedAnnularCellulation G)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges cell)
    {f g : AmbientFace (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))}
    (hf : f.1 ∈ cell.interiorFaces) (hg : g.1 ∈ cell.interiorFaces)
    (hfg : (interiorDualGraph
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))).Adj f g)
    {e : G.edgeSet}
    (he : e ∈ sharedInteriorEdges
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem)) f.1 g.1) :
    interiorFaceEdge cell hinterior hf hg hfg = e :=
  sharedInteriorEdgeOfAdj_eq_of_mem _ _ _ hfg he

/-- Where the global hypothesis happens to be available the two lookups agree,
so a migrated call site returns the same edge as before. -/
theorem interiorFaceEdge_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    (cell : FramedAnnularCellulation G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem)))
    {f g : AmbientFace (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))}
    (hf : f.1 ∈ cell.interiorFaces) (hg : g.1 ∈ cell.interiorFaces)
    (hfg : (interiorDualGraph
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace cell.rotation.toRotationSystem))).Adj f g) :
    interiorFaceEdge cell (interiorPairwiseUnique_of_pairwiseUnique cell hunique) hf hg hfg =
      sharedInteriorEdgeOfAdjOfPairwiseUnique _ _ hunique hfg :=
  interiorFaceEdge_eq_of_mem cell _ hf hg hfg
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges _ _ hunique hfg)

end GoertzelV24AnnularInteriorFaceUniqueness

end Mettapedia.GraphTheory.FourColor
