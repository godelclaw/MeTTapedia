import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscut

/-!
# Closed-web rails avoid the named hole boundaries

Addendum XXVII(iii) requires the two holes to remain outside the pumped
region.  This small graph-level lemma supplies the local safety fact needed
for that bookkeeping: a facial-dual rail whose support is wholly internal to a
closed-web annulus cannot cross either of its named hole boundaries.

The statement is deliberately about the actual `ClosedWebAnnularEmbedding`
carrier used by Cell 3, rather than the separate framed-trail carrier.  It is
only an incidence argument; it does not manufacture the repeated
transversals or assert the full splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebCrosscutHoleBoundary

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/- Keep the edge carrier's equality instance aligned with the finite facial
boundaries used by the annular cellulation. -/
local instance closedWebCrosscutEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace ClosedWebAnnularEmbedding

/-- A facial-dual walk wholly contained in the annular interior cannot cross
an edge of a named hole boundary.  Its two incident dual faces are distinct
internal faces; if the same edge also met a hole face, the rotation system
would give that edge three incidences, contradicting the at-most-two facial
incidence bound. -/
theorem dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {start finish : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      start finish)
    (hsupport : ∀ face ∈ walk.support,
      face.1 ∈ embedded.cellulation.interiorFaces)
    (hole : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hhole : hole ∉ embedded.cellulation.interiorFaces) :
    Disjoint
      (dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique walk)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem hole) := by
  rw [Finset.disjoint_left]
  intro edge hcrossing hholeBoundary
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      walk edge).1 hcrossing with ⟨step, hstep⟩
  let leftFace := walk.getVert step.val
  let rightFace := walk.getVert (step.val + 1)
  have hleftRight : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (walk.adj_getVert_succ step.isLt).ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem leftFace.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique walk step
  have hright : edge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem rightFace.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique walk step
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
      leftFace.2 rightFace.2 (Finset.mem_univ hole)
      hleftRight hleft hright hholeBoundary
  rcases hcases with hholeLeft | hholeRight
  · apply hhole
    have hint := hsupport leftFace (walk.getVert_mem_support step.val)
    simpa [hholeLeft] using hint
  · apply hhole
    have hint := hsupport rightFace
      (walk.getVert_mem_support (step.val + 1))
    simpa [hholeRight] using hint

/-- In particular, an internal rail cannot cross the designated inner hole. -/
theorem dualWalkCrossingEdges_disjoint_innerHoleBoundary_of_support_internal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {start finish : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      start finish)
    (hsupport : ∀ face ∈ walk.support,
      face.1 ∈ embedded.cellulation.interiorFaces) :
    Disjoint
      (dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique walk)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.innerHole) := by
  exact dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    embedded walk hsupport embedded.cellulation.innerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- Likewise, an internal rail cannot cross the designated outer hole. -/
theorem dualWalkCrossingEdges_disjoint_outerHoleBoundary_of_support_internal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {start finish : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      start finish)
    (hsupport : ∀ face ∈ walk.support,
      face.1 ∈ embedded.cellulation.interiorFaces) :
    Disjoint
      (dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique walk)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.outerHole) := by
  exact dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    embedded walk hsupport embedded.cellulation.outerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

end ClosedWebAnnularEmbedding

end

end GoertzelV24ClosedWebCrosscutHoleBoundary

end Mettapedia.GraphTheory.FourColor
