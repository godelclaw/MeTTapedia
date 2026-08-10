import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections

/-!
# Minimal-normal-form rails for the Cell-3 closed-web corridor

Addendum XXVII takes its profiles on actual simple transversal/layer
boundaries.  Before constructing those boundaries, the clean corridor needs
two concrete ambient facts: a facial edge has two distinct sides, and two
different faces have at most one shared edge.  These are not extra corridor
assumptions.  They follow from the source minimal-counterexample normal form:
the first is stored in the graph-backed minimal carrier and the second is the
existing two-edge-separator consequence of that carrier.

This file transports those facts to the actual Cell-3
`ClosedWebAtGoodWord.Instance`, then turns the source's boundary-clean L1
block into a corridor with canonical, noncolliding rung edges.  It does not
claim that the rungs already form transversals; that is the next geometric
construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebMinimalCorridorEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- The Cell-3 ambient map is facially two-sided when it is the map of a
vertex-minimal counterexample.  This is the precise normal-form fact needed
to read a unique dart position for each selected corridor rung. -/
theorem facesTwoSided_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    OrbitFacesTwoSided web.annular.cellulation.rotation.toRotationSystem :=
  minimal.facesTwoSided

/-- In the same normal form, two quotient faces of the actual closed-web map
share at most one primal edge.  Thus a facial-dual adjacency has one
canonical rung rather than an arbitrary choice among parallel contacts. -/
theorem pairwiseUniqueSharedInteriorEdges_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace web.annular.cellulation.rotation.toRotationSystem)) :=
  GoertzelV24MinimalFaceIntersections.pairwiseUniqueSharedInteriorEdges
    web.annular.cellulation.rotation minimal

/-- A boundary-clean Cell-3 L1 block in minimal normal form has actual,
injectively indexed primal rungs.  This is the concrete input for assembling
the source's simple layer boundaries; no profile or abstract separator is
introduced here. -/
theorem exists_cleanCorridorWithCanonicalRungs_of_boundaryCleanBlock
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation)
    (blockLength : Nat)
    (hclean : web.annular.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    ∃ clean : CleanOrbitHexCorridorSkeleton
        web.annular.cellulation.rotation.toRotationSystem blockLength,
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
          (orbitFaceBoundary web.annular.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace web.annular.cellulation.rotation.toRotationSystem)),
        Function.Injective
          (clean.toOrbitHexCorridorSkeleton.rungEdge hunique) ∧
        ∀ offset : Fin (blockLength - 2),
          Nonempty (InternalHexRungPlacement
            clean.toOrbitHexCorridorSkeleton hunique
            (corridorInteriorOfOffset offset)) := by
  let clean : CleanOrbitHexCorridorSkeleton
      web.annular.cellulation.rotation.toRotationSystem blockLength :=
    Classical.choice
      (web.annular.nonempty_cleanOrbitHexCorridorSkeleton_of_boundaryCleanBlock
        blockLength hclean)
  let hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace web.annular.cellulation.rotation.toRotationSystem)) :=
    web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal
  let htwoSided : OrbitFacesTwoSided
      web.annular.cellulation.rotation.toRotationSystem :=
    web.facesTwoSided_of_minimal minimal
  refine ⟨clean, hunique, ?_, ?_⟩
  · exact clean.toOrbitHexCorridorSkeleton.rungEdge_injective
      htwoSided hunique
  · intro offset
    exact exists_internalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton htwoSided hunique
        (corridorInteriorOfOffset offset)

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
