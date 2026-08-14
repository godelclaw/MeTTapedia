import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedInteriorDual
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicFiveFaceIntersections

/-!
# Minimal-normal-form input to framed corridor geometry

For a closed ambient carrier backed by a vertex-minimal Tait counterexample,
two of the three geometric hypotheses used by weighted L1 are consequences,
not assumptions.  Two-sided quotient faces have simple edge boundaries, and
minimality excludes facial cycles of length below five.

A well-formed `SourceTrail` is already an open framed carrier with two
degree-two defects, so it cannot itself carry that closed minimality package.
The guard below makes this distinction explicit: source formation must
transport closed facts through the opening, rather than applying the closed
normal form to the open carrier.

The remaining premise below is intentionally only connectedness of the
internal facial dual after the two container faces are removed.  The bare
`AnnularEmbedding` record does not imply it: that fact belongs to the future
formation-to-graph theorem for the manuscript's Jordan annulus.  Keeping it
visible prevents a topological obligation from being hidden inside the
numerical corridor layer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24CyclicFiveFaceIntersections
open GoertzelV24FourEdgeCutGluing
open GoertzelV24MinimalFaceSize
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A well-formed framed source trail cannot itself be a graph-backed
vertex-minimal Tait counterexample: the latter is globally cubic, while the
former has its two named degree-two defect vertices.  This rules out using the
closed-minimality adapters below directly on the opened source carrier. -/
theorem graphBackedVertexMinimalTaitCounterexample_elim_of_wellFormed
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      embedded.cellulation.rotation) : False :=
  embedded.rotationSystem_not_isCubic_of_wellFormed hsource
    minimal.spherical.cubic

/-- In the vertex-minimal normal form, two distinct quotient faces of the
ambient spherical map share at most one primal edge.  This is the exact
incidence hypothesis used by the framed-corridor coordinates; it follows from
the already-proved cyclic five-edge-connectivity of a minimal counterexample,
rather than being an additional corridor assumption. -/
theorem pairwiseUniqueSharedInteriorEdges_of_vertexMinimalTaitCounterexample
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      embedded.cellulation.rotation) :
    PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G embedded.cellulation.rotation]
    exact minimal.primalConnected
  apply pairwiseUniqueSharedInteriorEdges_of_cyclicallyFiveEdgeConnected
    embedded.cellulation.rotation minimal.facesTwoSided hconnected
      minimal.spherical minimal.vertexRotationCyclic
  exact cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
    embedded.cellulation.rotation minimal

/-- In the vertex-minimal normal form, internal-dual connectedness is the
only additional geometric input needed by the weighted corridor extractor.
Boundary simplicity and minimum face size are derived from minimality. -/
theorem corridorGeometry_of_vertexMinimalTaitCounterexample
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      embedded.cellulation.rotation)
    (hinternalDualConnected :
      (interiorDualGraph
        (orbitFaceBoundary
          embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Connected) :
    embedded.CorridorGeometry := by
  refine {
    internalBoundarySimple := ?_
    internalMinimumFive := ?_
    internalDualConnected := hinternalDualConnected
  }
  · intro face _hface
    simpa [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength]
      using (orbitFaceBoundarySimple_of_twoSided
        embedded.cellulation.rotation.toRotationSystem
        minimal.facesTwoSided face)
  · intro face _hface
    exact orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample
      embedded.cellulation.rotation minimal face

/-- Formation-facing version of the adapter: the remaining premise is stated
as connectedness of the full facial dual after the two hole faces are
deleted. -/
theorem corridorGeometry_of_vertexMinimalTaitCounterexample_of_fullDualInduceConnected
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      embedded.cellulation.rotation)
    (hfullDualInduceConnected :
      ((interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).induce
        (fun face => face.1 ∈
          embedded.cellulation.interiorFaces)).Connected) :
    embedded.CorridorGeometry :=
  embedded.corridorGeometry_of_vertexMinimalTaitCounterexample minimal
    (embedded.internalDualConnected_iff_fullDualInduceConnected.mpr
      hfullDualInduceConnected)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
