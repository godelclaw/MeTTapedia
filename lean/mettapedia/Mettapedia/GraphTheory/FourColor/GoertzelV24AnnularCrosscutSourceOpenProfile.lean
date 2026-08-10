import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenRegionalProfile

/-!
# The source crosscut profile from a literal open coloring

The paired source transversals already construct a component whose boundary is
exactly their primal cut.  Opening that cut gives the tangle required by the
compositional `Count` semantics.  This file attaches its actual open Tait
colorings to the existing source-ordered profile carrier, rather than reading
the carrier from a hypothetical coloring of the original closed graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq
attribute [-instance] GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
attribute [-instance] GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The full finite profile of the actual component-side tangle cut open
along the paired source transversals.  Its port order and face fragments are
the existing source construction; its colors and tracked connectivity are now
read from a literal open Tait coloring of that same cut. -/
noncomputable def sourceCrosscutOpenProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).EdgeColoring Color)
    (hcoloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).IsTaitEdgeColoring coloring) :=
  slitRegionalProfile (pair.sourceCrosscutBoundaryProfileData data boundary)
    (pair.primalCutEdges data) (pair.componentSide boundary.component)
    (by
      intro edge hedge
      simpa [sourceCrosscutBoundaryProfileData,
        vertexSetBoundaryGraphCutDataWithIndexing] using hedge)
    (pair.sourceCrosscutBoundaryProfileData_portsInRegion data boundary)
    coloring hcoloring

/-- The first source-order block of the literal open profile reads exactly
the colors at the opened left transversal. -/
theorem sourceCrosscutOpenProfile_left_edgeColor
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).EdgeColoring Color)
    (hcoloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).IsTaitEdgeColoring coloring)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutOpenProfile data boundary coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.castAdd pair.right.walk.length step))).toColor =
      slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
        (pair.componentSide boundary.component) coloring
          (pair.left.crossingEdge hunique step) := by
  unfold sourceCrosscutOpenProfile
  rw [slitRegionalProfile_edgeColor_toColor]
  change slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
      (pair.componentSide boundary.component) coloring
      (vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
        (pair.componentSide boundary.component)
        (pair.sourceCrosscutBoundaryIndexing data boundary)
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.castAdd pair.right.walk.length step))) = _
  exact congrArg
    (slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
      (pair.componentSide boundary.component) coloring)
    (pair.sourceCrosscutBoundaryIndexing_left data boundary step)

/-- The second source-order block reads the corresponding opened right
transversal, after the source's aligned-rung reindexing. -/
theorem sourceCrosscutOpenProfile_right_edgeColor
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).EdgeColoring Color)
    (hcoloring : (slitRotationSystem data.toRotationSystem
      (pair.primalCutEdges data)).IsTaitEdgeColoring coloring)
    (step : Fin pair.right.walk.length) :
    ((pair.sourceCrosscutOpenProfile data boundary coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.natAdd pair.left.walk.length step))).toColor =
      slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
        (pair.componentSide boundary.component) coloring
          (pair.right.crossingEdge hunique step) := by
  unfold sourceCrosscutOpenProfile
  rw [slitRegionalProfile_edgeColor_toColor]
  change slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
      (pair.componentSide boundary.component) coloring
      (vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
        (pair.componentSide boundary.component)
        (pair.sourceCrosscutBoundaryIndexing data boundary)
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.natAdd pair.left.walk.length step))) = _
  exact congrArg
    (slitColorOnVertexSide data.toRotationSystem (pair.primalCutEdges data)
      (pair.componentSide boundary.component) coloring)
    (pair.sourceCrosscutBoundaryIndexing_right data boundary step)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
