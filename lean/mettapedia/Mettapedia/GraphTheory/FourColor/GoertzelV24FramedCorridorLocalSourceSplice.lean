import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalOrderedProfile

/-!
# Exact source-splice boundary data for one corridor layer tile

A source corridor tile supplies two literal simple facial-dual layers.  The
generic annular-crosscut construction turns that pair into an actual deletion
component with its exact primal boundary, oriented boundary ports, an outer
retained side, and a genuinely removed vertex.  This is the geometric input
to an open splice; it is constructed here from the source realization rather
than left as an abstract `OrderedCutSidesData` premise.

The later corridor-composition theorem must still choose two *distinct*
source layer tiles and prove their rails form the relevant global paired
crosscuts.  This local module neither identifies a chord wall with a
transversal nor treats an arbitrary finite cut as one.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SpliceUnification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorLocalSourceSpliceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The two literal local source layers already determine the full geometric
boundary package needed by the open splice.  In particular, the component and
the removed vertex are constructed from the dual cycle rather than supplied
by a caller. -/
theorem localLayerPair_sourceCrosscutBoundaryData_nonempty
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    Nonempty (SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      embedded.cellulation.rotation interface.separatedLocalLayerPair) := by
  let hsphere : OrbitSphericalCubicMapData
      embedded.cellulation.rotation.toRotationSystem := {
    cubic := hcubic
    euler := embedded.cellulation.euler
  }
  exact SeparatedAlignedSimpleDualCrosscuts.exists_sourceCrosscutBoundaryData
    embedded.cellulation.rotation htwoSided
    embedded.cellulation.fullOrbitFaceInteriorDual_connected
    embedded.cellulation.connected hsphere
    interface.separatedLocalLayerPair

/-- The canonical source-derived deletion side of this literal corridor tile.
All its boundary facts are projections of the preceding constructive theorem. -/
noncomputable def localLayerPairSourceCrosscutBoundaryData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      embedded.cellulation.rotation interface.separatedLocalLayerPair :=
  Classical.choice
    (interface.localLayerPair_sourceCrosscutBoundaryData_nonempty hcubic)

/-- The source-local layer pair therefore instantiates the concrete,
source-ordered open-splice input.  Its two coordinate blocks are the two
literal dual layers, not a `Fintype` enumeration of their union. -/
noncomputable def localLayerPairOrderedCutSidesData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    OrderedCutSidesData embedded.cellulation.rotation.toRotationSystem
      interface.localLayer.walk.length 0
      (interface.separatedLocalLayerPair.sourceCrosscutFaceFragmentCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic)) :=
  interface.separatedLocalLayerPair.sourceCrosscutOrderedCutSidesData
    embedded.cellulation.rotation
    (interface.localLayerPairSourceCrosscutBoundaryData hcubic)

/-- The left open-splice ports are literally the first source layer's
facial-dual crossings, in path order. -/
@[simp]
theorem localLayerPairOrderedCutSidesData_left
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (step : Fin interface.localLayer.walk.length) :
    (interface.localLayerPairOrderedCutSidesData hcubic).left.crossingEdge step =
      interface.localLayer.crossingEdge hunique step :=
  SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutOrderedCutSidesData_left
    embedded.cellulation.rotation interface.separatedLocalLayerPair
    (interface.localLayerPairSourceCrosscutBoundaryData hcubic) step

/-- The right open-splice ports are literally the second source layer's
crossings, transported only along the proved equality of their two widths. -/
@[simp]
theorem localLayerPairOrderedCutSidesData_right
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (step : Fin interface.localLayer.walk.length) :
    (interface.localLayerPairOrderedCutSidesData hcubic).right.crossingEdge step =
      interface.nextLocalLayer.crossingEdge hunique
        (Fin.cast interface.separatedLocalLayerPair.length_eq step) :=
  SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutOrderedCutSidesData_right
    embedded.cellulation.rotation interface.separatedLocalLayerPair
    (interface.localLayerPairSourceCrosscutBoundaryData hcubic) step

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
