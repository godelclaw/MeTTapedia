import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebProfileSpliceBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalProfile

/-!
# Finite L7 state of a source corridor slab

The source transfer state must be computed from a real open region, rather
than introduced as an abstract finite label.  A paired local layer now has an
exact deletion component and four actual crossing ports.  This file places
that computed profile in the common finite L7 carrier of width four.

It is intentionally local: a single slab is a generator for the open
corridor category.  The later corridor-composition construction must prove
which consecutive generators form the two global repeated layer boundaries;
this module does not identify a local cell wall with that global boundary.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebProfileSpliceBridge
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the component-profile carrier definitionally aligned with the source
   slab construction, despite a broader imported splice module installing an
   extensionally equal global instance. -/
local instance corridorLocalDepthProfileGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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

/-- The literal source slab has a bounded L7 profile: its four crossed primal
edges carry all of the cut colors, connectivity, and capped face data. -/
noncomputable def localLayerDepthProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 4 :=
  graphCutDepthProfile 4 interface.localLayerProfileData coloring hcoloring
    (by
      rw [interface.localLayerProfile_crossingCard_eq_four])
    (vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent))

/-- The L7 carrier does not hide a synthetic region: its profile payload is
definitionally the profile computed from the selected source slab component. -/
theorem localLayerDepthProfile_profile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    (interface.localLayerDepthProfile coloring hcoloring).profile.profile =
      interface.localLayerProfileData.profile coloring hcoloring := by
  rfl

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
