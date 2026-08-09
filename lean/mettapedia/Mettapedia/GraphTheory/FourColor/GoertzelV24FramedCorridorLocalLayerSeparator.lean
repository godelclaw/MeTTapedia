import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedDualCycleSeparator

/-!
# Separation by a source-realized local corridor layer

The two local layers of one clean source corridor slab form an explicit simple
facial-dual loop.  The bridge-safe separator turns that checked loop into an
actual deletion cut in the framed annular graph, without recasting the loop as
an abstract chord or assuming that boundary stub edges are two-sided.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24HexFaceRungType
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24FramedAnnularExcess.FramedAnnularCellulation
open GoertzelV24FramedDualCycleSeparator
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the source corridor's edge carrier aligned with the finite face
   boundaries used by its local layer construction. -/
local instance corridorSeparatorGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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

/-- Deleting the four source edges crossed by the literal local layer loop
disconnects the framed annular graph.  This is the geometric fact needed to
promote a repeated local layer from finite profile data to a real cut. -/
theorem localLayerLoop_crossings_disconnect
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    ¬ (G.deleteEdges
      (GoertzelV24DualCycleSeparator.dualWalkPrimalCut
        embedded.cellulation.rotation hunique
      interface.localLayerLoop)).Connected := by
  exact not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
    embedded.cellulation.rotation
    embedded.cellulation.fullOrbitFaceInteriorDual_connected
    embedded.cellulation.connected embedded.cellulation.euler hunique
    interface.localLayerLoop interface.localLayerLoop_isCycle

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
