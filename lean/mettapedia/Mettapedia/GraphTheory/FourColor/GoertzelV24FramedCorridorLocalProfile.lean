import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComponentProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerComponent

/-!
# Profile carrier of a source corridor slab

The source's finite profile is meaningful only when it is computed from an
actual cut-open region.  The local source slab now has such a region: its
paired layers give an exact deletion component, whose graph-derived profile
data is therefore available without a caller-provided side predicate.  This
file connects the literal four-edge slab generator to the finite profile
engine used by the compositional splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorLocalProfileGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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

/-- The generic paired-crosscut cut carrier is definitionally the literal
four-edge source layer wall constructed from the slab rotations. -/
theorem separatedLocalLayerPair_primalCutEdges_eq_localLayerLoopCutEdges
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.separatedLocalLayerPair.primalCutEdges embedded.cellulation.rotation =
      interface.localLayerLoopCutEdges := by
  rfl

/-- The actual deletion component selected by the source slab's simple
layer loop, retargeted to the generic paired-crosscut profile carrier. -/
noncomputable def localLayerProfileComponent
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (G.deleteEdges (edgeFinsetValueSet
      (interface.separatedLocalLayerPair.primalCutEdges
        embedded.cellulation.rotation))).ConnectedComponent :=
  Classical.choose interface.exists_localLayerLoop_component_exactBoundary

/-- The profile component has exactly the source layer wall as its computed
boundary, so no abstract chord-side or external separator is left in this
local profile construction. -/
theorem localLayerProfileComponent_boundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    componentCrossingEdges
      (interface.separatedLocalLayerPair.primalCutEdges
        embedded.cellulation.rotation)
      interface.localLayerProfileComponent =
        interface.separatedLocalLayerPair.primalCutEdges
          embedded.cellulation.rotation := by
  exact Classical.choose_spec interface.exists_localLayerLoop_component_exactBoundary

/-- The source local profile is computed from the component side exposed by
the paired layer cut.  It includes the real port colors, connectivity, and
face-fragment data used by the finite-state factorization. -/
noncomputable def localLayerProfileData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  interface.separatedLocalLayerPair.componentBoundaryProfileData
    embedded.cellulation.rotation interface.localLayerProfileComponent

/-- Every port in the local source profile lies in the certified component
region, rather than in an arbitrary syntactic finite carrier. -/
theorem localLayerProfileData_portsInRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerProfileData.PortsInRegion := by
  exact interface.separatedLocalLayerPair.componentBoundaryProfileData_portsInRegion
    embedded.cellulation.rotation interface.localLayerProfileComponent

/-- The actual local profile has four crossing ports: two from each of its
paired source layers. -/
theorem localLayerProfile_crossingCard_eq_four
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent)) = 4 := by
  calc
    Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent)) =
        interface.separatedLocalLayerPair.left.walk.length +
          interface.separatedLocalLayerPair.right.walk.length :=
      interface.separatedLocalLayerPair.componentBoundaryProfileData_crossingCard_eq_interfaceWidths
        embedded.cellulation.rotation interface.localLayerProfileComponent
        interface.localLayerProfileComponent_boundary
    _ = 4 := by
      simp [SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface.localLayer_walk_length_eq_two,
        interface.nextLocalLayer_walk_length_eq_two]

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
