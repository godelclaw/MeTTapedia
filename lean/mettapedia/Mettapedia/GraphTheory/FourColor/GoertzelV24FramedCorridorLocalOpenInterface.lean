import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerPair

/-!
# Open-interface realization of a source corridor slab

The source treats a clean corridor as a composite of open slabs.  This file
turns one literal pair of source-derived local layers into that open object:
the four crossed primal edges become four fresh boundary ends, and any
left-to-right gluing of those ends is loop-free in the slit rotation system.
This is local formation data; the later corridor induction is responsible for
assembling these local interfaces into a boundary-to-boundary transversal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorOpenInterfaceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/- Keep the cut-dart carrier on Lean's ordinary subtype enumeration.  The
   source-open construction was compiled before the retained-vertex splice
   module introduced an extensionally equivalent finite instance, so selecting
   this concrete one avoids an irrelevant instance mismatch at the interface. -/
local instance corridorOpenInterfaceCutDartFintype
    {RS : RotationSystem V G.edgeSet} (cut : Finset G.edgeSet) :
    Fintype (CutDart RS cut) :=
  Subtype.fintype _

local instance corridorOpenInterfaceCutDartDecidableEq
    {RS : RotationSystem V G.edgeSet} (cut : Finset G.edgeSet) :
    DecidableEq (CutDart RS cut) :=
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

/-- A literal source corridor slab opens exactly four distinct primal edges:
two on each of its paired local layers. -/
theorem localLayerPair_crossingSupport_card_eq_four
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerPair.crossingSupport.card = 4 := by
  have hcard := interface.localLayerPair.card_crossingSupport_eq_twice_left_length
    (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
  change interface.localLayerPair.crossingSupport.card =
    2 * interface.localLayer.walk.length at hcard
  rw [interface.localLayer_walk_length_eq_two] at hcard
  norm_num at hcard ⊢
  exact hcard

/-- The actual source slab is a well-formed generator of the open-interface
semantics: after opening its two local layers, identifying any corresponding
left and right ports cannot create a self-loop.  The distinctness is proved
in the slit map itself, so it does not rely on the old closed graph having
different endpoint vertices. -/
theorem localLayerPair_openInterface_matching_no_selfLoop
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (matching : interface.localLayerPair.LeftInterfaceEnd →
      interface.localLayerPair.RightInterfaceEnd) :
    ∀ left,
      (interface.localLayerPair.slitRotationSystem).vertOf
          (interface.localLayerPair.leftInterfaceStub left) ≠
        (interface.localLayerPair.slitRotationSystem).vertOf
          (interface.localLayerPair.rightInterfaceStub (matching left)) := by
  exact interface.localLayerPair.openInterface_matching_no_selfLoop matching

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
