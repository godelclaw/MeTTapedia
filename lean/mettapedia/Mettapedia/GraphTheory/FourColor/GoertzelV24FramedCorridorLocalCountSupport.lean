import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSerialOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialCountSupport

/-!
# `Count` support of source Cell-3 corridor tiles

The framed source corridor constructs a literal two-boundary open tangle at
each Cell-3 position.  This file reads its coloring support in the common
two-position source coordinate and installs the generic support-composition
and relevant-profile pumping laws at that concrete geometry.

The remaining L2 content is deliberately visible as
`localLayerPairSupportsOrderedIdentityOn`: proving it requires the source's
finite stay-transition calculation for the relevant full profiles.  It is
not inferred from finiteness or from the existence of one ambient coloring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorLocalCountSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
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
  {leftInterior loopInterior rightInterior : CorridorInterior blockLength}
  {hleftNext : leftInterior.center.val + 2 < blockLength}
  {hloopNext : loopInterior.center.val + 2 < blockLength}
  {hrightNext : rightInterior.center.val + 2 < blockLength}

/-- Boundary-word support of one literal source Cell-3 tile. -/
def localLayerPairAcceptsOrderedBoundaryWords
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hleftNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftWord rightWord : Fin 2 → Color) : Prop :=
  (interface.localLayerPairOrderedCutSidesDataTwo hcubic)
    |>.AcceptsOrderedBoundaryWords leftWord rightWord

/-- The exact source-local L2 obligation: every relevant two-position word
has an identity-like realization through this concrete tile. -/
def localLayerPairSupportsOrderedIdentityOn
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hleftNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : (Fin 2 → Color) → Prop) : Prop :=
  (interface.localLayerPairOrderedCutSidesDataTwo hcubic)
    |>.SupportsOrderedIdentityOn Relevant

/-- Exterior support of two source tiles joined through their common ordered
two-position interface. -/
def serialLocalLayerPairsAcceptOrderedBoundaryWords
    (leftInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique leftInterior hleftNext)
    (rightInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique rightInterior hrightNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftWord rightWord : Fin 2 → Color) : Prop :=
  (leftInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    |>.SerialAcceptsOrderedBoundaryWords
      (rightInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
      leftWord rightWord

/-- Source-tile support composes by existentially matching the middle
source-coordinate word. -/
theorem serialLocalLayerPairsAcceptOrderedBoundaryWords_iff
    (leftInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique leftInterior hleftNext)
    (rightInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique rightInterior hrightNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftWord rightWord : Fin 2 → Color) :
    serialLocalLayerPairsAcceptOrderedBoundaryWords leftInterface rightInterface
        hcubic leftWord rightWord ↔
      ∃ middle : Fin 2 → Color,
        localLayerPairAcceptsOrderedBoundaryWords leftInterface hcubic
          leftWord middle ∧
        localLayerPairAcceptsOrderedBoundaryWords rightInterface hcubic
          middle rightWord := by
  exact OrderedCutSidesData.serialAcceptsOrderedBoundaryWords_iff
    (leftInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    (rightInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    leftWord rightWord

/-- Exterior support after inserting a third source tile between two others. -/
def pumpedLocalLayerPairsAcceptOrderedBoundaryWords
    (leftInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique leftInterior hleftNext)
    (loopInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique loopInterior hloopNext)
    (rightInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique rightInterior hrightNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftWord rightWord : Fin 2 → Color) : Prop :=
  let leftData := leftInterface.localLayerPairOrderedCutSidesDataTwo hcubic
  let loopData := loopInterface.localLayerPairOrderedCutSidesDataTwo hcubic
  let rightData := rightInterface.localLayerPairOrderedCutSidesDataTwo hcubic
  (TwoSidedOpenTangleData.serialCompose (leftData.serialCompose loopData)
      rightData.toTwoSidedOpenTangle
      (OrderedCutSidesData.rightToLeftBoundaryMatching loopData rightData))
    |>.AcceptsBoundaryWords
      (leftData.leftBoundaryWord leftWord) (rightData.rightBoundaryWord rightWord)

/-- The concrete source-tile pumping consequence.  Its hypotheses separate
the two real tasks: the middle tile realizes identity on relevant profiles,
and any seam word occurring in the shortened composition is relevant. -/
theorem pumpedLocalLayerPairsAcceptOrderedBoundaryWords_of_relevantIdentity
    (leftInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique leftInterior hleftNext)
    (loopInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique loopInterior hloopNext)
    (rightInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique rightInterior hrightNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : (Fin 2 → Color) → Prop)
    (hloop : localLayerPairSupportsOrderedIdentityOn loopInterface hcubic Relevant)
    (leftWord rightWord : Fin 2 → Color)
    (hrelevant : ∀ middle : Fin 2 → Color,
      localLayerPairAcceptsOrderedBoundaryWords leftInterface hcubic
          leftWord middle →
      localLayerPairAcceptsOrderedBoundaryWords rightInterface hcubic
          middle rightWord →
      Relevant middle)
    (hshort : serialLocalLayerPairsAcceptOrderedBoundaryWords
      leftInterface rightInterface hcubic leftWord rightWord) :
    pumpedLocalLayerPairsAcceptOrderedBoundaryWords leftInterface loopInterface
      rightInterface hcubic leftWord rightWord := by
  exact OrderedCutSidesData.serialSupport_pump_of_orderedIdentityOn
    (leftInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    (loopInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    (rightInterface.localLayerPairOrderedCutSidesDataTwo hcubic)
    Relevant hloop leftWord rightWord hrelevant hshort

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
