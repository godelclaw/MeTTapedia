import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSuccessorCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceOldCapAdequacy

/-!
# Exact successor face cap with a finite predecessor decoder

The geometric successor inclusion--exclusion law formerly queried the entire
old prefix to obtain its capped face contribution.  The finite predecessor
decoder now computes that term exactly.  This file substitutes the adequacy
theorem into the successor law, leaving only the newly displayed two-edge
slice and its literal overlap with the old slice.

This is one source-faithful recurrence equation, not yet a graph-free Cell
letter: the new slice and overlap still have to be decoded from the bounded
local receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFinitePredecessorCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The successor capped face length uses the finite predecessor component
sum, together with the literal new two-edge slice and their true overlap. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_finiteOldSum
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let oldRegion :=
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
    let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
      hcubic hrotation htwoSided hunique offset hnext
    let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
      hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let boundaryFragment :=
      sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment
    let root := orbitFaceRoot RS boundaryFragment.1.1
    let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let semantic :=
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
        realization hcubic hrotation htwoSided hunique offset hnext root
    let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val =
      min
        (code.oldComponentCapSumAt semantic output +
          min (faceRegionalFragmentPositionSlice RS root
              nextRegion newRegion boundaryFragment.2.1).card 5 -
          (faceRegionalFragmentPositionSlice RS root
                nextRegion oldRegion boundaryFragment.2.1 ∩
            faceRegionalFragmentPositionSlice RS root
                nextRegion newRegion boundaryFragment.2.1).card)
        5 := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization hcubic
      hrotation htwoSided hunique offset hnext fragment
  let root := orbitFaceRoot RS boundaryFragment.1.1
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
    (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext fragment)
  have hnextRegion : nextRegion = oldRegion ∪ newRegion := by
    exact sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
      realization hcubic hrotation htwoSided hunique offset hnext
  subst nextRegion
  have hold :=
    sourceCorridorSerialBoundaryRebaseOldComponentCapSumAt_eq_slice realization
      hcubic hrotation htwoSided hunique offset hnext fragment
  change code.oldComponentCapSumAt semantic output =
      min (faceRegionalFragmentPositionSlice RS root (oldRegion ∪ newRegion)
        oldRegion boundaryFragment.2.1).card 5 at hold
  have hsuccessor :=
    sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_slices
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        fragment
  change
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val =
      min
        (min (faceRegionalFragmentPositionSlice RS root
              (oldRegion ∪ newRegion) oldRegion boundaryFragment.2.1).card 5 +
          min (faceRegionalFragmentPositionSlice RS root
              (oldRegion ∪ newRegion) newRegion boundaryFragment.2.1).card 5 -
          (faceRegionalFragmentPositionSlice RS root
                (oldRegion ∪ newRegion) oldRegion boundaryFragment.2.1 ∩
            faceRegionalFragmentPositionSlice RS root
                (oldRegion ∪ newRegion) newRegion boundaryFragment.2.1).card)
        5 at hsuccessor
  rw [← hold] at hsuccessor
  exact hsuccessor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
