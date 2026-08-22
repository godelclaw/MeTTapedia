import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFinitePredecessorCap

/-!
# Finite local face caps for a serial boundary rebase

The predecessor contribution to a successor face is already decoded by the
finite capped rebase state.  The other two terms in the exact successor law
are local to the newly displayed two-edge rebase: its capped contribution and
its literal overlap with the old prefix.  This file stores those terms in a
small graph-free table and proves that the table, together with the decoded
predecessor sum, computes every successor face cap exactly.

The table is extracted from each literal rebase.  This is not yet the complete
heterogeneous Cell/rebase letter: the next packaging theorem must combine it
with the finite continuation, port-incidence, and tracked-connectivity fields.
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

/-- The two finite local terms in the capped face recurrence, indexed by the
actual successor fragment coordinates. -/
structure BoundedSerialBoundaryRebaseFaceLocalCapCode (outputCount : Nat) where
  localCap : Fin outputCount → Fin 6
  overlapCap : Fin outputCount → Fin 6

private def boundedSerialBoundaryRebaseFaceLocalCapCodeEquiv
    (outputCount : Nat) :
    BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount ≃
      (Fin outputCount → Fin 6) × (Fin outputCount → Fin 6) where
  toFun code := ⟨code.localCap, code.overlapCap⟩
  invFun code := { localCap := code.1, overlapCap := code.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (outputCount : Nat) :
    DecidableEq (BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount) :=
  Classical.decEq _

noncomputable instance (outputCount : Nat) :
    Fintype (BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount) :=
  Fintype.ofEquiv _
    (boundedSerialBoundaryRebaseFaceLocalCapCodeEquiv outputCount).symm

/-- Decode the capped successor length from the finite predecessor component
sum and the two local cap coordinates. -/
def BoundedSerialBoundaryRebaseFaceLocalCapCode.outputCap
    {outputCount : Nat}
    (receipt : BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount)
    (oldCap : Fin outputCount → Nat) (output : Fin outputCount) : Nat :=
  min (oldCap output + (receipt.localCap output).val -
    (receipt.overlapCap output).val) 5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFiniteLocalCapsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Exact number of occurrence-sensitive successor face fragments in one
literal boundary rebase. -/
abbrev SourceCorridorSerialBoundaryRebaseSuccessorFaceCountAt
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
    (hnext : offset.val + 1 < blockLength - 3) :=
  Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext)))

/-- The literal finite local-cap table of one serial boundary rebase.  Both
entries are capped at five so the stored carrier is independent of the ambient
graph and face length. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedSerialBoundaryRebaseFaceLocalCapCode
      (SourceCorridorSerialBoundaryRebaseSuccessorFaceCountAt realization
        hcubic hrotation htwoSided hunique offset hnext) := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  exact
    { localCap := fun output =>
        let boundaryFragment :=
          sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
            hcubic hrotation htwoSided hunique offset hnext output
        let root := orbitFaceRoot RS boundaryFragment.1.1
        ⟨min (faceRegionalFragmentPositionSlice RS root nextRegion newRegion
            boundaryFragment.2.1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      overlapCap := fun output =>
        let boundaryFragment :=
          sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
            hcubic hrotation htwoSided hunique offset hnext output
        let root := orbitFaceRoot RS boundaryFragment.1.1
        ⟨min ((faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
              boundaryFragment.2.1) ∩
            faceRegionalFragmentPositionSlice RS root nextRegion newRegion
              boundaryFragment.2.1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- The local table stores exactly the capped newly displayed slice. -/
theorem sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt_localCap
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
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
      hcubic hrotation htwoSided hunique offset hnext
    let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
      hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let boundaryFragment :=
      sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment
    let root := orbitFaceRoot RS boundaryFragment.1.1
    ((sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).localCap fragment).val =
      min (faceRegionalFragmentPositionSlice RS root nextRegion newRegion
        boundaryFragment.2.1).card 5 := by
  rfl

/-- The local table stores exactly the capped literal old/new overlap. -/
theorem sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt_overlapCap
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
    ((sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).overlapCap fragment).val =
      min ((faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
            boundaryFragment.2.1) ∩
          faceRegionalFragmentPositionSlice RS root nextRegion newRegion
            boundaryFragment.2.1).card 5 := by
  rfl

/-- The complete successor cap is decoded by the finite predecessor sum and
the finite local table. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_finiteCode
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
    let boundaryFragment :=
      sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment
    let root := orbitFaceRoot RS boundaryFragment.1.1
    let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let predecessor := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let semantic :=
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
        realization hcubic hrotation htwoSided hunique offset hnext root
    let output : Fin predecessor.localCode.vertexCount.val :=
      carrierCoordinate carrier
        (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
          hcubic hrotation htwoSided hunique offset hnext fragment)
    let receipt := sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val =
      receipt.outputCap
        (fun _ => predecessor.oldComponentCapSumAt semantic output) fragment := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization hcubic
      hrotation htwoSided hunique offset hnext fragment
  let root := orbitFaceRoot RS boundaryFragment.1.1
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let predecessor := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin predecessor.localCode.vertexCount.val :=
    carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
  let receipt := sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext
  have hcap :=
    sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_finiteOldSum
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        fragment
  change
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val =
      min
        (predecessor.oldComponentCapSumAt semantic output +
          min (faceRegionalFragmentPositionSlice RS root nextRegion newRegion
              boundaryFragment.2.1).card 5 -
          (faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
                boundaryFragment.2.1 ∩
            faceRegionalFragmentPositionSlice RS root nextRegion newRegion
                boundaryFragment.2.1).card)
        5 at hcap
  change _ = min
    (predecessor.oldComponentCapSumAt semantic output +
      (receipt.localCap fragment).val - (receipt.overlapCap fragment).val) 5
  rw [sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt_localCap
    realization hcubic hrotation htwoSided hunique offset hnext fragment]
  rw [sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt_overlapCap
    realization hcubic hrotation htwoSided hunique offset hnext fragment]
  have hoverlapLe :
      (faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
            boundaryFragment.2.1 ∩
        faceRegionalFragmentPositionSlice RS root nextRegion newRegion
            boundaryFragment.2.1).card ≤ 5 := by
    have hcard := card_faceRegionalFragmentPositionSlice_inter_le_region_inter
      RS htwoSided root oldRegion newRegion boundaryFragment.2.1
    have hnew : newRegion.card ≤ 2 := by
      exact sourceCorridorSerialBoundaryRebaseEdgeSetAt_card_le_two realization
        hcubic hrotation htwoSided hunique offset hnext
    exact hcard.trans
      ((Finset.card_le_card Finset.inter_subset_right).trans (hnew.trans (by omega)))
  rw [Nat.min_eq_left hoverlapLe]
  exact hcap

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
