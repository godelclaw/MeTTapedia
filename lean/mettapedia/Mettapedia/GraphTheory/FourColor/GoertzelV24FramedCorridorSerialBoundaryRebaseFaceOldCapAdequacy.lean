import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFactorRepresentativeEquiv

/-!
# Adequacy of the finite predecessor face-cap sum

The canonical finite representatives of a literal serial rebase are exactly
the old-prefix factor fragments of each successor face.  Consequently the
finite decoder's capped predecessor sum is exactly the cap at five of the
literal old-prefix position slice.

This closes the predecessor half of the face-length recurrence.  The complete
successor cap still combines this value with the newly displayed Cell slice
and subtracts their proved overlap.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceOldCapAdequacyEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A contributing representative stores exactly the cap of the literal old
factor fragment to which the finite equivalence sends it. -/
theorem sourceCorridorSerialBoundaryRebaseRepresentative_oldComponentCap
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext)
    (representative :
      SourceCorridorSerialBoundaryRebaseContributingOldRepresentativeAt
        realization hcubic hrotation htwoSided hunique offset hnext
          successorFragment) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
    let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges
    let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let factor :=
      sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor realization
        hcubic hrotation htwoSided hunique offset hnext successorFragment
          representative
    (code.oldComponentCap representative.1).val =
      min (faceRegionalFragmentPositions RS root oldRegion factor.1).card 5 := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
    (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment)
  let factor :=
    sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor realization
      hcubic hrotation htwoSided hunique offset hnext successorFragment
        representative
  have hpresent : code.oldPresent representative.1 = true :=
    (code.mem_oldComponentRepresentatives_iff semantic representative.1).1
      ((code.mem_contributingOldComponentRepresentatives_iff semantic output
        representative.1).1 representative.2).1 |>.1
  change (code.oldComponentCap representative.1).val =
    min (faceRegionalFragmentPositions RS root oldRegion factor.1).card 5
  rw [sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldComponentCap]
  rw [sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_eq_positions
    realization hcubic hrotation htwoSided hunique offset hnext root
      representative.1 hpresent]
  rfl

/-- The finite predecessor cap sum is exactly the cap at five of the literal
old-prefix slice of the chosen successor face fragment. -/
theorem sourceCorridorSerialBoundaryRebaseOldComponentCapSumAt_eq_slice
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
    let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges
    let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
      hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let semantic :=
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
        realization hcubic hrotation htwoSided hunique offset hnext root
    let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext successorFragment)
    let boundaryFragment :=
      sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext successorFragment
    code.oldComponentCapSumAt semantic output =
      min (faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
        boundaryFragment.2.1).card 5 := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
    (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment
  let representatives :=
    code.contributingOldComponentRepresentatives semantic output
  let factors := faceRegionalFactorFragments RS root nextRegion oldRegion
    boundaryFragment.2.1
  let factorEquiv := sourceCorridorSerialBoundaryRebaseOldFactorEquiv realization
    hcubic hrotation htwoSided hunique offset hnext successorFragment
  have hregion : oldRegion ⊆ nextRegion := by
    dsimp [oldRegion, nextRegion]
    rw [sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
      realization hcubic hrotation htwoSided hunique offset hnext]
    exact Finset.subset_union_left
  change code.oldComponentCapSumAt semantic output =
    min (faceRegionalFragmentPositionSlice RS root nextRegion oldRegion
      boundaryFragment.2.1).card 5
  unfold BoundedCappedSerialBoundaryRebaseFaceStepCode.oldComponentCapSumAt
  rw [min_card_faceRegionalFragmentPositionSlice_eq_min_sum_fragmentCaps RS
    root nextRegion oldRegion hregion boundaryFragment.2.1]
  congr 1
  rw [Finset.sum_subtype representatives (fun _ => Iff.rfl)
    (fun representative => (code.oldComponentCap representative).val)]
  rw [Finset.sum_subtype factors (fun _ => Iff.rfl)
    (fun factorFragment =>
      min (faceRegionalFragmentPositions RS root oldRegion factorFragment).card
        5)]
  rw [← Equiv.sum_comp factorEquiv]
  apply Fintype.sum_congr
  intro representative
  exact sourceCorridorSerialBoundaryRebaseRepresentative_oldComponentCap
    realization hcubic hrotation htwoSided hunique offset hnext
      successorFragment representative

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
