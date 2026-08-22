import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceOldFactorAnchor

/-!
# Literal old face factors named by finite rebase coordinates

An active finite switch coordinate names a literal position in the old-prefix
regional face graph.  This file turns that position into its actual connected
factor fragment and proves that the stored old-component position set is exactly the
position set of that fragment.

This is the decoding direction needed for the finite face-cap recurrence.  It
does not yet identify which decoded fragments meet a chosen successor fragment,
nor does it sum their capped weights.
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
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceOldFactorFragmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal old-prefix regional position named by an active finite switch
coordinate. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldFactorPositionAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hpresent :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent
          coordinate = true) :
    FaceRegionalPosition embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let position := ((carrierCoordinate carrier).symm coordinate).1
  have hpresentPosition : faceCycleEdge RS root position ∈ region :=
    (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldPresent_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        coordinate).1 hpresent
  refine ⟨position, ?_⟩
  rw [mem_faceRegionalPositions_iff]
  exact hpresentPosition

@[simp]
theorem sourceCorridorSerialBoundaryRebaseOldFactorPositionAt_val
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hpresent :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent
          coordinate = true) :
    (sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization hcubic
      hrotation htwoSided hunique offset hnext root coordinate hpresent).1 =
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root)).symm
            coordinate).1 :=
  rfl

/-- The literal old-prefix connected face fragment named by one active finite
switch coordinate. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hpresent :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent
          coordinate = true) :
    FaceRegionalFragment embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges :=
  (faceRegionalPositionGraph embedded.cellulation.rotation.toRotationSystem
    root (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges).connectedComponentMk
        (sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate
            hpresent)

/-- The stored positions of a present old component are precisely the cyclic
position set of its decoded literal old-prefix factor fragment. -/
theorem sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_eq_positions
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hpresent :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent
          coordinate = true) :
    sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate =
      faceRegionalFragmentPositions
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges
        (sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate
            hpresent) := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let anchor := sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization
    hcubic hrotation htwoSided hunique offset hnext root coordinate hpresent
  let fragment := sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext root coordinate
      hpresent
  ext position
  rw [mem_sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_iff]
  rw [mem_faceRegionalFragmentPositions_iff]
  constructor
  · rintro ⟨hpositionRegion, hreachable⟩
    let regionalPosition : FaceRegionalPosition RS root region :=
      ⟨position, (mem_faceRegionalPositions_iff RS root region position).2
        hpositionRegion⟩
    have hregional :
        (faceRegionalPositionGraph RS root region).Reachable anchor
          regionalPosition := by
      apply (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        anchor regionalPosition).2
      simpa [anchor, regionalPosition] using hreachable
    refine ⟨regionalPosition, ?_, rfl⟩
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff fragment
      regionalPosition).2
    exact (SimpleGraph.ConnectedComponent.sound hregional).symm
  · rintro ⟨regionalPosition, hpositionFragment, hpositionValue⟩
    subst position
    have hregional :
        (faceRegionalPositionGraph RS root region).Reachable anchor
          regionalPosition := by
      apply SimpleGraph.ConnectedComponent.exact
      exact ((SimpleGraph.ConnectedComponent.mem_supp_iff fragment anchor).1
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff fragment
            regionalPosition).1 hpositionFragment).symm
    have hambient :
        (faceRegionalAmbientPositionGraph RS root region).Reachable anchor.1
          regionalPosition.1 :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root region anchor
        regionalPosition).1 hregional
    refine ⟨(mem_faceRegionalPositions_iff RS root region
      regionalPosition.1).1 regionalPosition.2, ?_⟩
    simpa [anchor, carrier] using hambient

/-- If a present old coordinate is connected to a chosen successor coordinate
by the exact finite rebase closure, its decoded old fragment is one of the
literal old-prefix factors of that successor face fragment. -/
theorem sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_mem_factors
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
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
              htwoSided hunique
                (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                  successorFragment))).localCode.vertexCount.val)
    (hpresent :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
              htwoSided hunique
                (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                  successorFragment))).oldPresent coordinate = true)
    (hclosure :
      Relation.ReflTransGen
        (boundedSerialBoundaryRebaseFaceComponentStep
          (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext
              (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
                ((sourceCorridorSerialInputCutDataAt realization hcubic
                  hrotation htwoSided hunique
                    (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                      successorFragment))).toBoundedSerialBoundaryRebaseFaceStepCode)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext
              (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
                ((sourceCorridorSerialInputCutDataAt realization hcubic
                  hrotation htwoSided hunique
                    (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                      successorFragment)))
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext successorFragment))
        coordinate) :
    sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
        hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
              htwoSided hunique
                (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                  successorFragment)) coordinate hpresent ∈
      faceRegionalFactorFragments
        embedded.cellulation.rotation.toRotationSystem
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
            htwoSided hunique
              (sourceCorridorSerialNextOffset offset hnext)).fragmentFace
                successorFragment))
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
          hunique (sourceCorridorSerialNextOffset offset hnext))
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges
        (sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
          hcubic hrotation htwoSided hunique offset hnext
            successorFragment).2.1 := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
      hcubic hrotation htwoSided hunique offset hnext successorFragment
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let output := sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt
    realization hcubic hrotation htwoSided hunique offset hnext
      successorFragment
  let anchorSubtype := (carrierCoordinate carrier).symm coordinate
  let anchor := sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization
    hcubic hrotation htwoSided hunique offset hnext root coordinate hpresent
  let oldFragment := sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext root coordinate
      hpresent
  apply (mem_faceRegionalFactorFragments_iff RS root nextRegion oldRegion
    boundaryFragment.2.1 oldFragment).2
  refine ⟨anchor.1, ?_, ?_⟩
  · apply (mem_faceRegionalFragmentPositions_iff RS root oldRegion oldFragment
      anchor.1).2
    exact ⟨anchor, SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
      rfl⟩
  · have hclosure' : Relation.ReflTransGen
        (boundedSerialBoundaryRebaseFaceComponentStep
          (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext root
              ).toBoundedSerialBoundaryRebaseFaceStepCode)
        (carrierCoordinate carrier output)
        (carrierCoordinate carrier anchorSubtype) := by
      simpa [root, carrier, output, anchorSubtype] using hclosure
    have hambient : (faceRegionalAmbientPositionGraph RS root nextRegion).Reachable
        output.1 anchor.1 := by
      have hreach :=
        (sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceStepCode
          realization hcubic hrotation htwoSided hunique offset hnext root
            output.1 anchorSubtype.1 output.2 anchorSubtype.2).2 hclosure'
      simpa [anchor, anchorSubtype] using hreach
    have houtputFragment : output.1 ∈
        faceRegionalFragmentPositions RS root nextRegion boundaryFragment.2.1 :=
      boundaryRegionalFragmentCutPosition_mem RS
        (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        nextRegion boundaryFragment
    rcases (mem_faceRegionalFragmentPositions_iff RS root nextRegion
      boundaryFragment.2.1 output.1).1 houtputFragment with
      ⟨outputRegional, houtputSupp, houtputValue⟩
    have hanchorRegion : faceCycleEdge RS root anchor.1 ∈ nextRegion := by
      have hnextRegion : nextRegion = oldRegion ∪
          sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext :=
        sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
          realization hcubic hrotation htwoSided hunique offset hnext
      rw [hnextRegion]
      exact Finset.mem_union_left _
        ((mem_faceRegionalPositions_iff RS root oldRegion anchor.1).1 anchor.2)
    let anchorRegional : FaceRegionalPosition RS root nextRegion :=
      ⟨anchor.1, (mem_faceRegionalPositions_iff RS root nextRegion anchor.1).2
        hanchorRegion⟩
    have hregional :
        (faceRegionalPositionGraph RS root nextRegion).Reachable outputRegional
          anchorRegional := by
      apply (faceRegionalPositionGraph_reachable_iff_ambient RS root nextRegion
        outputRegional anchorRegional).2
      simpa [houtputValue, anchorRegional] using hambient
    have hanchorSupp : anchorRegional ∈ boundaryFragment.2.1.supp := by
      apply (SimpleGraph.ConnectedComponent.mem_supp_iff boundaryFragment.2.1
        anchorRegional).2
      exact (SimpleGraph.ConnectedComponent.sound hregional).symm.trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff boundaryFragment.2.1
          outputRegional).1 houtputSupp)
    apply (mem_faceRegionalFragmentPositions_iff RS root nextRegion
      boundaryFragment.2.1 anchor.1).2
    exact ⟨anchorRegional, hanchorSupp, rfl⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
