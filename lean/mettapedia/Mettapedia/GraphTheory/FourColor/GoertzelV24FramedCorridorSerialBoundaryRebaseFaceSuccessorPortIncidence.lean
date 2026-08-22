import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSuccessorState
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSupportedStep

/-!
# Finite successor port incidence for a serial boundary rebase

The successor face fragments and their canonical dart occurrences already
live on the stable switch carrier.  A fragment contains one of the two new
crossing ports exactly when its canonical occurrence is connected, in the
successor regional face graph, to an occurrence over that port edge.

This file expresses that test entirely through the finite face-step closure.
The existential port occurrence is retained because one primal edge can have
two facial occurrences; projecting the test to the underlying edge before
choosing the occurrence would lose precisely the bridge information carried
by the profile.

This closes the successor `fragmentContainsPort` coordinate for one literal
rebase.  It does not yet update capped face length, form the alternating
Cell/rebase recurrence, measure reachable closure, or derive a threshold.
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
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceSuccessorPortIncidenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The canonical cut position of a successor boundary fragment, regarded as
one coordinate of the finite facial switch on its ambient orbit face. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt
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
    {position // position ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
            |>.fragmentFace fragment))} := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let cut := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let region := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment := sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext fragment
  let position := boundaryRegionalFragmentCutPosition RS cut region boundaryFragment
  refine ⟨position, ?_⟩
  rw [mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff]
  change RS.edgeOf
      (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment).1 ∈
    sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext
  exact (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt realization
    hcubic hrotation htwoSided hunique offset hnext fragment).2

/-- The exact finite predicate saying that one successor face fragment
contains one of the two displayed successor ports. -/
def SourceCorridorSerialBoundaryRebaseSuccessorFaceContainsPortAt
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
      realization hcubic hrotation htwoSided hunique offset hnext)
    (port : Fin 2) : Prop :=
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  ∃ occurrence : {position // position ∈ carrier},
    faceCycleEdge RS root occurrence.1 = data.portEdge (.inl port) ∧
      Relation.ReflTransGen
        (boundedSerialBoundaryRebaseFaceComponentStep code)
        (carrierCoordinate carrier
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext fragment))
        (carrierCoordinate carrier occurrence)

/-- Successor `fragmentContainsPort` is computed exactly by the finite facial
switch closure, including the choice of facial occurrence over the port edge. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_faceStepCode
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
      realization hcubic hrotation htwoSided hunique offset hnext)
    (port : Fin 2) :
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.fragmentContainsPort fragment (.inl port) = true) ↔
      SourceCorridorSerialBoundaryRebaseSuccessorFaceContainsPortAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment port := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let cut := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let region := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment := sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext fragment
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let start := sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt
    realization hcubic hrotation htwoSided hunique offset hnext fragment
  change
    ((data.regionalProfile color hcolor).fragmentContainsPort fragment
      (.inl port) = true) ↔ _
  rw [data.regionalProfile_fragmentContainsPort_eq_true_iff]
  have hfragmentEdges : data.regionalFragmentEdges fragment =
      boundaryRegionalFragmentEdges RS cut region boundaryFragment := by
    rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS region
        (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext))]
    rfl
  rw [hfragmentEdges]
  change data.portEdge (.inl port) ∈
      boundaryRegionalFragmentEdges RS cut region boundaryFragment ↔ _
  constructor
  · intro hedge
    rcases (mem_faceRegionalFragmentEdges_iff RS root region
      boundaryFragment.2.1 (data.portEdge (.inl port))).1 hedge with
      ⟨position, hpositionFragment, hpositionEdge⟩
    have hpositionSwitch : position ∈ carrier := by
      rw [mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff]
      rw [hpositionEdge]
      exact sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext port
    refine ⟨⟨position, hpositionSwitch⟩, hpositionEdge, ?_⟩
    have hstartFragment : start.1 ∈
        faceRegionalFragmentPositions RS root region boundaryFragment.2.1 := by
      exact boundaryRegionalFragmentCutPosition_mem RS cut region boundaryFragment
    rcases (mem_faceRegionalFragmentPositions_iff RS root region
      boundaryFragment.2.1 start.1).1 hstartFragment with
      ⟨startRegional, hstartSupp, hstartValue⟩
    rcases (mem_faceRegionalFragmentPositions_iff RS root region
      boundaryFragment.2.1 position).1 hpositionFragment with
      ⟨positionRegional, hpositionSupp, hpositionValue⟩
    have hregional := faceRegionalFragment_reachable RS root region
      boundaryFragment.2.1 hstartSupp hpositionSupp
    have hambient :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        startRegional positionRegional).1 hregional
    apply (sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceStepCode
      realization hcubic hrotation htwoSided hunique offset hnext root start.1
        position start.2 hpositionSwitch).1
    simpa [hstartValue, hpositionValue] using hambient
  · rintro ⟨occurrence, hedge, hstep⟩
    have hambient :=
      (sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceStepCode
        realization hcubic hrotation htwoSided hunique offset hnext root
          start.1 occurrence.1 start.2 occurrence.2).2 hstep
    have hstartFragment : start.1 ∈
        faceRegionalFragmentPositions RS root region boundaryFragment.2.1 := by
      exact boundaryRegionalFragmentCutPosition_mem RS cut region boundaryFragment
    rcases (mem_faceRegionalFragmentPositions_iff RS root region
      boundaryFragment.2.1 start.1).1 hstartFragment with
      ⟨startRegional, hstartSupp, hstartValue⟩
    have hportRegion : data.portEdge (.inl port) ∈ region :=
      sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) (.inl port)
    let occurrenceRegional : FaceRegionalPosition RS root region :=
      ⟨occurrence.1, (mem_faceRegionalPositions_iff RS root region
        occurrence.1).2 (by
          rw [hedge]
          exact hportRegion)⟩
    have hregional :
        (faceRegionalPositionGraph RS root region).Reachable startRegional
          occurrenceRegional := by
      apply (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        startRegional occurrenceRegional).2
      simpa [hstartValue, occurrenceRegional] using hambient
    have hstartComponent :
        (faceRegionalPositionGraph RS root region).connectedComponentMk
            startRegional = boundaryFragment.2.1 :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff boundaryFragment.2.1
        startRegional).1 hstartSupp
    have hoccurrenceComponent :
        (faceRegionalPositionGraph RS root region).connectedComponentMk
            occurrenceRegional = boundaryFragment.2.1 :=
      (SimpleGraph.ConnectedComponent.sound hregional).symm.trans
        hstartComponent
    have hoccurrenceSupp : occurrenceRegional ∈ boundaryFragment.2.1.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff boundaryFragment.2.1
        occurrenceRegional).2 hoccurrenceComponent
    apply (mem_faceRegionalFragmentEdges_iff RS root region
      boundaryFragment.2.1 (data.portEdge (.inl port))).2
    refine ⟨occurrence.1, ?_, hedge⟩
    apply (mem_faceRegionalFragmentPositions_iff RS root region
      boundaryFragment.2.1 occurrence.1).2
    exact ⟨occurrenceRegional, hoccurrenceSupp, rfl⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
