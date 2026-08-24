import Mathlib.Order.Partition.Finpartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap

/-!
# Canonical predecessor components for one finite source-Cell face step

The facial predecessor state stores the same capped component weight at every
represented dart of one accumulated-prefix component.  Adding those values at
all occurrences would overcount.  This file selects one canonical live
coordinate per present predecessor component and then retains exactly the
components joined to a chosen output coordinate by the already proved finite
three-factor closure.

The construction is graph-free once a finite state and transition code are
given.  A semantic certificate records precisely the equivalence, activity,
and cap-coherence laws used by the selector; every literal source Cell
constructs that certificate.  The newly adjoined Cell edges are deliberately
not counted here.  They require the separate primal-edge equality table so
that repeated dart occurrences contribute only once.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- The predecessor-component relation reconstructed from the fixed attachment
state, restricted to the live coordinates of one transition code. -/
def SourceLocalLayerSerialFaceFinitePredecessorConnected
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Prop :=
  SupportedPortResidualFactoredReachability
    state.toBoundedSupportedPortResidualCode
    (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
    (sourceLocalLayerSerialFaceFiniteStableSlot code left)
    (sourceLocalLayerSerialFaceFiniteStableSlot code right)

/-- Exact laws needed to quotient the live finite coordinates by predecessor
components. -/
structure SourceLocalLayerSerialFaceFinitePredecessorSemantic
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool) : Prop where
  connected_refl : ∀ coordinate,
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code coordinate
      coordinate
  connected_symm : ∀ {left right},
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right →
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code right left
  connected_trans : ∀ {left middle right},
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code left middle →
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code middle right →
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right
  present_constant : ∀ {left right},
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right →
      state.interfacePresent
          (sourceLocalLayerSerialFaceFiniteStableSlot code left) =
        state.interfacePresent
          (sourceLocalLayerSerialFaceFiniteStableSlot code right)
  cap_constant : ∀ {left right},
    SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right →
      state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code left) =
        state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code right)

/-- The predecessor component relation as a setoid on live coordinates. -/
def sourceLocalLayerSerialFaceFinitePredecessorSetoid
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code) :
    Setoid (Fin code.vertexCount.val) where
  r := SourceLocalLayerSerialFaceFinitePredecessorConnected state code
  iseqv := {
    refl := semantic.connected_refl
    symm := semantic.connected_symm
    trans := semantic.connected_trans }

/-- The finite partition of live coordinates into predecessor components. -/
noncomputable def sourceLocalLayerSerialFaceFinitePredecessorPartition
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code) :
    Finpartition (Finset.univ : Finset (Fin code.vertexCount.val)) := by
  letI : DecidableRel
      (sourceLocalLayerSerialFaceFinitePredecessorSetoid state code semantic).r :=
    Classical.decRel _
  exact Finpartition.ofSetoid
    (sourceLocalLayerSerialFaceFinitePredecessorSetoid state code semantic)

@[simp]
theorem mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (left right : Fin code.vertexCount.val) :
    right ∈ (sourceLocalLayerSerialFaceFinitePredecessorPartition state code
        semantic).part left ↔
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
        right := by
  classical
  change right ∈
      (Finpartition.ofSetoid
        (sourceLocalLayerSerialFaceFinitePredecessorSetoid state code semantic)
      ).part left ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- The least live coordinate in one predecessor component. -/
noncomputable def sourceLocalLayerSerialFaceFinitePredecessorRepresentative
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (coordinate : Fin code.vertexCount.val) : Fin code.vertexCount.val :=
  ((sourceLocalLayerSerialFaceFinitePredecessorPartition state code semantic
      ).part coordinate).min'
    ⟨coordinate,
      (mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff state
        code semantic coordinate coordinate).2
        (semantic.connected_refl coordinate)⟩

theorem sourceLocalLayerSerialFaceFinitePredecessorRepresentative_mem_part
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (coordinate : Fin code.vertexCount.val) :
    sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
        semantic coordinate ∈
      (sourceLocalLayerSerialFaceFinitePredecessorPartition state code semantic
        ).part coordinate :=
  Finset.min'_mem _ _

/-- Equality of canonical representatives is exactly predecessor-component
connectivity. -/
theorem sourceLocalLayerSerialFaceFinitePredecessorRepresentative_eq_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (left right : Fin code.vertexCount.val) :
    sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code semantic
        right =
      sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code semantic
        left ↔
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
        right := by
  classical
  let partition := sourceLocalLayerSerialFaceFinitePredecessorPartition state
    code semantic
  have hmem : right ∈ partition.part left ↔
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
        right :=
    mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff state code
      semantic left right
  rw [← hmem]
  constructor
  · intro hrepresentative
    apply (partition.mem_part_iff_part_eq_part
      (Finset.mem_univ right) (Finset.mem_univ left)).2
    apply partition.eq_of_mem_parts
      (partition.part_mem.2 (Finset.mem_univ right))
      (partition.part_mem.2 (Finset.mem_univ left))
    · exact sourceLocalLayerSerialFaceFinitePredecessorRepresentative_mem_part
        state code semantic right
    · rw [hrepresentative]
      exact sourceLocalLayerSerialFaceFinitePredecessorRepresentative_mem_part
        state code semantic left
  · intro hmem
    have hparts : partition.part right = partition.part left :=
      (partition.mem_part_iff_part_eq_part
        (Finset.mem_univ right) (Finset.mem_univ left)).1 hmem
    simp only [sourceLocalLayerSerialFaceFinitePredecessorRepresentative,
      partition, hparts]

/-- One present canonical coordinate per physically present predecessor
component. -/
noncomputable def sourceLocalLayerSerialFaceFinitePredecessorRepresentatives
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code) :
    Finset (Fin code.vertexCount.val) :=
  Finset.univ.filter fun coordinate =>
    state.interfacePresent
        (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true ∧
      sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
        semantic coordinate = coordinate

@[simp]
theorem mem_sourceLocalLayerSerialFaceFinitePredecessorRepresentatives_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (coordinate : Fin code.vertexCount.val) :
    coordinate ∈ sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state
        code semantic ↔
      state.interfacePresent
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true ∧
        sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
          semantic coordinate = coordinate := by
  classical
  simp [sourceLocalLayerSerialFaceFinitePredecessorRepresentatives]

/-- Canonical predecessor components joined to one output coordinate by the
complete finite Cell closure. -/
noncomputable def sourceLocalLayerSerialFaceFiniteContributingPredecessors
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (output : Fin code.vertexCount.val) : Finset (Fin code.vertexCount.val) := by
  classical
  exact
    (sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state code
      semantic).filter fun representative =>
        Relation.ReflTransGen
          (SourceLocalLayerSerialFaceFiniteComponentStep state code) output
          representative

/-- The finite capped predecessor contribution.  Every old component is
counted once, at its canonical live coordinate. -/
noncomputable def sourceLocalLayerSerialFaceFinitePredecessorCapSum
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (semantic : SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (output : Fin code.vertexCount.val) : Nat :=
  min
    (∑ representative ∈
      sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
        semantic output,
      (state.componentCap
        (sourceLocalLayerSerialFaceFiniteStableSlot code representative)).val)
    5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFinitePredecessorRepresentativesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Full predecessor components based at connected darts have exactly the same
distinct primal-edge support. -/
theorem sourceLocalLayerBoundaryRebaseFaceComponentEdges_eq_of_reachable
    (RS : RotationSystem V G.edgeSet) (region : Finset G.edgeSet)
    {left right : RS.D}
    (hreachable : (faceRegionalDartGraph RS region).Reachable left right) :
    sourceLocalLayerBoundaryRebaseFaceComponentEdges RS region left =
      sourceLocalLayerBoundaryRebaseFaceComponentEdges RS region right := by
  classical
  ext edge
  rw [GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap.mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff,
    GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap.mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff]
  constructor
  · rintro ⟨dart, hedge, hdart⟩
    exact ⟨dart, hedge, hreachable.symm.trans hdart⟩
  · rintro ⟨dart, hedge, hdart⟩
    exact ⟨dart, hedge, hreachable.trans hdart⟩

/-- Every actual opened-source Cell supplies the equivalence, activity, and
cap-coherence laws required by the finite predecessor selector. -/
theorem sourceLocalLayerSerialFaceFinitePredecessorSemanticAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceFinitePredecessorSemantic
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
        hcell)
      (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
        hcell) := by
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hconnected (left right : Fin code.vertexCount.val) :
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
          right ↔
        graph.Reachable (coordinate.symm left).1 (coordinate.symm right).1 := by
    unfold SourceLocalLayerSerialFaceFinitePredecessorConnected
    rw [hslot left, hslot right]
    exact
      sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
        corridor hunique offset hcell (coordinate.symm left)
          (coordinate.symm right)
  have hpresent (coordinateIndex : Fin code.vertexCount.val) :
      state.interfacePresent
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
            true ↔
        web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈ region := by
    rw [hslot coordinateIndex]
    rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
    simp [region]
  have hcap (coordinateIndex : Fin code.vertexCount.val) :
      state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
        ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
            region (coordinate.symm coordinateIndex).1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
    rw [hslot coordinateIndex]
    exact sourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap
      corridor hunique offset hcell (coordinate.symm coordinateIndex)
  refine {
    connected_refl := ?_
    connected_symm := ?_
    connected_trans := ?_
    present_constant := ?_
    cap_constant := ?_ }
  · intro coordinateIndex
    exact (hconnected coordinateIndex coordinateIndex).2
      SimpleGraph.Reachable.rfl
  · intro left right hsame
    exact (hconnected right left).2 ((hconnected left right).1 hsame).symm
  · intro left middle right hleft hright
    exact (hconnected left right).2
      (((hconnected left middle).1 hleft).trans
        ((hconnected middle right).1 hright))
  · intro left right hsame
    apply Bool.eq_iff_iff.mpr
    rw [hpresent left, hpresent right]
    have hreachable := (hconnected left right).1 hsame
    by_cases heq : (coordinate.symm left).1 = (coordinate.symm right).1
    · rw [heq]
    · constructor
      · intro _
        have hsupport := SimpleGraph.mem_support_of_reachable (Ne.symm heq)
          hreachable.symm
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
      · intro _
        have hsupport := SimpleGraph.mem_support_of_reachable heq hreachable
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
  · intro left right hsame
    rw [hcap left, hcap right]
    congr 2
    exact congrArg Finset.card
      (sourceLocalLayerBoundaryRebaseFaceComponentEdges_eq_of_reachable
        web.annular.RS region ((hconnected left right).1 hsame))

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives

end Mettapedia.GraphTheory.FourColor
