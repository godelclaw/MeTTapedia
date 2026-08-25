import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFacePrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformInterface

/-!
# A fixed occurrence interface for one facial Cell rebase

The literal pre-rebase facial carrier has at most twenty-four darts.  The
following boundary switch has at most eight dart occurrences, and its facial
collar consists exactly of each occurrence together with its forward and
backward face neighbours.  Thus the sum

`Fin 24 + (Fin 8 × FaceCollarDirection)`

is a fixed forty-eight-slot presentation of every dart touched by one Cell
and its following rebase.  Slots may be inactive and distinct slots may name
the same ambient dart; both facts are exposed by the partial decoder.

The main coverage theorem proves that every dart in the literal uniform
interaction carrier is decoded by some fixed slot.  This is the structural
termination certificate for the facial receipt: later factorization may work
on this fixed occurrence type and need not enlarge it when another semantic
role is discovered.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceInterfaceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The three literal darts contributed by one changed occurrence to the
one-step face collar. -/
inductive SourceLocalLayerSerialCellRebaseFaceCollarDirection
  | center
  | forward
  | backward
  deriving DecidableEq, Fintype

/-- Stable occurrence coordinates for a facial Cell update and its following
boundary rebase. -/
abbrev SourceLocalLayerSerialCellRebaseExpandedFaceInterface :=
  Fin 24 ⊕
    (Fin 8 × SourceLocalLayerSerialCellRebaseFaceCollarDirection)

@[simp]
theorem card_sourceLocalLayerSerialCellRebaseExpandedFaceInterface :
    Fintype.card SourceLocalLayerSerialCellRebaseExpandedFaceInterface = 48 := by
  have hdirection :
      Fintype.card SourceLocalLayerSerialCellRebaseFaceCollarDirection = 3 := by
    decide
  simp [SourceLocalLayerSerialCellRebaseExpandedFaceInterface, hdirection]

/-- Interpret one of the three collar directions at an ambient dart. -/
def sourceLocalLayerSerialCellRebaseFaceCollarDartAt
    (RS : RotationSystem V G.edgeSet) (dart : RS.D) :
    SourceLocalLayerSerialCellRebaseFaceCollarDirection → RS.D
  | .center => dart
  | .forward => RS.phi dart
  | .backward => RS.phi.symm dart

/-- Decode the fixed forty-eight-slot occurrence interface.  The left summand
is the padded predecessor carrier.  The right summand is the padded switch
occurrence together with one of its three literal collar positions. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
      Option web.annular.RS.D
  | .inl slot =>
      (sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
        hcell slot).map Subtype.val
  | .inr (occurrenceSlot, direction) =>
      (sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot? corridor hunique
        offset hnext occurrenceSlot).map fun occurrence =>
          sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?_old
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell dart)) =
      some dart.1 := by
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?]

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
      hunique offset hnext)
    (direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection) :
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell
        (.inr (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor
          hunique offset hnext occurrence, direction)) =
      some (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
        occurrence.1 direction) := by
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?]

/-- Every one of the three darts named from an actual switch occurrence lies
in the literal facial collar. -/
theorem sourceLocalLayerSerialCellRebaseFaceCollarDartAt_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
      hunique offset hnext)
    (direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection) :
    sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
        occurrence.1 direction ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
  have hchanged : occurrence.1 ∈
      sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
        hnext := by
    simpa using occurrence.2
  cases direction with
  | center =>
      exact sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
        corridor hunique offset hnext hchanged
  | forward =>
      exact sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_mem corridor hunique
        offset hnext hchanged
  | backward =>
      exact sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_symm_mem corridor
        hunique offset hnext hchanged

/-- Any occupied expanded slot names a dart of the literal uniform interaction
carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?_mem_uniform
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell slot = some dart) :
    dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext := by
  rcases slot with oldSlot | ⟨occurrenceSlot, direction⟩
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hdecoded : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
        hunique offset hcell oldSlot with
    | none => simp [hdecoded] at hdecode
    | some oldDart =>
        simp only [hdecoded, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        exact Finset.mem_union_left _ oldDart.2
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hdecoded : sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
        corridor hunique offset hnext occurrenceSlot with
    | none => simp [hdecoded] at hdecode
    | some occurrence =>
        simp only [hdecoded, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        exact Finset.mem_union_right _
          (sourceLocalLayerSerialCellRebaseFaceCollarDartAt_mem corridor hunique
            offset hnext occurrence direction)

/-- Every literal collar dart has a fixed occurrence coordinate. -/
theorem exists_expandedFaceSlot_of_mem_faceCollar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    {dart : web.annular.RS.D}
    (hdart : dart ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext) :
    ∃ slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface,
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell slot = some dart := by
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion] at hdart
  rcases hdart with ⟨changed, hchanged, hdart⟩
  let occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
      hunique offset hnext :=
    ⟨changed, by simpa using hchanged⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
  rcases hdart with rfl | rfl | rfl
  · exact ⟨.inr (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor
      hunique offset hnext occurrence, .center), by
        simp [occurrence,
          sourceLocalLayerSerialCellRebaseFaceCollarDartAt]⟩
  · exact ⟨.inr (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor
      hunique offset hnext occurrence, .forward), by
        simp [occurrence,
          sourceLocalLayerSerialCellRebaseFaceCollarDartAt]⟩
  · exact ⟨.inr (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor
      hunique offset hnext occurrence, .backward), by
        simp [occurrence,
          sourceLocalLayerSerialCellRebaseFaceCollarDartAt]⟩

/-- The fixed forty-eight-slot occurrence interface covers the complete
literal facial interaction carrier. -/
theorem exists_expandedFaceSlot_of_mem_uniformFaceCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    {dart : web.annular.RS.D}
    (hdart : dart ∈
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext) :
    ∃ slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface,
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell slot = some dart := by
  rcases Finset.mem_union.mp hdart with hold | hcollar
  · let oldDart : {dart // dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} :=
      ⟨dart, hold⟩
    exact ⟨.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
      offset hcell oldDart), by simp [oldDart]⟩
  · exact exists_expandedFaceSlot_of_mem_faceCollar corridor hunique offset
      hnext hcell hcollar

/-- Choose a fixed occurrence source for every actual coordinate of the
uniform facial carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext).card →
      SourceLocalLayerSerialCellRebaseExpandedFaceInterface :=
  fun target => Classical.choose
    (exists_expandedFaceSlot_of_mem_uniformFaceCarrier corridor hunique offset
      hnext hcell ((carrierCoordinate _).symm target).2)

/-- The chosen fixed occurrence decodes to the literal ambient dart of its
uniform-carrier coordinate. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt_dart_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (target : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card) :
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell
        (sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt corridor hunique
          offset hnext hcell target) =
      some (((carrierCoordinate
        (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
          hunique offset hnext)).symm target).1) := by
  exact Classical.choose_spec
    (exists_expandedFaceSlot_of_mem_uniformFaceCarrier corridor hunique offset
      hnext hcell ((carrierCoordinate _).symm target).2)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
