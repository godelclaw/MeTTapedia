import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPreRebaseState

/-!
# The fixed facial rebase interface as an exact occurrence receipt

The forty-eight-slot facial Cell--rebase interface is an occurrence
presentation.  Some padded slots are inactive and different active slots may
name the same ambient dart.  This file records those facts explicitly and
constructs the partial map from the fixed presentation back to the rolling
predecessor carrier.

The resulting finite state contains only literal local data: occurrence
activity, ambient-dart equality, equality of underlying primal edges,
pre-rebase presence, direct pre-rebase facial adjacency, and equality with
each oriented predecessor face-incidence vertex.  It does not store cumulative
exterior connectivity.  An active occurrence which is not mapped to the
predecessor carrier is therefore exposed as a genuinely new collar occurrence,
rather than being confused with inactive padding; its oriented predecessor
entry address remains recoverable without conflating the two face sides.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPreRebaseState
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceSourceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Literal local information on the fixed forty-eight-slot facial occurrence
interface.  No cumulative exterior-component row is stored here. -/
structure SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState where
  occupied : SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool
  vertexEq : SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool
  samePrimalEdge : SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool
  preRebasePresent :
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool
  directAdj : SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool
  oldIncidenceVertexEq : Fin 48 →
    SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool

/-- The forty-eight canonical predecessor face-incidence coordinates are the
two oriented face neighbours of each of the twenty-four padded predecessor
slots. -/
def sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceEquiv :
    (Fin 24 × Bool) ≃ Fin 48 :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- Decode one canonical predecessor face-incidence coordinate. -/
def sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
    (index : Fin 48) : Fin 24 × Bool :=
  sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceEquiv.symm index

private def sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateEquiv :
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState ≃
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) ×
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
        SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) ×
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
        SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) ×
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) ×
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
        SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) ×
      (Fin 48 → SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) where
  toFun state :=
    ⟨state.occupied, state.vertexEq, state.samePrimalEdge,
      state.preRebasePresent, state.directAdj, state.oldIncidenceVertexEq⟩
  invFun state := ⟨state.1, state.2.1, state.2.2.1,
    state.2.2.2.1, state.2.2.2.2.1, state.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState :=
  Classical.decEq _

noncomputable instance :
    Fintype SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState := by
  letI : Fintype
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) :=
    Fintype.ofFinite _
  letI : Fintype
      (SourceLocalLayerSerialCellRebaseExpandedFaceInterface →
        SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) :=
    Fintype.ofFinite _
  letI : Fintype
      (Fin 48 → SourceLocalLayerSerialCellRebaseExpandedFaceInterface → Bool) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateEquiv.symm

/-- The exact local occurrence state extracted from one literal Cell rebase.
Inactive slots are unequal unless they are the same fixed slot.  This gives
each padding coordinate its own isolated identity and prevents padding aliases
from entering later closure computations. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState := by
  classical
  let decode := sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
    corridor hunique offset hnext hcell
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  exact {
    occupied := fun slot => (decode slot).isSome
    vertexEq := fun left right =>
      match decode left, decode right with
      | some leftDart, some rightDart => decide (leftDart = rightDart)
      | none, none => decide (left = right)
      | _, _ => false
    samePrimalEdge := fun left right =>
      match decode left, decode right with
      | some leftDart, some rightDart =>
          decide (web.annular.RS.edgeOf leftDart =
            web.annular.RS.edgeOf rightDart)
      | _, _ => false
    preRebasePresent := fun slot =>
      match decode slot with
      | some dart => decide (web.annular.RS.edgeOf dart ∈ region)
      | none => false
    directAdj := fun left right =>
      match decode left, decode right with
      | some leftDart, some rightDart => decide (graph.Adj leftDart rightDart)
      | _, _ => false
    oldIncidenceVertexEq := fun index occurrence =>
      let incidence :=
        sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt index
      match sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
          offset hcell incidence.1, decode occurrence with
      | some oldDart, some dart =>
          decide
            (faceInterfaceIncidenceVertex web.annular.RS oldDartAt
                (carrierCoordinate oldCarrier oldDart, incidence.2) = dart)
      | _, _ => false }

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).occupied slot = true ↔
      ∃ dart, sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
        hunique offset hnext hcell slot = some dart := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt
  dsimp only
  cases hdecode :
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell slot <;> simp_all

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_vertexEq_iff_of_decode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (leftDart rightDart : web.annular.RS.D)
    (hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell left = some leftDart)
    (hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell right = some rightDart) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).vertexEq left right = true ↔
      leftDart = rightDart := by
  classical
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    hleft, hright]

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_samePrimalEdge_iff_of_decode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (leftDart rightDart : web.annular.RS.D)
    (hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell left = some leftDart)
    (hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell right = some rightDart) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).samePrimalEdge left right = true ↔
      web.annular.RS.edgeOf leftDart = web.annular.RS.edgeOf rightDart := by
  classical
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    hleft, hright]

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_preRebasePresent_iff_of_decode
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
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).preRebasePresent slot = true ↔
      web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset := by
  classical
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    hdecode]

@[simp]
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_iff_of_decode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (leftDart rightDart : web.annular.RS.D)
    (hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell left = some leftDart)
    (hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell right = some rightDart) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).directAdj left right = true ↔
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Adj leftDart rightDart := by
  classical
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    hleft, hright]

/-- The oriented predecessor-incidence row has its literal ambient meaning.
Unlike undirected direct adjacency, this row distinguishes the two face sides
of an old dart; those sides may enter different exterior components. -/
@[simp]
theorem
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (index : Fin 48)
    (oldDart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset})
    (holdDecode :
      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
          hcell
          (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt index).1 =
        some oldDart)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell occurrence = some dart) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).oldIncidenceVertexEq index occurrence =
          true ↔
      let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique offset
      let oldDartAt := fun slot : Fin oldCarrier.card =>
        ((carrierCoordinate oldCarrier).symm slot).1
      faceInterfaceIncidenceVertex web.annular.RS oldDartAt
          (carrierCoordinate oldCarrier oldDart,
            (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
              index).2) = dart := by
  classical
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    holdDecode, hdecode]

/-- Partial map from the fixed occurrence interface to the actual predecessor
carrier.  An active occurrence maps precisely when its ambient dart is already
one of the predecessor's rolling coordinates. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt
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
      Option (Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card) := by
  classical
  intro occurrence
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  match sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell occurrence with
  | none => exact none
  | some dart =>
      if hold : dart ∈ oldCarrier then
        exact some (carrierCoordinate oldCarrier ⟨dart, hold⟩)
      else exact none

/-- A mapped occurrence denotes exactly the ambient dart of the old rolling
coordinate to which it maps. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt_dart_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (slot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card)
    (hsource : sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt corridor
      hunique offset hnext hcell occurrence = some slot) :
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell occurrence =
      some (((carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
          ).symm slot).1) := by
  classical
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  cases hdecode :
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell occurrence with
  | none =>
      simp [sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt, hdecode]
        at hsource
  | some dart =>
      by_cases hold : dart ∈ oldCarrier
      · have hsource' :
            some (carrierCoordinate oldCarrier ⟨dart, hold⟩) = some slot := by
          simpa [sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt,
            hdecode, hold, oldCarrier] using hsource
        have heq : carrierCoordinate oldCarrier ⟨dart, hold⟩ = slot :=
          Option.some.inj hsource'
        subst slot
        simp [oldCarrier]
      · simp [sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt, hdecode,
          hold, oldCarrier] at hsource

/-- Failure to map has exactly two causes: inactive padding, or an active
collar occurrence outside the old rolling carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt_eq_none_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt corridor hunique
        offset hnext hcell occurrence = none ↔
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell occurrence = none ∨
        ∃ dart,
          sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
              hunique offset hnext hcell occurrence = some dart ∧
            dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor
              hunique offset := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt
  split <;> rename_i hdecode
  · simp [hdecode]
  · rename_i dart
    split <;> rename_i hold
    · simp [hdecode, hold]
    · simp [hdecode, hold]

/-- On active predecessor slots, the new occurrence equality row is exactly
the equality row already carried by the cap-seven pre-rebase state. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_old_vertexEq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).vertexEq
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell left))
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell right)) =
      ((sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt corridor
        hunique offset hcell).code ()).connectivity.vertexEq
        (carrierCoordinate _ left) (carrierCoordinate _ right) := by
  rw [sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt_code_eq]
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    exactFaceInterfaceExteriorLabelCapCode, exactInterfaceExteriorLabelCapCode,
    exactInterfaceExteriorCode]

/-- Literal pre-rebase presence agrees on the old twenty-four-slot summand. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_old_present
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
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).preRebasePresent
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell dart)) =
      ((sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt corridor
        hunique offset hcell).code ()).interfacePresent
        (carrierCoordinate _ dart) := by
  rw [sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt_code_eq]
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    exactFaceInterfaceExteriorLabelCapCode, exactInterfaceExteriorLabelCapCode]

/-- Direct pre-rebase facial adjacency also agrees on the old summand.  Thus
the new receipt extends the cap-seven state rather than replacing it with an
independent semantic extraction. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_old_directAdj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).directAdj
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell left))
        (.inl (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
          offset hcell right)) =
      ((sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt corridor
        hunique offset hcell).code ()).connectivity.directAdj
        (carrierCoordinate _ left) (carrierCoordinate _ right) := by
  rw [sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt_code_eq]
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
    exactFaceInterfaceExteriorLabelCapCode, exactInterfaceExteriorLabelCapCode,
    exactInterfaceExteriorCode]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
