import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives

/-!
# Canonical new-edge representatives for one finite source-Cell face step

The predecessor cap already counts every edge lying in the accumulated prefix.
The local Cell contribution must therefore retain only edges absent from that
prefix, connected to the selected output component, and count each underlying
primal edge once even when both of its dart occurrences lie in the common
twenty-four-slot carrier.

This file defines that finite selector.  Its only semantic law is that the
stored primal-edge equality table is an equivalence on contributing live
coordinates.  Every actual source Cell supplies the law definitionally from
equality of its represented primal edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

/-- A live slot contributes a genuinely new Cell edge to one selected output
component exactly when it is in the Cell, absent from the predecessor, and
joined to the output by the complete finite facial closure. -/
def SourceLocalLayerSerialFaceFiniteNewEdgeContributes
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate : Fin code.vertexCount.val) : Prop :=
  edgeState.cellPresent
      (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true ∧
    state.interfacePresent
      (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = false ∧
    Relation.ReflTransGen
      (SourceLocalLayerSerialFaceFiniteComponentStep state code) output
      coordinate

/-- Equality-table laws needed to choose one representative of each new
primal edge. -/
structure SourceLocalLayerSerialFaceFiniteNewEdgeSemantic
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val) : Prop where
  same_refl : ∀ coordinate,
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output coordinate →
      edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate)
        (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true
  same_symm : ∀ {left right},
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output left →
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output right →
    edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code left)
        (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true →
      edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code right)
        (sourceLocalLayerSerialFaceFiniteStableSlot code left) = true
  same_trans : ∀ {left middle right},
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output left →
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output middle →
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output right →
    edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code left)
        (sourceLocalLayerSerialFaceFiniteStableSlot code middle) = true →
    edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code middle)
        (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true →
      edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code left)
        (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true

/-- Contributing live coordinates denoting the same primal edge as a chosen
coordinate. -/
noncomputable def sourceLocalLayerSerialFaceFiniteNewEdgeClass
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate : Fin code.vertexCount.val) :
    Finset (Fin code.vertexCount.val) := by
  classical
  exact Finset.univ.filter fun candidate =>
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output candidate ∧
      edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code candidate)
        (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true

@[simp]
theorem mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate candidate : Fin code.vertexCount.val) :
    candidate ∈ sourceLocalLayerSerialFaceFiniteNewEdgeClass state code
        edgeState output coordinate ↔
      SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
          output candidate ∧
        edgeState.samePrimalEdge
          (sourceLocalLayerSerialFaceFiniteStableSlot code candidate)
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinate) = true := by
  classical
  simp [sourceLocalLayerSerialFaceFiniteNewEdgeClass]

/-- Least coordinate naming one contributing new primal edge. -/
noncomputable def sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output)
    (coordinate : Fin code.vertexCount.val)
    (hcoordinate : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code
      edgeState output coordinate) : Fin code.vertexCount.val :=
  (sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
    coordinate).min'
      ⟨coordinate,
        (mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code
          edgeState output coordinate coordinate).2
          ⟨hcoordinate, semantic.same_refl coordinate hcoordinate⟩⟩

theorem sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output)
    (coordinate : Fin code.vertexCount.val)
    (hcoordinate : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code
      edgeState output coordinate) :
    sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic coordinate hcoordinate ∈
      sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
        coordinate :=
  Finset.min'_mem _ _

/-- For contributing coordinates, equality of canonical representatives is
exactly equality of the represented primal edges. -/
theorem sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_eq_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output)
    (left right : Fin code.vertexCount.val)
    (hleft : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code
      edgeState output left)
    (hright : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code
      edgeState output right) :
    sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic right hright =
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic left hleft ↔
      edgeState.samePrimalEdge
        (sourceLocalLayerSerialFaceFiniteStableSlot code left)
        (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true := by
  classical
  have hclass (hsame : edgeState.samePrimalEdge
      (sourceLocalLayerSerialFaceFiniteStableSlot code left)
      (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true) :
      sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
          right =
        sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
          left := by
    ext candidate
    simp only [mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff]
    constructor
    · rintro ⟨hcandidate, hcandRight⟩
      refine ⟨hcandidate, ?_⟩
      exact semantic.same_trans hcandidate hright hleft hcandRight
        (semantic.same_symm hleft hright hsame)
    · rintro ⟨hcandidate, hcandLeft⟩
      exact ⟨hcandidate,
        semantic.same_trans hcandidate hleft hright hcandLeft hsame⟩
  constructor
  · intro hrepresentative
    let representative :=
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic left hleft
    have hleftMem :=
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class state code
        edgeState output semantic left hleft
    have hrightMem :=
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class state code
        edgeState output semantic right hright
    have hrepLeft :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code edgeState
        output left representative).1 hleftMem
    have hrepRight : representative ∈
        sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
          right := by
      simpa [representative, hrepresentative] using hrightMem
    have hrepRight' :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code edgeState
        output right representative).1 hrepRight
    exact semantic.same_trans hleft hrepLeft.1 hright
      (semantic.same_symm hrepLeft.1 hleft hrepLeft.2) hrepRight'.2
  · intro hsame
    change
      (sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
        right).min' _ =
      (sourceLocalLayerSerialFaceFiniteNewEdgeClass state code edgeState output
        left).min' _
    apply (Finset.min'_eq_iff _ _ _).2
    constructor
    · rw [hclass hsame]
      exact Finset.min'_mem _ _
    · intro candidate hcandidate
      apply Finset.min'_le
      rw [← hclass hsame]
      exact hcandidate

/-- All canonical representatives of genuinely new edges in one output
component. -/
noncomputable def sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output) : Finset (Fin code.vertexCount.val) := by
  classical
  exact Finset.univ.filter fun coordinate =>
    ∃ hcoordinate : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code
        edgeState output coordinate,
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic coordinate hcoordinate = coordinate

@[simp]
theorem mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (semantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code
      edgeState output)
    (coordinate : Fin code.vertexCount.val) :
    coordinate ∈ sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state
        code edgeState output semantic ↔
      ∃ hcoordinate : SourceLocalLayerSerialFaceFiniteNewEdgeContributes state
          code edgeState output coordinate,
        sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code
          edgeState output semantic coordinate hcoordinate = coordinate := by
  classical
  simp [sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentativesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The exact primal-edge equality table of an actual source Cell satisfies
the finite selector laws at every output coordinate. -/
theorem sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (output : Fin
      (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell
        ).vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteNewEdgeSemantic
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
        hcell)
      (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell)
      (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset hcell)
      output := by
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
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
  have hsame (left right : Fin code.vertexCount.val) :
      edgeState.samePrimalEdge
          (sourceLocalLayerSerialFaceFiniteStableSlot code left)
          (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true ↔
        web.annular.RS.edgeOf (coordinate.symm left).1 =
          web.annular.RS.edgeOf (coordinate.symm right).1 := by
    rw [hslot left, hslot right]
    exact sourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
      corridor hunique offset hcell (coordinate.symm left)
        (coordinate.symm right)
  refine {
    same_refl := ?_
    same_symm := ?_
    same_trans := ?_ }
  · intro coordinateIndex _hcontributes
    exact (hsame coordinateIndex coordinateIndex).2 rfl
  · intro left right _hleft _hright hsameEdge
    exact (hsame right left).2 ((hsame left right).1 hsameEdge).symm
  · intro left middle right _hleft _hmiddle _hright hleft hright
    exact (hsame left right).2
      (((hsame left middle).1 hleft).trans
        ((hsame middle right).1 hright))

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives

end Mettapedia.GraphTheory.FourColor
