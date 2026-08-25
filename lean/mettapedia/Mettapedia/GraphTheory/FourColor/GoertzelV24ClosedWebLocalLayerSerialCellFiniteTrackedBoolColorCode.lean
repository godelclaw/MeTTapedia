import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode

/-!
# Native Boolean reconstruction of the tracked Cell factors

The proof-facing factorization reconstructs the Cell tracked graph and the
residual prefix--Cell seam from uncoloured local geometry and two partial
colour tables.  This file performs the same reconstruction directly in the
native Boolean graph-family representation used by the finite transfer
engine.

The local letter is therefore independent of the cumulative prefix: its
geometry and Cell colours are fixed locally, while the transition combines
them with the prefix colour table supplied by the incoming state.  The crown
theorem proves that native reconstruction from a reflected source geometry is
exactly the proof-facing reconstruction, for every tracked colour pair and for
both the Cell and seam factors.

This is executable representation infrastructure for the source's Phase-5
factorization.  It does not enumerate reachable states, assert positivity of a
literal `Count`, or revive the refuted good-word closed-web obstruction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

/-- Embed one live coordinate of a native geometry code into the stable
twenty-one-slot Cell-transition ABI. -/
def SourceLocalLayerSerialTrackedBoolGeometryStableSlot
    (geometry : BoundedCarrierBoolGraphFamilyCode 21 5 Unit)
    (coordinate : Fin geometry.vertexCount.val) : Fin 21 :=
  Fin.castLE (Nat.le_of_lt_succ geometry.vertexCount.isLt) coordinate

/-- Executable test that a partial colour-table slot is active and carries one
of the two selected tracked colours. -/
def SourceLocalLayerSerialCarrierHasTrackedColorBool
    (code : SourceLocalLayerSerialCarrierColorCode)
    (pair : TrackedColorPair) (slot : Fin 21) : Bool :=
  match code slot with
  | none => false
  | some color =>
      decide (IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 color)

@[simp]
theorem sourceLocalLayerSerialCarrierHasTrackedColorBool_eq_true_iff
    (code : SourceLocalLayerSerialCarrierColorCode)
    (pair : TrackedColorPair) (slot : Fin 21) :
    SourceLocalLayerSerialCarrierHasTrackedColorBool code pair slot = true ↔
      SourceLocalLayerSerialCarrierHasTrackedColor code pair slot := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColorBool
    SourceLocalLayerSerialCarrierHasTrackedColor
  cases hcode : code slot with
  | none => simp
  | some color => simp

/-- Executable test that a partial colour-table slot is active. -/
def SourceLocalLayerSerialCarrierColorActiveBool
    (code : SourceLocalLayerSerialCarrierColorCode) (slot : Fin 21) : Bool :=
  (code slot).isSome

@[simp]
theorem sourceLocalLayerSerialCarrierColorActiveBool_eq_true_iff
    (code : SourceLocalLayerSerialCarrierColorCode) (slot : Fin 21) :
    SourceLocalLayerSerialCarrierColorActiveBool code slot = true ↔
      ∃ color, code slot = some color := by
  cases hcode : code slot with
  | none => simp [SourceLocalLayerSerialCarrierColorActiveBool, hcode]
  | some color => simp [SourceLocalLayerSerialCarrierColorActiveBool, hcode]

@[simp]
theorem sourceLocalLayerSerialCarrierColorActiveBool_eq_false_iff
    (code : SourceLocalLayerSerialCarrierColorCode) (slot : Fin 21) :
    SourceLocalLayerSerialCarrierColorActiveBool code slot = false ↔
      code slot = none := by
  cases hcode : code slot with
  | none => simp [SourceLocalLayerSerialCarrierColorActiveBool, hcode]
  | some color => simp [SourceLocalLayerSerialCarrierColorActiveBool, hcode]

/-- Native compatibility test for the prefix and Cell partial colour tables.
Inactive padding slots impose no condition; two active entries must agree. -/
def SourceLocalLayerSerialCarrierColorsCompatibleBool
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) : Bool :=
  (List.ofFn fun slot : Fin 21 =>
    match oldCode slot, cellCode slot with
    | some prefixColor, some cellColor => decide (prefixColor = cellColor)
    | _, _ => true).all id

@[simp]
theorem sourceLocalLayerSerialCarrierColorsCompatibleBool_eq_true_iff
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    SourceLocalLayerSerialCarrierColorsCompatibleBool oldCode cellCode = true ↔
      SourceLocalLayerSerialCarrierColorsCompatible oldCode cellCode := by
  rw [SourceLocalLayerSerialCarrierColorsCompatibleBool, List.all_eq_true,
    List.forall_mem_ofFn_iff]
  simp only [id_eq]
  unfold SourceLocalLayerSerialCarrierColorsCompatible
  constructor
  · intro hfinite slot prefixColor cellColor hold hcell
    simpa [hold, hcell] using hfinite slot
  · intro hactual slot
    cases hold : oldCode slot with
    | none => simp
    | some prefixColor =>
        cases hcell : cellCode slot with
        | none => simp
        | some cellColor =>
            simpa [hold, hcell] using
              hactual slot prefixColor cellColor hold hcell

/-- A seam edge has one endpoint belonging only to the prefix and the other
belonging only to the new Cell. -/
def SourceLocalLayerSerialFiniteTrackedSeamCrossesBool
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (first second : Fin 21) : Bool :=
  (SourceLocalLayerSerialCarrierColorActiveBool oldCode first &&
      !SourceLocalLayerSerialCarrierColorActiveBool cellCode first &&
      SourceLocalLayerSerialCarrierColorActiveBool cellCode second &&
      !SourceLocalLayerSerialCarrierColorActiveBool oldCode second) ||
    (SourceLocalLayerSerialCarrierColorActiveBool cellCode first &&
      !SourceLocalLayerSerialCarrierColorActiveBool oldCode first &&
      SourceLocalLayerSerialCarrierColorActiveBool oldCode second &&
      !SourceLocalLayerSerialCarrierColorActiveBool cellCode second)

@[simp]
theorem sourceLocalLayerSerialFiniteTrackedSeamCrossesBool_eq_true_iff
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (first second : Fin 21) :
    SourceLocalLayerSerialFiniteTrackedSeamCrossesBool oldCode cellCode
        first second = true ↔
      (((∃ color, oldCode first = some color) ∧ cellCode first = none ∧
          (∃ color, cellCode second = some color) ∧ oldCode second = none) ∨
        ((∃ color, cellCode first = some color) ∧ oldCode first = none ∧
          (∃ color, oldCode second = some color) ∧ cellCode second = none)) := by
  simp [SourceLocalLayerSerialFiniteTrackedSeamCrossesBool,
    Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (⟨⟨⟨hOldFirst, hCellFirst⟩, hCellSecond⟩, hOldSecond⟩ |
      ⟨⟨⟨hCellFirst, hOldFirst⟩, hOldSecond⟩, hCellSecond⟩)
    · exact Or.inl ⟨hOldFirst, hCellFirst, hCellSecond, hOldSecond⟩
    · exact Or.inr ⟨hCellFirst, hOldFirst, hOldSecond, hCellSecond⟩
  · rintro (⟨hOldFirst, hCellFirst, hCellSecond, hOldSecond⟩ |
      ⟨hCellFirst, hOldFirst, hOldSecond, hCellSecond⟩)
    · exact Or.inl ⟨⟨⟨hOldFirst, hCellFirst⟩, hCellSecond⟩, hOldSecond⟩
    · exact Or.inr ⟨⟨⟨hCellFirst, hOldFirst⟩, hOldSecond⟩, hCellSecond⟩

/-- Native Boolean reconstruction of the two tracked local factors.  `false`
selects the Cell graph and `true` selects the residual prefix--Cell seam. -/
def sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    (geometry : BoundedCarrierBoolGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    BoundedCarrierBoolGraphFamilyCode 21 5 (TrackedColorPair × Bool) where
  vertexCount := geometry.vertexCount
  point := geometry.point
  adjacency factor first second :=
    let firstSlot :=
      SourceLocalLayerSerialTrackedBoolGeometryStableSlot geometry first
    let secondSlot :=
      SourceLocalLayerSerialTrackedBoolGeometryStableSlot geometry second
    let geometric := decide ((geometry.toGraph ()).Adj first second)
    if factor.2 then
      geometric &&
        SourceLocalLayerSerialCarrierHasTrackedColorBool
          (SourceLocalLayerSerialFiniteSplicedColor oldCode cellCode)
          factor.1 firstSlot &&
        SourceLocalLayerSerialCarrierHasTrackedColorBool
          (SourceLocalLayerSerialFiniteSplicedColor oldCode cellCode)
          factor.1 secondSlot &&
        SourceLocalLayerSerialFiniteTrackedSeamCrossesBool oldCode cellCode
          firstSlot secondSlot
    else
      geometric &&
        SourceLocalLayerSerialCarrierHasTrackedColorBool cellCode factor.1
          firstSlot &&
        SourceLocalLayerSerialCarrierHasTrackedColorBool cellCode factor.1
          secondSlot

/-- The native adjacency table reflects the proof-facing reconstruction
exactly when its uncoloured geometry is itself reflected from the same
proof-facing geometry code. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_adjacency_eq_true_iff
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (factor : TrackedColorPair × Bool)
    (first second : Fin geometry.vertexCount.val) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode geometry) oldCode cellCode).adjacency factor
          first second = true ↔
      ((sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode
        cellCode).graph factor).Adj first second := by
  rcases factor with ⟨pair, seam⟩
  cases seam <;>
    simp [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry,
      sourceLocalLayerSerialTrackedCodeOfFiniteColors,
      SourceLocalLayerSerialFiniteCellTrackedGraph,
      SourceLocalLayerSerialFiniteTrackedSeamGraph,
      SourceLocalLayerSerialTrackedBoolGeometryStableSlot,
      SourceLocalLayerSerialTrackedGeometryStableSlot,
      ofGraphFamilyCode_toGraph, Bool.and_eq_true]
  · constructor
    · rintro ⟨⟨hgeometric, hfirst⟩, hsecond⟩
      exact ⟨hgeometric, hfirst, hsecond⟩
    · rintro ⟨hgeometric, hfirst, hsecond⟩
      exact ⟨⟨hgeometric, hfirst⟩, hsecond⟩
  · constructor
    · rintro ⟨⟨⟨hgeometric, hfirst⟩, hsecond⟩, hseam⟩
      exact ⟨hgeometric, hfirst, hsecond, hseam⟩
    · rintro ⟨hgeometric, hfirst, hsecond, hseam⟩
      exact ⟨⟨⟨hgeometric, hfirst⟩, hsecond⟩, hseam⟩

/-- Rebuilding simple graphs from the native Boolean reconstruction changes
neither the Cell factor nor the seam factor. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_toGraph
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (factor : TrackedColorPair × Bool) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode geometry) oldCode cellCode).toGraph factor =
      (sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode
        cellCode).graph factor := by
  apply SimpleGraph.ext
  funext first second
  apply propext
  change first ≠ second ∧
      ((sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
          (ofGraphFamilyCode geometry) oldCode cellCode).adjacency factor
            first second = true ∨
        (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
          (ofGraphFamilyCode geometry) oldCode cellCode).adjacency factor
            second first = true) ↔ _
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_adjacency_eq_true_iff,
    sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_adjacency_eq_true_iff]
  constructor
  · rintro ⟨_, hadj | hadj⟩
    · exact hadj
    · exact hadj.symm
  · intro hadj
    exact ⟨((sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode
      cellCode).graph factor).ne_of_adj hadj, Or.inl hadj⟩

/-- Hence native reconstruction preserves the exact local component relation
used by the finite transfer step. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_reachable_eq_true_iff
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (factor : TrackedColorPair × Bool)
    (left right : Fin geometry.vertexCount.val) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode geometry) oldCode cellCode).reachable factor
          left right = true ↔
      ((sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode
        cellCode).graph factor).Reachable left right := by
  rw [BoundedCarrierBoolGraphFamilyCode.reachable_eq_true_iff,
    sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_toGraph]
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- At literal source data, native reconstruction is exactly the formerly
stored prefix-specialized tracked factor. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryAt_toGraph_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (factor : TrackedColorPair × Bool) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode
          (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
            coloring web corridor hunique offset))
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).toGraph factor =
        (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)).graph factor := by
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_toGraph,
    sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq]

/-- The executable native query therefore computes the literal source
component relation exactly, in both the Cell and seam factors. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryAt_reachable_eq_true_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (factor : TrackedColorPair × Bool)
    (left right : Fin
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset).vertexCount.val) :
    (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode
          (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
            coloring web corridor hunique offset))
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).reachable factor left right = true ↔
        ((sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)).graph factor).Reachable left right := by
  rw [BoundedCarrierBoolGraphFamilyCode.reachable_eq_true_iff,
    sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryAt_toGraph_eq]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode

end Mettapedia.GraphTheory.FourColor
