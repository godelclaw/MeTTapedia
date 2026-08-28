import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter

/-!
# A normalized finite receipt for the pointwise-selected boundary rebase

The physical rebase collar admits many carrier presentations.  The finite
transition observes only their resulting component relations.  This file
chooses a canonical quotient presentation: the complete successor component
relation occupies the first tracked channel and the second channel is empty.
The Boolean union-closure is proved equal to the actual selected successor
connectivity, so this normalization loses no observable information.

The facial carrier is normalized independently to four discrete coordinates,
one for each possible output row.  Its closure is literal row equality.  The
unused coordinates do not enter the decoded dependent profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24CorridorProfile
open GoertzelV24FiniteBoolRelationClosure
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedBoundaryRebaseFiniteReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open Instance.LocalLayerFormation

@[simp]
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleInRegion_eq_true_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
        formation corridor hinterior offset hnext color hrole).roleInRegion
          role = true ↔
      pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext role ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext) := by
  simp [
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt]

/-- Complete component graph of the selected successor tracked graph, moved
to the canonical four-role coordinate system. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (pair : TrackedColorPair) : SimpleGraph (Fin 4) where
  Adj left right :=
    left ≠ right ∧
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm left))
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm right))
  symm := ⟨by
    rintro left right ⟨hne, hreachable⟩
    exact ⟨hne.symm, hreachable.symm⟩⟩
  loopless := ⟨by
    intro role hrole
    exact hrole.1 rfl⟩

/-- Reachability in the normalized component graph is exactly reachability in
the actual selected successor graph between the corresponding named roles. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt_reachable_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (pair : TrackedColorPair) (left right : Fin 4) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt
        formation corridor hinterior offset hnext color pair).Reachable
          left right ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm left))
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm right)) := by
  let actual := regionalTrackedEdgeGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext))
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
    corridor hinterior offset hnext ∘
      sourceLocalLayerBoundaryRebaseRoleEquivFin.symm
  constructor
  · intro hreachable
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
    induction hreachable with
    | refl => exact ⟨.nil⟩
    | tail hprefix hstep ih =>
        exact ih.trans hstep.2
  · intro hreachable
    by_cases heq : left = right
    · subst right
      exact ⟨.nil⟩
    · exact (show
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt
          formation corridor hinterior offset hnext color pair).Adj left right
          from ⟨heq, hreachable⟩).reachable

/-- Proof-facing normalized two-channel graph family.  The complete component
relation is placed in the first channel and the second channel is empty. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedGraphCodeForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 28 4 (TrackedColorPair × Bool) where
  vertexCount := ⟨4, by omega⟩
  point := fun coordinate => coordinate
  graph family :=
    if family.2 then ⊥ else
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt
        formation corridor hinterior offset hnext color family.1

/-- Native Boolean reflection of the normalized tracked quotient. -/
noncomputable abbrev pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) :
    BoundedCarrierBoolGraphFamilyCode 28 4 (TrackedColorPair × Bool) :=
  ofGraphFamilyCode
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedGraphCodeForColorAt
      formation corridor hinterior offset hnext color)

@[simp]
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_point
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (coordinate : Fin 4) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
      formation corridor hinterior offset hnext color).point coordinate =
        coordinate := by
  rfl

/-- The occupied channel of the normalized code represents the actual
successor component relation exactly. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_reachable_false_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin 4) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
      formation corridor hinterior offset hnext color).reachable
        (pair, false) left right = true ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm left))
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm right)) := by
  rw [ofGraphFamilyCode_reachable_eq_true_iff]
  change
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt
      formation corridor hinterior offset hnext color pair).Reachable
        left right ↔ _
  exact
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorComponentGraphForColorAt_reachable_iff
      formation corridor hinterior offset hnext color pair left right

/-- The unused channel is the discrete graph, hence contributes only
reflexivity to the union-closure. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_reachable_true_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin 4) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
      formation corridor hinterior offset hnext color).reachable
        (pair, true) left right = true ↔ left = right := by
  rw [ofGraphFamilyCode_reachable_eq_true_iff]
  change (⊥ : SimpleGraph (Fin 4)).Reachable left right ↔ left = right
  simp

/-- One normalized tracked finite step is already the complete actual
successor component relation. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedFiniteStepForColorAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin 4) :
    SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
          formation corridor hinterior offset hnext color)
        pair left right = true ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm left))
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm right)) := by
  rw [SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool, Bool.or_eq_true,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_reachable_false_iff,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_reachable_true_iff]
  constructor
  · rintro (hreachable | heq)
    · exact hreachable
    · subst right
      exact ⟨.nil⟩
  · exact fun hreachable => Or.inl hreachable

/-- Saturating the normalized finite step changes nothing: it remains exactly
the actual successor tracked component relation. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedFiniteClosureForColorAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin 4) :
    SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
          formation corridor hinterior offset hnext color)
        pair left right = true ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm left))
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext
          (sourceLocalLayerBoundaryRebaseRoleEquivFin.symm right)) := by
  rw [SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · intro hclosure
    induction hclosure with
    | refl => exact ⟨.nil⟩
    | tail hprefix hstep ih =>
        exact ih.trans
          ((pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedFiniteStepForColorAt_iff
            formation corridor hinterior offset hnext color pair _ _).1 hstep)
  · intro hreachable
    exact Relation.ReflTransGen.single
      ((pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedFiniteStepForColorAt_iff
        formation corridor hinterior offset hnext color pair left right).2
          hreachable)

/-! ## Canonical facial quotient -/

/-- Canonical four-coordinate facial receipt.  Both factor channels are
discrete: the only facial identifications visible after closure are equality
of output rows. -/
noncomputable abbrev pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceCollarCode :
    BoundedCarrierBoolGraphFamilyCode 24 0 Bool where
  vertexCount := ⟨4, by omega⟩
  point := Fin.elim0
  adjacency := fun _ _ _ => false

/-- The canonical facial closure is exactly equality of its four stable row
coordinates. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceFiniteClosure_iff
    (left right : Fin 4) :
    SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
        pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceCollarCode
        left right = true ↔ left = right := by
  have hgraph (family : Bool) :
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceCollarCode.toGraph
          family = (⊥ : SimpleGraph (Fin 4)) := by
    ext first second
    simp [BoundedCarrierBoolGraphFamilyCode.toGraph]
  have hstep_iff (first second : Fin 4) :
      SourceLocalLayerBoundaryRebaseFaceFiniteStepBool
          pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceCollarCode
          first second = true ↔ first = second := by
    simp [SourceLocalLayerBoundaryRebaseFaceFiniteStepBool,
      BoundedCarrierBoolGraphFamilyCode.reachable, hgraph]
  rw [SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · intro hclosure
    induction hclosure with
    | refl => rfl
    | tail hprefix hstep ih =>
        exact ih.trans ((hstep_iff _ _).1 hstep)
  · rintro rfl
    exact .refl

/-! ## Dependent output rows -/

/-- Extend a dependent output row to the fixed four-slot receipt carrier.
Inactive slots receive an arbitrary default which the decoder never reads. -/
def sourceLocalLayerBoundaryRebaseExtendOutputRow
    {A : Type*} (count : Fin 5) (row : Fin count.val → A) (default : A)
    (slot : Fin 4) : A :=
  if hslot : slot.val < count.val then row ⟨slot.val, hslot⟩ else default

/-- Extend a dependent square output table to the fixed four-slot receipt
carrier. -/
def sourceLocalLayerBoundaryRebaseExtendOutputTable
    {A : Type*} (count : Fin 5)
    (table : Fin count.val → Fin count.val → A) (default : A)
    (left right : Fin 4) : A :=
  if hleft : left.val < count.val then
    if hright : right.val < count.val then
      table ⟨left.val, hleft⟩ ⟨right.val, hright⟩
    else default
  else default

@[simp]
theorem sourceLocalLayerBoundaryRebaseExtendOutputRow_castLE
    {A : Type*} (count : Fin 5) (row : Fin count.val → A) (default : A)
    (fragment : Fin count.val) :
    sourceLocalLayerBoundaryRebaseExtendOutputRow count row default
        (Fin.castLE (Nat.le_of_lt_succ count.isLt) fragment) =
      row fragment := by
  simp [sourceLocalLayerBoundaryRebaseExtendOutputRow]

@[simp]
theorem sourceLocalLayerBoundaryRebaseExtendOutputTable_castLE
    {A : Type*} (count : Fin 5)
    (table : Fin count.val → Fin count.val → A) (default : A)
    (left right : Fin count.val) :
    sourceLocalLayerBoundaryRebaseExtendOutputTable count table default
        (Fin.castLE (Nat.le_of_lt_succ count.isLt) left)
        (Fin.castLE (Nat.le_of_lt_succ count.isLt) right) =
      table left right := by
  simp [sourceLocalLayerBoundaryRebaseExtendOutputTable]

/-- Canonical facial receipt carrying exactly the dependent facial fields of
one selected output profile. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceReceipt
    (output : BoundedCorridorCutProfile 2 1 4) :
    SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt where
  collarCode :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceCollarCode
  fragmentOccupied := fun slot =>
    decide (slot.val < output.faceFragmentCount.val)
  fragmentCoordinate := fun slot =>
    if slot.val < output.faceFragmentCount.val then some slot else none
  faceContinues :=
    sourceLocalLayerBoundaryRebaseExtendOutputTable output.faceFragmentCount
      output.profile.faceContinues false
  fragmentContainsPort :=
    sourceLocalLayerBoundaryRebaseExtendOutputRow output.faceFragmentCount
      output.profile.fragmentContainsPort (fun _ => false)
  faceLengthCap :=
    sourceLocalLayerBoundaryRebaseExtendOutputRow output.faceFragmentCount
      output.profile.faceLengthCap ⟨0, by omega⟩

/-- Canonical native-Boolean output letter for the exact selected successor. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode :=
  let output := pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt
    formation corridor hinterior offset hnext color hrole
  { outputCount := output.faceFragmentCount
    tracked :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
        formation corridor hinterior offset hnext color hrole
    facial :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceReceipt output }

/-- The canonical native receipt decodes to the exact selected successor
profile, field for field. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt_outputProfile
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt
        formation corridor hinterior offset hnext color hrole).outputProfile =
      pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
        corridor hinterior offset hnext color hrole := by
  simp only [
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt,
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputProfile]
  rw [GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext crossing
    exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_edgeColor_output
        formation corridor hinterior offset hnext color hrole crossing
  · funext pair left right
    apply Bool.eq_iff_iff.mpr
    rw [trackedConnectedBool_eq_true_iff]
    exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_connected_output
        formation corridor hinterior offset hnext color hrole pair left right
  · funext left right
    exact sourceLocalLayerBoundaryRebaseExtendOutputTable_castLE _ _ _ left right
  · funext fragment port
    exact congrFun
      (sourceLocalLayerBoundaryRebaseExtendOutputRow_castLE
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
          corridor hinterior offset hnext color hrole).faceFragmentCount
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
          corridor hinterior offset hnext color hrole).profile.fragmentContainsPort
        (fun _ => false) fragment) port
  · funext fragment
    exact sourceLocalLayerBoundaryRebaseExtendOutputRow_castLE _ _ _ fragment

/-! ## Complete normalized support letter -/

/-- Complete finite rebase letter extracted from the selected successor.  The
input endpoint is a caller argument because compatibility with the preceding
literal Cell is imposed by the heterogeneous total transition, not by the
successor receipt itself. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (input : BoundedCorridorCutProfile 2 0 4)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter where
  input := input
  output := pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt
    formation corridor hinterior offset hnext color hrole
  trackedCode :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt
      formation corridor hinterior offset hnext color
  outputCode :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt
      formation corridor hinterior offset hnext color hrole

/-- Every pointwise-selected positive rebase has a supported canonical finite
letter.  No physical carrier presentation survives in the conclusion. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt_supports
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (input : BoundedCorridorCutProfile 2 0 4)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
          formation corridor hinterior offset hnext input color hrole) = true := by
  rw [SourceLocalLayerBoundaryRebaseFiniteSupportsBool, decide_eq_true_eq]
  dsimp only [
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt]
  refine ⟨
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt_outputProfile
      formation corridor hinterior offset hnext color hrole).symm, ?_, ?_, ?_⟩
  · intro pair left right
    dsimp only [
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt]
    apply Bool.eq_iff_iff.mpr
    simp only [trackedConnectedBool_eq_true_iff,
      SourceLocalLayerBoundaryRebaseTrackedClosureConnectedBool,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_connected_iff,
      regionalTrackedConnectivity_eq_true_iff,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedFiniteClosureForColorAt_iff]
    simp only [
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleInRegion_eq_true_iff,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleColor_toColor,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedTrackedCodeForColorAt_point,
      Equiv.symm_apply_apply]
    simp only [and_assoc]
  · intro fragment
    refine ⟨?_, ?_⟩
    · simp [
        pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt,
        pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceReceipt,
        SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
    · refine ⟨
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt
          formation corridor hinterior offset hnext color hrole).outputFaceSlot
            fragment, ?_⟩
      simp [
        pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt,
        pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceReceipt,
        SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
  · intro left right
    dsimp only [
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedOutputCodeForColorAt,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceReceipt]
    refine ⟨
      Fin.castLE (Nat.le_of_lt_succ
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
          corridor hinterior offset hnext color hrole).faceFragmentCount.isLt) left,
      Fin.castLE (Nat.le_of_lt_succ
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
          corridor hinterior offset hnext color hrole).faceFragmentCount.isLt) right,
      ?_, ?_, ?_⟩
    · simp [SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
    · simp [SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
    · rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedFaceFiniteClosure_iff]
      exact Fin.castLE_inj

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
