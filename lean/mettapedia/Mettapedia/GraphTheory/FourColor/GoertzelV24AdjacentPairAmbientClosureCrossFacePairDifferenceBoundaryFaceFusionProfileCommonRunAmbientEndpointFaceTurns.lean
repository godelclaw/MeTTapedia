import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunAmbientEndpointRotation

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The quotient face on a chosen side of an oriented dart. `true` is the
dart side and `false` is the opposite-dart side. -/
def dartSideOrbitFace (RS : RotationSystem V E) (dart : RS.D)
    (side : Bool) : OrbitFace RS :=
  if side then dartOrbitFace RS dart
  else dartOrbitFace RS (RS.alpha dart)

/-- The canonical side coordinate of an incident face relative to an
oriented dart. -/
noncomputable def incidentFaceSide (RS : RotationSystem V E) (dart : RS.D)
    (face : OrbitFace RS) : Bool :=
  decide (dartOrbitFace RS dart = face)

@[simp] theorem incidentFaceSide_eq_true_iff
    (RS : RotationSystem V E) (dart : RS.D) (face : OrbitFace RS) :
    RS.incidentFaceSide dart face = true ↔
      dartOrbitFace RS dart = face := by
  simp [incidentFaceSide]

@[simp] theorem incidentFaceSide_eq_false_iff
    (RS : RotationSystem V E) (dart : RS.D) (face : OrbitFace RS) :
    RS.incidentFaceSide dart face = false ↔
      dartOrbitFace RS dart ≠ face := by
  simp [incidentFaceSide]

/-- In a two-sided facial structure, the canonical side coordinate recovers
every face incident to the dart's underlying edge. -/
theorem dartSideOrbitFace_incidentFaceSide_eq
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) (face : OrbitFace RS)
    (hedge : RS.edgeOf dart ∈ orbitFaceBoundary RS face) :
    RS.dartSideOrbitFace dart (RS.incidentFaceSide dart face) = face := by
  by_cases hface : dartOrbitFace RS dart = face
  · simp [dartSideOrbitFace, incidentFaceSide, hface]
  · have hopposite := dartOrbitFace_alpha_eq_of_mem_other_face
      RS htwoSided dart face hedge hface
    simp [dartSideOrbitFace, incidentFaceSide, hface, hopposite]

/-- Two-sidedness makes the two Boolean dart-side coordinates distinct. -/
theorem dartSideOrbitFace_injective
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) :
    Function.Injective (RS.dartSideOrbitFace dart) := by
  intro left right heq
  cases left <;> cases right
  · rfl
  · exact False.elim (htwoSided dart heq.symm)
  · exact False.elim (htwoSided dart heq)
  · rfl

/-- Any side coordinate representing an incident face is the canonical
one computed by `incidentFaceSide`. -/
theorem incidentFaceSide_eq_of_dartSideOrbitFace_eq
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) (face : OrbitFace RS)
    (hedge : RS.edgeOf dart ∈ orbitFaceBoundary RS face)
    (side : Bool) (hside : RS.dartSideOrbitFace dart side = face) :
    side = RS.incidentFaceSide dart face := by
  apply RS.dartSideOrbitFace_injective htwoSided dart
  rw [hside, RS.dartSideOrbitFace_incidentFaceSide_eq htwoSided dart face hedge]

/-- Entering through the first displayed dart leaves the vertex through the
second or third displayed dart according to the certified orientation. -/
theorem ThreeDartRotation.phi_alpha_first
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    RS.phi (RS.alpha rotation.first) =
      if rotation.orientation then rotation.second else rotation.third := by
  rw [RotationSystem.phi_apply, RS.alpha_involutive, rotation.rho_first]

/-- Entering through the second displayed dart leaves through the next dart
in the certified cyclic orientation. -/
theorem ThreeDartRotation.phi_alpha_second
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    RS.phi (RS.alpha rotation.second) =
      if rotation.orientation then rotation.third else rotation.first := by
  rw [RotationSystem.phi_apply, RS.alpha_involutive, rotation.rho_second]

/-- Entering through the third displayed dart leaves through the next dart
in the certified cyclic orientation. -/
theorem ThreeDartRotation.phi_alpha_third
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    RS.phi (RS.alpha rotation.third) =
      if rotation.orientation then rotation.first else rotation.second := by
  rw [RotationSystem.phi_apply, RS.alpha_involutive, rotation.rho_third]

/-- The face entering through the first displayed arm continues along the
second or third displayed arm according to the orientation bit. -/
theorem ThreeDartRotation.dartOrbitFace_alpha_first
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    dartOrbitFace RS (RS.alpha rotation.first) =
      if rotation.orientation then
        dartOrbitFace RS rotation.second
      else dartOrbitFace RS rotation.third := by
  calc
    dartOrbitFace RS (RS.alpha rotation.first) =
        dartOrbitFace RS (RS.rho rotation.first) :=
      dartOrbitFace_alpha_eq_dartOrbitFace_rho RS rotation.first
    _ = _ := by rw [rotation.rho_first]; split <;> rfl

/-- The face entering through the second displayed arm continues along the
third or first displayed arm according to the orientation bit. -/
theorem ThreeDartRotation.dartOrbitFace_alpha_second
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    dartOrbitFace RS (RS.alpha rotation.second) =
      if rotation.orientation then
        dartOrbitFace RS rotation.third
      else dartOrbitFace RS rotation.first := by
  calc
    dartOrbitFace RS (RS.alpha rotation.second) =
        dartOrbitFace RS (RS.rho rotation.second) :=
      dartOrbitFace_alpha_eq_dartOrbitFace_rho RS rotation.second
    _ = _ := by rw [rotation.rho_second]; split <;> rfl

/-- The face entering through the third displayed arm continues along the
first or second displayed arm according to the orientation bit. -/
theorem ThreeDartRotation.dartOrbitFace_alpha_third
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    dartOrbitFace RS (RS.alpha rotation.third) =
      if rotation.orientation then
        dartOrbitFace RS rotation.first
      else dartOrbitFace RS rotation.second := by
  calc
    dartOrbitFace RS (RS.alpha rotation.third) =
        dartOrbitFace RS (RS.rho rotation.third) :=
      dartOrbitFace_alpha_eq_dartOrbitFace_rho RS rotation.third
    _ = _ := by rw [rotation.rho_third]; split <;> rfl

/-- The complete side-face formula for the first displayed dart. -/
theorem ThreeDartRotation.dartSideOrbitFace_first
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    RS.dartSideOrbitFace rotation.first side =
      if side then dartOrbitFace RS rotation.first
      else if rotation.orientation then
        dartOrbitFace RS rotation.second
      else dartOrbitFace RS rotation.third := by
  cases side
  · simpa [dartSideOrbitFace] using rotation.dartOrbitFace_alpha_first
  · rfl

/-- The complete side-face formula for the second displayed dart. -/
theorem ThreeDartRotation.dartSideOrbitFace_second
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    RS.dartSideOrbitFace rotation.second side =
      if side then dartOrbitFace RS rotation.second
      else if rotation.orientation then
        dartOrbitFace RS rotation.third
      else dartOrbitFace RS rotation.first := by
  cases side
  · simpa [dartSideOrbitFace] using rotation.dartOrbitFace_alpha_second
  · rfl

/-- The complete side-face formula for the third displayed dart. -/
theorem ThreeDartRotation.dartSideOrbitFace_third
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    RS.dartSideOrbitFace rotation.third side =
      if side then dartOrbitFace RS rotation.third
      else if rotation.orientation then
        dartOrbitFace RS rotation.first
      else dartOrbitFace RS rotation.second := by
  cases side
  · simpa [dartSideOrbitFace] using rotation.dartOrbitFace_alpha_third
  · rfl

/-- The dart occupying a displayed position in a certified three-dart
rotation. -/
def ThreeDartRotation.displayedDart
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3) : RS.D :=
  if position = 0 then rotation.first
  else if position = 1 then rotation.second
  else rotation.third

@[simp] theorem ThreeDartRotation.displayedDart_zero
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    rotation.displayedDart 0 = rotation.first := by
  simp [ThreeDartRotation.displayedDart]

@[simp] theorem ThreeDartRotation.displayedDart_one
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    rotation.displayedDart 1 = rotation.second := by
  simp [ThreeDartRotation.displayedDart]

@[simp] theorem ThreeDartRotation.displayedDart_two
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    rotation.displayedDart 2 = rotation.third := by
  simp [ThreeDartRotation.displayedDart]

/-- The quotient face on a chosen side of a displayed endpoint position. -/
def ThreeDartRotation.displayedSideOrbitFace
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3)
    (side : Bool) : OrbitFace RS :=
  RS.dartSideOrbitFace (rotation.displayedDart position) side

@[simp] theorem ThreeDartRotation.displayedSideOrbitFace_zero
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    rotation.displayedSideOrbitFace 0 side =
      if side then dartOrbitFace RS rotation.first
      else if rotation.orientation then
        dartOrbitFace RS rotation.second
      else dartOrbitFace RS rotation.third := by
  exact rotation.dartSideOrbitFace_first side

@[simp] theorem ThreeDartRotation.displayedSideOrbitFace_one
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    rotation.displayedSideOrbitFace 1 side =
      if side then dartOrbitFace RS rotation.second
      else if rotation.orientation then
        dartOrbitFace RS rotation.third
      else dartOrbitFace RS rotation.first := by
  exact rotation.dartSideOrbitFace_second side

@[simp] theorem ThreeDartRotation.displayedSideOrbitFace_two
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (side : Bool) :
    rotation.displayedSideOrbitFace 2 side =
      if side then dartOrbitFace RS rotation.third
      else if rotation.orientation then
        dartOrbitFace RS rotation.first
      else dartOrbitFace RS rotation.second := by
  exact rotation.dartSideOrbitFace_third side

end RotationSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The position occupied by the common trunk in the restored merge word. -/
def LocalizedCommonRunMergeArmState.ambientTrunkPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Fin 3
  | .internal _ _ => 2
  | .prefixPort _ _ _ => 1
  | .suffixPort _ _ _ => 1

/-- The common trunk is the first displayed direction at the split. -/
def LocalizedCommonRunSplitArmState.ambientTrunkPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Fin 3
  | .internal _ _ => 0
  | .prefixPort _ _ _ => 0
  | .suffixPort _ _ _ => 0

/-- The selected remote face's side coordinate on the first oriented trunk
dart. -/
def LocalizedAlignedCommonRunSplice.mergeTrunkFaceSide
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_splice : LocalizedAlignedCommonRunSplice profile) : Bool :=
  graphData.toRotationSystem.incidentFaceSide
    (pair.ambientPrefixSharedEdgeDart profile.firstRank) face

/-- The selected remote face's side coordinate on the reverse of the last
oriented trunk dart, which is outgoing from the split. -/
def LocalizedAlignedCommonRunSplice.splitTrunkFaceSide
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_splice : LocalizedAlignedCommonRunSplice profile) : Bool :=
  graphData.toRotationSystem.incidentFaceSide
    (pair.ambientPrefixSharedEdgeDart profile.lastRank).symm face

/-- The first trunk side coordinate reconstructs the selected remote face. -/
theorem LocalizedAlignedCommonRunSplice.mergeTrunkSideFace_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    graphData.toRotationSystem.dartSideOrbitFace
        (pair.ambientPrefixSharedEdgeDart profile.firstRank)
        splice.mergeTrunkFaceSide = face := by
  apply graphData.toRotationSystem.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided
  have hedge : graphData.toRotationSystem.edgeOf
        (pair.ambientPrefixSharedEdgeDart profile.firstRank) =
      retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.firstRank) := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge]
  exact splice.trunk.first_edge_mem_face

/-- The last reversed trunk side coordinate reconstructs the same selected
remote face. -/
theorem LocalizedAlignedCommonRunSplice.splitTrunkSideFace_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    graphData.toRotationSystem.dartSideOrbitFace
        (pair.ambientPrefixSharedEdgeDart profile.lastRank).symm
        splice.splitTrunkFaceSide = face := by
  apply graphData.toRotationSystem.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided
  have hedge : graphData.toRotationSystem.edgeOf
        (pair.ambientPrefixSharedEdgeDart profile.lastRank).symm =
      retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.lastRank) := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  rw [hedge]
  exact splice.trunk.last_edge_mem_face

/-- The displayed merge position in every endpoint rotation is exactly the
first ambient trunk dart. -/
theorem LocalizedCommonRunMergeArmState.ambientRotation_displayedDart_eq_trunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientTrunkPosition =
      pair.ambientPrefixSharedEdgeDart profile.firstRank := by
  cases state with
  | internal hprefix hsuffix =>
      change rotation.third =
        retainedDartToAmbientDart data
          (pair.prefixSharedEdgeDart profile.firstRank)
      have hword := rotation.word_eq
      simp [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.outgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] at hword
      exact (List.cons.inj (List.cons.inj
        (List.cons.inj hword).2).2).1.symm
  | prefixPort hnil heq hsuffix =>
      change rotation.second =
        retainedDartToAmbientDart data
          (pair.prefixSharedEdgeDart profile.firstRank)
      have hword := rotation.word_eq
      simp [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.outgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] at hword
      exact (List.cons.inj (List.cons.inj hword).2).1.symm
  | suffixPort hnil heq hprefix =>
      change rotation.second =
        retainedDartToAmbientDart data
          (pair.prefixSharedEdgeDart profile.firstRank)
      have hword := rotation.word_eq
      simp [LocalizedCommonRunMergeArmState.ambientOutgoingDarts,
        LocalizedCommonRunMergeArmState.outgoingDarts,
        LocalizedCommonRunMergeArmState.collapsedPort] at hword
      exact (List.cons.inj (List.cons.inj hword).2).1.symm

/-- The displayed split position in every endpoint rotation is exactly the
reverse of the last ambient trunk dart. -/
theorem LocalizedCommonRunSplitArmState.ambientRotation_displayedDart_eq_trunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) :
    rotation.displayedDart state.ambientTrunkPosition =
      (pair.ambientPrefixSharedEdgeDart profile.lastRank).symm := by
  cases state <;>
    change rotation.first =
      (retainedDartToAmbientDart data
        (pair.prefixSharedEdgeDart profile.lastRank)).symm <;>
    have hword := rotation.word_eq <;>
    simp [LocalizedCommonRunSplitArmState.ambientOutgoingDarts,
      LocalizedCommonRunSplitArmState.outgoingDarts,
      LocalizedCommonRunSplitArmState.collapsedPort] at hword <;>
    have hfirst := (List.cons.inj hword).1 <;>
    exact hfirst.symm

/-- In every merge state, the selected face is exactly the canonical side
face of the displayed trunk position. -/
theorem LocalizedCommonRunMergeArmState.ambientRotation_trunkSideFace_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    rotation.displayedSideOrbitFace state.ambientTrunkPosition
        splice.mergeTrunkFaceSide = face := by
  unfold RotationSystem.ThreeDartRotation.displayedSideOrbitFace
  rw [state.ambientRotation_displayedDart_eq_trunk rotation]
  exact splice.mergeTrunkSideFace_eq htwoSided

/-- In every split state, the selected face is exactly the canonical side
face of the displayed reversed-trunk position. -/
theorem LocalizedCommonRunSplitArmState.ambientRotation_trunkSideFace_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    rotation.displayedSideOrbitFace state.ambientTrunkPosition
        splice.splitTrunkFaceSide = face := by
  unfold RotationSystem.ThreeDartRotation.displayedSideOrbitFace
  rw [state.ambientRotation_displayedDart_eq_trunk rotation]
  exact splice.splitTrunkSideFace_eq htwoSided

/-- The merge and split rotation certificates expose the same remote face
at their respective canonical trunk-side coordinates. This is the exact
endpoint equation before any parity convention is imposed. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpoint_trunkFace_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (mergeState : LocalizedCommonRunMergeArmState splice)
    (splitState : LocalizedCommonRunSplitArmState splice)
    (mergeRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem mergeState.ambientOutgoingDarts)
    (splitRotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem splitState.ambientOutgoingDarts)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    mergeRotation.displayedSideOrbitFace
        mergeState.ambientTrunkPosition splice.mergeTrunkFaceSide =
      splitRotation.displayedSideOrbitFace
        splitState.ambientTrunkPosition splice.splitTrunkFaceSide := by
  calc
    mergeRotation.displayedSideOrbitFace
          mergeState.ambientTrunkPosition splice.mergeTrunkFaceSide = face :=
      mergeState.ambientRotation_trunkSideFace_eq mergeRotation htwoSided
    _ = splitRotation.displayedSideOrbitFace
          splitState.ambientTrunkPosition splice.splitTrunkFaceSide :=
      (splitState.ambientRotation_trunkSideFace_eq
        splitRotation htwoSided).symm

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
