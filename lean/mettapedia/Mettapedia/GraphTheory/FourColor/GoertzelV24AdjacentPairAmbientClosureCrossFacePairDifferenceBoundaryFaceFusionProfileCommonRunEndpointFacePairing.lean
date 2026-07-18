import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunTrunkFaceTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OrbitFaceTwoSided

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Advance one place around a displayed three-arm word. `true` follows
the displayed order and `false` follows it in reverse. -/
def orientedStepPosition (orientation : Bool) (position : Fin 3) : Fin 3 :=
  if orientation then
    if position = 0 then 1 else if position = 1 then 2 else 0
  else
    if position = 0 then 2 else if position = 1 then 0 else 1

/-- The displayed position reached by the actual vertex rotation. -/
def ThreeDartRotation.rhoPosition
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3) : Fin 3 :=
  orientedStepPosition rotation.orientation position

/-- The other arm bounding the face on a chosen side of a displayed arm.
For the opposite-dart side it is the rotational successor; for the dart
side it is the rotational predecessor. -/
def ThreeDartRotation.faceMatePosition
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3)
    (side : Bool) : Fin 3 :=
  orientedStepPosition
    (if side then !rotation.orientation else rotation.orientation) position

/-- The finite position map `rhoPosition` exactly tracks `rho` on the
three displayed darts. -/
theorem ThreeDartRotation.displayedDart_rhoPosition
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3) :
    rotation.displayedDart (rotation.rhoPosition position) =
      RS.rho (rotation.displayedDart position) := by
  cases horientation : rotation.orientation <;> fin_cases position <;>
    simp [ThreeDartRotation.rhoPosition, orientedStepPosition,
      ThreeDartRotation.displayedDart, horientation,
      rotation.rho_first, rotation.rho_second, rotation.rho_third]

/-- A rotational step in a three-arm word always reaches a different
position. -/
theorem orientedStepPosition_ne (orientation : Bool) (position : Fin 3) :
    orientedStepPosition orientation position ≠ position := by
  cases orientation <;> fin_cases position <;>
    simp [orientedStepPosition]

/-- The other arm bounding a face is genuinely different from the arm at
which that face side was selected. -/
theorem ThreeDartRotation.faceMatePosition_ne
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3)
    (side : Bool) :
    rotation.faceMatePosition position side ≠ position := by
  exact orientedStepPosition_ne _ _

/-- Every face incident to a displayed arm is paired canonically with the
opposite side of an adjacent displayed arm. -/
theorem ThreeDartRotation.displayedSideOrbitFace_faceMatePosition
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3)
    (side : Bool) :
    rotation.displayedSideOrbitFace position side =
      rotation.displayedSideOrbitFace
        (rotation.faceMatePosition position side) (!side) := by
  cases horientation : rotation.orientation <;> cases side <;>
    fin_cases position <;>
    simp [ThreeDartRotation.faceMatePosition, orientedStepPosition,
      horientation]

/-- Taking the canonical face mate twice returns to the original displayed
position. -/
theorem ThreeDartRotation.faceMatePosition_involutive
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (position : Fin 3)
    (side : Bool) :
    rotation.faceMatePosition
        (rotation.faceMatePosition position side) (!side) = position := by
  cases horientation : rotation.orientation <;> cases side <;>
    fin_cases position <;>
    simp [ThreeDartRotation.faceMatePosition, orientedStepPosition,
      horientation]

/-- The six displayed arm-side states are paired by a fixed-point-free
involution following the local face sectors. -/
def ThreeDartRotation.faceSideMate
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    Equiv.Perm (Fin 3 × Bool) where
  toFun state :=
    (rotation.faceMatePosition state.1 state.2, !state.2)
  invFun state :=
    (rotation.faceMatePosition state.1 state.2, !state.2)
  left_inv state := by
    rcases state with ⟨position, side⟩
    apply Prod.ext
    · exact rotation.faceMatePosition_involutive position side
    · cases side <;> rfl
  right_inv state := by
    rcases state with ⟨position, side⟩
    apply Prod.ext
    · exact rotation.faceMatePosition_involutive position side
    · cases side <;> rfl

/-- The face-sector involution preserves the represented quotient face. -/
theorem ThreeDartRotation.displayedSideOrbitFace_faceSideMate
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) (state : Fin 3 × Bool) :
    rotation.displayedSideOrbitFace
        (rotation.faceSideMate state).1
        (rotation.faceSideMate state).2 =
      rotation.displayedSideOrbitFace state.1 state.2 := by
  exact (rotation.displayedSideOrbitFace_faceMatePosition
    state.1 state.2).symm

/-- Route label selected by a three-arm face sector. With the standard
displayed route order, the suffix route is selected exactly when rotation
orientation and trunk-side coordinate agree; a reversed route order flips
that answer. -/
def threeArmFaceRoute (routeOrderFlipped orientation side : Bool) : Bool :=
  if routeOrderFlipped then !(decide (orientation = side))
  else decide (orientation = side)

/-- Endpoint frame parity: equality of the two rotation orientations,
toggled once for each displayed route-order reversal. -/
def threeArmEndpointFrameParity
    (mergeRouteOrderFlipped splitRouteOrderFlipped
      mergeOrientation splitOrientation : Bool) : Bool :=
  Bool.xor (decide (mergeOrientation = splitOrientation))
    (Bool.xor mergeRouteOrderFlipped splitRouteOrderFlipped)

/-- Complementary trunk-side coordinates cancel from endpoint route
transport. The remaining route flip depends only on the two local frames. -/
theorem threeArmFaceRoute_xor_complement
    (mergeRouteOrderFlipped splitRouteOrderFlipped
      mergeOrientation splitOrientation side : Bool) :
    Bool.xor
        (threeArmFaceRoute mergeRouteOrderFlipped mergeOrientation side)
        (threeArmFaceRoute splitRouteOrderFlipped splitOrientation (!side)) =
      threeArmEndpointFrameParity mergeRouteOrderFlipped
        splitRouteOrderFlipped mergeOrientation splitOrientation := by
  cases mergeRouteOrderFlipped <;> cases splitRouteOrderFlipped <;>
    cases mergeOrientation <;> cases splitOrientation <;> cases side <;> rfl

end RotationSystem

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The external displayed arm sharing the selected remote face with the
merge trunk. -/
def LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) : Fin 3 :=
  rotation.faceMatePosition state.ambientTrunkPosition
    splice.mergeTrunkFaceSide

/-- The external displayed arm sharing the selected remote face with the
split trunk. -/
def LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) : Fin 3 :=
  rotation.faceMatePosition state.ambientTrunkPosition
    splice.splitTrunkFaceSide

/-- The prefix-route direction in the displayed merge word, restoring its
boundary direction when the retained prefix arm is collapsed. -/
def LocalizedCommonRunMergeArmState.ambientPrefixPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Fin 3
  | .internal _ _ => 0
  | .prefixPort _ _ _ => 2
  | .suffixPort _ _ _ => 0

/-- The suffix-route direction in the displayed merge word, restoring its
boundary direction when the retained suffix arm is collapsed. -/
def LocalizedCommonRunMergeArmState.ambientSuffixPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Fin 3
  | .internal _ _ => 1
  | .prefixPort _ _ _ => 0
  | .suffixPort _ _ _ => 2

/-- The prefix-route direction in the displayed split word, restoring its
boundary direction when the retained prefix arm is collapsed. -/
def LocalizedCommonRunSplitArmState.ambientPrefixPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Fin 3
  | .internal _ _ => 1
  | .prefixPort _ _ _ => 2
  | .suffixPort _ _ _ => 1

/-- The suffix-route direction in the displayed split word, restoring its
boundary direction when the retained suffix arm is collapsed. -/
def LocalizedCommonRunSplitArmState.ambientSuffixPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Fin 3
  | .internal _ _ => 2
  | .prefixPort _ _ _ => 1
  | .suffixPort _ _ _ => 2

/-- Select the prefix (`false`) or suffix (`true`) route position at the
merge. -/
def LocalizedCommonRunMergeArmState.ambientRoutePosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice) (route : Bool) : Fin 3 :=
  if route then state.ambientSuffixPosition else state.ambientPrefixPosition

/-- Select the prefix (`false`) or suffix (`true`) route position at the
split. -/
def LocalizedCommonRunSplitArmState.ambientRoutePosition
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice) (route : Bool) : Fin 3 :=
  if route then state.ambientSuffixPosition else state.ambientPrefixPosition

/-- Whether the displayed merge ordering reverses the standard
prefix--suffix route order around its trunk position. -/
def LocalizedCommonRunMergeArmState.ambientRouteOrderFlipped
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunMergeArmState splice → Bool
  | .internal _ _ => false
  | .prefixPort _ _ _ => false
  | .suffixPort _ _ _ => true

/-- Whether the displayed split ordering reverses the standard
prefix--suffix route order around its trunk position. -/
def LocalizedCommonRunSplitArmState.ambientRouteOrderFlipped
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile} :
    LocalizedCommonRunSplitArmState splice → Bool
  | .internal _ _ => false
  | .prefixPort _ _ _ => true
  | .suffixPort _ _ _ => false

/-- The merge route selected by the remote face: `false` is prefix and
`true` is suffix. -/
noncomputable def LocalizedCommonRunMergeArmState.ambientTrunkFaceRoute
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunMergeArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) : Bool :=
  decide (state.ambientTrunkFaceMatePosition rotation =
    state.ambientSuffixPosition)

/-- The split route selected by the remote face: `false` is prefix and
`true` is suffix. -/
noncomputable def LocalizedCommonRunSplitArmState.ambientTrunkFaceRoute
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    {splice : LocalizedAlignedCommonRunSplice profile}
    (state : LocalizedCommonRunSplitArmState splice)
    (rotation : RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) : Bool :=
  decide (state.ambientTrunkFaceMatePosition rotation =
    state.ambientSuffixPosition)

/-- At the merge, the selected face leaves the trunk through a genuinely
external displayed arm. -/
theorem LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition_ne
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
    state.ambientTrunkFaceMatePosition rotation ≠
      state.ambientTrunkPosition :=
  rotation.faceMatePosition_ne _ _

/-- At the split, the selected face leaves the reversed trunk through a
genuinely external displayed arm. -/
theorem LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition_ne
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
    state.ambientTrunkFaceMatePosition rotation ≠
      state.ambientTrunkPosition :=
  rotation.faceMatePosition_ne _ _

/-- The canonical merge face mate is exactly the prefix or suffix position
named by `ambientTrunkFaceRoute`. -/
theorem LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition_eq_route
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
    state.ambientTrunkFaceMatePosition rotation =
      state.ambientRoutePosition
        (state.ambientTrunkFaceRoute rotation) := by
  cases state <;>
    cases horientation : rotation.orientation <;>
    cases hside : splice.mergeTrunkFaceSide <;>
    simp [LocalizedCommonRunMergeArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition,
      LocalizedCommonRunMergeArmState.ambientRoutePosition,
      LocalizedCommonRunMergeArmState.ambientPrefixPosition,
      LocalizedCommonRunMergeArmState.ambientSuffixPosition,
      LocalizedCommonRunMergeArmState.ambientTrunkPosition,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition, horientation, hside]

/-- The canonical split face mate is exactly the prefix or suffix position
named by `ambientTrunkFaceRoute`. -/
theorem LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition_eq_route
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
    state.ambientTrunkFaceMatePosition rotation =
      state.ambientRoutePosition
        (state.ambientTrunkFaceRoute rotation) := by
  cases state <;>
    cases horientation : rotation.orientation <;>
    cases hside : splice.splitTrunkFaceSide <;>
    simp [LocalizedCommonRunSplitArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition,
      LocalizedCommonRunSplitArmState.ambientRoutePosition,
      LocalizedCommonRunSplitArmState.ambientPrefixPosition,
      LocalizedCommonRunSplitArmState.ambientSuffixPosition,
      LocalizedCommonRunSplitArmState.ambientTrunkPosition,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition, horientation, hside]

/-- Closed merge route table: the local face chooses a route from the
rotation orientation, trunk-side coordinate, and displayed-order flip. -/
theorem LocalizedCommonRunMergeArmState.ambientTrunkFaceRoute_eq
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
    state.ambientTrunkFaceRoute rotation =
      RotationSystem.threeArmFaceRoute state.ambientRouteOrderFlipped
        rotation.orientation splice.mergeTrunkFaceSide := by
  cases state <;>
    cases horientation : rotation.orientation <;>
    cases hside : splice.mergeTrunkFaceSide <;>
    simp [LocalizedCommonRunMergeArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition,
      LocalizedCommonRunMergeArmState.ambientSuffixPosition,
      LocalizedCommonRunMergeArmState.ambientTrunkPosition,
      LocalizedCommonRunMergeArmState.ambientRouteOrderFlipped,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition,
      RotationSystem.threeArmFaceRoute, horientation, hside]

/-- Closed split route table: the local face chooses a route from the
rotation orientation, reversed-trunk side, and displayed-order flip. -/
theorem LocalizedCommonRunSplitArmState.ambientTrunkFaceRoute_eq
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
    state.ambientTrunkFaceRoute rotation =
      RotationSystem.threeArmFaceRoute state.ambientRouteOrderFlipped
        rotation.orientation splice.splitTrunkFaceSide := by
  cases state <;>
    cases horientation : rotation.orientation <;>
    cases hside : splice.splitTrunkFaceSide <;>
    simp [LocalizedCommonRunSplitArmState.ambientTrunkFaceRoute,
      LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition,
      LocalizedCommonRunSplitArmState.ambientSuffixPosition,
      LocalizedCommonRunSplitArmState.ambientTrunkPosition,
      LocalizedCommonRunSplitArmState.ambientRouteOrderFlipped,
      RotationSystem.ThreeDartRotation.faceMatePosition,
      RotationSystem.orientedStepPosition,
      RotationSystem.threeArmFaceRoute, horientation, hside]

/-- The merge face mate carries the selected remote face on the side
opposite its trunk-side coordinate. -/
theorem LocalizedCommonRunMergeArmState.ambientRotation_faceMateSideFace_eq
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
    rotation.displayedSideOrbitFace
        (state.ambientTrunkFaceMatePosition rotation)
        (!splice.mergeTrunkFaceSide) = face := by
  unfold LocalizedCommonRunMergeArmState.ambientTrunkFaceMatePosition
  rw [← rotation.displayedSideOrbitFace_faceMatePosition
    state.ambientTrunkPosition splice.mergeTrunkFaceSide]
  exact state.ambientRotation_trunkSideFace_eq rotation htwoSided

/-- The split face mate carries the selected remote face on the side
opposite its reversed-trunk coordinate. -/
theorem LocalizedCommonRunSplitArmState.ambientRotation_faceMateSideFace_eq
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
    rotation.displayedSideOrbitFace
        (state.ambientTrunkFaceMatePosition rotation)
        (!splice.splitTrunkFaceSide) = face := by
  unfold LocalizedCommonRunSplitArmState.ambientTrunkFaceMatePosition
  rw [← rotation.displayedSideOrbitFace_faceMatePosition
    state.ambientTrunkPosition splice.splitTrunkFaceSide]
  exact state.ambientRotation_trunkSideFace_eq rotation htwoSided

/-- Exact endpoint face-mate equation: after the trunk reversal, the split
external arm exposes the remote face at the original merge trunk-side
coordinate. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpoint_faceMateFace_eq
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
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    mergeRotation.displayedSideOrbitFace
        (mergeState.ambientTrunkFaceMatePosition mergeRotation)
        (!splice.mergeTrunkFaceSide) =
      splitRotation.displayedSideOrbitFace
        (splitState.ambientTrunkFaceMatePosition splitRotation)
        splice.mergeTrunkFaceSide := by
  have hcomplement := splice.splitTrunkFaceSide_eq_not_merge
    hcubic hrotation htwoSided
  calc
    mergeRotation.displayedSideOrbitFace
          (mergeState.ambientTrunkFaceMatePosition mergeRotation)
          (!splice.mergeTrunkFaceSide) = face :=
      mergeState.ambientRotation_faceMateSideFace_eq
        mergeRotation htwoSided
    _ = splitRotation.displayedSideOrbitFace
          (splitState.ambientTrunkFaceMatePosition splitRotation)
          (!splice.splitTrunkFaceSide) :=
      (splitState.ambientRotation_faceMateSideFace_eq
        splitRotation htwoSided).symm
    _ = splitRotation.displayedSideOrbitFace
          (splitState.ambientTrunkFaceMatePosition splitRotation)
          splice.mergeTrunkFaceSide := by
      rw [hcomplement]
      cases splice.mergeTrunkFaceSide <;> rfl

/-- Exact endpoint equation expressed in prefix/suffix route coordinates
rather than raw displayed positions. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpoint_routeFace_eq
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
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    mergeRotation.displayedSideOrbitFace
        (mergeState.ambientRoutePosition
          (mergeState.ambientTrunkFaceRoute mergeRotation))
        (!splice.mergeTrunkFaceSide) =
      splitRotation.displayedSideOrbitFace
        (splitState.ambientRoutePosition
          (splitState.ambientTrunkFaceRoute splitRotation))
        splice.mergeTrunkFaceSide := by
  rw [← mergeState.ambientTrunkFaceMatePosition_eq_route mergeRotation,
    ← splitState.ambientTrunkFaceMatePosition_eq_route splitRotation]
  exact splice.ambientEndpoint_faceMateFace_eq mergeState splitState
    mergeRotation splitRotation hcubic hrotation htwoSided

/-- Whether the selected remote-face route changes from prefix to suffix,
or from suffix to prefix, between the two trunk endpoints. -/
noncomputable def LocalizedAlignedCommonRunSplice.ambientEndpointRouteFlip
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
      graphData.toRotationSystem splitState.ambientOutgoingDarts) : Bool :=
  Bool.xor (mergeState.ambientTrunkFaceRoute mergeRotation)
    (splitState.ambientTrunkFaceRoute splitRotation)

/-- Local chiral monodromy formula for a common-run trunk. Once facial
transport complements the endpoint side coordinate, the prefix/suffix
route flip is independent of that face coordinate and equals the finite
parity of the two endpoint frames. -/
theorem LocalizedAlignedCommonRunSplice.ambientEndpointRouteFlip_eq_frameParity
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
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    splice.ambientEndpointRouteFlip mergeState splitState
        mergeRotation splitRotation =
      RotationSystem.threeArmEndpointFrameParity
        mergeState.ambientRouteOrderFlipped
        splitState.ambientRouteOrderFlipped
        mergeRotation.orientation splitRotation.orientation := by
  unfold LocalizedAlignedCommonRunSplice.ambientEndpointRouteFlip
  rw [mergeState.ambientTrunkFaceRoute_eq mergeRotation,
    splitState.ambientTrunkFaceRoute_eq splitRotation,
    splice.splitTrunkFaceSide_eq_not_merge hcubic hrotation htwoSided]
  exact RotationSystem.threeArmFaceRoute_xor_complement
    mergeState.ambientRouteOrderFlipped
    splitState.ambientRouteOrderFlipped
    mergeRotation.orientation splitRotation.orientation
    splice.mergeTrunkFaceSide

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
