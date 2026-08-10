import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile

/-!
# Regional profiles for cut-open corridor pieces

The compositional source's `Count` functor assigns a finite profile to an
*open* piece.  The existing graph-derived profile used a closed ambient Tait
coloring as its input, even though its five coordinates only inspect the
selected regional edges and require nonzero colors at the crossed ports.

This file exposes that smaller dependency.  It does not assert that an
arbitrary regional color function is proper: properness belongs to the
concrete open-tangle coloring layer.  The compatibility theorem at the end
shows that the established closed-graph profile is exactly this construction
when the regional colors come from a closed Tait coloring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphDerivedCorridorCutProfile

open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The finite corridor profile read from a color function on the selected
regional edges.  Only the crossing-port colors need to be nonzero in order to
enter the three-symbol boundary alphabet.  This is the profile component used
by an actual cut-open tangle; a later construction supplies the regional
color function from that tangle and proves its local Tait property. -/
def GraphCorridorCutData.regionalProfile
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0) :
    CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount where
  edgeColor crossing :=
    strandColorOfNonzero (color (data.crossingEdge crossing))
      (hcrossing crossing)
  strandConnected pair left right :=
    regionalTrackedConnectivity RS data.regionEdges color pair
      (data.portEdge left) (data.portEdge right)
  faceContinues left right :=
    decide (data.fragmentFace left = data.fragmentFace right)
  fragmentContainsPort fragment port :=
    decide (data.portEdge port ∈ data.regionalFragmentEdges fragment)
  faceLengthCap := data.cappedRegionalFaceLength

@[simp]
theorem GraphCorridorCutData.regionalProfile_edgeColor_toColor
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (crossing : Fin crossingEdgeCount) :
    ((data.regionalProfile color hcrossing).edgeColor crossing).toColor =
      color (data.crossingEdge crossing) := by
  simp [GraphCorridorCutData.regionalProfile]

theorem GraphCorridorCutData.regionalProfile_strandConnected_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (pair : TrackedColorPair)
    (left right : CorridorPort crossingEdgeCount terminalCount) :
    (data.regionalProfile color hcrossing).strandConnected pair left right = true ↔
      data.portEdge left ∈ data.regionEdges ∧
      data.portEdge right ∈ data.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (color (data.portEdge left)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (color (data.portEdge right)) ∧
      (regionalTrackedEdgeGraph RS data.regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (data.portEdge left) (data.portEdge right) := by
  exact regionalTrackedConnectivity_eq_true_iff RS data.regionEdges color
    pair (data.portEdge left) (data.portEdge right)

@[simp]
theorem GraphCorridorCutData.regionalProfile_faceContinues_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (left right : Fin faceFragmentCount) :
    (data.regionalProfile color hcrossing).faceContinues left right = true ↔
      data.fragmentFace left = data.fragmentFace right := by
  simp [GraphCorridorCutData.regionalProfile]

@[simp]
theorem GraphCorridorCutData.regionalProfile_fragmentContainsPort_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (fragment : Fin faceFragmentCount)
    (port : CorridorPort crossingEdgeCount terminalCount) :
    (data.regionalProfile color hcrossing).fragmentContainsPort fragment port = true ↔
      data.portEdge port ∈ data.regionalFragmentEdges fragment := by
  simp [GraphCorridorCutData.regionalProfile]

@[simp]
theorem GraphCorridorCutData.regionalProfile_faceLengthCap_val
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (fragment : Fin faceFragmentCount) :
    ((data.regionalProfile color hcrossing).faceLengthCap fragment).val =
      min (data.regionalFragmentEdges fragment).card 5 :=
  rfl

/-- Closed graph profiles are the special case of regional profiles obtained
by restricting the ambient Tait coloring to the selected region.  Thus moving
to the open interface has changed no finite state or splice observation. -/
theorem GraphCorridorCutData.regionalProfile_eq_profile
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    data.regionalProfile coloring
      (fun crossing => hcoloring (data.crossingEdge crossing)) =
      data.profile coloring hcoloring := by
  rfl

end

end GoertzelV24GraphDerivedCorridorCutProfile

end Mettapedia.GraphTheory.FourColor
