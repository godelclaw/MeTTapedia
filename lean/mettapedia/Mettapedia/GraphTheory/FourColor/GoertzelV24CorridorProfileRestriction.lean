import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Restricting a full corridor profile to selected crossing ports

A literal corridor Cell has one combined profile on all of its boundary
crossings, while its transfer matrix exposes only one boundary block at a
time.  This file gives that operation its small generic form.  The face
fragment carrier and every terminal remain unchanged; only the crossing-port
coordinates are selected by an explicit map.

No geometry, profile equality, or transfer conclusion is asserted here.  The
compatibility theorem proves that restricting a graph-derived profile is the
same operation as first restricting its raw cut coordinates and then computing
the profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorProfileRestriction

open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Select crossing ports while leaving terminal coordinates fixed. -/
def mapCorridorPort
    {smallWidth largeWidth terminalCount : Nat}
    (inclusion : Fin smallWidth → Fin largeWidth) :
    CorridorPort smallWidth terminalCount →
      CorridorPort largeWidth terminalCount
  | .inl crossing => .inl (inclusion crossing)
  | .inr terminal => .inr terminal

@[simp]
theorem mapCorridorPort_inl
    {smallWidth largeWidth terminalCount : Nat}
    (inclusion : Fin smallWidth → Fin largeWidth)
    (crossing : Fin smallWidth) :
    mapCorridorPort (terminalCount := terminalCount) inclusion (.inl crossing) =
      .inl (inclusion crossing) :=
  rfl

@[simp]
theorem mapCorridorPort_inr
    {smallWidth largeWidth terminalCount : Nat}
    (inclusion : Fin smallWidth → Fin largeWidth)
    (terminal : Fin terminalCount) :
    mapCorridorPort (smallWidth := smallWidth) inclusion (.inr terminal) =
      .inr terminal :=
  rfl

/-- Restrict a complete five-field profile to a selected crossing block.
Face fragments and terminals are retained exactly. -/
def CorridorCutProfile.restrictCrossings
    {smallWidth largeWidth terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile largeWidth terminalCount faceFragmentCount)
    (inclusion : Fin smallWidth → Fin largeWidth) :
    CorridorCutProfile smallWidth terminalCount faceFragmentCount where
  edgeColor crossing := profile.edgeColor (inclusion crossing)
  strandConnected pair first second :=
    profile.strandConnected pair
      (mapCorridorPort inclusion first) (mapCorridorPort inclusion second)
  faceContinues := profile.faceContinues
  fragmentContainsPort fragment port :=
    profile.fragmentContainsPort fragment (mapCorridorPort inclusion port)
  faceLengthCap := profile.faceLengthCap

/-- Restrict the raw crossing coordinates of graph-derived cut data while
leaving its region, terminals, and fragment indexing unchanged. -/
def GraphCorridorCutData.restrictCrossings
    {RS : RotationSystem V E}
    {smallWidth largeWidth terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS largeWidth terminalCount faceFragmentCount)
    (inclusion : Fin smallWidth → Fin largeWidth) :
    GraphCorridorCutData RS smallWidth terminalCount faceFragmentCount where
  regionEdges := data.regionEdges
  crossingEdge crossing := data.crossingEdge (inclusion crossing)
  terminalEdge := data.terminalEdge
  fragmentFace := data.fragmentFace
  fragmentEdges := data.fragmentEdges

/-- Two raw graph-cut presentations are equal when their five stored fields
agree pointwise.  This is the record extensionality needed by concrete source
restrictions; no validity predicate is added to the data. -/
theorem graphCorridorCutData_eq_of_fields
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount}
    (regionEdges : left.regionEdges = right.regionEdges)
    (crossingEdge : ∀ crossing,
      left.crossingEdge crossing = right.crossingEdge crossing)
    (terminalEdge : ∀ terminal,
      left.terminalEdge terminal = right.terminalEdge terminal)
    (fragmentFace : ∀ fragment,
      left.fragmentFace fragment = right.fragmentFace fragment)
    (fragmentEdges : ∀ fragment,
      left.fragmentEdges fragment = right.fragmentEdges fragment) :
    left = right := by
  have crossingEdge' : left.crossingEdge = right.crossingEdge :=
    funext crossingEdge
  have terminalEdge' : left.terminalEdge = right.terminalEdge :=
    funext terminalEdge
  have fragmentFace' : left.fragmentFace = right.fragmentFace :=
    funext fragmentFace
  have fragmentEdges' : left.fragmentEdges = right.fragmentEdges :=
    funext fragmentEdges
  cases left
  cases right
  cases regionEdges
  cases crossingEdge'
  cases terminalEdge'
  cases fragmentFace'
  cases fragmentEdges'
  rfl

@[simp]
theorem GraphCorridorCutData.restrictCrossings_portEdge
    {RS : RotationSystem V E}
    {smallWidth largeWidth terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS largeWidth terminalCount faceFragmentCount)
    (inclusion : Fin smallWidth → Fin largeWidth)
    (port : CorridorPort smallWidth terminalCount) :
    (GraphCorridorCutData.restrictCrossings data inclusion).portEdge port =
      data.portEdge (mapCorridorPort inclusion port) := by
  cases port <;> rfl

/-- Profile construction commutes with restriction of crossing coordinates.
This is the graph-facing justification for using a combined Cell profile and
then exposing either source boundary block. -/
theorem GraphCorridorCutData.restrictCrossings_regionalProfile
    {RS : RotationSystem V E}
    {smallWidth largeWidth terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS largeWidth terminalCount faceFragmentCount)
    (inclusion : Fin smallWidth → Fin largeWidth)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.restrictCrossings
        (data.regionalProfile color hcrossing) inclusion =
      (GraphCorridorCutData.restrictCrossings data inclusion).regionalProfile color
        (fun crossing => hcrossing (inclusion crossing)) := by
  unfold CorridorCutProfile.restrictCrossings
  unfold GraphCorridorCutData.regionalProfile
  congr 1
  · exact funext fun pair => funext fun first => funext fun second => by
      cases first <;> cases second <;> rfl
  · exact funext fun fragment => funext fun port => by
      cases port <;> rfl

/-- Regional profile construction respects equality of the raw cut data.
The nonzero-crossing witnesses may be propositionally different; proof
irrelevance is discharged here so concrete transports do not need dependent
rewrites through `regionalProfile`. -/
theorem graphCorridorCutData_regionalProfile_eq_of_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount}
    (hdata : left = right)
    (color : E → Color)
    (hleft : ∀ crossing, color (left.crossingEdge crossing) ≠ 0)
    (hright : ∀ crossing, color (right.crossingEdge crossing) ≠ 0) :
    left.regionalProfile color hleft =
      right.regionalProfile color hright := by
  cases hdata
  have hproof : hleft = hright := Subsingleton.elim _ _
  cases hproof
  rfl

end

end GoertzelV24CorridorProfileRestriction

end Mettapedia.GraphTheory.FourColor
