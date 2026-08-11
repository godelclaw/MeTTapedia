import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile

/-!
# Restricting terminal-aware corridor profiles

The source Cell-3 state remembers five fixed cap-foot terminals, whereas the
literal Cell generator has no terminals.  This file supplies the exact
forgetful map between those two finite carriers.  It proves that terminal
augmentation is conservative: after forgetting the terminal rows and
columns, a graph-derived augmented profile is definitionally the original
zero-terminal profile.

This is only a restriction theorem.  It does not claim that the terminal
coordinates are determined by the local Cell, nor that the one-Cell transfer
is deterministic.  The terminal-aware transfer remains a relation whose
connectivity and capped-face coordinates must be updated together.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphDerivedTerminalProfile

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Embed a crossing-only port into a terminal-aware port carrier.  The
`Fin 0` branch is impossible, so this adds no synthetic terminal. -/
def crossingPortOfNoTerminals
    {crossingEdgeCount terminalCount : Nat} :
    CorridorPort crossingEdgeCount 0 →
      CorridorPort crossingEdgeCount terminalCount
  | .inl crossing => .inl crossing
  | .inr terminal => Fin.elim0 terminal

/-- Forget every fixed-terminal observation while retaining the complete
crossing-color, crossing-connectivity, face-incidence, and capped-length
coordinates. -/
def forgetTerminals
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) :
    CorridorCutProfile crossingEdgeCount 0 faceFragmentCount where
  edgeColor := profile.edgeColor
  strandConnected pair left right :=
    profile.strandConnected pair
      (crossingPortOfNoTerminals left)
      (crossingPortOfNoTerminals right)
  faceContinues := profile.faceContinues
  fragmentContainsPort fragment port :=
    profile.fragmentContainsPort fragment
      (crossingPortOfNoTerminals port)
  faceLengthCap := profile.faceLengthCap

@[simp] theorem forgetTerminals_edgeColor
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (crossing : Fin crossingEdgeCount) :
    (forgetTerminals profile).edgeColor crossing =
      profile.edgeColor crossing :=
  rfl

@[simp] theorem forgetTerminals_strandConnected
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (pair : TrackedColorPair) (left right : Fin crossingEdgeCount) :
    (forgetTerminals profile).strandConnected pair (.inl left) (.inl right) =
      profile.strandConnected pair (.inl left) (.inl right) :=
  rfl

@[simp] theorem forgetTerminals_faceContinues
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (left right : Fin faceFragmentCount) :
    (forgetTerminals profile).faceContinues left right =
      profile.faceContinues left right :=
  rfl

@[simp] theorem forgetTerminals_fragmentContainsPort
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (fragment : Fin faceFragmentCount) (crossing : Fin crossingEdgeCount) :
    (forgetTerminals profile).fragmentContainsPort fragment (.inl crossing) =
      profile.fragmentContainsPort fragment (.inl crossing) :=
  rfl

@[simp] theorem forgetTerminals_faceLengthCap
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (fragment : Fin faceFragmentCount) :
    (forgetTerminals profile).faceLengthCap fragment =
      profile.faceLengthCap fragment :=
  rfl

/-- Forget terminal observations without changing the exact face-fragment
coordinate of a bounded profile. -/
def forgetBoundedTerminals
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (state : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    BoundedCorridorCutProfile crossingEdgeCount 0 faceFragmentBound where
  faceFragmentCount := state.faceFragmentCount
  profile := forgetTerminals state.profile

@[simp] theorem forgetBoundedTerminals_faceFragmentCount
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (state : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    (forgetBoundedTerminals state).faceFragmentCount = state.faceFragmentCount :=
  rfl

@[simp] theorem forgetBoundedTerminals_profile
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (state : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    (forgetBoundedTerminals state).profile = forgetTerminals state.profile :=
  rfl

/-- Adding terminal edges to raw graph data and then forgetting their profile
coordinates recovers the original graph-derived profile exactly.  Thus the
terminal-aware state is a conservative refinement of the existing local
profile carrier, not a replacement for its `Count` semantics. -/
@[simp] theorem profile_forgetTerminals_withTerminalEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount → E)
    (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    forgetTerminals
        ((withTerminalEdges cut terminalEdge).profile coloring hcoloring) =
      cut.profile coloring hcoloring := by
  simp [forgetTerminals, GraphCorridorCutData.profile,
    withTerminalEdges, crossingPortOfNoTerminals]
  constructor
  · funext pair left right
    rcases left with crossing | terminal
    · rcases right with crossing' | terminal'
      · rfl
      · exact Fin.elim0 terminal'
    · exact Fin.elim0 terminal
  · constructor
    · rfl
    · constructor
      · funext fragment port
        rcases port with crossing | terminal
        · rfl
        · exact Fin.elim0 terminal
      · rfl

end

end GoertzelV24GraphDerivedTerminalProfile

end Mettapedia.GraphTheory.FourColor
