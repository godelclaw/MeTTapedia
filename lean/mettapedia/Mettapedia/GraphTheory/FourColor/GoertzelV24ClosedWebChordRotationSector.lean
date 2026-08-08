import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordCycleFaceSideTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChordDiagram
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleTurn

/-!
# Rotation-side coordinates for closed-web radial chords

The source's two sectors are the two local sides of an oriented radial path.
At the left endpoint of an actual third-color chord there are exactly three
outgoing darts: backward along the radial path, forward along it, and along
the chord.  The cyclic vertex rotation therefore gives the chord one of two
possible sides.  This module materializes that intrinsic Boolean coordinate;
the subsequent noncrossing theorem must prove that strictly interleaving
chords receive opposite coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordRotationSector

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordCycleFaceSideTransport
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24FaceDualConnectedness
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordRotationSectorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace MajorityChordOnRadialPath

variable {data : AnnularBoundaryData G outerCount}
  {C : G.EdgeColoring Color} {majority first second : Color}
  {component : (colorPairSupportGraph C first second).ConnectedComponent}
  {radial : ComponentRadialPath data C first second component}

/-- The outgoing dart from the left chord endpoint toward the preceding
radial-path vertex. -/
def leftBackwardDart
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) : G.Dart := by
  let ambient := ambientRadialPath radial
  have hleft : 0 < chord.left.val := chord.left_pos hdata htriple
  have hstep : chord.left.val - 1 < ambient.length := by
    rw [ambientRadialPath_length]
    have hright := chord.right_lt_length hdata htriple
    omega
  have hadj := ambient.adj_getVert_succ hstep
  have hnext : chord.left.val - 1 + 1 = chord.left.val := by omega
  exact ⟨(ambient.getVert chord.left.val,
      ambient.getVert (chord.left.val - 1)), by
    simpa [hnext] using hadj.symm⟩

/-- The outgoing dart from the left chord endpoint toward the succeeding
radial-path vertex. -/
def leftForwardDart
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) : G.Dart := by
  let ambient := ambientRadialPath radial
  have hstep : chord.left.val < ambient.length := by
    rw [ambientRadialPath_length]
    exact lt_trans chord.left_lt_right
      (chord.right_lt_length hdata htriple)
  exact ⟨(ambient.getVert chord.left.val,
      ambient.getVert (chord.left.val + 1)),
    ambient.adj_getVert_succ hstep⟩

@[simp] theorem leftBackwardDart_fst
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    (leftBackwardDart chord hdata htriple).fst = chord.chordDart.fst := by
  rfl

@[simp] theorem leftForwardDart_fst
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    (leftForwardDart chord hdata htriple).fst = chord.chordDart.fst := by
  rfl

/-- The backward and forward radial darts at a chord endpoint are distinct. -/
theorem leftBackwardDart_ne_leftForwardDart
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    leftBackwardDart chord hdata htriple ≠
      leftForwardDart chord hdata htriple := by
  intro hdarts
  have hsnd := congrArg (fun dart : G.Dart => dart.snd) hdarts
  change (ambientRadialPath radial).getVert (chord.left.val - 1) =
      (ambientRadialPath radial).getVert (chord.left.val + 1) at hsnd
  have hleft : 0 < chord.left.val := chord.left_pos hdata htriple
  have hright := chord.right_lt_length hdata htriple
  have hleftBound : chord.left.val ≤ radial.path.length :=
    Nat.le_of_lt (lt_trans chord.left_lt_right hright)
  have hbackBound : chord.left.val - 1 ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact le_trans (Nat.sub_le _ _) hleftBound
  have hforwardBound : chord.left.val + 1 ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact Nat.succ_le_of_lt (lt_trans chord.left_lt_right hright)
  have hindices : chord.left.val - 1 = chord.left.val + 1 :=
    (ambientRadialPath_isPath radial).getVert_injOn
      hbackBound hforwardBound hsnd
  omega

/-- The third-color chord dart is not the backward selected-color dart. -/
theorem chordDart_ne_leftBackwardDart
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    chord.chordDart ≠ leftBackwardDart chord hdata htriple := by
  intro hdarts
  have hsnd := congrArg (fun dart : G.Dart => dart.snd) hdarts
  change (ambientRadialPath radial).getVert chord.right.val =
      (ambientRadialPath radial).getVert (chord.left.val - 1) at hsnd
  have hleft : 0 < chord.left.val := chord.left_pos hdata htriple
  have hright := chord.right_lt_length hdata htriple
  have hrightBound : chord.right.val ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact Nat.le_of_lt hright
  have hbackBound : chord.left.val - 1 ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact le_trans (Nat.sub_le _ _)
      (Nat.le_of_lt (lt_trans chord.left_lt_right hright))
  have hindices : chord.right.val = chord.left.val - 1 :=
    (ambientRadialPath_isPath radial).getVert_injOn
      hrightBound hbackBound hsnd
  have horder := chord.left_lt_right
  omega

/-- The third-color chord dart is not the forward selected-color dart. -/
theorem chordDart_ne_leftForwardDart
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    chord.chordDart ≠ leftForwardDart chord hdata htriple := by
  intro hdarts
  have hsnd := congrArg (fun dart : G.Dart => dart.snd) hdarts
  change (ambientRadialPath radial).getVert chord.right.val =
      (ambientRadialPath radial).getVert (chord.left.val + 1) at hsnd
  have hright := chord.right_lt_length hdata htriple
  have hrightBound : chord.right.val ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact Nat.le_of_lt hright
  have hforwardBound : chord.left.val + 1 ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    exact Nat.succ_le_of_lt (lt_trans chord.left_lt_right hright)
  have hindices : chord.right.val = chord.left.val + 1 :=
    (ambientRadialPath_isPath radial).getVert_injOn
      hrightBound hforwardBound hsnd
  have hspan := chord.one_lt_span htriple
  omega

/-- At the left endpoint, the vertex rotation sends the chord dart to one
of the two radial darts.  These are exactly the two embedded sectors. -/
theorem rho_chordDart_eq_backward_or_forward
    (embedded : ClosedWebAnnularEmbedding data)
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    embedded.RS.rho chord.chordDart =
        leftBackwardDart chord hdata htriple ∨
      embedded.RS.rho chord.chordDart =
        leftForwardDart chord hdata htriple := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hchordMem : chord.chordDart ∈ chord.cycleWalk.darts := by
    simp [MajorityChordOnRadialPath.cycleWalk]
  have hcard := cycleWalk_dartsAt_card_eq_three
    embedded hdata chord htriple chord.chordDart hchordMem
  exact embedded.RS.rho_eq_second_or_third_of_card_dartsAt_eq_three
    hrotation hcard
      (by simp) (by simp)
      (chordDart_ne_leftBackwardDart chord hdata htriple)
      (chordDart_ne_leftForwardDart chord hdata htriple)
      (leftBackwardDart_ne_leftForwardDart chord hdata htriple)

/-- Intrinsic Boolean side of a chord: `true` means that the forward radial
dart is the immediate successor of the chord dart in the vertex rotation. -/
def rotationSector
    (embedded : ClosedWebAnnularEmbedding data)
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) : Bool :=
  decide (embedded.RS.rho chord.chordDart =
    leftForwardDart chord hdata htriple)

@[simp] theorem rotationSector_eq_true_iff
    (embedded : ClosedWebAnnularEmbedding data)
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    rotationSector embedded chord hdata htriple = true ↔
      embedded.RS.rho chord.chordDart =
        leftForwardDart chord hdata htriple := by
  simp [rotationSector]

@[simp] theorem rotationSector_eq_false_iff
    (embedded : ClosedWebAnnularEmbedding data)
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second) :
    rotationSector embedded chord hdata htriple = false ↔
      embedded.RS.rho chord.chordDart =
        leftBackwardDart chord hdata htriple := by
  unfold rotationSector
  rw [decide_eq_false_iff_not]
  constructor
  · intro hnotForward
    rcases rho_chordDart_eq_backward_or_forward embedded chord
        hdata htriple with hbackward | hforward
    · exact hbackward
    · exact False.elim (hnotForward hforward)
  · intro hbackward hforward
    exact leftBackwardDart_ne_leftForwardDart chord hdata htriple
      (hbackward.symm.trans hforward)

end MajorityChordOnRadialPath

/-- The rotation-side coordinate on every ordered chord position.  Positions
which are not actual majority chords receive the harmless default `false`;
`SameSectorNoncrossing` only queries members of the actual diagram. -/
def positionRotationSector
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (htriple : IsTaitColorTriple majority first second)
    (position : OrderedPathChord (radial.path.length + 1)) : Bool := by
  classical
  exact if hposition : IsMajorityChordAt
        C majority first second radial position then
      MajorityChordOnRadialPath.rotationSector embedded
        (majorityChordOfPosition position hposition) hdata htriple
    else false

/-- On an actual diagram member, the position-level coordinate is exactly
the intrinsic rotation coordinate of its materialized graph chord. -/
theorem positionRotationSector_eq_rotationSector
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (htriple : IsTaitColorTriple majority first second)
    (position : OrderedPathChord (radial.path.length + 1))
    (hposition : position ∈
      majorityChordDiagram C majority first second radial) :
    positionRotationSector embedded hdata radial htriple position =
      MajorityChordOnRadialPath.rotationSector embedded
        (majorityChordOfPosition position
          ((mem_majorityChordDiagram_iff).1 hposition)) hdata htriple := by
  classical
  simp [positionRotationSector,
    (mem_majorityChordDiagram_iff).1 hposition]

end

end GoertzelV24ClosedWebChordRotationSector

end Mettapedia.GraphTheory.FourColor
