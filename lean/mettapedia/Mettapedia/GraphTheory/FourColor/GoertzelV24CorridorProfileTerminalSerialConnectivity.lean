import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileSerialConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestriction

/-!
# Serial composition of terminal-aware profile connectivity

The moving corridor cut composes with one combined Cell while the fixed
terminal family remains visible on both sides.  The finite carrier for one
serial step is therefore the sum of the Cell's crossing ports and the fixed
terminals.  Incoming and outgoing crossing ports are embedded into the Cell
block; terminal positions are carried identically.

The relation below is terminal-aware but still only the connectivity
coordinate of the manuscript profile.  The Cell has no independent terminal
ports.  Its components compose with components already recorded by the
incoming cumulative profile, and the outgoing component matrix is their
guarded reflexive-transitive closure.

Terminal guards are read from the incoming diagonal component bits.  This is
load-bearing: reflexive closure alone would otherwise make every terminal
diagonal true for every tracked color pair.  No functional update,
determinism, face-progress law, or geometric carrier identification is
asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorProfileTerminalSerialConnectivity

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileSerialConnectivity
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- Embed every incoming cumulative-profile port into the common serial
carrier.  Moving crossings enter through the Cell's left interface; fixed
terminals retain their source index. -/
def serialTerminalInputPort
    {inputWidth cellWidth terminalCount : Nat}
    (leftIndex : Fin inputWidth → Fin cellWidth) :
    CorridorPort inputWidth terminalCount →
      CorridorPort cellWidth terminalCount
  | .inl crossing => .inl (leftIndex crossing)
  | .inr terminal => .inr terminal

/-- Embed every outgoing port into the same serial carrier. -/
def serialTerminalOutputPort
    {outputWidth cellWidth terminalCount : Nat}
    (rightIndex : Fin outputWidth → Fin cellWidth) :
    CorridorPort outputWidth terminalCount →
      CorridorPort cellWidth terminalCount
  | .inl crossing => .inl (rightIndex crossing)
  | .inr terminal => .inr terminal

@[simp] theorem serialTerminalInputPort_crossing
    {inputWidth cellWidth terminalCount : Nat}
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (crossing : Fin inputWidth) :
    serialTerminalInputPort (terminalCount := terminalCount) leftIndex
        (.inl crossing) =
      (.inl (leftIndex crossing) : CorridorPort cellWidth terminalCount) :=
  rfl

@[simp] theorem serialTerminalInputPort_terminal
    {inputWidth cellWidth terminalCount : Nat}
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (terminal : Fin terminalCount) :
    serialTerminalInputPort leftIndex (.inr terminal) =
      (.inr terminal : CorridorPort cellWidth terminalCount) :=
  rfl

@[simp] theorem serialTerminalOutputPort_crossing
    {outputWidth cellWidth terminalCount : Nat}
    (rightIndex : Fin outputWidth → Fin cellWidth)
    (crossing : Fin outputWidth) :
    serialTerminalOutputPort (terminalCount := terminalCount) rightIndex
        (.inl crossing) =
      (.inl (rightIndex crossing) : CorridorPort cellWidth terminalCount) :=
  rfl

@[simp] theorem serialTerminalOutputPort_terminal
    {outputWidth cellWidth terminalCount : Nat}
    (rightIndex : Fin outputWidth → Fin cellWidth)
    (terminal : Fin terminalCount) :
    serialTerminalOutputPort rightIndex (.inr terminal) =
      (.inr terminal : CorridorPort cellWidth terminalCount) :=
  rfl

/-- One component move on the common terminal-aware carrier.  It is either an
incoming cumulative component after port reindexing, or a component of the
combined Cell between two of its crossing ports. -/
def serialTerminalProfileConnectivityStep
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair)
    (first second : CorridorPort cellWidth terminalCount) : Prop :=
  (∃ left right : CorridorPort inputWidth terminalCount,
      serialTerminalInputPort leftIndex left = first ∧
        serialTerminalInputPort leftIndex right = second ∧
        input.strandConnected pair left right = true) ∨
    ∃ left right : Fin cellWidth,
      first = .inl left ∧ second = .inl right ∧
        cell.strandConnected pair (.inl left) (.inl right) = true

/-- Whether an outgoing port carries the tracked pair.  Crossing colors are
read from the outgoing cut coloring.  A fixed terminal's tracked-color guard
is its incoming diagonal component bit, which is the profile's finite record
of that unchanged terminal color. -/
def serialTerminalOutputPortTracked
    {inputWidth outputWidth terminalCount inputFragmentCount
      outputFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (output : CorridorCutProfile outputWidth terminalCount outputFragmentCount)
    (pair : TrackedColorPair) :
    CorridorPort outputWidth terminalCount → Prop
  | .inl crossing =>
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (output.edgeColor crossing).toColor
  | .inr terminal =>
      input.strandConnected pair (.inr terminal) (.inr terminal) = true

/-- The terminal-aware finite connectivity coordinate of serial profile
composition.  It preserves the fixed terminal family, glues the incoming cut
to the Cell's left ports, and reads the outgoing cut from the Cell's right
ports. -/
structure SerialTerminalProfileConnectivity
    {inputWidth outputWidth cellWidth terminalCount : Nat}
    {inputFragmentCount cellFragmentCount outputFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (output : CorridorCutProfile outputWidth terminalCount outputFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (rightIndex : Fin outputWidth → Fin cellWidth) : Prop where
  leftColors : ∀ index,
    input.edgeColor index = cell.edgeColor (leftIndex index)
  rightColors : ∀ index,
    output.edgeColor index = cell.edgeColor (rightIndex index)
  strandConnected : ∀ (pair : TrackedColorPair)
      (first second : CorridorPort outputWidth terminalCount),
    output.strandConnected pair first second = true ↔
      serialTerminalOutputPortTracked input output pair first ∧
        serialTerminalOutputPortTracked input output pair second ∧
        Relation.ReflTransGen
          (serialTerminalProfileConnectivityStep input cell leftIndex pair)
          (serialTerminalOutputPort rightIndex first)
          (serialTerminalOutputPort rightIndex second)

/-- Every incoming component is one step after embedding its endpoints in the
common serial carrier. -/
theorem serialTerminalProfileConnectivityStep_of_input
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair)
    (first second : CorridorPort inputWidth terminalCount)
    (hconnected : input.strandConnected pair first second = true) :
    serialTerminalProfileConnectivityStep input cell leftIndex pair
      (serialTerminalInputPort leftIndex first)
      (serialTerminalInputPort leftIndex second) := by
  exact Or.inl ⟨first, second, rfl, rfl, hconnected⟩

/-- Every Cell component is one step between the corresponding crossing
positions of the common carrier. -/
theorem serialTerminalProfileConnectivityStep_of_cell
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hconnected :
      cell.strandConnected pair (.inl first) (.inl second) = true) :
    serialTerminalProfileConnectivityStep input cell leftIndex pair
      (.inl first) (.inl second) := by
  exact Or.inr ⟨first, second, rfl, rfl, hconnected⟩

/-- A zero-terminal component step embeds into the richer fixed-terminal
step.  The converse is intentionally absent: a genuine serial path may pass
through a fixed terminal and disappear after terminal observations are
forgotten. -/
theorem serialTerminalProfileConnectivityStep_of_forgetTerminals
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hstep : serialProfileConnectivityStep (forgetTerminals input) cell
      leftIndex pair first second) :
    serialTerminalProfileConnectivityStep input cell leftIndex pair
      (.inl first) (.inl second) := by
  rcases hstep with hinput | hcell
  · rcases hinput with ⟨left, right, hleft, hright, hconnected⟩
    refine Or.inl ⟨.inl left, .inl right, ?_, ?_, ?_⟩
    · simpa using congrArg
        (fun position =>
          (.inl position : CorridorPort cellWidth terminalCount)) hleft
    · simpa using congrArg
        (fun position =>
          (.inl position : CorridorPort cellWidth terminalCount)) hright
    · exact hconnected
  · exact Or.inr ⟨first, second, rfl, rfl, hcell⟩

/-- Consequently every zero-terminal serial closure embeds in the
terminal-aware closure on crossing ports.  Terminal-aware closure can be
strictly richer, so this theorem is one-way. -/
theorem serialTerminalProfileConnectivityClosure_of_forgetTerminals
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hclosure : Relation.ReflTransGen
      (serialProfileConnectivityStep (forgetTerminals input) cell
        leftIndex pair) first second) :
    Relation.ReflTransGen
      (serialTerminalProfileConnectivityStep input cell leftIndex pair)
      (.inl first) (.inl second) := by
  exact Relation.ReflTransGen.lift
    (fun position =>
      (.inl position : CorridorPort cellWidth terminalCount))
    (fun left right step =>
      serialTerminalProfileConnectivityStep_of_forgetTerminals
        input cell leftIndex pair left right step)
    hclosure

/-- An incoming component is available to the serial closure. -/
theorem serialTerminalProfileConnectivityClosure_of_input
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair)
    (first second : CorridorPort inputWidth terminalCount)
    (hconnected : input.strandConnected pair first second = true) :
    Relation.ReflTransGen
      (serialTerminalProfileConnectivityStep input cell leftIndex pair)
      (serialTerminalInputPort leftIndex first)
      (serialTerminalInputPort leftIndex second) := by
  exact Relation.ReflTransGen.single
    (serialTerminalProfileConnectivityStep_of_input input cell leftIndex pair
      first second hconnected)

/-- A Cell component is likewise available to the serial closure. -/
theorem serialTerminalProfileConnectivityClosure_of_cell
    {inputWidth cellWidth terminalCount inputFragmentCount
      cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hconnected :
      cell.strandConnected pair (.inl first) (.inl second) = true) :
    Relation.ReflTransGen
      (serialTerminalProfileConnectivityStep input cell leftIndex pair)
      (.inl first) (.inl second) := by
  exact Relation.ReflTransGen.single
    (serialTerminalProfileConnectivityStep_of_cell input cell leftIndex pair
      first second hconnected)

/-- Fixed-terminal diagonal guards are preserved exactly.  This is the
finite-state statement that serial closure neither loses nor invents a
terminal's tracked color. -/
theorem SerialTerminalProfileConnectivity.terminalDiagonal_iff
    {inputWidth outputWidth cellWidth terminalCount : Nat}
    {inputFragmentCount cellFragmentCount outputFragmentCount : Nat}
    {input : CorridorCutProfile inputWidth terminalCount inputFragmentCount}
    {cell : CorridorCutProfile cellWidth 0 cellFragmentCount}
    {output : CorridorCutProfile outputWidth terminalCount outputFragmentCount}
    {leftIndex : Fin inputWidth → Fin cellWidth}
    {rightIndex : Fin outputWidth → Fin cellWidth}
    (serial : SerialTerminalProfileConnectivity input cell output
      leftIndex rightIndex)
    (pair : TrackedColorPair) (terminal : Fin terminalCount) :
    output.strandConnected pair (.inr terminal) (.inr terminal) = true ↔
      input.strandConnected pair (.inr terminal) (.inr terminal) = true := by
  constructor
  · intro houtput
    exact ((serial.strandConnected pair (.inr terminal) (.inr terminal)).1
      houtput).1
  · intro hinput
    apply (serial.strandConnected pair (.inr terminal) (.inr terminal)).2
    exact ⟨hinput, hinput, Relation.ReflTransGen.refl⟩

/-- The terminal-aware serial connectivity proposition is decidable on its
explicit finite carriers. -/
noncomputable instance instDecidableSerialTerminalProfileConnectivity
    {inputWidth outputWidth cellWidth terminalCount : Nat}
    {inputFragmentCount cellFragmentCount outputFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth terminalCount inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (output : CorridorCutProfile outputWidth terminalCount outputFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (rightIndex : Fin outputWidth → Fin cellWidth) :
    Decidable (SerialTerminalProfileConnectivity input cell output
      leftIndex rightIndex) :=
  Classical.propDecidable _

end GoertzelV24CorridorProfileTerminalSerialConnectivity

end Mettapedia.GraphTheory.FourColor
