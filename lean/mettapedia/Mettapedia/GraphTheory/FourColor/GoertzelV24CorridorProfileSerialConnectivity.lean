import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

/-!
# Serial composition of finite profile connectivity

The source transfer is relational: an incoming cumulative profile composes
with one combined Cell profile, and the outgoing connectivity is the closure
of component moves supplied by either factor.  The Cell profile is indexed on
all of its left and right crossings at once; connectivity through internal
edges (in particular the shared rung) is therefore retained inside that one
finite state rather than reconstructed from two unrelated boundary profiles.

This file defines only the finite connectivity coordinate of that serial law.
It neither identifies two geometric regions nor asserts determinism.  Face
continuation, fragment incidence, and capped progress remain separate
coordinates of the full five-field relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorProfileSerialConnectivity

open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- One finite component move while adjoining a Cell.  A move either stays
inside a component already recorded by the cumulative input profile, after
embedding its ports into the combined Cell carrier, or stays inside a
component recorded by the combined Cell profile itself. -/
def serialProfileConnectivityStep
    {inputWidth cellWidth inputFragmentCount cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth) : Prop :=
  (∃ left right : Fin inputWidth,
      leftIndex left = first ∧ leftIndex right = second ∧
        input.strandConnected pair (.inl left) (.inl right) = true) ∨
    cell.strandConnected pair (.inl first) (.inl second) = true

/-- The finite connectivity part of serial profile composition.  Boundary
colors agree at the glued input, the output colors are the Cell's right-hand
colors, and every outgoing connectivity bit is the guarded relational closure
of the two factor component relations.

The endpoint guards are load-bearing: reflexive-transitive closure is always
reflexive, whereas an untracked port must have a false diagonal connectivity
entry. -/
structure SerialProfileConnectivity
    {inputWidth outputWidth cellWidth : Nat}
    {inputFragmentCount cellFragmentCount outputFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (output : CorridorCutProfile outputWidth 0 outputFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (rightIndex : Fin outputWidth → Fin cellWidth) : Prop where
  leftColors : ∀ index,
    input.edgeColor index = cell.edgeColor (leftIndex index)
  rightColors : ∀ index,
    output.edgeColor index = cell.edgeColor (rightIndex index)
  strandConnected : ∀ (pair : TrackedColorPair)
      (first second : Fin outputWidth),
    output.strandConnected pair (.inl first) (.inl second) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.edgeColor first).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.edgeColor second).toColor ∧
        Relation.ReflTransGen
          (serialProfileConnectivityStep input cell leftIndex pair)
          (rightIndex first) (rightIndex second)

/-- Every recorded input component gives one step of the finite serial
relation after reindexing into the combined Cell carrier. -/
theorem serialProfileConnectivityStep_of_input
    {inputWidth cellWidth inputFragmentCount cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin inputWidth)
    (hconnected :
      input.strandConnected pair (.inl first) (.inl second) = true) :
    serialProfileConnectivityStep input cell leftIndex pair
      (leftIndex first) (leftIndex second) := by
  exact Or.inl ⟨first, second, rfl, rfl, hconnected⟩

/-- Every component recorded by the combined Cell is directly available to
the finite serial closure. -/
theorem serialProfileConnectivityStep_of_cell
    {inputWidth cellWidth inputFragmentCount cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hconnected :
      cell.strandConnected pair (.inl first) (.inl second) = true) :
    serialProfileConnectivityStep input cell leftIndex pair first second := by
  exact Or.inr hconnected

/-- A Cell connectivity entry is therefore a path in the composed finite
relation. -/
theorem serialProfileConnectivityClosure_of_cell
    {inputWidth cellWidth inputFragmentCount cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin cellWidth)
    (hconnected :
      cell.strandConnected pair (.inl first) (.inl second) = true) :
    Relation.ReflTransGen
      (serialProfileConnectivityStep input cell leftIndex pair)
      first second := by
  exact Relation.ReflTransGen.single
    (serialProfileConnectivityStep_of_cell input cell leftIndex pair
      first second hconnected)

/-- An input connectivity entry is likewise a path after embedding both
endpoints into the combined carrier. -/
theorem serialProfileConnectivityClosure_of_input
    {inputWidth cellWidth inputFragmentCount cellFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (pair : TrackedColorPair) (first second : Fin inputWidth)
    (hconnected :
      input.strandConnected pair (.inl first) (.inl second) = true) :
    Relation.ReflTransGen
      (serialProfileConnectivityStep input cell leftIndex pair)
      (leftIndex first) (leftIndex second) := by
  exact Relation.ReflTransGen.single
    (serialProfileConnectivityStep_of_input input cell leftIndex pair
      first second hconnected)

/-- The finite serial connectivity proposition is classically decidable on
the explicit finite profile carriers.  Concrete generated transfers may
replace this instance by executable reachability without changing the
relation. -/
noncomputable instance instDecidableSerialProfileConnectivity
    {inputWidth outputWidth cellWidth : Nat}
    {inputFragmentCount cellFragmentCount outputFragmentCount : Nat}
    (input : CorridorCutProfile inputWidth 0 inputFragmentCount)
    (cell : CorridorCutProfile cellWidth 0 cellFragmentCount)
    (output : CorridorCutProfile outputWidth 0 outputFragmentCount)
    (leftIndex : Fin inputWidth → Fin cellWidth)
    (rightIndex : Fin outputWidth → Fin cellWidth) :
    Decidable (SerialProfileConnectivity input cell output
      leftIndex rightIndex) :=
  Classical.propDecidable _

end GoertzelV24CorridorProfileSerialConnectivity

end Mettapedia.GraphTheory.FourColor
