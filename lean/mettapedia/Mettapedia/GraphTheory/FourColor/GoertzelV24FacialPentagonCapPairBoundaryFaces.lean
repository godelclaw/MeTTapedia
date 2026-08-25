import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapRetainedConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningBoundary

/-!
# Facial separation for a simultaneous pentagon-cap opening

The one-cap planar-bond argument proves that each ambient facial cycle meets
one cap interface in at most one retained boundary occurrence.  For two caps,
one additional source fact is necessary: no ambient facial cycle may meet both
interfaces.  This file names that exact remote-separation condition and proves
that it combines the two one-cap results into touched-face uniqueness for the
literal simultaneous vertex cut.

The condition is not inferred from graph-level cap separation.  It is the
remaining source-corridor obligation for C-4; this module is a conditional
consumer, not its construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairBoundaryFaces

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapRetainedConnectivity
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

/-- The exact remote facial-separation property needed to combine the two
one-cap planar bonds: an ambient face cannot contain retained-to-cap boundary
darts from both named interfaces. -/
def RemoteBoundaryFacesSeparated
    (data : Data G) (caps : OrientedFacialPentagonCapPair data) : Prop :=
  ∀ inner outer : Fin 5,
    ¬ data.toRotationSystem.phi.SameCycle
      (caps.toFacialPentagonCapPair.toPentagonCapPair.innerBoundaryDart inner)
      (caps.toFacialPentagonCapPair.toPentagonCapPair.outerBoundaryDart outer)

namespace OrientedFacialPentagonCapPair

variable {data : Data G}

/-- Regard one retained boundary dart of the simultaneous vertex cut as the
corresponding manuscript-side boundary port. -/
def boundaryPortOfBoundaryDart
    (caps : OrientedFacialPentagonCapPair data)
    (boundary : BoundaryDart data.toRotationSystem
      (deletedRegionKeep
        caps.toFacialPentagonCapPair.toPentagonCapPair.deletedVertexSupport)) :
    DeletedRegionBoundaryPort G
      caps.toFacialPentagonCapPair.toPentagonCapPair.deletedVertexSupport where
  dart := boundary.1.1
  retained := by
    simpa [deletedRegionKeep] using boundary.1.2
  removed := by
    simpa [deletedRegionKeep,
      SimpleGraphDartRotation.Data.toRotationSystem_alpha] using boundary.2

/-- Every retained boundary occurrence of the simultaneous cut is one of the
two named five-spoke families, at the level of its ambient dart. -/
theorem boundaryDart_eq_inner_or_outer
    (caps : OrientedFacialPentagonCapPair data)
    (boundary : BoundaryDart data.toRotationSystem
      (deletedRegionKeep
        caps.toFacialPentagonCapPair.toPentagonCapPair.deletedVertexSupport)) :
    (∃ step : Fin 5, boundary.1.1 =
        caps.toFacialPentagonCapPair.toPentagonCapPair.innerBoundaryDart step) ∨
      ∃ step : Fin 5, boundary.1.1 =
        caps.toFacialPentagonCapPair.toPentagonCapPair.outerBoundaryDart step := by
  let pair := caps.toFacialPentagonCapPair.toPentagonCapPair
  rcases pair.boundaryPort_eq_inner_or_outer
      (boundaryPortOfBoundaryDart caps boundary) with hinner | houter
  · rcases hinner with ⟨step, hstep⟩
    left
    refine ⟨step, ?_⟩
    exact congrArg DeletedRegionBoundaryPort.dart hstep
  · rcases houter with ⟨step, hstep⟩
    right
    refine ⟨step, ?_⟩
    exact congrArg DeletedRegionBoundaryPort.dart hstep

/-- Under the explicitly named remote facial-separation condition, the two
one-cap planar bonds assemble into touched-face uniqueness for the literal
simultaneous two-cap vertex cut.  This theorem consumes, but does not construct,
the source corridor's remote separation. -/
theorem cutFacesHaveUniqueRetainedBoundaryDart_of_remoteBoundaryFacesSeparated
    (caps : OrientedFacialPentagonCapPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data caps) :
    CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem
      caps.toFacialPentagonCapPair.toPentagonCapPair.deletedVertexSupport := by
  let pair := caps.toFacialPentagonCapPair.toPentagonCapPair
  have hinner :=
    GoertzelV24FacialPentagonCapRetainedConnectivity.PentagonCap.cutFacesHaveUniqueRetainedBoundaryDart_of_vertexMinimalTaitCounterexample
      data minimal caps.innerOriented
  have houter :=
    GoertzelV24FacialPentagonCapRetainedConnectivity.PentagonCap.cutFacesHaveUniqueRetainedBoundaryDart_of_vertexMinimalTaitCounterexample
      data minimal caps.outerOriented
  intro left right hface
  rcases boundaryDart_eq_inner_or_outer caps left with
      ⟨leftStep, hleft⟩ | ⟨leftStep, hleft⟩ <;>
    rcases boundaryDart_eq_inner_or_outer caps right with
      ⟨rightStep, hright⟩ | ⟨rightStep, hright⟩
  · let leftOne :=
      GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
        data pair.inner leftStep
    let rightOne :=
      GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
        data pair.inner rightStep
    have hleftOne : left.1.1 = leftOne.1.1 := by
      apply hleft.trans
      apply SimpleGraph.Dart.ext
      rfl
    have hrightOne : right.1.1 = rightOne.1.1 := by
      apply hright.trans
      apply SimpleGraph.Dart.ext
      rfl
    have honeFace : data.toRotationSystem.phi.SameCycle leftOne.1.1 rightOne.1.1 := by
      rw [← hleftOne, ← hrightOne]
      exact hface
    have honeEq : leftOne = rightOne := hinner leftOne rightOne honeFace
    apply Subtype.ext
    apply Subtype.ext
    exact hleftOne.trans
      ((congrArg (fun dart => dart.1.1) honeEq).trans hrightOne.symm)
  · exfalso
    apply hremote leftStep rightStep
    rw [← hleft, ← hright]
    exact hface
  · exfalso
    apply hremote rightStep leftStep
    rw [← hright, ← hleft]
    exact hface.symm
  · let leftOne :=
      GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
        data pair.outer leftStep
    let rightOne :=
      GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
        data pair.outer rightStep
    have hleftOne : left.1.1 = leftOne.1.1 := by
      apply hleft.trans
      apply SimpleGraph.Dart.ext
      rfl
    have hrightOne : right.1.1 = rightOne.1.1 := by
      apply hright.trans
      apply SimpleGraph.Dart.ext
      rfl
    have honeFace : data.toRotationSystem.phi.SameCycle leftOne.1.1 rightOne.1.1 := by
      rw [← hleftOne, ← hrightOne]
      exact hface
    have honeEq : leftOne = rightOne := houter leftOne rightOne honeFace
    apply Subtype.ext
    apply Subtype.ext
    exact hleftOne.trans
      ((congrArg (fun dart => dart.1.1) honeEq).trans hrightOne.symm)

end OrientedFacialPentagonCapPair

end

end GoertzelV24FacialPentagonCapPairBoundaryFaces

end Mettapedia.GraphTheory.FourColor
