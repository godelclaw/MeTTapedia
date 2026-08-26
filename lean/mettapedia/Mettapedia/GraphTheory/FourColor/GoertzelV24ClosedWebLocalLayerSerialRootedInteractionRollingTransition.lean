import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter

/-!
# One finite rooted rolling Cell transition

This file assembles the bounded pieces already verified separately: a physical
Cell factor, its boundary-rebase support letter, tracked and facial rolling
factors, and the fixed-slot projection receipt.  Application is a partial
function on the rooted interaction state.  It rejects unsupported Cell/rebase
endpoints and every dependent-cardinality mismatch before constructing the
following rooted state.

The transition is graph-free.  This module deliberately does not yet identify
arbitrary inhabitants of the rolling factors with literal source geometry;
that is the soundness/completeness layer.  It does, however, expose the exact
single executable map which that layer must characterize and which the later
reachable-closure computation will iterate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24CorridorProfile

/-- A complete finite candidate for one rooted Cell--rebase--roll step. -/
structure SourceLocalLayerSerialRootedInteractionRollingCellFactor where
  cellOutput : BoundedCorridorCutProfile 2 0 4
  localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
    cellOutput.faceFragmentCount
  rebaseLetter : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter
  trackedRolling : SourceLocalLayerSerialTrackedRollingFactor
  faceRolling : SourceLocalLayerSerialFaceRollingFactor
  projection : SourceLocalLayerSerialRollingProjectionFactor
    trackedRolling.rebase.targetCount faceRolling.rebase.targetCount
      rebaseLetter.output.faceFragmentCount

noncomputable instance :
    DecidableEq SourceLocalLayerSerialRootedInteractionRollingCellFactor :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialRootedInteractionRollingCellFactorCode :=
  Σ cellOutput : BoundedCorridorCutProfile 2 0 4,
    Σ _localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
        cellOutput.faceFragmentCount,
      Σ rebaseLetter : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter,
        Σ trackedRolling : SourceLocalLayerSerialTrackedRollingFactor,
          Σ faceRolling : SourceLocalLayerSerialFaceRollingFactor,
            SourceLocalLayerSerialRollingProjectionFactor
              trackedRolling.rebase.targetCount faceRolling.rebase.targetCount
                rebaseLetter.output.faceFragmentCount

private def sourceLocalLayerSerialRootedInteractionRollingCellFactorEquiv :
    SourceLocalLayerSerialRootedInteractionRollingCellFactor ≃
      sourceLocalLayerSerialRootedInteractionRollingCellFactorCode where
  toFun factor :=
    ⟨factor.cellOutput, factor.localFactor, factor.rebaseLetter,
      factor.trackedRolling, factor.faceRolling, factor.projection⟩
  invFun data := by
    rcases data with ⟨cellOutput, localFactor, rebaseLetter, trackedRolling,
      faceRolling, projection⟩
    exact {
      cellOutput := cellOutput
      localFactor := localFactor
      rebaseLetter := rebaseLetter
      trackedRolling := trackedRolling
      faceRolling := faceRolling
      projection := projection }
  left_inv factor := by cases factor; rfl
  right_inv data := by
    rcases data with ⟨_, _, _, _, _, _⟩
    rfl

set_option synthInstance.maxSize 512 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialRootedInteractionRollingCellFactorCode

noncomputable instance :
    Fintype SourceLocalLayerSerialRootedInteractionRollingCellFactor :=
  Fintype.ofEquiv _
    sourceLocalLayerSerialRootedInteractionRollingCellFactorEquiv.symm

/-- Endpoint support for the physical Cell and boundary rebase.  Equality of
their shared intermediate profile is a separate conjunct, so no transition
can silently glue unlike boundaries. -/
def SourceLocalLayerSerialRootedInteractionRollingCellFactor.supportsBool
    (factor : SourceLocalLayerSerialRootedInteractionRollingCellFactor)
    (state : SourceLocalLayerSerialRootedInteractionState) : Bool :=
  SourceLocalLayerSerialCellPhysicalSupportsBool
      state.toSourceLocalLayerSerialColoredCumulativeState factor.cellOutput
        factor.localFactor &&
    decide (factor.rebaseLetter.input = factor.cellOutput) &&
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool factor.rebaseLetter

/-- Apply one complete finite candidate.  After the two guarded pre-rebase
updates, one explicit cardinality equality per carrier constructs both its
cumulative target and its following rolling interaction root. -/
noncomputable def
    SourceLocalLayerSerialRootedInteractionRollingCellFactor.successor?
    (factor : SourceLocalLayerSerialRootedInteractionRollingCellFactor)
    (state : SourceLocalLayerSerialRootedInteractionState) :
    Option SourceLocalLayerSerialRootedInteractionState :=
  if factor.supportsBool state then
    (sourceLocalLayerSerialRootedInteractionPreRebaseState? state
      factor.localFactor).bind fun trackedPreRebase =>
    (sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state
      factor.localFactor).bind fun facePreRebase =>
    if htracked : trackedPreRebase.vertexCount =
        factor.trackedRolling.rebase.interactionCount then
      if hface : facePreRebase.vertexCount =
          factor.faceRolling.rebase.interactionCount then
        let trackedTarget := factor.trackedRolling.rebase.targetState
          trackedPreRebase htracked
        let faceTarget := factor.faceRolling.rebase.targetState facePreRebase
          hface
        let nextTrackedInteraction :=
          factor.trackedRolling.nextInteractionState trackedPreRebase htracked
        let nextFaceInteraction :=
          factor.faceRolling.nextInteractionState facePreRebase hface
        some {
          input := factor.rebaseLetter.output
          tracked := factor.projection.trackedState trackedTarget.code
          face := factor.projection.faceState (faceTarget.code ())
          colorCode := factor.projection.colorCode state.colorCode
            factor.localFactor.trackedCellColor
              factor.rebaseLetter.outputCode.tracked
          faceCapSix := faceTarget
          trackedExterior := trackedTarget
          interactionExterior := nextTrackedInteraction
          currentCoordinate := factor.trackedRolling.nextCurrentCoordinate
          faceInteractionExterior := nextFaceInteraction
          faceCurrentCoordinate := factor.faceRolling.nextCurrentCoordinate }
      else none
    else none
  else none

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition

end Mettapedia.GraphTheory.FourColor
