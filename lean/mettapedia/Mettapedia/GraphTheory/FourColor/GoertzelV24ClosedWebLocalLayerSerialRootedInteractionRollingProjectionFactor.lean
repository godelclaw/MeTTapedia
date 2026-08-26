import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport

/-!
# Finite projection receipt for a rolling rooted Cell transition

The tracked and facial rolling recurrences retain their actual target-carrier
sizes.  The cumulative state has fixed twenty-one-edge and twenty-four-dart
slot carriers, while its colour table has a fixed twenty-one-edge carrier.
This file packages exactly the finite coordinate receipts that cross those
three representation seams.

No graph, path, face orbit, or precomputed successor state occurs in the
receipt.  Its indices are the target sizes and output-fragment count already
carried by the rolling and boundary-rebase factors.  Consequently the receipt
is finite and can be enumerated as part of the eventual transition alphabet.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor

open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection
open GoertzelV24CorridorProfile

/-- All fixed-slot projection data needed after the two rolling target
contractions. -/
structure SourceLocalLayerSerialRollingProjectionFactor
    (trackedTargetCount : Fin 22)
    (faceTargetCount : Fin 25)
    (outputCount : Fin 5) where
  trackedSlot : Fin 21 → Option (Fin trackedTargetCount.val)
  trackedPortCoordinate : CorridorPort 2 1 → Fin trackedTargetCount.val
  faceSlot : Fin 24 → Option (Fin faceTargetCount.val)
  facePortCoordinate : Fin outputCount.val → Fin faceTargetCount.val
  colorSourceAt : Fin 21 → Option SourceLocalLayerSerialCellRebaseCarrierSource

noncomputable instance (trackedTargetCount : Fin 22)
    (faceTargetCount : Fin 25) (outputCount : Fin 5) :
    DecidableEq (SourceLocalLayerSerialRollingProjectionFactor
      trackedTargetCount faceTargetCount outputCount) :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialRollingProjectionFactorCode
    (trackedTargetCount : Fin 22)
    (faceTargetCount : Fin 25)
    (outputCount : Fin 5) :=
  (Fin 21 → Option (Fin trackedTargetCount.val)) ×
    (CorridorPort 2 1 → Fin trackedTargetCount.val) ×
    (Fin 24 → Option (Fin faceTargetCount.val)) ×
    (Fin outputCount.val → Fin faceTargetCount.val) ×
    (Fin 21 → Option SourceLocalLayerSerialCellRebaseCarrierSource)

private def sourceLocalLayerSerialRollingProjectionFactorEquiv
    (trackedTargetCount : Fin 22)
    (faceTargetCount : Fin 25)
    (outputCount : Fin 5) :
    SourceLocalLayerSerialRollingProjectionFactor trackedTargetCount
        faceTargetCount outputCount ≃
      sourceLocalLayerSerialRollingProjectionFactorCode trackedTargetCount
        faceTargetCount outputCount where
  toFun factor :=
    ⟨factor.trackedSlot, factor.trackedPortCoordinate, factor.faceSlot,
      factor.facePortCoordinate, factor.colorSourceAt⟩
  invFun data := {
    trackedSlot := data.1
    trackedPortCoordinate := data.2.1
    faceSlot := data.2.2.1
    facePortCoordinate := data.2.2.2.1
    colorSourceAt := data.2.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv data := by rcases data with ⟨_, _, _, _, _⟩; rfl

deriving noncomputable instance Fintype for
  sourceLocalLayerSerialRollingProjectionFactorCode

noncomputable instance (trackedTargetCount : Fin 22)
    (faceTargetCount : Fin 25) (outputCount : Fin 5) :
    Fintype (SourceLocalLayerSerialRollingProjectionFactor trackedTargetCount
      faceTargetCount outputCount) :=
  Fintype.ofEquiv _
    (sourceLocalLayerSerialRollingProjectionFactorEquiv trackedTargetCount
      faceTargetCount outputCount).symm

/-- Project the tracked target code through this receipt. -/
noncomputable def SourceLocalLayerSerialRollingProjectionFactor.trackedState
    {trackedTargetCount : Fin 22} {faceTargetCount : Fin 25}
    {outputCount : Fin 5}
    (factor : SourceLocalLayerSerialRollingProjectionFactor trackedTargetCount
      faceTargetCount outputCount)
    (code : TrackedColorPair →
      GoertzelV24InterfaceDeletionComponentFactor.BoundedInterfaceExteriorCode
        (Fin trackedTargetCount.val)) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  trackedCumulativeStateOfCode code factor.trackedSlot
    factor.trackedPortCoordinate

/-- Project the cap-six facial target code through this receipt. -/
noncomputable def SourceLocalLayerSerialRollingProjectionFactor.faceState
    {trackedTargetCount : Fin 22} {faceTargetCount : Fin 25}
    {outputCount : Fin 5}
    (factor : SourceLocalLayerSerialRollingProjectionFactor trackedTargetCount
      faceTargetCount outputCount)
    (code : GoertzelV24InterfaceExteriorLabelCapFactor.BoundedInterfaceExteriorLabelCapCode
      (Fin faceTargetCount.val) (Fin faceTargetCount.val × Bool) 6) :
    SourceLocalLayerSerialFacePrefixAttachmentState :=
  facialCumulativeStateOfCode code factor.faceSlot outputCount
    factor.facePortCoordinate

/-- Transport the finite post-Cell colour table through this receipt and the
literal boundary-rebase role state. -/
def SourceLocalLayerSerialRollingProjectionFactor.colorCode
    {trackedTargetCount : Fin 22} {faceTargetCount : Fin 25}
    {outputCount : Fin 5}
    (factor : SourceLocalLayerSerialRollingProjectionFactor trackedTargetCount
      faceTargetCount outputCount)
    (oldColor cellColor : SourceLocalLayerSerialCarrierColorCode)
    (rebaseState : SourceLocalLayerBoundaryRebaseTrackedState) :
    SourceLocalLayerSerialCarrierColorCode :=
  SourceLocalLayerSerialCellRebaseTransportedColorCode factor.colorSourceAt
    (SourceLocalLayerSerialFiniteSplicedColor oldColor cellColor) rebaseState

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor

end Mettapedia.GraphTheory.FourColor
