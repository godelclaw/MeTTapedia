import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFullComponent

/-!
# Project rolling interaction roots to the cumulative state

The rolling tracked and facial recurrences produce exact deletion-stable
codes on the actual following carriers.  The cumulative transfer state uses
fixed padded carriers instead: twenty-one edge slots, twenty-four dart slots,
and four facial-fragment ports.  This file gives the graph-free projections
between those presentations.

The facial projection reads presence and capped full-component size from the
same cap-six interaction code used by the rolling recurrence.  In particular,
it does not re-observe a source graph and it does not infer presence from graph
support.  Coordinate decoders and named port coordinates remain explicit
finite inputs, which is the representation seam used later by the complete
rooted Cell--rebase transition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
open GoertzelV24CorridorProfile
open GoertzelV24FramedTrail
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFullComponent
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24InterfaceDeletionComponentFactor

noncomputable section

local instance interactionIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool => toLex incidence)
    toLex.injective

/-- Project a tracked deletion-stable code onto the fixed cumulative
twenty-one-slot attachment state.  Its carrier size is explicit: no dependent
root record has to be normalized in order to execute the projection. -/
noncomputable def trackedCumulativeStateOfCode
    {n : Nat}
    (code : TrackedColorPair → BoundedInterfaceExteriorCode (Fin n))
    (decode : Fin 21 → Option (Fin n))
    (portCoordinate : CorridorPort 2 1 → Fin n) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  fun pair ↦ projectSupportedPortResidualCode (code pair) decode portCoordinate

/-- Convenience wrapper for a packaged deletion-stable target root. -/
noncomputable def trackedCumulativeStateOfTarget
    (target : SourceLocalLayerSerialTrackedDeletionStablePrefixState)
    (decode : Fin 21 → Option (Fin target.vertexCount.val))
    (portCoordinate : CorridorPort 2 1 → Fin target.vertexCount.val) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  trackedCumulativeStateOfCode target.code decode portCoordinate

/-- Cap-at-five size of the full component through one present coordinate of
a cap-six deletion-stable facial target. -/
noncomputable def facialTargetComponentCap
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (slot : Fin n) : Fin 6 := by
  classical
  exact if code.interfacePresent slot then
    ⟨min (interfaceExteriorLabelCapFullComponent code Prod.fst slot).val 5,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  else 0

/-- Project one cap-six facial code onto the fixed cumulative
twenty-four-slot/four-port state.  Its carrier size is explicit and the
dependent live port carrier is indexed by `outputCount`; padding to four ports
is canonical. -/
noncomputable def facialCumulativeStateOfCode
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n) (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n) :
    SourceLocalLayerSerialFacePrefixAttachmentState := by
  classical
  let hports : Fintype.card (Fin outputCount.val) ≤ 4 := by
    simpa using Nat.le_of_lt_succ outputCount.isLt
  exact {
    toBoundedSupportedPortResidualCode :=
      padSupportedPortResidualCodePorts (boundedFiniteSlot? hports)
        (projectSupportedPortResidualCode code.connectivity decode
          portCoordinate)
    interfacePresent := fun slot ↦
      match decode slot with
      | some targetSlot => code.interfacePresent targetSlot
      | none => false
    componentCap := fun slot ↦
      match decode slot with
      | some targetSlot => facialTargetComponentCap code targetSlot
      | none => 0 }

/-- Convenience wrapper for a packaged cap-six facial target root. -/
noncomputable def facialCumulativeStateOfTarget
    (target : SourceLocalLayerSerialFaceDeletionStableCapSixState)
    (decode : Fin 24 → Option (Fin target.vertexCount.val))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin target.vertexCount.val) :
    SourceLocalLayerSerialFacePrefixAttachmentState :=
  facialCumulativeStateOfCode (target.code ()) decode outputCount portCoordinate

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection

end Mettapedia.GraphTheory.FourColor
