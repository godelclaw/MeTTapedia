import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseOldAttachmentSlots
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedSupportedState

/-!
# Stable tracked residual state for a serial boundary rebase

The exact tracked predecessor state was previously indexed by the dependent
type of actual old-attachment roles.  This file transports it to the uniform
six-slot carrier.  Slots without an actual role are inactive and carry no
attachment or residual-component bit; real roles round-trip exactly.

This is a lossless source-image stabilization, not a claim that the successor
state has already been computed.  It provides the fixed tracked-state carrier
on which that recurrence can be stated.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- Pad a supported residual code along a partial decoder.  Missing stable
slots are explicitly inactive rather than interpreted as graph vertices. -/
def padSupportedPortResidualCode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port) :
    BoundedSupportedPortResidualCode Stable Port where
  toBoundedPortResidualCode :=
    { attaches := fun stable port =>
        match decode stable with
        | some interface => code.attaches interface port
        | none => false
      residualConnected := fun left right =>
        match decode left, decode right with
        | some leftInterface, some rightInterface =>
            code.residualConnected leftInterface rightInterface
        | _, _ => false }
  interfaceActive := fun stable =>
    match decode stable with
    | some interface => code.interfaceActive interface
    | none => false
  portActive := code.portActive

@[simp] theorem padSupportedPortResidualCode_attaches_of_decode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (stable : Stable) (interface : Interface) (port : Port)
    (hdecode : decode stable = some interface) :
    (padSupportedPortResidualCode decode code).attaches stable port =
      code.attaches interface port := by
  simp [padSupportedPortResidualCode, hdecode]

@[simp] theorem padSupportedPortResidualCode_residualConnected_of_decode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (left right : Stable) (leftInterface rightInterface : Interface)
    (hleft : decode left = some leftInterface)
    (hright : decode right = some rightInterface) :
    (padSupportedPortResidualCode decode code).residualConnected left right =
      code.residualConnected leftInterface rightInterface := by
  simp [padSupportedPortResidualCode, hleft, hright]

@[simp] theorem padSupportedPortResidualCode_interfaceActive_of_decode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (stable : Stable) (interface : Interface)
    (hdecode : decode stable = some interface) :
    (padSupportedPortResidualCode decode code).interfaceActive stable =
      code.interfaceActive interface := by
  simp [padSupportedPortResidualCode, hdecode]

@[simp] theorem padSupportedPortResidualCode_portActive
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (port : Port) :
    (padSupportedPortResidualCode decode code).portActive port =
      code.portActive port :=
  rfl

@[simp] theorem padSupportedPortResidualCode_fields_eq_false_of_decode_none
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (stable : Stable) (hdecode : decode stable = none) :
    (padSupportedPortResidualCode decode code).interfaceActive stable = false ∧
      (∀ port, (padSupportedPortResidualCode decode code).attaches
        stable port = false) ∧
      (∀ other,
        (padSupportedPortResidualCode decode code).residualConnected
          stable other = false ∧
        (padSupportedPortResidualCode decode code).residualConnected
          other stable = false) := by
  simp [padSupportedPortResidualCode, hdecode]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Uniform six-slot tracked predecessor state for all three tracked colour
pairs. -/
abbrev BoundedSerialBoundaryRebaseStableSupportedTrackedCode :=
  TrackedColorPair →
    BoundedSupportedPortResidualCode
      BoundedSerialBoundaryRebaseOldAttachmentSlot (Fin 2)

/-- Transport the exact literal predecessor state onto the stable six-slot
carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) :
    BoundedSerialBoundaryRebaseStableSupportedTrackedCode :=
  fun pair =>
    padSupportedPortResidualCode
      (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset)
      (sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset color pair)

/-- The stable state agrees exactly with the dependent state on every actual
old-attachment role. -/
theorem sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt_role
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    let stable :=
      sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt
        realization hcubic hrotation htwoSided hunique offset color pair
    let dependent :=
      sourceCorridorSerialBoundaryRebaseSupportedTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset color pair
    stable.interfaceActive
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role) =
        dependent.interfaceActive role ∧
      (∀ port, stable.attaches
          (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role) port =
        dependent.attaches role port) ∧
      (∀ other,
        stable.residualConnected
            (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role)
            (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot other) =
          dependent.residualConnected role other) := by
  simp [sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt]

/-- At the first source offset the two predecessor slots are explicitly
inactive in every tracked-colour state. -/
theorem sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt_previous_inactive
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3)) (hoffset : offset.val = 0)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) (step : Fin 2) :
    let stable :=
      sourceCorridorSerialBoundaryRebaseStableSupportedTrackedCodeAt
        realization hcubic hrotation htwoSided hunique offset color pair
    stable.interfaceActive (.inr step) = false ∧
      (∀ port, stable.attaches (.inr step) port = false) ∧
      (∀ other,
        stable.residualConnected (.inr step) other = false ∧
          stable.residualConnected other (.inr step) = false) := by
  apply padSupportedPortResidualCode_fields_eq_false_of_decode_none
  exact
    (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?_previous_eq_none_iff
      offset step).2 hoffset

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
