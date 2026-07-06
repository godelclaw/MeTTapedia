import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeBoundarySupportFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk carrier-endpoint and off-carrier foundation targets for the
CAP5-free peeled-collar regime route.

These targets expose the older annulus-carrier route at the closed-walk
CAP5-free level.  Carrier endpoint support now feeds the boundary-support
route directly, and off-carrier walk consistency feeds both carrier endpoint
support and off-boundary no-crossing.
-/

/--
Closed-walk carrier-endpoint foundation target for the selected induced
peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget

/--
Closed-walk off-carrier walk-consistency foundation target for the selected
induced peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget

/--
Closed-walk off-carrier route-input foundation target for the selected
induced peeled collar embedding.  This is equivalent to the off-carrier
walk-consistency target, but exposes the exact regime-route input record
consumed by the downstream cyclic-connectivity and S4 APIs.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
        (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)

/--
Closed-walk off-carrier component-attachment foundation target for the
selected induced peeled collar embedding: every off-carrier component attaches
on only one side of every small cyclic carrier cut.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierComponentOneSidedAttachmentTarget

/--
Closed-walk off-carrier component-attachment route-input foundation target.
This exposes the exact route-input record below off-carrier walk consistency.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentRouteInputsFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
        (MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs G
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)

/--
Closed-walk off-carrier attachment-carrier connectivity foundation target for
the selected induced peeled collar embedding: attachments of one off-carrier
component are connected in the carrier after deleting the small carrier cut.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget

/--
Closed-walk off-carrier attachment-carrier connectivity route-input
foundation target.  This exposes the exact route-input record one step below
component one-sided attachment.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
        (MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs G
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)

/--
Closed-walk off-carrier cut-avoiding shared-endpoint foundation target for
the selected induced peeled collar embedding: attachments of one off-carrier
component can be joined through shared endpoints while avoiding the small
carrier cut.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget

/--
Closed-walk off-carrier cut-avoiding shared-endpoint route-input foundation
target.  This exposes the exact route-input record one step below
attachment-carrier connectivity.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
        (MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs G
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)

/--
Cut-avoiding shared-endpoint reachability supplies the attachment-carrier
connectivity foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
        (hfoundation source regime)

/--
Cut-avoiding shared-endpoint reachability supplies the component-attachment
foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
        (source.toPlanarBoundaryAnnulusBoundaryData
          |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
            (hfoundation source regime))

/--
Cut-avoiding shared-endpoint reachability supplies off-carrier walk
consistency.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
        (source.toPlanarBoundaryAnnulusBoundaryData
          |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
            (hfoundation source regime))

/--
The cut-avoiding shared-endpoint foundation target supplies its exact
route-input foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget := by
  intro V _ G emb source regime
  exact ⟨
    { regime := regime
      offCarrierCutAvoidingSharedEndpointReachabilities := hfoundation source regime }⟩

/--
The cut-avoiding shared-endpoint route-input target supplies the
cut-avoiding shared-endpoint foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact inputs.offCarrierCutAvoidingSharedEndpointReachabilities

/--
Cut-avoiding shared-endpoint route inputs and cut-avoiding shared-endpoint
targets are equivalent closed-walk foundation presentations.
-/
theorem
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget_iff_cutAvoidingSharedEndpointReachabilityFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget,
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget⟩

/--
Attachment-carrier connectivity supplies the component-attachment foundation
target.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
        (hfoundation source regime)

/--
Attachment-carrier connectivity supplies off-carrier walk consistency.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
        (hfoundation source regime)

/--
The attachment-carrier connectivity foundation target supplies its exact
route-input foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget := by
  intro V _ G emb source regime
  exact ⟨
    { regime := regime
      offCarrierAttachmentCarrierConnectivities := hfoundation source regime }⟩

/--
The attachment-carrier connectivity route-input target supplies the
attachment-carrier connectivity foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTarget_of_attachmentCarrierConnectivityRouteInputsFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact inputs.offCarrierAttachmentCarrierConnectivities

/--
Attachment-carrier route inputs and attachment-carrier connectivity targets
are equivalent closed-walk foundation presentations.
-/
theorem
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget_iff_attachmentCarrierConnectivityFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTarget_of_attachmentCarrierConnectivityRouteInputsFoundationTarget,
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget⟩

/--
Off-carrier walk consistency supplies the component-attachment foundation
target.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget.1
        (hfoundation source regime)

/--
The component-attachment foundation target supplies off-carrier walk
consistency.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_componentAttachmentFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget.2
        (hfoundation source regime)

/--
The component-attachment and off-carrier walk-consistency closed-walk
foundation targets are equivalent presentations of the same obstruction.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_iff_offCarrierWalkConsistencyFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_componentAttachmentFoundationTarget,
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget⟩

/--
The component-attachment foundation target supplies the component-attachment
route-input foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTarget_of_componentAttachmentFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentRouteInputsFoundationTarget := by
  intro V _ G emb source regime
  exact ⟨
    { regime := regime
      offCarrierComponentOneSidedAttachments := hfoundation source regime }⟩

/--
The component-attachment route-input foundation target supplies the
component-attachment foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_componentAttachmentRouteInputsFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentRouteInputsFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact inputs.offCarrierComponentOneSidedAttachments

/--
Component-attachment route inputs and component-attachment targets are
equivalent closed-walk foundation presentations.
-/
theorem
    cap5FreeClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTarget_iff_componentAttachmentFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentRouteInputsFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_componentAttachmentRouteInputsFoundationTarget,
    cap5FreeClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTarget_of_componentAttachmentFoundationTarget⟩

/--
Off-carrier walk consistency supplies the closed-walk route-input foundation
target.
-/
theorem
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget := by
  intro V _ G emb source regime
  exact ⟨
    { regime := regime
      offCarrierWalkConsistencies := hfoundation source regime }⟩

/--
The closed-walk route-input foundation target supplies off-carrier walk
consistency.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact inputs.offCarrierWalkConsistencies

/--
The route-input and off-carrier walk-consistency closed-walk foundation
targets are equivalent presentations of the same planar-normal-form
obligation.
-/
theorem
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_iff_offCarrierWalkConsistencyFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget,
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget⟩

/--
Off-carrier walk consistency supplies the closed-walk carrier-endpoint
foundation target.
-/
theorem
    cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
        (hfoundation source regime)

/--
Carrier-endpoint support supplies the closed-walk boundary-support foundation
target.
-/
theorem
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
        (hfoundation source regime)

/--
Off-carrier walk consistency supplies the closed-walk boundary-support
foundation target.
-/
theorem
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget :=
  cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hfoundation)

/--
Off-carrier walk consistency supplies the closed-walk off-boundary no-crossing
foundation target.
-/
theorem
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
        (hfoundation source regime)

/--
Closed-walk off-boundary no-crossing also supplies off-carrier walk
consistency, via the no-avoiding-walk separation bridge for the induced
boundary carrier.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_of_ambientSideSeparations
        (peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideOffBoundaryNoCrossings
          (hfoundation source regime))

/--
Closed-walk off-carrier walk consistency and off-boundary no-crossing are
equivalent public foundation targets.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_iff_offBoundaryNoCrossingFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget :=
  ⟨cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget⟩

/--
Carrier-endpoint support supplies the selected-source small-cut lift
foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
        (hfoundation source regime)

/--
Off-carrier walk consistency supplies the selected-source small-cut lift
foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget :=
  cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hfoundation)

/--
Public index with the closed-walk carrier-endpoint target as the closed-walk
foundation field.
-/
def CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget

/--
Public index with the closed-walk off-carrier walk-consistency target as the
closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget

/--
Public index with the closed-walk off-carrier route-input target as the
closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget

/--
Public index with the closed-walk off-carrier component-attachment target as
the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget

/--
Public index with the closed-walk off-carrier component-attachment route-input
target as the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentRouteInputsFoundationTarget

/--
Public index with the closed-walk off-carrier attachment-carrier connectivity
target as the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget

/--
Public index with the closed-walk off-carrier attachment-carrier connectivity
route-input target as the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget

/--
Public index with the closed-walk off-carrier cut-avoiding shared-endpoint
target as the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget

/--
Public index with the closed-walk off-carrier cut-avoiding shared-endpoint
route-input target as the closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget

/--
The off-carrier public index supplies the off-carrier route-input public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The off-carrier route-input public index supplies the off-carrier public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget
      hindex.2.2⟩

/--
The off-carrier and route-input public indices are equivalent presentations of
the same closed-walk foundation checklist.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_iff_offCarrierWalkConsistencyFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex⟩

/--
The off-carrier public index supplies the component-attachment public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The component-attachment public index supplies the off-carrier public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_componentAttachmentFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_componentAttachmentFoundationTarget
      hindex.2.2⟩

/--
The component-attachment and off-carrier public indices are equivalent
presentations of the same closed-walk foundation checklist.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_iff_offCarrierWalkConsistencyFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_componentAttachmentFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex⟩

/--
The component-attachment public index supplies the component-attachment
route-input public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex_of_componentAttachmentFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTarget_of_componentAttachmentFoundationTarget
      hindex.2.2⟩

/--
The component-attachment route-input public index supplies the
component-attachment public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_componentAttachmentRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_componentAttachmentRouteInputsFoundationTarget
      hindex.2.2⟩

/--
The component-attachment route-input and component-attachment public indices
are equivalent.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex_iff_componentAttachmentFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_componentAttachmentRouteInputsFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex_of_componentAttachmentFoundationTargetIndex⟩

/--
The attachment-carrier connectivity public index supplies the
component-attachment public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierComponentAttachmentFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
      hindex.2.2⟩

/--
The attachment-carrier connectivity public index supplies the off-carrier
walk-consistency public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
      hindex.2.2⟩

/--
The attachment-carrier connectivity public index supplies its route-input
public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTarget_of_attachmentCarrierConnectivityFoundationTarget
      hindex.2.2⟩

/--
The attachment-carrier connectivity route-input public index supplies the
attachment-carrier connectivity public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_attachmentCarrierConnectivityRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTarget_of_attachmentCarrierConnectivityRouteInputsFoundationTarget
      hindex.2.2⟩

/--
The attachment-carrier route-input and attachment-carrier public indices are
equivalent.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex_iff_attachmentCarrierConnectivityFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_attachmentCarrierConnectivityRouteInputsFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex⟩

/--
The cut-avoiding shared-endpoint public index supplies the
attachment-carrier connectivity public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
      hindex.2.2⟩

/--
The cut-avoiding shared-endpoint public index supplies the
component-attachment public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
      hindex)

/--
The cut-avoiding shared-endpoint public index supplies the off-carrier
walk-consistency public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
      hindex)

/--
The cut-avoiding shared-endpoint public index supplies its route-input public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget_of_cutAvoidingSharedEndpointReachabilityFoundationTarget
      hindex.2.2⟩

/--
The cut-avoiding shared-endpoint route-input public index supplies the
cut-avoiding shared-endpoint public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTarget
      hindex.2.2⟩

/--
The cut-avoiding shared-endpoint route-input and cut-avoiding shared-endpoint
public indices are equivalent.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex_iff_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex⟩

/--
The off-carrier public index supplies the carrier-endpoint public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The carrier-endpoint public index supplies the boundary-support public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
      hindex.2.2⟩

/--
The off-carrier public index supplies the boundary-support public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex)

/--
The off-carrier public index supplies the off-boundary public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The off-boundary public index supplies the off-carrier public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
      hindex.2.2⟩

/--
The off-carrier and off-boundary public indices are equivalent presentations
of the same closed-walk cut-lift foundation checklist.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_iff_offBoundaryNoCrossingFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex⟩

/--
Closed-walk carrier-endpoint route target: carrier endpoint support supplies
boundary support, the selected-source small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Route-index theorem for the closed-walk carrier-endpoint foundation target.
-/
theorem section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hcarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget :=
    hfoundation source regime
  have hsupport :
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
        hcarrier
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
        hcarrier
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hcarrier,
      hsupport,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Closed-walk off-carrier route target: off-carrier walk consistency supplies
carrier endpoint support, boundary support, off-boundary no-crossing, the
selected-source small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget ∧
        source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk off-carrier route-input route target: the planar target returns
the exact route-input record, and that record supplies cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
          (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk off-carrier component-attachment route target: the planar target
states that off-carrier components attach on one side of each small cyclic
carrier cut, and this supplies cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierComponentOneSidedAttachmentTarget ∧
        Nonempty
          (MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk off-carrier attachment-carrier route target: the planar target
states that attachments of one off-carrier component are carrier-connected
after the small cut is removed, and this supplies component one-sidedness,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget ∧
        (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierComponentOneSidedAttachmentTarget ∧
        Nonempty
          (MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk off-carrier cut-avoiding shared-endpoint route target: the planar
target states that same-component off-carrier attachments have cut-avoiding
shared-endpoint reachability, and this supplies attachment-carrier
connectivity, cyclic five-edge-connectivity, no cyclic two-cut, and S4
no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget ∧
        (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget ∧
        Nonempty
          (MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Route-index theorem for the closed-walk off-carrier cut-avoiding
shared-endpoint foundation target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hreach :
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
    hfoundation source regime
  have hconnectivity :
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
        hreach
  let inputs :
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet := {
    regime := regime
    offCarrierCutAvoidingSharedEndpointReachabilities := hreach
  }
  exact
    ⟨hreach,
      hconnectivity,
      ⟨inputs⟩,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Route-index theorem for the closed-walk off-carrier attachment-carrier
connectivity foundation target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierAttachmentCarrierConnectivityFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hconnectivity :
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
    hfoundation source regime
  have hcomponent :
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
        hconnectivity
  let inputs :
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet := {
    regime := regime
    offCarrierAttachmentCarrierConnectivities := hconnectivity
  }
  exact
    ⟨hconnectivity,
      hcomponent,
      ⟨inputs⟩,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Route-index theorem for the closed-walk off-carrier component-attachment
foundation target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierComponentAttachmentFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hcomponent :
      (source.toPlanarBoundaryAnnulusBoundaryData).PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
    hfoundation source regime
  let inputs :
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet := {
    regime := regime
    offCarrierComponentOneSidedAttachments := hcomponent
  }
  exact
    ⟨hcomponent,
      ⟨inputs⟩,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Route-index theorem for the closed-walk off-carrier route-input foundation
target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact
    ⟨⟨inputs⟩,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Route-index theorem for the closed-walk off-carrier foundation target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hoffCarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget :=
    hfoundation source regime
  have hcarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
        hoffCarrier
  have hcarrierRoute :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
      (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
        hfoundation)
      source regime
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
        hoffCarrier
  exact
    ⟨hoffCarrier,
      hcarrier,
      hcarrierRoute.2.1,
      hoffBoundary,
      hcarrierRoute.2.2.1,
      hcarrierRoute.2.2.2.1,
      hcarrierRoute.2.2.2.2.1,
      hcarrierRoute.2.2.2.2.2⟩

/--
Closed-walk S4 salvage target for the carrier-endpoint foundation route.  This
is the downstream statement with cyclic five-edge-connectivity supplied by the
CAP5-free regime route, not assumed.
-/
def Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk S4 salvage target for the off-carrier walk-consistency foundation
route.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
The carrier-endpoint foundation target supplies the explicit closed-walk S4
salvage target.
-/
theorem section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
      hfoundation source regime).2.2.2.2.2

/--
The off-carrier walk-consistency foundation target supplies the explicit
closed-walk S4 salvage target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
      hfoundation source regime).2.2.2.2.2.2.2

/--
The carrier-endpoint public index supplies the carrier-endpoint route target,
the boundary-support route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hboundaryIndex :
      CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
      hindex
  have hboundaryRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_routeIndexTargets
      hboundaryIndex
  exact
    ⟨hboundaryRoutes.1,
      hboundaryRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
        hindex.2.2,
      hboundaryRoutes.2.2.1,
      hboundaryRoutes.2.2.2.2⟩

/--
The off-carrier public index supplies the off-carrier route target, the
carrier-endpoint route target, the off-boundary route target, and the compact
regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hcarrierIndex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex
  have hcarrierRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_routeIndexTargets
      hcarrierIndex
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hcarrierRoutes.1,
      hcarrierRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
        hindex.2.2,
      hcarrierRoutes.2.2.1,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2⟩

/--
The off-carrier route-input public index supplies the route-input target, the
off-carrier route target, the carrier-endpoint route target, the off-boundary
route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hoffRoutes.1,
      hoffRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget
        hindex.2.2,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2.1,
      hoffRoutes.2.2.2.2.1,
      hoffRoutes.2.2.2.2.2⟩

/--
The component-attachment public index supplies the component-attachment route
target, the off-carrier route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_componentAttachmentFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hoffRoutes.1,
      hoffRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget
        hindex.2.2,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2.2.2⟩

/--
The component-attachment route-input public index supplies the
component-attachment route target, the off-carrier route target, and the
compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentRouteInputsFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hcomponentIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_componentAttachmentRouteInputsFoundationTargetIndex
      hindex
  exact
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_routeIndexTargets
      hcomponentIndex

/--
The attachment-carrier connectivity public index supplies the
attachment-carrier route target, the component-attachment route target, the
off-carrier route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hcomponentIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_of_attachmentCarrierConnectivityFoundationTargetIndex
      hindex
  have hcomponentRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffCarrierComponentAttachmentFoundationTargetIndex_routeIndexTargets
      hcomponentIndex
  exact
    ⟨hcomponentRoutes.1,
      hcomponentRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget
        hindex.2.2,
      hcomponentRoutes.2.2.1,
      hcomponentRoutes.2.2.2.1,
      hcomponentRoutes.2.2.2.2⟩

/--
The attachment-carrier connectivity route-input public index supplies the
attachment-carrier route target, the component-attachment route target, the
off-carrier route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityRouteInputsFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hconnectivityIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_attachmentCarrierConnectivityRouteInputsFoundationTargetIndex
      hindex
  exact
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_routeIndexTargets
      hconnectivityIndex

/--
The cut-avoiding shared-endpoint public index supplies the cut-avoiding route
target, the attachment-carrier route target, the component-attachment route
target, the off-carrier route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hconnectivityIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityFoundationTargetIndex
      hindex
  have hconnectivityRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffCarrierAttachmentCarrierConnectivityFoundationTargetIndex_routeIndexTargets
      hconnectivityIndex
  exact
    ⟨hconnectivityRoutes.1,
      hconnectivityRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget
        hindex.2.2,
      hconnectivityRoutes.2.2.1,
      hconnectivityRoutes.2.2.2.1,
      hconnectivityRoutes.2.2.2.2.1,
      hconnectivityRoutes.2.2.2.2.2⟩

/--
The cut-avoiding shared-endpoint route-input public index supplies the
cut-avoiding route target, the attachment-carrier route target, the
component-attachment route target, the off-carrier route target, and the
compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierCutAvoidingSharedEndpointReachabilityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierAttachmentCarrierConnectivityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierComponentAttachmentFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hreachIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex_of_cutAvoidingSharedEndpointReachabilityRouteInputsFoundationTargetIndex
      hindex
  exact
    cap5FreePeeledCollarClosedWalkOffCarrierCutAvoidingSharedEndpointReachabilityFoundationTargetIndex_routeIndexTargets
      hreachIndex

end Mettapedia.GraphTheory.FourColor
