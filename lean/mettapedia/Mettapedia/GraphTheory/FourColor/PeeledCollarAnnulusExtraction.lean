import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundaryCarrierWalkExtension
import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftLocalConstancy
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
Named annulus-extraction foundation target for the peeled-collar regime route.
The current annulus API supplies face layers and boundary edge sets; the still
missing extraction theorem must turn that geometry, together with an embedded
collar graph, into the equivalent local/off-boundary side condition for every
small cyclic collar cut.

This definition is deliberately a target, not a theorem from annulus geometry.
-/
def PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusCollarGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ

/--
Equivalent separation-form annulus-extraction target.  This is the preferred
foundation statement for the remaining planar step: every small cyclic collar
cut separates the two collar sides in the ambient graph after deleting the
mapped cut.
-/
def PlanarBoundaryAnnulusPeeledCollarSeparationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusCollarGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideSeparationsToAmbient φ

/--
The repaired previous-boundary annulus geometry uses the same extraction
target, but keeps the stronger geometry package in the statement for callers
that have already discharged the witness-placement seam.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ

/--
Equivalent separation-form target for the repaired previous-boundary annulus
geometry.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideSeparationsToAmbient φ

/--
Canonical annulus off-carrier component target.  This is the most direct
graph-facing form of the remaining planar foundation theorem: no off-carrier
component joins opposite sides of any small cyclic cut in the canonical
endpoint-support carrier.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget

/--
Canonical annulus off-carrier component-attachment target.  This is the
component-facing version of the remaining planar foundation theorem: each
off-carrier component attaches to at most one side of any small cyclic cut in
the canonical endpoint-support carrier.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget

/--
Canonical annulus attachment-carrier-connectivity target.  This asks for a
carrier walk avoiding the small cut between any two carrier vertices attached
to the same off-carrier component.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget

/--
Canonical annulus cut-avoiding shared-endpoint reachability target.  This is
the planar-facing boundary-route obligation that implies attachment-carrier
connectivity.
-/
def
    PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget

/--
Canonical annulus mapped-cut-deleted shared-endpoint connectivity target.
This is the most concrete boundary-route obligation currently exposed for the
remaining planar annulus theorem.
-/
def
    PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget

/--
Canonical annulus attachment-face noncrossing route target.  This is the
face-local normal-form obligation that supplies mapped-cut-deleted
shared-endpoint connectivity for off-carrier component attachments.
-/
def
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget

/--
Canonical annulus noncrossing selected-boundary arc source target.  This is
the face-local normal-form source obligation before deriving face-supported
walks.
-/
def
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget

/--
Repaired previous-boundary annulus variant of the no-opposite-side off-carrier
component target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget

/--
Repaired previous-boundary annulus variant of the off-carrier
component-attachment target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget

/--
Repaired previous-boundary annulus variant of the
attachment-carrier-connectivity target.
-/
def
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget

/--
Repaired previous-boundary annulus variant of the cut-avoiding shared-endpoint
reachability target.
-/
def
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget

/--
Repaired previous-boundary annulus variant of the mapped-cut-deleted
shared-endpoint connectivity target.
-/
def
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget

/--
Repaired previous-boundary annulus variant of the attachment-face noncrossing
route target.
-/
def
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget

/--
Repaired previous-boundary annulus variant of the noncrossing
selected-boundary arc source target.
-/
def
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget

/-- The annulus-extraction target is exactly the local-constancy bridge input. -/
theorem peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
  h

/-- Annulus separation extraction supplies local constancy. -/
theorem planarBoundaryAnnulusPeeledCollarLocalConstancyTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget data φ) :
    PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ :=
  peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideSeparations h

/-- Annulus local constancy supplies the equivalent separation target. -/
theorem planarBoundaryAnnulusPeeledCollarSeparationTarget_of_localConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget data φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_localConstancies h

/-- The annulus extraction target can be stated as local constancy or as
no-avoiding-walk side separation. -/
theorem planarBoundaryAnnulusPeeledCollarLocalConstancyTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G} :
    PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ ↔
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget data φ :=
  peeledCollarCutAmbientSideLocalConstanciesToAmbient_iff_ambientSideSeparations

/--
Canonical annulus off-carrier walk consistency supplies the named
separation-form extraction target for the canonical induced peeled collar.
-/
theorem planarBoundaryAnnulusPeeledCollarSeparationTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  data.peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
    h

/--
The named separation-form extraction target supplies canonical annulus
off-carrier walk consistency.
-/
theorem planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_ambientSideSeparations h

/--
The named canonical annulus separation target is equivalent to off-carrier
walk consistency.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  data.offCarrierWalkConsistencyTarget_iff_ambientSideSeparations

/--
The canonical annulus no-opposite-side off-carrier target supplies
off-carrier walk consistency.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget h

/--
Canonical annulus off-carrier walk consistency supplies the no-opposite-side
off-carrier target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data :=
  data.oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget h

/--
The canonical annulus no-opposite-side target supplies the component-facing
attachment target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget data :=
  data.componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget h

/--
The canonical annulus component-facing attachment target supplies the
no-opposite-side off-carrier target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data :=
  data.oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget h

/--
The canonical annulus attachment-carrier-connectivity target supplies the
component-facing attachment target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
      data :=
  data.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget h

/--
The canonical annulus attachment-carrier-connectivity target supplies
off-carrier walk consistency.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget h

/--
The canonical annulus cut-avoiding shared-endpoint target supplies the
attachment-carrier-connectivity target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
      data :=
  data.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget h

/--
The canonical annulus mapped-cut-deleted shared-endpoint connectivity target
supplies cut-avoiding shared-endpoint reachability.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
      data :=
  data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    h

/--
The canonical annulus cut-avoiding shared-endpoint target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    h

/--
The canonical annulus attachment-face noncrossing route target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_attachmentFaceNoncrossingRouteTarget
    h

/--
The canonical annulus noncrossing selected-boundary arc source target supplies
the attachment-face noncrossing route target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
      data :=
  data.attachmentFaceNoncrossingRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
The canonical annulus noncrossing selected-boundary arc source target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
The canonical annulus cut-avoiding shared-endpoint and mapped-cut-deleted
shared-endpoint targets are equivalent.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data ↔
      PlanarBoundaryAnnulusPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
        data :=
  data.cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget

/--
The canonical annulus off-carrier target can be stated either as walk
consistency or as no opposite-side off-carrier component.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_iff_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data :=
  data.offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget

/--
The canonical annulus off-carrier target can be stated either as
no-opposite-side components or as one-sided component attachments.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_iff_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data ↔
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data :=
  data.oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget

/--
The canonical annulus off-carrier target can be stated either as walk
consistency or as one-sided component attachments.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_iff_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data :=
  data.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget

/--
The canonical annulus no-opposite-side off-carrier target supplies the
separation-form extraction target.
-/
theorem planarBoundaryAnnulusPeeledCollarSeparationTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryAnnulusPeeledCollarSeparationTarget_of_offCarrierWalkConsistencyTarget
    (planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
      h)

/--
The canonical annulus separation-form extraction target supplies the
no-opposite-side off-carrier target.
-/
theorem planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data :=
  planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_offCarrierWalkConsistencyTarget
    (planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      h)

/--
The canonical annulus component-facing attachment target supplies the
separation-form extraction target.
-/
theorem planarBoundaryAnnulusPeeledCollarSeparationTarget_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryAnnulusPeeledCollarSeparationTarget_of_oppositeSideTarget
    (planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
      h)

/--
The canonical annulus attachment-carrier-connectivity target supplies the
separation-form extraction target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarSeparationTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryAnnulusPeeledCollarSeparationTarget_of_componentAttachmentTarget
    (planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
      h)

/--
The canonical annulus separation-form extraction target supplies the
component-facing attachment target.
-/
theorem planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
      data :=
  planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_oppositeSideTarget
    (planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget
      h)

/--
The canonical annulus extraction target can equivalently be stated as
no-avoiding-walk side separation or as no off-carrier component joining
opposite carrier sides.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data ↔
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  ⟨planarBoundaryAnnulusPeeledCollarSeparationTarget_of_oppositeSideTarget,
    planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget⟩

/--
The canonical annulus extraction target can equivalently be stated as
no-avoiding-walk side separation or as one-sided off-carrier component
attachments.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data ↔
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  ⟨planarBoundaryAnnulusPeeledCollarSeparationTarget_of_componentAttachmentTarget,
    planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_separationTarget⟩

/-- The previous-boundary annulus-extraction target is exactly the local-constancy bridge input. -/
theorem
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
  h

/-- Previous-boundary annulus separation extraction supplies local constancy. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget data φ) :
    PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ :=
  peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideSeparations h

/-- Previous-boundary annulus local constancy supplies the equivalent
separation target. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_localConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget data φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_localConstancies h

/-- The previous-boundary extraction target can be stated as local constancy or
as no-avoiding-walk side separation. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G} :
    PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget data φ :=
  peeledCollarCutAmbientSideLocalConstanciesToAmbient_iff_ambientSideSeparations

/--
Repaired annulus off-carrier walk consistency supplies the named
previous-boundary separation-form extraction target for the canonical induced
peeled collar.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  data.peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
    h

/--
The named previous-boundary separation-form extraction target supplies
repaired annulus off-carrier walk consistency.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_ambientSideSeparations h

/--
The named repaired annulus separation target is equivalent to off-carrier walk
consistency.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  data.offCarrierWalkConsistencyTarget_iff_ambientSideSeparations

/--
The repaired annulus no-opposite-side off-carrier target supplies off-carrier
walk consistency.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget h

/--
Repaired annulus off-carrier walk consistency supplies the no-opposite-side
off-carrier target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
      data :=
  data.oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget h

/--
The repaired annulus no-opposite-side target supplies the component-facing
attachment target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
      data :=
  data.componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget h

/--
The repaired annulus component-facing attachment target supplies the
no-opposite-side off-carrier target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
      data :=
  data.oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget h

/--
The repaired annulus attachment-carrier-connectivity target supplies the
component-facing attachment target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
      data :=
  data.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget h

/--
The repaired annulus attachment-carrier-connectivity target supplies
off-carrier walk consistency.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget h

/--
The repaired annulus cut-avoiding shared-endpoint target supplies the
attachment-carrier-connectivity target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
      data :=
  data.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget h

/--
The repaired annulus mapped-cut-deleted shared-endpoint connectivity target
supplies cut-avoiding shared-endpoint reachability.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
      data :=
  data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    h

/--
The repaired annulus cut-avoiding shared-endpoint target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    h

/--
The repaired annulus attachment-face noncrossing route target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_attachmentFaceNoncrossingRouteTarget
    h

/--
The repaired annulus noncrossing selected-boundary arc source target supplies
the attachment-face noncrossing route target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
      data :=
  data.attachmentFaceNoncrossingRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
The repaired annulus noncrossing selected-boundary arc source target supplies
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
      data :=
  data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
The repaired annulus cut-avoiding shared-endpoint and mapped-cut-deleted
shared-endpoint targets are equivalent.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
        data :=
  data.cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget

/--
The repaired annulus off-carrier target can be stated either as walk
consistency or as no opposite-side off-carrier component.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_iff_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data :=
  data.offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget

/--
The repaired annulus off-carrier target can be stated either as
no-opposite-side components or as one-sided component attachments.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_iff_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data :=
  data.oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget

/--
The repaired annulus off-carrier target can be stated either as walk
consistency or as one-sided component attachments.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_iff_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data :=
  data.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget

/--
The repaired annulus no-opposite-side off-carrier target supplies the
separation-form extraction target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_offCarrierWalkConsistencyTarget
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
      h)

/--
The repaired annulus separation-form extraction target supplies the
no-opposite-side off-carrier target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
      data :=
  planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_offCarrierWalkConsistencyTarget
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      h)

/--
The repaired annulus component-facing attachment target supplies the
separation-form extraction target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_oppositeSideTarget
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
      h)

/--
The repaired annulus attachment-carrier-connectivity target supplies the
separation-form extraction target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding :=
  planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_componentAttachmentTarget
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
      h)

/--
The repaired annulus separation-form extraction target supplies the
component-facing attachment target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
      data :=
  planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_oppositeSideTarget
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget
      h)

/--
The repaired annulus extraction target can equivalently be stated as
no-avoiding-walk side separation or as no off-carrier component joining
opposite carrier sides.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  ⟨planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_oppositeSideTarget,
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_separationTarget⟩

/--
The repaired annulus extraction target can equivalently be stated as
no-avoiding-walk side separation or as one-sided off-carrier component
attachments.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_iff_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
  ⟨planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_componentAttachmentTarget,
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_separationTarget⟩

/-- Annulus extraction supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_annulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget h)

/-- Previous-boundary annulus extraction supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_previousBoundaryAnnulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget h)

/--
Regime-facing inheritance theorem from the named annulus-extraction target.
The ambient minimal-counterexample regime supplies the no-small-cut obstruction;
the annulus extraction target supplies the collar-to-ambient cut lift.
-/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_annulusExtractionTarget
    [DecidableEq W]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_localConstancies
    regime
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget h)

/--
Regime-facing inheritance theorem from the repaired previous-boundary
annulus-extraction target.
-/
theorem
    peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_previousBoundaryAnnulusExtractionTarget
    [DecidableEq W]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_localConstancies
    regime
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget h)

end Mettapedia.GraphTheory.FourColor
