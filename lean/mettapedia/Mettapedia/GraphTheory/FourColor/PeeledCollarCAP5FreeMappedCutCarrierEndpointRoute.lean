import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeCarrierEndpointFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Mapped-cut face-route bridges into the carrier-endpoint route.

The mapped-cut face-route target is the strongest closed-walk face-local
foundation interface currently exposed by the CAP5-free route.  This module
connects it to the newer off-carrier and carrier-endpoint support interfaces,
so downstream users can consume either presentation without re-proving the
route plumbing.
-/

/--
Mapped-cut face routes supply the closed-walk off-carrier mapped-cut-deleted
shared-endpoint connectivity foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
      (hfoundation source regime)

/--
Mapped-cut face routes supply the closed-walk off-carrier walk-consistency
foundation target.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
      (hfoundation source regime)

/--
Mapped-cut face routes supply the closed-walk carrier-endpoint support
foundation target.
-/
theorem
    cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget :=
  cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
The mapped-cut public foundation index supplies the off-carrier
mapped-cut-deleted shared-endpoint public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hindex.2.2⟩

/--
The mapped-cut public foundation index supplies the off-carrier public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hindex.2.2⟩

/--
The mapped-cut public foundation index supplies the carrier-endpoint public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex)

/--
The mapped-cut public foundation index supplies the boundary-support public
index through carrier-endpoint support.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex)

/--
Mapped-cut face routes supply the closed-walk off-carrier mapped-cut route
target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationRouteIndexTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationRouteIndexTarget
    (cap5FreeClosedWalkOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
Mapped-cut face routes supply the closed-walk off-carrier route target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
    (cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
Mapped-cut face routes supply the closed-walk carrier-endpoint route target.
-/
theorem
    section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
    (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
Mapped-cut face routes supply the explicit off-carrier S4 salvage target, with
cyclic five-edge-connectivity obtained through the regime route.
-/
theorem
    section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget :=
  section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget
    (cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
The mapped-cut public foundation index supplies the mapped-cut, off-carrier,
carrier-endpoint, boundary-support, and compact regime route targets.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_carrierEndpointRouteIndexTargets
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hmappedRoutes :=
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_routeIndexTargets
      hindex
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex
  have hoffRoutes :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
      hoffIndex
  have hcarrierIndex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex
  have hcarrierRoutes :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_routeIndexTargets
      hcarrierIndex
  exact
    ⟨hmappedRoutes.1,
      hmappedRoutes.2.1,
      hmappedRoutes.2.2,
      hoffRoutes.2.2.1,
      hcarrierRoutes.2.2.1,
      hcarrierRoutes.2.2.2.1,
      hcarrierRoutes.2.2.2.2⟩

/--
The mapped-cut public foundation index supplies the direct off-carrier
mapped-cut route target together with the older mapped-cut, off-carrier,
carrier-endpoint, boundary-support, and compact regime route targets.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_mappedCutConnectivityCarrierEndpointRouteIndexTargets
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hbase :=
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_carrierEndpointRouteIndexTargets
      hindex
  exact
    ⟨hbase.1,
      hbase.2.1,
      hbase.2.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierMappedCutAvoidingSharedEndpointConnectivityFoundationRouteIndexTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
        hindex.2.2,
      hbase.2.2.2.1,
      hbase.2.2.2.2.1,
      hbase.2.2.2.2.2.1,
      hbase.2.2.2.2.2.2⟩

end Mettapedia.GraphTheory.FourColor
