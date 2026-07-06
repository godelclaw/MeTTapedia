import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeFacePlacementFoundation
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeCarrierEndpointFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Planar-normal-form foundation index for the CAP5-free peeled-collar route.

This module names the remaining foundation theorem targets without adding
them as assumed fields of the minimal-counterexample regime.  The stronger
target is the statement that the planar/CAP5-free normal form supplies the
public face-placement foundation checklist.  The smaller cut-lift target is
the closed-walk off-boundary no-crossing checklist: enough to supply the
small-cut lift, inherited cyclic five-edge-connectivity, no realized cyclic
two-cut, and the S4 no-escape conclusion.
-/

/--
Next foundation theorem target for the planar-normal-form regime route.

This is deliberately a standalone theorem target, not a field on
`MinimalCounterexamplePeeledCollarRegime`: proving it is the remaining
planar/dual/CAP5-free work needed upstream of the already verified
connectivity bridge.
-/
def CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex : Prop :=
  CAP5FreePeeledCollarFacePlacementFoundationTargetIndex

/--
The planar-normal-form foundation target is the face-placement public
foundation index, with a name that records where the proof must come from.
-/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_facePlacementFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex ↔
      CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  Iff.rfl

/-- The face-placement index supplies the planar-normal-form target. -/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex :=
  hindex

/-- The planar-normal-form target supplies the face-placement index. -/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex) :
    CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  hindex

/--
The planar-normal-form target and mapped-cut public index are equivalent
interfaces for the same missing upstream theorem.
-/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_mappedCutFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex ↔
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.trans
    cap5FreePeeledCollarFacePlacementFoundationTargetIndex_iff_mappedCutFoundationTargetIndex

/-- The planar-normal-form target supplies the mapped-cut public index. -/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_mappedCutFoundationTargetIndex.1
    hindex

/-- The mapped-cut public index supplies the planar-normal-form target. -/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_mappedCutFoundationTargetIndex.2
    hindex

/--
The planar-normal-form target and the compact selected-source route index are
equivalent foundation interfaces.
-/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_regimeRouteFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex ↔
      CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.trans
    cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.symm

/-- The planar-normal-form target supplies the compact route index. -/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_regimeRouteFoundationTargetIndex.1
    hindex

/-- The compact route index supplies the planar-normal-form target. -/
theorem cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_of_regimeRouteFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormFoundationTargetIndex_iff_regimeRouteFoundationTargetIndex.2
    hindex

/--
Smaller planar-normal-form theorem target for the cyclic-connectivity bridge.

This records the precise cut-lift obligation needed upstream of the S4
salvage: for the two annulus families, keep the existing separation targets;
for the selected closed-walk collar, prove off-boundary no-crossing for each
small cyclic collar cut.  This is weaker than the face-placement checklist but
strong enough to discharge cyclic five-edge-connectivity.
-/
def CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex :
    Prop :=
  CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex

/--
The smaller planar-normal-form cut-lift target is the closed-walk
off-boundary public foundation index.
-/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffBoundaryNoCrossingFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  Iff.rfl

/--
The smaller planar-normal-form cut-lift target can equivalently be supplied in
the closed-walk off-carrier walk-consistency language.
-/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierWalkConsistencyFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffBoundaryNoCrossingFoundationTargetIndex.trans
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_iff_offBoundaryNoCrossingFoundationTargetIndex.symm

/-- The off-carrier public index supplies the smaller planar-normal-form target. -/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_of_closedWalkOffCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierWalkConsistencyFoundationTargetIndex.2
    hindex

/-- The smaller planar-normal-form target supplies the off-carrier public index. -/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierWalkConsistencyFoundationTargetIndex.1
    hindex

/--
The smaller planar-normal-form cut-lift target can also be supplied as the
closed-walk off-carrier route-input public index.
-/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierRouteInputsFoundationTargetIndex :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierWalkConsistencyFoundationTargetIndex.trans
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_iff_offCarrierWalkConsistencyFoundationTargetIndex.symm

/-- The off-carrier route-input public index supplies the smaller target. -/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_of_closedWalkOffCarrierRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierRouteInputsFoundationTargetIndex.2
    hindex

/-- The smaller target supplies the off-carrier route-input public index. -/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_iff_closedWalkOffCarrierRouteInputsFoundationTargetIndex.1
    hindex

/-- The stronger face-placement index supplies the smaller cut-lift target. -/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    hindex

/--
The stronger planar-normal-form face-placement target supplies the smaller
cut-lift target.
-/
theorem
    cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex) :
    CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex :=
  cap5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
      hindex)

/-- The smaller cut-lift target supplies the compact selected-source route index. -/
theorem
    cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_closedWalkOffBoundaryNoCrossingFoundationTargetIndex
    hindex

/--
Route target reached once the planar-normal-form foundation target is proved.
This is the reusable end-to-end CAP5-free/S4 index with cyclic
five-edge-connectivity supplied by the regime route rather than assumed.
-/
def Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget : Prop :=
  Section92Step4CAP5FreeRegimeRouteIndexTarget

/--
The planar-normal-form foundation target supplies the full downstream regime
route index.
-/
theorem section92Step4CAP5FreePlanarNormalFormRouteIndexTarget_of_planarNormalFormFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarPlanarNormalFormFoundationTargetIndex) :
    Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_planarNormalFormFoundationTargetIndex
      hindex)

/--
The smaller planar-normal-form cut-lift target also supplies the full
downstream regime route index.
-/
theorem
    section92Step4CAP5FreePlanarNormalFormRouteIndexTarget_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
      hindex)

/--
Expanded route target reached from the smaller planar-normal-form cut-lift
foundation: both annulus separation routes, the closed-walk off-boundary route,
and the regime-discharged S4 route.
-/
def Section92Step4CAP5FreePlanarNormalFormCutLiftRouteIndexTarget :
    Prop :=
  Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
    Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget

/--
The smaller planar-normal-form cut-lift target supplies the expanded route
index, including the off-boundary/local-constancy/separation/small-cut-lift
closed-walk consequences.
-/
theorem
    section92Step4CAP5FreePlanarNormalFormCutLiftRouteIndexTarget_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    Section92Step4CAP5FreePlanarNormalFormCutLiftRouteIndexTarget := by
  have hroutes :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
      hindex
  exact ⟨hroutes.1, hroutes.2.1, hroutes.2.2.1, hroutes.2.2.2⟩

/--
Expanded off-carrier route target reached from the smaller planar-normal-form
cut-lift foundation: both annulus separation routes, the closed-walk
off-carrier route, and the regime-discharged S4 route.
-/
def Section92Step4CAP5FreePlanarNormalFormOffCarrierCutLiftRouteIndexTarget :
    Prop :=
  Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
    Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget

/--
The smaller planar-normal-form cut-lift target supplies the expanded
off-carrier route index as well.
-/
theorem
    section92Step4CAP5FreePlanarNormalFormOffCarrierCutLiftRouteIndexTarget_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    Section92Step4CAP5FreePlanarNormalFormOffCarrierCutLiftRouteIndexTarget := by
  have hoffCarrierIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
      hindex
  have hroutes :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
      hoffCarrierIndex
  exact ⟨hroutes.1, hroutes.2.1, hroutes.2.2.1, hroutes.2.2.2.2.2⟩

/--
Expanded route-input route target reached from the smaller planar-normal-form
cut-lift foundation: both annulus separation routes, the closed-walk
off-carrier route-input route, and the regime-discharged S4 route.
-/
def Section92Step4CAP5FreePlanarNormalFormOffCarrierRouteInputsCutLiftRouteIndexTarget :
    Prop :=
  Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget ∧
    Section92Step4CAP5FreePlanarNormalFormRouteIndexTarget

/--
The smaller planar-normal-form cut-lift target supplies the expanded
off-carrier route-input route index as well.
-/
theorem
    section92Step4CAP5FreePlanarNormalFormOffCarrierRouteInputsCutLiftRouteIndexTarget_of_planarNormalFormCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarPlanarNormalFormCutLiftFoundationTargetIndex) :
    Section92Step4CAP5FreePlanarNormalFormOffCarrierRouteInputsCutLiftRouteIndexTarget := by
  have hrouteInputsIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_planarNormalFormCutLiftFoundationTargetIndex
      hindex
  have hroutes :=
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_routeIndexTargets
      hrouteInputsIndex
  exact ⟨hroutes.1, hroutes.2.1, hroutes.2.2.1, hroutes.2.2.2.2.2.2⟩

end Mettapedia.GraphTheory.FourColor
