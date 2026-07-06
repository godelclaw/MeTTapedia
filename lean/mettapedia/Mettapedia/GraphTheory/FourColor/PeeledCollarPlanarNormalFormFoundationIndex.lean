import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeFacePlacementFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Planar-normal-form foundation index for the CAP5-free peeled-collar route.

This module names the remaining foundation theorem target without adding it
as an assumed field of the minimal-counterexample regime.  The target is the
statement that the planar/CAP5-free normal form supplies the public
face-placement foundation checklist.  Once that target is proved from the
rotation-system, face-incidence, and CAP5-free infrastructure, the existing
route immediately yields small-cut lifting, inherited cyclic
five-edge-connectivity, no realized cyclic two-cut, and the S4 no-escape
conclusion.
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

end Mettapedia.GraphTheory.FourColor
