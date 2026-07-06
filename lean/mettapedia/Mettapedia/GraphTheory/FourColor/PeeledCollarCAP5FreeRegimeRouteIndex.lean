import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeAttachmentFaceSplitSourceIndex
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeMappedCutObstructionCandidate

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Short public index for the CAP5-free peeled-collar regime route.

The selected-source small-cut lift is the canonical closed-walk foundation
target consumed by the route.  It is equivalent to the mapped-cut avoiding
face-route formulation and feeds the downstream cyclic-connectivity, two-cut,
and S4 salvage interfaces without assuming cyclic five-edge-connectivity as an
input.
-/

/--
Canonical foundation index for the regime route: the two annulus separation
targets plus the selected closed-walk small-cut lift target.
-/
def CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex : Prop :=
  CAP5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex

/--
Proof-facing split-source variant of the public route index.  Its closed-walk
field is the two-half attachment-face source and face-noncrossing upgrade
target; downstream code forgets it to the selected-source small-cut lift index.
-/
def CAP5FreePeeledCollarSplitSourceFoundationTargetIndex : Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget

/--
The selected-source small-cut route index is equivalent to the mapped-cut
avoiding face-route public index.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_mappedCutFoundationTargetIndex :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex ↔
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex := by
  simpa [CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex] using
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_iff_closedWalkSmallCutLiftFoundationTargetIndex.symm

/--
The mapped-cut public index supplies the selected-source small-cut route index.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    hindex

/--
The older face-source public foundation index supplies the selected-source
small-cut route index.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_of_foundationTargetIndex
    hindex

/--
The selected-boundary-arc source public index supplies the selected-source
small-cut route index through the source-data and face-source public
equivalences.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_foundationTargetIndex
    ((cap5FreePeeledCollarFoundationTargetIndex_iff_sourceDataFoundationTargetIndex).2
      (cap5FreePeeledCollarSourceDataFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex
        hindex))

/--
The split-source index forgets to the older public face-source foundation index.
-/
theorem cap5FreePeeledCollarFoundationTargetIndex_of_splitSourceFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarSplitSourceFoundationTargetIndex) :
    CAP5FreePeeledCollarFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hindex.2.2⟩

/--
The split-source index also supplies the selected-source small-cut route index.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_splitSourceFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarSplitSourceFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_foundationTargetIndex
    (cap5FreePeeledCollarFoundationTargetIndex_of_splitSourceFoundationTargetIndex
      hindex)

/--
Compact downstream route target supplied by the selected-source small-cut
foundation index: both annulus separation routes, the mapped-cut closed-walk
route, the closed-walk small-cut route, and the explicit S4 no-escape statement.
-/
def Section92Step4CAP5FreeRegimeRouteIndexTarget : Prop :=
  Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget ∧
    Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget

/--
The selected-source small-cut foundation index supplies the compact route index.
-/
theorem section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex) :
    Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hroutes :=
    cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_routeIndexTargets
      hindex
  exact
    ⟨hroutes.1,
      hroutes.2.1,
      hroutes.2.2.1,
      hroutes.2.2.2,
      cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_regimeDischargedS4SalvageTarget
        hindex⟩

/--
The mapped-cut public index supplies the compact route index.
-/
theorem section92Step4CAP5FreeRegimeRouteIndexTarget_of_mappedCutFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CAP5FreeRegimeRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex)

/--
The older face-source public foundation index supplies the compact route index.
-/
theorem section92Step4CAP5FreeRegimeRouteIndexTarget_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    Section92Step4CAP5FreeRegimeRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_foundationTargetIndex
      hindex)

/--
The selected-boundary-arc source public index supplies the compact regime route
index.
-/
theorem section92Step4CAP5FreeRegimeRouteIndexTarget_of_selectedBoundaryArcSourceFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex) :
    Section92Step4CAP5FreeRegimeRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex
      hindex)

/--
The split-source public index supplies the compact route index.
-/
theorem section92Step4CAP5FreeRegimeRouteIndexTarget_of_splitSourceFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarSplitSourceFoundationTargetIndex) :
    Section92Step4CAP5FreeRegimeRouteIndexTarget :=
  section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
    (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_splitSourceFoundationTargetIndex
      hindex)

end Mettapedia.GraphTheory.FourColor
