import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeAttachmentFaceSplitSource
import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationSplit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Public index bridge for the CAP5-free attachment-face split-source route.

The attachment-face split-source target is the closed-walk CAP5-free version
of the two geometric halves already named by the face-placement split
foundation layer.  This module records that equivalence and connects the
split-source target back to the older face-source route indices.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The existing two-half face-placement split target supplies the split-source
target used by the selected-boundary-arc route.
-/
theorem
    regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hface : source.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : source.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    source.RegimeAttachmentFaceSplitSourceFoundationTarget :=
  ⟨hface, hnoncross⟩

/-- The split-source target supplies its attachment-face placement half. -/
theorem
    regimeAttachmentFaceSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeAttachmentFaceSourceFoundationTarget :=
  h.1

/-- The split-source target supplies its face-noncrossing upgrade half. -/
theorem
    regimeFaceNoncrossingUpgradeFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeFaceNoncrossingUpgradeFoundationTarget :=
  h.2

/--
The selected-boundary-arc split-source target is equivalent to the existing
two-half face-placement split interface.
-/
theorem regimeAttachmentFaceSplitSourceFoundationTarget_iff_facePlacementSplitFoundationTargets
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeAttachmentFaceSplitSourceFoundationTarget ↔
      source.RegimeAttachmentFaceSourceFoundationTarget ∧
        source.RegimeFaceNoncrossingUpgradeFoundationTarget :=
  ⟨fun h =>
      ⟨source.regimeAttachmentFaceSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
          h,
        source.regimeFaceNoncrossingUpgradeFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
          h⟩,
    fun h =>
      source.regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
        h.1 h.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk CAP5-free face-placement split target using the earlier two-half
foundation names.
-/
def CAP5FreeClosedWalkPeeledCollarFacePlacementSplitFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeAttachmentFaceSourceFoundationTarget ∧
        source.RegimeFaceNoncrossingUpgradeFoundationTarget

/--
The earlier two-half face-placement split target supplies the CAP5-free
attachment-face split-source target.
-/
theorem cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_facePlacementSplitFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFacePlacementSplitFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      (hfoundation source regime).1 (hfoundation source regime).2

/--
The attachment-face split-source target supplies the earlier two-half
face-placement split target.
-/
theorem cap5FreeClosedWalkFacePlacementSplitFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFacePlacementSplitFoundationTarget := by
  intro V _ G emb source regime
  exact
    ⟨(hfoundation source regime).1,
      (hfoundation source regime).2⟩

/--
The CAP5-free attachment-face split-source target is exactly the CAP5-free
form of the existing two-half face-placement split target.
-/
theorem
    cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_iff_facePlacementSplitFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarFacePlacementSplitFoundationTarget :=
  ⟨cap5FreeClosedWalkFacePlacementSplitFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget,
    cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_facePlacementSplitFoundationTarget⟩

/--
The split-source target supplies the older CAP5-free face-source foundation
target consumed by the public foundation index.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      (hfoundation source regime)

/--
The split-source target feeds the older closed-walk CAP5-free face-source
route index.
-/
theorem
    section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget
    (cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation)

/--
The split-source target feeds the older canonical aligned CAP5-free
face-source route index.
-/
theorem
    section92Step4CanonicalAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget :=
  section92Step4CanonicalAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget
    (cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation)

/--
The split-source target feeds the older repaired aligned CAP5-free
face-source route index.
-/
theorem
    section92Step4RepairedAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget :=
  section92Step4RepairedAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget
    (cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation)

end Mettapedia.GraphTheory.FourColor
