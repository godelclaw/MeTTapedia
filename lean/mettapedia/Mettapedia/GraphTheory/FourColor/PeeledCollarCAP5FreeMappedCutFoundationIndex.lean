import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeMappedCutFaceRouteFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Public mapped-cut foundation index for the CAP5-free peeled-collar route.

This module packages the same CAP5-free foundation checklist as the older
face-source index, but names the closed-walk obligation in the mapped-cut
face-route language used by the cyclic-connectivity bridge.
-/

/--
Mapped-cut variant of the public CAP5-free peeled-collar foundation index.
The two annulus separation obligations are unchanged; only the closed-walk
face-source obligation is presented as the equivalent mapped-cut face-route
foundation target.
-/
def CAP5FreePeeledCollarMappedCutFoundationTargetIndex : Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget

/-- The older face-source public foundation index supplies the mapped-cut index. -/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  ⟨hindex.1, hindex.2.1,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_faceSourceFoundationTarget
      hindex.2.2⟩

/-- The mapped-cut public foundation index supplies the older face-source index. -/
theorem cap5FreePeeledCollarFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarFoundationTargetIndex :=
  ⟨hindex.1, hindex.2.1,
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hindex.2.2⟩

/--
The mapped-cut public foundation index and the existing face-source public
foundation index are equivalent.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_iff_foundationTargetIndex :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex ↔
      CAP5FreePeeledCollarFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarFoundationTargetIndex_of_mappedCutFoundationTargetIndex,
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_foundationTargetIndex⟩

/--
The mapped-cut public index supplies the selected-boundary-arc source public
index through the face-source and source-data public equivalences.
-/
theorem cap5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex :=
  cap5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex_of_sourceDataFoundationTargetIndex
    ((cap5FreePeeledCollarFoundationTargetIndex_iff_sourceDataFoundationTargetIndex).1
      (cap5FreePeeledCollarFoundationTargetIndex_of_mappedCutFoundationTargetIndex
        hindex))

/--
The selected-boundary-arc source public index supplies the mapped-cut public
index through the source-data and face-source public equivalences.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_foundationTargetIndex
    ((cap5FreePeeledCollarFoundationTargetIndex_iff_sourceDataFoundationTargetIndex).2
      (cap5FreePeeledCollarSourceDataFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex
        hindex))

/--
The mapped-cut public foundation index and the selected-boundary-arc source
public index are equivalent interfaces.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_iff_selectedBoundaryArcSourceFoundationTargetIndex :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex ↔
      CAP5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex_of_mappedCutFoundationTargetIndex,
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_selectedBoundaryArcSourceFoundationTargetIndex⟩

/--
Closed-walk CAP5-free mapped-cut route index: once the mapped-cut foundation
target is proved, the face-source equivalents, small-cut lifting, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape consequences are
available from the shared source interface.
-/
def Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph),
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ∧
        source.RegimeNoncrossingFaceSourceFoundationTarget ∧
        source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        source.RegimeFacePlacementFoundationTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Route-index theorem for the closed-walk CAP5-free mapped-cut target. -/
theorem section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hmapped :
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
    hfoundation source regime
  have hface :
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
    source.regimeNoncrossingFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
      hmapped
  have hconsequences :=
    source.routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
      regime hface
  exact
    ⟨hmapped,
      hface,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2⟩

/--
The mapped-cut public foundation index supplies the three main downstream
route indices.  This is the mapped-cut checklist for the CAP5-free regime
route.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_routeIndexTargets
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  ⟨section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.1,
    section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.2.1,
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
      hindex.2.2⟩

/--
The mapped-cut public foundation index also supplies the aligned canonical and
repaired face-source route indices, via the proved mapped-cut/face-source
equivalence.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_alignedFaceSourceRouteIndexTargets
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget := by
  have hface :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget :=
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hindex.2.2
  exact
    ⟨section92Step4CanonicalAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget
        hface,
      section92Step4RepairedAnnulusCAP5FreeFaceSourceFoundationRouteIndexTarget
        hface⟩

/--
The mapped-cut public foundation index also supplies the aligned
selected-boundary-arc source route indices.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_alignedSelectedBoundaryArcSourceRouteIndexTargets
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget :=
  cap5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex_alignedRouteIndexTargets
    (cap5FreePeeledCollarSelectedBoundaryArcSourceFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex)

end Mettapedia.GraphTheory.FourColor
