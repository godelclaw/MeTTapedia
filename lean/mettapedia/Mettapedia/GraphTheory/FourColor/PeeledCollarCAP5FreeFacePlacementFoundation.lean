import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementOffBoundaryRoute
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeClosedWalkOffBoundaryFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
CAP5-free face-placement foundation interface.

This module promotes the source-level `RegimeFacePlacementFoundationTarget`
to a public CAP5-free closed-walk foundation target.  It is equivalent to the
older face-source foundation interface, and it directly exposes the
off-boundary, local-constancy, separation, small-cut lift, cyclic
five-edge-connectivity, no-cyclic-two-cut, and S4 consequences.
-/

/--
Closed-walk CAP5-free face-placement foundation target for the selected
induced peeled collar.
-/
def CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeFacePlacementFoundationTarget

/--
The older closed-walk face-source foundation target supplies the face-placement
foundation target.
-/
theorem cap5FreeClosedWalkFacePlacementFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeFacePlacementFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation source regime)

/--
The closed-walk face-placement foundation target supplies the older
face-source foundation target.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_of_facePlacementFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeFacePlacementFoundationTarget
      (hfoundation source regime)

/--
The closed-walk face-source and face-placement foundation targets are
equivalent.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_iff_facePlacementFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget :=
  ⟨cap5FreeClosedWalkFacePlacementFoundationTarget_of_faceSourceFoundationTarget,
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_facePlacementFoundationTarget⟩

/--
The closed-walk face-placement foundation target supplies the closed-walk
off-boundary no-crossing foundation target.
-/
theorem cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_facePlacementFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.offBoundaryNoCrossingsToAmbient_of_regimeFacePlacementFoundationTarget
      (hfoundation source regime)

/--
Public CAP5-free foundation index with the closed-walk field stated in the
face-placement language.
-/
def CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget

/--
The older public face-source foundation index supplies the face-placement
public index.
-/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkFacePlacementFoundationTarget_of_faceSourceFoundationTarget
      hindex.2.2⟩

/--
The face-placement public index supplies the older face-source public index.
-/
theorem cap5FreePeeledCollarFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_facePlacementFoundationTarget
      hindex.2.2⟩

/--
The face-source and face-placement public CAP5-free foundation indices are
equivalent.
-/
theorem cap5FreePeeledCollarFoundationTargetIndex_iff_facePlacementFoundationTargetIndex :
    CAP5FreePeeledCollarFoundationTargetIndex ↔
      CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_foundationTargetIndex,
    cap5FreePeeledCollarFoundationTargetIndex_of_facePlacementFoundationTargetIndex⟩

/--
The face-placement public index and the mapped-cut public index are
equivalent presentations of the same CAP5-free foundation checklist.
-/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_iff_mappedCutFoundationTargetIndex :
    CAP5FreePeeledCollarFacePlacementFoundationTargetIndex ↔
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.symm.trans
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_iff_foundationTargetIndex.symm

/--
The mapped-cut public index supplies the face-placement public index.
-/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_foundationTargetIndex
    (cap5FreePeeledCollarFoundationTargetIndex_of_mappedCutFoundationTargetIndex
      hindex)

/--
The face-placement public index supplies the mapped-cut public index.
-/
theorem cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_foundationTargetIndex
    (cap5FreePeeledCollarFoundationTargetIndex_of_facePlacementFoundationTargetIndex
      hindex)

/--
The compact selected-source regime route index and the face-placement public
index are equivalent foundation interfaces.
-/
theorem cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_facePlacementFoundationTargetIndex :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex ↔
      CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_mappedCutFoundationTargetIndex.trans
    cap5FreePeeledCollarFacePlacementFoundationTargetIndex_iff_mappedCutFoundationTargetIndex.symm

/--
The compact selected-source regime route index supplies the face-placement
public index.
-/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_of_regimeRouteFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex) :
    CAP5FreePeeledCollarFacePlacementFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.1
    hindex

/--
The face-placement public index supplies the compact selected-source regime
route index.
-/
theorem
    cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_iff_facePlacementFoundationTargetIndex.2
    hindex

/--
The face-placement public index supplies the off-boundary public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_facePlacementFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_facePlacementFoundationTarget
      hindex.2.2⟩

/--
Closed-walk CAP5-free face-placement route target: the face-placement
foundation theorem supplies the named face-placement target, off-boundary
no-crossing, local constancy, separation, small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeFacePlacementFoundationOffBoundaryRouteIndexTarget :
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
      source.RegimeFacePlacementFoundationTarget ∧
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideLocalConstanciesToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideSeparationsToAmbient
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
Route-index theorem for the closed-walk CAP5-free face-placement foundation
target.
-/
theorem section92Step4ClosedWalkCAP5FreeFacePlacementFoundationOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFacePlacementFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeFacePlacementFoundationOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime
  have hface : source.RegimeFacePlacementFoundationTarget :=
    hfoundation source regime
  have hroute :=
    source.offBoundaryRouteConsequences_of_regimeFacePlacementFoundationTarget
      regime hface
  exact
    ⟨hface,
      hroute.1,
      hroute.2.1,
      hroute.2.2.1,
      hroute.2.2.2.1,
      hroute.2.2.2.2.1,
      hroute.2.2.2.2.2.1,
      hroute.2.2.2.2.2.2⟩

/--
The face-placement public index supplies the face-placement route target, the
off-boundary route target, and the compact CAP5-free regime route index.
-/
theorem cap5FreePeeledCollarFacePlacementFoundationTargetIndex_routeIndexTargets
    (hindex : CAP5FreePeeledCollarFacePlacementFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeFacePlacementFoundationOffBoundaryRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_facePlacementFoundationTargetIndex
      hindex
  have hoffRoutes :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
        hindex.1,
      section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
        hindex.2.1,
      section92Step4ClosedWalkCAP5FreeFacePlacementFoundationOffBoundaryRouteIndexTarget
        hindex.2.2,
      hoffRoutes.2.2.1,
      section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
        (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_facePlacementFoundationTargetIndex
          hindex)⟩

end Mettapedia.GraphTheory.FourColor
