import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeClosedWalkOffBoundaryFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk boundary-support foundation target for the CAP5-free peeled-collar
regime route.

This is the boundary-facing form of the remaining planar foundation theorem:
for every small cyclic cut in the selected closed-walk collar, the filled
ambient side has every side-crossing endpoint on the mapped collar-cut
boundary.  The equivalence with off-boundary no-crossing lets downstream route
theorems target either formulation.
-/

/--
Closed-walk boundary-support foundation target for the selected induced
peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding

/--
The closed-walk boundary-support foundation target supplies the closed-walk
off-boundary no-crossing foundation target.
-/
theorem cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_boundarySupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget := by
  intro V _ G emb source regime
  exact
    peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports
      (hfoundation source regime)

/--
The closed-walk off-boundary no-crossing foundation target supplies the
closed-walk boundary-support foundation target.
-/
theorem cap5FreeClosedWalkBoundarySupportFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget := by
  intro V _ G emb source regime
  exact
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      (hfoundation source regime)

/--
Boundary-support and off-boundary no-crossing are equivalent closed-walk
CAP5-free foundation targets.
-/
theorem cap5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget_iff_offBoundaryNoCrossingFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget :=
  ⟨cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_boundarySupportFoundationTarget,
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_offBoundaryNoCrossingFoundationTarget⟩

/--
The closed-walk boundary-support foundation target supplies the selected-source
small-cut lift foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_boundarySupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget :=
  cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_boundarySupportFoundationTarget
      hfoundation)

/--
Public index with the closed-walk boundary-support target as the closed-walk
foundation field.
-/
def CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget

/--
The boundary-support public index supplies the off-boundary public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_boundarySupportFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_boundarySupportFoundationTarget
      hindex.2.2⟩

/--
The off-boundary public index supplies the boundary-support public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
      hindex.2.2⟩

/--
Boundary-support and off-boundary no-crossing give equivalent public
closed-walk CAP5-free foundation indices.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_iff_offBoundaryNoCrossingFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_boundarySupportFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex⟩

/--
The older face-source public foundation index supplies the boundary-support
public index through the off-boundary equivalence.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_foundationTargetIndex
      hindex)

/--
Closed-walk boundary-support route target: boundary-support data supply
off-boundary no-crossing, local constancy, separation, the selected-source
small-cut lift, cyclic five-edge-connectivity, no cyclic two-cut, and S4
no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
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
Route-index theorem for the closed-walk boundary-support foundation target.
-/
theorem section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hsupport :
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    hfoundation source regime
  have hoffFoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget :=
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_boundarySupportFoundationTarget
      hfoundation
  have hroute :
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
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
      hoffFoundation source regime
  exact
    ⟨hsupport,
      hroute.1,
      hroute.2.1,
      hroute.2.2.1,
      hroute.2.2.2.1,
      hroute.2.2.2.2.1,
      hroute.2.2.2.2.2.1,
      hroute.2.2.2.2.2.2⟩

/--
The boundary-support public index supplies the boundary-support route target,
the off-boundary route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_boundarySupportFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hoffRoutes.1,
      hoffRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget
        hindex.2.2,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2⟩

/--
Closed-walk S4 salvage target for the boundary-support foundation route.  This
is the downstream statement with cyclic five-edge-connectivity supplied by the
CAP5-free regime route, not assumed.
-/
def Section92Step4ClosedWalkCAP5FreeBoundarySupportRegimeDischargedS4SalvageTarget :
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
The boundary-support foundation target supplies the explicit closed-walk S4
salvage target.
-/
theorem section92Step4ClosedWalkCAP5FreeBoundarySupportRegimeDischargedS4SalvageTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeBoundarySupportRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget
      hfoundation source regime).2.2.2.2.2.2.2

/--
The boundary-support public index supplies the explicit closed-walk S4 salvage
target.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (hindex :
      CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex) :
    Section92Step4ClosedWalkCAP5FreeBoundarySupportRegimeDischargedS4SalvageTarget :=
  section92Step4ClosedWalkCAP5FreeBoundarySupportRegimeDischargedS4SalvageTarget
    hindex.2.2

end Mettapedia.GraphTheory.FourColor
