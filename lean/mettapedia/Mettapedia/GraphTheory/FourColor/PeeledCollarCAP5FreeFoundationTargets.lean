import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFaceSourceFoundationMappedCut

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
This module is the public index for the remaining CAP5-free
minimal-counterexample peeled-collar foundation theorem.  It does not assume
cyclic five-edge-connectivity as a field.  Instead, it names the planar
normal-form obligations whose proofs would supply the existing downstream
route interfaces.
-/

/--
Canonical annulus foundation target: a CAP5-free minimal-counterexample
regime supplies no-avoiding-walk side separation for the canonical peeled
collar carrier.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding

/--
Repaired annulus foundation target: the previous-boundary witness geometry
variant of the same CAP5-free separation theorem.
-/
def CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding

/--
Closed-walk face-source foundation target: the face-source form consumed by
the mapped-cut route.  This is the source-level normal-form obligation, not a
connectivity hypothesis.
-/
def CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget : Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeNoncrossingFaceSourceFoundationTarget

/--
Combined index for the CAP5-free peeled-collar foundation package.  Each
component is a theorem target for the planar-normal-form layer; downstream
S4 consequences are proved below from these targets.
-/
def CAP5FreePeeledCollarFoundationTargetIndex : Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget

namespace PlanarBoundaryAnnulusCollarGeometry

/--
A canonical CAP5-free separation foundation theorem supplies separation,
cyclic five-edge-connectivity, no cyclic two-cut, and the closed-collar S4
no-escape consequence for the induced peeled collar graph.
-/
theorem routeIndexConsequences_of_cap5FreeSeparationFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
  let inputs :
      MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
        data := {
    regime := regime
    annulusSeparation := hseparate
  }
  exact
    ⟨hseparate,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
A repaired CAP5-free separation foundation theorem supplies separation,
cyclic five-edge-connectivity, no cyclic two-cut, and the closed-collar S4
no-escape consequence for the induced peeled collar graph.
-/
theorem routeIndexConsequences_of_cap5FreeSeparationFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
  let inputs :
      MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
        data := {
    regime := regime
    annulusSeparation := hseparate
  }
  exact
    ⟨hseparate,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
A closed-walk CAP5-free face-source foundation theorem supplies the
face-source target, equivalent face-placement and mapped-cut route targets,
small-cut lifting, cyclic five-edge-connectivity, no cyclic two-cut, and the
closed-collar S4 no-escape consequence.
-/
theorem routeIndexConsequences_of_cap5FreeFaceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    source.RegimeNoncrossingFaceSourceFoundationTarget ∧
      source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      source.RegimeFacePlacementFoundationTarget ∧
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hsource :
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
    hfoundation source regime
  have hconsequences :=
    source.routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
      regime hsource
  exact
    ⟨hsource,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Canonical annulus CAP5-free route index: once the named foundation target is
proved, the S4 bridge is discharged without carrying cyclic five-edge
connectivity as an input.
-/
def Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical CAP5-free separation foundation target. -/
theorem section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeSeparationFoundationTarget
      hfoundation regime

/--
Repaired annulus CAP5-free route index: the previous-boundary witness
geometry variant of the same discharged S4 bridge.
-/
def Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired CAP5-free separation foundation target. -/
theorem section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeSeparationFoundationTarget
      hfoundation regime

/--
Closed-walk CAP5-free face-source route index: once the face-source foundation
target is proved, the mapped-cut and cyclic-connectivity consequences are all
available from the shared source interface.
-/
def Section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget :
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
      source.RegimeNoncrossingFaceSourceFoundationTarget ∧
        source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        source.RegimeFacePlacementFoundationTarget ∧
        source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Route-index theorem for the closed-walk CAP5-free face-source target. -/
theorem section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  exact
    source.routeIndexConsequences_of_cap5FreeFaceSourceFoundationTarget
      hfoundation regime

/--
The combined CAP5-free foundation index supplies all three downstream route
indices.  This is the compact checklist for the regime route.
-/
theorem cap5FreePeeledCollarFoundationTargetIndex_routeIndexTargets
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget := by
  exact
    ⟨section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
        hindex.1,
      section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
        hindex.2.1,
      section92Step4ClosedWalkCAP5FreeFaceSourceFoundationRouteIndexTarget
        hindex.2.2⟩

end Mettapedia.GraphTheory.FourColor
