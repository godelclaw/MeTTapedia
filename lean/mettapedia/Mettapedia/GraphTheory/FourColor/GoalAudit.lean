import Mettapedia.GraphTheory.FourColor.Goal
import Mettapedia.GraphTheory.FourColor.FrontierRefutations
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWinding
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWindingRealization
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TwoLayerEscape
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TwoSidedAvoidance
import Mettapedia.GraphTheory.FourColor.PillarASmallerSpace

/-!
# Audit consequences for the FourColor goal

This module keeps the benchmark-heavy negative-oracle refutations separate from
the live `Goal` target.  The statements are part of the v23 route audit, but
they should not be imported when a developer only needs the positive shell-to-
synthesis theorem surface.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
open Theorem49ForcingInteriorEdgeObstructionRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarS2Bridge
open GoertzelLemma818ClosedCollarWinding
open GoertzelLemma818ClosedCollarWindingRealization
open GoertzelLemma818TwoLayerEscape
open GoertzelLemma818TwoSidedAvoidance

/-! ## Section 9.2 closed-collar bridge -/

theorem closedCollarS2BridgeTarget_audit :
    closedCollarS2BridgeTarget :=
  closedCollarS2BridgeTarget_proved

theorem section92S2BridgeLemmaTarget_audit :
    section92S2BridgeLemmaTarget :=
  section92S2BridgeLemmaTarget_proved

theorem closedCollarWindingFreedomTheorem_audit :
    ClosedCollarWindingFreedomTheorem :=
  closedCollarWindingFreedomTheorem

theorem closedCollarWindingZeroSwitchChangesProfile_audit :
    ClosedCollarWindingZeroSwitchChangesProfile :=
  closedCollarWindingZeroSwitchChangesProfile

theorem closedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm_audit :
    ClosedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm :=
  closedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm

theorem localTwoPoleDesingularizationCannotRemoveCyclicTwoCut_audit :
    LocalTwoPoleDesingularizationCannotRemoveCyclicTwoCut :=
  localTwoPoleDesingularizationCannotRemoveCyclicTwoCut

theorem closedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix_audit :
    ClosedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix :=
  closedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix

theorem closedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence :=
  closedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence

theorem closedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence :=
  closedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence

theorem closedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence :=
  closedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence

theorem closedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence :=
  closedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence

theorem closedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence :=
  closedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence

theorem closedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence :=
  closedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence :=
  closedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence :=
  closedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence :=
  closedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence

theorem section92WindingExactTemplateNormalFormExclusion_audit :
    Section92WindingExactTemplateNormalFormExclusion :=
  section92WindingExactTemplateNormalFormExclusion

theorem closedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm_audit :
    ClosedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm :=
  closedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_forcesExactTemplate_audit
    (hforces : ClosedCollarWindingFreedomNormalFormRealizationForcesExactTemplate) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_forcesExactTemplate hforces

theorem section92Step4RepairedByNormalFormWindingTarget_audit :
    Section92Step4RepairedByNormalFormWindingTarget :=
  section92Step4RepairedByNormalFormWindingTarget

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence :=
  closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion_audit :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion :=
  closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion

theorem closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence :=
  closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence

theorem closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion_audit :
    ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion :=
  closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion

theorem closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass_audit
    {V : Type} {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G) :
    False :=
  closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass data

theorem closedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm_audit :
    ClosedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm :=
  closedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm

theorem closedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence :=
  closedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence

theorem closedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence :=
  closedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceCaseCandidate_audit
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceCaseCandidate
    candidate

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceRotationCandidate_audit
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRotationCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceRotationCandidate
    candidate

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation

theorem section92Step4RadialFaceSampleNormalFormObstructionTarget_audit :
    Section92Step4RadialFaceSampleNormalFormObstructionTarget :=
  section92Step4RadialFaceSampleNormalFormObstructionTarget

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence

theorem section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget_audit :
    Section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget :=
  section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000_noRadialFaceRotationCandidate_audit
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceRotationCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000_noRadialFaceRotationCandidate
    candidate

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation_audit :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation

theorem section92Step4RadialFaceSlice1000000NormalFormObstructionTarget_audit :
    Section92Step4RadialFaceSlice1000000NormalFormObstructionTarget :=
  section92Step4RadialFaceSlice1000000NormalFormObstructionTarget

theorem closedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence :=
  closedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence

theorem closedCollarWindingFreedomSimplePatchN8First1000000_noProfilePreservingCandidate_audit
    (candidate : ClosedCollarWindingFreedomSimplePatchN8First1000000ProfilePreservingCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN8First1000000_noProfilePreservingCandidate candidate

theorem closedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence :=
  closedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence

theorem closedCollarWindingFreedomSimplePatchN8First2000000_noProfilePreservingCandidate_audit
    (candidate : ClosedCollarWindingFreedomSimplePatchN8First2000000ProfilePreservingCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN8First2000000_noProfilePreservingCandidate candidate

theorem closedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence :=
  closedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence

theorem closedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence_audit :
    ClosedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence :=
  closedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence

theorem closedCollarWindingFreedomSimplePatchN8Stratified33_noProfilePreservingCandidate_audit
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN8Stratified33ProfilePreservingCandidate) :
    False :=
  closedCollarWindingFreedomSimplePatchN8Stratified33_noProfilePreservingCandidate candidate

/-! ## Section 9.2 two-layer ambient execution obstruction -/

theorem section92Step4TwoLayerCounterexampleClass_audit :
    Section92Step4TwoLayerCounterexampleClass :=
  section92Step4TwoLayerCounterexampleClass

theorem section92Step4TwoSidedAvoidanceCounterexampleClass_audit :
    Section92Step4TwoSidedAvoidanceCounterexampleClass :=
  section92Step4TwoSidedAvoidanceCounterexampleClass

/-! ## Corrected need-based Pillar-A audit hook -/

theorem needBasedPillarARequirement_routeKempeSwitch_audit_of_boundaryZeroAnnihilatorTrivial
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_routeKempeSwitch_of_boundaryZeroAnnihilatorTrivial_of_hasCubicIncidentEdgeTriples
    (G := G) emb vertices C₀ htrivial hG

theorem needBasedPillarARequirement_routeKempeSwitch_audit_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryHeightOrderedFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    (G := G) emb vertices data C₀ hC₀ hG

/-! ## All four uniform geometric oracles are false -/

theorem not_interiorDualPeelOracle : ¬ InteriorDualPeelOracle := by
  intro h
  exact not_forall_interiorDualPeelData_of_closedWalkExactShell_wheel
    (fun emb hshell => h emb hshell)

theorem not_wellFoundedPeelOracle : ¬ WellFoundedPeelOracle := by
  intro h
  obtain ⟨source⟩ := nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source
  obtain ⟨wf⟩ :=
    h sharedInteriorPairAnnulusEmbedding
      ⟨{ source := source
         oneCollar := ⟨data, hnum, hboundary⟩
         tait :=
           TaitV23Data.ofTait sharedInteriorPairTaitEdgeColoring
             sharedInteriorPairTaitEdgeColoring_isTait red blue ∅
         endpoint := hasUnblockedInteriorEndpoint_sharedInteriorPair }⟩
  exact
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_witnessCoverData.2.2.2.1
      ⟨wf.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩

theorem not_previousBoundaryGeometryOracle : ¬ PreviousBoundaryGeometryOracle := by
  intro h
  obtain ⟨emb, hshell, _, _, hNotClosedWalkCollar, _⟩ :=
    exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair
  obtain ⟨shell⟩ := hshell
  obtain ⟨geometry⟩ := h emb ⟨shell⟩
  exact hNotClosedWalkCollar
    (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      shell.source geometry shell.endpoint)

/-- The v23.5 repair, as currently specified, is also false as a uniform
oracle: its positive wrapper is fixed-embedding equivalent to the collar-layer
surface, which the shared-interior-pair benchmark refutes while inhabiting the
shell. -/
theorem not_residualBoundaryGeometryOracle : ¬ ResidualBoundaryGeometryOracle := by
  intro h
  obtain ⟨emb, hshell, _, hNotCollar, _, _⟩ :=
    exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair
  exact hNotCollar
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (h emb hshell))

end Mettapedia.GraphTheory.FourColor
