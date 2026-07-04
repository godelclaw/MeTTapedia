import Mettapedia.GraphTheory.FourColor.Goal
import Mettapedia.GraphTheory.FourColor.FrontierRefutations
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Bridge
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

/-! ## Section 9.2 closed-collar bridge -/

theorem closedCollarS2BridgeTarget_audit :
    closedCollarS2BridgeTarget :=
  closedCollarS2BridgeTarget_proved

theorem section92S2BridgeLemmaTarget_audit :
    section92S2BridgeLemmaTarget :=
  section92S2BridgeLemmaTarget_proved

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
