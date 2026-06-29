import Mettapedia.GraphTheory.FourColor.CAP5PathXorDetector
import Mettapedia.GraphTheory.FourColor.FrontierGeometric

/-!
# CAP5/F2 route verdict

This module packages the current endpoint of the CAP5/F2 route.  The theorem
below does not claim the Four Color Theorem.  It states the precise
closed-frontier barrier for the already-reduced CAP5/F2 branch: either the
primitive portal/cycle checker has a concrete missing-evidence row, or, after
that frontier is closed, the route closes exactly when the concrete
target/off-target F2 evaders are absent; in the same branch the CAP5/Jordan
geometric separator repair is ruled out by the small cyclic-cut obstruction.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
variable [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]

/-- The primitive portal/cycle checker gap returned by the executable CAP5 report. -/
def CAP5PrimitiveCheckerGap
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop) : Prop :=
  (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingComplementarySideCycleEvidence)

/--
The finite F2 data consumed by the closed-frontier route theorem.  This bundles the
classifier, the portal/cycle side data, and the red/blue coordinate generators so the top-level
verdict can name the residual no-evader question without restating the full scheduler surface.
-/
structure CAP5F2RouteCertificate
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (side : V → Prop) : Type _ where
  subset : colorings ⊆ G.EdgeKempeClosure C₀
  portal_crosses :
    ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation →
      edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
      ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
        EdgeCrossesVertexSide G side (boundaryEdge i)
  cycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)
  classifier : data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side
  redEmitted :
    ∀ e ∈ classifier.emittedFinset,
      Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings
  blueEmitted :
    ∀ e ∈ classifier.emittedFinset,
      Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings
  redRemaining :
    ∀ e ∈ classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces),
      Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings
  blueRemaining :
    ∀ e ∈ classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces),
      Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings

/-- The closed no-evader side of the CAP5/F2 route, split into target and off-target evaders. -/
def CAP5F2NoTargetOffTargetEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) : Prop :=
  (¬ ∃ z : G.edgeSet → Color,
    z ∈ Theorem49BoundaryTarget emb ∧
      z ≠ 0 ∧
        ∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) ∧
    ¬ ∃ z : planarBoundaryZeroSubmodule emb,
      ((z : G.edgeSet → Color) ≠ 0) ∧
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            (z : G.edgeSet → Color) e = 0) ∧
          z ∈ LinearMap.ker
            (planarBoundaryZeroFamilyPairingMap
              (redBlueSingleCoordinateFamily cert.classifier.emittedFinset
                cert.redEmitted cert.blueEmitted)) ∧
            planarBoundaryZeroFamilyPairingMap
                (redBlueSingleCoordinateFamily
                  (cert.classifier.remainingControlEdges
                    (interiorEdgeSupport emb.faceBoundary emb.faces))
                  cert.redRemaining cert.blueRemaining) z ≠ 0 ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G (z : G.edgeSet → Color) v ≠ 0

/-- The route-success endpoint: theorem-4.9 synthesis plus full selected-boundary-zero control. -/
def CAP5F2RouteClosed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) : Prop :=
  Theorem49BoundaryRootSynthesis emb C₀ ∧
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ cert.classifier.emittedFinset, z e = 0) →
        z = 0

/-- The geometric repair surfaces already ruled out in the closed primitive-frontier branch. -/
def CAP5GeometricRepairBlocked
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)] : Prop :=
  (¬ Nonempty
    (PlanarBoundaryCanonicalWitnessChoice
      shell.source.toPlanarBoundaryAnnulusBoundaryData)) ∧
    (¬ ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb, collar.numCollars = 1) ∧
      (¬ ∃ previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        previous.numCollars = 1) ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).forcedCounterexampleLatents =
            CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          ¬ CAP5ExceptionalCyclicSeparatorRepairRealization (G := G)
            data p0Inside p4Inside

/--
Top-level CAP5/F2 route verdict.  Under the standard cyclic-five and finite F2 route data, the
route has no remaining scheduler/rank/report fork: either the executable checker returns a
primitive portal/cycle evidence gap, or the closed-frontier route is exactly the absence of the
two concrete target/off-target F2 evaders.  In that same closed-frontier branch, the
CAP5/Jordan separator repair is impossible by the fundamental cyclic-cut obstruction.
-/
theorem cap5F2Route_irreducibleBarrier
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (C₀ : G.EdgeColoring Color) (colorings : Set (G.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    CAP5PrimitiveCheckerGap boundaryEdge side ∨
      ((CAP5F2NoTargetOffTargetEvader cert ↔ CAP5F2RouteClosed cert) ∧
        CAP5GeometricRepairBlocked shell data p0Inside p4Inside side) := by
  classical
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    have hnoMissing : ¬ CAP5PrimitiveCheckerGap boundaryEdge side := by
      exact
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
          boundaryEdge side).1 (by simpa [report] using hmissingEmpty)
    constructor
    · constructor
      · intro hnoEvader
        exact
          data.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure
            emb C₀ colorings cert.subset p0Inside p4Inside h side hcyclic
            cert.portal_crosses cert.cycles cert.classifier cert.redEmitted
            cert.blueEmitted cert.redRemaining cert.blueRemaining hnoMissing
            hnoEvader.1 hnoEvader.2
      · intro hclosed
        constructor
        · rintro ⟨z, hzTarget, hzNonzero, hvanishForced⟩
          have hzBoundary : z ∈ planarBoundaryZeroSubmodule emb :=
            (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
              emb (Theorem49BoundaryVertices emb)) (by
                simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hzTarget)
          have hvanishEmitted :
              ∀ e ∈ cert.classifier.emittedFinset, z e = 0 := by
            intro e he
            exact hvanishForced e ((cert.classifier.emittedFinset_spec e).1 he)
          exact hzNonzero (hclosed.2 hzBoundary hvanishEmitted)
        · rintro ⟨z, hzNonzero, hvanishForced, _hkernel, _hmapNonzero, _hvertex⟩
          have hvanishEmitted :
              ∀ e ∈ cert.classifier.emittedFinset, (z : G.edgeSet → Color) e = 0 := by
            intro e he
            exact hvanishForced e ((cert.classifier.emittedFinset_spec e).1 he)
          exact hzNonzero (hclosed.2 z.property hvanishEmitted)
    · exact
        closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction
          shell data p0Inside p4Inside report hcyclic hmissingEmpty
  · left
    exact
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient
        boundaryEdge side).1 (by simpa [report] using hmissingEmpty)

end Mettapedia.GraphTheory.FourColor
