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

/-- The route-level checker gap is exactly a nonempty executable missing-evidence report. -/
theorem cap5PrimitiveCheckerGap_iff_missingCheckerEvidenceLatents_ne_nil
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)] :
    CAP5PrimitiveCheckerGap boundaryEdge side ↔
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents ≠ [] := by
  simpa [CAP5PrimitiveCheckerGap] using
    (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient
        boundaryEdge side).symm

/-- Closing the route-level checker gap is exactly emptying the executable missing-evidence report. -/
theorem no_cap5PrimitiveCheckerGap_iff_missingCheckerEvidenceLatents_eq_nil
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)] :
    ¬ CAP5PrimitiveCheckerGap boundaryEdge side ↔
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [] := by
  simpa [CAP5PrimitiveCheckerGap] using
    (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
        boundaryEdge side).symm

/-- Any enumerated latent missing portal-crossing evidence is already a primitive checker gap. -/
theorem cap5PrimitiveCheckerGap_of_missingPortal
    {side : V → Prop} {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge)
    (hmissing :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).MissingPortalCrossingEvidence) :
    CAP5PrimitiveCheckerGap boundaryEdge side :=
  Or.inl ⟨latent, hmem, hmissing⟩

/-- Any enumerated latent missing the selected-side cycle is already a primitive checker gap. -/
theorem cap5PrimitiveCheckerGap_of_missingSelectedCycle
    {side : V → Prop} {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge)
    (hmissing :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).MissingSelectedSideCycleEvidence) :
    CAP5PrimitiveCheckerGap boundaryEdge side :=
  Or.inr (Or.inl ⟨latent, hmem, hmissing⟩)

/-- Any enumerated latent missing the complementary-side cycle is already a primitive checker gap. -/
theorem cap5PrimitiveCheckerGap_of_missingComplementaryCycle
    {side : V → Prop} {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge)
    (hmissing :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).MissingComplementarySideCycleEvidence) :
    CAP5PrimitiveCheckerGap boundaryEdge side :=
  Or.inr (Or.inr ⟨latent, hmem, hmissing⟩)

/--
No primitive checker gap forces portal crossings for every enumerated latent.  This is the
precise bridge from the finite checker frontier to the portal premise consumed by the F2 oracle.
-/
theorem noGap_portalsCross
    {side : V → Prop}
    (hno : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      boundaryEdge side latent).PortalCrosses := by
  by_contra hmissing
  exact hno (cap5PrimitiveCheckerGap_of_missingPortal hmem hmissing)

/-- Since the latent list enumerates every latent, no gap gives portal crossings for all latents. -/
theorem noGap_portalsCross_allLatents
    {side : V → Prop}
    (hno : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      boundaryEdge side latent).PortalCrosses :=
  noGap_portalsCross hno (CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent)

/--
No primitive checker gap supplies the broad portal-crossing premise used by the F2 oracle.  The
candidate need not be definitionally the canonical latent candidate: matching the selected
portal-side case is enough, because both portal lists are the same finite side-case portal set.
-/
theorem noGap_portalsCross_matchingCandidate
    {side : V → Prop} (p0Inside p4Inside : Bool)
    (hno : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside) :
    ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
      EdgeCrossesVertexSide G side (boundaryEdge i) := by
  let latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge :=
    { orientation := edgeCandidate.portalCandidate.orientation
      p0Inside := p0Inside
      p4Inside := p4Inside }
  have hportal :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses :=
    noGap_portalsCross_allLatents hno latent
  intro i hi
  apply hportal i
  have hiSideCase :
      i ∈ edgeCandidate.portalCandidate.sideCase.separatorPortalSet := by
    simpa [edgeCandidate.portalCandidate.hportalSet] using hi
  have hiSelected :
      i ∈ (CAP5ExceptionalAnnulusSideCase.ofPortalSides
        p0Inside p4Inside).separatorPortalSet := by
    simpa [hsideCase] using hiSideCase
  simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
    CAP5ExceptionalAnnulusGeneratorNode.candidate,
    CAP5ExceptionalAnnulusGeneratorLatent.candidate,
    CAP5ExceptionalAnnulusGeneratorLatent.sideCase,
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
    CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
    latent] using hiSelected

/-- If the selected side has no cycle, the primitive checker gap is forced. -/
theorem cap5PrimitiveCheckerGap_of_no_selectedSideCycle
    {side : V → Prop} (hmissing : ¬ HasCycleOnSide G side) :
    CAP5PrimitiveCheckerGap boundaryEdge side := by
  let latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge :=
    { orientation := .redBlue03_redPurple04
      p0Inside := true
      p4Inside := true }
  exact
    cap5PrimitiveCheckerGap_of_missingSelectedCycle
      (CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent) (by
        simpa [CAP5ExceptionalAnnulusGeneratorNode.MissingSelectedSideCycleEvidence,
          CAP5ExceptionalAnnulusGeneratorReport.latentNode, latent] using hmissing)

/-- If the complementary side has no cycle, the primitive checker gap is forced. -/
theorem cap5PrimitiveCheckerGap_of_no_complementarySideCycle
    {side : V → Prop} (hmissing : ¬ HasCycleOnSide G (fun v => ¬ side v)) :
    CAP5PrimitiveCheckerGap boundaryEdge side := by
  let latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge :=
    { orientation := .redBlue03_redPurple04
      p0Inside := true
      p4Inside := true }
  exact
    cap5PrimitiveCheckerGap_of_missingComplementaryCycle
      (CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent) (by
        simpa [CAP5ExceptionalAnnulusGeneratorNode.MissingComplementarySideCycleEvidence,
          CAP5ExceptionalAnnulusGeneratorReport.latentNode, latent] using hmissing)

/--
No primitive checker gap forces both side-cycle witnesses.  Hence an unconditional discharge of
the checker gap must prove these graph-side cycle facts for the selected CAP5 side.
-/
theorem noGap_sideCycles
    {side : V → Prop}
    (hno : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v) := by
  constructor
  · by_contra hmissing
    exact hno
      (cap5PrimitiveCheckerGap_of_missingSelectedCycle hmem (by
        simpa [CAP5ExceptionalAnnulusGeneratorNode.MissingSelectedSideCycleEvidence,
          CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing))
  · by_contra hmissing
    exact hno
      (cap5PrimitiveCheckerGap_of_missingComplementaryCycle hmem (by
        simpa [CAP5ExceptionalAnnulusGeneratorNode.MissingComplementarySideCycleEvidence,
          CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing))

/-- No primitive checker gap forces the two graph-side cycle witnesses outright. -/
theorem noGap_forces_sideCycles
    {side : V → Prop}
    (hno : ¬ CAP5PrimitiveCheckerGap boundaryEdge side) :
    HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v) := by
  constructor
  · by_contra hmissing
    exact hno (cap5PrimitiveCheckerGap_of_no_selectedSideCycle hmissing)
  · by_contra hmissing
    exact hno (cap5PrimitiveCheckerGap_of_no_complementarySideCycle hmissing)

/-- The constant-empty side always has a primitive checker gap: it has no selected-side cycle. -/
theorem cap5PrimitiveCheckerGap_falseSide
    (boundaryEdge : Fin 5 → G.edgeSet) :
    CAP5PrimitiveCheckerGap boundaryEdge (fun _ : V => False) := by
  exact cap5PrimitiveCheckerGap_of_no_selectedSideCycle (boundaryEdge := boundaryEdge)
    (side := fun _ : V => False) (by
      rintro ⟨_u, hfalse, _p, _hpcycle, _hpside⟩
      exact hfalse)

/--
A completely side-uniform checker-gap discharge is impossible from the current hypotheses:
the constant-empty side is a formal counterexample.
-/
theorem not_forall_no_cap5PrimitiveCheckerGap_allSides
    (boundaryEdge : Fin 5 → G.edgeSet) :
    ¬ (∀ side : V → Prop, ¬ CAP5PrimitiveCheckerGap boundaryEdge side) := by
  intro hforall
  exact hforall (fun _ : V => False)
    (cap5PrimitiveCheckerGap_falseSide boundaryEdge)

variable [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]

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

/-- Build the route certificate after the primitive checker gap has been closed. -/
def CAP5F2RouteCertificate.ofNoGap
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (hnoGap : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side where
  subset := hsubset
  portal_crosses := by
    intro edgeCandidate _horientation hsideCase
    exact noGap_portalsCross_matchingCandidate p0Inside p4Inside hnoGap
      edgeCandidate hsideCase
  cycles := noGap_forces_sideCycles hnoGap
  classifier := classifier
  redEmitted := hredEmitted
  blueEmitted := hblueEmitted
  redRemaining := hredRemaining
  blueRemaining := hblueRemaining

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

/--
The single unified emitted-kernel/remaining-map evader left by the packaged F2 oracle.
This is the witness returned when the closed-frontier route is not closed.
-/
def CAP5F2UnifiedKernelMapEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side)
    (z : planarBoundaryZeroSubmodule emb) : Prop :=
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
              cert.redRemaining cert.blueRemaining) z ≠ 0

/-- The closed-frontier no-evader predicate for the unified kernel/map witness. -/
def CAP5F2NoUnifiedKernelMapEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    Prop :=
  ¬ ∃ z : planarBoundaryZeroSubmodule emb, CAP5F2UnifiedKernelMapEvader cert z

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

/--
Closed-frontier budget oracle with the portal/cycle/no-missing side conditions discharged from
`¬ CAP5PrimitiveCheckerGap`.  The remaining mathematical question is exactly the unified
emitted-kernel/remaining-map evader set in the conclusion.
-/
theorem budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (hnoGap : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ((¬ ∃ z : planarBoundaryZeroSubmodule emb,
      ((z : G.edgeSet → Color) ≠ 0) ∧
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            (z : G.edgeSet → Color) e = 0) ∧
          z ∈ LinearMap.ker
            (planarBoundaryZeroFamilyPairingMap
              (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted
                hblueEmitted)) ∧
            planarBoundaryZeroFamilyPairingMap
                (redBlueSingleCoordinateFamily
                  (classifier.remainingControlEdges
                    (interiorEdgeSupport emb.faceBoundary emb.faces))
                  hredRemaining hblueRemaining) z ≠ 0) ↔
      Theorem49BoundaryRootSynthesis emb C₀ ∧
        (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ e ∈ classifier.emittedFinset, z e = 0) →
            z = 0)) ∧
      (¬ (Theorem49BoundaryRootSynthesis emb C₀ ∧
        (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ e ∈ classifier.emittedFinset, z e = 0) →
            z = 0)) →
        ∃ z : planarBoundaryZeroSubmodule emb,
          ((z : G.edgeSet → Color) ≠ 0) ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                (z : G.edgeSet → Color) e = 0) ∧
              z ∈ LinearMap.ker
                (planarBoundaryZeroFamilyPairingMap
                  (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted
                    hblueEmitted)) ∧
                planarBoundaryZeroFamilyPairingMap
                    (redBlueSingleCoordinateFamily
                      (classifier.remainingControlEdges
                        (interiorEdgeSupport emb.faceBoundary emb.faces))
                      hredRemaining hblueRemaining) z ≠ 0) := by
  exact
    data.budgetMetNoEvader_boundaryZeroControl_oracle
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic
      (fun edgeCandidate _horientation hsideCase =>
        noGap_portalsCross_matchingCandidate p0Inside p4Inside hnoGap
          edgeCandidate hsideCase)
      (noGap_forces_sideCycles hnoGap)
      classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
      (by simpa [CAP5PrimitiveCheckerGap] using hnoGap)

/--
Closed-frontier route equivalence stated directly in the single unified-evader vocabulary.
After the primitive checker frontier is closed, this is the exact remaining F2 question.
-/
theorem cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
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
    (hnoGap : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    CAP5F2NoUnifiedKernelMapEvader cert ↔ CAP5F2RouteClosed cert := by
  have horacle :=
    budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap
      emb C₀ colorings cert.subset p0Inside p4Inside h side hcyclic hnoGap
      cert.classifier cert.redEmitted cert.blueEmitted cert.redRemaining
      cert.blueRemaining
  simpa [CAP5F2NoUnifiedKernelMapEvader, CAP5F2UnifiedKernelMapEvader,
    CAP5F2RouteClosed] using horacle.1

/--
The pinned barrier form of the same oracle: under no checker gap, the unified evader set is
inhabited exactly when the closed route endpoint fails.
-/
theorem cap5F2UnifiedKernelMapEvader_exists_iff_not_routeClosed_of_noGap
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
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
    (hnoGap : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    (∃ z : planarBoundaryZeroSubmodule emb, CAP5F2UnifiedKernelMapEvader cert z) ↔
      ¬ CAP5F2RouteClosed cert := by
  constructor
  · intro hevader hclosed
    have hnoEvader :
        CAP5F2NoUnifiedKernelMapEvader cert :=
      (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
        emb C₀ colorings p0Inside p4Inside h side hcyclic hnoGap cert).2 hclosed
    exact hnoEvader hevader
  · intro hnotClosed
    have horacle :=
      budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap
        emb C₀ colorings cert.subset p0Inside p4Inside h side hcyclic hnoGap
        cert.classifier cert.redEmitted cert.blueEmitted cert.redRemaining
        cert.blueRemaining
    have hevader :=
      horacle.2 (by simpa [CAP5F2RouteClosed] using hnotClosed)
    simpa [CAP5F2UnifiedKernelMapEvader] using hevader

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

/--
No-gap form of the top route verdict.  Once exact side data closes the primitive checker
frontier, the route has only the target/off-target F2 no-evader question and the geometric
repair obstruction remains blocked.
-/
theorem cap5F2Route_irreducibleBarrier_of_noGap
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
    (hnoGap : ¬ CAP5PrimitiveCheckerGap boundaryEdge side)
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    (CAP5F2NoTargetOffTargetEvader cert ↔ CAP5F2RouteClosed cert) ∧
      CAP5GeometricRepairBlocked shell data p0Inside p4Inside side := by
  rcases
      cap5F2Route_irreducibleBarrier
        shell C₀ colorings p0Inside p4Inside h side hcyclic cert with
    hgap | hclosed
  · exact False.elim (hnoGap hgap)
  · exact hclosed

end Mettapedia.GraphTheory.FourColor
