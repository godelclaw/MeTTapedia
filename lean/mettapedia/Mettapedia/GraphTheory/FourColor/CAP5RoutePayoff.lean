import Mettapedia.GraphTheory.FourColor.CAP5RouteVerdict
import Mettapedia.GraphTheory.FourColor.F2KernelCertificate
import Mettapedia.GraphTheory.FourColor.Goal
import Mettapedia.GraphTheory.FourColor.Theorem49WheelWithInnerTriangleBenchmark

/-!
# CAP5 route payoff and finite gate surface

This module records the route-dependent endpoint obtained from the closed CAP5/F2 route
surface.  The route currently closes the Theorem 4.9 synthesis/control layer; it does
not by itself supply a new proper edge coloring, because the route certificate still
takes the root as `G.EdgeColoring Color`.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

variable [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]

/--
The route-dependent endpoint currently justified by a closed CAP5/F2 route certificate:
theorem-4.9 synthesis plus the selected-boundary-zero classifier control carried by
`CAP5F2RouteClosed`.  This deliberately contains no `EdgeColorable 4` field, because
`C₀ : G.EdgeColoring Color` is already a proper coloring in the current route type.
-/
structure CAP5RouteClosedSynthesisPayoff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    Prop where
  routeClosed : CAP5F2RouteClosed cert
  synthesis : Theorem49BoundaryRootSynthesis emb C₀
  boundaryZeroControl :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ cert.classifier.emittedFinset, z e = 0) →
        z = 0

theorem cap5RouteClosedSynthesisPayoff_of_routeClosed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hclosed : CAP5F2RouteClosed cert) :
    CAP5RouteClosedSynthesisPayoff cert where
  routeClosed := hclosed
  synthesis := hclosed.1
  boundaryZeroControl := hclosed.2

/--
The exact additional bridge needed to upgrade a closed route to Tait colorability from the
route data alone.  This is not supplied by `CAP5F2RouteClosed`; the current route type
already assumes `C₀` is a proper `EdgeColoring`, and the missing Tait part is the
nonzero-color condition.
-/
def CAP5RouteClosedRootTaitBridge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    Prop :=
  CAP5F2RouteClosed cert → IsTaitEdgeColoring G C₀

theorem taitColorable_of_routeClosedRootTaitBridge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hbridge : CAP5RouteClosedRootTaitBridge cert)
    (hclosed : CAP5F2RouteClosed cert) :
    TaitColorable G :=
  ⟨C₀, hbridge hclosed⟩

/-- Decidable ingredients for the executable CAP5 primitive-checker report. -/
structure CAP5DecidableCheckerEvidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop) : Type _ where
  portal :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)
  cycles :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)
  realized :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)

namespace CAP5DecidableCheckerEvidence

noncomputable def report
    {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}
    (checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side) :
    CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side := by
  classical
  letI := checks.portal
  letI := checks.cycles
  letI := checks.realized
  exact CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side

def noPrimitiveGapByFiniteCheck
    {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}
    (checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side) : Prop :=
  checks.report.missingCheckerEvidenceLatents = []

omit [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem noPrimitiveGap_of_noPrimitiveGapByFiniteCheck
    {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}
    (checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side)
    (hclosed : checks.noPrimitiveGapByFiniteCheck) :
    ¬ CAP5PrimitiveCheckerGap boundaryEdge side := by
  classical
  letI := checks.portal
  letI := checks.cycles
  letI := checks.realized
  exact
    (no_cap5PrimitiveCheckerGap_iff_missingCheckerEvidenceLatents_eq_nil
      boundaryEdge side).2 (by
        simpa [noPrimitiveGapByFiniteCheck, report] using hclosed)

end CAP5DecidableCheckerEvidence

/--
The exact finite input needed before the unified F2 question can be decided for a concrete CAP5
side.  It combines the executable primitive-checker closure with the forced-edge classifier and
the emitted/remaining red-blue single-coordinate witnesses consumed by the route certificate.
-/
structure CAP5FiniteNoGapRouteInput
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color)) (p0Inside p4Inside : Bool)
    (side : V → Prop) : Type _ where
  checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side
  checkerClosed : checks.noPrimitiveGapByFiniteCheck
  subset : colorings ⊆ G.EdgeKempeClosure C₀
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

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noPrimitiveGap
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    ¬ CAP5PrimitiveCheckerGap boundaryEdge side :=
  CAP5DecidableCheckerEvidence.noPrimitiveGap_of_noPrimitiveGapByFiniteCheck
    input.checks input.checkerClosed

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Generic Gate-1 meta-barrier for honest odd CAP5 boundaries.  If the five CAP5 boundary edges
cover an odd closed walk, no finite no-gap route input exists: closing the primitive checker
would force every boundary edge to cross one vertex side, which is impossible on an odd closed
walk.
-/
theorem CAP5FiniteNoGapRouteInput.false_of_boundaryEdge_odd_closed_walk
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hsubset :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → ∃ i : Fin 5, boundaryEdge i = e)
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    False :=
  input.noPrimitiveGap
    (cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk p hodd hsubset)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.redInterior_mem_projectedColoringGeneratorSubspace
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings := by
  classical
  by_cases hemitted : e ∈ input.classifier.emittedFinset
  · exact input.redEmitted e hemitted
  · exact input.redRemaining e
      ((input.classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨he, hemitted⟩)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.blueInterior_mem_projectedColoringGeneratorSubspace
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings := by
  classical
  by_cases hemitted : e ∈ input.classifier.emittedFinset
  · exact input.blueEmitted e hemitted
  · exact input.blueRemaining e
      ((input.classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨he, hemitted⟩)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.false_of_missing_interior_red_probe
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {e : G.edgeSet}
    (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hmissing :
      Pi.single e red ∉ projectedColoringGeneratorSubspace emb colorings)
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    False :=
  hmissing (input.redInterior_mem_projectedColoringGeneratorSubspace he)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.false_of_missing_interior_blue_probe
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {e : G.edgeSet}
    (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hmissing :
      Pi.single e blue ∉ projectedColoringGeneratorSubspace emb colorings)
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    False :=
  hmissing (input.blueInterior_mem_projectedColoringGeneratorSubspace he)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noMissingCheckerEvidence
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
              boundaryEdge side latent).MissingComplementarySideCycleEvidence)) := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  simpa [CAP5PrimitiveCheckerGap] using input.noPrimitiveGap

def CAP5FiniteNoGapRouteInput.toRouteCertificate
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side :=
  CAP5F2RouteCertificate.ofNoGap input.subset input.noPrimitiveGap input.classifier
    input.redEmitted input.blueEmitted input.redRemaining input.blueRemaining

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem cap5F2NoUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hemittedKernel :
      LinearMap.ker
          (planarBoundaryZeroFamilyPairingMap
            (redBlueSingleCoordinateFamily cert.classifier.emittedFinset
              cert.redEmitted cert.blueEmitted)) = ⊥) :
    CAP5F2NoUnifiedKernelMapEvader cert := by
  rintro ⟨z, hzNonzero, _hvanishForced, hmemKernel, _hmapNonzero⟩
  have hbot : z ∈ (⊥ : Submodule F2 (planarBoundaryZeroSubmodule emb)) := by
    simpa [hemittedKernel] using hmemKernel
  rw [Submodule.mem_bot] at hbot
  exact hzNonzero (by
    simpa using
      congrArg (fun w : planarBoundaryZeroSubmodule emb => (w : G.edgeSet → Color)) hbot)

/--
MAKE side of the finite CAP5 route gate: once the executable primitive-checker
frontier is closed, a checked absence of the unified emitted-kernel/remaining-map
evader is exactly enough to close the packaged CAP5/F2 route.
-/
theorem CAP5FiniteNoGapRouteInput.routeClosed_of_noUnifiedKernelMapEvader
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate) :
    CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  exact
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).1 hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hemittedKernel :
      LinearMap.ker
          (planarBoundaryZeroFamilyPairingMap
            (redBlueSingleCoordinateFamily input.classifier.emittedFinset
              input.redEmitted input.blueEmitted)) = ⊥) :
    CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  simpa [CAP5FiniteNoGapRouteInput.toRouteCertificate, CAP5F2RouteCertificate.ofNoGap] using
    cap5F2NoUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot
      (cert := input.toRouteCertificate) hemittedKernel

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Certificate-consuming MAKE side: an explicit finite F2 left-inverse certificate for the emitted
pairing map proves the no-unified-evader oracle used by the route gate.
-/
theorem CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_of_emittedFinsetPairingLeftInverseCertificate
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι F2 (planarBoundaryZeroSubmodule emb))
    (hleftInv :
      F2LeftInverseKernelCertificate B
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily input.classifier.emittedFinset
            input.redEmitted input.blueEmitted))) :
    CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.noUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot hleftInv.ker_eq_bot

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem cap5F2NoUnifiedKernelMapEvader_of_remainingControlEdges_eq_empty
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hremaining :
      cert.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    CAP5F2NoUnifiedKernelMapEvader cert := by
  rintro ⟨z, _hzNonzero, _hvanishForced, _hmemKernel, hremainingMap⟩
  apply hremainingMap
  ext i
  rcases i with ⟨⟨e, he⟩, b⟩
  simp [hremaining] at he

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_of_remainingControlEdges_eq_empty
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hremaining :
      input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  simpa [CAP5FiniteNoGapRouteInput.toRouteCertificate, CAP5F2RouteCertificate.ofNoGap] using
    cap5F2NoUnifiedKernelMapEvader_of_remainingControlEdges_eq_empty
      (cert := input.toRouteCertificate) hremaining

/--
MAKE side for the empty-remaining finite certificate: after the primitive checker frontier is
closed, if the classifier emits every interior-support control edge, the unified
emitted-kernel/remaining-map evader is impossible and the route closes.
-/
theorem CAP5FiniteNoGapRouteInput.routeClosed_of_remainingControlEdges_eq_empty
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hremaining :
      input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    CAP5F2RouteClosed input.toRouteCertificate :=
  input.routeClosed_of_noUnifiedKernelMapEvader hExceptional hcyclic
    (input.noUnifiedKernelMapEvader_of_remainingControlEdges_eq_empty hremaining)

/--
MAKE side in the RREF-shaped certificate vocabulary: after the primitive checker frontier is
closed, a checked bottom emitted-pairing kernel proves the CAP5/F2 route endpoint.
-/
theorem CAP5FiniteNoGapRouteInput.routeClosed_of_emittedFinsetPairingKernel_eq_bot
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hemittedKernel :
      LinearMap.ker
          (planarBoundaryZeroFamilyPairingMap
            (redBlueSingleCoordinateFamily input.classifier.emittedFinset
              input.redEmitted input.blueEmitted)) = ⊥) :
    CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  simpa [CAP5F2RouteClosed, CAP5FiniteNoGapRouteInput.toRouteCertificate,
    CAP5F2RouteCertificate.ofNoGap] using
    data.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_emittedFinsetPairingKernel_eq_bot
      emb C₀ colorings input.subset p0Inside p4Inside hExceptional side hcyclic
      (fun edgeCandidate _horientation hsideCase =>
        noGap_portalsCross_matchingCandidate p0Inside p4Inside input.noPrimitiveGap
          edgeCandidate hsideCase)
      (noGap_forces_sideCycles input.noPrimitiveGap)
      input.classifier input.redEmitted input.blueEmitted input.redRemaining input.blueRemaining
      input.noMissingCheckerEvidence hemittedKernel

/--
MAKE side with a checked finite left-inverse/RREF-style certificate.  This is the concrete
certificate consumer for Gate 2; it does not supply the actual CAP5 instance or its matrix data.
-/
theorem CAP5FiniteNoGapRouteInput.routeClosed_of_emittedFinsetPairingLeftInverseCertificate
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι F2 (planarBoundaryZeroSubmodule emb))
    (hleftInv :
      F2LeftInverseKernelCertificate B
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily input.classifier.emittedFinset
            input.redEmitted input.blueEmitted))) :
    CAP5F2RouteClosed input.toRouteCertificate :=
  input.routeClosed_of_emittedFinsetPairingKernel_eq_bot hExceptional hcyclic hleftInv.ker_eq_bot

/--
A finite checked route-closed certificate: executable primitive checker evidence is complete, and
the route endpoint itself is closed.  Supplying one of these for a concrete graph is the exact
canary obligation left by the current route surface.
-/
structure CAP5FiniteRouteClosedWitness
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color)) (p0Inside p4Inside : Bool)
    (side : V → Prop) : Type _ where
  checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side
  cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side
  checkerClosed : checks.noPrimitiveGapByFiniteCheck
  routeClosed : CAP5F2RouteClosed cert

theorem CAP5FiniteRouteClosedWitness.noPrimitiveGap
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (w :
      CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side) :
    ¬ CAP5PrimitiveCheckerGap boundaryEdge side :=
  CAP5DecidableCheckerEvidence.noPrimitiveGap_of_noPrimitiveGapByFiniteCheck
    w.checks w.checkerClosed

/--
The same honest-boundary barrier rules out finite route-closed witnesses, since every such
witness contains a closed primitive checker frontier.
-/
theorem CAP5FiniteRouteClosedWitness.false_of_boundaryEdge_odd_closed_walk
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hsubset :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → ∃ i : Fin 5, boundaryEdge i = e)
    (w :
      CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side) :
    False :=
  w.noPrimitiveGap
    (cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk p hodd hsubset)

def CAP5FiniteRouteClosedWitness.ofNoGapRouteInput
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hclosed : CAP5F2RouteClosed input.toRouteCertificate) :
    CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side where
  checks := input.checks
  cert := input.toRouteCertificate
  checkerClosed := input.checkerClosed
  routeClosed := hclosed

def CAP5FiniteNoGapRouteInput.toClosedWitness_of_noUnifiedKernelMapEvader
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate) :
    CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side :=
  CAP5FiniteRouteClosedWitness.ofNoGapRouteInput input
    (input.routeClosed_of_noUnifiedKernelMapEvader hExceptional hcyclic hnoEvader)

def CAP5FiniteNoGapRouteInput.toClosedWitness_of_emittedFinsetPairingKernel_eq_bot
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hemittedKernel :
      LinearMap.ker
          (planarBoundaryZeroFamilyPairingMap
            (redBlueSingleCoordinateFamily input.classifier.emittedFinset
              input.redEmitted input.blueEmitted)) = ⊥) :
    CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side :=
  CAP5FiniteRouteClosedWitness.ofNoGapRouteInput input
    (input.routeClosed_of_emittedFinsetPairingKernel_eq_bot hExceptional hcyclic hemittedKernel)

def CAP5FiniteNoGapRouteInput.toClosedWitness_of_remainingControlEdges_eq_empty
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hremaining :
      input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side :=
  CAP5FiniteRouteClosedWitness.ofNoGapRouteInput input
    (input.routeClosed_of_remainingControlEdges_eq_empty
      hExceptional hcyclic hremaining)

def CAP5FiniteNoGapRouteInput.toClosedWitness_of_emittedFinsetPairingLeftInverseCertificate
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι F2 (planarBoundaryZeroSubmodule emb))
    (hleftInv :
      F2LeftInverseKernelCertificate B
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily input.classifier.emittedFinset
            input.redEmitted input.blueEmitted))) :
    CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side :=
  CAP5FiniteRouteClosedWitness.ofNoGapRouteInput input
    (input.routeClosed_of_emittedFinsetPairingLeftInverseCertificate
      hExceptional hcyclic B hleftInv)

/--
BREAK side of the finite CAP5 route gate after primitive-checker closure: a concrete unified
emitted-kernel/remaining-map evader for the certificate induced by the finite no-gap input.
-/
structure CAP5FiniteUnifiedKernelMapEvaderWitness
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color)) (p0Inside p4Inside : Bool)
    (side : V → Prop) : Type _ where
  input : CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side
  evader : ∃ z : planarBoundaryZeroSubmodule emb,
    CAP5F2UnifiedKernelMapEvader input.toRouteCertificate z

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.exists_unifiedKernelMapEvader_of_boundaryZeroChain
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (z : planarBoundaryZeroSubmodule emb)
    (hzNonzero : ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) ≠ 0)
    (hvanishEmitted :
      ∀ e ∈ input.classifier.emittedFinset,
        ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e = 0)
    {e : G.edgeSet}
    (heRemaining :
      e ∈ input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces))
    (hzEdge :
      ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e ≠ 0) :
    ∃ z : planarBoundaryZeroSubmodule emb,
      CAP5F2UnifiedKernelMapEvader input.toRouteCertificate z := by
  classical
  refine ⟨z, ?_⟩
  refine ⟨hzNonzero, ?_, ?_, ?_⟩
  · intro e hedge
    exact hvanishEmitted e ((input.classifier.emittedFinset_spec e).2 hedge)
  · change
      planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily input.classifier.emittedFinset
            input.redEmitted input.blueEmitted) z = 0
    ext i
    exact
      forall_redBlueSingleCoordinateFamily_pairing_eq_zero_of_vanishes_on_controlEdges
        input.classifier.emittedFinset input.redEmitted input.blueEmitted
        hvanishEmitted i
  · change
      planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily
            (input.classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces))
            input.redRemaining input.blueRemaining) z ≠ 0
    rcases
      exists_familyPairing_ne_zero_of_redBlueSingleCoordinateMembership
        (input.classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces))
        input.redRemaining input.blueRemaining heRemaining hzEdge with
      ⟨i, hi⟩
    intro hzero
    exact hi (by
      simpa [planarBoundaryZeroFamilyPairingMap] using congrFun hzero i)

def CAP5FiniteNoGapRouteInput.toUnifiedKernelMapEvaderWitness_of_boundaryZeroChain
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (z : planarBoundaryZeroSubmodule emb)
    (hzNonzero : ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) ≠ 0)
    (hvanishEmitted :
      ∀ e ∈ input.classifier.emittedFinset,
        ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e = 0)
    {e : G.edgeSet}
    (heRemaining :
      e ∈ input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces))
    (hzEdge :
      ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e ≠ 0) :
    CAP5FiniteUnifiedKernelMapEvaderWitness data emb C₀ colorings p0Inside p4Inside side where
  input := input
  evader :=
    input.exists_unifiedKernelMapEvader_of_boundaryZeroChain
      z hzNonzero hvanishEmitted heRemaining hzEdge

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.exists_unifiedKernelMapEvader_of_mem_remainingControlEdges
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet}
    (heRemaining :
      e ∈ input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces)) :
    ∃ z : planarBoundaryZeroSubmodule emb,
      CAP5F2UnifiedKernelMapEvader input.toRouteCertificate z := by
  classical
  let zChain : G.edgeSet → Color := Pi.single e red
  have heRemainingParts :=
    (input.classifier.mem_remainingControlEdges_iff
      (interiorEdgeSupport emb.faceBoundary emb.faces) e).1 heRemaining
  have heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := heRemainingParts.1
  have heNotEmitted : e ∉ input.classifier.emittedFinset := heRemainingParts.2
  have hzBoundary : zChain ∈ planarBoundaryZeroSubmodule emb := by
    intro f hfBoundary
    have hfe : f ≠ e := by
      intro h
      subst f
      exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            emb.faceBoundary emb.faces))
          hfBoundary heInterior
    simp [zChain, Pi.single_eq_of_ne hfe]
  let z : planarBoundaryZeroSubmodule emb := ⟨zChain, hzBoundary⟩
  have hzNonzero :
      ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) ≠ 0 := by
    intro hzero
    have hcoord :
        ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e = 0 := by
      simpa using congrFun hzero e
    simp [z, zChain] at hcoord
  have hvanishEmitted :
      ∀ f ∈ input.classifier.emittedFinset,
        ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) f = 0 := by
    intro f hf
    have hfe : f ≠ e := by
      intro h
      subst f
      exact heNotEmitted hf
    simp [z, zChain, Pi.single_eq_of_ne hfe]
  have hzEdge :
      ((z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) e ≠ 0 := by
    simp [z, zChain]
  exact
    input.exists_unifiedKernelMapEvader_of_boundaryZeroChain
      z hzNonzero hvanishEmitted heRemaining hzEdge

def CAP5FiniteNoGapRouteInput.toUnifiedKernelMapEvaderWitness_of_mem_remainingControlEdges
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet}
    (heRemaining :
      e ∈ input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces)) :
    CAP5FiniteUnifiedKernelMapEvaderWitness data emb C₀ colorings p0Inside p4Inside side where
  input := input
  evader := input.exists_unifiedKernelMapEvader_of_mem_remainingControlEdges heRemaining

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteUnifiedKernelMapEvaderWitness.not_noUnifiedKernelMapEvader
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (w :
      CAP5FiniteUnifiedKernelMapEvaderWitness data emb C₀ colorings p0Inside p4Inside side) :
    ¬ CAP5F2NoUnifiedKernelMapEvader w.input.toRouteCertificate := by
  intro hnoEvader
  exact hnoEvader w.evader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_mem_remainingControlEdges
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet}
    (heRemaining :
      e ∈ input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces)) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  exact hnoEvader (input.exists_unifiedKernelMapEvader_of_mem_remainingControlEdges heRemaining)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate ↔
      input.classifier.remainingControlEdges
        (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅ := by
  constructor
  · intro hnoEvader
    exact Finset.eq_empty_of_forall_notMem fun e heRemaining =>
      input.not_noUnifiedKernelMapEvader_of_mem_remainingControlEdges heRemaining hnoEvader
  · intro hremaining
    exact input.noUnifiedKernelMapEvader_of_remainingControlEdges_eq_empty hremaining

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side) :
    CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate ↔
      interiorEdgeSupport emb.faceBoundary emb.faces ⊆ input.classifier.emittedFinset := by
  rw [input.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty]
  exact
    input.classifier.remainingControlEdges_eq_empty_iff_controlEdges_subset_emittedFinset
      (interiorEdgeSupport emb.faceBoundary emb.faces)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_exists_interiorEdgeSupport_not_emitted
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hgap :
      ∃ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
          e ∉ input.classifier.emittedFinset) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  rcases hgap with ⟨e, heInterior, heNotEmitted⟩
  exact heNotEmitted
    ((input.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset).1
      hnoEvader heInterior)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Generic current-route-surface BREAK: the CAP5 forced-edge classifier only emits edges that
cross the selected vertex side.  Therefore any interior-support control edge that does not
cross the side remains in the route kernel-map worklist, yielding a unified evader.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_noncrossing_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hnotCross : ¬ EdgeCrossesVertexSide G side e) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.not_noUnifiedKernelMapEvader_of_exists_interiorEdgeSupport_not_emitted
    ⟨e, heInterior, fun hemitted =>
      hnotCross (input.classifier.emittedFinset_edges_cross hemitted)⟩

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sameSide_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hsame :
      ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) → (side u ↔ side v)) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.not_noUnifiedKernelMapEvader_of_noncrossing_interiorEdgeSupport heInterior
    ((not_edgeCrossesVertexSide_iff_forall_side_iff G side e).2 hsame)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate)
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    EdgeCrossesVertexSide G side e :=
  input.classifier.emittedFinset_edges_cross
    ((input.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset).1
      hnoEvader heInterior)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Necessary side-cut shape for any current finite no-evader certificate: the selected route side
must bipartition every edge in the canonical interior support.  Equivalently, any interior edge
not crossing that side is a Gate-2 unified-kernel-map evader source for this route surface.
-/
theorem CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_noUnifiedKernelMapEvader
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate) :
    ∀ e : G.edgeSet, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
      EdgeCrossesVertexSide G side e :=
  fun _ heInterior =>
    input.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
      hnoEvader heInterior

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Side-cycle obstruction for the current finite route surface.  Gate 1 supplies a cycle contained
inside the selected side; if that cycle is not shielded by selected-boundary support, then the
no-evader condition would force one of its own side-internal edges to cross the same side.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hcycle : HasCycleOnSide G side)
    (hcycleInterior :
      ∀ {u : V} (p : G.Walk u u), p.IsCycle →
        (∀ v : V, v ∈ p.support → side v) →
          ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
            e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  rcases hcycle with ⟨_u, _hu, p, hpcycle, hpside⟩
  have hedgesLength : 0 < p.edges.length := by
    rw [SimpleGraph.Walk.length_edges]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 3) hpcycle.three_le_length
  rcases List.length_pos_iff_exists_mem.1 hedgesLength with ⟨edgeSym, hedgeSym⟩
  let e : G.edgeSet := ⟨edgeSym, p.edges_subset_edgeSet hedgeSym⟩
  have heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
    hcycleInterior p hpcycle hpside e hedgeSym
  have hcross : EdgeCrossesVertexSide G side e :=
    input.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
      hnoEvader heInterior
  have hnotCross : ¬ EdgeCrossesVertexSide G side e := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro x y hx hy
    have hxSupport : x ∈ p.support := p.mem_support_of_mem_edges hedgeSym hx
    have hySupport : y ∈ p.support := p.mem_support_of_mem_edges hedgeSym hy
    exact ⟨fun _ => hpside y hySupport, fun _ => hpside x hxSupport⟩
  exact hnotCross hcross

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
All-interior closed-surface obstruction for the current finite route surface.  If every graph
edge is in canonical interior support, Gate 1's selected-side cycle is automatically an interior
cycle, so the finite no-evader branch is impossible.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_forall_mem_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hallInterior :
      ∀ e : G.edgeSet, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport
    (noGap_forces_sideCycles (boundaryEdge := boundaryEdge) input.noPrimitiveGap).1
    (fun _p _hpcycle _hpside e _he => hallInterior e)

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_forall_mem_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hallInterior :
      ∀ e : G.edgeSet, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_forall_mem_interiorEdgeSupport
      hallInterior) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Non-interior-crossing obstruction for the current finite route surface.  If every edge outside
canonical interior support already crosses the selected route side, then Gate 1's selected-side
cycle forces a contradiction: its side-internal edges cannot cross that same side, so they would
all have to be interior, and the side-cycle/interior obstruction applies.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_edges_cross
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hNonInteriorCross :
      ∀ e : G.edgeSet, e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
        EdgeCrossesVertexSide G side e) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport
    (noGap_forces_sideCycles (boundaryEdge := boundaryEdge) input.noPrimitiveGap).1
    (fun p _hpcycle hpside e he => by
      by_contra hnotInterior
      have hcross : EdgeCrossesVertexSide G side e := hNonInteriorCross e hnotInterior
      have hnotCross : ¬ EdgeCrossesVertexSide G side e := by
        rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
        intro x y hx hy
        have hxSupport : x ∈ p.support := p.mem_support_of_mem_edges he hx
        have hySupport : y ∈ p.support := p.mem_support_of_mem_edges he hy
        exact ⟨fun _ => hpside y hySupport, fun _ => hpside x hxSupport⟩
      exact hnotCross hcross)

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_edges_cross
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hNonInteriorCross :
      ∀ e : G.edgeSet, e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
        EdgeCrossesVertexSide G side e) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_nonInterior_edges_cross
      hNonInteriorCross) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Boundary-slot corollary of the non-interior-crossing obstruction.  Under no-gap, all five CAP5
boundary slots cross the selected side.  Hence the current finite route surface cannot be
no-evader if every non-interior graph edge is one of those five boundary slots.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_subset_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hNonInteriorBoundary :
      ∀ e : G.edgeSet, e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
        ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
  input.not_noUnifiedKernelMapEvader_of_nonInterior_edges_cross
    (fun e heNonInterior => by
      rcases hNonInteriorBoundary e heNonInterior with ⟨i, hi⟩
      have hboundary :
          EdgeCrossesVertexSide G side (boundaryEdge i) :=
        noGap_forall_boundaryEdge_crosses
          (G := G) (boundaryEdge := boundaryEdge) input.noPrimitiveGap i
      simpa [hi] using hboundary)

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_subset_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hNonInteriorBoundary :
      ∀ e : G.edgeSet, e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
        ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate :=
  input.not_routeClosed_of_nonInterior_edges_cross hExceptional hcyclic
    (fun e heNonInterior => by
      rcases hNonInteriorBoundary e heNonInterior with ⟨i, hi⟩
      have hboundary :
          EdgeCrossesVertexSide G side (boundaryEdge i) :=
        noGap_forall_boundaryEdge_crosses
          (G := G) (boundaryEdge := boundaryEdge) input.noPrimitiveGap i
      simpa [hi] using hboundary)

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Local side-cycle coverage obstruction for the current finite route surface.  It is enough to
cover Gate 1's selected-side cycle by canonical interior support plus the five CAP5 boundary
slots: no-evader forces interior edges to cross the selected side, and no-gap forces boundary
slots to cross it, contradicting that the cycle is contained in the selected side.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hcycleCovered :
      ∀ {u : V} (p : G.Walk u u), p.IsCycle →
        (∀ v : V, v ∈ p.support → side v) →
          ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
            e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∨
              ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  rcases (noGap_forces_sideCycles (boundaryEdge := boundaryEdge) input.noPrimitiveGap).1 with
    ⟨_u, _hu, p, hpcycle, hpside⟩
  have hedgesLength : 0 < p.edges.length := by
    rw [SimpleGraph.Walk.length_edges]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 3) hpcycle.three_le_length
  rcases List.length_pos_iff_exists_mem.1 hedgesLength with ⟨edgeSym, hedgeSym⟩
  let e : G.edgeSet := ⟨edgeSym, p.edges_subset_edgeSet hedgeSym⟩
  have hcross : EdgeCrossesVertexSide G side e := by
    rcases hcycleCovered p hpcycle hpside e hedgeSym with heInterior | ⟨i, hi⟩
    · exact
        input.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
          hnoEvader heInterior
    · have hboundary :
          EdgeCrossesVertexSide G side (boundaryEdge i) :=
        noGap_forall_boundaryEdge_crosses
          (G := G) (boundaryEdge := boundaryEdge) input.noPrimitiveGap i
      simpa [hi] using hboundary
  have hnotCross : ¬ EdgeCrossesVertexSide G side e := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro x y hx hy
    have hxSupport : x ∈ p.support := p.mem_support_of_mem_edges hedgeSym hx
    have hySupport : y ∈ p.support := p.mem_support_of_mem_edges hedgeSym hy
    exact ⟨fun _ => hpside y hySupport, fun _ => hpside x hxSupport⟩
  exact hnotCross hcross

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcycleCovered :
      ∀ {u : V} (p : G.Walk u u), p.IsCycle →
        (∀ v : V, v ∈ p.support → side v) →
          ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
            e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∨
              ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
      hcycleCovered) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Explicit covered-cycle obstruction for the current finite route surface.  A single cycle
contained in the selected side is enough: if each of its edges is either canonical interior
support or one of the five CAP5 boundary slots, then no-evader would force every edge of that
side-internal cycle to cross the selected side.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (p : G.Walk u u) (hpcycle : p.IsCycle)
    (hpside : ∀ v : V, v ∈ p.support → side v)
    (hcovered :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∨
          ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  have hedgesLength : 0 < p.edges.length := by
    rw [SimpleGraph.Walk.length_edges]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 3) hpcycle.three_le_length
  rcases List.length_pos_iff_exists_mem.1 hedgesLength with ⟨edgeSym, hedgeSym⟩
  let e : G.edgeSet := ⟨edgeSym, p.edges_subset_edgeSet hedgeSym⟩
  have hcross : EdgeCrossesVertexSide G side e := by
    rcases hcovered e hedgeSym with heInterior | ⟨i, hi⟩
    · exact
        input.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
          hnoEvader heInterior
    · have hboundary :
          EdgeCrossesVertexSide G side (boundaryEdge i) :=
        noGap_forall_boundaryEdge_crosses
          (G := G) (boundaryEdge := boundaryEdge) input.noPrimitiveGap i
      simpa [hi] using hboundary
  have hnotCross : ¬ EdgeCrossesVertexSide G side e := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro x y hx hy
    have hxSupport : x ∈ p.support := p.mem_support_of_mem_edges hedgeSym hx
    have hySupport : y ∈ p.support := p.mem_support_of_mem_edges hedgeSym hy
    exact ⟨fun _ => hpside y hySupport, fun _ => hpside x hxSupport⟩
  exact hnotCross hcross

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (p : G.Walk u u) (hpcycle : p.IsCycle)
    (hpside : ∀ v : V, v ∈ p.support → side v)
    (hcovered :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∨
          ∃ i : Fin 5, boundaryEdge i = e) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge
      p hpcycle hpside hcovered) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Active-portal BREAK for the current finite route surface: a sidecase portal edge is part of
every enumerated separator candidate for that sidecase, while emitted forced edges are outside
their candidate support.  Hence an active portal edge that is also in canonical interior support
cannot be emitted and gives a unified kernel-map evader.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_activePortal_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    {i : Fin 5}
    (hiPortal :
      i ∈ (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside).separatorPortalSet)
    (heInterior :
      boundaryEdge i ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  refine input.not_noUnifiedKernelMapEvader_of_exists_interiorEdgeSupport_not_emitted
    ⟨boundaryEdge i, heInterior, ?_⟩
  intro hemitted
  have hforced :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side (boundaryEdge i) :=
    (input.classifier.emittedFinset_spec (boundaryEdge i)).1 hemitted
  rcases hforced with ⟨latent, _hmem, hp0, hp4, _horientation, hforcedEdge⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hnodePortal :
      i ∈ node.candidate.portalCandidate.portalSet := by
    subst hp0
    subst hp4
    simpa [node, CAP5ExceptionalAnnulusGeneratorNode.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase] using hiPortal
  have hinside :
      boundaryEdge i ∈ node.candidate.edgeSupport :=
    (node.candidate.mem_edgeSupport_iff_exists_portal (boundaryEdge i)).2
      ⟨i, hnodePortal, rfl⟩
  have houtside :
      boundaryEdge i ∉ node.candidate.edgeSupport := by
    have hforcedNode : node.ForcedCounterexampleEdge (boundaryEdge i) := by
      simpa [node] using hforcedEdge
    exact ((node.forcedCounterexampleEdge_iff_crossing_outside).1 hforcedNode).1
  exact houtside hinside

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_activePortal_interiorEdgeSupport
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    {i : Fin 5}
    (hiPortal :
      i ∈ (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside).separatorPortalSet)
    (heInterior :
      boundaryEdge i ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_activePortal_interiorEdgeSupport
      hiPortal heInterior) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
/--
Odd-interior-walk BREAK for the current finite route surface: if the canonical
interior support contains an odd closed walk, then no unified-evader-free Gate-2
certificate can exist.  Otherwise no-evader would force every traversed edge to
cross one vertex side, contradicting odd closed-walk parity.
-/
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_interiorEdgeSupport_odd_closed_walk
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (p : G.Walk u u) (hodd : Odd p.length)
    (hsubset :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  exact not_forall_edgeCrossesVertexSide_of_closed_walk_odd_length p hodd
    (fun e he =>
      input.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport
        hnoEvader (hsubset e he))

theorem CAP5FiniteNoGapRouteInput.not_routeClosed_of_interiorEdgeSupport_odd_closed_walk
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop} {u : V}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (p : G.Walk u u) (hodd : Odd p.length)
    (hsubset :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ CAP5F2RouteClosed input.toRouteCertificate := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  intro hclosed
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact
    (input.not_noUnifiedKernelMapEvader_of_interiorEdgeSupport_odd_closed_walk
      p hodd hsubset) hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_noUnifiedKernelMapEvader
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate) :
    ¬ ∃ u : V, ∃ p : G.Walk u u,
      Odd p.length ∧
        ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  rintro ⟨_u, p, hodd, hsubset⟩
  exact
    (input.not_noUnifiedKernelMapEvader_of_interiorEdgeSupport_odd_closed_walk
      p hodd hsubset) hnoEvader

theorem CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_routeClosed
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hclosed : CAP5F2RouteClosed input.toRouteCertificate) :
    ¬ ∃ u : V, ∃ p : G.Walk u u,
      Odd p.length ∧
        ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  rintro ⟨_u, p, hodd, hsubset⟩
  exact
    (input.not_routeClosed_of_interiorEdgeSupport_odd_closed_walk
      hExceptional hcyclic p hodd hsubset) hclosed

theorem CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_routeClosed
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hExceptional : data.IsExceptional) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hclosed : CAP5F2RouteClosed input.toRouteCertificate) :
    ∀ e : G.edgeSet, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
      EdgeCrossesVertexSide G side e := by
  classical
  letI := input.checks.portal
  letI := input.checks.cycles
  letI := input.checks.realized
  have hnoEvader : CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate :=
    (cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap
      emb C₀ colorings p0Inside p4Inside hExceptional side hcyclic
      input.noPrimitiveGap input.toRouteCertificate).2 hclosed
  exact input.interiorEdgeSupport_edges_cross_of_noUnifiedKernelMapEvader hnoEvader

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_emittedInterior_card_lt_interiorEdgeSupport_card
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hcard :
      (input.classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces).card <
          (interiorEdgeSupport emb.faceBoundary emb.faces).card) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  have hsubset :
      interiorEdgeSupport emb.faceBoundary emb.faces ⊆ input.classifier.emittedFinset :=
    (input.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset).1 hnoEvader
  have hle :
      (interiorEdgeSupport emb.faceBoundary emb.faces).card ≤
        (input.classifier.emittedFinset.filter fun e =>
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces).card :=
    Finset.card_le_card (by
      intro e heInterior
      exact Finset.mem_filter.2 ⟨hsubset heInterior, heInterior⟩)
  exact (Nat.not_lt_of_ge hle) hcard

omit [FiniteDimensional F2 (G.edgeSet → Color)] in
theorem CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_emittedFinset_card_lt_interiorEdgeSupport_card
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (input :
      CAP5FiniteNoGapRouteInput data emb C₀ colorings p0Inside p4Inside side)
    (hcard :
      input.classifier.emittedFinset.card <
        (interiorEdgeSupport emb.faceBoundary emb.faces).card) :
    ¬ CAP5F2NoUnifiedKernelMapEvader input.toRouteCertificate := by
  intro hnoEvader
  have hsubset :
      interiorEdgeSupport emb.faceBoundary emb.faces ⊆ input.classifier.emittedFinset :=
    (input.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset).1 hnoEvader
  have hleInterior :
      (interiorEdgeSupport emb.faceBoundary emb.faces).card ≤
        (input.classifier.emittedFinset.filter fun e =>
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces).card :=
    Finset.card_le_card (by
      intro e heInterior
      exact Finset.mem_filter.2 ⟨hsubset heInterior, heInterior⟩)
  have hleFilter :
      (input.classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces).card ≤
          input.classifier.emittedFinset.card :=
    Finset.card_filter_le _ _
  exact (Nat.not_lt_of_ge (Nat.le_trans hleInterior hleFilter)) hcard

theorem CAP5FiniteRouteClosedWitness.synthesisPayoff
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (w :
      CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side) :
    CAP5RouteClosedSynthesisPayoff w.cert :=
  cap5RouteClosedSynthesisPayoff_of_routeClosed w.routeClosed

namespace WheelCAP5RoutePayoff

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

theorem color_card : Fintype.card Color = 4 := by
  decide

/-!
The wheel-with-inner-triangle benchmark has an independent coloring canary from the maintained
benchmark module.  This is not a payoff from the CAP5 route.  The CAP5 finite route-closed canary
is the separate existential `WheelCAP5FiniteRouteClosedCanary` below.
-/

structure WheelColoringCanary : Prop where
  edgeColorable_four : wheelWithInnerTriangleGraph.EdgeColorable 4
  taitColorable : TaitColorable wheelWithInnerTriangleGraph

theorem wheelColoringCanary : WheelColoringCanary where
  edgeColorable_four :=
    by
      simpa [SimpleGraph.EdgeColorable, color_card] using
        (SimpleGraph.Coloring.colorable wheelWithInnerTriangleTaitEdgeColoring)
  taitColorable :=
    exists_taitEdgeColoring_wheelWithInnerTriangleGraph

/--
The exact missing positive canary requested at the CAP5 route layer: a concrete finite checker
and closed CAP5/F2 route certificate for the wheel benchmark.
-/
def WheelCAP5FiniteRouteClosedCanary : Prop :=
  ∃ (boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet) (n : Nat)
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop),
      Nonempty
        (CAP5FiniteRouteClosedWitness data wheelWithInnerTriangleEmbedding
          wheelWithInnerTriangleTaitEdgeColoring colorings p0Inside p4Inside side)

theorem wheelSynthesisPayoff_of_CAP5FiniteRouteClosedCanary
    (hcanary : WheelCAP5FiniteRouteClosedCanary) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring := by
  rcases hcanary with
    ⟨_boundaryEdge, _n, _data, _colorings, _p0Inside, _p4Inside, _side, hwitness⟩
  rcases hwitness with ⟨witness⟩
  exact witness.routeClosed.1

end WheelCAP5RoutePayoff

end Mettapedia.GraphTheory.FourColor
