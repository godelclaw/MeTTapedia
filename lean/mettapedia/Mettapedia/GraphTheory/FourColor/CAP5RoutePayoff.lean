import Mettapedia.GraphTheory.FourColor.CAP5RouteVerdict
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
