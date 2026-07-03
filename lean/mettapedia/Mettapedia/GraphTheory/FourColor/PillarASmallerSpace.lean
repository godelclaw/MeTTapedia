import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection

/-!
# Pillar A: route-used discrepancies in the smaller detector space

The v23 Theorem 4.9 statement is used by the later annulus assembly only for
differences between boundary-compatible Tait colorings:

* The wide-annulus setup forms `Delta = phi + psi`.
* The collar assembly repeats the same construction for the current coloring
  and the target coloring on each peeled collar.
* Downstream gadget execution only needs those discrepancies, and their
  execution successors, to lie in the projected Definition 4.8 generator span.

The existing formal shell consumer still asks for the full boundary-root
synthesis surface.  This file records the smaller algebraic consumer used by
the route ledger without attempting the false full selected-boundary-zero
spanning claim.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A route-used coloring pair: two Tait edge colorings with identical selected
boundary values. -/
structure RouteBoundaryCompatiblePair (emb : PlaneEmbeddingWithBoundary G) where
  phi : G.EdgeColoring Color
  psi : G.EdgeColoring Color
  phi_tait : IsTaitEdgeColoring G phi
  psi_tait : IsTaitEdgeColoring G psi
  selectedBoundary_eq :
    ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, phi e = psi e

/-- The route discrepancy class `Delta(phi, psi) = phi + psi`. -/
def routeDiscrepancyClass {emb : PlaneEmbeddingWithBoundary G}
    (pair : RouteBoundaryCompatiblePair emb) : G.edgeSet → Color :=
  fun e => pair.phi e + pair.psi e

/-- The exact class of discrepancies used by the synthesis route ledger. -/
def RouteUsedDiscrepancyClass (emb : PlaneEmbeddingWithBoundary G)
    (z : G.edgeSet → Color) : Prop :=
  ∃ pair : RouteBoundaryCompatiblePair emb, z = routeDiscrepancyClass pair

/-- Prop (1): the existing Theorem-4.9 detector subspace is exactly the span of
the projected route generator family. -/
def PillarADetectorSubspaceEqualsRouteGeneratorSpan
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V) (C₀ : G.EdgeColoring Color) : Prop :=
  theorem49BoundaryZeroKirchhoffSubspace emb vertices =
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀)

/-- Prop (2): a chosen Pillar-C execution step preserves membership in the
existing Theorem-4.9 detector subspace. -/
def PillarCExecutionStepPreservesDetectorSubspace
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V)
    (step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop) : Prop :=
  ∀ ⦃x y : G.edgeSet → Color⦄,
    x ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      step x y →
        y ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices

/-- Prop (3): every discrepancy actually used by the route lies in the existing
Theorem-4.9 detector subspace. -/
def RouteUsedDiscrepancyClassesLieInDetectorSubspace
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V) : Prop :=
  ∀ ⦃z : G.edgeSet → Color⦄,
    RouteUsedDiscrepancyClass emb z →
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices

/-- The smaller Pillar-A consumer: every route-used discrepancy, after any
finite sequence of route execution steps, remains in the route generator span. -/
def NeedBasedPillarARequirement
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (_vertices : Finset V) (C₀ : G.EdgeColoring Color)
    (step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop) : Prop :=
  ∀ ⦃initial z : G.edgeSet → Color⦄,
    RouteUsedDiscrepancyClass emb initial →
      Relation.ReflTransGen step initial z →
        z ∈ Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀)

/-- The shell-facing specialization of the smaller Pillar-A consumer. -/
def ClosedWalkExactShellNeedBasedPillarARequirement
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop) : Prop :=
  NeedBasedPillarARequirement emb (selectedBoundaryInteriorEdgeEndpointVertices emb)
    shell.tait.coloring step

theorem routeDiscrepancyClass_mem_theorem49BoundaryZeroKirchhoffSubspace
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (vertices : Finset V) (hG : HasCubicIncidentEdgeTriples G)
    (pair : RouteBoundaryCompatiblePair emb) :
    routeDiscrepancyClass pair ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  constructor
  · intro v hv
    have hphi :=
      isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
        (G := G) hG pair.phi_tait v
    have hpsi :=
      isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
        (G := G) hG pair.psi_tait v
    unfold routeDiscrepancyClass vertexKirchhoffSum
    unfold vertexKirchhoffSum at hphi hpsi
    rw [Finset.sum_add_distrib, hphi, hpsi]
    simp
  · intro e he
    have hboundary := pair.selectedBoundary_eq e he
    simp [routeDiscrepancyClass, hboundary, color_add_self]

theorem routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V) (hG : HasCubicIncidentEdgeTriples G) :
    RouteUsedDiscrepancyClassesLieInDetectorSubspace emb vertices := by
  rintro z ⟨pair, rfl⟩
  exact
    routeDiscrepancyClass_mem_theorem49BoundaryZeroKirchhoffSubspace
      (G := G) vertices hG pair

theorem closedWalkExactShell_routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (_shell : ClosedWalkExactShell emb) (hG : HasCubicIncidentEdgeTriples G) :
    RouteUsedDiscrepancyClassesLieInDetectorSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
  routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
    (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb) hG

theorem pillarCExecution_preserves_detectorSubspace_of_step
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V}
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (hstep : PillarCExecutionStepPreservesDetectorSubspace emb vertices step)
    {x y : G.edgeSet → Color}
    (hx : x ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices)
    (hxy : Relation.ReflTransGen step x y) :
    y ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact hx
  | head hxy _ ih =>
      exact ih (hstep hx hxy)

theorem needBasedPillarARequirement_of_detectorSpan_of_stepPreserves_of_routeDiscrepancies
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {C₀ : G.EdgeColoring Color}
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (hspan : PillarADetectorSubspaceEqualsRouteGeneratorSpan emb vertices C₀)
    (hstep : PillarCExecutionStepPreservesDetectorSubspace emb vertices step)
    (hdisc : RouteUsedDiscrepancyClassesLieInDetectorSubspace emb vertices) :
    NeedBasedPillarARequirement emb vertices C₀ step := by
  intro initial z hinitial hreach
  have hinitialU := hdisc hinitial
  have hzU :=
    pillarCExecution_preserves_detectorSubspace_of_step
      (G := G) (emb := emb) (vertices := vertices) hstep hinitialU hreach
  have hspanEq :
      theorem49BoundaryZeroKirchhoffSubspace emb vertices =
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
    simpa [PillarADetectorSubspaceEqualsRouteGeneratorSpan] using hspan
  rw [hspanEq] at hzU
  exact hzU

theorem closedWalkExactShell_needBasedPillarARequirement_of_detectorSpan_of_stepPreserves
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (hG : HasCubicIncidentEdgeTriples G)
    (hspan :
      PillarADetectorSubspaceEqualsRouteGeneratorSpan emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) shell.tait.coloring)
    (hstep :
      PillarCExecutionStepPreservesDetectorSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) step) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell step := by
  exact
    needBasedPillarARequirement_of_detectorSpan_of_stepPreserves_of_routeDiscrepancies
      (G := G) (emb := emb)
      (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
      (C₀ := shell.tait.coloring) hspan hstep
      (closedWalkExactShell_routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
        (G := G) shell hG)

end Mettapedia.GraphTheory.FourColor
