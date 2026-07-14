import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection
import Mettapedia.GraphTheory.FourColor.Theorem49DetectorStrength

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

/-- v23 Definition 4.1's `W₀(H)`, with the two semantic carriers explicit:
`interiorVertices` must be all annulus interior vertices and `boundaryEdges`
must be the union of both boundary cycles. -/
def V23W0CycleSpace [Fintype G.edgeSet]
    (interiorVertices : Finset V) (boundaryEdges : Finset G.edgeSet) :
    Submodule F2 (G.edgeSet → Color) :=
  kirchhoffSubmodule G interiorVertices ⊓ boundaryZeroSubmodule boundaryEdges

/-- The inclusion stated by v23 Theorem 4.9: the Kirchhoff-constrained,
full-boundary-zero `W₀(H)` is contained in the span of the unprojected
Definition 4.8 Kempe-closure generator family. -/
def V23Theorem49W0ContainedInKempeClosureGeneratorSpan
    [Fintype G.edgeSet] {F : Type*}
    (faceBoundary : F → Finset G.edgeSet)
    (interiorVertices : Finset V) (boundaryEdges : Finset G.edgeSet)
    (C₀ : G.EdgeColoring Color) : Prop :=
  V23W0CycleSpace interiorVertices boundaryEdges ≤
    Submodule.span F2 (kempeClosureGeneratorFamily faceBoundary C₀)

/-- Equality between the formal detector and the projected route-generator
span.  This is a stronger projected-oracle statement, not v23 Theorem 4.9. -/
def PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V) (C₀ : G.EdgeColoring Color) : Prop :=
  theorem49BoundaryZeroKirchhoffSubspace emb vertices =
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀)

/-- Need-based inclusion from the formal detector to the projected
route-generator span.  This is what the route consumer uses, but it remains
stronger and differently shaped than v23's unprojected Theorem 4.9 target. -/
def PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V) (C₀ : G.EdgeColoring Color) : Prop :=
  theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
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

/-- The route's single Kempe-switch move, stated on the discrepancy/flow chain:
add one fixed two-color delta on a Kirchhoff-neutral support disjoint from the
selected boundary.  A genuine two-color component switch supplies exactly such
support data. -/
def RouteKempeSwitchExecutionStep
    [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G) :
    (G.edgeSet → Color) → (G.edgeSet → Color) → Prop :=
  fun x y =>
    ∃ (C : Finset G.edgeSet) (g : Color),
      IsKirchhoffNeutralMoveSupport G C ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, e ∉ C) ∧
          y = cdlOneStepMoveOn G C g x

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

theorem cdlOneStepMoveOn_mem_theorem49BoundaryZeroKirchhoffSubspace_of_kirchhoffNeutral_of_selectedBoundaryDisjoint
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {C : Finset G.edgeSet} {g : Color}
    {x : G.edgeSet → Color}
    (hx : x ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hboundary :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, e ∉ C) :
    cdlOneStepMoveOn G C g x ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  constructor
  · intro v hv
    rw [vertexKirchhoffSum_cdlOneStepMoveOn_eq]
    rw [hx.1 v hv, nsmul_even_eq_zero (hC v)]
    simp
  · intro e he
    rw [cdlOneStepMoveOn_apply_not_mem (hboundary e he)]
    exact hx.2 e he

theorem routeKempeSwitchExecutionStep_preserves_detectorSubspace
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} :
    PillarCExecutionStepPreservesDetectorSubspace emb vertices
      (RouteKempeSwitchExecutionStep emb) := by
  intro x y hx hxy
  rcases hxy with ⟨C, g, hC, hboundary, rfl⟩
  exact
    cdlOneStepMoveOn_mem_theorem49BoundaryZeroKirchhoffSubspace_of_kirchhoffNeutral_of_selectedBoundaryDisjoint
      (G := G) (emb := emb) (vertices := vertices) (C := C) (g := g)
      hx hC hboundary

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
    (hspan : PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan emb vertices C₀)
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
    simpa [PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan] using hspan
  rw [hspanEq] at hzU
  exact hzU

/-- Inclusion-form Pillar-A assembly.  This is the need-based route endpoint:
route-used discrepancies stay inside the detector under execution, and the
detector is included in the projected route-generator span. -/
theorem needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {C₀ : G.EdgeColoring Color}
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (hle : PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀)
    (hstep : PillarCExecutionStepPreservesDetectorSubspace emb vertices step)
    (hdisc : RouteUsedDiscrepancyClassesLieInDetectorSubspace emb vertices) :
    NeedBasedPillarARequirement emb vertices C₀ step := by
  intro initial z hinitial hreach
  have hinitialU := hdisc hinitial
  have hzU :=
    pillarCExecution_preserves_detectorSubspace_of_step
      (G := G) (emb := emb) (vertices := vertices) hstep hinitialU hreach
  exact hle hzU

/-- Boundary-zero annihilator triviality supplies exactly the corrected
inclusion needed by the need-based Pillar-A consumer. -/
theorem pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_boundaryZeroAnnihilatorTrivial
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀ := by
  intro z hz
  have hzProjected :
      z ∈ projectedKempeClosureGeneratorSubspace emb C₀ :=
    theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
      emb C₀ htrivial vertices hz
  simpa [projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
    using hzProjected

/-- Boundary-rooted interior-dual peel data supplies the corrected need-based
Prop (1') inclusion directly. -/
theorem pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data C₀ hC₀ vertices

/-- Height-ordered same-embedding peel data supplies the corrected need-based
Prop (1') inclusion directly. -/
theorem pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryHeightOrderedFacePeelWitnessData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryHeightOrderedFacePeelWitnessData
    (G := G) emb data C₀ hC₀ vertices

/-- Finite collar-layer peel data supplies the corrected need-based Prop (1')
inclusion directly. -/
theorem pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryCollarLayerFacePeelWitnessData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryCollarLayerFacePeelWitnessData
    (G := G) emb data C₀ hC₀ vertices

/-- Local-remainder collar peel data supplies the corrected need-based Prop
(1') inclusion through the same annihilator endpoint. -/
theorem pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    PillarAProjectedDetectorContainedInProjectedRouteGeneratorSpan emb vertices C₀ :=
  pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_boundaryZeroAnnihilatorTrivial
    (G := G) emb vertices C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)

/-- Need-based Pillar A assembled from boundary-zero annihilator triviality,
step preservation, and the route-used discrepancy detector theorem. -/
theorem needBasedPillarARequirement_of_boundaryZeroAnnihilatorTrivial_of_stepPreserves_of_routeDiscrepancies
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {C₀ : G.EdgeColoring Color}
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (hstep : PillarCExecutionStepPreservesDetectorSubspace emb vertices step)
    (hdisc : RouteUsedDiscrepancyClassesLieInDetectorSubspace emb vertices) :
    NeedBasedPillarARequirement emb vertices C₀ step :=
  needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀) (step := step)
    (pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_boundaryZeroAnnihilatorTrivial
      (G := G) emb vertices C₀ htrivial)
    hstep hdisc

/-- Concrete need-based Pillar A for the route's Kempe-switch execution step,
under the natural cubic hypothesis and the boundary-zero annihilator endpoint. -/
theorem needBasedPillarARequirement_routeKempeSwitch_of_boundaryZeroAnnihilatorTrivial_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_of_boundaryZeroAnnihilatorTrivial_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀)
    (step := RouteKempeSwitchExecutionStep emb)
    htrivial
    routeKempeSwitchExecutionStep_preserves_detectorSubspace
    (routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
      (G := G) emb vertices hG)

/-- Concrete need-based Pillar A for the route's Kempe-switch execution step
from boundary-rooted interior-dual peel data and the natural cubic hypothesis. -/
theorem needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀)
    (step := RouteKempeSwitchExecutionStep emb)
    (pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb vertices data C₀ hC₀)
    routeKempeSwitchExecutionStep_preserves_detectorSubspace
    (routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
      (G := G) emb vertices hG)

/-- Concrete need-based Pillar A for the route's Kempe-switch execution step
from height-ordered peel data and the natural cubic hypothesis. -/
theorem needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryHeightOrderedFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀)
    (step := RouteKempeSwitchExecutionStep emb)
    (pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) emb vertices data C₀ hC₀)
    routeKempeSwitchExecutionStep_preserves_detectorSubspace
    (routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
      (G := G) emb vertices hG)

/-- Concrete need-based Pillar A for the route's Kempe-switch execution step
from finite collar-layer peel data and the natural cubic hypothesis. -/
theorem needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀)
    (step := RouteKempeSwitchExecutionStep emb)
    (pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) emb vertices data C₀ hC₀)
    routeKempeSwitchExecutionStep_preserves_detectorSubspace
    (routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
      (G := G) emb vertices hG)

/-- Concrete need-based Pillar A for the route's Kempe-switch execution step
from local-remainder collar peel data and the natural cubic hypothesis. -/
theorem needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : HasCubicIncidentEdgeTriples G) :
    NeedBasedPillarARequirement emb vertices C₀
      (RouteKempeSwitchExecutionStep emb) :=
  needBasedPillarARequirement_of_detector_le_span_of_stepPreserves_of_routeDiscrepancies
    (G := G) (emb := emb) (vertices := vertices) (C₀ := C₀)
    (step := RouteKempeSwitchExecutionStep emb)
    (pillarADetectorSubspaceContainedInRouteGeneratorSpan_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (G := G) emb vertices data C₀ hC₀)
    routeKempeSwitchExecutionStep_preserves_detectorSubspace
    (routeUsedDiscrepancyClassesLieInDetectorSubspace_of_hasCubicIncidentEdgeTriples
      (G := G) emb vertices hG)

theorem closedWalkExactShell_needBasedPillarARequirement_of_detectorSpan_of_stepPreserves
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    {step : (G.edgeSet → Color) → (G.edgeSet → Color) → Prop}
    (hG : HasCubicIncidentEdgeTriples G)
    (hspan :
      PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan emb
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

/-- Closed-walk shell form of the corrected inclusion-based need-based Pillar A
endpoint for the route's Kempe-switch execution step. -/
theorem closedWalkExactShell_needBasedPillarARequirement_routeKempeSwitch_of_boundaryZeroAnnihilatorTrivial_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb shell.tait.coloring)
    (hG : HasCubicIncidentEdgeTriples G) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell
      (RouteKempeSwitchExecutionStep emb) := by
  exact
    needBasedPillarARequirement_routeKempeSwitch_of_boundaryZeroAnnihilatorTrivial_of_hasCubicIncidentEdgeTriples
      (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb)
      shell.tait.coloring htrivial hG

/-- Closed-walk shell form of the need-based route endpoint from
boundary-rooted interior-dual peel data. -/
theorem closedWalkExactShell_needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (hG : HasCubicIncidentEdgeTriples G) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell
      (RouteKempeSwitchExecutionStep emb) := by
  exact
    needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_hasCubicIncidentEdgeTriples
      (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb) data
      shell.tait.coloring shell.tait.isTait hG

/-- Closed-walk shell form of the need-based route endpoint from
height-ordered peel data. -/
theorem closedWalkExactShell_needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryHeightOrderedFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hG : HasCubicIncidentEdgeTriples G) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell
      (RouteKempeSwitchExecutionStep emb) := by
  exact
    needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryHeightOrderedFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
      (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb) data
      shell.tait.coloring shell.tait.isTait hG

/-- Closed-walk shell form of the need-based route endpoint from finite
collar-layer peel data. -/
theorem closedWalkExactShell_needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (hG : HasCubicIncidentEdgeTriples G) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell
      (RouteKempeSwitchExecutionStep emb) := by
  exact
    needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
      (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb) data
      shell.tait.coloring shell.tait.isTait hG

/-- Closed-walk shell form of the need-based route endpoint from local-remainder
collar peel data. -/
theorem closedWalkExactShell_needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (hG : HasCubicIncidentEdgeTriples G) :
    ClosedWalkExactShellNeedBasedPillarARequirement shell
      (RouteKempeSwitchExecutionStep emb) := by
  exact
    needBasedPillarARequirement_routeKempeSwitch_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_hasCubicIncidentEdgeTriples
      (G := G) emb (selectedBoundaryInteriorEdgeEndpointVertices emb) data
      shell.tait.coloring shell.tait.isTait hG

/-- On shell-bearing embeddings, the projected generator span contains an
explicit direction outside the detector whenever the manuscript-style
annihilator endpoint makes that projected family span all selected-boundary-zero
chains. -/
theorem exists_mem_projectedKempeClosureGeneratorSpan_not_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkExactShell_of_boundaryZeroAnnihilatorTrivial
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {C₀ : G.EdgeColoring Color}
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    ∃ z : G.edgeSet → Color,
      z ∈ Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) ∧
        z ∉ theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
  rcases
    exists_mem_planarBoundaryZeroSubmodule_not_mem_theorem49BoundaryZeroKirchhoffSubspace_of_hasUnblockedInteriorEndpoint
      shell.endpoint with
    ⟨z, hzBoundary, hzNotDetector⟩
  refine ⟨z, ?_, hzNotDetector⟩
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀ htrivial]
  exact hzBoundary

/-- The escaping direction is precisely the failed inclusion
`span(projected family) ≤ detector` on shell-bearing embeddings. -/
theorem not_projectedKempeClosureGeneratorSpan_le_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkExactShell_of_boundaryZeroAnnihilatorTrivial
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {C₀ : G.EdgeColoring Color}
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    ¬ Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) ≤
        theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
  intro hle
  rcases
    exists_mem_projectedKempeClosureGeneratorSpan_not_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkExactShell_of_boundaryZeroAnnihilatorTrivial
      (G := G) shell htrivial with
    ⟨z, hzSpan, hzNotDetector⟩
  exact hzNotDetector (hle hzSpan)

/-- If the projected generator family spans the unrestricted selected-boundary-
zero submodule, then the strict detector/domain gap refutes equality for that
stronger projected oracle.  It says nothing negative about v23's unprojected
`W₀(H) ≤ span(KC(C₀))` inclusion. -/
theorem not_pillarADetectorSubspaceEqualsRouteGeneratorSpan_of_span_eq_planarBoundaryZeroSubmodule_of_detector_lt
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {C₀ : G.EdgeColoring Color}
    (hspan :
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
        planarBoundaryZeroSubmodule emb)
    (hlt :
      theorem49BoundaryZeroKirchhoffSubspace emb vertices <
        planarBoundaryZeroSubmodule emb) :
    ¬ PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan emb vertices C₀ := by
  intro hpillar
  have htargetFull :
      theorem49BoundaryZeroKirchhoffSubspace emb vertices =
        planarBoundaryZeroSubmodule emb := by
    calc
      theorem49BoundaryZeroKirchhoffSubspace emb vertices =
          Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
            simpa [PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan] using hpillar
      _ = planarBoundaryZeroSubmodule emb := hspan
  rw [htargetFull] at hlt
  exact (lt_irrefl (planarBoundaryZeroSubmodule emb)) hlt

/-- Closed-walk shell specialization of the same projected-oracle obstruction.
It is formally stronger-oracle evidence, not a refutation of v23 Theorem 4.9. -/
theorem not_pillarADetectorSubspaceEqualsRouteGeneratorSpan_of_closedWalkExactShell_of_span_eq_planarBoundaryZeroSubmodule
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb) {C₀ : G.EdgeColoring Color}
    (hspan :
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
        planarBoundaryZeroSubmodule emb) :
    ¬ PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb) C₀ :=
  not_pillarADetectorSubspaceEqualsRouteGeneratorSpan_of_span_eq_planarBoundaryZeroSubmodule_of_detector_lt
    (G := G) (emb := emb)
    (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
    (C₀ := C₀) hspan
    (formalW0Proxy_lt_unrestrictedSelectedBoundaryZeroChainSpace_of_hasUnblockedInteriorEndpoint
      shell.endpoint)

/-- Boundary-zero annihilator form of the closed-walk projected-oracle
obstruction.  Full unrestricted boundary-zero spanning is too large to equal
the detector on a shell-bearing embedding. This theorem does not decide v23's
unprojected inclusion. -/
theorem not_pillarADetectorSubspaceEqualsRouteGeneratorSpan_of_closedWalkExactShell_of_boundaryZeroAnnihilatorTrivial
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {C₀ : G.EdgeColoring Color}
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    ¬ PillarAProjectedDetectorEqualsProjectedRouteGeneratorSpan emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb) C₀ :=
  not_pillarADetectorSubspaceEqualsRouteGeneratorSpan_of_closedWalkExactShell_of_span_eq_planarBoundaryZeroSubmodule
    (G := G) shell
    (span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
      emb C₀ htrivial)

end Mettapedia.GraphTheory.FourColor
