import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalParallelExclusion
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalColorTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalGeometryTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphBoundaryWellFormed
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphAnnularCellulation
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge

/-!
# Canonical graph backing of a least Tait counterexample

After parallel edges have been excluded, the canonical primal simple graph
has exactly the source edge and dart carriers.  This file transports the
structural class and Tait colorability across that presentation and packages
the resulting graph-backed vertex-minimal counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalGraphBackedPresentation

open GoertzelV24ClosedWebSpliceGraphAnnularCellulation
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSystemPrimalColorTransport
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalFaceTransport
open GoertzelV24RotationSystemPrimalGeometryTransport
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

local instance primalAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance primalEdgeDecidableEq (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

/-- Pull an ordinary edge coloring of the computed primal graph back to the
literal rotation-system edge carrier. -/
def rotationEdgeColoring (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : (rotationPrimalGraph RS).EdgeColoring Color) :
    RS.EdgeColoring Color :=
  coloring.comp (edgeAdjacencyIso RS hinjective).toHom

@[simp] theorem rotationEdgeColoring_apply
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : (rotationPrimalGraph RS).EdgeColoring Color)
    (edge : E) :
    rotationEdgeColoring RS hinjective coloring edge =
      coloring (edgeEquiv RS hinjective edge) :=
  rfl

/-- Pullback preserves the nonzero Tait condition. -/
theorem rotationEdgeColoring_isTait
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : (rotationPrimalGraph RS).EdgeColoring Color)
    (hTait : IsTaitEdgeColoring (rotationPrimalGraph RS) coloring) :
    RS.IsTaitEdgeColoring
      (rotationEdgeColoring RS hinjective coloring) := by
  intro edge
  exact hTait (edgeEquiv RS hinjective edge)

/-- The graph-backed presentation being Tait colorable implies that the
literal endpoint-simple rotation system is Tait colorable. -/
theorem rotationSystemTaitColorable_of_graphData
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (hcolorable : RotationSystemTaitColorable
      (graphData RS hinjective).toRotationSystem) :
    RotationSystemTaitColorable RS := by
  rcases hcolorable with ⟨coloring, hTait⟩
  have hline :
      (graphData RS hinjective).toRotationSystem.edgeAdjacencyGraph =
        (rotationPrimalGraph RS).lineGraph :=
    toRotationSystem_edgeAdjacencyGraph_eq_lineGraph
      (graphData RS hinjective)
  let toGraphPresentation :
      RS.edgeAdjacencyGraph →g
        (graphData RS hinjective).toRotationSystem.edgeAdjacencyGraph :=
    { toFun := edgeEquiv RS hinjective
      map_rel' := by
        intro first second hadj
        rw [hline]
        exact (edgeAdjacencyIso RS hinjective).map_adj_iff.mpr hadj }
  let pulled : RS.EdgeColoring Color := coloring.comp toGraphPresentation
  refine ⟨pulled, ?_⟩
  intro edge
  change coloring (edgeEquiv RS hinjective edge) ≠ 0
  exact hTait (edgeEquiv RS hinjective edge)

/-- Deleting one literal edge identifier agrees with deleting its canonical
primal-simple-graph edge. -/
theorem edgeDeletedPrimalGraph_eq_deleteEdges
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (removed : E) :
    edgeDeletedPrimalGraph RS removed =
      (rotationPrimalGraph RS).deleteEdges
        {(edgeEquiv RS hinjective removed).1} := by
  ext left right
  simp only [edgeDeletedPrimalGraph_adj_iff, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨dart, hedge, hleft, hright⟩
    refine ⟨⟨dart, hleft, hright⟩, ?_⟩
    intro heq
    apply hedge
    apply (edgeEquiv RS hinjective).injective
    apply Subtype.ext
    rw [← graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
      RS hinjective dart]
    change s(RS.vertOf dart, RS.vertOf (RS.alpha dart)) =
      (edgeEquiv RS hinjective removed).1
    simpa [hleft, hright] using heq
  · rintro ⟨hadj, hedge⟩
    rcases hadj with ⟨dart, hleft, hright⟩
    refine ⟨dart, ?_, hleft, hright⟩
    intro heq
    apply hedge
    rw [← heq]
    have hgraph := graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
      RS hinjective dart
    have hvalue := congrArg Subtype.val hgraph
    change s(RS.vertOf dart, RS.vertOf (RS.alpha dart)) =
      (edgeEquiv RS hinjective (RS.edgeOf dart)).1 at hvalue
    simpa [hleft, hright] using hvalue

/-- Bridge-freeness is invariant under the canonical graph backing. -/
theorem graphData_edgeBridgeFree
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (hfree : EdgeBridgeFree RS) :
    EdgeBridgeFree (graphData RS hinjective).toRotationSystem := by
  rw [edgeBridgeFree_toRotationSystem_iff]
  intro dart hbridge
  let sourceDart := (primalDartEquiv RS hinjective).symm dart
  have hreach := hfree sourceDart
  rw [edgeDeletedPrimalGraph_eq_deleteEdges RS hinjective] at hreach
  have hremoved :
      (edgeEquiv RS hinjective (RS.edgeOf sourceDart)).1 = dart.edge := by
    have hgraph := graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
      RS hinjective sourceDart
    rw [(primalDartEquiv RS hinjective).apply_symm_apply] at hgraph
    exact congrArg Subtype.val hgraph.symm
  rw [hremoved] at hreach
  have hsource : RS.vertOf sourceDart = dart.fst := by
    exact primalDartEquiv_symm_fst RS hinjective dart
  have halpha :
      primalDartEquiv RS hinjective (RS.alpha sourceDart) = dart.symm := by
    simpa [sourceDart] using primalDartEquiv_alpha RS hinjective sourceDart
  have htarget : RS.vertOf (RS.alpha sourceDart) = dart.snd := by
    rw [← primalDartEquiv_fst RS hinjective, halpha]
    rfl
  apply (SimpleGraph.isBridge_iff.mp hbridge)
  simpa [SimpleGraph.Dart.edge, hsource, htarget] using hreach

/-- Cubicity is invariant under the canonical graph backing. -/
theorem graphData_isCubic
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (hCubic : RS.IsCubic) :
    (graphData RS hinjective).toRotationSystem.IsCubic := by
  rw [SimpleGraphDartRotation.Data.toRotationSystem_isCubic_iff]
  intro vertex
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
  rw [incidentEdgeFinset_card_rotationPrimalGraph_eq_dartsAt_card
    RS hinjective vertex]
  exact hCubic vertex

/-- Local two-sidedness is invariant under the facial-orbit equivalence. -/
theorem graphData_orbitFacesTwoSided
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (htwoSided : OrbitFacesTwoSided RS) :
    OrbitFacesTwoSided (graphData RS hinjective).toRotationSystem := by
  intro dart hsame
  let source := (primalDartEquiv RS hinjective).symm dart
  apply htwoSided source
  apply (graphFaceEquiv RS hinjective).injective
  rw [graphFaceEquiv_dartOrbitFace, graphFaceEquiv_dartOrbitFace]
  have halpha := primalDartEquiv_alpha RS hinjective source
  rw [(primalDartEquiv RS hinjective).apply_symm_apply] at halpha
  simpa [source, halpha] using hsame

/-- The entire cap-stable structural class is invariant under canonical
simple-graph presentation. -/
def graphData_bridgelessSphericalCubicMapData
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (hclass : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData
      (graphData RS hinjective).toRotationSystem where
  spherical :=
    { cubic := graphData_isCubic RS hinjective hclass.spherical.cubic
      euler := graphData_euler_of_literal RS hinjective hclass.spherical.euler }
  primalConnected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hclass.primalConnected
  vertexRotationCyclic := by
    apply hasCyclicVertexRotations_implies_vertexRotationCyclic
    exact graphData_hasCyclicVertexRotations RS hinjective
      hclass.vertexRotationCyclic
  edgeBridgeFree :=
    graphData_edgeBridgeFree RS hinjective hclass.edgeBridgeFree

/-- A least counterexample has a canonical graph-backed presentation on the
same vertex type. -/
def graphBackedVertexMinimalTaitCounterexample
    {V E : Type u} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E)
    (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hnot : ¬ RotationSystemTaitColorable RS)
    (hsmaller :
      ∀ {V' E' : Type u}
        [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
        (candidate : RotationSystem.{u, u, u} V' E'),
        Fintype.card V' < Fintype.card V →
        BridgelessSphericalCubicMapData candidate →
        RotationSystemTaitColorable candidate) :
    GraphBackedVertexMinimalTaitCounterexample
      (graphData RS
        (RotationSystem.endpoints_injective_of_minimal
          RS hclass htwoSided hnot hsmaller)) := by
  let hinjective := RotationSystem.endpoints_injective_of_minimal
    RS hclass htwoSided hnot hsmaller
  exact
    { toBridgelessSphericalCubicMapData :=
        graphData_bridgelessSphericalCubicMapData RS hinjective hclass
      facesTwoSided := graphData_orbitFacesTwoSided RS hinjective htwoSided
      notColorable := fun hgraph =>
        hnot (rotationSystemTaitColorable_of_graphData RS hinjective hgraph)
      smallerColorable := hsmaller }

end

end GoertzelV24MinimalGraphBackedPresentation

end Mettapedia.GraphTheory.FourColor
