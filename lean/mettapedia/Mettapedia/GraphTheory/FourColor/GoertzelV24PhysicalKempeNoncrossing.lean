import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBoundaryClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSidePrimalKempeTrail

/-!
# Physical Kempe components do not cross on a cyclic shore boundary

For one literal vertex shore of a spherical cubic map, selected two-colour
components are actual primal paths in the shore.  If two distinct components
had alternating endpoints in the cyclic boundary order, close one component
through the complementary shore.  The exact face-label separator then forbids
the other, edge-disjoint component from joining the two resulting boundary
arcs.

The cyclic-arc hypotheses are explicit.  In a fixed-width application (in
particular the six-port cell) they are a finite calculation in `Fin n`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PhysicalKempeNoncrossing

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24CyclicBondBoundary
open GoertzelV24CyclicBoundaryAlternatingTrail
open GoertzelV24CyclicBoundaryClosure
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePrimalKempeGraph
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSidePrimalKempeTrail

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A boundary port of the colouring reduct is carried by the literal retained
endpoint of the corresponding ambient boundary dart. -/
@[simp]
theorem vertexSidePortTangle_vert_boundary
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (port : BoundaryDart graphData.toRotationSystem keep) :
    (vertexSidePortTangle graphData keep outer).vert (Sum.inr port) =
      ⟨graphData.toRotationSystem.vertOf port.1.1, port.1.2⟩ := by
  rfl

/-- **Physical common-web noncrossing, in cyclic-arc form.**

`cutPort` and `separatorPort` are the endpoints of one selected Kempe
component.  `leftPort` and `rightPort` lie on the two complementary cyclic
arcs, and form a second component.  The two components cannot be distinct.

This is the graph-backed form of the source's statement that same-pair outside
Kempe components induce a noncrossing matching on a facial interface. -/
theorem no_distinct_kempe_components_between_boundary_arcs
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (hcomplementConnected :
      (G.induce {vertex | ¬keep vertex}).Connected)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair)
    (cutPort separatorPort leftPort rightPort : Fin data.length)
    (hcutSeparator : cutPort ≠ separatorPort)
    (hrouteEndpoints :
      retainedPort graphData keep data leftPort ≠
        retainedPort graphData keep data rightPort)
    (leftSteps rightSteps : Nat)
    (hleftPort :
      (finRotate data.length)^[leftSteps]
          (finRotate data.length cutPort) = leftPort)
    (hrightPort :
      (finRotate data.length)^[rightSteps] rightPort = cutPort)
    (hleftAvoid : ∀ index, index < leftSteps →
      let port := (finRotate data.length)^[index]
        (finRotate data.length cutPort)
      port ≠ cutPort ∧ port ≠ separatorPort)
    (hrightAvoid : ∀ index, index < rightSteps →
      let port := (finRotate data.length)^[index] rightPort
      port ≠ cutPort ∧ port ≠ separatorPort)
    (hleftEndpoint : leftPort ≠ cutPort ∧ leftPort ≠ separatorPort)
    (hrightEndpoint : rightPort ≠ cutPort ∧ rightPort ≠ separatorPort)
    (hcutActive : pairActiveDart coloring pair
      (Sum.inr (data.order cutPort)))
    (hseparatorActive : pairActiveDart coloring pair
      (Sum.inr (data.order separatorPort)))
    (hleftActive : pairActiveDart coloring pair
      (Sum.inr (data.order leftPort)))
    (hrightActive : pairActiveDart coloring pair
      (Sum.inr (data.order rightPort)))
    (hseparatorConnected : KempeConnected
      (vertexSidePortTangle graphData keep outer) coloring pair
      (Sum.inr (data.order cutPort)) (Sum.inr (data.order separatorPort)))
    (hrouteConnected : KempeConnected
      (vertexSidePortTangle graphData keep outer) coloring pair
      (Sum.inr (data.order leftPort)) (Sum.inr (data.order rightPort)))
    (hdistinctComponents : ¬KempeConnected
      (vertexSidePortTangle graphData keep outer) coloring pair
      (Sum.inr (data.order cutPort)) (Sum.inr (data.order leftPort))) :
    False := by
  let T := vertexSidePortTangle graphData keep outer
  rcases exists_primalKempePath T coloring pair hcutActive hseparatorActive
      hseparatorConnected with ⟨insideRaw, hinsideRaw⟩
  rcases exists_primalKempePath T coloring pair hleftActive hrightActive
      hrouteConnected with ⟨routeRaw, hrouteRaw⟩
  let insidePath := primalKempeWalkToSide
    graphData keep outer coloring pair insideRaw
  let routePath := primalKempeWalkToSide
    graphData keep outer coloring pair routeRaw
  have hinsidePath : insidePath.IsPath :=
    primalKempeWalkToSide_isPath
      graphData keep outer coloring pair hinsideRaw
  have hroutePath : routePath.IsPath :=
    primalKempeWalkToSide_isPath
      graphData keep outer coloring pair hrouteRaw
  have hrawDisjoint : insideRaw.edges.Disjoint routeRaw.edges :=
    walk_edges_disjoint_of_not_kempeConnected T coloring pair
      hcutActive hleftActive hdistinctComponents insideRaw routeRaw
  have hsideDisjoint : routePath.edges.Disjoint insidePath.edges := by
    exact (primalKempeWalkToSide_edges_disjoint
      graphData keep outer coloring pair insideRaw routeRaw
      hrawDisjoint).symm
  rcases hcomplementConnected.exists_isPath
      (deletedPort graphData keep data separatorPort)
      (deletedPort graphData keep data cutPort) with
    ⟨outsidePath, houtsidePath⟩
  let separator := boundaryClosure graphData keep data
    cutPort separatorPort insidePath outsidePath
  let route := sideWalkToAmbient G keep routePath
  have hseparatorTrail : separator.IsTrail :=
    boundaryClosure_isTrail graphData keep data
      cutPort separatorPort hcutSeparator insidePath outsidePath
      hinsidePath.isTrail houtsidePath.isTrail
  have hrouteTrail : route.IsTrail :=
    (sideWalkToAmbient_isPath keep hroutePath).isTrail
  have hrouteVertexNe :
      (retainedPort graphData keep data leftPort).1 ≠
        (retainedPort graphData keep data rightPort).1 := by
    intro heq
    apply hrouteEndpoints
    exact Subtype.ext heq
  have hrouteNil : ¬route.Nil := Walk.not_nil_of_ne hrouteVertexNe
  have hrouteDisjointList : route.edges.Disjoint separator.edges :=
    sideWalkToAmbient_edges_disjoint_boundaryClosure
      graphData keep data cutPort separatorPort insidePath outsidePath
      routePath hsideDisjoint
  have hrouteDisjoint : ∀ edge : G.edgeSet,
      edge.1 ∈ route.edges → edge.1 ∉ separator.edges := by
    intro edge hroute
    exact List.disjoint_left.mp hrouteDisjointList hroute
  have hboundaryMembership : ∀ port : Fin data.length,
      boundaryEdge graphData keep data port ∈ separator.edges ↔
        port = cutPort ∨ port = separatorPort := by
    intro port
    exact boundaryEdge_mem_boundaryClosure_edges_iff
      graphData keep data cutPort separatorPort
        insidePath outsidePath port
  have hcut : boundaryEdge graphData keep data cutPort ∈ separator.edges :=
    (hboundaryMembership cutPort).2 (Or.inl rfl)
  have hleftBoundary :
      boundaryEdge graphData keep data leftPort ∉ separator.edges := by
    intro hmem
    exact (hboundaryMembership leftPort).1 hmem |>.elim
      hleftEndpoint.1 hleftEndpoint.2
  have hrightBoundary :
      boundaryEdge graphData keep data rightPort ∉ separator.edges := by
    intro hmem
    exact (hboundaryMembership rightPort).1 hmem |>.elim
      hrightEndpoint.1 hrightEndpoint.2
  have hleftArc : ∀ index, index < leftSteps →
      boundaryEdge graphData keep data
        ((finRotate data.length)^[index]
          (finRotate data.length cutPort)) ∉ separator.edges := by
    intro index hindex hmem
    exact (hboundaryMembership _).1 hmem |>.elim
      (hleftAvoid index hindex).1 (hleftAvoid index hindex).2
  have hrightArc : ∀ index, index < rightSteps →
      boundaryEdge graphData keep data
        ((finRotate data.length)^[index] rightPort) ∉ separator.edges := by
    intro index hindex hmem
    exact (hboundaryMembership _).1 hmem |>.elim
      (hrightAvoid index hindex).1 (hrightAvoid index hindex).2
  have hleftBoundaryNotRoute :
      boundaryEdge graphData keep data leftPort ∉ route.edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges keep
      (boundaryEdge_crosses graphData keep data leftPort) routePath
  have hrightBoundaryNotRoute :
      boundaryEdge graphData keep data rightPort ∉ route.edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges keep
      (boundaryEdge_crosses graphData keep data rightPort) routePath
  have hfirstNe : route.firstDart hrouteNil ≠ (data.order leftPort).1.1 := by
    intro heq
    apply hleftBoundaryNotRoute
    change (graphData.toRotationSystem.edgeOf
      (data.order leftPort).1.1).1 ∈ route.edges
    rw [← heq]
    change (route.firstDart hrouteNil).edge ∈ route.edges
    rw [route.edge_firstDart hrouteNil]
    exact route.mk_start_snd_mem_edges hrouteNil
  have hlastNe : graphData.toRotationSystem.alpha
      (route.lastDart hrouteNil) ≠ (data.order rightPort).1.1 := by
    intro heq
    apply hrightBoundaryNotRoute
    change (graphData.toRotationSystem.edgeOf
      (data.order rightPort).1.1).1 ∈ route.edges
    rw [← heq, graphData.toRotationSystem.edge_alpha]
    change (route.lastDart hrouteNil).edge ∈ route.edges
    rw [route.edge_lastDart hrouteNil]
    exact route.mk_penultimate_end_mem_edges hrouteNil
  exact no_disjoint_trail_between_boundary_arcs
    graphData htwoSided hdual hconnected hsphere hcubic hrotation
    keep data cutPort leftPort rightPort leftSteps rightSteps
    hleftPort hrightPort separator hseparatorTrail hcut
    hleftBoundary hrightBoundary hleftArc hrightArc route hrouteNil
    hrouteTrail hrouteDisjoint hfirstNe hlastNe

end

end GoertzelV24PhysicalKempeNoncrossing

end Mettapedia.GraphTheory.FourColor
