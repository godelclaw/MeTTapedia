import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareBond

/-!
# L1: internal dual adjacency of a replacement square bond

An acyclic four-step replacement separator cuts off two adjacent primal
vertices with a two-plus-two external boundary.  The internal primal bond has
two facial sides.  Local cubic rotation at the stub-free endpoints identifies
one selected external crossing on each of those sides, so both incident faces
belong to the selected dual cycle.  The internal bond therefore supplies a
literal facial-dual adjacency between two distinct cycle-support faces.

This is local annular geometry.  It assumes neither global cubicity nor global
face two-sidedness, and it does not assert that the adjacency is a chord of the
simple dual graph: the same two faces may still share a selected boundary edge.
It therefore does not yet reroute the rail pair, invoke the manuscript's primal
square reduction, attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24SelectedDualCycleSeparator
open GoertzelV24SelectedDualCycleSeparator.SelectedDualCycle
open SimpleGraph
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

variable {face : SelectedFace (web := web)}

/-- A locally three-dart cyclic vertex rotation changes the underlying graph
edge at its first step. -/
private theorem edgeOf_rho_ne_edgeOf_of_dartsAt_card_eq_three
    (web : Instance data coloring)
    (hrotation : VertexRotationCyclic web.annular.RS) (dart : G.Dart)
    (hcard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf dart)).card = 3) :
    web.annular.RS.edgeOf (web.annular.RS.rho dart) ≠
      web.annular.RS.edgeOf dart := by
  have hdart0 : dart ∈ web.annular.RS.dartsAt
      (web.annular.RS.vertOf dart) := by
    rw [RotationSystem.dartsAt]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  let RS := web.annular.RS
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := hdart0
  have hnontrivialFinset :
      (RS.dartsAt (RS.vertOf dart)).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcard]
    omega
  have hnontrivial :
      (RS.dartsAt (RS.vertOf dart) : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hstep : RS.rho dart ≠ dart :=
    (rho_isCycleOn_dartsAt RS hrotation (RS.vertOf dart)).apply_ne
      hnontrivial hdart
  intro hedge
  have hfst : (RS.rho dart).fst = dart.fst := by
    simpa only [RS, Data.toRotationSystem_vertOf] using RS.vert_rho dart
  have hedgeValue : (RS.rho dart).edge = dart.edge := by
    simpa only [RS, Data.toRotationSystem_edgeOf] using
      congrArg Subtype.val hedge
  exact hstep (SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq _ _ hfst hedgeValue)

/-- A face incident to a literally selected crossing of a simple dual cycle
is one of the two cycle vertices at that step. -/
private theorem face_mem_support_of_mem_crossingEdges_of_mem_boundary
    (cycle : GoertzelV24SelectedDualCycleSeparator.SelectedDualCycle
      web.annular.RS face)
    {edge : G.edgeSet} {candidate : OrbitFace web.annular.RS}
    (hedge : edge ∈ cycle.crossingEdges)
    (hface : edge ∈ orbitFaceBoundary web.annular.RS candidate) :
    (⟨candidate, Finset.mem_univ candidate⟩ : SelectedFace (web := web)) ∈
      cycle.walk.support := by
  rcases (cycle.mem_crossingEdges_iff edge).1 hedge with ⟨step, hstep⟩
  let left := cycle.walk.getVert step.val
  let right := cycle.walk.getVert (step.val + 1)
  have hadj := cycle.walk.adj_getVert_succ step.isLt
  have hleftRight : left.1 ≠ right.1 := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary web.annular.RS left.1 := by
    rw [← hstep]
    exact cycle.crossingEdge_mem_leftFace step
  have hright : edge ∈ orbitFaceBoundary web.annular.RS right.1 := by
    rw [← hstep]
    exact cycle.crossingEdge_mem_rightFace step
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS) left.2 right.2
      (Finset.mem_univ candidate) hleftRight hleft hright hface
  rcases hcases with hcandidateLeft | hcandidateRight
  · have heq :
        (⟨candidate, Finset.mem_univ candidate⟩ : SelectedFace (web := web)) =
          left := Subtype.ext hcandidateLeft
    rw [heq]
    exact cycle.walk.getVert_mem_support step.val
  · have heq :
        (⟨candidate, Finset.mem_univ candidate⟩ : SelectedFace (web := web)) =
          right := Subtype.ext hcandidateRight
    rw [heq]
    exact cycle.walk.getVert_mem_support (step.val + 1)

/-- The internal primal bond joins two distinct faces already occurring in
the selected four-cycle support.  This packet intentionally stops at dual
adjacency; whether that adjacency is off the walk remains a separate local
classification. -/
structure SquareBondRealization.InternalDualAdjacency
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  leftFace : SelectedFace (web := web)
  rightFace : SelectedFace (web := web)
  left_mem_support : leftFace ∈ cycle.walk.support
  right_mem_support : rightFace ∈ cycle.walk.support
  faces_ne : leftFace ≠ rightFace
  internal_mem_left : bond.internalEdge ∈
    orbitFaceBoundary web.annular.RS leftFace.1
  internal_mem_right : bond.internalEdge ∈
    orbitFaceBoundary web.annular.RS rightFace.1
  adjacent : (interiorDualGraph
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj leftFace rightFace

/-- **L1 square-bond local consumer.**  The internal edge of the exact
two-vertex residue produces a literal dual adjacency inside the selected
four-cycle support, using only local cubicity and local face two-sidedness. -/
theorem SquareBondRealization.exists_internalDualAdjacency
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    Nonempty bond.InternalDualAdjacency := by
  let RS := web.annular.RS
  let central : G.Dart := ⟨(bond.first, bond.second), bond.adjacent⟩
  let leftFace : SelectedFace (web := web) :=
    ⟨dartOrbitFace RS central, Finset.mem_univ _⟩
  let rightFace : SelectedFace (web := web) :=
    ⟨dartOrbitFace RS (RS.alpha central), Finset.mem_univ _⟩
  have hfirstMem : bond.first ∈ component.supp := by
    rw [bond.component_supp]
    simp
  have hsecondMem : bond.second ∈ component.supp := by
    rw [bond.component_supp]
    simp
  have hfirstCubic := web.boundary_wellFormed.cubic_elsewhere bond.first
    (by
      intro inner heq
      apply cycle.innerStub_not_mem_component component hroot inner
      rw [← heq]
      exact hfirstMem)
    (by
      intro outer heq
      apply cycle.outerStub_not_mem_component component hroot outer
      rw [← heq]
      exact hfirstMem)
  have hsecondCubic := web.boundary_wellFormed.cubic_elsewhere bond.second
    (by
      intro inner heq
      apply cycle.innerStub_not_mem_component component hroot inner
      rw [← heq]
      exact hsecondMem)
    (by
      intro outer heq
      apply cycle.outerStub_not_mem_component component hroot outer
      rw [← heq]
      exact hsecondMem)
  have hfirstDarts : (RS.dartsAt (RS.vertOf central)).card = 3 := by
    change ({candidate : G.Dart | candidate.fst = bond.first} :
      Finset G.Dart).card = 3
    rw [G.dart_fst_fiber_card_eq_degree]
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
    exact hfirstCubic
  have hsecondDarts :
      (RS.dartsAt (RS.vertOf (RS.alpha central))).card = 3 := by
    change ({candidate : G.Dart | candidate.fst = bond.second} :
      Finset G.Dart).card = 3
    rw [G.dart_fst_fiber_card_eq_degree]
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
    exact hsecondCubic
  have hfirstFst : (RS.rho central).fst = bond.first := by
    simpa only [RS, Data.toRotationSystem_vertOf] using RS.vert_rho central
  have hfirstIncident : RS.edgeOf (RS.rho central) ∈
      incidentEdgeFinset G bond.first := by
    simpa only [RS, Data.toRotationSystem_edgeOf] using
      (RS.rho central).edgeSet_mem_incidentEdgeFinset_of_fst_eq hfirstFst
  have hfirstNe : RS.edgeOf (RS.rho central) ≠ bond.internalEdge := by
    simpa [RS, central, SquareBondRealization.internalEdge,
      Data.toRotationSystem_edgeOf] using
      edgeOf_rho_ne_edgeOf_of_dartsAt_card_eq_three web
        (Instance.InteriorFace.vertexRotationCyclic web) central hfirstDarts
  have hfirstCrossing : RS.edgeOf (RS.rho central) ∈
      cycle.selectedCycle.crossingEdges := by
    have herase : RS.edgeOf (RS.rho central) ∈
        (incidentEdgeFinset G bond.first).erase bond.internalEdge :=
      Finset.mem_erase.2 ⟨hfirstNe, hfirstIncident⟩
    rw [← bond.filter_incident_first_eq_erase_internalEdge hroot] at herase
    exact (Finset.mem_filter.1 herase).2
  have hsecondFst :
      (RS.rho (RS.alpha central)).fst = bond.second := by
    calc
      (RS.rho (RS.alpha central)).fst = (RS.alpha central).fst := by
        simpa only [RS, Data.toRotationSystem_vertOf] using
          RS.vert_rho (RS.alpha central)
      _ = bond.second := rfl
  have hsecondIncident : RS.edgeOf (RS.rho (RS.alpha central)) ∈
      incidentEdgeFinset G bond.second := by
    simpa only [RS, Data.toRotationSystem_edgeOf] using
      (RS.rho (RS.alpha central)).edgeSet_mem_incidentEdgeFinset_of_fst_eq
        hsecondFst
  have hsecondNe :
      RS.edgeOf (RS.rho (RS.alpha central)) ≠ bond.internalEdge := by
    have hne := edgeOf_rho_ne_edgeOf_of_dartsAt_card_eq_three web
      (Instance.InteriorFace.vertexRotationCyclic web) (RS.alpha central)
        hsecondDarts
    simpa [RS, central, SquareBondRealization.internalEdge,
      Data.toRotationSystem_edgeOf, Data.toRotationSystem_alpha,
      Sym2.eq_swap] using hne
  have hsecondCrossing : RS.edgeOf (RS.rho (RS.alpha central)) ∈
      cycle.selectedCycle.crossingEdges := by
    have herase : RS.edgeOf (RS.rho (RS.alpha central)) ∈
        (incidentEdgeFinset G bond.second).erase bond.internalEdge :=
      Finset.mem_erase.2 ⟨hsecondNe, hsecondIncident⟩
    rw [← bond.filter_incident_second_eq_erase_internalEdge hroot] at herase
    exact (Finset.mem_filter.1 herase).2
  have hleftInternal : bond.internalEdge ∈
      orbitFaceBoundary RS leftFace.1 := by
    simpa [RS, central, leftFace, SquareBondRealization.internalEdge] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS central
  have hrightInternal : bond.internalEdge ∈
      orbitFaceBoundary RS rightFace.1 := by
    simpa [RS, central, rightFace, SquareBondRealization.internalEdge,
      RS.edge_alpha, Sym2.eq_swap] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha central)
  have hleftExternal : RS.edgeOf (RS.rho (RS.alpha central)) ∈
      orbitFaceBoundary RS leftFace.1 := by
    have hmem := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.phi central)
    rw [dartOrbitFace_phi_eq RS central] at hmem
    simpa [leftFace, RotationSystem.phi_apply] using hmem
  have hrightExternal : RS.edgeOf (RS.rho central) ∈
      orbitFaceBoundary RS rightFace.1 := by
    have hmem := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
      (RS.phi (RS.alpha central))
    rw [dartOrbitFace_phi_eq RS (RS.alpha central)] at hmem
    simpa [rightFace, RotationSystem.phi_apply, RS.alpha_involutive] using hmem
  have hleftSupportSelected : leftFace ∈
      cycle.selectedCycle.walk.support := by
    exact face_mem_support_of_mem_crossingEdges_of_mem_boundary
      cycle.selectedCycle hsecondCrossing hleftExternal
  have hrightSupportSelected : rightFace ∈
      cycle.selectedCycle.walk.support := by
    exact face_mem_support_of_mem_crossingEdges_of_mem_boundary
      cycle.selectedCycle hfirstCrossing hrightExternal
  have hleftSupport : leftFace ∈ cycle.walk.support := by
    simpa using hleftSupportSelected
  have hrightSupport : rightFace ∈ cycle.walk.support := by
    simpa using hrightSupportSelected
  have hleftInterior : leftFace.1 ∈
      web.annular.cellulation.interiorFaces :=
    cycle.support_internal leftFace hleftSupport
  have hfacesValueNe : leftFace.1 ≠ rightFace.1 := by
    simpa [leftFace, rightFace, RS] using
      Instance.dartOrbitFace_ne_alpha_of_mem_interiorFaces web central
        hleftInterior
  have hfacesNe : leftFace ≠ rightFace := by
    intro hfaces
    exact hfacesValueNe (congrArg Subtype.val hfaces)
  have hadjDual : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj leftFace rightFace := by
    apply
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_incidence_le_two RS) hfacesValueNe
    · exact hleftInternal
    · exact hrightInternal
  exact ⟨{
    leftFace := leftFace
    rightFace := rightFace
    left_mem_support := hleftSupport
    right_mem_support := hrightSupport
    faces_ne := hfacesNe
    internal_mem_left := hleftInternal
    internal_mem_right := hrightInternal
    adjacent := hadjDual
  }⟩

/-- The internal bond adjacency is genuinely off the selected dual walk. -/
structure SquareBondRealization.InternalDualChord
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  adjacency : bond.InternalDualAdjacency
  isChord : cycle.walk.IsChord
    s(adjacency.leftFace, adjacency.rightFace)

/-- The alternative to an off-walk chord: one selected crossing and the
internal bond are two distinct primal edges on the same pair of cycle-support
faces.  This is the exact local residue that a later two-edge-cut or face-pair
uniqueness consumer must discharge. -/
structure SquareBondRealization.ParallelSelectedBoundary
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  adjacency : bond.InternalDualAdjacency
  selectedEdge : G.edgeSet
  selected_mem_crossingEdges :
    selectedEdge ∈ cycle.selectedCycle.crossingEdges
  selected_ne_internal : selectedEdge ≠ bond.internalEdge
  selected_mem_left : selectedEdge ∈
    orbitFaceBoundary web.annular.RS adjacency.leftFace.1
  selected_mem_right : selectedEdge ∈
    orbitFaceBoundary web.annular.RS adjacency.rightFace.1

/-- **L1 square-bond fail-closed split.**  The literal internal adjacency is
either an off-walk chord of the selected four-cycle, or a selected boundary
edge is a second, distinct primal edge shared by the same two faces.  No
global pairwise-unique-face-edge hypothesis is assumed. -/
theorem SquareBondRealization.exists_internalDualChord_or_parallelSelectedBoundary
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    Nonempty bond.InternalDualChord ∨
      Nonempty bond.ParallelSelectedBoundary := by
  obtain ⟨adjacency⟩ := bond.exists_internalDualAdjacency hroot
  let dualEdge : Sym2 (SelectedFace (web := web)) :=
    s(adjacency.leftFace, adjacency.rightFace)
  by_cases hoff : dualEdge ∉ cycle.walk.edges
  · left
    refine ⟨{
      adjacency := adjacency
      isChord := ?_
    }⟩
    exact (SimpleGraph.Walk.isChord_sym2Mk).2
      ⟨adjacency.adjacent, hoff, adjacency.left_mem_support,
        adjacency.right_mem_support⟩
  · right
    have hon : dualEdge ∈ cycle.walk.edges := not_not.mp hoff
    rcases List.mem_iff_getElem.mp hon with ⟨index, hindex, hget⟩
    let step : Fin cycle.walk.length :=
      ⟨index, by simpa using hindex⟩
    let edgeStep : Fin cycle.walk.edges.length :=
      Fin.cast cycle.walk.length_edges.symm step
    have hget' : cycle.walk.edges.get edgeStep = dualEdge := by
      simpa [edgeStep, step] using hget
    have hpair :
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            cycle.walk step = dualEdge := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) cycle.walk step]
      exact hget'
    let selectedEdge := cycle.selectedCycle.crossingEdge step
    have hselectedCrossing : selectedEdge ∈
        cycle.selectedCycle.crossingEdges :=
      (cycle.selectedCycle.mem_crossingEdges_iff selectedEdge).2
        ⟨step, rfl⟩
    have hselectedNe : selectedEdge ≠ bond.internalEdge := by
      intro heq
      apply bond.internalEdge_not_mem_crossingEdges hroot
      rw [← heq]
      exact hselectedCrossing
    have hselectedShared := cycle.selectedCycle.crossing_mem_shared step
    rcases (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).1
        hselectedShared with ⟨_hinterior, hstepLeft, hstepRight⟩
    change s(cycle.walk.getVert step.val,
      cycle.walk.getVert (step.val + 1)) =
        s(adjacency.leftFace, adjacency.rightFace) at hpair
    rcases Sym2.eq_iff.mp hpair with horiented | hreversed
    · rcases horiented with ⟨hleft, hright⟩
      refine ⟨{
        adjacency := adjacency
        selectedEdge := selectedEdge
        selected_mem_crossingEdges := hselectedCrossing
        selected_ne_internal := hselectedNe
        selected_mem_left := ?_
        selected_mem_right := ?_
      }⟩
      · simpa [hleft] using hstepLeft
      · simpa [hright] using hstepRight
    · rcases hreversed with ⟨hleft, hright⟩
      refine ⟨{
        adjacency := adjacency
        selectedEdge := selectedEdge
        selected_mem_crossingEdges := hselectedCrossing
        selected_ne_internal := hselectedNe
        selected_mem_left := ?_
        selected_mem_right := ?_
      }⟩
      · simpa [hright] using hstepRight
      · simpa [hleft] using hstepLeft

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
