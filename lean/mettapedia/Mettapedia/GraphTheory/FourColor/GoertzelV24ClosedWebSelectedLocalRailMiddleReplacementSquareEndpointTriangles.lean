import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareChordTriangles

/-!
# L1: literal endpoint triangles of a replacement-square bond

The four-edge boundary of a two-vertex square residue has an internal bond.
At either cubic endpoint, that bond and the two remaining incident edges form
one literal facial-dual triangle.  This module constructs those triangles from
the actual oriented bond dart and its three-step local rotation.

This is source-local annular geometry.  It does not import closed-map
minimality or global uniqueness of shared face edges, and it does not identify
these facial-dual triangles with the manuscript's primal rotor triangle.
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
open SimpleGraph
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

variable {face : SelectedFace (web := web)}

private def selectedTriangleWalk
    {first second third : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFirst : SelectedDualGraph (web := web).Adj third first) :
    SelectedDualGraph (web := web).Walk first first :=
  .cons hfirstSecond (.cons hsecondThird (.cons hthirdFirst .nil))

@[simp] private theorem selectedTriangleWalk_length
    {first second third : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFirst : SelectedDualGraph (web := web).Adj third first) :
    (selectedTriangleWalk hfirstSecond hsecondThird hthirdFirst).length = 3 := by
  simp [selectedTriangleWalk]

private theorem selectedTriangleWalk_isCycle
    {first second third : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFirst : SelectedDualGraph (web := web).Adj third first) :
    (selectedTriangleWalk hfirstSecond hsecondThird hthirdFirst).IsCycle := by
  simp [selectedTriangleWalk, SimpleGraph.Walk.isCycle_def,
    SimpleGraph.Walk.isTrail_def, hfirstSecond.ne,
    hfirstSecond.ne.symm, hsecondThird.ne, hthirdFirst.ne,
    hthirdFirst.ne.symm]

/-- Package three prescribed primal crossings around a literal dual
triangle.  Unlike `SelectedDualCycle.ofWalk`, this constructor retains all
three crossing choices rather than only a distinguished anchor. -/
private noncomputable def selectedTriangle
    {first second third : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFirst : SelectedDualGraph (web := web).Adj third first)
    (firstSecondEdge secondThirdEdge thirdFirstEdge : G.edgeSet)
    (hfirstSecondEdge : firstSecondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) first.1 second.1)
    (hsecondThirdEdge : secondThirdEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) second.1 third.1)
    (hthirdFirstEdge : thirdFirstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) third.1 first.1) :
    SelectedDualCycle web.annular.RS first where
  walk := selectedTriangleWalk hfirstSecond hsecondThird hthirdFirst
  isCycle := selectedTriangleWalk_isCycle hfirstSecond hsecondThird hthirdFirst
  crossingEdge := fun step =>
    if step.val = 0 then firstSecondEdge
    else if step.val = 1 then secondThirdEdge
    else thirdFirstEdge
  crossing_mem_shared := by
    intro step
    have hlt : step.val < 3 := by
      simpa using step.isLt
    interval_cases hstep : step.val <;>
      simp [selectedTriangleWalk, hfirstSecondEdge,
        hsecondThirdEdge, hthirdFirstEdge]

/-- A literal selected facial-dual triangle around one endpoint of the
two-vertex bond.  The stepwise incidence field is stronger than merely saying
that the crossing finset has size three: it identifies the common primal
centre without any cyclic-cut argument. -/
structure SquareBondRealization.EndpointSelectedTriangle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  start : SelectedFace (web := web)
  selectedCycle : SelectedDualCycle web.annular.RS start
  center : V
  center_mem_internal : center ∈ bond.internalEdge.1
  length_eq_three : selectedCycle.walk.length = 3
  support_original : ∀ current ∈ selectedCycle.walk.support,
    current ∈ cycle.walk.support
  crossingEdge_meets_center : ∀ step,
    center ∈ (selectedCycle.crossingEdge step).1
  incidentEdgeFinset_card_eq_three :
    (incidentEdgeFinset G center).card = 3

/-- The three explicitly selected crossings are exactly all primal edges at
the endpoint centre. -/
theorem SquareBondRealization.EndpointSelectedTriangle.crossingEdges_eq_incidentEdgeFinset
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle) :
    triangle.selectedCycle.crossingEdges =
      incidentEdgeFinset G triangle.center := by
  apply Finset.eq_of_subset_of_card_le
  · intro edge hedge
    rcases (triangle.selectedCycle.mem_crossingEdges_iff edge).1 hedge with
      ⟨step, hstep⟩
    have hcenter := triangle.crossingEdge_meets_center step
    rw [hstep] at hcenter
    simpa [incidentEdgeFinset] using hcenter
  · rw [triangle.incidentEdgeFinset_card_eq_three,
      triangle.selectedCycle.card_crossingEdges_eq_length
        (orbitFace_incidence_le_two web.annular.RS),
      triangle.length_eq_three]

/-- Every two distinct faces on an endpoint triangle are adjacent.  Thus, once
a later collision consumer identifies its two surviving attachment faces in
this support, the third face can be bypassed by one literal dual edge. -/
theorem SquareBondRealization.EndpointSelectedTriangle.adj_of_mem_support_of_ne
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    {first second : SelectedFace (web := web)}
    (hfirst : first ∈ triangle.selectedCycle.walk.support)
    (hsecond : second ∈ triangle.selectedCycle.walk.support)
    (hne : first ≠ second) :
    SelectedDualGraph (web := web).Adj first second := by
  have hcycle := triangle.selectedCycle.isCycle
  have hlength := triangle.length_eq_three
  cases hwalk : triangle.selectedCycle.walk with
  | nil => simp [hwalk] at hlength
  | cons hfirstSecond tail =>
      cases tail with
      | nil => simp [hwalk] at hlength
      | cons hsecondThird tail =>
          cases tail with
          | nil => simp [hwalk] at hlength
          | cons hthirdFirst tail =>
              cases tail with
              | nil =>
                  simp only [hwalk, SimpleGraph.Walk.support_cons,
                    SimpleGraph.Walk.support_nil, List.mem_cons,
                    List.not_mem_nil, or_false] at hfirst hsecond
                  rcases hfirst with rfl | rfl | rfl | rfl <;>
                    rcases hsecond with rfl | rfl | rfl | rfl <;>
                    simp_all [SimpleGraph.Walk.isCycle_def] <;>
                    first | assumption | (symm; assumption)
              | cons hfourth tail => simp [hwalk] at hlength

/-- Removing any chosen face from an endpoint triangle leaves its other two
faces joined by one dual edge.  This is the complete local bypass geometry;
a later rail consumer must still identify those two faces with the actual
predecessor and successor of its collision. -/
theorem SquareBondRealization.EndpointSelectedTriangle.exists_bypass_faces
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    {current : SelectedFace (web := web)}
    (hcurrent : current ∈ triangle.selectedCycle.walk.support) :
    ∃ first second : SelectedFace (web := web),
      first ∈ triangle.selectedCycle.walk.support ∧
        second ∈ triangle.selectedCycle.walk.support ∧
        first ≠ current ∧ second ≠ current ∧ first ≠ second ∧
        SelectedDualGraph (web := web).Adj current first ∧
        SelectedDualGraph (web := web).Adj current second ∧
        SelectedDualGraph (web := web).Adj first second := by
  have hlength := triangle.length_eq_three
  cases hwalk : triangle.selectedCycle.walk with
  | nil => simp [hwalk] at hlength
  | cons hfirstSecond tail =>
      cases tail with
      | nil => simp [hwalk] at hlength
      | cons hsecondThird tail =>
          cases tail with
          | nil => simp [hwalk] at hlength
          | cons hthirdFirst tail =>
              cases tail with
              | nil =>
                  simp only [hwalk, SimpleGraph.Walk.support_cons,
                    SimpleGraph.Walk.support_nil, List.mem_cons,
                    List.not_mem_nil, or_false] at hcurrent
                  rcases hcurrent with rfl | rfl | rfl | rfl
                  · refine ⟨_, _, by simp, by simp,
                      hfirstSecond.ne.symm, hthirdFirst.ne,
                      hsecondThird.ne, hfirstSecond, hthirdFirst.symm,
                      hsecondThird⟩
                  · refine ⟨_, _, by simp, by simp,
                      hfirstSecond.ne, hsecondThird.ne.symm,
                      hthirdFirst.ne.symm, hfirstSecond.symm, hsecondThird,
                      hthirdFirst.symm⟩
                  · refine ⟨_, _, by simp, by simp,
                      hsecondThird.ne, hthirdFirst.ne.symm,
                      hfirstSecond.ne.symm, hsecondThird.symm, hthirdFirst,
                      hfirstSecond.symm⟩
                  · refine ⟨_, _, by simp, by simp,
                      hfirstSecond.ne.symm, hthirdFirst.ne,
                      hsecondThird.ne, hfirstSecond, hthirdFirst.symm,
                      hsecondThird⟩
              | cons hfourth tail => simp [hwalk] at hlength

/-- The incident stars of the two bond endpoints overlap in exactly the
internal bond.  This is a simple-graph fact: an edge incident to both distinct
endpoints is the bond itself. -/
theorem SquareBondRealization.incidentEdgeFinset_inter_eq_singleton_internalEdge
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) :
    incidentEdgeFinset G bond.first ∩ incidentEdgeFinset G bond.second =
      {bond.internalEdge} := by
  classical
  ext edge
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hfirstIncident, hsecondIncident⟩
    apply Subtype.ext
    have hfirst : bond.first ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hfirstIncident
    have hsecond : bond.second ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hsecondIncident
    exact Sym2.eq_of_ne_mem bond.first_ne_second hfirst hsecond
      (by simp [SquareBondRealization.internalEdge, Sym2.mem_iff])
      (by simp [SquareBondRealization.internalEdge, Sym2.mem_iff])
  · rintro rfl
    simp [SquareBondRealization.internalEdge, incidentEdgeFinset, Sym2.mem_iff]

/-- The two endpoint stars cover precisely the selected four-edge square
boundary together with the internal bond.  No other primal crossing is
introduced by the endpoint-triangle construction. -/
theorem SquareBondRealization.incidentEdgeFinset_union_eq_insert_internalEdge
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    incidentEdgeFinset G bond.first ∪ incidentEdgeFinset G bond.second =
      insert bond.internalEdge cycle.selectedCycle.crossingEdges := by
  classical
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_union.1 hedge with hfirst | hsecond
    · by_cases heq : edge = bond.internalEdge
      · exact Finset.mem_insert.2 (.inl heq)
      · apply Finset.mem_insert.2
        apply Or.inr
        have herase : edge ∈
            (incidentEdgeFinset G bond.first).erase bond.internalEdge :=
          Finset.mem_erase.2 ⟨heq, hfirst⟩
        rw [← bond.filter_incident_first_eq_erase_internalEdge hroot] at herase
        exact (Finset.mem_filter.1 herase).2
    · by_cases heq : edge = bond.internalEdge
      · exact Finset.mem_insert.2 (.inl heq)
      · apply Finset.mem_insert.2
        apply Or.inr
        have herase : edge ∈
            (incidentEdgeFinset G bond.second).erase bond.internalEdge :=
          Finset.mem_erase.2 ⟨heq, hsecond⟩
        rw [← bond.filter_incident_second_eq_erase_internalEdge hroot] at herase
        exact (Finset.mem_filter.1 herase).2
  · intro hedge
    rcases Finset.mem_insert.1 hedge with heq | hcrossing
    · subst edge
      exact Finset.mem_union.2 (.inl (by
        simp [SquareBondRealization.internalEdge, incidentEdgeFinset,
          Sym2.mem_iff]))
    · rcases bond.covers_crossingEdges edge hcrossing with hfirst | hsecond
      · exact Finset.mem_union.2 (.inl (by
          simpa [incidentEdgeFinset] using hfirst))
      · exact Finset.mem_union.2 (.inr (by
          simpa [incidentEdgeFinset] using hsecond))

/-- If two endpoint triangles have the exact crossing-edge union, then their
face supports cover the original square-cycle support.  At a visited square
face, choose an incident selected crossing; the union receipt assigns that
crossing to one endpoint triangle, and local two-sidedness puts the face on
that triangle. -/
theorem SquareBondRealization.original_support_covered_by_endpointTriangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hunion : firstTriangle.selectedCycle.crossingEdges ∪
        secondTriangle.selectedCycle.crossingEdges =
      insert bond.internalEdge cycle.selectedCycle.crossingEdges) :
    ∀ current ∈ cycle.walk.support,
      current ∈ firstTriangle.selectedCycle.walk.support ∨
        current ∈ secondTriangle.selectedCycle.walk.support := by
  intro current hcurrent
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hcurrent with
    ⟨index, hindex, hindexLe⟩
  have hpositive : 0 < cycle.walk.length := by
    rcases cycle.length_eq_three_or_four with hthree | hfour <;> omega
  by_cases hindexLt : index < cycle.walk.length
  · let step : Fin cycle.walk.length := ⟨index, hindexLt⟩
    have hget : cycle.walk.getVert step.val = current := by
      exact hindex
    let edge := cycle.selectedCycle.crossingEdge step
    have hedgeOriginal : edge ∈ cycle.selectedCycle.crossingEdges :=
      (cycle.selectedCycle.mem_crossingEdges_iff edge).2 ⟨step, rfl⟩
    have hedgePair : edge ∈ firstTriangle.selectedCycle.crossingEdges ∪
        secondTriangle.selectedCycle.crossingEdges := by
      rw [hunion]
      exact Finset.mem_insert.2 (.inr hedgeOriginal)
    have hboundary : edge ∈ orbitFaceBoundary web.annular.RS current.1 := by
      have hleft := cycle.selectedCycle.crossingEdge_mem_leftFace step
      simpa only [MiddleReplacementShortDualCycle.selectedCycle_walk, hget] using hleft
    rcases Finset.mem_union.1 hedgePair with hfirst | hsecond
    · exact .inl (by
        simpa using face_mem_support_of_mem_crossingEdges_of_mem_boundary
          firstTriangle.selectedCycle hfirst hboundary)
    · exact .inr (by
        simpa using face_mem_support_of_mem_crossingEdges_of_mem_boundary
          secondTriangle.selectedCycle hsecond hboundary)
  · have hindexEq : index = cycle.walk.length :=
      Nat.le_antisymm hindexLe (Nat.le_of_not_gt hindexLt)
    subst index
    let step : Fin cycle.walk.length := ⟨0, hpositive⟩
    have hget : cycle.walk.getVert step.val = current := by
      simpa [step] using hindex
    let edge := cycle.selectedCycle.crossingEdge step
    have hedgeOriginal : edge ∈ cycle.selectedCycle.crossingEdges :=
      (cycle.selectedCycle.mem_crossingEdges_iff edge).2 ⟨step, rfl⟩
    have hedgePair : edge ∈ firstTriangle.selectedCycle.crossingEdges ∪
        secondTriangle.selectedCycle.crossingEdges := by
      rw [hunion]
      exact Finset.mem_insert.2 (.inr hedgeOriginal)
    have hboundary : edge ∈ orbitFaceBoundary web.annular.RS current.1 := by
      have hleft := cycle.selectedCycle.crossingEdge_mem_leftFace step
      simpa only [MiddleReplacementShortDualCycle.selectedCycle_walk, hget] using hleft
    rcases Finset.mem_union.1 hedgePair with hfirst | hsecond
    · exact .inl (by
        simpa using face_mem_support_of_mem_crossingEdges_of_mem_boundary
          firstTriangle.selectedCycle hfirst hboundary)
    · exact .inr (by
        simpa using face_mem_support_of_mem_crossingEdges_of_mem_boundary
          secondTriangle.selectedCycle hsecond hboundary)

/-- The oriented internal bond and the two following darts at its first cubic
endpoint form a literal selected dual triangle whose three primal crossings
all meet that endpoint. -/
theorem SquareBondRealization.InternalDualAdjacency.exists_firstEndpointSelectedTriangle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (adjacency : bond.InternalDualAdjacency)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ triangle : bond.EndpointSelectedTriangle,
      triangle.center = bond.first := by
  let RS := web.annular.RS
  let central := adjacency.central
  let firstFace := adjacency.leftFace
  let secondFace := adjacency.rightFace
  let firstOuter := RS.rho central
  let secondOuter := RS.rho firstOuter
  let middleFace : SelectedFace (web := web) :=
    ⟨dartOrbitFace RS (RS.alpha firstOuter), Finset.mem_univ _⟩
  have hcentralInterior : dartOrbitFace RS central ∈
      web.annular.cellulation.interiorFaces := by
    rw [← adjacency.leftFace_eq]
    exact cycle.support_internal adjacency.leftFace
      adjacency.left_mem_support
  have hincidentFirst :
      (incidentEdgeFinset G bond.first).card = 3 := by
    have hcard := web.incidentEdgeFinset_card_eq_three_of_dartOrbitFace_mem_interiorFaces
      hcentralInterior
    change (incidentEdgeFinset G central.fst).card = 3 at hcard
    rw [adjacency.central_fst] at hcard
    exact hcard
  have hcard : (RS.dartsAt (RS.vertOf central)).card = 3 := by
    apply Instance.dartsAt_card_eq_three_of_dartOrbitFace_mem_interiorFaces
    exact hcentralInterior
  have hcube : RS.rho (RS.rho (RS.rho central)) = central :=
    rho_cube_apply_of_dartsAt_card_eq_three RS
      (Instance.InteriorFace.vertexRotationCyclic web) central hcard
  have hfirstOuterFst : firstOuter.fst = bond.first := by
    calc
      firstOuter.fst = central.fst := by
        simpa [RS, firstOuter, central,
          Data.toRotationSystem_vertOf] using RS.vert_rho central
      _ = bond.first := adjacency.central_fst
  have hsecondOuterFst : secondOuter.fst = bond.first := by
    calc
      secondOuter.fst = firstOuter.fst := by
        simpa [RS, secondOuter, Data.toRotationSystem_vertOf] using
          RS.vert_rho firstOuter
      _ = bond.first := hfirstOuterFst
  have hfirstOuterIncident : RS.edgeOf firstOuter ∈
      incidentEdgeFinset G bond.first := by
    simpa only [RS, Data.toRotationSystem_edgeOf] using
      firstOuter.edgeSet_mem_incidentEdgeFinset_of_fst_eq hfirstOuterFst
  have hsecondOuterIncident : RS.edgeOf secondOuter ∈
      incidentEdgeFinset G bond.first := by
    simpa only [RS, Data.toRotationSystem_edgeOf] using
      secondOuter.edgeSet_mem_incidentEdgeFinset_of_fst_eq hsecondOuterFst
  have hfirstOuterNe : RS.edgeOf firstOuter ≠ bond.internalEdge := by
    have hne : RS.edgeOf (RS.rho central) ≠ RS.edgeOf central :=
      edgeOf_rho_ne_edgeOf_of_dartsAt_card_eq_three web
        (Instance.InteriorFace.vertexRotationCyclic web) central hcard
    intro heq
    apply hne
    exact heq.trans adjacency.central_edge.symm
  have hsecondOuterNe : RS.edgeOf secondOuter ≠ bond.internalEdge := by
    have hcardSecond :
        (RS.dartsAt (RS.vertOf secondOuter)).card = 3 := by
      simpa [secondOuter, firstOuter, RS.vert_rho] using hcard
    have hne := edgeOf_rho_ne_edgeOf_of_dartsAt_card_eq_three web
      (Instance.InteriorFace.vertexRotationCyclic web) secondOuter hcardSecond
    have hrhoSecond : RS.rho secondOuter = central := by
      simpa [secondOuter, firstOuter] using hcube
    rw [hrhoSecond] at hne
    exact fun heq => hne (adjacency.central_edge.trans heq.symm)
  have hfirstOuterCrossing : RS.edgeOf firstOuter ∈
      cycle.selectedCycle.crossingEdges := by
    have herase : RS.edgeOf firstOuter ∈
        (incidentEdgeFinset G bond.first).erase bond.internalEdge :=
      Finset.mem_erase.2 ⟨hfirstOuterNe, hfirstOuterIncident⟩
    rw [← bond.filter_incident_first_eq_erase_internalEdge hroot] at herase
    exact (Finset.mem_filter.1 herase).2
  have hsecondOuterCrossing : RS.edgeOf secondOuter ∈
      cycle.selectedCycle.crossingEdges := by
    have herase : RS.edgeOf secondOuter ∈
        (incidentEdgeFinset G bond.first).erase bond.internalEdge :=
      Finset.mem_erase.2 ⟨hsecondOuterNe, hsecondOuterIncident⟩
    rw [← bond.filter_incident_first_eq_erase_internalEdge hroot] at herase
    exact (Finset.mem_filter.1 herase).2
  have hfirstOuterInterior : RS.edgeOf firstOuter ∈ interiorEdgeSupport
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) := by
    rcases (cycle.selectedCycle.mem_crossingEdges_iff _).1
        hfirstOuterCrossing with ⟨step, hstep⟩
    have hshared := cycle.selectedCycle.crossing_mem_shared step
    rw [hstep] at hshared
    exact (mem_sharedInteriorEdges_iff _ _).1 hshared |>.1
  have hsecondOuterInterior : RS.edgeOf secondOuter ∈ interiorEdgeSupport
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) := by
    rcases (cycle.selectedCycle.mem_crossingEdges_iff _).1
        hsecondOuterCrossing with ⟨step, hstep⟩
    have hshared := cycle.selectedCycle.crossing_mem_shared step
    rw [hstep] at hshared
    exact (mem_sharedInteriorEdges_iff _ _).1 hshared |>.1
  have hfirstOuterOwn : dartOrbitFace RS firstOuter = secondFace.1 := by
    have hphi := dartOrbitFace_phi_eq RS (RS.alpha central)
    calc
      dartOrbitFace RS firstOuter =
          dartOrbitFace RS (RS.alpha central) := by
        simpa [firstOuter, RotationSystem.phi_apply,
          RS.alpha_involutive] using hphi
      _ = secondFace.1 := adjacency.rightFace_eq.symm
  have hsecondOuterOwn : dartOrbitFace RS secondOuter = middleFace.1 := by
    have hphi := dartOrbitFace_phi_eq RS (RS.alpha firstOuter)
    simpa [secondOuter, middleFace, RotationSystem.phi_apply,
      RS.alpha_involutive] using hphi
  have hsecondOuterOpposite :
      dartOrbitFace RS (RS.alpha secondOuter) = firstFace.1 := by
    have hphi := dartOrbitFace_phi_eq RS (RS.alpha secondOuter)
    have hraw : dartOrbitFace RS central =
        dartOrbitFace RS (RS.alpha secondOuter) := by
      simpa [secondOuter, firstOuter, RotationSystem.phi_apply,
        RS.alpha_involutive, hcube] using hphi
    exact hraw.symm.trans adjacency.leftFace_eq.symm
  have hmiddleSupport : middleFace ∈ cycle.walk.support := by
    apply face_mem_support_of_mem_crossingEdges_of_mem_boundary
      cycle.selectedCycle hfirstOuterCrossing
    change RS.edgeOf firstOuter ∈ orbitFaceBoundary RS middleFace.1
    simpa [RS.edge_alpha] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha firstOuter)
  have hsecondMiddleNe : secondFace ≠ middleFace := by
    have hsecondInterior := cycle.support_internal secondFace
      adjacency.right_mem_support
    have hne := Instance.dartOrbitFace_ne_alpha_of_mem_interiorFaces
      web firstOuter (by rw [hfirstOuterOwn]; exact hsecondInterior)
    intro heq
    apply hne
    rw [hfirstOuterOwn]
    exact congrArg Subtype.val heq
  have hmiddleFirstNe : middleFace ≠ firstFace := by
    have hmiddleInterior := cycle.support_internal middleFace hmiddleSupport
    have hne := Instance.dartOrbitFace_ne_alpha_of_mem_interiorFaces
      web secondOuter (by rw [hsecondOuterOwn]; exact hmiddleInterior)
    intro heq
    apply hne
    rw [hsecondOuterOwn, hsecondOuterOpposite]
    exact congrArg Subtype.val heq
  have hinternalShared : bond.internalEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      firstFace.1 secondFace.1 := by
    exact adjacency.internal_mem_shared
  have hfirstOuterShared : RS.edgeOf firstOuter ∈ sharedInteriorEdges
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      secondFace.1 middleFace.1 := by
    apply (mem_sharedInteriorEdges_iff _ _).2
    refine ⟨hfirstOuterInterior, ?_, ?_⟩
    · rw [← hfirstOuterOwn]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS firstOuter
    · simpa [RS.edge_alpha] using
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha firstOuter)
  have hsecondOuterShared : RS.edgeOf secondOuter ∈ sharedInteriorEdges
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      middleFace.1 firstFace.1 := by
    apply (mem_sharedInteriorEdges_iff _ _).2
    refine ⟨hsecondOuterInterior, ?_, ?_⟩
    · rw [← hsecondOuterOwn]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS secondOuter
    · rw [← hsecondOuterOpposite]
      simpa [RS.edge_alpha] using
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha secondOuter)
  have hfirstSecond : SelectedDualGraph (web := web).Adj
      firstFace secondFace := adjacency.adjacent
  have hsecondMiddle : SelectedDualGraph (web := web).Adj
      secondFace middleFace :=
    (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty _ _).2
      ⟨by exact fun heq => hsecondMiddleNe (Subtype.ext heq),
        ⟨RS.edgeOf firstOuter, hfirstOuterShared⟩⟩
  have hmiddleFirst : SelectedDualGraph (web := web).Adj
      middleFace firstFace :=
    (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty _ _).2
      ⟨by exact fun heq => hmiddleFirstNe (Subtype.ext heq),
        ⟨RS.edgeOf secondOuter, hsecondOuterShared⟩⟩
  let triangle := selectedTriangle hfirstSecond hsecondMiddle hmiddleFirst
    bond.internalEdge (RS.edgeOf firstOuter) (RS.edgeOf secondOuter)
    hinternalShared hfirstOuterShared hsecondOuterShared
  refine ⟨{
    start := firstFace
    selectedCycle := triangle
    center := bond.first
    center_mem_internal := by
      simp [SquareBondRealization.internalEdge, Sym2.mem_iff]
    length_eq_three := by simp [triangle, selectedTriangle]
    support_original := by
      intro current hcurrent
      simp [triangle, selectedTriangle, selectedTriangleWalk] at hcurrent
      rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent
      · simpa [firstFace, hcurrent] using adjacency.left_mem_support
      · simpa [secondFace, hcurrent] using adjacency.right_mem_support
      · simpa [hcurrent] using hmiddleSupport
      · simpa [firstFace, hcurrent] using adjacency.left_mem_support
    crossingEdge_meets_center := by
      intro step
      have hlt : step.val < 3 := by
        simpa [triangle, selectedTriangle] using step.isLt
      interval_cases hstep : step.val
      · simp [triangle, selectedTriangle, hstep,
          SquareBondRealization.internalEdge, Sym2.mem_iff]
      · simpa [triangle, selectedTriangle, hstep, incidentEdgeFinset,
          Sym2.mem_iff] using hfirstOuterIncident
      · simpa [triangle, selectedTriangle, hstep, incidentEdgeFinset,
          Sym2.mem_iff] using hsecondOuterIncident
    incidentEdgeFinset_card_eq_three := hincidentFirst
  }, rfl⟩

/-- Reversing the oriented internal bond and applying the same local rotation
calculation constructs the symmetric selected triangle at the second residue
vertex. -/
theorem SquareBondRealization.InternalDualAdjacency.exists_secondEndpointSelectedTriangle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (adjacency : bond.InternalDualAdjacency)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ triangle : bond.EndpointSelectedTriangle,
      triangle.center = bond.second := by
  let swapped : SquareBondRealization cycle component := {
    first := bond.second
    second := bond.first
    first_ne_second := bond.first_ne_second.symm
    component_supp := by simpa [Set.pair_comm] using bond.component_supp
    adjacent := bond.adjacent.symm
    covers_crossingEdges := by
      intro edge hedge
      rcases bond.covers_crossingEdges edge hedge with hfirst | hsecond
      · exact .inr hfirst
      · exact .inl hsecond
  }
  let reversed : swapped.InternalDualAdjacency := {
    central := web.annular.RS.alpha adjacency.central
    central_fst := by
      simpa [swapped, Data.toRotationSystem_alpha] using adjacency.central_snd
    central_snd := by
      simpa [swapped, Data.toRotationSystem_alpha] using adjacency.central_fst
    central_edge := by
      simpa [swapped, SquareBondRealization.internalEdge,
        web.annular.RS.edge_alpha, Sym2.eq_swap] using adjacency.central_edge
    leftFace := adjacency.rightFace
    rightFace := adjacency.leftFace
    leftFace_eq := adjacency.rightFace_eq
    rightFace_eq := by
      simpa [web.annular.RS.alpha_involutive] using adjacency.leftFace_eq
    left_mem_support := adjacency.right_mem_support
    right_mem_support := adjacency.left_mem_support
    faces_ne := adjacency.faces_ne.symm
    internal_mem_left := by
      simpa [swapped, SquareBondRealization.internalEdge, Sym2.eq_swap] using
        adjacency.internal_mem_right
    internal_mem_right := by
      simpa [swapped, SquareBondRealization.internalEdge, Sym2.eq_swap] using
        adjacency.internal_mem_left
    adjacent := adjacency.adjacent.symm
  }
  rcases reversed.exists_firstEndpointSelectedTriangle hroot with
    ⟨triangle, hcenter⟩
  let result : bond.EndpointSelectedTriangle := {
    start := triangle.start
    selectedCycle := triangle.selectedCycle
    center := triangle.center
    center_mem_internal := by
      simpa [swapped, SquareBondRealization.internalEdge, Sym2.eq_swap] using
        triangle.center_mem_internal
    length_eq_three := triangle.length_eq_three
    support_original := triangle.support_original
    crossingEdge_meets_center := triangle.crossingEdge_meets_center
    incidentEdgeFinset_card_eq_three :=
      triangle.incidentEdgeFinset_card_eq_three
  }
  exact ⟨result, by simpa [result, swapped] using hcenter⟩

/-- **L1 square-bond endpoint consumer.**  Every literal two-vertex square
residue constructs both endpoint triangles directly from its local cubic
rotation.  This bypasses the chord-versus-parallel-face classification for
the purpose of finding common primal centres, while making no rail-rerouting
claim. -/
theorem SquareBondRealization.exists_endpointSelectedTriangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ firstTriangle secondTriangle : bond.EndpointSelectedTriangle,
      firstTriangle.center = bond.first ∧
        secondTriangle.center = bond.second := by
  obtain ⟨adjacency⟩ := bond.exists_internalDualAdjacency hroot
  rcases adjacency.exists_firstEndpointSelectedTriangle hroot with
    ⟨firstTriangle, hfirst⟩
  rcases adjacency.exists_secondEndpointSelectedTriangle hroot with
    ⟨secondTriangle, hsecond⟩
  exact ⟨firstTriangle, secondTriangle, hfirst, hsecond⟩

/-- **L1 exact endpoint-triangle decomposition.**  The two constructed
triangles meet on exactly the internal bond and together cross exactly that
bond plus the original four selected square-boundary edges.  This is the
edge-level packet needed by a later rail reroute; it does not itself choose or
append either repaired rail. -/
theorem SquareBondRealization.exists_endpointSelectedTriangles_exact
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ firstTriangle secondTriangle : bond.EndpointSelectedTriangle,
      firstTriangle.center = bond.first ∧
        secondTriangle.center = bond.second ∧
        firstTriangle.selectedCycle.crossingEdges ∩
            secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge} ∧
        firstTriangle.selectedCycle.crossingEdges ∪
            secondTriangle.selectedCycle.crossingEdges =
          insert bond.internalEdge cycle.selectedCycle.crossingEdges := by
  rcases bond.exists_endpointSelectedTriangles hroot with
    ⟨firstTriangle, secondTriangle, hfirst, hsecond⟩
  refine ⟨firstTriangle, secondTriangle, hfirst, hsecond, ?_, ?_⟩
  · rw [firstTriangle.crossingEdges_eq_incidentEdgeFinset,
      secondTriangle.crossingEdges_eq_incidentEdgeFinset, hfirst, hsecond]
    exact bond.incidentEdgeFinset_inter_eq_singleton_internalEdge
  · rw [firstTriangle.crossingEdges_eq_incidentEdgeFinset,
      secondTriangle.crossingEdges_eq_incidentEdgeFinset, hfirst, hsecond]
    exact bond.incidentEdgeFinset_union_eq_insert_internalEdge hroot

/-- The exact endpoint decomposition also assigns the original collision face
to at least one endpoint triangle.  This is a face-level choice receipt for a
later reroute, not yet a choice of the surviving rail attachment on that
triangle. -/
theorem SquareBondRealization.exists_endpointSelectedTriangles_exact_with_face
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ firstTriangle secondTriangle : bond.EndpointSelectedTriangle,
      firstTriangle.center = bond.first ∧
        secondTriangle.center = bond.second ∧
        firstTriangle.selectedCycle.crossingEdges ∩
            secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge} ∧
        firstTriangle.selectedCycle.crossingEdges ∪
            secondTriangle.selectedCycle.crossingEdges =
          insert bond.internalEdge cycle.selectedCycle.crossingEdges ∧
        (face ∈ firstTriangle.selectedCycle.walk.support ∨
          face ∈ secondTriangle.selectedCycle.walk.support) := by
  rcases bond.exists_endpointSelectedTriangles_exact hroot with
    ⟨firstTriangle, secondTriangle, hfirst, hsecond, hinter, hunion⟩
  have hface := bond.original_support_covered_by_endpointTriangles
    firstTriangle secondTriangle hunion face cycle.face_mem_support
  exact ⟨firstTriangle, secondTriangle, hfirst, hsecond, hinter, hunion, hface⟩

/-- **L1 local square-collision bypass.**  The realized square supplies an
endpoint triangle containing the collision face, and deleting that face from
the triangle leaves two distinct support faces joined by one dual edge.  This
constructs the local bypass edge; it does not yet identify its endpoints with
the predecessor and successor on either retained rail. -/
theorem SquareBondRealization.exists_collisionEndpointTriangle_bypass
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ triangle : bond.EndpointSelectedTriangle,
      face ∈ triangle.selectedCycle.walk.support ∧
        ∃ first second : SelectedFace (web := web),
          first ∈ triangle.selectedCycle.walk.support ∧
            second ∈ triangle.selectedCycle.walk.support ∧
            first ≠ face ∧ second ≠ face ∧ first ≠ second ∧
            SelectedDualGraph (web := web).Adj face first ∧
            SelectedDualGraph (web := web).Adj face second ∧
            SelectedDualGraph (web := web).Adj first second := by
  rcases bond.exists_endpointSelectedTriangles_exact_with_face hroot with
    ⟨firstTriangle, secondTriangle, _hfirst, _hsecond, _hinter, _hunion,
      hface⟩
  rcases hface with hface | hface
  · exact ⟨firstTriangle, hface,
      firstTriangle.exists_bypass_faces hface⟩
  · exact ⟨secondTriangle, hface,
      secondTriangle.exists_bypass_faces hface⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
