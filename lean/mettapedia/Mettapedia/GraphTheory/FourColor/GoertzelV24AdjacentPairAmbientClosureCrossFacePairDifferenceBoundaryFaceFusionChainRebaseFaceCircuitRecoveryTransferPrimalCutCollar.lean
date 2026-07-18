import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutBond

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [decidableAdjacency : DecidableRel G.Adj]

noncomputable section

local instance collarFiniteGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency' : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency' vertex) inferInstance

attribute [local instance]
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

namespace GoertzelV24FiniteEdgeDeletion

omit [DecidableEq V] decidableAdjacency in
/-- A finite-deletion component with exactly two vertices is supported on
a unique unordered pair of distinct adjacent vertices. -/
theorem exists_adjacent_pair_of_component_card_eq_two
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 2) :
    ∃ first second : V,
      first ≠ second ∧ component.supp = {first, second} ∧
        G.Adj first second := by
  classical
  have hsuppCard : component.supp.ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  rcases Set.ncard_eq_two.mp hsuppCard with
    ⟨first, second, hfirstSecond, hsupp⟩
  have hfirstMem : first ∈ component.supp := by
    rw [hsupp]
    simp
  have hsecondMem : second ∈ component.supp := by
    rw [hsupp]
    simp
  let firstVertex : component.supp := ⟨first, hfirstMem⟩
  let secondVertex : component.supp := ⟨second, hsecondMem⟩
  have hverticesNe : firstVertex ≠ secondVertex := by
    intro heq
    exact hfirstSecond (congrArg Subtype.val heq)
  have hconnected :=
    connected_induce_delete_component removed component
  rcases hconnected.exists_isPath firstVertex secondVertex with
    ⟨path, hpath⟩
  have hsubtypeCard : Fintype.card component.supp = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlengthLt : path.length < 2 := by
    simpa [hsubtypeCard] using hpath.length_lt
  have hlengthPositive : 0 < path.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hverticesNe (path.eq_of_length_eq_zero hzero)
  have hlength : path.length = 1 := by omega
  have hadj : (G.induce component.supp).Adj firstVertex secondVertex :=
    path.adj_of_length_eq_one hlength
  exact ⟨first, second, hfirstSecond, hsupp, hadj⟩

end GoertzelV24FiniteEdgeDeletion

namespace GoertzelV24CubicSmallBoundaryCycle

omit [DecidableEq V] decidableAdjacency in
/-- The edge internal to an adjacent vertex pair does not cross the pair's
vertex side. -/
theorem adjacent_pair_internalEdge_not_mem_crossingEdgeFinset
    {first second : V} (hadj : G.Adj first second) :
    (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) ∉
      crossingEdgeFinset G
        (fun vertex => vertex ∈ ({first, second} : Set V)) := by
  intro hedge
  have hcross :=
    (mem_crossingEdgeFinset_iff
      (fun vertex => vertex ∈ ({first, second} : Set V)) _).1 hedge
  rcases hcross with
    ⟨inside, outside, _hinsideEdge, houtsideEdge,
      _hinsideSide, houtsideSide⟩
  apply houtsideSide
  simpa [Sym2.mem_iff] using houtsideEdge

/-- At either endpoint of an adjacent pair, the side-crossing incident
edges are exactly the incident edges other than the pair's internal edge. -/
theorem filter_incidentEdgeFinset_crossing_pair_eq_erase_internalEdge
    {first second : V} (hadj : G.Adj first second) :
    (incidentEdgeFinset G first).filter
        (fun edge => edge ∈ crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V))) =
      (incidentEdgeFinset G first).erase
        (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ :
          G.edgeSet) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hincident, hcrossing⟩
    refine ⟨?_, hincident⟩
    intro hedge
    subst edge
    exact adjacent_pair_internalEdge_not_mem_crossingEdgeFinset hadj
      hcrossing
  · rintro ⟨hedgeNe, hincident⟩
    refine ⟨hincident, ?_⟩
    have hfirstEdge : first ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hincident
    rcases Sym2.mem_iff_exists.1 hfirstEdge with ⟨other, hedgeValue⟩
    have hfirstOther : G.Adj first other := by
      rw [← SimpleGraph.mem_edgeSet G, ← hedgeValue]
      exact edge.2
    have hotherNeFirst : other ≠ first := hfirstOther.ne.symm
    have hotherNeSecond : other ≠ second := by
      intro hother
      subst other
      apply hedgeNe
      apply Subtype.ext
      exact hedgeValue
    apply (mem_crossingEdgeFinset_iff
      (fun vertex => vertex ∈ ({first, second} : Set V)) edge).2
    refine ⟨first, other, hfirstEdge, ?_, by simp, ?_⟩
    · rw [hedgeValue]
      simp
    · simp [hotherNeFirst, hotherNeSecond]

/-- Cubicity makes the preceding endpoint boundary consist of exactly two
edges. -/
theorem card_filter_incidentEdgeFinset_crossing_pair_eq_two_of_cubic
    (hregular : G.IsRegularOfDegree 3)
    {first second : V} (hadj : G.Adj first second) :
    ((incidentEdgeFinset G first).filter
      (fun edge => edge ∈ crossingEdgeFinset G
        (fun vertex => vertex ∈ ({first, second} : Set V)))).card = 2 := by
  classical
  rw [filter_incidentEdgeFinset_crossing_pair_eq_erase_internalEdge hadj]
  have hinternal :
      (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ :
          G.edgeSet) ∈ incidentEdgeFinset G first := by
    simp [incidentEdgeFinset, Sym2.mem_iff]
  rw [Finset.card_erase_of_mem hinternal,
    incidentEdgeFinset_card_eq_degree, hregular.degree_eq]

end GoertzelV24CubicSmallBoundaryCycle

namespace GoertzelV24DualCycleCollar

/-- A face incident to a crossed edge of a facial-dual walk occurs in the
support of that walk. -/
theorem face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start finish)
    {edge : G.edgeSet} {face : OrbitFace data.toRotationSystem}
    (hedge : edge ∈ dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (hface : edge ∈ orbitFaceBoundary data.toRotationSystem face) :
    (⟨face, Finset.mem_univ face⟩ : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        walk.support := by
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      edge).1 hedge with
    ⟨step, hstep⟩
  let left := walk.getVert step.val
  let right := walk.getVert (step.val + 1)
  have hadj := walk.adj_getVert_succ step.isLt
  have hleftRight : left.1 ≠ right.1 := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary data.toRotationSystem left.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      step
  have hright : edge ∈ orbitFaceBoundary data.toRotationSystem right.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      step
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) left.2 right.2
      (Finset.mem_univ face) hleftRight hleft hright hface
  rcases hcases with hfaceLeft | hfaceRight
  · have hvertices :
        (⟨face, Finset.mem_univ face⟩ : AmbientFace
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))) = left :=
      Subtype.ext hfaceLeft
    rw [hvertices]
    exact walk.getVert_mem_support step.val
  · have hvertices :
        (⟨face, Finset.mem_univ face⟩ : AmbientFace
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))) = right :=
      Subtype.ext hfaceRight
    rw [hvertices]
    exact walk.getVert_mem_support (step.val + 1)

/-- In a cubic cyclic vertex rotation, advancing one dart around its vertex
changes the underlying graph edge. -/
theorem edgeOf_rho_ne_edgeOf_of_isCubic
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (dart : G.Dart) :
    data.toRotationSystem.edgeOf (data.toRotationSystem.rho dart) ≠
      data.toRotationSystem.edgeOf dart := by
  intro hedge
  have hfst : (data.toRotationSystem.rho dart).fst = dart.fst := by
    simpa only [Data.toRotationSystem_vertOf] using
      data.toRotationSystem.vert_rho dart
  have hedgeValue :
      (data.toRotationSystem.rho dart).edge = dart.edge := by
    simpa only [Data.toRotationSystem_edgeOf] using congrArg Subtype.val hedge
  have hdart : data.toRotationSystem.rho dart = dart :=
    SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq _ _ hfst hedgeValue
  exact
    (GoertzelV24AdjacentPairBoundary.AdjacentPairData.rho_triple_pairwise_ne
      data.toRotationSystem hcubic hrotation dart).1 hdart.symm

/-- The first rotation away from either orientation of an adjacent pair's
internal dart is one of the four edges crossing the pair boundary. -/
theorem rho_edges_mem_crossingEdgeFinset_pair
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {first second : V} (hadj : G.Adj first second) :
    let central : G.Dart := ⟨(first, second), hadj⟩
    data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho central) ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) ∧
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) := by
  dsimp only
  let central : G.Dart := ⟨(first, second), hadj⟩
  let internalEdge : G.edgeSet :=
    ⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩
  have hfirstFst :
      (data.toRotationSystem.rho central).fst = first := by
    calc
      (data.toRotationSystem.rho central).fst = central.fst := by
        simpa only [Data.toRotationSystem_vertOf] using
          data.toRotationSystem.vert_rho central
      _ = first := rfl
  have hfirstIncident :
      data.toRotationSystem.edgeOf (data.toRotationSystem.rho central) ∈
        incidentEdgeFinset G first := by
    simpa only [Data.toRotationSystem_edgeOf] using
      (data.toRotationSystem.rho central).edgeSet_mem_incidentEdgeFinset_of_fst_eq
        hfirstFst
  have hfirstNe :
      data.toRotationSystem.edgeOf (data.toRotationSystem.rho central) ≠
        internalEdge := by
    simpa [internalEdge, central, Data.toRotationSystem_edgeOf] using
      edgeOf_rho_ne_edgeOf_of_isCubic data hcubic hrotation central
  have hfirstErase :
      data.toRotationSystem.edgeOf (data.toRotationSystem.rho central) ∈
        (incidentEdgeFinset G first).erase internalEdge :=
    Finset.mem_erase.2 ⟨hfirstNe, hfirstIncident⟩
  have hfirstCrossing :
      data.toRotationSystem.edgeOf (data.toRotationSystem.rho central) ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) := by
    have hfiltered := hfirstErase
    rw [← filter_incidentEdgeFinset_crossing_pair_eq_erase_internalEdge hadj]
      at hfiltered
    exact (Finset.mem_filter.1 hfiltered).2
  have hsecondFst :
      (data.toRotationSystem.rho
          (data.toRotationSystem.alpha central)).fst = second := by
    calc
      (data.toRotationSystem.rho
          (data.toRotationSystem.alpha central)).fst =
          (data.toRotationSystem.alpha central).fst := by
        simpa only [Data.toRotationSystem_vertOf] using
          data.toRotationSystem.vert_rho
            (data.toRotationSystem.alpha central)
      _ = second := rfl
  have hsecondIncident :
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ∈
        incidentEdgeFinset G second := by
    simpa only [Data.toRotationSystem_edgeOf] using
      (data.toRotationSystem.rho
          (data.toRotationSystem.alpha central)).edgeSet_mem_incidentEdgeFinset_of_fst_eq
        hsecondFst
  have hsecondNe :
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ≠ internalEdge := by
    have hne := edgeOf_rho_ne_edgeOf_of_isCubic data hcubic hrotation
      (data.toRotationSystem.alpha central)
    simpa [internalEdge, central, Data.toRotationSystem_edgeOf,
      Data.toRotationSystem_alpha, Sym2.eq_swap] using hne
  have hsecondErase :
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ∈
        (incidentEdgeFinset G second).erase internalEdge :=
    Finset.mem_erase.2 ⟨hsecondNe, hsecondIncident⟩
  have hsecondEraseReversed :
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ∈
        (incidentEdgeFinset G second).erase
          (⟨s(second, first),
            (SimpleGraph.mem_edgeSet G).2 hadj.symm⟩ : G.edgeSet) := by
    simpa [internalEdge, Sym2.eq_swap] using hsecondErase
  have hsecondCrossingReversed :
      data.toRotationSystem.edgeOf
          (data.toRotationSystem.rho
            (data.toRotationSystem.alpha central)) ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ ({second, first} : Set V)) := by
    have hfiltered := hsecondEraseReversed
    rw [← filter_incidentEdgeFinset_crossing_pair_eq_erase_internalEdge
      hadj.symm] at hfiltered
    exact (Finset.mem_filter.1 hfiltered).2
  have hpairs : ({second, first} : Set V) = {first, second} := by
    ext vertex
    simp [or_comm]
  rw [hpairs] at hsecondCrossingReversed
  exact ⟨hfirstCrossing, hsecondCrossingReversed⟩

/-- If a facial-dual walk is the exact boundary of an adjacent vertex pair,
the pair's internal edge joins two distinct faces on the walk while not
being one of its crossing edges. Thus it is an off-walk edge of the full
facial dual between two vertices of the walk support. -/
theorem exists_internal_dual_chord_of_adjacent_pair_boundary_eq
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start finish)
    {first second : V} (hadj : G.Adj first second)
    (hboundary :
      crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) =
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ internalEdge : G.edgeSet,
      ∃ leftFace rightFace : AmbientFace
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        internalEdge.1 = s(first, second) ∧
          internalEdge ∉ removed ∧
          leftFace ∈ walk.support ∧ rightFace ∈ walk.support ∧
          leftFace ≠ rightFace ∧
          internalEdge ∈
            orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
          internalEdge ∈
            orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
          (interiorDualGraph
            (orbitFaceBoundary data.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace data.toRotationSystem))).Adj leftFace rightFace := by
  dsimp only
  let RS := data.toRotationSystem
  let central : G.Dart := ⟨(first, second), hadj⟩
  let internalEdge : G.edgeSet := RS.edgeOf central
  let leftFace : AmbientFace
      (Finset.univ : Finset (OrbitFace RS)) :=
    ⟨dartOrbitFace RS central, Finset.mem_univ _⟩
  let rightFace : AmbientFace
      (Finset.univ : Finset (OrbitFace RS)) :=
    ⟨dartOrbitFace RS (RS.alpha central), Finset.mem_univ _⟩
  have hinternalValue : internalEdge.1 = s(first, second) := by
    rfl
  have hinternalNotRemoved :
      internalEdge ∉ dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk := by
    rw [← hboundary]
    simpa [internalEdge, central, RS, Data.toRotationSystem_edgeOf] using
      adjacent_pair_internalEdge_not_mem_crossingEdgeFinset hadj
  have hrhoCrossing := rho_edges_mem_crossingEdgeFinset_pair
    data hcubic hrotation hadj
  have hfirstRemoved :
      RS.edgeOf (RS.rho central) ∈ dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk := by
    rw [← hboundary]
    simpa [RS, central] using hrhoCrossing.1
  have hsecondRemoved :
      RS.edgeOf (RS.rho (RS.alpha central)) ∈ dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk := by
    rw [← hboundary]
    simpa [RS, central] using hrhoCrossing.2
  have hleftInternal :
      internalEdge ∈ orbitFaceBoundary RS leftFace.1 := by
    simpa [internalEdge, leftFace] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS central
  have hrightInternal :
      internalEdge ∈ orbitFaceBoundary RS rightFace.1 := by
    simpa [internalEdge, rightFace, RS.edge_alpha] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha central)
  have hleftExternal :
      RS.edgeOf (RS.rho (RS.alpha central)) ∈
        orbitFaceBoundary RS leftFace.1 := by
    have hmem :=
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.phi central)
    rw [dartOrbitFace_phi_eq RS central] at hmem
    simpa [leftFace, RotationSystem.phi_apply] using hmem
  have hrightExternal :
      RS.edgeOf (RS.rho central) ∈
        orbitFaceBoundary RS rightFace.1 := by
    have hmem := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
      (RS.phi (RS.alpha central))
    rw [dartOrbitFace_phi_eq RS (RS.alpha central)] at hmem
    simpa [rightFace, RotationSystem.phi_apply, RS.alpha_involutive] using
      hmem
  have hleftSupport : leftFace ∈ walk.support := by
    have hmem := face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      data hunique walk hsecondRemoved hleftExternal
    simpa [leftFace, RS] using hmem
  have hrightSupport : rightFace ∈ walk.support := by
    have hmem := face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      data hunique walk hfirstRemoved hrightExternal
    simpa [rightFace, RS] using hmem
  have hfacesValueNe : leftFace.1 ≠ rightFace.1 := by
    simpa [leftFace, rightFace, RS, Data.toRotationSystem_alpha] using
      htwoSided central
  have hfacesNe : leftFace ≠ rightFace := by
    intro hfaces
    exact hfacesValueNe (congrArg Subtype.val hfaces)
  have hadjDual :
      (interiorDualGraph
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem))).Adj leftFace rightFace := by
    apply
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem) hfacesValueNe
    · simpa [RS] using hleftInternal
    · simpa [RS] using hrightInternal
  exact ⟨internalEdge, leftFace, rightFace, hinternalValue,
    hinternalNotRemoved, hleftSupport, hrightSupport, hfacesNe,
    hleftInternal, hrightInternal, hadjDual⟩

end GoertzelV24DualCycleCollar

namespace GoertzelV24DualCycleSeparator

/-- The exact small side behind a separating facial-dual four-cycle can be
named as two distinct adjacent vertices whose four-edge boundary is the
whole dual crossing set. -/
theorem exists_primalCut_adjacent_pair_collar_of_isCycle_of_length_eq_four
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length = 4)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      ∃ first second : V,
        first ≠ second ∧ component.supp = {first, second} ∧
        G.Adj first second ∧
          crossingEdgeFinset G
              (fun vertex => vertex ∈ component.supp) =
            removed ∧
          ∃ internalEdge : G.edgeSet,
            internalEdge.1 = s(first, second) ∧
              internalEdge ∉ removed ∧
          (removed ∩ incidentEdgeFinset G first).card = 2 ∧
          (removed ∩ incidentEdgeFinset G second).card = 2 := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hcutEq :=
    dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      data hunique walk
  have hexact :=
    exists_primalCut_component_card_eq_two_and_boundary_eq_of_isCycle_of_length_eq_four
      data hregular hconnected hcyclic htwoSided hunique walk hcycle
        hlength hdelete
  rw [hcutEq] at hexact ⊢
  rcases hexact with ⟨component, hcomponentCard, hboundary⟩
  rcases
      GoertzelV24FiniteEdgeDeletion.exists_adjacent_pair_of_component_card_eq_two
        removed component hcomponentCard with
    ⟨first, second, hfirstSecond, hsupp, hadj⟩
  have hsideEq :
      (fun vertex => vertex ∈ component.supp) =
        (fun vertex => vertex ∈ ({first, second} : Set V)) := by
    funext vertex
    rw [hsupp]
  have hboundaryPair := hboundary
  rw [hsideEq] at hboundaryPair
  have hinternalNotRemoved :
      (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ :
          G.edgeSet) ∉ removed := by
    have hinternalNotBoundary :
        (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ :
            G.edgeSet) ∉ crossingEdgeFinset G
              (fun vertex => vertex ∈ component.supp) := by
      rw [hsideEq]
      exact adjacent_pair_internalEdge_not_mem_crossingEdgeFinset hadj
    change
      (⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ :
          G.edgeSet) ∉
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk
    rw [← hboundary]
    exact hinternalNotBoundary
  have hfirstBoundaryCard :
      (removed ∩ incidentEdgeFinset G first).card = 2 := by
    have hcard :=
      card_filter_incidentEdgeFinset_crossing_pair_eq_two_of_cubic
        hregular hadj
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm,
      hboundaryPair] at hcard
    exact hcard
  have hpairs :
      ({second, first} : Set V) = {first, second} := by
    ext vertex
    simp [or_comm]
  have hsecondBoundaryCard :
      (removed ∩ incidentEdgeFinset G second).card = 2 := by
    have hcard :=
      card_filter_incidentEdgeFinset_crossing_pair_eq_two_of_cubic
        hregular hadj.symm
    rw [hpairs, Finset.filter_mem_eq_inter, Finset.inter_comm,
      hboundaryPair] at hcard
    exact hcard
  exact ⟨component, first, second, hfirstSecond, hsupp, hadj,
    hboundary,
    ⟨⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩,
      rfl, hinternalNotRemoved, hfirstBoundaryCard,
        hsecondBoundaryCard⟩⟩

/-- A separating facial-dual four-cycle therefore cuts off a canonical
four-port adjacent-pair collar. Its internal edge is an off-cycle chord of
the full facial dual between two faces in the cycle support. -/
theorem exists_primalCut_adjacent_pair_collar_with_internal_dual_chord_of_isCycle_of_length_eq_four
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length = 4)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      ∃ first second : V,
        first ≠ second ∧ component.supp = {first, second} ∧
          G.Adj first second ∧
          crossingEdgeFinset G
              (fun vertex => vertex ∈ component.supp) =
            removed ∧
          (removed ∩ incidentEdgeFinset G first).card = 2 ∧
          (removed ∩ incidentEdgeFinset G second).card = 2 ∧
          ∃ internalEdge : G.edgeSet,
            ∃ leftFace rightFace : AmbientFace
                (Finset.univ : Finset
                  (OrbitFace data.toRotationSystem)),
              internalEdge.1 = s(first, second) ∧
                internalEdge ∉ removed ∧
                leftFace ∈ walk.support ∧ rightFace ∈ walk.support ∧
                leftFace ≠ rightFace ∧
                internalEdge ∈
                  orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
                internalEdge ∈
                  orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
                (interiorDualGraph
                  (orbitFaceBoundary data.toRotationSystem)
                  (Finset.univ : Finset
                    (OrbitFace data.toRotationSystem))).Adj
                      leftFace rightFace := by
  dsimp only
  have hcollar :=
    exists_primalCut_adjacent_pair_collar_of_isCycle_of_length_eq_four
      data hregular hconnected hcyclic htwoSided hunique walk hcycle hlength
        hdelete
  rcases hcollar with
    ⟨component, first, second, hfirstSecond, hsupp, hadj, hboundary,
      _internalEdge, _hinternalValue, _hinternalNotRemoved,
      hfirstBoundaryCard, hsecondBoundaryCard⟩
  have hsideEq :
      (fun vertex => vertex ∈ component.supp) =
        (fun vertex => vertex ∈ ({first, second} : Set V)) := by
    funext vertex
    rw [hsupp]
  have hboundaryPair := hboundary
  rw [hsideEq] at hboundaryPair
  have hchord :=
    GoertzelV24DualCycleCollar.exists_internal_dual_chord_of_adjacent_pair_boundary_eq
      data (data.toRotationSystem_isCubic_iff.mpr hregular) hrotation
        htwoSided hunique walk hadj hboundaryPair
  exact ⟨component, first, second, hfirstSecond, hsupp, hadj, hboundary,
    hfirstBoundaryCard, hsecondBoundaryCard, hchord⟩

end GoertzelV24DualCycleSeparator

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- In the short saturated regime, recovery returns a remote facial-dual
four-cycle together with its exact adjacent-pair primal collar, the collar's
two-plus-two port split, and its internal off-cycle dual chord. -/
theorem exists_remote_primal_separator_with_four_port_dual_chord_of_arcLength_le_four
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (hshort : rebaseCircuit.arcLength ≤ 4) :
    rebaseCircuit.arcLength = 4 ∧
      ∃ walk :
          (interiorDualGraph
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace graphData.toRotationSystem))).Walk
            rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
        walk.IsCycle ∧
          ¬ (G.deleteEdges
            (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk)).Connected ∧
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).ncard = 4 ∧
          (let removed := dualWalkCrossingEdges
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
            ∃ component :
                (G.deleteEdges
                  (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
                    (pairwiseUniqueSharedInteriorEdges graphData minimal)
                    walk)).ConnectedComponent,
              ∃ first second : V,
                first ≠ second ∧ component.supp = {first, second} ∧
                  G.Adj first second ∧
                  crossingEdgeFinset G
                      (fun vertex => vertex ∈ component.supp) =
                    removed ∧
                  (removed ∩ incidentEdgeFinset G first).card = 2 ∧
                  (removed ∩ incidentEdgeFinset G second).card = 2 ∧
                  ∃ internalEdge : G.edgeSet,
                    ∃ leftFace rightFace : AmbientFace
                        (Finset.univ : Finset
                          (OrbitFace graphData.toRotationSystem)),
                      internalEdge.1 = s(first, second) ∧
                        internalEdge ∉ removed ∧
                        leftFace ∈ walk.support ∧
                        rightFace ∈ walk.support ∧
                        leftFace ≠ rightFace ∧
                        internalEdge ∈ orbitFaceBoundary
                          graphData.toRotationSystem leftFace.1 ∧
                        internalEdge ∈ orbitFaceBoundary
                          graphData.toRotationSystem rightFace.1 ∧
                        (interiorDualGraph
                          (orbitFaceBoundary graphData.toRotationSystem)
                          (Finset.univ : Finset
                            (OrbitFace graphData.toRotationSystem))).Adj
                              leftFace rightFace) ∧
          (∀ face ∈ walk.support,
            centralEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) ∧
          (∀ face ∈ walk.support, ∀ port : Fin 4,
            boundaryEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) := by
  rcases
      circuit.exists_remote_primal_separator_with_exact_two_vertex_collar_of_arcLength_le_four
        hcyclic hminimal hlength hshort with
    ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard,
      _hexact, hcentral, hboundary⟩
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hwalkLength : walk.length = 4 := by
    calc
      walk.length =
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk).ncard :=
        (GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
          graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
            walk hcycle).symm
      _ = 4 := hcutCard
  have hcollar :=
    GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_with_internal_dual_chord_of_isCycle_of_length_eq_four
      graphData hregular hconnected hcyclic minimal.vertexRotationCyclic
        minimal.facesTwoSided
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
          hwalkLength hdelete
  exact ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard, hcollar,
    hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
