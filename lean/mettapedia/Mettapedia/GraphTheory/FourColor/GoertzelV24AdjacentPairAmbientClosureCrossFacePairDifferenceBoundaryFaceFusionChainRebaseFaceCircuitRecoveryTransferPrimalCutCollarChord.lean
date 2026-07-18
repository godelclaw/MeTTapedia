import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollar

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
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  collarFiniteGraphLocallyFinite
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

namespace GoertzelV24DualCycleChord

variable {W : Type*} {H : SimpleGraph W} {root : W}

/-- Every support vertex of a simple cycle has a representative position
strictly before the repeated terminal position. -/
theorem exists_fin_getVert_eq_of_mem_support_of_isCycle
    {walk : H.Walk root root} (hcycle : walk.IsCycle)
    {vertex : W} (hvertex : vertex ∈ walk.support) :
    ∃ step : Fin walk.length, walk.getVert step.val = vertex := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
    ⟨position, hposition, hpositionLe⟩
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  by_cases hterminal : position = walk.length
  · refine ⟨⟨0, hpositive⟩, ?_⟩
    rw [← hposition, hterminal, walk.getVert_length, walk.getVert_zero]
  · exact ⟨⟨position, by omega⟩, hposition⟩

/-- Cyclic successor agrees with the next ordinary walk position, including
the closing step. -/
theorem getVert_succ_eq_getVert_finRotate_of_isCycle
    {walk : H.Walk root root} (hcycle : walk.IsCycle)
    (step : Fin walk.length) :
    walk.getVert (step.val + 1) =
      walk.getVert (finRotate walk.length step).val := by
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  have hone : 1 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  letI : NeZero walk.length := ⟨Nat.ne_of_gt hpositive⟩
  by_cases hnext : step.val + 1 < walk.length
  · have hrotate : (finRotate walk.length step).val = step.val + 1 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
  · have hlast : step.val + 1 = walk.length := by omega
    have hrotate : (finRotate walk.length step).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, hlast, Nat.mod_self]
    rw [hlast, hrotate, walk.getVert_length, walk.getVert_zero]

/-- Positional reading of a walk edge gives the unordered pair of its two
successive vertices. -/
theorem edges_get_cast_eq_s_getVert
    (walk : H.Walk root root) (step : Fin walk.length) :
    walk.edges.get (Fin.cast walk.length_edges.symm step) =
      s(walk.getVert step.val, walk.getVert (step.val + 1)) := by
  simp [SimpleGraph.Walk.edges, List.get_eq_getElem,
    SimpleGraph.Walk.darts_getElem_eq_getVert]

/-- The endpoints of a chord of a simple four-cycle occupy opposite cyclic
positions. -/
theorem exists_opposite_getVert_of_isCycle_of_length_eq_four_of_isChord
    {walk : H.Walk root root} (hcycle : walk.IsCycle)
    (hlength : walk.length = 4) {left right : W}
    (hchord : walk.IsChord s(left, right)) :
    ∃ step : Fin walk.length,
      walk.getVert step.val = left ∧
        walk.getVert
          (finRotate walk.length (finRotate walk.length step)).val = right := by
  rcases (SimpleGraph.Walk.isChord_sym2Mk.1 hchord) with
    ⟨hadj, hnotEdge, hleftSupport, hrightSupport⟩
  rcases exists_fin_getVert_eq_of_mem_support_of_isCycle hcycle hleftSupport with
    ⟨leftStep, hleft⟩
  rcases exists_fin_getVert_eq_of_mem_support_of_isCycle hcycle hrightSupport with
    ⟨rightStep, hright⟩
  have hstepsNe : leftStep ≠ rightStep := by
    intro hsteps
    apply hadj.ne
    rw [← hleft, ← hright, hsteps]
  have hrightNotSuccessor :
      rightStep ≠ finRotate walk.length leftStep := by
    intro hsteps
    apply hnotEdge
    have hmember := List.get_mem walk.edges
      (Fin.cast walk.length_edges.symm leftStep)
    rw [edges_get_cast_eq_s_getVert walk leftStep] at hmember
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle leftStep
    rw [← hsteps] at hsuccessor
    simpa [hleft, hsuccessor, hright] using hmember
  have hleftNotSuccessor :
      leftStep ≠ finRotate walk.length rightStep := by
    intro hsteps
    apply hnotEdge
    have hmember := List.get_mem walk.edges
      (Fin.cast walk.length_edges.symm rightStep)
    rw [edges_get_cast_eq_s_getVert walk rightStep] at hmember
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle rightStep
    rw [← hsteps] at hsuccessor
    simpa [hleft, hsuccessor, hright, Sym2.eq_swap] using hmember
  have hrightStep :
      rightStep =
        finRotate walk.length (finRotate walk.length leftStep) := by
    apply Fin.ext
    have hleftLt : leftStep.val < 4 := by omega
    have hrightLt : rightStep.val < 4 := by omega
    have hstepsValNe : leftStep.val ≠ rightStep.val := by
      intro hvalues
      exact hstepsNe (Fin.ext hvalues)
    have hrightNotSuccessorVal :
        rightStep.val ≠ (finRotate walk.length leftStep).val := by
      intro hvalues
      exact hrightNotSuccessor (Fin.ext hvalues)
    have hleftNotSuccessorVal :
        leftStep.val ≠ (finRotate walk.length rightStep).val := by
      intro hvalues
      exact hleftNotSuccessor (Fin.ext hvalues)
    simp only [finRotate_apply, Fin.val_add, Fin.val_one'] at hrightNotSuccessorVal hleftNotSuccessorVal ⊢
    simp only [hlength] at hrightNotSuccessorVal hleftNotSuccessorVal ⊢
    omega
  exact ⟨leftStep, hleft, hrightStep ▸ hright⟩

/-- A chord splits a simple four-cycle into two simple triangles, and the
chord belongs to both triangle edge lists. -/
theorem exists_two_triangles_of_isCycle_of_length_eq_four_of_isChord
    {walk : H.Walk root root} (hcycle : walk.IsCycle)
    (hlength : walk.length = 4) {left right : W}
    (hchord : walk.IsChord s(left, right)) :
    ∃ firstTriangle secondTriangle : H.Walk left left,
      firstTriangle.IsCycle ∧ firstTriangle.length = 3 ∧
        secondTriangle.IsCycle ∧ secondTriangle.length = 3 ∧
        s(left, right) ∈ firstTriangle.edges ∧
        s(left, right) ∈ secondTriangle.edges ∧
        ∃ firstOnly : Sym2 W,
          firstOnly ∈ firstTriangle.edges ∧
            firstOnly ∉ secondTriangle.edges := by
  classical
  rcases exists_opposite_getVert_of_isCycle_of_length_eq_four_of_isChord
      hcycle hlength hchord with
    ⟨step, hleftPosition, hrightPosition⟩
  rcases (SimpleGraph.Walk.isChord_sym2Mk.1 hchord) with
    ⟨hleftRight, hnotEdge, _hleftSupport, _hrightSupport⟩
  let next := finRotate walk.length step
  let opposite := finRotate walk.length next
  let previous := finRotate walk.length opposite
  let firstMiddle := walk.getVert next.val
  let secondMiddle := walk.getVert previous.val
  have hrightAtOpposite : walk.getVert opposite.val = right := by
    simpa [opposite, next] using hrightPosition
  have hclose : finRotate walk.length previous = step := by
    apply Fin.ext
    simp only [previous, opposite, next, finRotate_apply, Fin.val_add,
      Fin.val_one']
    simp only [hlength]
    omega
  have hleftFirstMiddle : H.Adj left firstMiddle := by
    have hadj := walk.adj_getVert_succ step.isLt
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle step
    rw [hsuccessor] at hadj
    simpa [firstMiddle, next, hleftPosition] using hadj
  have hfirstMiddleRight : H.Adj firstMiddle right := by
    have hadj := walk.adj_getVert_succ next.isLt
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle next
    rw [hsuccessor] at hadj
    rw [hrightAtOpposite] at hadj
    simpa [firstMiddle, next, opposite] using hadj
  have hrightSecondMiddle : H.Adj right secondMiddle := by
    have hadj := walk.adj_getVert_succ opposite.isLt
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle opposite
    rw [hsuccessor] at hadj
    rw [hrightAtOpposite] at hadj
    simpa [secondMiddle, previous, opposite] using hadj
  have hsecondMiddleLeft : H.Adj secondMiddle left := by
    have hadj := walk.adj_getVert_succ previous.isLt
    have hsuccessor :=
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle previous
    rw [hsuccessor, hclose] at hadj
    simpa [secondMiddle, previous, hleftPosition] using hadj
  have hstepEdge :
      walk.edges.get (Fin.cast walk.length_edges.symm step) =
        s(left, firstMiddle) := by
    rw [edges_get_cast_eq_s_getVert,
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle]
    simp [firstMiddle, next, hleftPosition]
  have hoppositeEdge :
      walk.edges.get (Fin.cast walk.length_edges.symm opposite) =
        s(right, secondMiddle) := by
    rw [edges_get_cast_eq_s_getVert,
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle]
    simp [secondMiddle, previous, hrightAtOpposite]
  have hpreviousEdge :
      walk.edges.get (Fin.cast walk.length_edges.symm previous) =
        s(secondMiddle, left) := by
    rw [edges_get_cast_eq_s_getVert,
      getVert_succ_eq_getVert_finRotate_of_isCycle hcycle, hclose]
    simp [secondMiddle, hleftPosition]
  have hstepNeOpposite : step ≠ opposite := by
    intro hsteps
    have hvalues := congrArg Fin.val hsteps
    simp only [opposite, next, finRotate_apply, Fin.val_add,
      Fin.val_one', hlength] at hvalues
    omega
  have hstepNePrevious : step ≠ previous := by
    intro hsteps
    have hvalues := congrArg Fin.val hsteps
    simp only [previous, opposite, next, finRotate_apply, Fin.val_add,
      Fin.val_one', hlength] at hvalues
    omega
  have hgetInjective : Function.Injective walk.edges.get :=
    List.nodup_iff_injective_get.mp hcycle.edges_nodup
  have hfirstNeChord : s(left, firstMiddle) ≠ s(left, right) := by
    intro hedges
    apply hnotEdge
    rw [← hedges]
    exact hstepEdge ▸ List.get_mem walk.edges
      (Fin.cast walk.length_edges.symm step)
  have hfirstNeOpposite :
      s(left, firstMiddle) ≠ s(right, secondMiddle) := by
    intro hedges
    apply hstepNeOpposite
    exact Fin.cast_injective walk.length_edges.symm
      (hgetInjective (hstepEdge.trans (hedges.trans hoppositeEdge.symm)))
  have hfirstNePrevious :
      s(left, firstMiddle) ≠ s(secondMiddle, left) := by
    intro hedges
    apply hstepNePrevious
    exact Fin.cast_injective walk.length_edges.symm
      (hgetInjective (hstepEdge.trans (hedges.trans hpreviousEdge.symm)))
  let firstTriangle : H.Walk left left :=
    .cons hleftFirstMiddle
      (.cons hfirstMiddleRight (.cons hleftRight.symm .nil))
  let secondTriangle : H.Walk left left :=
    .cons hleftRight
      (.cons hrightSecondMiddle (.cons hsecondMiddleLeft .nil))
  have hfirstCycle : firstTriangle.IsCycle := by
    simp [firstTriangle, SimpleGraph.Walk.isCycle_def,
      SimpleGraph.Walk.isTrail_def, hleftFirstMiddle.ne,
      hleftFirstMiddle.ne.symm, hfirstMiddleRight.ne,
      hleftRight.ne, hleftRight.ne.symm]
  have hsecondCycle : secondTriangle.IsCycle := by
    simp [secondTriangle, SimpleGraph.Walk.isCycle_def,
      SimpleGraph.Walk.isTrail_def, hleftRight.ne, hleftRight.ne.symm,
      hrightSecondMiddle.ne, hsecondMiddleLeft.ne,
      hsecondMiddleLeft.ne.symm]
  exact ⟨firstTriangle, secondTriangle, hfirstCycle, by simp [firstTriangle],
    hsecondCycle, by simp [secondTriangle], by
      simp [firstTriangle, Sym2.eq_swap], by
      simp [secondTriangle, Sym2.eq_swap],
    s(left, firstMiddle), by simp [firstTriangle], by
      simp [secondTriangle, hfirstNeChord, hfirstNeOpposite,
        hfirstNePrevious]⟩

end GoertzelV24DualCycleChord

namespace GoertzelV24DualCycleCollar

/-- A primal edge shared by two vertices of a facial-dual walk, but absent
from the walk's crossing set, induces a chord of that dual walk. -/
theorem isChord_of_shared_primal_edge_not_mem_crossings
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
    {edge : G.edgeSet}
    {leftFace rightFace : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hleftSupport : leftFace ∈ walk.support)
    (hrightSupport : rightFace ∈ walk.support)
    (hfacesNe : leftFace ≠ rightFace)
    (hleftBoundary : edge ∈
      orbitFaceBoundary data.toRotationSystem leftFace.1)
    (hrightBoundary : edge ∈
      orbitFaceBoundary data.toRotationSystem rightFace.1)
    (hnotCrossing : edge ∉ dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk) :
    walk.IsChord s(leftFace, rightFace) := by
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  have hfacesValueNe : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact hfacesNe (Subtype.ext hfaces)
  have hadjDual :
      (interiorDualGraph
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem))).Adj leftFace rightFace := by
    exact
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem) hfacesValueNe
          hleftBoundary hrightBoundary
  refine ⟨hadjDual, ?_, hleftSupport, hrightSupport⟩
  have hcount :
      totalIncidenceCount
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) edge = 2 :=
    totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) leftFace.2
        rightFace.2 hfacesValueNe hleftBoundary hrightBoundary
  have hinterior : edge ∈ interiorEdgeSupport
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) := by
    apply (mem_interiorEdgeSupport_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).2
    exact ⟨Finset.mem_biUnion.2
      ⟨leftFace.1, leftFace.2, hleftBoundary⟩, hcount⟩
  have hsharedLeftRight : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      leftFace.1 rightFace.1 :=
    (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).2
        ⟨hinterior, hleftBoundary, hrightBoundary⟩
  have hsharedRightLeft : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      rightFace.1 leftFace.1 :=
    (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).2
        ⟨hinterior, hrightBoundary, hleftBoundary⟩
  intro hwalkEdge
  rcases List.get_of_mem hwalkEdge with ⟨edgeStep, hedgeStep⟩
  let step : Fin walk.length := Fin.cast walk.length_edges edgeStep
  have hedgeStepCast :
      Fin.cast walk.length_edges.symm step = edgeStep := by
    apply Fin.ext
    rfl
  have hpositional := edges_get_dualWalkGraphEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) walk step
  have hgraphEdge :
      dualWalkGraphEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) walk step =
        s(leftFace, rightFace) := by
    calc
      dualWalkGraphEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) walk step =
          walk.edges.get (Fin.cast walk.length_edges.symm step) :=
        hpositional.symm
      _ = walk.edges.get edgeStep := by rw [hedgeStepCast]
      _ = s(leftFace, rightFace) := hedgeStep
  change s(walk.getVert step.val, walk.getVert (step.val + 1)) =
    s(leftFace, rightFace) at hgraphEdge
  have hsharedStep : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (walk.getVert step.val).1 (walk.getVert (step.val + 1)).1 := by
    rcases (Sym2.eq_iff.1 hgraphEdge) with hsame | hreverse
    · rcases hsame with ⟨hleft, hright⟩
      simpa [hleft, hright] using hsharedLeftRight
    · rcases hreverse with ⟨hleft, hright⟩
      simpa [hleft, hright] using hsharedRightLeft
  have hcrossingEdge :
      dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk step = edge := by
    exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
      (walk.adj_getVert_succ step.isLt) hsharedStep
  apply hnotCrossing
  exact (mem_dualWalkCrossingEdges_iff
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      edge).2 ⟨step, hcrossingEdge⟩

/-- The internal edge of an exact adjacent-pair walk boundary is therefore
a chord in the standard walk-theoretic sense. -/
theorem exists_internal_walk_chord_of_adjacent_pair_boundary_eq
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
      GoertzelV24CubicSmallBoundaryCycle.crossingEdgeFinset G
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
          internalEdge ∈
            orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
          internalEdge ∈
            orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
          walk.IsChord s(leftFace, rightFace) := by
  dsimp only
  rcases
      exists_internal_dual_chord_of_adjacent_pair_boundary_eq
        data hcubic hrotation htwoSided hunique walk hadj hboundary with
    ⟨internalEdge, leftFace, rightFace, hinternalValue,
      hinternalNotRemoved, hleftSupport, hrightSupport, hfacesNe,
      hleftBoundary, hrightBoundary, _hadjDual⟩
  have hchord := isChord_of_shared_primal_edge_not_mem_crossings
    data hunique walk hleftSupport hrightSupport hfacesNe hleftBoundary
      hrightBoundary hinternalNotRemoved
  exact ⟨internalEdge, leftFace, rightFace, hinternalValue,
    hinternalNotRemoved, hleftBoundary, hrightBoundary, hchord⟩

/-- On an exact adjacent-pair boundary of length four, the internal chord's
two face endpoints occur at opposite cyclic positions. -/
theorem exists_internal_opposite_walk_chord_of_adjacent_pair_boundary_eq
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
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
        ∃ step : Fin walk.length,
          internalEdge.1 = s(first, second) ∧
            internalEdge ∉ removed ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
            walk.IsChord s(leftFace, rightFace) ∧
            walk.getVert step.val = leftFace ∧
            walk.getVert
              (finRotate walk.length (finRotate walk.length step)).val =
                rightFace := by
  dsimp only
  rcases exists_internal_walk_chord_of_adjacent_pair_boundary_eq
      data hcubic hrotation htwoSided hunique walk hadj hboundary with
    ⟨internalEdge, leftFace, rightFace, hinternalValue,
      hinternalNotRemoved, hleftBoundary, hrightBoundary, hchord⟩
  rcases
      GoertzelV24DualCycleChord.exists_opposite_getVert_of_isCycle_of_length_eq_four_of_isChord
        hcycle hlength hchord with
    ⟨step, hleftPosition, hrightPosition⟩
  exact ⟨internalEdge, leftFace, rightFace, step, hinternalValue,
    hinternalNotRemoved, hleftBoundary, hrightBoundary, hchord,
    hleftPosition, hrightPosition⟩

/-- The internal chord of an exact adjacent-pair four-cycle splits that
cycle into two explicit facial-dual triangles sharing the chord. -/
theorem exists_internal_chord_two_triangles_of_adjacent_pair_boundary_eq
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
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
        ∃ firstTriangle secondTriangle :
            (interiorDualGraph
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem))).Walk leftFace leftFace,
          internalEdge.1 = s(first, second) ∧
            internalEdge ∉ removed ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
            walk.IsChord s(leftFace, rightFace) ∧
            firstTriangle.IsCycle ∧ firstTriangle.length = 3 ∧
            secondTriangle.IsCycle ∧ secondTriangle.length = 3 ∧
            s(leftFace, rightFace) ∈ firstTriangle.edges ∧
            s(leftFace, rightFace) ∈ secondTriangle.edges ∧
            ∃ firstOnly : Sym2
                (AmbientFace
                  (Finset.univ : Finset
                    (OrbitFace data.toRotationSystem))),
              firstOnly ∈ firstTriangle.edges ∧
                firstOnly ∉ secondTriangle.edges := by
  dsimp only
  rcases exists_internal_walk_chord_of_adjacent_pair_boundary_eq
      data hcubic hrotation htwoSided hunique walk hadj hboundary with
    ⟨internalEdge, leftFace, rightFace, hinternalValue,
      hinternalNotRemoved, hleftBoundary, hrightBoundary, hchord⟩
  rcases
      GoertzelV24DualCycleChord.exists_two_triangles_of_isCycle_of_length_eq_four_of_isChord
        hcycle hlength hchord with
    ⟨firstTriangle, secondTriangle, hfirstCycle, hfirstLength,
      hsecondCycle, hsecondLength, hfirstChord, hsecondChord,
      hfirstOnly⟩
  exact ⟨internalEdge, leftFace, rightFace, firstTriangle, secondTriangle,
    hinternalValue, hinternalNotRemoved, hleftBoundary, hrightBoundary,
    hchord, hfirstCycle, hfirstLength, hsecondCycle, hsecondLength,
    hfirstChord, hsecondChord, hfirstOnly⟩

end GoertzelV24DualCycleCollar

namespace GoertzelV24DualCycleSeparator

/-- A separating facial-dual triangle in a cubic cyclically
five-edge-connected graph cuts off exactly one vertex, and all three cycle
crossings are incident to that singleton component. -/
theorem exists_primalCut_component_card_eq_one_and_boundary_eq_of_isCycle_of_length_eq_three
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hcycle : walk.IsCycle) (hlength : walk.length = 3)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∧
        crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) =
          removed := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hremovedCard : removed.card = 3 := by
    rw [GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle,
      hlength]
  have hcutEq :=
    dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      data hunique walk
  rw [hcutEq] at hdelete ⊢
  rcases
      GoertzelV24FiniteEdgeDeletion.exists_component_card_le_two_of_cyclicallyFive_of_not_connected
        hregular hconnected hcyclic removed (by omega) hdelete with
    ⟨component, hcomponentCardLe⟩
  have hboundarySubset :=
    GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_subset_removed
      removed component
  have hboundaryCard :=
    GoertzelV24FiniteEdgeDeletion.card_componentCrossingEdges_eq_card_add_two_of_cubic_of_card_le_two
      hregular removed component hcomponentCardLe
  have hcomponentCardPositive :
      0 < Nat.card {vertex : V // vertex ∈ component.supp} := by
    letI : Nonempty {vertex : V // vertex ∈ component.supp} :=
      ⟨⟨component.nonempty_supp.choose,
        component.nonempty_supp.choose_spec⟩⟩
    exact Nat.card_pos
  have hboundaryCardLe :
      (GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
        removed component).card ≤ removed.card :=
    Finset.card_le_card hboundarySubset
  have hcomponentCard :
      Nat.card {vertex : V // vertex ∈ component.supp} = 1 := by
    rw [hboundaryCard, hremovedCard] at hboundaryCardLe
    omega
  have hboundaryEq :
      GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
        removed component = removed := by
    apply Finset.eq_of_subset_of_card_le hboundarySubset
    rw [hboundaryCard, hcomponentCard, hremovedCard]
  rw [GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_eq_crossingEdgeFinset]
    at hboundaryEq
  exact ⟨component, hcomponentCard, hboundaryEq⟩

/-- A separating facial-dual four-cycle cuts off an adjacent-pair collar
whose internal primal edge is a genuine chord joining opposite positions
of the dual cycle. -/
theorem exists_primalCut_adjacent_pair_collar_with_opposite_walk_chord_of_isCycle_of_length_eq_four
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
              ∃ step : Fin walk.length,
                internalEdge.1 = s(first, second) ∧
                  internalEdge ∉ removed ∧
                  internalEdge ∈
                    orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
                  internalEdge ∈
                    orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
                  walk.IsChord s(leftFace, rightFace) ∧
                  walk.getVert step.val = leftFace ∧
                  walk.getVert
                    (finRotate walk.length
                      (finRotate walk.length step)).val = rightFace := by
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
    GoertzelV24DualCycleCollar.exists_internal_opposite_walk_chord_of_adjacent_pair_boundary_eq
      data (data.toRotationSystem_isCubic_iff.mpr hregular) hrotation
        htwoSided hunique walk hcycle hlength hadj hboundaryPair
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

/-- Short saturated recovery produces a remote facial-dual four-cycle with
a standard walk chord joining opposite positions and carried by the
internal edge of its exact four-port adjacent-pair collar. -/
theorem exists_remote_primal_separator_with_four_port_opposite_walk_chord_of_arcLength_le_four
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
                      ∃ step : Fin walk.length,
                        internalEdge.1 = s(first, second) ∧
                          internalEdge ∉ removed ∧
                          internalEdge ∈ orbitFaceBoundary
                            graphData.toRotationSystem leftFace.1 ∧
                          internalEdge ∈ orbitFaceBoundary
                            graphData.toRotationSystem rightFace.1 ∧
                          walk.IsChord s(leftFace, rightFace) ∧
                          walk.getVert step.val = leftFace ∧
                          walk.getVert
                            (finRotate walk.length
                              (finRotate walk.length step)).val =
                                rightFace) ∧
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
      circuit.exists_remote_primal_separator_with_four_port_dual_chord_of_arcLength_le_four
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
    GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_with_opposite_walk_chord_of_isCycle_of_length_eq_four
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
