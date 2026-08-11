import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleCrossingInjective

/-!
# Local separation by a facial-dual cycle

The Cell-3 carrier is an open annular tangle, so its hole faces need not be
two-sided.  A simple facial-dual layer still separates its crossed primal
edges.  This is the generic parity proof of that fact, expressed with a local
cut definition so the open-tangle branch does not import the older closed-cubic
collar hierarchy.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24PrimalCycleSpace
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24FramedLocalDualCycleSeparator

/-- The ambient primal-edge set crossed by a facial-dual walk.  This local
definition is extensionally the familiar dual cut, but has no dependency on
the closed-cubic separator development. -/
def localDualWalkPrimalCut
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    Set (Sym2 V) :=
  {edge | ∃ step : Fin walk.length,
    (dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)) hunique walk step).1 = edge}

/-- The local primal cut is the range of the crossing-edge reader. -/
theorem localDualWalkPrimalCut_eq_range
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    localDualWalkPrimalCut data hunique walk =
      Set.range (fun step : Fin walk.length =>
        (dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk step).1) := by
  ext edge
  simp [localDualWalkPrimalCut]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance framedLocalDualCycleSeparatorEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Values of a finite collection of graph-edge subtypes, viewed as ambient
unordered vertex pairs.  Keeping this finite-deletion adapter here lets the
Cell-3 separator stay independent of the older collar development. -/
def localEdgeFinsetValueSet (removed : Finset G.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (removed : Set G.edgeSet)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_localEdgeFinsetValueSet_iff
    (removed : Finset G.edgeSet) (edge : Sym2 V) :
    edge ∈ localEdgeFinsetValueSet removed ↔
      ∃ graphEdge ∈ removed, graphEdge.1 = edge := by
  simp [localEdgeFinsetValueSet]

/-- The set-valued local dual cut agrees exactly with the finite collection of
crossing edges used by the source layer. -/
theorem localDualWalkPrimalCut_eq_localEdgeFinsetValueSet_dualWalkCrossingEdges
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    localDualWalkPrimalCut data hunique walk =
      localEdgeFinsetValueSet
        (dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk) := by
  ext edge
  constructor
  · rintro ⟨step, rfl⟩
    refine (mem_localEdgeFinsetValueSet_iff _ _).2
      ⟨dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk step, ?_, rfl⟩
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk _).2
      ⟨step, rfl⟩
  · intro hmem
    rcases (mem_localEdgeFinsetValueSet_iff _ _).1 hmem with
      ⟨graphEdge, hgraphEdge, hvalue⟩
    rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      graphEdge).1 hgraphEdge with ⟨step, hstep⟩
    exact ⟨step, congrArg Subtype.val hstep |>.trans hvalue⟩

/-- The exact graph boundary of a connected component after a finite local
edge deletion. -/
noncomputable def localComponentCrossingEdges
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge =>
    EdgeCrossesVertexSide G (fun vertex => vertex ∈ component.supp) edge

omit [DecidableEq V] in
@[simp]
theorem mem_localComponentCrossingEdges_iff
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent)
    (edge : G.edgeSet) :
    edge ∈ localComponentCrossingEdges removed component ↔
      EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ component.supp) edge := by
  simp [localComponentCrossingEdges]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A graph edge crossing a deletion component must be one of the deleted
edges. -/
theorem localEdge_mem_removed_of_crosses_delete_component
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge) :
    edge ∈ removed := by
  rcases hcross with ⟨left, right, hleftEdge, hrightEdge,
    hleftComponent, hrightComponent⟩
  have hne : left ≠ right := by
    intro heq
    exact hrightComponent (heq ▸ hleftComponent)
  have hedgeValue : edge.1 = s(left, right) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hleftEdge hrightEdge hne
  by_contra hnotMem
  have hnotValue : edge.1 ∉ localEdgeFinsetValueSet removed := by
    intro hvalue
    rcases (mem_localEdgeFinsetValueSet_iff removed edge.1).1 hvalue with
      ⟨other, hother, hotherValue⟩
    apply hnotMem
    simpa [Subtype.ext hotherValue] using hother
  have hadj : G.Adj left right :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  have hdeleteAdj :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).Adj left right := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hadj, by simpa [← hedgeValue] using hnotValue⟩
  exact hrightComponent
    ((component.mem_supp_congr_adj hdeleteAdj).mp hleftComponent)

/-- The computed component boundary is contained in the finite set deleted to
form that component. -/
theorem localComponentCrossingEdges_subset_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent) :
    localComponentCrossingEdges removed component ⊆ removed := by
  intro edge hedge
  exact localEdge_mem_removed_of_crosses_delete_component removed component edge
    ((mem_localComponentCrossingEdges_iff removed component edge).1 hedge)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Disconnecting a connected graph by a finite local edge deletion produces
two distinct components. -/
theorem exists_distinct_localComponents_of_not_connected
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (hdelete :
      ¬ (G.deleteEdges (localEdgeFinsetValueSet removed)).Connected) :
    ∃ inside outside :
        (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent,
      inside ≠ outside := by
  let deleted := G.deleteEdges (localEdgeFinsetValueSet removed)
  letI : Nonempty V := hconnected.nonempty
  have hnotPreconnected : ¬ deleted.Preconnected := by
    intro hpreconnected
    exact hdelete ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with ⟨insideVertex, outsideVertex, hnotReachable⟩
  let inside := deleted.connectedComponentMk insideVertex
  let outside := deleted.connectedComponentMk outsideVertex
  refine ⟨inside, outside, ?_⟩
  intro heq
  exact hnotReachable (SimpleGraph.ConnectedComponent.exact heq)

/-- A dual step is witnessed by the two opposite darts of its crossed edge.
The parity boundary therefore sees the two incident face labels correctly even
when unrelated Cell-3 hole-stub edges are one-sided. -/
theorem orbitFaceParityBoundaryLinearMap_apply_dualWalkCrossingEdge
    (RS : RotationSystem V E)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (step : Fin walk.length)
    (coefficients : OrbitFace RS → F2) :
    orbitFaceParityBoundaryLinearMap RS coefficients
        (dualWalkCrossingEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step) =
      coefficients (walk.getVert step.val).1 +
        coefficients (walk.getVert (step.val + 1)).1 := by
  have hadj := walk.adj_getVert_succ step.isLt
  have hfaces : (walk.getVert step.val).1 ≠
      (walk.getVert (step.val + 1)).1 := by
    intro hface
    exact hadj.ne (Subtype.ext hface)
  have hleft : dualWalkCrossingEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step ∈
      orbitFaceBoundary RS (walk.getVert step.val).1 :=
    dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hright : dualWalkCrossingEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step ∈
      orbitFaceBoundary RS (walk.getVert (step.val + 1)).1 :=
    dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  rcases (mem_orbitFaceBoundary_iff RS (walk.getVert step.val).1 _).1 hleft
      with ⟨leftDart, hleftDart, hleftEdge⟩
  rcases (mem_orbitFaceBoundary_iff RS
      (walk.getVert (step.val + 1)).1 _).1 hright with
      ⟨rightDart, hrightDart, hrightEdge⟩
  have hleftFace : dartOrbitFace RS leftDart =
      (walk.getVert step.val).1 :=
    (mem_orbitFaceDarts_iff RS _ _).1 hleftDart
  have hrightFace : dartOrbitFace RS rightDart =
      (walk.getVert (step.val + 1)).1 :=
    (mem_orbitFaceDarts_iff RS _ _).1 hrightDart
  have hrightDartEq : rightDart = RS.alpha leftDart := by
    rcases RS.edge_fiber_two_cases hleftEdge hrightEdge with heq | heq
    · exfalso
      apply hfaces
      rw [← hleftFace, ← hrightFace, heq]
    · exact heq
  have halphaFace : dartOrbitFace RS (RS.alpha leftDart) =
      (walk.getVert (step.val + 1)).1 := by
    rw [← hrightDartEq]
    exact hrightFace
  rw [← hleftEdge, orbitFaceParityBoundaryLinearMap_apply_edgeOf,
    hleftFace, halphaFace]

omit [Fintype V] [DecidableEq V] in
private theorem getVert_succ_eq_getVert_finRotate
    {H : SimpleGraph V} {start : V}
    (walk : H.Walk start start)
    (hcycle : walk.IsCycle)
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

/-- The total parity-boundary coordinate of the primal crossings of a simple
facial-dual cycle vanishes.  No global face-two-sidedness hypothesis is used. -/
theorem sum_orbitFaceParityBoundaryLinearMap_dualCycle_eq_zero
    (RS : RotationSystem V E)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle)
    (coefficients : OrbitFace RS → F2) :
    (∑ step : Fin walk.length,
      orbitFaceParityBoundaryLinearMap RS coefficients
        (dualWalkCrossingEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step)) = 0 := by
  simp_rw [orbitFaceParityBoundaryLinearMap_apply_dualWalkCrossingEdge
    RS hunique walk]
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ step : Fin walk.length,
        coefficients (walk.getVert (step.val + 1)).1) =
      ∑ step : Fin walk.length,
        coefficients (walk.getVert step.val).1 := by
    calc
      (∑ step : Fin walk.length,
          coefficients (walk.getVert (step.val + 1)).1) =
          ∑ step : Fin walk.length,
            coefficients
              (walk.getVert (finRotate walk.length step).val).1 := by
        apply Finset.sum_congr rfl
        intro step _hstep
        rw [getVert_succ_eq_getVert_finRotate walk hcycle step]
      _ = ∑ step : Fin walk.length,
          coefficients (walk.getVert step.val).1 :=
        Equiv.sum_comp (finRotate walk.length)
          (fun step : Fin walk.length =>
            coefficients (walk.getVert step.val).1)
  rw [hshift]
  simp

/-- Every primal cycle has even intersection with the crossings of a simple
facial-dual cycle in a connected framed spherical cellulation. -/
theorem f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
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
    (hdualCycle : walk.IsCycle)
    {cycle : G.edgeSet → F2}
    (hcycle : cycle ∈ f2CycleSpace G) :
    (∑ step : Fin walk.length,
      cycle (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step)) = 0 := by
  have hspan : cycle ∈ LinearMap.range
      (orbitFaceParityBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceParityBoundaryLinearMap_eq_f2CycleSpace
      data hdual hconnected heuler]
    exact hcycle
  rcases hspan with ⟨coefficients, rfl⟩
  exact sum_orbitFaceParityBoundaryLinearMap_dualCycle_eq_zero
    data.toRotationSystem hunique walk hdualCycle coefficients

/-- The primal crossings of a simple closed facial-dual walk disconnect the
underlying framed graph.  A return path after deleting the crossings would
close one crossing into a primal cycle meeting the dual cycle once. -/
theorem not_connected_deleteEdges_localDualWalkPrimalCut_of_isCycle
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
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
    (hdualCycle : walk.IsCycle) :
    ¬ (G.deleteEdges (localDualWalkPrimalCut data hunique walk)).Connected := by
  intro hdeleteConnected
  let firstStep : Fin walk.length :=
    ⟨0, lt_of_lt_of_le (by omega) hdualCycle.three_le_length⟩
  let firstEdge : G.edgeSet :=
    dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      firstStep
  rcases data.toRotationSystem.dartsOn_nonempty firstEdge with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = firstEdge :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hdartEdgeValue : dart.edge = firstEdge.1 :=
    congrArg Subtype.val hdartEdge
  rcases hdeleteConnected dart.snd dart.fst with ⟨returnWalkDeleted⟩
  let returnWalk : G.Walk dart.snd dart.fst :=
    returnWalkDeleted.mapLe
      (G.deleteEdges_le (localDualWalkPrimalCut data hunique walk))
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le (localDualWalkPrimalCut data hunique walk))
  have hcrossingCut (step : Fin walk.length) :
      (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step).1 ∈
        localDualWalkPrimalCut data hunique walk := by
    exact ⟨step, rfl⟩
  have hreturnAvoid (step : Fin walk.length) :
      (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step).1 ∉
        returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
    exact hdeleted.2 (hcrossingCut step)
  let closedWalk : G.Walk dart.fst dart.fst :=
    SimpleGraph.Walk.cons dart.adj returnWalk
  have hcycle : walkEdgeParity closedWalk ∈ f2CycleSpace G :=
    walkEdgeParity_mem_f2CycleSpace_of_closed closedWalk
  have hcoordinates :=
    f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
      data hdual hconnected heuler hunique walk hdualCycle hcycle
  have hinjective := dualWalkCrossingEdge_injective_of_isCycle_core
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))
    (orbitFace_incidence_le_two data.toRotationSystem)
    hunique walk hdualCycle
  have hfirstCoordinate : walkEdgeParity closedWalk firstEdge = 1 := by
    have hreturnCount : returnWalk.edges.count firstEdge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid firstStep)
    have hdartPairValue : s(dart.fst, dart.snd) = firstEdge.1 :=
      hdartEdgeValue
    change ((List.count firstEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 1
    simp [hdartPairValue, hreturnCount]
  have hotherCoordinate (step : Fin walk.length) (hne : step ≠ firstStep) :
      walkEdgeParity closedWalk
        (dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk step) = 0 := by
    let edge := dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)) hunique walk step
    have hreturnCount : returnWalk.edges.count edge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid step)
    have hdartPairNe : s(dart.fst, dart.snd) ≠ edge.1 := by
      intro heq
      apply hne
      apply hinjective
      apply Subtype.ext
      exact (hdartEdgeValue.symm.trans heq).symm
    change ((List.count edge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [hdartPairNe, hreturnCount]
  have hsumOne :
      (∑ step : Fin walk.length,
        walkEdgeParity closedWalk
          (dualWalkCrossingEdge
            (orbitFaceBoundary data.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace data.toRotationSystem)) hunique walk step)) = 1 := by
    rw [Finset.sum_eq_single firstStep]
    · exact hfirstCoordinate
    · intro step _hstep hne
      exact hotherCoordinate step hne
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ firstStep))
  rw [hsumOne] at hcoordinates
  exact one_ne_zero hcoordinates

end GoertzelV24FramedLocalDualCycleSeparator

end

end Mettapedia.GraphTheory.FourColor
