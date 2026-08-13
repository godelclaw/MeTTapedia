import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut

/-!
# Bridge-safe separation by a facial-dual cycle

The source corridor lives in a framed annular cellulation, whose boundary
stubs may be one-sided edges.  The older dual-cycle separator was formulated
for globally cubic, two-sided maps.  This file reconstructs the separator
using the multiplicity-correct facial boundary map, so the local layer cycle
can be used in the actual framed source geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24DualPathTransversal
open GoertzelV24DualCycleSeparator
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

namespace GoertzelV24FramedDualCycleSeparator

/-- A dual step is witnessed by the two opposite darts of its crossed edge.
Unlike the support-based facial boundary map, the parity boundary therefore
computes the two incident face labels correctly even when other, unrelated
edges of the framed cellulation are one-sided. -/
theorem orbitFaceParityBoundaryLinearMap_apply_dualWalkCrossingEdge
    (RS : RotationSystem V E)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
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
/-- Cyclic successor of a dual-cycle step reads the ordinary next walk
position, including the closing step. -/
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
facial-dual cycle vanishes.  This is the bridge-safe version of the usual
dual-cycle cancellation: no global two-sidedness hypothesis is used. -/
theorem sum_orbitFaceParityBoundaryLinearMap_dualCycle_eq_zero
    (RS : RotationSystem V E)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
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

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq (G : SimpleGraph V) :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every primal cycle has even intersection with the crossings of a simple
facial-dual cycle in a connected framed spherical cellulation.  Euler and the
multiplicity-correct facial span replace the old cubic/two-sided package. -/
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
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start start)
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
underlying framed graph.  A hypothetical return path after deleting the
crossings would close one crossing into a primal cycle meeting the dual cycle
once, contradicting the bridge-safe parity theorem above. -/
theorem not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
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
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start start)
    (hdualCycle : walk.IsCycle) :
    ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected := by
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
      (G.deleteEdges_le (dualWalkPrimalCut data hunique walk))
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le (dualWalkPrimalCut data hunique walk))
  have hcrossingCut (step : Fin walk.length) :
      (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step).1 ∈
        dualWalkPrimalCut data hunique walk := by
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
  have hinjective := dualWalkCrossingEdge_injective_of_isCycle
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

/-- Re-express the set-valued primal cut of a dual walk as its finite graph
edge carrier.  Keeping this bridge in the framed separator layer avoids
importing an older cubic component package merely for a representation change. -/
theorem dualWalkPrimalCut_eq_finiteDeletionValueSet_dualWalkCrossingEdges
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start start) :
    dualWalkPrimalCut data hunique walk =
      GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet
        (dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk) := by
  ext edge
  rw [GoertzelV24FiniteDeletionCyclicCut.mem_edgeFinsetValueSet_iff]
  constructor
  · rintro ⟨step, hstep⟩
    let crossing := dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step
    refine ⟨crossing, ?_, hstep⟩
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      crossing).2 ⟨step, rfl⟩
  · rintro ⟨crossing, hcrossing, hvalue⟩
    rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      crossing).1 hcrossing with ⟨step, hstep⟩
    exact ⟨step, congrArg Subtype.val hstep |>.trans hvalue⟩

/-- A simple facial-dual cycle supplies a concrete finite component with a
nonempty graph-computed boundary.  This is the graph-facing part of annular
separation: it does not construct the dual cycle, choose the source's retained
side, saturate the boundary, or establish either side-cycle witness. -/
theorem exists_componentCrossingEdges_nonempty_of_dualCycle
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
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start start)
    (hdualCycle : walk.IsCycle) :
    ∃ component :
        (G.deleteEdges
          (GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet
            (dualWalkCrossingEdges
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem)) hunique walk))).ConnectedComponent,
      (GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
        (dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk) component).Nonempty := by
  apply GoertzelV24FiniteDeletionCyclicCut.exists_componentCrossingEdges_nonempty_of_not_connected hconnected
  have hnotConnected : ¬ (G.deleteEdges
      (dualWalkPrimalCut data hunique walk)).Connected :=
    not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
      data hdual hconnected heuler hunique walk hdualCycle
  rw [dualWalkPrimalCut_eq_finiteDeletionValueSet_dualWalkCrossingEdges] at hnotConnected
  exact hnotConnected

end GoertzelV24FramedDualCycleSeparator

end

end Mettapedia.GraphTheory.FourColor
