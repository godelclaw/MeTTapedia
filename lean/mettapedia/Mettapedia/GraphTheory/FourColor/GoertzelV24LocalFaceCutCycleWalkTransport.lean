import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleTurn

/-!
# Exact-cut transport along a chain of locally cubic cycle turns

The annular closed-web graph has degree-one interface stubs, so the global
cubic trail transport theorem cannot be used on it.  This module instead
iterates the one-vertex theorem under a local hypothesis at every consecutive
pair of oriented cycle darts.

No planar separation conclusion is built into the relation: it records only
the actual nonbacktracking turn, local cubicity, and avoidance of the cut by
the unused incident edge.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open SimpleGraph

namespace SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At a vertex of a simple cycle, two distinct cycle darts exhaust its two
cycle neighbours.  A third distinct outgoing dart therefore lies outside the
cycle.  This is local and does not require the ambient graph to be cubic. -/
theorem IsCycle.third_dart_edge_not_mem_of_two_darts_mem
    {base : V} {cycle : G.Walk base base} (hcycle : cycle.IsCycle)
    (first second third : G.Dart)
    (hsecondBase : second.fst = first.fst)
    (hthirdBase : third.fst = first.fst)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirstMem : first.edge ∈ cycle.edges)
    (hsecondMem : second.edge ∈ cycle.edges) :
    third.edge ∉ cycle.edges := by
  intro hthirdMem
  have hfirstSndSecondSnd : first.snd ≠ second.snd := by
    intro hsnd
    apply hfirstSecond
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact hsecondBase.symm
    · exact hsnd
  have hfirstSndThirdSnd : first.snd ≠ third.snd := by
    intro hsnd
    apply hfirstThird
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact hthirdBase.symm
    · exact hsnd
  have hsecondSndThirdSnd : second.snd ≠ third.snd := by
    intro hsnd
    apply hsecondThird
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact hsecondBase.trans hthirdBase.symm
    · exact hsnd
  have hfirstNeighbor : first.snd ∈
      cycle.toSubgraph.neighborSet first.fst := by
    change cycle.toSubgraph.Adj first.fst first.snd
    exact cycle.mem_edges_toSubgraph.mpr hfirstMem
  have hsecondNeighbor : second.snd ∈
      cycle.toSubgraph.neighborSet first.fst := by
    change cycle.toSubgraph.Adj first.fst second.snd
    rw [← hsecondBase]
    exact cycle.mem_edges_toSubgraph.mpr hsecondMem
  have hthirdNeighbor : third.snd ∈
      cycle.toSubgraph.neighborSet first.fst := by
    change cycle.toSubgraph.Adj first.fst third.snd
    rw [← hthirdBase]
    exact cycle.mem_edges_toSubgraph.mpr hthirdMem
  have htripleSubset :
      ({first.snd, second.snd, third.snd} : Set V) ⊆
        cycle.toSubgraph.neighborSet first.fst := by
    intro vertex hvertex
    rcases hvertex with (rfl | rfl | rfl)
    · exact hfirstNeighbor
    · exact hsecondNeighbor
    · exact hthirdNeighbor
  have htripleCard :
      ({first.snd, second.snd, third.snd} : Set V).ncard = 3 := by
    simp [hfirstSndSecondSnd, hfirstSndThirdSnd,
      hsecondSndThirdSnd]
  have hfirstSupport : first.fst ∈ cycle.support :=
    cycle.mem_support_of_mem_edges hfirstMem (by
      simp [SimpleGraph.Dart.edge])
  have hcycleCard :
      (cycle.toSubgraph.neighborSet first.fst).ncard = 2 :=
    hcycle.ncard_neighborSet_toSubgraph_eq_two hfirstSupport
  have hcardLe := Set.ncard_le_ncard htripleSubset
  rw [htripleCard, hcycleCard] at hcardLe
  omega

end SimpleGraph.Walk

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Two consecutive oriented cut-cycle darts form a locally cubic turn when
they are nonbacktracking and every other edge at their common vertex avoids
the cut. -/
def FaceCutCycleTurnStep (RS : RotationSystem V E) (cut : E → Prop)
    (previous outgoing : RS.D) : Prop :=
  RS.vertOf outgoing = RS.vertOf (RS.alpha previous) ∧
    RS.alpha previous ≠ outgoing ∧
    (RS.dartsAt (RS.vertOf outgoing)).card = 3 ∧
    ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf outgoing →
      dart ≠ RS.alpha previous → dart ≠ outgoing →
      ¬cut (RS.edgeOf dart)

/-- An exact-cut label is constant on the selected oriented side of a finite
chain of locally cubic cycle turns. -/
theorem labels_eq_head_getLast_of_faceCutCycleTurnChain
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (darts : List RS.D) (hne : darts ≠ [])
    (hchain : darts.IsChain (RS.FaceCutCycleTurnStep cut)) :
    labels (dartOrbitFace RS (darts.head hne)) =
      labels (dartOrbitFace RS (darts.getLast hne)) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hresult :
      labels (dartOrbitFace RS first) =
        labels (dartOrbitFace RS
          ((first :: rest).getLast (by simp))) := by
    induction rest generalizing first with
    | nil => rfl
    | cons second rest ih =>
        have hstep : RS.FaceCutCycleTurnStep cut first second :=
          hchain.rel
        have htail : (second :: rest).IsChain
            (RS.FaceCutCycleTurnStep cut) :=
          hchain.of_cons
        have hturn :=
          labels_eq_of_cutCycle_turn_at_card_dartsAt_eq_three
            RS hrotation labels cut hexact first second
              hstep.2.2.1 hstep.1 hstep.2.1 hstep.2.2.2
        have htailLabels :
            labels (dartOrbitFace RS second) =
              labels (dartOrbitFace RS
                ((second :: rest).getLast (by simp))) :=
          ih second (by simp) htail
        calc
          labels (dartOrbitFace RS first) =
              labels (dartOrbitFace RS second) := hturn
          _ = labels (dartOrbitFace RS
                ((second :: rest).getLast (by simp))) := htailLabels
          _ = labels (dartOrbitFace RS
                ((first :: second :: rest).getLast (by simp))) := by
            simp
  simpa using hresult

end RotationSystem

namespace SimpleGraphDartRotation.Data

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance localCycleWalkGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Graph-level iteration on the oriented side of a simple cycle.  Global
cubicity is replaced by the exact local three-dart hypothesis on the darts
that occur in the cycle walk. -/
theorem cycle_labels_eq_firstDart_lastDart_of_local_cubic
    (graphData : Data G)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    {base : V} (cycle : G.Walk base base) (hcycle : cycle.IsCycle)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈ cycle.edges)
    (hlocalCubic : ∀ dart ∈ cycle.darts,
      (graphData.toRotationSystem.dartsAt
        (graphData.toRotationSystem.vertOf dart)).card = 3) :
    labels (dartOrbitFace graphData.toRotationSystem
        (cycle.firstDart hcycle.not_nil)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (cycle.lastDart hcycle.not_nil)) := by
  let RS := graphData.toRotationSystem
  have hdartsNe : cycle.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hcycle.not_nil
  have hvertices : cycle.darts.IsChain (fun first second =>
      RS.vertOf second = RS.vertOf (RS.alpha first)) := by
    apply cycle.isChain_dartAdj_darts.imp
    intro first second hadj
    change second.fst = first.symm.fst
    exact hadj.symm
  have hedges : (cycle.darts.map RS.edgeOf).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [List.map_map]
    change (cycle.darts.map SimpleGraph.Dart.edge).Nodup
    exact hcycle.isTrail.edges_nodup
  have htrailChain : cycle.darts.IsChain RS.FaceCutTrailStep :=
    RS.isChain_faceCutTrailStep_of_edgeOf_nodup
      cycle.darts hvertices hedges
  have hturnChain : cycle.darts.IsChain
      (RS.FaceCutCycleTurnStep
        (fun edge => edge.1 ∈ cycle.edges)) := by
    rw [List.isChain_iff_getElem]
    intro index hnext
    have hindex : index < cycle.darts.length :=
      Nat.lt_trans (Nat.lt_succ_self index) hnext
    let previous := cycle.darts[index]'hindex
    let outgoing := cycle.darts[index + 1]'hnext
    have hstep : RS.FaceCutTrailStep previous outgoing :=
      List.isChain_iff_getElem.mp htrailChain index hnext
    have hpreviousMemList : previous ∈ cycle.darts := by
      exact List.getElem_mem hindex
    have houtgoingMemList : outgoing ∈ cycle.darts := by
      exact List.getElem_mem hnext
    have hpreviousEdge : previous.edge ∈ cycle.edges := by
      exact List.mem_map_of_mem hpreviousMemList
    have houtgoingEdge : outgoing.edge ∈ cycle.edges := by
      exact List.mem_map_of_mem houtgoingMemList
    refine ⟨hstep.1, hstep.2, hlocalCubic outgoing
      houtgoingMemList, ?_⟩
    intro dart hbase hneArrived hneOutgoing
    change dart.edge ∉ cycle.edges
    have harrivedEdge : (RS.alpha previous).edge ∈ cycle.edges := by
      simpa [RS] using hpreviousEdge
    exact SimpleGraph.Walk.IsCycle.third_dart_edge_not_mem_of_two_darts_mem
      hcycle (RS.alpha previous) outgoing dart hstep.1
        (hbase.trans hstep.1) hstep.2 hneArrived.symm
        hneOutgoing.symm harrivedEdge houtgoingEdge
  have hlabels :=
    RS.labels_eq_head_getLast_of_faceCutCycleTurnChain
      hrotation labels (fun edge => edge.1 ∈ cycle.edges)
        hexact cycle.darts hdartsNe hturnChain
  have hfirstLabel := congrArg
    (fun dart : G.Dart =>
      labels (dartOrbitFace graphData.toRotationSystem dart))
    (cycle.firstDart_eq_head_darts hcycle.not_nil)
  have hlastLabel := congrArg
    (fun dart : G.Dart =>
      labels (dartOrbitFace graphData.toRotationSystem dart))
    (cycle.getLast_darts_eq_lastDart hdartsNe)
  exact hfirstLabel.trans (hlabels.trans hlastLabel)

end

end SimpleGraphDartRotation.Data

end Mettapedia.GraphTheory.FourColor
