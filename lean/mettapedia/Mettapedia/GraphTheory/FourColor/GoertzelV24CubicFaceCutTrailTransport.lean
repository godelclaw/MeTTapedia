import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFacePairing
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutTransport
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open SimpleGraph
open SimpleGraphDartRotation

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- In a cyclic cubic dart fiber, either of two distinct darts is the
immediate successor of the other. -/
theorem rho_eq_or_rho_eq_of_cubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second : RS.D}
    (hbase : RS.vertOf second = RS.vertOf first)
    (hne : first ≠ second) :
    RS.rho first = second ∨ RS.rho second = first := by
  by_cases hforward : RS.rho first = second
  · exact Or.inl hforward
  · right
    let third := RS.rho first
    let vertex := RS.vertOf first
    have hfirstMem : first ∈ RS.dartsAt vertex := by
      simp [RotationSystem.dartsAt, vertex]
    have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
      apply Finset.one_lt_card_iff_nontrivial.mp
      rw [hcubic vertex]
      omega
    have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial := by
      simpa only [Finset.coe_sort_coe] using hnontrivialFinset
    have hfirstThird : first ≠ third := by
      exact ((rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
        hnontrivial hfirstMem).symm
    have hthirdSecond : third ≠ second := by
      exact hforward
    exact (rho_three_cycle_of_eq_second RS hcubic hrotation
      (first := first) (second := third) (third := second)
      (RS.vert_rho first) hbase hfirstThird hne hthirdSecond rfl).2

/-- Exact-cut labels agree on any two distinct darts at one cubic vertex
when both incident edges are outside the cut. -/
theorem labels_eq_of_distinct_dartsAt_of_edges_not_cut
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (first second : RS.D)
    (hbase : RS.vertOf second = RS.vertOf first)
    (hne : first ≠ second)
    (hfirst : ¬cut (RS.edgeOf first))
    (hsecond : ¬cut (RS.edgeOf second)) :
    labels (dartOrbitFace RS first) =
      labels (dartOrbitFace RS second) := by
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation hbase hne with
    hforward | hreverse
  · simpa only [hforward] using
      labels_eq_rho_of_not_cut RS labels cut hexact first hfirst
  · have hlabel :=
      labels_eq_rho_of_not_cut RS labels cut hexact second hsecond
    rw [hreverse] at hlabel
    exact hlabel.symm

/-- The local relation followed by a nonbacktracking dart trail: the next
dart starts where the previous opposite dart is based, without immediately
returning over the same edge. -/
def FaceCutTrailStep (RS : RotationSystem V E)
    (first second : RS.D) : Prop :=
  RS.vertOf second = RS.vertOf (RS.alpha first) ∧
    RS.alpha first ≠ second

/-- A vertex-compatible dart chain whose edge sequence has no repetition is
automatically nonbacktracking. -/
theorem isChain_faceCutTrailStep_of_edgeOf_nodup
    (RS : RotationSystem V E) (darts : List RS.D)
    (hvertices : darts.IsChain (fun first second =>
      RS.vertOf second = RS.vertOf (RS.alpha first)))
    (hedges : (darts.map RS.edgeOf).Nodup) :
    darts.IsChain RS.FaceCutTrailStep := by
  induction darts with
  | nil => exact .nil
  | cons first rest ih =>
      cases rest with
      | nil => exact .singleton first
      | cons second rest =>
          have hvertex := hvertices.rel
          have hverticesTail := hvertices.of_cons
          have hedgesCons :
              RS.edgeOf first ∉ (second :: rest).map RS.edgeOf ∧
                ((second :: rest).map RS.edgeOf).Nodup := by
            simpa only [List.map_cons, List.nodup_cons] using hedges
          have hedgesTail : (second :: rest).map RS.edgeOf |>.Nodup := by
            exact hedgesCons.2
          have hedgeNe : RS.edgeOf first ≠ RS.edgeOf second := by
            intro hedge
            have : RS.edgeOf first ∈ (second :: rest).map RS.edgeOf := by
              exact List.mem_map.mpr ⟨second, by simp, hedge.symm⟩
            exact hedgesCons.1 this
          have hne : RS.alpha first ≠ second := by
            intro hdart
            apply hedgeNe
            calc
              RS.edgeOf first = RS.edgeOf (RS.alpha first) :=
                (RS.edge_alpha first).symm
              _ = RS.edgeOf second := congrArg RS.edgeOf hdart
          exact .cons_cons ⟨hvertex, hne⟩
            (ih hverticesTail hedgesTail)

/-- A finite nonbacktracking dart trail carried entirely by non-cut edges
transports the exact-cut label from its first oriented side to the opposite
side of its last dart. -/
theorem labels_eq_head_alpha_getLast_of_faceCutTrail
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (darts : List RS.D) (hne : darts ≠ [])
    (hchain : darts.IsChain RS.FaceCutTrailStep)
    (hnot : ∀ dart ∈ darts, ¬cut (RS.edgeOf dart)) :
    labels (dartOrbitFace RS (darts.head hne)) =
      labels (dartOrbitFace RS
        (RS.alpha (darts.getLast hne))) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hresult :
      labels (dartOrbitFace RS first) =
        labels (dartOrbitFace RS
          (RS.alpha ((first :: rest).getLast (by simp)))) := by
    induction rest generalizing first with
    | nil =>
        exact labels_eq_alpha_of_not_cut RS labels cut hexact first
          (hnot first (by simp))
    | cons second rest ih =>
        have hstep : RS.FaceCutTrailStep first second := hchain.rel
        have htail : (second :: rest).IsChain RS.FaceCutTrailStep :=
          hchain.of_cons
        have hnotFirst : ¬cut (RS.edgeOf first) :=
          hnot first (by simp)
        have hnotAlphaFirst : ¬cut (RS.edgeOf (RS.alpha first)) := by
          rw [RS.edge_alpha]
          exact hnotFirst
        have hnotSecond : ¬cut (RS.edgeOf second) :=
          hnot second (by simp)
        have hturn := RS.labels_eq_of_distinct_dartsAt_of_edges_not_cut
          hcubic hrotation labels cut hexact (RS.alpha first) second
            hstep.1 hstep.2 hnotAlphaFirst hnotSecond
        have htailLabels := ih second (by simp) htail (by
          intro dart hdart
          exact hnot dart (by simp [hdart]))
        calc
          labels (dartOrbitFace RS first) =
              labels (dartOrbitFace RS (RS.alpha first)) :=
            labels_eq_alpha_of_not_cut RS labels cut hexact first hnotFirst
          _ = labels (dartOrbitFace RS second) := hturn
          _ = labels (dartOrbitFace RS
                (RS.alpha ((second :: rest).getLast (by simp)))) :=
            htailLabels
          _ = labels (dartOrbitFace RS
                (RS.alpha ((first :: second :: rest).getLast (by simp)))) := by
            simp
  simpa using hresult

end RotationSystem

namespace SimpleGraphDartRotation.Data

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cubicFaceCutTrailGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Graph-level trail transport. If every edge traversed by a nonempty
primal trail avoids an exact cut, its first dart and the reverse of its last
dart carry the same face-side label. -/
theorem trail_labels_eq_firstDart_alpha_lastDart_of_edges_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil) (htrail : walk.IsTrail)
    (hnot : ∀ dart ∈ walk.darts,
      ¬cut (graphData.toRotationSystem.edgeOf dart)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (walk.firstDart hnil)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha (walk.lastDart hnil))) := by
  have hdartsNe : walk.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hnil
  have hvertices : walk.darts.IsChain (fun first second =>
      graphData.toRotationSystem.vertOf second =
        graphData.toRotationSystem.vertOf
          (graphData.toRotationSystem.alpha first)) := by
    apply walk.isChain_dartAdj_darts.imp
    intro first second hadj
    change second.fst = first.symm.fst
    exact hadj.symm
  have hedges :
      (walk.darts.map graphData.toRotationSystem.edgeOf).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [List.map_map]
    change (walk.darts.map SimpleGraph.Dart.edge).Nodup
    exact htrail.edges_nodup
  have hchain : walk.darts.IsChain
      graphData.toRotationSystem.FaceCutTrailStep :=
    graphData.toRotationSystem.isChain_faceCutTrailStep_of_edgeOf_nodup
      walk.darts hvertices hedges
  have hlabels :=
    graphData.toRotationSystem.labels_eq_head_alpha_getLast_of_faceCutTrail
    hcubic hrotation labels cut hexact walk.darts hdartsNe hchain hnot
  have hfirstLabel := congrArg
    (fun dart : G.Dart =>
      labels (dartOrbitFace graphData.toRotationSystem dart))
    (walk.firstDart_eq_head_darts hnil)
  have hlastLabel := congrArg
    (fun dart : G.Dart => labels (dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.alpha dart)))
    (walk.getLast_darts_eq_lastDart hdartsNe)
  have hmiddle :
      labels (dartOrbitFace graphData.toRotationSystem
        (walk.darts.head hdartsNe)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha
            (walk.darts.getLast hdartsNe))) := by
    exact hlabels
  exact hfirstLabel.trans (hmiddle.trans hlastLabel)

/-- Edge-list form of graph-level trail transport. This is convenient when a
trail is supplied together with a support certificate rather than a dart-list
certificate. -/
theorem trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil) (htrail : walk.IsTrail)
    (hnot : ∀ edge : G.edgeSet, edge.1 ∈ walk.edges → ¬cut edge) :
    labels (dartOrbitFace graphData.toRotationSystem
        (walk.firstDart hnil)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha (walk.lastDart hnil))) := by
  apply graphData.trail_labels_eq_firstDart_alpha_lastDart_of_edges_not_cut
    hcubic hrotation labels cut hexact walk hnil htrail
  intro dart hdart
  apply hnot (graphData.toRotationSystem.edgeOf dart)
  change dart.edge ∈ walk.edges
  rw [SimpleGraph.Walk.edges]
  exact List.mem_map.mpr ⟨dart, hdart, rfl⟩

end

end SimpleGraphDartRotation.Data

end Mettapedia.GraphTheory.FourColor
