import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCoherentSplices
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphPrimalLift

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Membership in a support interval is witnessed by an ambient support
position between the interval endpoints. -/
theorem exists_support_position_of_mem_supportInterval {u v vertex : V}
    (path : G.Walk u v) (first second : Fin path.support.length)
    (horder : first ≤ second)
    (hvertex : vertex ∈ (path.supportInterval first second horder).support) :
    ∃ position : Fin path.support.length,
      first ≤ position ∧ position ≤ second ∧
        path.support.get position = vertex := by
  simp only [supportInterval, support_copy, support_take,
    drop_support_eq_support_drop_min] at hvertex
  have hfirstLength : first.val ≤ path.length := by
    have hfirst := first.isLt
    have hlength := path.length_support
    omega
  rw [Nat.min_eq_left hfirstLength] at hvertex
  rcases List.getElem_of_mem hvertex with ⟨offset, hoffset, hvalue⟩
  have hoffsetBound : offset < second.val - first.val + 1 := by
    simp only [List.length_take] at hoffset
    omega
  have hpositionLength : first.val + offset < path.support.length := by
    have hsecond := second.isLt
    omega
  refine ⟨⟨first.val + offset, hpositionLength⟩, ?_, ?_, ?_⟩
  · exact Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
  · apply Fin.mk_le_mk.mpr
    omega
  · simpa only [List.get_eq_getElem, List.getElem_take,
      List.getElem_drop] using hvalue

theorem supportInterval_getVert {u v : V}
    (path : G.Walk u v) (first second : Fin path.support.length)
    (horder : first ≤ second) (offset : Nat)
    (hoffset : offset ≤ second.val - first.val) :
    (path.supportInterval first second horder).getVert offset =
      path.getVert (first.val + offset) := by
  simp only [supportInterval, getVert_copy, take_getVert, drop_getVert]
  rw [Nat.min_eq_right hoffset]

/-- The initial vertex of a simple walk does not reappear in its support
tail. -/
theorem IsPath.start_not_mem_support_tail {u v : V}
    {path : G.Walk u v} (hpath : path.IsPath) :
    u ∉ path.support.tail := by
  have hnodup : (u :: path.support.tail).Nodup := by
    rw [path.cons_tail_support]
    exact hpath.support_nodup
  exact (List.nodup_cons.mp hnodup).1

/-- The terminal vertex of a simple walk does not occur in the support
with both endpoints trimmed. -/
theorem IsPath.end_not_mem_support_tail_dropLast {u v : V}
    {path : G.Walk u v} (hpath : path.IsPath) :
    v ∉ path.support.tail.dropLast := by
  intro hmem
  have htailNonempty : path.support.tail ≠ [] :=
    List.ne_nil_of_mem (List.mem_of_mem_dropLast hmem)
  have hlast : path.support.tail.getLast htailNonempty = v := by
    have hsupportLast : path.support.getLast? = some v := by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp), path.getLast_support]
    have hconsLast := congrArg List.getLast? path.cons_tail_support
    have htailLast : path.support.tail.getLast? = some v := by
      calc
        path.support.tail.getLast? =
            (u :: path.support.tail).getLast? := by
          simpa only [List.singleton_append] using
            (List.getLast?_append_of_ne_nil [u] htailNonempty).symm
        _ = path.support.getLast? := hconsLast
        _ = some v := hsupportLast
    rw [List.getLast?_eq_getLast_of_ne_nil htailNonempty] at htailLast
    exact Option.some.inj htailLast
  have hne := hpath.support_nodup.tail.rel_dropLast_getLast hmem
  exact hne hlast.symm

/-- Internal steps of a simple bicolored line-graph path are
primal-coherent. If two successive junctions coincided, the path vertices
two steps apart would be adjacent primal edges of the same color. -/
theorem lineGraphJunctionAt_ne_succ_of_bicolored
    {first last : G.edgeSet}
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    {a b : Mettapedia.GraphTheory.FourColor.Color}
    (walk : G.lineGraph.Walk first last) (hpath : walk.IsPath)
    (hcolors : ∀ edge ∈ walk.support, C edge = a ∨ C edge = b)
    (position : Nat) (hposition : position + 1 < walk.length) :
    walk.lineGraphJunctionAt ⟨position, by omega⟩ ≠
      walk.lineGraphJunctionAt ⟨position + 1, hposition⟩ := by
  let previousEdge : G.edgeSet := walk.getVert position
  let middleEdge : G.edgeSet := walk.getVert (position + 1)
  let nextEdge : G.edgeSet := walk.getVert (position + 2)
  have hpreviousMiddle : G.lineGraph.Adj previousEdge middleEdge := by
    exact walk.adj_getVert_succ (by omega)
  have hmiddleNext : G.lineGraph.Adj middleEdge nextEdge := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      walk.adj_getVert_succ (i := position + 1) hposition
  have hpreviousColor := hcolors previousEdge (walk.getVert_mem_support position)
  have hmiddleColor := hcolors middleEdge (walk.getVert_mem_support (position + 1))
  have hnextColor := hcolors nextEdge (walk.getVert_mem_support (position + 2))
  have hpreviousMiddleColor : C previousEdge ≠ C middleEdge :=
    C.valid hpreviousMiddle
  have hmiddleNextColor : C middleEdge ≠ C nextEdge :=
    C.valid hmiddleNext
  have hpreviousNextColor : C previousEdge = C nextEdge := by
    rcases hpreviousColor with hpa | hpb <;>
      rcases hmiddleColor with hma | hmb <;>
      rcases hnextColor with hna | hnb
    all_goals aesop
  have hpreviousNext : previousEdge ≠ nextEdge := by
    intro hedge
    have hindices := hpath.getVert_injOn
      (show position ∈ {index | index ≤ walk.length} by
        simp only [Set.mem_setOf_eq]
        omega)
      (show position + 2 ∈ {index | index ≤ walk.length} by
        simp only [Set.mem_setOf_eq]
        omega)
      hedge
    omega
  intro hjunction
  have hpreviousMem : walk.lineGraphJunctionAt ⟨position, by omega⟩ ∈
      (previousEdge.1 : Sym2 V) :=
    walk.lineGraphJunctionAt_mem_left ⟨position, by omega⟩
  have hnextMem : walk.lineGraphJunctionAt ⟨position, by omega⟩ ∈
      (nextEdge.1 : Sym2 V) := by
    rw [hjunction]
    exact walk.lineGraphJunctionAt_mem_right ⟨position + 1, hposition⟩
  have hpreviousNextAdj : G.lineGraph.Adj previousEdge nextEdge :=
    (SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hpreviousNext, walk.lineGraphJunctionAt ⟨position, by omega⟩,
        hpreviousMem, hnextMem⟩
  exact C.valid hpreviousNextAdj hpreviousNextColor

/-- An open line-graph walk is primal-coherent when successive junctions
use opposite endpoints at every internal primal edge. -/
def IsPrimalCoherent {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) : Prop :=
  ∀ (position : Nat) (hposition : position + 1 < walk.length),
    walk.lineGraphJunctionAt ⟨position, by omega⟩ ≠
      walk.lineGraphJunctionAt ⟨position + 1, hposition⟩

theorem lineGraphJunctionAt_append_left
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (position : Fin left.length) :
    (left.append right).lineGraphJunctionAt
        ⟨position.val, by simp; omega⟩ =
      left.lineGraphJunctionAt position := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := left.lineGraphJunctionAt_mem_left position
    simpa only [SimpleGraph.Walk.getVert_append, if_pos position.isLt]
      using hmem
  · have hmem := left.lineGraphJunctionAt_mem_right position
    by_cases hbefore : position.val + 1 < left.length
    · rw [SimpleGraph.Walk.getVert_append, if_pos hbefore]
      exact hmem
    · rw [SimpleGraph.Walk.getVert_append, if_neg hbefore]
      have heq : position.val + 1 = left.length := by omega
      simpa only [heq, Nat.sub_self, SimpleGraph.Walk.getVert_zero,
        SimpleGraph.Walk.getVert_length] using hmem

theorem lineGraphJunctionAt_append_right
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (position : Fin right.length) :
    (left.append right).lineGraphJunctionAt
        ⟨left.length + position.val, by simp⟩ =
      right.lineGraphJunctionAt position := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := right.lineGraphJunctionAt_mem_left position
    change right.lineGraphJunctionAt position ∈
      (((left.append right).getVert
        (left.length + position.val)).1 : Sym2 V)
    rw [SimpleGraph.Walk.getVert_append, if_neg (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hmem
  · have hmem := right.lineGraphJunctionAt_mem_right position
    change right.lineGraphJunctionAt position ∈
      (((left.append right).getVert
        (left.length + position.val + 1)).1 : Sym2 V)
    rw [SimpleGraph.Walk.getVert_append, if_neg (by omega)]
    simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hmem

/-- Two positive coherent line-graph arcs form a coherent closed walk when
their junctions also differ across the join and across the closure. -/
theorem IsPrimalCoherent.append_isPrimalCoherentClosed
    {first middle : G.edgeSet}
    {left : G.lineGraph.Walk first middle}
    {right : G.lineGraph.Walk middle first}
    (hleft : left.IsPrimalCoherent)
    (hright : right.IsPrimalCoherent)
    (hleftPositive : 0 < left.length)
    (hrightPositive : 0 < right.length)
    (hseam :
      left.lineGraphJunctionAt
          ⟨left.length - 1,
            Nat.sub_lt hleftPositive Nat.zero_lt_one⟩ ≠
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hclosing :
      right.lineGraphJunctionAt
          ⟨right.length - 1,
            Nat.sub_lt hrightPositive Nat.zero_lt_one⟩ ≠
        left.lineGraphJunctionAt ⟨0, hleftPositive⟩) :
    (left.append right).IsPrimalCoherentClosed := by
  constructor
  · intro position hposition
    by_cases hleftStep : position + 1 < left.length
    · let firstPosition : Fin left.length := ⟨position, by omega⟩
      let secondPosition : Fin left.length := ⟨position + 1, hleftStep⟩
      have hfirst := left.lineGraphJunctionAt_append_left right firstPosition
      have hsecond := left.lineGraphJunctionAt_append_left right secondPosition
      intro hjunction
      exact hleft position hleftStep
        (hfirst.symm.trans (hjunction.trans hsecond))
    · by_cases hpositionLeft : position < left.length
      · have hpositionEq : position = left.length - 1 := by omega
        subst position
        let leftLast : Fin left.length :=
          ⟨left.length - 1,
            Nat.sub_lt hleftPositive Nat.zero_lt_one⟩
        let rightFirst : Fin right.length := ⟨0, hrightPositive⟩
        have hfirst := left.lineGraphJunctionAt_append_left right leftLast
        have hsecond := left.lineGraphJunctionAt_append_right right rightFirst
        intro hjunction
        have hsecondFin :
            (⟨(left.length - 1) + 1, by omega⟩ :
              Fin (left.append right).length) =
            ⟨left.length + rightFirst.val, by simp⟩ := by
          apply Fin.ext
          dsimp only [rightFirst]
          omega
        rw [hsecondFin] at hjunction
        exact hseam (hfirst.symm.trans (hjunction.trans hsecond))
      · let rightPosition : Fin right.length :=
          ⟨position - left.length, by
            simp only [SimpleGraph.Walk.length_append] at hposition
            omega⟩
        let rightNext : Fin right.length :=
          ⟨position - left.length + 1, by
            simp only [SimpleGraph.Walk.length_append] at hposition
            omega⟩
        have hrightStep : rightPosition.val + 1 < right.length := by
          dsimp only [rightPosition]
          simp only [SimpleGraph.Walk.length_append] at hposition
          omega
        have hfirst := left.lineGraphJunctionAt_append_right right rightPosition
        have hsecond := left.lineGraphJunctionAt_append_right right rightNext
        intro hjunction
        have hfirstFin :
            (⟨position, by omega⟩ : Fin (left.append right).length) =
            ⟨left.length + rightPosition.val, by simp⟩ := by
          apply Fin.ext
          dsimp only [rightPosition]
          omega
        have hsecondFin :
            (⟨position + 1, hposition⟩ :
              Fin (left.append right).length) =
            ⟨left.length + rightNext.val, by simp⟩ := by
          apply Fin.ext
          dsimp only [rightNext]
          omega
        rw [hfirstFin, hsecondFin] at hjunction
        exact hright rightPosition.val hrightStep
          (hfirst.symm.trans (hjunction.trans hsecond))
  · intro _
    let rightLast : Fin right.length :=
      ⟨right.length - 1,
        Nat.sub_lt hrightPositive Nat.zero_lt_one⟩
    let leftFirst : Fin left.length := ⟨0, hleftPositive⟩
    have hlast := left.lineGraphJunctionAt_append_right right rightLast
    have hfirst := left.lineGraphJunctionAt_append_left right leftFirst
    intro hjunction
    have hlastFin :
        (⟨(left.append right).length - 1, by simp; omega⟩ :
          Fin (left.append right).length) =
        ⟨left.length + rightLast.val, by simp⟩ := by
      apply Fin.ext
      dsimp only [rightLast]
      simp only [SimpleGraph.Walk.length_append]
      omega
    rw [hlastFin] at hjunction
    exact hclosing (hlast.symm.trans (hjunction.trans hfirst))

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

@[simp] theorem EvenKempePortPath.ambientPath_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) (position : Nat) :
    route.ambientPath.getVert position = (route.path.getVert position).1 := by
  exact SimpleGraph.Walk.getVert_map
    (SimpleGraph.Embedding.induce
      (G := G.lineGraph) (C.bicoloredSet a b)).toHom route.path position

/-- The fusion-support embedding uses the same coordinate as the original
`(a,b)` route path. -/
theorem EvenKempeFusionLens.bFusionSupportOrderEmbedding_val_eq_pathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (position : Fin lens.fusionSiteCount) :
    (lens.bFusionSupportOrderEmbedding position).val =
      lens.bFusionPathIndex (lens.bFusionSiteAt position) := by
  let site := lens.bFusionSiteAt position
  have hembedBound :
      (lens.bFusionSupportOrderEmbedding position).val ≤
        lens.bRoute.ambientPath.length := by
    have hembed := (lens.bFusionSupportOrderEmbedding position).isLt
    have hsupport := lens.bRoute.ambientPath.length_support
    omega
  have hpathBound : lens.bFusionPathIndex site ≤
      lens.bRoute.ambientPath.length := by
    have hbounds := lens.bFusionPathIndex_bounds hab site
    rw [lens.bRoute.ambientPath_length]
    omega
  apply lens.bRoute.ambientPath_isPath.getVert_injOn
    (by simpa only [Set.mem_setOf_eq] using hembedBound)
    (by simpa only [Set.mem_setOf_eq] using hpathBound)
  calc
    lens.bRoute.ambientPath.getVert
          (lens.bFusionSupportOrderEmbedding position).val =
        lens.bRoute.ambientPath.support.get
          (lens.bFusionSupportOrderEmbedding position) :=
      lens.bRoute.ambientPath.getVert_eq_support_getElem hembedBound
    _ = lens.bFusionSites.get position :=
      (lens.bFusionSupportOrderEmbedding_preserves_edge position).symm
    _ = site.1 := rfl
    _ = lens.bRoute.ambientPath.getVert
          (lens.bFusionPathIndex site) := by
      symm
      rw [lens.bRoute.ambientPath_getVert]
      exact congrArg Subtype.val (lens.bRoute_getVert_fusionPathIndex site)

/-- The analogous support coordinate agrees with the original `(a,c)`
route path index. -/
theorem EvenKempeFusionLens.cFusionSupportOrderEmbedding_val_eq_pathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (position : Fin lens.cFusionSites.length) :
    (lens.cFusionSupportOrderEmbedding position).val =
      lens.cFusionPathIndex (lens.cFusionSiteAt position) := by
  let site := lens.cFusionSiteAt position
  have hembedBound :
      (lens.cFusionSupportOrderEmbedding position).val ≤
        lens.cRoute.ambientPath.length := by
    have hembed := (lens.cFusionSupportOrderEmbedding position).isLt
    have hsupport := lens.cRoute.ambientPath.length_support
    omega
  have hpathBound : lens.cFusionPathIndex site ≤
      lens.cRoute.ambientPath.length := by
    have hbounds := lens.cFusionPathIndex_bounds hac site
    rw [lens.cRoute.ambientPath_length]
    omega
  apply lens.cRoute.ambientPath_isPath.getVert_injOn
    (by simpa only [Set.mem_setOf_eq] using hembedBound)
    (by simpa only [Set.mem_setOf_eq] using hpathBound)
  calc
    lens.cRoute.ambientPath.getVert
          (lens.cFusionSupportOrderEmbedding position).val =
        lens.cRoute.ambientPath.support.get
          (lens.cFusionSupportOrderEmbedding position) :=
      lens.cRoute.ambientPath.getVert_eq_support_getElem hembedBound
    _ = lens.cFusionSites.get position :=
      (lens.cFusionSupportOrderEmbedding_preserves_edge position).symm
    _ = site.1 := rfl
    _ = lens.cRoute.ambientPath.getVert
          (lens.cFusionPathIndex site) := by
      symm
      rw [lens.cRoute.ambientPath_getVert]
      exact congrArg Subtype.val (lens.cRoute_getVert_fusionPathIndex site)

theorem EvenKempeFusionLens.fusionSupportEdgeAt_eq_bFusionSiteAt
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    lens.fusionSupportEdgeAt position = (lens.bFusionSiteAt position).1 :=
  (lens.bFusionSupportOrderEmbedding_preserves_edge position).symm

/-- Fusion monodromy transports a first-route position to the second-route
position naming the same shared edge. -/
theorem EvenKempeFusionLens.cFusionSiteAt_fusionMonodromy
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    lens.cFusionSiteAt
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position)) =
      lens.bFusionSiteAt position := by
  have hposition :
      finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position) =
        lens.fusionOrderEquiv position := by
    apply Fin.ext
    rfl
  rw [hposition, lens.cFusionSiteAt_fusionOrderEquiv]

theorem EvenKempeFusionLens.bFusionOrderInterval_getVert_one
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second hbOrder).getVert 1 =
      (lens.bNextVertex (lens.bFusionSiteAt first)).1 := by
  change (lens.bRoute.ambientPath.supportInterval
      (lens.bFusionSupportOrderEmbedding first)
      (lens.bFusionSupportOrderEmbedding second) hbOrder.le).getVert 1 = _
  calc
    _ = lens.bRoute.ambientPath.getVert
          ((lens.bFusionSupportOrderEmbedding first).val + 1) :=
      lens.bRoute.ambientPath.supportInterval_getVert
        (lens.bFusionSupportOrderEmbedding first)
        (lens.bFusionSupportOrderEmbedding second) hbOrder.le 1 (by omega)
    _ = _ := by
      rw [lens.bFusionSupportOrderEmbedding_val_eq_pathIndex hab first,
        lens.bRoute.ambientPath_getVert]
      rfl

theorem EvenKempeFusionLens.bFusionOrderInterval_getVert_penultimate
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second hbOrder).getVert
        ((lens.bFusionOrderInterval first second hbOrder).length - 1) =
      (lens.bPreviousVertex (lens.bFusionSiteAt second)).1 := by
  let bInterval := lens.bFusionOrderInterval first second hbOrder
  have hlength : bInterval.length =
      (lens.bFusionSupportOrderEmbedding second).val -
        (lens.bFusionSupportOrderEmbedding first).val := by
    exact lens.bRoute.ambientPath.supportInterval_length
      (lens.bFusionSupportOrderEmbedding first)
      (lens.bFusionSupportOrderEmbedding second) hbOrder.le
  change (lens.bRoute.ambientPath.supportInterval
      (lens.bFusionSupportOrderEmbedding first)
      (lens.bFusionSupportOrderEmbedding second) hbOrder.le).getVert
        (bInterval.length - 1) = _
  calc
    _ = lens.bRoute.ambientPath.getVert
          ((lens.bFusionSupportOrderEmbedding first).val +
            (bInterval.length - 1)) :=
      lens.bRoute.ambientPath.supportInterval_getVert
        (lens.bFusionSupportOrderEmbedding first)
        (lens.bFusionSupportOrderEmbedding second) hbOrder.le
        (bInterval.length - 1) (by omega)
    _ = lens.bRoute.ambientPath.getVert
          ((lens.bFusionSupportOrderEmbedding second).val - 1) := by
      congr 1
      omega
    _ = lens.bRoute.ambientPath.getVert
          (lens.bFusionPathIndex (lens.bFusionSiteAt second) - 1) := by
      rw [lens.bFusionSupportOrderEmbedding_val_eq_pathIndex hab second]
    _ = _ := by
      rw [lens.bRoute.ambientPath_getVert]
      rfl

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (offset : Nat)
    (hoffset : offset ≤
      (lens.cFusionOrderInterval first second hcOrder).length) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.getVert offset =
      lens.cRoute.ambientPath.getVert
        ((lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy second))).val + offset) := by
  simp only [EvenKempeFusionLens.cFusionOrderInterval,
    SimpleGraph.Walk.reverse_copy, SimpleGraph.Walk.reverse_reverse,
    SimpleGraph.Walk.getVert_copy]
  exact lens.cRoute.ambientPath.supportInterval_getVert
    (lens.cFusionSupportOrderEmbedding
      (finCongr lens.fusionSites_length_eq
        (lens.fusionMonodromy second)))
    (lens.cFusionSupportOrderEmbedding
      (finCongr lens.fusionSites_length_eq
        (lens.fusionMonodromy first)))
    hcOrder.le offset (by
      simpa only [EvenKempeFusionLens.cFusionOrderInterval,
        SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.supportInterval_length] using hoffset)

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_getVert_one
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.getVert 1 =
      (lens.cNextVertex (lens.bFusionSiteAt second)).1 := by
  have hlength : 1 ≤
      (lens.cFusionOrderInterval first second hcOrder).length := by
    simp only [EvenKempeFusionLens.cFusionOrderInterval,
      SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.supportInterval_length]
    omega
  calc
    _ = lens.cRoute.ambientPath.getVert
          ((lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy second))).val + 1) :=
      lens.cFusionOrderInterval_reverse_getVert
        first second hcOrder 1 hlength
    _ = lens.cRoute.ambientPath.getVert
          (lens.cFusionPathIndex
            (lens.cFusionSiteAt
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy second))) + 1) := by
      rw [lens.cFusionSupportOrderEmbedding_val_eq_pathIndex hac]
    _ = (lens.cNextVertex
          (lens.cFusionSiteAt
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy second)))).1 := by
      rw [lens.cRoute.ambientPath_getVert]
      rfl
    _ = (lens.cNextVertex (lens.bFusionSiteAt second)).1 := by
      rw [lens.cFusionSiteAt_fusionMonodromy second]

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_getVert_penultimate
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.getVert
        ((lens.cFusionOrderInterval first second hcOrder).length - 1) =
      (lens.cPreviousVertex (lens.bFusionSiteAt first)).1 := by
  let cInterval := lens.cFusionOrderInterval first second hcOrder
  let low := lens.cFusionSupportOrderEmbedding
    (finCongr lens.fusionSites_length_eq
      (lens.fusionMonodromy second))
  let high := lens.cFusionSupportOrderEmbedding
    (finCongr lens.fusionSites_length_eq
      (lens.fusionMonodromy first))
  have hlength : cInterval.length = high.val - low.val := by
    simp only [cInterval, high, low,
      EvenKempeFusionLens.cFusionOrderInterval,
      SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.supportInterval_length]
  calc
    _ = lens.cRoute.ambientPath.getVert
          (low.val + (cInterval.length - 1)) :=
      lens.cFusionOrderInterval_reverse_getVert first second hcOrder
        (cInterval.length - 1) (Nat.sub_le _ _)
    _ = lens.cRoute.ambientPath.getVert (high.val - 1) := by
      congr 1
      omega
    _ = lens.cRoute.ambientPath.getVert
          ((lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy first))).val - 1) := by
      rfl
    _ = lens.cRoute.ambientPath.getVert
          (lens.cFusionPathIndex
            (lens.cFusionSiteAt
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy first))) - 1) := by
      rw [lens.cFusionSupportOrderEmbedding_val_eq_pathIndex hac]
    _ = (lens.cPreviousVertex
          (lens.cFusionSiteAt
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy first)))).1 := by
      rw [lens.cRoute.ambientPath_getVert]
      rfl
    _ = (lens.cPreviousVertex (lens.bFusionSiteAt first)).1 := by
      rw [lens.cFusionSiteAt_fusionMonodromy first]

theorem EvenKempeFusionLens.bFusionOrderInterval_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    0 < (lens.bFusionOrderInterval first second hbOrder).length := by
  change 0 < (lens.bRoute.ambientPath.supportInterval
    (lens.bFusionSupportOrderEmbedding first)
    (lens.bFusionSupportOrderEmbedding second) hbOrder.le).length
  rw [lens.bRoute.ambientPath.supportInterval_length]
  omega

theorem EvenKempeFusionLens.cFusionOrderInterval_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    0 < (lens.cFusionOrderInterval first second hcOrder).length := by
  simp only [EvenKempeFusionLens.cFusionOrderInterval,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.supportInterval_length]
  omega

theorem EvenKempeFusionLens.bFusionOrderInterval_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second hbOrder).lineGraphJunctionAt
        ⟨0, lens.bFusionOrderInterval_length_pos first second hbOrder⟩ =
      lens.bExitVertex hab (lens.bFusionSiteAt first) := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.bExitVertex_mem_fusionEdge hab
      (lens.bFusionSiteAt first)
    simpa only [SimpleGraph.Walk.getVert_zero,
      lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using hmem
  · have hmem := lens.bExitVertex_mem_nextEdge hab
      (lens.bFusionSiteAt first)
    simpa only [lens.bFusionOrderInterval_getVert_one hab first second hbOrder]
      using hmem

theorem EvenKempeFusionLens.bFusionOrderInterval_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    let interval := lens.bFusionOrderInterval first second hbOrder
    interval.lineGraphJunctionAt
        ⟨interval.length - 1,
          Nat.sub_lt (lens.bFusionOrderInterval_length_pos
            first second hbOrder) Nat.zero_lt_one⟩ =
      lens.bEntryVertex hab (lens.bFusionSiteAt second) := by
  dsimp only
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.bEntryVertex_mem_previousEdge hab
      (lens.bFusionSiteAt second)
    simpa only [lens.bFusionOrderInterval_getVert_penultimate
      hab first second hbOrder] using hmem
  · have hmem := lens.bEntryVertex_mem_fusionEdge hab
      (lens.bFusionSiteAt second)
    simpa only [Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt
          (lens.bFusionOrderInterval_length_pos first second hbOrder))),
      SimpleGraph.Walk.getVert_length,
      lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using hmem

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using
          lens.cFusionOrderInterval_length_pos first second hcOrder⟩ =
      lens.cExitVertex hac (lens.bFusionSiteAt second) := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cExitVertex_mem_fusionEdge hac
      (lens.bFusionSiteAt second)
    simpa only [SimpleGraph.Walk.getVert_zero,
      lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using hmem
  · have hmem := lens.cExitVertex_mem_nextEdge hac
      (lens.bFusionSiteAt second)
    simpa only [lens.cFusionOrderInterval_reverse_getVert_one
      hac first second hcOrder] using hmem

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    let interval := (lens.cFusionOrderInterval first second hcOrder).reverse
    interval.lineGraphJunctionAt
        ⟨interval.length - 1,
          Nat.sub_lt (by
            dsimp only [interval]
            simpa only [SimpleGraph.Walk.length_reverse] using
              lens.cFusionOrderInterval_length_pos first second hcOrder)
            Nat.zero_lt_one⟩ =
      lens.cEntryVertex hac (lens.bFusionSiteAt first) := by
  dsimp only
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cEntryVertex_mem_previousEdge hac
      (lens.bFusionSiteAt first)
    simpa only [SimpleGraph.Walk.length_reverse,
      lens.cFusionOrderInterval_reverse_getVert_penultimate
        hac first second hcOrder] using hmem
  · have hmem := lens.cEntryVertex_mem_fusionEdge hac
      (lens.bFusionSiteAt first)
    have hpositive : 0 <
        (lens.cFusionOrderInterval first second hcOrder).reverse.length := by
      simpa only [SimpleGraph.Walk.length_reverse] using
        lens.cFusionOrderInterval_length_pos first second hcOrder
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hpositive)),
      SimpleGraph.Walk.getVert_length]
    simpa only [lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using hmem

theorem EvenKempeFusionLens.bFusionOrderInterval_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second hbOrder).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := lens.bFusionOrderInterval first second hbOrder)
    (hpath := lens.bFusionOrderInterval_isPath first second hbOrder)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ lens.bRoute.ambientPath.support :=
        lens.bFusionOrderInterval_support_subset first second hbOrder hedge
      rcases (lens.bRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := (lens.cFusionOrderInterval first second hcOrder).reverse)
    (hpath :=
      (lens.cFusionOrderInterval first second hcOrder).isPath_reverse_iff.mpr
        (lens.cFusionOrderInterval_isPath first second hcOrder))
    (hcolors := by
      intro edge hedge
      have hcInterval : edge ∈
          (lens.cFusionOrderInterval first second hcOrder).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hedge
      have hambient : edge ∈ lens.cRoute.ambientPath.support :=
        lens.cFusionOrderInterval_support_subset first second hcOrder hcInterval
      rcases (lens.cRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

/-- Between consecutive fusion positions on the first route, a common route
edge in the interval is necessarily one of its two endpoints. -/
theorem EvenKempeFusionLens.eq_endpoint_of_mem_bFusionOrderInterval_of_mem_cSupport
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hadjacent : first.val + 1 = second.val)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    {edge : G.edgeSet}
    (hbInterval : edge ∈
      (lens.bFusionOrderInterval first second hbOrder).support)
    (hcSupport : edge ∈ lens.cRoute.ambientPath.support) :
    edge = lens.fusionSupportEdgeAt first ∨
      edge = lens.fusionSupportEdgeAt second := by
  have hbSupport : edge ∈ lens.bRoute.ambientPath.support :=
    lens.bFusionOrderInterval_support_subset first second hbOrder hbInterval
  have hfusion : edge ∈ lens.bFusionSites :=
    (lens.mem_bFusionSites_iff edge).2 ⟨hbSupport, hcSupport⟩
  rcases List.get_of_mem hfusion with ⟨fusionPosition, hfusionValue⟩
  have hbRawInterval : edge ∈
      (lens.bRoute.ambientPath.supportInterval
        (lens.bFusionSupportOrderEmbedding first)
        (lens.bFusionSupportOrderEmbedding second) hbOrder.le).support := by
    change edge ∈
      (lens.bRoute.ambientPath.supportInterval
        (lens.bFusionSupportOrderEmbedding first)
        (lens.bFusionSupportOrderEmbedding second) hbOrder.le).support at hbInterval
    exact hbInterval
  rcases lens.bRoute.ambientPath.exists_support_position_of_mem_supportInterval
      (lens.bFusionSupportOrderEmbedding first)
      (lens.bFusionSupportOrderEmbedding second) hbOrder.le hbRawInterval with
    ⟨ambientPosition, hfirstAmbient, hambientSecond, hambientValue⟩
  have hembeddingPosition :
      lens.bFusionSupportOrderEmbedding fusionPosition = ambientPosition := by
    apply (lens.bRoute.ambientPath_isPath.support_nodup.get_inj_iff).1
    calc
      lens.bRoute.ambientPath.support.get
          (lens.bFusionSupportOrderEmbedding fusionPosition) =
          lens.bFusionSites.get fusionPosition :=
        (lens.bFusionSupportOrderEmbedding_preserves_edge
          fusionPosition).symm
      _ = edge := hfusionValue
      _ = lens.bRoute.ambientPath.support.get ambientPosition :=
        hambientValue.symm
  have hfirstFusion : first ≤ fusionPosition := by
    apply (lens.bFusionSupportOrderEmbedding.le_iff_le).1
    simpa only [hembeddingPosition] using hfirstAmbient
  have hfusionSecond : fusionPosition ≤ second := by
    apply (lens.bFusionSupportOrderEmbedding.le_iff_le).1
    simpa only [hembeddingPosition] using hambientSecond
  have hpositionValueCases : fusionPosition.val = first.val ∨
      fusionPosition.val = second.val := by
    change first.val ≤ fusionPosition.val at hfirstFusion
    change fusionPosition.val ≤ second.val at hfusionSecond
    omega
  rcases hpositionValueCases with hfirstValue | hsecondValue
  · have hposition : fusionPosition = first := Fin.ext hfirstValue
    subst fusionPosition
    left
    exact hfusionValue.symm.trans
      (lens.bFusionSupportOrderEmbedding_preserves_edge first)
  · have hposition : fusionPosition = second := Fin.ext hsecondValue
    subst fusionPosition
    right
    exact hfusionValue.symm.trans
      (lens.bFusionSupportOrderEmbedding_preserves_edge second)

/-- Between consecutive fusion positions on the second route, a common
route edge in the corresponding reversed interval is one of its endpoints. -/
theorem EvenKempeFusionLens.eq_endpoint_of_mem_cFusionOrderInterval_of_mem_bSupport
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hadjacent :
      (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)).val + 1 =
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)).val)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    {edge : G.edgeSet}
    (hcInterval : edge ∈
      (lens.cFusionOrderInterval first second hcOrder).support)
    (hbSupport : edge ∈ lens.bRoute.ambientPath.support) :
    edge = lens.fusionSupportEdgeAt first ∨
      edge = lens.fusionSupportEdgeAt second := by
  let firstC : Fin lens.cFusionSites.length :=
    finCongr lens.fusionSites_length_eq (lens.fusionMonodromy second)
  let secondC : Fin lens.cFusionSites.length :=
    finCongr lens.fusionSites_length_eq (lens.fusionMonodromy first)
  have hcSupport : edge ∈ lens.cRoute.ambientPath.support :=
    lens.cFusionOrderInterval_support_subset first second hcOrder hcInterval
  have hfusion : edge ∈ lens.cFusionSites :=
    (lens.mem_cFusionSites_iff edge).2 ⟨hcSupport, hbSupport⟩
  rcases List.get_of_mem hfusion with ⟨fusionPosition, hfusionValue⟩
  have hcRawInterval : edge ∈
      (lens.cRoute.ambientPath.supportInterval
        (lens.cFusionSupportOrderEmbedding firstC)
        (lens.cFusionSupportOrderEmbedding secondC) hcOrder.le).support := by
    simpa only [firstC, secondC,
      EvenKempeFusionLens.cFusionOrderInterval,
      SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hcInterval
  rcases lens.cRoute.ambientPath.exists_support_position_of_mem_supportInterval
      (lens.cFusionSupportOrderEmbedding firstC)
      (lens.cFusionSupportOrderEmbedding secondC) hcOrder.le hcRawInterval with
    ⟨ambientPosition, hfirstAmbient, hambientSecond, hambientValue⟩
  have hembeddingPosition :
      lens.cFusionSupportOrderEmbedding fusionPosition = ambientPosition := by
    apply (lens.cRoute.ambientPath_isPath.support_nodup.get_inj_iff).1
    calc
      lens.cRoute.ambientPath.support.get
          (lens.cFusionSupportOrderEmbedding fusionPosition) =
          lens.cFusionSites.get fusionPosition :=
        (lens.cFusionSupportOrderEmbedding_preserves_edge
          fusionPosition).symm
      _ = edge := hfusionValue
      _ = lens.cRoute.ambientPath.support.get ambientPosition :=
        hambientValue.symm
  have hfirstFusion : firstC ≤ fusionPosition := by
    apply (lens.cFusionSupportOrderEmbedding.le_iff_le).1
    simpa only [hembeddingPosition] using hfirstAmbient
  have hfusionSecond : fusionPosition ≤ secondC := by
    apply (lens.cFusionSupportOrderEmbedding.le_iff_le).1
    simpa only [hembeddingPosition] using hambientSecond
  have hpositionValueCases : fusionPosition.val = firstC.val ∨
      fusionPosition.val = secondC.val := by
    change firstC.val ≤ fusionPosition.val at hfirstFusion
    change fusionPosition.val ≤ secondC.val at hfusionSecond
    have hadjacent' : firstC.val + 1 = secondC.val := by
      simpa only [firstC, secondC] using hadjacent
    omega
  rcases hpositionValueCases with hfirstValue | hsecondValue
  · have hposition : fusionPosition = firstC := Fin.ext hfirstValue
    subst fusionPosition
    right
    exact hfusionValue.symm.trans
      ((lens.cFusionSupportOrderEmbedding_preserves_edge firstC).trans
        (lens.support_get_fusionMonodromy_eq second).symm)
  · have hposition : fusionPosition = secondC := Fin.ext hsecondValue
    subst fusionPosition
    left
    exact hfusionValue.symm.trans
      ((lens.cFusionSupportOrderEmbedding_preserves_edge secondC).trans
        (lens.support_get_fusionMonodromy_eq first).symm)

/-- The two oppositely directed inversion intervals have disjoint support
tails when the first-route fusion positions are consecutive. -/
theorem EvenKempeFusionLens.bFusionOrderInterval_tail_disjoint_cReverse_tail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hadjacent : first.val + 1 = second.val)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.bFusionOrderInterval first second hbOrder).support.tail.Disjoint
      (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail := by
  rw [List.disjoint_left]
  intro edge hbTail hcTail
  have hcInterval : edge ∈
      (lens.cFusionOrderInterval first second hcOrder).support := by
    have hcReverse : edge ∈
        (lens.cFusionOrderInterval first second hcOrder).reverse.support :=
      List.mem_of_mem_tail hcTail
    simpa only [SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hcReverse
  have hcSupport : edge ∈ lens.cRoute.ambientPath.support :=
    lens.cFusionOrderInterval_support_subset first second hcOrder hcInterval
  rcases lens.eq_endpoint_of_mem_bFusionOrderInterval_of_mem_cSupport
      first second hadjacent hbOrder (List.mem_of_mem_tail hbTail) hcSupport with
    hfirst | hsecond
  · subst edge
    have hnodup :=
      (lens.bFusionOrderInterval_isPath first second hbOrder).support_nodup
    rw [← (lens.bFusionOrderInterval first second hbOrder).cons_tail_support]
      at hnodup
    exact (List.nodup_cons.mp hnodup).1 hbTail
  · subst edge
    have hpath :
        (lens.cFusionOrderInterval first second hcOrder).reverse.IsPath :=
      (lens.cFusionOrderInterval first second hcOrder).isPath_reverse_iff.mpr
        (lens.cFusionOrderInterval_isPath first second hcOrder)
    have hnodup := hpath.support_nodup
    rw [← (lens.cFusionOrderInterval first second hcOrder).reverse.cons_tail_support]
      at hnodup
    exact (List.nodup_cons.mp hnodup).1 hcTail

/-- A consecutive order inversion gives the explicit simple line-graph
cycle, rather than merely a cycle extracted from its two paths. -/
theorem EvenKempeFusionLens.fusionOrderInversionLoop_isCycle
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hadjacent : first.val + 1 = second.val)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.fusionOrderInversionLoop first second hbOrder hcOrder).IsCycle := by
  rw [EvenKempeFusionLens.fusionOrderInversionLoop]
  apply (lens.bFusionOrderInterval_isPath first second hbOrder).isCycle_append
    ((lens.cFusionOrderInterval first second hcOrder).isPath_reverse_iff.mpr
      (lens.cFusionOrderInterval_isPath first second hcOrder))
    (lens.bFusionOrderInterval_tail_disjoint_cReverse_tail
      first second hadjacent hbOrder hcOrder)
  by_contra hlengths
  push Not at hlengths
  have hbLength :
      (lens.bFusionOrderInterval first second hbOrder).length ≤ 1 := by
    omega
  have hcReverseLength :
      (lens.cFusionOrderInterval first second hcOrder).reverse.length ≤ 1 := by
    omega
  have hcLength :
      (lens.cFusionOrderInterval first second hcOrder).length ≤ 1 := by
    simpa only [SimpleGraph.Walk.length_reverse] using hcReverseLength
  exact lens.bFusionOrderInterval_ne_cFusionOrderInterval
    first second hbOrder hcOrder
    (SimpleGraph.Walk.eq_of_length_le_one hbLength hcLength)

/-- If the two endpoint splices are coherent, the explicit adjacent
inversion cycle also satisfies the exact no-bounce condition needed for a
primal lift. -/
theorem EvenKempeFusionLens.fusionOrderInversionLoop_isPrimalCoherentClosed
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (hfirst : lens.ThroughSpliceCoherent hab hac
      (lens.bFusionSiteAt first))
    (hsecond : lens.ThroughSpliceCoherent hab hac
      (lens.bFusionSiteAt second)) :
    (lens.fusionOrderInversionLoop first second hbOrder hcOrder).IsPrimalCoherentClosed := by
  rw [EvenKempeFusionLens.fusionOrderInversionLoop]
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
    (lens.cFusionOrderInterval_reverse_isPrimalCoherent
      first second hcOrder)
    (lens.bFusionOrderInterval_length_pos first second hbOrder)
    (by simpa only [SimpleGraph.Walk.length_reverse] using
      lens.cFusionOrderInterval_length_pos first second hcOrder)
  · simpa only [lens.bFusionOrderInterval_lastJunction
        hab first second hbOrder,
      lens.cFusionOrderInterval_reverse_firstJunction
        hac first second hcOrder] using hsecond.2
  · simpa only [lens.cFusionOrderInterval_reverse_lastJunction
        hac first second hcOrder,
      lens.bFusionOrderInterval_firstJunction
        hab first second hbOrder] using hfirst.1

/-- A coherent adjacent fusion inversion gives a strictly shorter circuit
in the original primal graph. Its edge run is exactly the tail of the
explicit line-graph inversion cycle. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_adjacentInversion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (first second : Fin lens.fusionSiteCount)
    (hadjacent : first.val + 1 = second.val)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (hfirst : lens.ThroughSpliceCoherent hab hac
      (lens.bFusionSiteAt first))
    (hsecond : lens.ThroughSpliceCoherent hab hac
      (lens.bFusionSiteAt second)) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens.closedWalk.length ∧
        circuit.edges =
          (lens.fusionOrderInversionLoop first second hbOrder hcOrder).support.tail.map
            Subtype.val := by
  let loop := lens.fusionOrderInversionLoop first second hbOrder hcOrder
  have hcycle : loop.IsCycle := by
    exact lens.fusionOrderInversionLoop_isCycle
      first second hadjacent hbOrder hcOrder
  have hpositive : 0 < loop.length := by
    have hthree := hcycle.three_le_length
    omega
  have hcoherent : loop.IsPrimalCoherentClosed := by
    exact lens.fusionOrderInversionLoop_isPrimalCoherentClosed
      hab hac first second hbOrder hcOrder hfirst hsecond
  let circuit := loop.primalLift hpositive hcoherent
  refine ⟨loop.lineGraphJunctionAt ⟨0, hpositive⟩, circuit, ?_, ?_, ?_⟩
  · exact loop.primalLift_isCircuit_of_isCycle
      hpositive hcoherent hcycle
  · rw [loop.primalLift_length hpositive hcoherent]
    exact lens.fusionOrderInversionLoop_length_lt_closedWalk
      first second hbOrder hcOrder
  · exact loop.primalLift_edges_eq_map_tail_support
      hpositive hcoherent

/-- Thus signed fusion nontriviality has a primal conclusion on its positive
branch: either it produces a strictly shorter primal circuit, or it exposes
the remaining coherent-return branch. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_or_coherentReturn_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    (∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length) ∨
      ∃ position : Fin lens.fusionSiteCount,
        (lens.fusionSiteLeftReturnLoop
            (lens.bFusionSiteAt position)).length < lens.closedWalk.length ∧
        lens.ReturnSpliceCoherent hab hac
          (lens.bFusionSiteAt position) := by
  rcases lens.exists_positiveAdjacentInversion_or_coherentReturn_of_signedMonodromy_ne_refl
      hab hac hsigned with hinversion | hreturn
  · rcases hinversion with
      ⟨first, second, hadjacent, hbOrder, hcOrder, hfirst, hsecond⟩
    left
    rcases lens.exists_shorter_primalCircuit_of_adjacentInversion
        hab hac first second hadjacent hbOrder hcOrder hfirst hsecond with
      ⟨start, circuit, hcircuit, hshorter, _⟩
    exact ⟨start, circuit, hcircuit, hshorter⟩
  · right
    rcases hreturn with ⟨position, hcoherent⟩
    exact ⟨position,
      lens.fusionSiteLeftReturnLoop_length_lt_closedWalk
        hab hac (lens.bFusionSiteAt position), hcoherent⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
