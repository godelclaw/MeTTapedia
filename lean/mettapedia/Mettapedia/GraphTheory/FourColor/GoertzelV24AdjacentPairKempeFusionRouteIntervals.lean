import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionOrderObstruction

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The contiguous part of a walk between two ordered positions in its
support. -/
def supportInterval {u v : V} (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first ≤ second) :
    G.Walk (path.support.get first) (path.support.get second) :=
  ((path.drop first.val).take (second.val - first.val)).copy
    (path.getVert_eq_support_getElem (by
      have hfirst := first.isLt
      have hlength := path.length_support
      omega))
    (by
      rw [drop_getVert, Nat.add_sub_of_le (show first.val ≤ second.val from horder)]
      exact path.getVert_eq_support_getElem (by
        have hsecond := second.isLt
        have hlength := path.length_support
        omega))

@[simp] theorem supportInterval_length {u v : V} (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first ≤ second) :
    (path.supportInterval first second horder).length =
      second.val - first.val := by
  simp only [supportInterval, length_copy, take_length, drop_length]
  apply Nat.min_eq_left
  have hsecond := second.isLt
  have hlength := path.length_support
  omega

theorem supportInterval_length_le {u v : V} (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first ≤ second) :
    (path.supportInterval first second horder).length ≤ path.length := by
  rw [supportInterval_length]
  have hsecond := second.isLt
  have hlength := path.length_support
  omega

theorem supportInterval_pos {u v : V} (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first < second) :
    0 < (path.supportInterval first second horder.le).length := by
  rw [supportInterval_length]
  omega

theorem supportInterval_isSubwalk {u v : V} (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first ≤ second) :
    (path.supportInterval first second horder).IsSubwalk path := by
  unfold supportInterval
  exact (((path.drop first.val).isSubwalk_take
      (second.val - first.val)).trans
        (path.isSubwalk_drop first.val)).copy _ _ rfl rfl

theorem IsPath.supportInterval {u v : V} {path : G.Walk u v}
    (hpath : path.IsPath)
    (first second : Fin path.support.length) (horder : first ≤ second) :
    (path.supportInterval first second horder).IsPath :=
  isPath_of_isSubwalk
    (path.supportInterval_isSubwalk first second horder) hpath

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The common edge selected by a position in the first fusion order. -/
def EvenKempeFusionLens.fusionSupportEdgeAt
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.fusionSiteCount) : G.edgeSet :=
  lens.bRoute.ambientPath.support.get
    (lens.bFusionSupportOrderEmbedding position)

/-- The interval from `first` to `second` along the first ambient route. -/
def EvenKempeFusionLens.bFusionOrderInterval
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    G.lineGraph.Walk (lens.fusionSupportEdgeAt first)
      (lens.fusionSupportEdgeAt second) :=
  lens.bRoute.ambientPath.supportInterval
    (lens.bFusionSupportOrderEmbedding first)
    (lens.bFusionSupportOrderEmbedding second) horder.le

/-- For an inversion, the oppositely ordered second-route interval is
reversed so that it has the same endpoints as the first-route interval. -/
def EvenKempeFusionLens.cFusionOrderInterval
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    G.lineGraph.Walk (lens.fusionSupportEdgeAt first)
      (lens.fusionSupportEdgeAt second) :=
  ((lens.cRoute.ambientPath.supportInterval
      (lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)))
      (lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) horder.le).reverse).copy
    (lens.support_get_fusionMonodromy_eq first).symm
    (lens.support_get_fusionMonodromy_eq second).symm

theorem EvenKempeFusionLens.bFusionOrderInterval_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second horder).IsPath := by
  exact lens.bRoute.ambientPath_isPath.supportInterval _ _ horder.le

theorem EvenKempeFusionLens.cFusionOrderInterval_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second horder).IsPath := by
  simp only [EvenKempeFusionLens.cFusionOrderInterval,
    SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.isPath_reverse_iff]
  exact lens.cRoute.ambientPath_isPath.supportInterval _ _ horder.le

theorem EvenKempeFusionLens.bFusionOrderInterval_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second horder).support ⊆
      lens.bRoute.ambientPath.support := by
  exact (lens.bRoute.ambientPath.supportInterval_isSubwalk _ _
    horder.le).support_subset

theorem EvenKempeFusionLens.cFusionOrderInterval_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second horder).support ⊆
      lens.cRoute.ambientPath.support := by
  intro edge hedge
  have hinterval : edge ∈
      (lens.cRoute.ambientPath.supportInterval
        (lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy second)))
        (lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy first))) horder.le).support := by
    simpa only [EvenKempeFusionLens.cFusionOrderInterval,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] using hedge
  exact (lens.cRoute.ambientPath.supportInterval_isSubwalk _ _
    horder.le).support_subset hinterval

/-- Common vertices of the two ambient Kempe routes form an independent
set in the line graph. -/
theorem EvenKempeFusionLens.not_adj_of_mem_both_ambient_supports
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    {first second : G.edgeSet}
    (hfirstB : first ∈ lens.bRoute.ambientPath.support)
    (hfirstC : first ∈ lens.cRoute.ambientPath.support)
    (hsecondB : second ∈ lens.bRoute.ambientPath.support)
    (hsecondC : second ∈ lens.cRoute.ambientPath.support) :
    ¬G.lineGraph.Adj first second := by
  intro hadj
  have hfirstColor : C first = a := lens.sharedColor first
    ((lens.bRoute.mem_ambientPath_support_iff first).1 hfirstB)
    ((lens.cRoute.mem_ambientPath_support_iff first).1 hfirstC)
  have hsecondColor : C second = a := lens.sharedColor second
    ((lens.bRoute.mem_ambientPath_support_iff second).1 hsecondB)
    ((lens.cRoute.mem_ambientPath_support_iff second).1 hsecondC)
  exact C.valid hadj (hfirstColor.trans hsecondColor.symm)

theorem EvenKempeFusionLens.bFusionOrderInterval_length_le_ambientPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second horder).length ≤
      lens.bRoute.ambientPath.length := by
  exact lens.bRoute.ambientPath.supportInterval_length_le _ _ horder.le

theorem EvenKempeFusionLens.cFusionOrderInterval_length_le_ambientPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (horder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second horder).length ≤
      lens.cRoute.ambientPath.length := by
  simpa only [EvenKempeFusionLens.cFusionOrderInterval,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse] using
      lens.cRoute.ambientPath.supportInterval_length_le
        (lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy second)))
        (lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy first))) horder.le

/-- The two paths supplied by an order inversion cannot coincide: their
first step would join two common route vertices, contradicting proper edge
coloring. -/
theorem EvenKempeFusionLens.bFusionOrderInterval_ne_cFusionOrderInterval
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    lens.bFusionOrderInterval first second hbOrder ≠
      lens.cFusionOrderInterval first second hcOrder := by
  intro heq
  let bInterval := lens.bFusionOrderInterval first second hbOrder
  let cInterval := lens.cFusionOrderInterval first second hcOrder
  have hbPositive : 0 < bInterval.length := by
    exact lens.bRoute.ambientPath.supportInterval_pos _ _ hbOrder
  have hadj : G.lineGraph.Adj (lens.fusionSupportEdgeAt first)
      (bInterval.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      bInterval.adj_getVert_succ (i := 0) hbPositive
  have hstartB : lens.fusionSupportEdgeAt first ∈
      lens.bRoute.ambientPath.support :=
    lens.bFusionOrderInterval_support_subset first second hbOrder
      bInterval.start_mem_support
  have hstartC : lens.fusionSupportEdgeAt first ∈
      lens.cRoute.ambientPath.support :=
    lens.cFusionOrderInterval_support_subset first second hcOrder
      cInterval.start_mem_support
  have hnextB : bInterval.getVert 1 ∈
      lens.bRoute.ambientPath.support :=
    lens.bFusionOrderInterval_support_subset first second hbOrder
      (bInterval.getVert_mem_support 1)
  have heqInterval : bInterval = cInterval := heq
  have hnextCInterval : bInterval.getVert 1 ∈ cInterval.support := by
    rw [← heqInterval]
    exact bInterval.getVert_mem_support 1
  have hnextC : bInterval.getVert 1 ∈
      lens.cRoute.ambientPath.support :=
    lens.cFusionOrderInterval_support_subset first second hcOrder
      hnextCInterval
  exact lens.not_adj_of_mem_both_ambient_supports
    hstartB hstartC hnextB hnextC hadj

/-- An order inversion therefore contains a cycle whose length is bounded
by the two route intervals that witness the inversion. -/
theorem EvenKempeFusionLens.exists_isCycle_of_ambient_order_inversion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    ∃ edge,
      edge ∈ (lens.bFusionOrderInterval first second hbOrder).support ∧
      edge ∈ (lens.cFusionOrderInterval first second hcOrder).support ∧
      ∃ cycle : G.lineGraph.Walk edge edge,
        cycle.IsCycle ∧
        cycle.length ≤
          (lens.bFusionOrderInterval first second hbOrder).length +
          (lens.cFusionOrderInterval first second hcOrder).length := by
  exact (lens.bFusionOrderInterval_isPath first second hbOrder).exists_isCycle_length_le_add_of_ne
    (lens.cFusionOrderInterval_isPath first second hcOrder)
    (lens.bFusionOrderInterval_ne_cFusionOrderInterval
      first second hbOrder hcOrder)

/-- Nonidentity fusion-site order produces a line-graph cycle strictly
shorter than the original two-route lens walk. -/
theorem EvenKempeFusionLens.exists_isCycle_length_lt_closedWalk_of_monodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hmonodromy : lens.fusionMonodromy ≠
      Equiv.refl (Fin lens.fusionSiteCount)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧ cycle.length < lens.closedWalk.length := by
  rcases lens.exists_ambientSupportOrderInversion_of_monodromy_ne_refl
    hmonodromy with
      ⟨first, second, hbOrder, hcOrder, _hfirstEdge, _hsecondEdge⟩
  rcases lens.exists_isCycle_of_ambient_order_inversion
    first second hbOrder hcOrder with
      ⟨edge, _hedgeB, _hedgeC, cycle, hcycle, hcycleLength⟩
  refine ⟨edge, cycle, hcycle, ?_⟩
  calc
    cycle.length ≤
        (lens.bFusionOrderInterval first second hbOrder).length +
          (lens.cFusionOrderInterval first second hcOrder).length :=
      hcycleLength
    _ ≤ lens.bRoute.ambientPath.length +
        lens.cRoute.ambientPath.length :=
      Nat.add_le_add
        (lens.bFusionOrderInterval_length_le_ambientPath
          first second hbOrder)
        (lens.cFusionOrderInterval_length_le_ambientPath
          first second hcOrder)
    _ < lens.closedWalk.length := by
      rw [lens.closedWalk_length]
      simp only [EvenKempePortPath.ambientPath_length]
      omega

end


end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
