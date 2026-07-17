import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionRouteIntervals

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- An interval beginning after the initial support position is strictly
shorter than the ambient walk. -/
theorem supportInterval_length_lt_of_first_pos {u v : V}
    (path : G.Walk u v)
    (first second : Fin path.support.length) (horder : first ≤ second)
    (hfirst : 0 < first.val) :
    (path.supportInterval first second horder).length < path.length := by
  rw [supportInterval_length]
  have hsecond := second.isLt
  have hlength := path.length_support
  omega

/-- A support position selecting a vertex other than the initial vertex is
positive. -/
theorem supportPosition_pos_of_get_ne_start {u v : V}
    (path : G.Walk u v) (position : Fin path.support.length)
    (hne : path.support.get position ≠ u) :
    0 < position.val := by
  by_contra hpos
  have hzero : position.val = 0 := Nat.eq_zero_of_not_pos hpos
  apply hne
  simpa [hzero] using path.support_getElem_zero

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelRouteIntervalsGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Exchange the two secondary colors and their routes in a fusion lens. -/
def EvenKempeFusionLens.swapSecondaryColors
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    data.EvenKempeFusionLens C a c b left right where
  bRoute := lens.cRoute
  cRoute := lens.bRoute
  leftConnector := lens.leftConnector.symm
  rightConnector := lens.rightConnector.symm
  sharedColor := fun edge hc hb ↦ lens.sharedColor edge hb hc

@[simp] theorem EvenKempeFusionLens.swapSecondaryColors_bRoute
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.swapSecondaryColors.bRoute = lens.cRoute := rfl

@[simp] theorem EvenKempeFusionLens.swapSecondaryColors_cRoute
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.swapSecondaryColors.cRoute = lens.bRoute := rfl

@[simp] theorem EvenKempeFusionLens.swapSecondaryColors_bcCrossSites_eq_cb
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.swapSecondaryColors.bcCrossSites lens23.swapSecondaryColors =
      lens01.cbCrossSites lens23 := rfl

@[simp] theorem EvenKempeFusionLens.swapSecondaryColors_bcCrossSitesOnSecond_eq_cb
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.swapSecondaryColors.bcCrossSitesOnSecond
        lens23.swapSecondaryColors =
      lens01.cbCrossSitesOnSecond lens23 := rfl

/-- Swapping the secondary colors identifies the first cross-channel
monodromy with the original second-channel monodromy. -/
theorem EvenKempeFusionLens.swapSecondaryColors_bcCrossMonodromy_eq_cb
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.swapSecondaryColors.bcCrossMonodromy
        lens23.swapSecondaryColors =
      lens01.cbCrossMonodromy lens23 := by
  rfl

/-- The common edge selected by a position in the first cross channel. -/
def EvenKempeFusionLens.bcCrossSupportEdgeAt
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSites lens23).length) : G.edgeSet :=
  lens01.bRoute.ambientPath.support.get
    (lens01.bcFirstSupportOrderEmbedding lens23 position)

/-- The interval from `first` to `second` along the first lens's `(a,b)`
route. -/
def EvenKempeFusionLens.bcFirstOrderInterval
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    G.lineGraph.Walk (lens01.bcCrossSupportEdgeAt lens23 first)
      (lens01.bcCrossSupportEdgeAt lens23 second) :=
  lens01.bRoute.ambientPath.supportInterval
    (lens01.bcFirstSupportOrderEmbedding lens23 first)
    (lens01.bcFirstSupportOrderEmbedding lens23 second) horder.le

/-- The oppositely ordered interval of the second lens's `(a,c)` route,
reversed to have the same endpoints as the first interval. -/
def EvenKempeFusionLens.bcSecondOrderInterval
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    G.lineGraph.Walk (lens01.bcCrossSupportEdgeAt lens23 first)
      (lens01.bcCrossSupportEdgeAt lens23 second) :=
  ((lens23.cRoute.ambientPath.supportInterval
      (lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)))
      (lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) horder.le).reverse).copy
    (lens01.support_get_bcCrossMonodromy_eq lens23 first).symm
    (lens01.support_get_bcCrossMonodromy_eq lens23 second).symm

theorem EvenKempeFusionLens.bcFirstOrderInterval_isPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    (lens01.bcFirstOrderInterval lens23 first second horder).IsPath := by
  exact lens01.bRoute.ambientPath_isPath.supportInterval _ _ horder.le

theorem EvenKempeFusionLens.bcSecondOrderInterval_isPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    (lens01.bcSecondOrderInterval lens23 first second horder).IsPath := by
  simp only [EvenKempeFusionLens.bcSecondOrderInterval,
    SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.isPath_reverse_iff]
  exact lens23.cRoute.ambientPath_isPath.supportInterval _ _ horder.le

theorem EvenKempeFusionLens.bcFirstOrderInterval_support_subset
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    (lens01.bcFirstOrderInterval lens23 first second horder).support ⊆
      lens01.bRoute.ambientPath.support := by
  exact (lens01.bRoute.ambientPath.supportInterval_isSubwalk _ _
    horder.le).support_subset

theorem EvenKempeFusionLens.bcSecondOrderInterval_support_subset
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    (lens01.bcSecondOrderInterval lens23 first second horder).support ⊆
      lens23.cRoute.ambientPath.support := by
  intro edge hedge
  have hinterval : edge ∈
      (lens23.cRoute.ambientPath.supportInterval
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 second)))
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 first))) horder.le).support := by
    simpa only [EvenKempeFusionLens.bcSecondOrderInterval,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] using hedge
  exact (lens23.cRoute.ambientPath.supportInterval_isSubwalk _ _
    horder.le).support_subset hinterval

/-- Every edge selected in the first cross channel has the common color. -/
theorem EvenKempeFusionLens.bcCrossSupportEdgeAt_color_eq
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    C (lens01.bcCrossSupportEdgeAt lens23 position) = a := by
  apply lens01.bRoute.color_eq_first_of_mem_ambientPath_supports
    hbc lens23.cRoute
  · exact List.get_mem _ _
  · change lens01.bRoute.ambientPath.support.get
        (lens01.bcFirstSupportOrderEmbedding lens23 position) ∈
      lens23.cRoute.ambientPath.support
    rw [lens01.support_get_bcCrossMonodromy_eq lens23 position]
    exact List.get_mem _ _

/-- A first-channel site lies strictly after the initial terminal in the
first route. -/
theorem EvenKempeFusionLens.bcFirstSupportOrderEmbedding_pos
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hbc : b ≠ c)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    0 < (lens01.bcFirstSupportOrderEmbedding lens23 position).val := by
  apply lens01.bRoute.ambientPath.supportPosition_pos_of_get_ne_start
  intro hedge
  apply hab
  calc
    a = C (lens01.bcCrossSupportEdgeAt lens23 position) :=
      (lens01.bcCrossSupportEdgeAt_color_eq lens23 hbc position).symm
    _ = C lens01.bRoute.leftEdge.1 := congrArg C hedge
    _ = b := lens01.bRoute.leftColor

/-- The same site, transported through cross-channel monodromy, lies
strictly after the initial terminal in the second route. -/
theorem EvenKempeFusionLens.bcSecondSupportOrderEmbedding_monodromy_pos
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hac : a ≠ c) (hbc : b ≠ c)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    0 < (lens01.bcSecondSupportOrderEmbedding lens23
      (finCongr (lens01.bcCrossSites_length_eq lens23)
        (lens01.bcCrossMonodromy lens23 position))).val := by
  apply lens23.cRoute.ambientPath.supportPosition_pos_of_get_ne_start
  intro hedge
  apply hac
  calc
    a = C (lens01.bcCrossSupportEdgeAt lens23 position) :=
      (lens01.bcCrossSupportEdgeAt_color_eq lens23 hbc position).symm
    _ = C (lens23.cRoute.ambientPath.support.get
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 position)))) :=
      congrArg C (lens01.support_get_bcCrossMonodromy_eq lens23 position)
    _ = C lens23.cRoute.leftEdge.1 := congrArg C hedge
    _ = c := lens23.cRoute.leftColor

/-- Because its first endpoint is internal, the first inversion interval is
strictly shorter than its ambient route. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_length_lt_ambientPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    (lens01.bcFirstOrderInterval lens23 first second horder).length <
      lens01.bRoute.ambientPath.length := by
  exact lens01.bRoute.ambientPath.supportInterval_length_lt_of_first_pos
    _ _ horder.le
    (lens01.bcFirstSupportOrderEmbedding_pos lens23 hab hbc first)

/-- The reversed second interval is likewise strictly shorter than its
ambient route. -/
theorem EvenKempeFusionLens.bcSecondOrderInterval_length_lt_ambientPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hac : a ≠ c) (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    (lens01.bcSecondOrderInterval lens23 first second horder).length <
      lens23.cRoute.ambientPath.length := by
  simpa only [EvenKempeFusionLens.bcSecondOrderInterval,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse] using
      lens23.cRoute.ambientPath.supportInterval_length_lt_of_first_pos
        _ _ horder.le
        (lens01.bcSecondSupportOrderEmbedding_monodromy_pos
          lens23 hac hbc second)

/-- Common vertices of the first `(a,b)` route and the second `(a,c)` route
form an independent set in the line graph. -/
theorem EvenKempeFusionLens.not_adj_of_mem_b01_c23_ambient_supports
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c) {first second : G.edgeSet}
    (hfirstB : first ∈ lens01.bRoute.ambientPath.support)
    (hfirstC : first ∈ lens23.cRoute.ambientPath.support)
    (hsecondB : second ∈ lens01.bRoute.ambientPath.support)
    (hsecondC : second ∈ lens23.cRoute.ambientPath.support) :
    ¬G.lineGraph.Adj first second := by
  intro hadj
  have hfirstColor : C first = a :=
    lens01.bRoute.color_eq_first_of_mem_ambientPath_supports
      hbc lens23.cRoute hfirstB hfirstC
  have hsecondColor : C second = a :=
    lens01.bRoute.color_eq_first_of_mem_ambientPath_supports
      hbc lens23.cRoute hsecondB hsecondC
  exact C.valid hadj (hfirstColor.trans hsecondColor.symm)

/-- The two inversion intervals cannot coincide: their first step would
join two common route vertices of the same color. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_ne_bcSecondOrderInterval
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    lens01.bcFirstOrderInterval lens23 first second hfirstOrder ≠
      lens01.bcSecondOrderInterval lens23 first second hsecondOrder := by
  intro heq
  let firstInterval :=
    lens01.bcFirstOrderInterval lens23 first second hfirstOrder
  let secondInterval :=
    lens01.bcSecondOrderInterval lens23 first second hsecondOrder
  have hpositive : 0 < firstInterval.length := by
    exact lens01.bRoute.ambientPath.supportInterval_pos _ _ hfirstOrder
  have hadj : G.lineGraph.Adj
      (lens01.bcCrossSupportEdgeAt lens23 first)
      (firstInterval.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      firstInterval.adj_getVert_succ (i := 0) hpositive
  have hstartFirst : lens01.bcCrossSupportEdgeAt lens23 first ∈
      lens01.bRoute.ambientPath.support :=
    lens01.bcFirstOrderInterval_support_subset lens23 first second
      hfirstOrder firstInterval.start_mem_support
  have hstartSecond : lens01.bcCrossSupportEdgeAt lens23 first ∈
      lens23.cRoute.ambientPath.support :=
    lens01.bcSecondOrderInterval_support_subset lens23 first second
      hsecondOrder secondInterval.start_mem_support
  have hnextFirst : firstInterval.getVert 1 ∈
      lens01.bRoute.ambientPath.support :=
    lens01.bcFirstOrderInterval_support_subset lens23 first second
      hfirstOrder (firstInterval.getVert_mem_support 1)
  have heqInterval : firstInterval = secondInterval := heq
  have hnextSecondInterval : firstInterval.getVert 1 ∈
      secondInterval.support := by
    rw [← heqInterval]
    exact firstInterval.getVert_mem_support 1
  have hnextSecond : firstInterval.getVert 1 ∈
      lens23.cRoute.ambientPath.support :=
    lens01.bcSecondOrderInterval_support_subset lens23 first second
      hsecondOrder hnextSecondInterval
  exact lens01.not_adj_of_mem_b01_c23_ambient_supports lens23 hbc
    hstartFirst hstartSecond hnextFirst hnextSecond hadj

/-- A first-channel order inversion contains a line-graph cycle supported
inside the two corresponding route intervals. -/
theorem EvenKempeFusionLens.exists_bcLineCycle_of_ambient_order_inversion
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    ∃ edge,
      edge ∈ (lens01.bcFirstOrderInterval lens23 first second
          hfirstOrder).support ∧
      edge ∈ (lens01.bcSecondOrderInterval lens23 first second
          hsecondOrder).support ∧
      ∃ cycle : G.lineGraph.Walk edge edge,
        cycle.IsCycle ∧
        cycle.length ≤
          (lens01.bcFirstOrderInterval lens23 first second
            hfirstOrder).length +
          (lens01.bcSecondOrderInterval lens23 first second
            hsecondOrder).length := by
  exact (lens01.bcFirstOrderInterval_isPath lens23 first second
      hfirstOrder).exists_isCycle_length_le_add_of_ne
    (lens01.bcSecondOrderInterval_isPath lens23 first second hsecondOrder)
    (lens01.bcFirstOrderInterval_ne_bcSecondOrderInterval lens23 hbc
      first second hfirstOrder hsecondOrder)

/-- Nonidentity first-channel monodromy therefore produces a genuine
line-graph cycle inside the two cross routes. -/
theorem EvenKempeFusionLens.exists_bcLineCycle_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧
        cycle.length ≤
          lens01.bRoute.ambientPath.length +
            lens23.cRoute.ambientPath.length := by
  rcases lens01.exists_bcAmbientSupportOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hfirstOrder, hsecondOrder,
      _hfirstEdge, _hsecondEdge⟩
  rcases lens01.exists_bcLineCycle_of_ambient_order_inversion lens23 hbc
      first second hfirstOrder hsecondOrder with
    ⟨edge, _hedgeFirst, _hedgeSecond, cycle, hcycle, hlength⟩
  refine ⟨edge, cycle, hcycle, hlength.trans ?_⟩
  exact Nat.add_le_add
    (lens01.bRoute.ambientPath.supportInterval_length_le _ _
      hfirstOrder.le)
    (by
      simpa only [EvenKempeFusionLens.bcSecondOrderInterval,
        SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse] using
        lens23.cRoute.ambientPath.supportInterval_length_le
          (lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 second)))
          (lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 first)))
          hsecondOrder.le)

/-- Nonidentity first-channel monodromy yields a cycle strictly shorter
than the sum of the two cross-route lengths. -/
theorem EvenKempeFusionLens.exists_bcLineCycle_length_lt_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧
        cycle.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  rcases lens01.exists_bcAmbientSupportOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hfirstOrder, hsecondOrder,
      _hfirstEdge, _hsecondEdge⟩
  rcases lens01.exists_bcLineCycle_of_ambient_order_inversion lens23 hbc
      first second hfirstOrder hsecondOrder with
    ⟨edge, _hedgeFirst, _hedgeSecond, cycle, hcycle, hlength⟩
  refine ⟨edge, cycle, hcycle, ?_⟩
  have hfirstLength :=
    lens01.bcFirstOrderInterval_length_lt_ambientPath lens23 hab hbc
      first second hfirstOrder
  have hsecondLength :=
    lens01.bcSecondOrderInterval_length_lt_ambientPath lens23 hac hbc
      first second hsecondOrder
  omega

/-- By secondary-color symmetry, nonidentity second-channel monodromy also
produces a line-graph cycle inside its two cross routes. -/
theorem EvenKempeFusionLens.exists_cbLineCycle_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧
        cycle.length ≤ lens01.cRoute.ambientPath.length +
          lens23.bRoute.ambientPath.length := by
  have hswap : lens01.swapSecondaryColors.bcCrossMonodromy
      lens23.swapSecondaryColors ≠
        Equiv.refl
          (Fin (lens01.swapSecondaryColors.bcCrossSites
            lens23.swapSecondaryColors).length) := by
    simpa only [EvenKempeFusionLens.swapSecondaryColors_bcCrossMonodromy_eq_cb,
      EvenKempeFusionLens.swapSecondaryColors_bcCrossSites_eq_cb]
      using hmonodromy
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors.exists_bcLineCycle_of_monodromy_ne_refl
      lens23.swapSecondaryColors hbc.symm hswap

/-- The second-channel cycle is strictly shorter than the sum of its two
cross-route lengths. -/
theorem EvenKempeFusionLens.exists_cbLineCycle_length_lt_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧
        cycle.length < lens01.cRoute.ambientPath.length +
          lens23.bRoute.ambientPath.length := by
  have hswap : lens01.swapSecondaryColors.bcCrossMonodromy
      lens23.swapSecondaryColors ≠
        Equiv.refl
          (Fin (lens01.swapSecondaryColors.bcCrossSites
            lens23.swapSecondaryColors).length) := by
    simpa only [EvenKempeFusionLens.swapSecondaryColors_bcCrossMonodromy_eq_cb,
      EvenKempeFusionLens.swapSecondaryColors_bcCrossSites_eq_cb]
      using hmonodromy
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors.exists_bcLineCycle_length_lt_of_monodromy_ne_refl
      lens23.swapSecondaryColors hac hab hbc.symm hswap

/-- Either both cross-route orders have trivial monodromy, or one channel
contains a cycle strictly shorter than the two routes carrying it. -/
theorem EvenKempeFusionLens.crossMonodromies_trivial_or_exists_shortLineCycle
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (lens01.bcCrossMonodromy lens23 =
          Equiv.refl (Fin (lens01.bcCrossSites lens23).length) ∧
        lens01.cbCrossMonodromy lens23 =
          Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) ∨
      ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
        cycle.IsCycle ∧
          (cycle.length < lens01.bRoute.ambientPath.length +
              lens23.cRoute.ambientPath.length ∨
            cycle.length < lens01.cRoute.ambientPath.length +
              lens23.bRoute.ambientPath.length) := by
  classical
  by_cases hbcMonodromy : lens01.bcCrossMonodromy lens23 =
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)
  · by_cases hcbMonodromy : lens01.cbCrossMonodromy lens23 =
        Equiv.refl (Fin (lens01.cbCrossSites lens23).length)
    · exact Or.inl ⟨hbcMonodromy, hcbMonodromy⟩
    · right
      rcases lens01.exists_cbLineCycle_length_lt_of_monodromy_ne_refl
          lens23 hab hac hbc hcbMonodromy with
        ⟨edge, cycle, hcycle, hlength⟩
      exact ⟨edge, cycle, hcycle, Or.inr hlength⟩
  · right
    rcases lens01.exists_bcLineCycle_length_lt_of_monodromy_ne_refl
        lens23 hab hac hbc hbcMonodromy with
      ⟨edge, cycle, hcycle, hlength⟩
    exact ⟨edge, cycle, hcycle, Or.inl hlength⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
