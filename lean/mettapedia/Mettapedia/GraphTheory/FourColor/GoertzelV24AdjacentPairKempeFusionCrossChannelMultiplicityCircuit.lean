import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelBounceCircuit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelMultiplicityGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The interval between two cross sites along the second route when their
order agrees with the first route. -/
def EvenKempeFusionLens.bcSecondForwardInterval
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    G.lineGraph.Walk (lens01.bcCrossSupportEdgeAt lens23 first)
      (lens01.bcCrossSupportEdgeAt lens23 second) :=
  (lens23.cRoute.ambientPath.supportInterval
      (lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)))
      (lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) horder.le).copy
    (lens01.support_get_bcCrossMonodromy_eq lens23 first).symm
    (lens01.support_get_bcCrossMonodromy_eq lens23 second).symm

theorem EvenKempeFusionLens.bcSecondForwardInterval_isPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    (lens01.bcSecondForwardInterval lens23 first second horder).IsPath := by
  simp only [EvenKempeFusionLens.bcSecondForwardInterval,
    SimpleGraph.Walk.isPath_copy]
  exact lens23.cRoute.ambientPath_isPath.supportInterval _ _ horder.le

theorem EvenKempeFusionLens.bcSecondForwardInterval_support_subset
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    (lens01.bcSecondForwardInterval lens23 first second horder).support ⊆
      lens23.cRoute.ambientPath.support := by
  intro edge hedge
  have hraw : edge ∈
      (lens23.cRoute.ambientPath.supportInterval
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 first)))
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 second))) horder.le).support := by
    simpa only [EvenKempeFusionLens.bcSecondForwardInterval,
      SimpleGraph.Walk.support_copy] using hedge
  exact (lens23.cRoute.ambientPath.supportInterval_isSubwalk _ _
    horder.le).support_subset hraw

theorem EvenKempeFusionLens.bcSecondForwardInterval_length_pos
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    0 < (lens01.bcSecondForwardInterval
      lens23 first second horder).length := by
  simp only [EvenKempeFusionLens.bcSecondForwardInterval,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.supportInterval_length]
  omega

/-- Both endpoints of a forward cross interval have the shared color, so
the interval has at least two line-graph steps. -/
theorem EvenKempeFusionLens.bcSecondForwardInterval_length_two_le
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    2 ≤ (lens01.bcSecondForwardInterval
      lens23 first second horder).length := by
  let interval := lens01.bcSecondForwardInterval
    lens23 first second horder
  have hpositive : 0 < interval.length :=
    lens01.bcSecondForwardInterval_length_pos
      lens23 first second horder
  change 2 ≤ interval.length
  by_contra htwo
  have hone : interval.length = 1 := by omega
  have hadj : G.lineGraph.Adj (interval.getVert 0) (interval.getVert 1) :=
    interval.adj_getVert_succ (i := 0) (by omega)
  apply C.valid hadj
  have hstart : C (interval.getVert 0) = a := by
    rw [SimpleGraph.Walk.getVert_zero]
    exact lens01.bcCrossSupportEdgeAt_color_eq lens23 hbc first
  have hend : C (interval.getVert 1) = a := by
    rw [← hone, SimpleGraph.Walk.getVert_length]
    exact lens01.bcCrossSupportEdgeAt_color_eq lens23 hbc second
  exact hstart.trans hend.symm

theorem EvenKempeFusionLens.bcSecondForwardInterval_reverse_isPrimalCoherent
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    (lens01.bcSecondForwardInterval lens23 first second
      horder).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := (lens01.bcSecondForwardInterval
      lens23 first second horder).reverse)
    (hpath := (lens01.bcSecondForwardInterval
      lens23 first second horder).isPath_reverse_iff.mpr
        (lens01.bcSecondForwardInterval_isPath
          lens23 first second horder))
    (hcolors := by
      intro edge hedge
      have hinterval : edge ∈
          (lens01.bcSecondForwardInterval
            lens23 first second horder).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
          hedge
      have hambient : edge ∈ lens23.cRoute.ambientPath.support :=
        lens01.bcSecondForwardInterval_support_subset
          lens23 first second horder hinterval
      exact (lens23.cRoute.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- Consecutive common sites leave no common edge in the interiors of the
two forward intervals. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_tail_disjoint_secondForwardReverse_tail
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hadjacent : first.val + 1 = second.val)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    (lens01.bcFirstOrderInterval lens23 first second
        hfirstOrder).support.tail.Disjoint
      (lens01.bcSecondForwardInterval lens23 first second
        hsecondOrder).reverse.support.tail := by
  rw [List.disjoint_left]
  intro edge hfirstTail hsecondTail
  have hsecondInterval : edge ∈
      (lens01.bcSecondForwardInterval lens23 first second
        hsecondOrder).support := by
    have hreverse : edge ∈
        (lens01.bcSecondForwardInterval lens23 first second
          hsecondOrder).reverse.support :=
      List.mem_of_mem_tail hsecondTail
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hreverse
  have hsecondSupport : edge ∈ lens23.cRoute.ambientPath.support :=
    lens01.bcSecondForwardInterval_support_subset
      lens23 first second hsecondOrder hsecondInterval
  rcases lens01.eq_endpoint_of_mem_bcFirstOrderInterval_of_mem_secondSupport
      lens23 first second hadjacent hfirstOrder
      (List.mem_of_mem_tail hfirstTail) hsecondSupport with
    hfirst | hsecond
  · subst edge
    have hnodup :=
      (lens01.bcFirstOrderInterval_isPath
        lens23 first second hfirstOrder).support_nodup
    rw [← (lens01.bcFirstOrderInterval lens23 first second
      hfirstOrder).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hfirstTail
  · subst edge
    have hpath :
        (lens01.bcSecondForwardInterval lens23 first second
          hsecondOrder).reverse.IsPath :=
      (lens01.bcSecondForwardInterval lens23 first second
        hsecondOrder).isPath_reverse_iff.mpr
          (lens01.bcSecondForwardInterval_isPath
            lens23 first second hsecondOrder)
    have hnodup := hpath.support_nodup
    rw [← (lens01.bcSecondForwardInterval lens23 first second
      hsecondOrder).reverse.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hsecondTail

theorem EvenKempeFusionLens.bcSecondForwardInterval_length_lt_ambientPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hac : a ≠ c) (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    (lens01.bcSecondForwardInterval lens23 first second horder).length <
      lens23.cRoute.ambientPath.length := by
  simpa only [EvenKempeFusionLens.bcSecondForwardInterval,
    SimpleGraph.Walk.length_copy] using
      lens23.cRoute.ambientPath.supportInterval_length_lt_of_first_pos
        _ _ horder.le
        (lens01.bcSecondSupportOrderEmbedding_monodromy_pos
          lens23 hac hbc first)

/-- Two consecutive cross sites met in the same order on both routes bound
a strictly shorter primal circuit. Bounced endpoint splices are suppressed
by the closed-walk shortcut. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_bcAdjacentSameOrder
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hadjacent : first.val + 1 = second.val)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second))) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  let left := lens01.bcFirstOrderInterval
    lens23 first second hfirstOrder
  let right := (lens01.bcSecondForwardInterval
    lens23 first second hsecondOrder).reverse
  have hleftTwo : 2 ≤ left.length := by
    dsimp only [left]
    exact lens01.bcFirstOrderInterval_length_two_le lens23 hbc
      first second hfirstOrder
  have hrightTwo : 2 ≤ right.length := by
    dsimp only [right]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens01.bcSecondForwardInterval_length_two_le lens23 hbc
        first second hsecondOrder
  have hleftCoherent : left.IsPrimalCoherent := by
    dsimp only [left]
    exact lens01.bcFirstOrderInterval_isPrimalCoherent
      lens23 first second hfirstOrder
  have hrightCoherent : right.IsPrimalCoherent := by
    dsimp only [right]
    exact lens01.bcSecondForwardInterval_reverse_isPrimalCoherent
      lens23 first second hsecondOrder
  have hdisjoint : left.support.tail.Disjoint right.support.tail := by
    dsimp only [left, right]
    exact lens01.bcFirstOrderInterval_tail_disjoint_secondForwardReverse_tail
      lens23 first second hadjacent hfirstOrder hsecondOrder
  rcases SimpleGraph.Walk.exists_isPrimalCoherentClosed_length_le_of_two_arcs
      left right hleftTwo hrightTwo hleftCoherent hrightCoherent hdisjoint with
    ⟨edge, shortcut, hshortcutPositive, hshortcutCoherent,
      hshortcutLength⟩
  rcases shortcut.exists_primal_isCycle_length_le_of_primalCoherentClosed
      hshortcutPositive hshortcutCoherent with
    ⟨start, cycle, hcycle, hcycleLength⟩
  refine ⟨start, cycle, hcycle.isCircuit, ?_⟩
  have hfirstLength :=
    lens01.bcFirstOrderInterval_length_lt_ambientPath lens23 hab hbc
      first second hfirstOrder
  have hsecondLength :=
    lens01.bcSecondForwardInterval_length_lt_ambientPath lens23 hac hbc
      first second hsecondOrder
  have happendLength :
      (left.append right).length <
        lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
    dsimp only [left, right]
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  exact lt_of_le_of_lt (hcycleLength.trans hshortcutLength) happendLength

/-- Any first cross channel containing at least two sites has a strictly
shorter primal circuit: the first two sites occur either in the same or in
the opposite order on the second route. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_bcCrossSites_length_two_le
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : 2 ≤ (lens01.bcCrossSites lens23).length) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  let first : Fin (lens01.bcCrossSites lens23).length := ⟨0, by omega⟩
  let second : Fin (lens01.bcCrossSites lens23).length := ⟨1, by omega⟩
  have hadjacent : first.val + 1 = second.val := rfl
  have hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second :=
    (lens01.bcFirstSupportOrderEmbedding lens23).lt_iff_lt.mpr (by omega)
  let firstOnSecond := finCongr (lens01.bcCrossSites_length_eq lens23)
    (lens01.bcCrossMonodromy lens23 first)
  let secondOnSecond := finCongr (lens01.bcCrossSites_length_eq lens23)
    (lens01.bcCrossMonodromy lens23 second)
  have htransportNe : firstOnSecond ≠ secondOnSecond := by
    intro heq
    have hmono : lens01.bcCrossMonodromy lens23 first =
        lens01.bcCrossMonodromy lens23 second := by
      exact (finCongr (lens01.bcCrossSites_length_eq lens23)).injective heq
    have hfirstSecond : first = second :=
      (lens01.bcCrossMonodromy lens23).injective hmono
    have hvaluesNe : first.val ≠ second.val := by
      simp only [first, second]
      omega
    exact hvaluesNe (congrArg Fin.val hfirstSecond)
  have hembedNe :
      lens01.bcSecondSupportOrderEmbedding lens23 firstOnSecond ≠
        lens01.bcSecondSupportOrderEmbedding lens23 secondOnSecond :=
    (lens01.bcSecondSupportOrderEmbedding lens23).injective.ne htransportNe
  rcases lt_or_gt_of_ne hembedNe with hsame | hopposite
  · exact lens01.exists_shorter_primalCircuit_of_bcAdjacentSameOrder
      lens23 hab hac hbc first second hadjacent hfirstOrder hsame
  · exact lens01.exists_shorter_primalCircuit_of_bcAdjacentInversion_unconditional
      lens23 hab hac hbc first second hadjacent hfirstOrder hopposite

/-- The symmetric multiplicity theorem for the second cross channel. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_cbCrossSites_length_two_le
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : 2 ≤ (lens01.cbCrossSites lens23).length) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.cRoute.ambientPath.length +
          lens23.bRoute.ambientPath.length := by
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bcCrossSites_eq_cb,
    EvenKempeFusionLens.swapSecondaryColors_bRoute,
    EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors.exists_shorter_primalCircuit_of_bcCrossSites_length_two_le
      lens23.swapSecondaryColors hac hab hbc.symm hcount

/-- Unless one cross-route pair already contains a strictly shorter primal
circuit, both cross channels contain at most one common edge. -/
theorem EvenKempeFusionLens.crossChannels_subsingleton_or_exists_shortPrimalCircuit
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((lens01.bcCrossSites lens23).length ≤ 1 ∧
        (lens01.cbCrossSites lens23).length ≤ 1) ∨
      (∃ (start : V) (circuit : G.Walk start start),
          circuit.IsCircuit ∧
            circuit.length < lens01.bRoute.ambientPath.length +
              lens23.cRoute.ambientPath.length) ∨
      ∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length := by
  by_cases hbcCount : (lens01.bcCrossSites lens23).length ≤ 1
  · by_cases hcbCount : (lens01.cbCrossSites lens23).length ≤ 1
    · exact Or.inl ⟨hbcCount, hcbCount⟩
    · right
      right
      exact lens01.exists_shorter_primalCircuit_of_cbCrossSites_length_two_le
        lens23 hab hac hbc (by omega)
  · right
    left
    exact lens01.exists_shorter_primalCircuit_of_bcCrossSites_length_two_le
      lens23 hab hac hbc (by omega)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
