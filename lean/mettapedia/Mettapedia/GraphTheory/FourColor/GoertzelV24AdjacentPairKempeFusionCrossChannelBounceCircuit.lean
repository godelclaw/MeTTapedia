import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelPrimalCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphClosedBounceShortcut

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelBounceGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A cross interval cannot consist of one line-graph step: both endpoint
edges have the common color, whereas adjacent edges have distinct colors. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_length_two_le
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    2 ≤ (lens01.bcFirstOrderInterval lens23 first second horder).length := by
  let interval := lens01.bcFirstOrderInterval lens23 first second horder
  have hpositive : 0 < interval.length :=
    lens01.bcFirstOrderInterval_length_pos lens23 first second horder
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

/-- The oppositely ordered cross interval also has at least two steps. -/
theorem EvenKempeFusionLens.bcSecondOrderInterval_length_two_le
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    2 ≤ (lens01.bcSecondOrderInterval lens23 first second horder).length := by
  let interval := lens01.bcSecondOrderInterval lens23 first second horder
  have hpositive : 0 < interval.length :=
    lens01.bcSecondOrderInterval_length_pos lens23 first second horder
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

/-- Suppressing either or both bounced splices turns every consecutive cross
inversion into a strictly shorter primal circuit. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_bcAdjacentInversion_unconditional
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
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  let left := lens01.bcFirstOrderInterval lens23 first second hfirstOrder
  let right := (lens01.bcSecondOrderInterval
    lens23 first second hsecondOrder).reverse
  have hleftTwo : 2 ≤ left.length := by
    dsimp only [left]
    exact lens01.bcFirstOrderInterval_length_two_le lens23 hbc
      first second hfirstOrder
  have hrightTwo : 2 ≤ right.length := by
    dsimp only [right]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens01.bcSecondOrderInterval_length_two_le lens23 hbc
        first second hsecondOrder
  have hleftCoherent : left.IsPrimalCoherent := by
    dsimp only [left]
    exact lens01.bcFirstOrderInterval_isPrimalCoherent
      lens23 first second hfirstOrder
  have hrightCoherent : right.IsPrimalCoherent := by
    dsimp only [right]
    exact lens01.bcSecondOrderInterval_reverse_isPrimalCoherent
      lens23 first second hsecondOrder
  have hdisjoint : left.support.tail.Disjoint right.support.tail := by
    dsimp only [left, right]
    exact lens01.bcFirstOrderInterval_tail_disjoint_secondReverse_tail
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
    lens01.bcSecondOrderInterval_length_lt_ambientPath lens23 hac hbc
      first second hsecondOrder
  have happendLength :
      (left.append right).length <
        lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
    dsimp only [left, right]
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  exact lt_of_le_of_lt (hcycleLength.trans hshortcutLength) happendLength

/-- Nonidentity first-channel monodromy therefore produces a strictly
shorter primal circuit, with no residual splice hypothesis. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_bcMonodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  rcases lens01.exists_bcAdjacentAmbientSupportOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hadjacent, hfirstOrder, hsecondOrder⟩
  exact lens01.exists_shorter_primalCircuit_of_bcAdjacentInversion_unconditional
    lens23 hab hac hbc first second hadjacent hfirstOrder hsecondOrder

/-- The second cross channel inherits the unconditional circuit theorem by
the exact secondary-color symmetry. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_cbMonodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.cRoute.ambientPath.length +
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
    lens01.swapSecondaryColors.exists_shorter_primalCircuit_of_bcMonodromy_ne_refl
      lens23.swapSecondaryColors hac hab hbc.symm hswap

/-- Either both cross-route orders are trivial, or one cross channel carries
a primal circuit strictly shorter than the two routes that produced it. -/
theorem EvenKempeFusionLens.crossMonodromies_trivial_or_exists_shortPrimalCircuit
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (lens01.bcCrossMonodromy lens23 =
          Equiv.refl (Fin (lens01.bcCrossSites lens23).length) ∧
        lens01.cbCrossMonodromy lens23 =
          Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) ∨
      (∃ (start : V) (circuit : G.Walk start start),
          circuit.IsCircuit ∧
            circuit.length < lens01.bRoute.ambientPath.length +
              lens23.cRoute.ambientPath.length) ∨
      ∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length := by
  classical
  by_cases hbcMonodromy : lens01.bcCrossMonodromy lens23 =
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)
  · by_cases hcbMonodromy : lens01.cbCrossMonodromy lens23 =
        Equiv.refl (Fin (lens01.cbCrossSites lens23).length)
    · exact Or.inl ⟨hbcMonodromy, hcbMonodromy⟩
    · exact Or.inr (Or.inr
        (lens01.exists_shorter_primalCircuit_of_cbMonodromy_ne_refl
          lens23 hab hac hbc hcbMonodromy))
  · exact Or.inr (Or.inl
      (lens01.exists_shorter_primalCircuit_of_bcMonodromy_ne_refl
        lens23 hab hac hbc hbcMonodromy))

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
