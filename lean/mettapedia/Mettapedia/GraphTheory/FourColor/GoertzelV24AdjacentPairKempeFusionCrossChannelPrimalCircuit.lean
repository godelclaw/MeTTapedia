import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRouteIntervals
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionPrimalCircuit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelPrimalCircuitGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The explicit closed line-graph walk obtained from a first-channel order
inversion. -/
def EvenKempeFusionLens.bcOrderInversionLoop
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    G.lineGraph.Walk (lens01.bcCrossSupportEdgeAt lens23 first)
      (lens01.bcCrossSupportEdgeAt lens23 first) :=
  (lens01.bcFirstOrderInterval lens23 first second hfirstOrder).append
    (lens01.bcSecondOrderInterval lens23 first second hsecondOrder).reverse

theorem EvenKempeFusionLens.bcFirstOrderInterval_length_pos
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    0 < (lens01.bcFirstOrderInterval lens23 first second horder).length := by
  exact lens01.bRoute.ambientPath.supportInterval_pos _ _ horder

theorem EvenKempeFusionLens.bcSecondOrderInterval_length_pos
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
    0 < (lens01.bcSecondOrderInterval lens23 first second horder).length := by
  simp only [EvenKempeFusionLens.bcSecondOrderInterval,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.supportInterval_length]
  omega

/-- Each first-route inversion interval is internally primal-coherent. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_isPrimalCoherent
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second) :
    (lens01.bcFirstOrderInterval lens23 first second horder).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := lens01.bcFirstOrderInterval lens23 first second horder)
    (hpath := lens01.bcFirstOrderInterval_isPath
      lens23 first second horder)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ lens01.bRoute.ambientPath.support :=
        lens01.bcFirstOrderInterval_support_subset
          lens23 first second horder hedge
      exact (lens01.bRoute.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- The reversed second-route inversion interval is internally
primal-coherent. -/
theorem EvenKempeFusionLens.bcSecondOrderInterval_reverse_isPrimalCoherent
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
    (lens01.bcSecondOrderInterval lens23 first second horder).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := (lens01.bcSecondOrderInterval
      lens23 first second horder).reverse)
    (hpath := (lens01.bcSecondOrderInterval
      lens23 first second horder).isPath_reverse_iff.mpr
        (lens01.bcSecondOrderInterval_isPath
          lens23 first second horder))
    (hcolors := by
      intro edge hedge
      have hinterval : edge ∈
          (lens01.bcSecondOrderInterval
            lens23 first second horder).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
          hedge
      have hambient : edge ∈ lens23.cRoute.ambientPath.support :=
        lens01.bcSecondOrderInterval_support_subset
          lens23 first second horder hinterval
      exact (lens23.cRoute.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- Between consecutive first-channel positions, a common edge in the
first route interval is one of its endpoints. -/
theorem EvenKempeFusionLens.eq_endpoint_of_mem_bcFirstOrderInterval_of_mem_secondSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hadjacent : first.val + 1 = second.val)
    (horder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    {edge : G.edgeSet}
    (hinterval : edge ∈
      (lens01.bcFirstOrderInterval lens23 first second horder).support)
    (hsecondSupport : edge ∈ lens23.cRoute.ambientPath.support) :
    edge = lens01.bcCrossSupportEdgeAt lens23 first ∨
      edge = lens01.bcCrossSupportEdgeAt lens23 second := by
  have hfirstSupport : edge ∈ lens01.bRoute.ambientPath.support :=
    lens01.bcFirstOrderInterval_support_subset
      lens23 first second horder hinterval
  have hcross : edge ∈ lens01.bcCrossSites lens23 :=
    (lens01.mem_bcCrossSites_iff lens23 edge).2
      ⟨hfirstSupport, hsecondSupport⟩
  rcases List.get_of_mem hcross with ⟨crossPosition, hcrossValue⟩
  have hrawInterval : edge ∈
      (lens01.bRoute.ambientPath.supportInterval
        (lens01.bcFirstSupportOrderEmbedding lens23 first)
        (lens01.bcFirstSupportOrderEmbedding lens23 second)
        horder.le).support := by
    change edge ∈
      (lens01.bRoute.ambientPath.supportInterval
        (lens01.bcFirstSupportOrderEmbedding lens23 first)
        (lens01.bcFirstSupportOrderEmbedding lens23 second)
        horder.le).support at hinterval
    exact hinterval
  rcases lens01.bRoute.ambientPath.exists_support_position_of_mem_supportInterval
      (lens01.bcFirstSupportOrderEmbedding lens23 first)
      (lens01.bcFirstSupportOrderEmbedding lens23 second)
      horder.le hrawInterval with
    ⟨ambientPosition, hfirstAmbient, hambientSecond, hambientValue⟩
  have hembeddingPosition :
      lens01.bcFirstSupportOrderEmbedding lens23 crossPosition =
        ambientPosition := by
    apply (lens01.bRoute.ambientPath_isPath.support_nodup.get_inj_iff).1
    calc
      lens01.bRoute.ambientPath.support.get
          (lens01.bcFirstSupportOrderEmbedding lens23 crossPosition) =
          (lens01.bcCrossSites lens23).get crossPosition :=
        (lens01.bcFirstSupportOrderEmbedding_preserves_edge
          lens23 crossPosition).symm
      _ = edge := hcrossValue
      _ = lens01.bRoute.ambientPath.support.get ambientPosition :=
        hambientValue.symm
  have hfirstCross : first ≤ crossPosition := by
    apply (lens01.bcFirstSupportOrderEmbedding lens23).le_iff_le.mp
    simpa only [hembeddingPosition] using hfirstAmbient
  have hcrossSecond : crossPosition ≤ second := by
    apply (lens01.bcFirstSupportOrderEmbedding lens23).le_iff_le.mp
    simpa only [hembeddingPosition] using hambientSecond
  have hpositionCases : crossPosition.val = first.val ∨
      crossPosition.val = second.val := by
    change first.val ≤ crossPosition.val at hfirstCross
    change crossPosition.val ≤ second.val at hcrossSecond
    omega
  rcases hpositionCases with hfirstValue | hsecondValue
  · have hposition : crossPosition = first := Fin.ext hfirstValue
    subst crossPosition
    left
    exact hcrossValue.symm.trans
      (lens01.bcFirstSupportOrderEmbedding_preserves_edge lens23 first)
  · have hposition : crossPosition = second := Fin.ext hsecondValue
    subst crossPosition
    right
    exact hcrossValue.symm.trans
      (lens01.bcFirstSupportOrderEmbedding_preserves_edge lens23 second)

/-- The two oppositely directed intervals of a consecutive cross inversion
have disjoint support tails. -/
theorem EvenKempeFusionLens.bcFirstOrderInterval_tail_disjoint_secondReverse_tail
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
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) :
    (lens01.bcFirstOrderInterval lens23 first second
        hfirstOrder).support.tail.Disjoint
      (lens01.bcSecondOrderInterval lens23 first second
        hsecondOrder).reverse.support.tail := by
  rw [List.disjoint_left]
  intro edge hfirstTail hsecondTail
  have hsecondInterval : edge ∈
      (lens01.bcSecondOrderInterval lens23 first second
        hsecondOrder).support := by
    have hreverse : edge ∈
        (lens01.bcSecondOrderInterval lens23 first second
          hsecondOrder).reverse.support :=
      List.mem_of_mem_tail hsecondTail
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hreverse
  have hsecondSupport : edge ∈ lens23.cRoute.ambientPath.support :=
    lens01.bcSecondOrderInterval_support_subset
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
        (lens01.bcSecondOrderInterval lens23 first second
          hsecondOrder).reverse.IsPath :=
      (lens01.bcSecondOrderInterval lens23 first second
        hsecondOrder).isPath_reverse_iff.mpr
          (lens01.bcSecondOrderInterval_isPath
            lens23 first second hsecondOrder)
    have hnodup := hpath.support_nodup
    rw [← (lens01.bcSecondOrderInterval lens23 first second
      hsecondOrder).reverse.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hsecondTail

/-- Consecutive inverted cross sites give the explicit simple line-graph
cycle. -/
theorem EvenKempeFusionLens.bcOrderInversionLoop_isCycle
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
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
    (lens01.bcOrderInversionLoop lens23 first second
      hfirstOrder hsecondOrder).IsCycle := by
  rw [EvenKempeFusionLens.bcOrderInversionLoop]
  apply (lens01.bcFirstOrderInterval_isPath
      lens23 first second hfirstOrder).isCycle_append
    ((lens01.bcSecondOrderInterval lens23 first second
      hsecondOrder).isPath_reverse_iff.mpr
        (lens01.bcSecondOrderInterval_isPath
          lens23 first second hsecondOrder))
    (lens01.bcFirstOrderInterval_tail_disjoint_secondReverse_tail
      lens23 first second hadjacent hfirstOrder hsecondOrder)
  by_contra hlengths
  push Not at hlengths
  have hfirstLength :
      (lens01.bcFirstOrderInterval lens23 first second
        hfirstOrder).length ≤ 1 := by omega
  have hsecondReverseLength :
      (lens01.bcSecondOrderInterval lens23 first second
        hsecondOrder).reverse.length ≤ 1 := by omega
  have hsecondLength :
      (lens01.bcSecondOrderInterval lens23 first second
        hsecondOrder).length ≤ 1 := by
    simpa only [SimpleGraph.Walk.length_reverse] using hsecondReverseLength
  exact lens01.bcFirstOrderInterval_ne_bcSecondOrderInterval lens23 hbc
    first second hfirstOrder hsecondOrder
    (SimpleGraph.Walk.eq_of_length_le_one hfirstLength hsecondLength)

/-- The exact no-bounce condition at the two splices of a cross-channel
order inversion. -/
def EvenKempeFusionLens.BcOrderInversionSeamsCoherent
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first))) : Prop :=
  let firstInterval := lens01.bcFirstOrderInterval
    lens23 first second hfirstOrder
  let secondReverse := (lens01.bcSecondOrderInterval
    lens23 first second hsecondOrder).reverse
  firstInterval.lineGraphJunctionAt
      ⟨firstInterval.length - 1,
        Nat.sub_lt (lens01.bcFirstOrderInterval_length_pos
          lens23 first second hfirstOrder) Nat.zero_lt_one⟩ ≠
    secondReverse.lineGraphJunctionAt
      ⟨0, by
        simpa only [secondReverse, SimpleGraph.Walk.length_reverse] using
          lens01.bcSecondOrderInterval_length_pos
            lens23 first second hsecondOrder⟩ ∧
  secondReverse.lineGraphJunctionAt
      ⟨secondReverse.length - 1,
        Nat.sub_lt (by
          simpa only [secondReverse, SimpleGraph.Walk.length_reverse] using
            lens01.bcSecondOrderInterval_length_pos
              lens23 first second hsecondOrder) Nat.zero_lt_one⟩ ≠
    firstInterval.lineGraphJunctionAt
      ⟨0, lens01.bcFirstOrderInterval_length_pos
        lens23 first second hfirstOrder⟩

/-- Coherent endpoint splices make the explicit cross inversion cycle
primal-coherent as a closed walk. -/
theorem EvenKempeFusionLens.bcOrderInversionLoop_isPrimalCoherentClosed
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.bcCrossSites lens23).length)
    (hfirstOrder : lens01.bcFirstSupportOrderEmbedding lens23 first <
      lens01.bcFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 second)) <
      lens01.bcSecondSupportOrderEmbedding lens23
        (finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 first)))
    (hseams : lens01.BcOrderInversionSeamsCoherent lens23
      first second hfirstOrder hsecondOrder) :
    (lens01.bcOrderInversionLoop lens23 first second
      hfirstOrder hsecondOrder).IsPrimalCoherentClosed := by
  rw [EvenKempeFusionLens.bcOrderInversionLoop]
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    (lens01.bcFirstOrderInterval_isPrimalCoherent
      lens23 first second hfirstOrder)
    (lens01.bcSecondOrderInterval_reverse_isPrimalCoherent
      lens23 first second hsecondOrder)
    (lens01.bcFirstOrderInterval_length_pos
      lens23 first second hfirstOrder)
    (by simpa only [SimpleGraph.Walk.length_reverse] using
      (lens01.bcSecondOrderInterval_length_pos
        lens23 first second hsecondOrder))
  · exact hseams.1
  · exact hseams.2

/-- A coherent consecutive cross inversion lifts to a primal circuit
strictly shorter than the two cross routes. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_bcAdjacentInversion
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
          (lens01.bcCrossMonodromy lens23 first)))
    (hseams : lens01.BcOrderInversionSeamsCoherent lens23
      first second hfirstOrder hsecondOrder) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.bRoute.ambientPath.length +
          lens23.cRoute.ambientPath.length := by
  let loop := lens01.bcOrderInversionLoop lens23 first second
    hfirstOrder hsecondOrder
  have hcycle : loop.IsCycle := by
    exact lens01.bcOrderInversionLoop_isCycle lens23 hbc
      first second hadjacent hfirstOrder hsecondOrder
  have hpositive : 0 < loop.length := by
    have hthree := hcycle.three_le_length
    omega
  have hcoherent : loop.IsPrimalCoherentClosed := by
    exact lens01.bcOrderInversionLoop_isPrimalCoherentClosed lens23
      first second hfirstOrder hsecondOrder hseams
  let circuit := loop.primalLift hpositive hcoherent
  refine ⟨loop.lineGraphJunctionAt ⟨0, hpositive⟩,
    circuit, loop.primalLift_isCircuit_of_isCycle
      hpositive hcoherent hcycle, ?_⟩
  rw [loop.primalLift_length hpositive hcoherent]
  dsimp only [loop]
  rw [EvenKempeFusionLens.bcOrderInversionLoop,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  have hfirstLength :=
    lens01.bcFirstOrderInterval_length_lt_ambientPath lens23 hab hbc
      first second hfirstOrder
  have hsecondLength :=
    lens01.bcSecondOrderInterval_length_lt_ambientPath lens23 hac hbc
      first second hsecondOrder
  omega

/-- Nontrivial first-channel monodromy has an inversion at two consecutive
positions of the first route order. -/
theorem EvenKempeFusionLens.exists_bcAdjacentAmbientSupportOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.bcCrossSites lens23).length,
      first.val + 1 = second.val ∧
        lens01.bcFirstSupportOrderEmbedding lens23 first <
          lens01.bcFirstSupportOrderEmbedding lens23 second ∧
        lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 second)) <
          lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 first)) := by
  rcases finPermutation_exists_adjacent_inversion_of_ne_refl
      (lens01.bcCrossMonodromy lens23) hmonodromy with
    ⟨first, second, hadjacent, hreverse⟩
  have hfirstSecond : first < second := by
    rw [Fin.lt_def]
    omega
  refine ⟨first, second, hadjacent,
    (lens01.bcFirstSupportOrderEmbedding lens23).lt_iff_lt.mpr
      hfirstSecond, ?_⟩
  exact (lens01.bcSecondSupportOrderEmbedding lens23).lt_iff_lt.mpr
    hreverse

/-- Thus nontrivial first-channel order has an exact geometric alternative:
a strictly shorter primal circuit, or a consecutive inversion with a bounce
at one of its two splices. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_or_incoherentBcSeam_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    (∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.bRoute.ambientPath.length +
            lens23.cRoute.ambientPath.length) ∨
      ∃ first second : Fin (lens01.bcCrossSites lens23).length,
        first.val + 1 = second.val ∧
          ∃ hfirstOrder :
              lens01.bcFirstSupportOrderEmbedding lens23 first <
                lens01.bcFirstSupportOrderEmbedding lens23 second,
            ∃ hsecondOrder :
                lens01.bcSecondSupportOrderEmbedding lens23
                    (finCongr (lens01.bcCrossSites_length_eq lens23)
                      (lens01.bcCrossMonodromy lens23 second)) <
                  lens01.bcSecondSupportOrderEmbedding lens23
                    (finCongr (lens01.bcCrossSites_length_eq lens23)
                      (lens01.bcCrossMonodromy lens23 first)),
              ¬lens01.BcOrderInversionSeamsCoherent lens23
                first second hfirstOrder hsecondOrder := by
  rcases lens01.exists_bcAdjacentAmbientSupportOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hadjacent, hfirstOrder, hsecondOrder⟩
  by_cases hseams : lens01.BcOrderInversionSeamsCoherent lens23
      first second hfirstOrder hsecondOrder
  · left
    exact lens01.exists_shorter_primalCircuit_of_bcAdjacentInversion
      lens23 hab hac hbc first second hadjacent
      hfirstOrder hsecondOrder hseams
  · right
    exact ⟨first, second, hadjacent, hfirstOrder, hsecondOrder, hseams⟩

/-- The no-bounce condition for a second-channel inversion, obtained by
the exact secondary-color symmetry. -/
def EvenKempeFusionLens.CbOrderInversionSeamsCoherent
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (first second : Fin (lens01.cbCrossSites lens23).length)
    (hfirstOrder : lens01.cbFirstSupportOrderEmbedding lens23 first <
      lens01.cbFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.cbSecondSupportOrderEmbedding lens23
        (finCongr (lens01.cbCrossSites_length_eq lens23)
          (lens01.cbCrossMonodromy lens23 second)) <
      lens01.cbSecondSupportOrderEmbedding lens23
        (finCongr (lens01.cbCrossSites_length_eq lens23)
          (lens01.cbCrossMonodromy lens23 first))) : Prop :=
  lens01.swapSecondaryColors.BcOrderInversionSeamsCoherent
    lens23.swapSecondaryColors first second hfirstOrder hsecondOrder

/-- A coherent consecutive second-channel inversion has the symmetric
strictly shorter primal circuit. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_cbAdjacentInversion
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (first second : Fin (lens01.cbCrossSites lens23).length)
    (hadjacent : first.val + 1 = second.val)
    (hfirstOrder : lens01.cbFirstSupportOrderEmbedding lens23 first <
      lens01.cbFirstSupportOrderEmbedding lens23 second)
    (hsecondOrder : lens01.cbSecondSupportOrderEmbedding lens23
        (finCongr (lens01.cbCrossSites_length_eq lens23)
          (lens01.cbCrossMonodromy lens23 second)) <
      lens01.cbSecondSupportOrderEmbedding lens23
        (finCongr (lens01.cbCrossSites_length_eq lens23)
          (lens01.cbCrossMonodromy lens23 first)))
    (hseams : lens01.CbOrderInversionSeamsCoherent lens23
      first second hfirstOrder hsecondOrder) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
        circuit.length < lens01.cRoute.ambientPath.length +
          lens23.bRoute.ambientPath.length := by
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors.exists_shorter_primalCircuit_of_bcAdjacentInversion
      lens23.swapSecondaryColors hac hab hbc.symm first second
        hadjacent hfirstOrder hsecondOrder hseams

/-- Nontrivial second-channel monodromy likewise has a consecutive ambient
support inversion. -/
theorem EvenKempeFusionLens.exists_cbAdjacentAmbientSupportOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.cbCrossSites lens23).length,
      first.val + 1 = second.val ∧
        lens01.cbFirstSupportOrderEmbedding lens23 first <
          lens01.cbFirstSupportOrderEmbedding lens23 second ∧
        lens01.cbSecondSupportOrderEmbedding lens23
            (finCongr (lens01.cbCrossSites_length_eq lens23)
              (lens01.cbCrossMonodromy lens23 second)) <
          lens01.cbSecondSupportOrderEmbedding lens23
            (finCongr (lens01.cbCrossSites_length_eq lens23)
              (lens01.cbCrossMonodromy lens23 first)) := by
  rcases finPermutation_exists_adjacent_inversion_of_ne_refl
      (lens01.cbCrossMonodromy lens23) hmonodromy with
    ⟨first, second, hadjacent, hreverse⟩
  have hfirstSecond : first < second := by
    rw [Fin.lt_def]
    omega
  refine ⟨first, second, hadjacent,
    (lens01.cbFirstSupportOrderEmbedding lens23).lt_iff_lt.mpr
      hfirstSecond, ?_⟩
  exact (lens01.cbSecondSupportOrderEmbedding lens23).lt_iff_lt.mpr
    hreverse

/-- The second-channel version of the circuit-or-bounce alternative. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_or_incoherentCbSeam_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    (∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length) ∨
      ∃ first second : Fin (lens01.cbCrossSites lens23).length,
        first.val + 1 = second.val ∧
          ∃ hfirstOrder :
              lens01.cbFirstSupportOrderEmbedding lens23 first <
                lens01.cbFirstSupportOrderEmbedding lens23 second,
            ∃ hsecondOrder :
                lens01.cbSecondSupportOrderEmbedding lens23
                    (finCongr (lens01.cbCrossSites_length_eq lens23)
                      (lens01.cbCrossMonodromy lens23 second)) <
                  lens01.cbSecondSupportOrderEmbedding lens23
                    (finCongr (lens01.cbCrossSites_length_eq lens23)
                      (lens01.cbCrossMonodromy lens23 first)),
              ¬lens01.CbOrderInversionSeamsCoherent lens23
                first second hfirstOrder hsecondOrder := by
  rcases lens01.exists_cbAdjacentAmbientSupportOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hadjacent, hfirstOrder, hsecondOrder⟩
  by_cases hseams : lens01.CbOrderInversionSeamsCoherent lens23
      first second hfirstOrder hsecondOrder
  · left
    exact lens01.exists_shorter_primalCircuit_of_cbAdjacentInversion
      lens23 hab hac hbc first second hadjacent
      hfirstOrder hsecondOrder hseams
  · right
    exact ⟨first, second, hadjacent, hfirstOrder, hsecondOrder, hseams⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
