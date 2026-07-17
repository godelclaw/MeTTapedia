import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRejectedTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenPrimalLift

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelSuffixSpliceGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Follow the first route backward from its right port to a cross site,
then follow the second route forward to its right port. -/
def EvenKempePortPath.crossSuffixSplice
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk first.rightEdge.1 second.rightEdge.1 :=
  (first.firstSuffixFromCrossSite second site).reverse.append
    (first.secondSuffixFromCrossSite second site)

/-- Every edge of the suffix splice belongs to one of its two source
routes. -/
theorem EvenKempePortPath.crossSuffixSplice_support_subset_route_supports
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.crossSuffixSplice second site).support ⊆
      first.ambientPath.support ++ second.ambientPath.support := by
  intro edge hmem
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.support_append] at hmem
  apply List.mem_append.mpr
  rcases List.mem_append.mp hmem with hfirstReverse | hsecondTail
  · left
    apply first.firstSuffixFromCrossSite_support_subset second site
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hfirstReverse
  · right
    apply first.secondSuffixFromCrossSite_support_subset second site
    exact List.mem_of_mem_tail hsecondTail

/-- If the selected cross site is the only common route edge, the two
suffixes form a simple line-graph path between the right ports. -/
theorem EvenKempePortPath.crossSuffixSplice_isPath_of_unique
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second)
    (hunique : ∀ edge : G.edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1) :
    (first.crossSuffixSplice second site).IsPath := by
  let firstReverse :=
    (first.firstSuffixFromCrossSite second site).reverse
  let secondSuffix := first.secondSuffixFromCrossSite second site
  have hfirstPath : firstReverse.IsPath := by
    exact (first.firstSuffixFromCrossSite_isPath second site).reverse
  have hsecondPath : secondSuffix.IsPath := by
    exact first.secondSuffixFromCrossSite_isPath second site
  have hsiteNotMemSecondTail : site.1 ∉ secondSuffix.support.tail := by
    have hnodup := hsecondPath.support_nodup
    rw [← secondSuffix.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      firstReverse.support.Disjoint secondSuffix.support.tail := by
    rw [List.disjoint_left]
    intro edge hfirstReverse hsecondTail
    have hfirstSuffix : edge ∈
        (first.firstSuffixFromCrossSite second site).support := by
      simpa only [firstReverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hfirstReverse
    have hfirstSupport : edge ∈ first.ambientPath.support :=
      first.firstSuffixFromCrossSite_support_subset second site hfirstSuffix
    have hsecondSupport : edge ∈ second.ambientPath.support :=
      first.secondSuffixFromCrossSite_support_subset second site
        (List.mem_of_mem_tail hsecondTail)
    have hedge : edge = site.1 :=
      hunique edge hfirstSupport hsecondSupport
    exact hsiteNotMemSecondTail (hedge ▸ hsecondTail)
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hfirstPath.support_nodup, hsecondPath.support_nodup.tail,
    hdisjoint⟩

/-- The reversed first suffix remains internally primal-coherent. -/
theorem EvenKempePortPath.firstSuffixFromCrossSite_reverse_isPrimalCoherent
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstSuffixFromCrossSite second site).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := (first.firstSuffixFromCrossSite second site).reverse)
    (hpath := (first.firstSuffixFromCrossSite second site).isPath_reverse_iff.mpr
      (first.firstSuffixFromCrossSite_isPath second site))
    (hcolors := by
      intro edge hedge
      have hsuffix : edge ∈
          (first.firstSuffixFromCrossSite second site).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
          hedge
      have hambient : edge ∈ first.ambientPath.support :=
        first.firstSuffixFromCrossSite_support_subset second site hsuffix
      exact (first.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- Reversed endpoint pairing at the cross edge makes the entire suffix
splice primal-coherent. -/
theorem EvenKempePortPath.crossSuffixSplice_isPrimalCoherent_of_pairing_false
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hpairing : first.crossPairingBit second hab hac hbc site = false) :
    (first.crossSuffixSplice second site).IsPrimalCoherent := by
  let firstSuffix := first.firstSuffixFromCrossSite second site
  let secondSuffix := first.secondSuffixFromCrossSite second site
  have hfirstPositive : 0 < firstSuffix.length := by
    exact first.firstSuffixFromCrossSite_length_pos second hab hbc site
  have hsecondPositive : 0 < secondSuffix.length := by
    exact first.secondSuffixFromCrossSite_length_pos second hac hbc site
  have hpair :
      firstSuffix.lineGraphJunctionAt ⟨0, hfirstPositive⟩ ≠
        secondSuffix.lineGraphJunctionAt ⟨0, hsecondPositive⟩ := by
    have hne := (first.crossPairingBit_eq_false_iff
      second hab hac hbc site).1 hpairing
    simpa only [EvenKempePortPath.firstCrossExitDart_fst,
      EvenKempePortPath.secondCrossExitDart_fst, firstSuffix,
      secondSuffix] using hne
  rw [EvenKempePortPath.crossSuffixSplice]
  apply (first.firstSuffixFromCrossSite_reverse_isPrimalCoherent
      second site).append
    (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
  intro hfirstReversePositive hsecondPositive'
  have hreverseLast := firstSuffix.lineGraphJunctionAt_reverse_last
    hfirstPositive
  intro hsame
  apply hpair
  have hsame' :
      firstSuffix.reverse.lineGraphJunctionAt
          ⟨firstSuffix.reverse.length - 1,
            Nat.sub_lt hfirstReversePositive Nat.zero_lt_one⟩ =
        secondSuffix.lineGraphJunctionAt ⟨0, hsecondPositive⟩ := by
    simpa only [firstSuffix, secondSuffix,
      Subsingleton.elim hsecondPositive' hsecondPositive] using hsame
  exact hreverseLast.symm.trans hsame'

/-- Both strict suffixes occur in the suffix splice, so it is nontrivial. -/
theorem EvenKempePortPath.crossSuffixSplice_length_pos
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    0 < (first.crossSuffixSplice second site).length := by
  have hpositive :=
    first.firstSuffixFromCrossSite_length_pos second hab hbc site
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-- The selected cross edge itself belongs to the suffix splice. -/
theorem EvenKempePortPath.crossSite_mem_crossSuffixSplice_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    site.1 ∈ (first.crossSuffixSplice second site).support := by
  rw [EvenKempePortPath.crossSuffixSplice,
    SimpleGraph.Walk.support_append]
  apply List.mem_append.mpr
  left
  exact (first.firstSuffixFromCrossSite second site).reverse.end_mem_support

/-- For a unique cross edge, the prefix and suffix splices meet in exactly
that edge. -/
theorem EvenKempePortPath.mem_crossSplice_and_crossSuffixSplice_iff
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second)
    (hunique : ∀ edge : G.edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1)
    (edge : G.edgeSet) :
    edge ∈ (first.crossSplice second site).support ∧
        edge ∈ (first.crossSuffixSplice second site).support ↔
      edge = site.1 := by
  constructor
  · rintro ⟨hprefix, hsuffix⟩
    rw [EvenKempePortPath.crossSuffixSplice,
      SimpleGraph.Walk.support_append] at hsuffix
    rcases List.mem_append.mp hsuffix with hfirstReverse | hsecondTail
    · have hfirstSuffix : edge ∈
          (first.firstSuffixFromCrossSite second site).support := by
        simpa only [SimpleGraph.Walk.support_reverse,
          List.mem_reverse] using hfirstReverse
      have hcases : edge = site.1 ∨ edge ∈
          (first.firstSuffixFromCrossSite second site).support.tail := by
        have hcons := hfirstSuffix
        rw [← (first.firstSuffixFromCrossSite second site).cons_tail_support]
          at hcons
        simpa only [SimpleGraph.Walk.getVert_zero, List.mem_cons] using hcons
      rcases hcases with hedge | htail
      · exact hedge
      · exact False.elim ((List.disjoint_left.mp
          (first.firstSuffix_tail_disjoint_crossSplice_support
            second site hunique)) htail hprefix)
    · exact False.elim ((List.disjoint_left.mp
        (first.secondSuffix_tail_disjoint_crossSplice_support
          second site hunique)) hsecondTail hprefix)
  · intro hedge
    subst edge
    constructor
    · rw [EvenKempePortPath.crossSplice,
        SimpleGraph.Walk.support_append]
      apply List.mem_append.mpr
      left
      exact (first.firstPrefixToCrossSite second site).end_mem_support
    · exact first.crossSite_mem_crossSuffixSplice_support second site

/-- In the reversed-pairing state, a unique `bc` cross edge also gives an
exact primal trail between the two right ports. Its edges are precisely the
two suffixes joined through the selected cross edge. -/
theorem EvenKempeFusionLens.exists_bcExactCrossSuffixSpliceTrail_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hpairing : lens01.bRoute.crossPairingBit lens23.cRoute
      hab hac hbc site = false) :
    ∃ trail : G.Walk (data.defectVertex 1) (data.defectVertex 3),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ trail.edges := by
  let firstSuffix :=
    lens01.bRoute.firstSuffixFromCrossSite lens23.cRoute site
  let secondSuffix :=
    lens01.bRoute.secondSuffixFromCrossSite lens23.cRoute site
  let joined := lens01.bRoute.crossSuffixSplice lens23.cRoute site
  have hunique : ∀ edge : G.edgeSet,
      edge ∈ lens01.bRoute.ambientPath.support →
      edge ∈ lens23.cRoute.ambientPath.support → edge = site.1 := by
    intro edge hfirst hsecond
    exact lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site edge
      hfirst hsecond
  have hpath : joined.IsPath := by
    exact lens01.bRoute.crossSuffixSplice_isPath_of_unique
      lens23.cRoute site hunique
  have hcoherent : joined.IsPrimalCoherent := by
    exact lens01.bRoute.crossSuffixSplice_isPrimalCoherent_of_pairing_false
      lens23.cRoute hab hac hbc site hpairing
  have hpositive : 0 < joined.length := by
    exact lens01.bRoute.crossSuffixSplice_length_pos
      lens23.cRoute hab hbc site
  have hfirstPositive : 0 < firstSuffix.length := by
    exact lens01.bRoute.firstSuffixFromCrossSite_length_pos
      lens23.cRoute hab hbc site
  have hsecondPositive : 0 < secondSuffix.length := by
    exact lens01.bRoute.secondSuffixFromCrossSite_length_pos
      lens23.cRoute hac hbc site
  have hfirstReversePositive : 0 < firstSuffix.reverse.length := by
    simpa only [SimpleGraph.Walk.length_reverse] using hfirstPositive
  have hfirstEndCap :=
    lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site
  have hstartBase : data.defectVertex 1 ≠
      firstSuffix.reverse.lineGraphJunctionAt
        ⟨0, hfirstReversePositive⟩ := by
    intro heq
    apply hfirstEndCap
    have hreverseZero :=
      firstSuffix.lineGraphJunctionAt_reverse_zero hfirstPositive
    exact hreverseZero.symm.trans heq.symm
  have hstartNe : data.defectVertex 1 ≠
      joined.lineGraphJunctionAt ⟨0, hpositive⟩ := by
    intro heq
    apply hstartBase
    have happendZero :=
      firstSuffix.reverse.lineGraphJunctionAt_append_zero_of_left_pos
        secondSuffix hfirstReversePositive
    exact heq.trans (by
      simpa only [joined, EvenKempePortPath.crossSuffixSplice,
        firstSuffix, secondSuffix] using happendZero)
  have hsecondEndCap :=
    lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site
  have hendNe : joined.lineGraphJunctionAt
        ⟨joined.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      data.defectVertex 3 := by
    intro heq
    apply hsecondEndCap
    have happendLast :=
      firstSuffix.reverse.lineGraphJunctionAt_append_last_of_right_pos
        secondSuffix hsecondPositive
    exact (by
      simpa only [joined, EvenKempePortPath.crossSuffixSplice,
        firstSuffix, secondSuffix] using happendLast.symm.trans heq)
  have hstartMem : data.defectVertex 1 ∈
      (lens01.bRoute.rightEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens01.bRoute.rightIncident
  have hendMem : data.defectVertex 3 ∈
      (lens23.cRoute.rightEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens23.cRoute.rightIncident
  let trail := joined.cappedPrimalLift hpositive hcoherent
    (data.defectVertex 1) (data.defectVertex 3)
    hstartMem hendMem hstartNe hendNe
  have hedges : trail.edges = joined.support.map Subtype.val := by
    dsimp only [trail]
    exact joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 1) (data.defectVertex 3)
      hstartMem hendMem hstartNe hendNe
  have hsiteSupport : site.1 ∈ joined.support := by
    exact lens01.bRoute.crossSite_mem_crossSuffixSplice_support
      lens23.cRoute site
  refine ⟨trail, ?_, ?_, hedges, ?_⟩
  · dsimp only [trail]
    exact joined.cappedPrimalLift_isTrail_of_isPath
      hpositive hcoherent hpath
      (data.defectVertex 1) (data.defectVertex 3)
      hstartMem hendMem hstartNe hendNe
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_length]
    omega
  · rw [hedges]
    exact List.mem_map.mpr ⟨site.1, hsiteSupport, rfl⟩

/-- Secondary-color symmetry gives the exact right-port trail for a unique
`cb` cross edge. -/
theorem EvenKempeFusionLens.exists_cbExactCrossSuffixSpliceTrail_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hpairing : lens01.cRoute.crossPairingBit lens23.bRoute
      hac hab hbc.symm site = false) :
    ∃ trail : G.Walk (data.defectVertex 1) (data.defectVertex 3),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val ∧
        site.1.1 ∈ trail.edges := by
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors
      |>.exists_bcExactCrossSuffixSpliceTrail_of_pairing_false
        lens23.swapSecondaryColors hdata hac hab hbc.symm hcount site hpairing

/-- A unique reversed-pairing `bc` cross edge supplies complementary exact
trails through the left and right port pairs. Their only common primal edge
is the selected cross edge. -/
theorem EvenKempeFusionLens.exists_bcExactCrossTrailPair_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hpairing : lens01.bRoute.crossPairingBit lens23.cRoute
      hab hac hbc site = false) :
    ∃ (prefixTrail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
        (suffixTrail : G.Walk (data.defectVertex 1) (data.defectVertex 3)),
      prefixTrail.IsTrail ∧ suffixTrail.IsTrail ∧
        0 < prefixTrail.length ∧ 0 < suffixTrail.length ∧
        prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        (∀ edge : Sym2 V,
          edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
            edge = site.1.1) := by
  rcases lens01.exists_bcExactCrossSpliceTrail_of_pairing_false lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hcount site hpairing with
    ⟨prefixTrail, hprefixTrail, hprefixPositive, hprefixEdges,
      hprefixSite⟩
  rcases lens01.exists_bcExactCrossSuffixSpliceTrail_of_pairing_false lens23
      hdata hab hac hbc hcount site hpairing with
    ⟨suffixTrail, hsuffixTrail, hsuffixPositive, hsuffixEdges,
      hsuffixSite⟩
  refine ⟨prefixTrail, suffixTrail, hprefixTrail, hsuffixTrail,
    hprefixPositive, hsuffixPositive, hprefixEdges, hsuffixEdges, ?_⟩
  intro edge
  constructor
  · rintro ⟨hprefix, hsuffix⟩
    rw [hprefixEdges] at hprefix
    rw [hsuffixEdges] at hsuffix
    rcases List.mem_map.mp hprefix with
      ⟨prefixSource, hprefixSource, rfl⟩
    rcases List.mem_map.mp hsuffix with
      ⟨suffixSource, hsuffixSource, hsources⟩
    have hsourcesEq : suffixSource = prefixSource :=
      Subtype.ext hsources
    subst suffixSource
    have hsite :=
      (lens01.bRoute.mem_crossSplice_and_crossSuffixSplice_iff
        lens23.cRoute site
        (fun candidate hfirst hsecond ↦
          lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site
            candidate hfirst hsecond)
        prefixSource).1 ⟨hprefixSource, hsuffixSource⟩
    exact congrArg Subtype.val hsite
  · intro hedge
    subst edge
    exact ⟨hprefixSite, hsuffixSite⟩

/-- The complementary cross channel has the same exact two-trail
decomposition. -/
theorem EvenKempeFusionLens.exists_cbExactCrossTrailPair_of_pairing_false
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hpairing : lens01.cRoute.crossPairingBit lens23.bRoute
      hac hab hbc.symm site = false) :
    ∃ (prefixTrail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
        (suffixTrail : G.Walk (data.defectVertex 1) (data.defectVertex 3)),
      prefixTrail.IsTrail ∧ suffixTrail.IsTrail ∧
        0 < prefixTrail.length ∧ 0 < suffixTrail.length ∧
        prefixTrail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        suffixTrail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val ∧
        (∀ edge : Sym2 V,
          edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
            edge = site.1.1) := by
  simpa only [EvenKempeFusionLens.swapSecondaryColors_bRoute,
      EvenKempeFusionLens.swapSecondaryColors_cRoute] using
    lens01.swapSecondaryColors
      |>.exists_bcExactCrossTrailPair_of_pairing_false
        lens23.swapSecondaryColors hdata hac hab hbc.symm hcDisjoint
          hbDisjoint hcount site hpairing

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A rejected unique `bc` cross state exposes the two exact complementary
retained trails, with the selected edge as their exact overlap. -/
theorem EvenKempeFusionLens.exists_bcExactCrossTrailPair_of_rejected
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      prefixTrail.IsTrail ∧ suffixTrail.IsTrail ∧
        0 < prefixTrail.length ∧ 0 < suffixTrail.length ∧
        prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        (∀ edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex),
          edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
            edge = site.1.1) := by
  have hpairing :=
    (EvenKempeFusionLens.bcRejectedCrossState_of_faceTransferBit_eq_false
      graphData data lens01 lens23 hab hac hbc site hfalse).1
  exact lens01.exists_bcExactCrossTrailPair_of_pairing_false lens23
    hdata hab hac hbc hbDisjoint hcDisjoint hcount site hpairing

/-- The rejected unique `cb` state has the symmetric exact two-trail
decomposition. -/
theorem EvenKempeFusionLens.exists_cbExactCrossTrailPair_of_rejected
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      prefixTrail.IsTrail ∧ suffixTrail.IsTrail ∧
        0 < prefixTrail.length ∧ 0 < suffixTrail.length ∧
        prefixTrail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        suffixTrail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val ∧
        (∀ edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex),
          edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
            edge = site.1.1) := by
  have hpairing :=
    (EvenKempeFusionLens.cbRejectedCrossState_of_faceTransferBit_eq_false
      graphData data lens01 lens23 hab hac hbc site hfalse).1
  exact lens01.exists_cbExactCrossTrailPair_of_pairing_false lens23
    hdata hab hac hbc hbDisjoint hcDisjoint hcount site hpairing

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
