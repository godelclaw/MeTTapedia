import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannels

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelSpliceGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A common ambient edge of two even Kempe port routes. -/
def EvenKempePortPath.CrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight) :=
  {edge : G.edgeSet //
    edge ∈ first.ambientPath.support ∧
      edge ∈ second.ambientPath.support}

/-- The first route stopped at a selected cross site. -/
def EvenKempePortPath.firstPrefixToCrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk first.leftEdge.1 site.1 :=
  first.ambientPath.takeUntil site.1 site.2.1

/-- The second route stopped at the same selected cross site. -/
def EvenKempePortPath.secondPrefixToCrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk second.leftEdge.1 site.1 :=
  second.ambientPath.takeUntil site.1 site.2.2

/-- The remainder of the first route beginning at a selected cross site. -/
def EvenKempePortPath.firstSuffixFromCrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk site.1 first.rightEdge.1 :=
  first.ambientPath.dropUntil site.1 site.2.1

/-- The remainder of the second route beginning at the same cross site. -/
def EvenKempePortPath.secondSuffixFromCrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk site.1 second.rightEdge.1 :=
  second.ambientPath.dropUntil site.1 site.2.2

/-- Follow the first prefix into a cross site and the second prefix backward
out to its boundary port. -/
def EvenKempePortPath.crossSplice
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    G.lineGraph.Walk first.leftEdge.1 second.leftEdge.1 :=
  (first.firstPrefixToCrossSite second site).append
    (first.secondPrefixToCrossSite second site).reverse

theorem EvenKempePortPath.firstPrefixToCrossSite_isPath
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).IsPath :=
  first.ambientPath_isPath.takeUntil site.2.1

theorem EvenKempePortPath.secondPrefixToCrossSite_isPath
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).IsPath :=
  second.ambientPath_isPath.takeUntil site.2.2

theorem EvenKempePortPath.firstPrefixToCrossSite_support_subset
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).support ⊆
      first.ambientPath.support :=
  first.ambientPath.support_takeUntil_subset_support site.2.1

theorem EvenKempePortPath.secondPrefixToCrossSite_support_subset
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).support ⊆
      second.ambientPath.support :=
  second.ambientPath.support_takeUntil_subset_support site.2.2

/-- Every edge in a cross prefix splice lies on one of its two source
routes. -/
theorem EvenKempePortPath.crossSplice_support_subset_route_supports
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.crossSplice second site).support ⊆
      first.ambientPath.support ++ second.ambientPath.support := by
  intro edge hmem
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.support_append] at hmem
  apply List.mem_append.mpr
  rcases List.mem_append.mp hmem with hfirst | hsecond
  · exact Or.inl
      (first.firstPrefixToCrossSite_support_subset second site hfirst)
  · right
    apply first.secondPrefixToCrossSite_support_subset second site
    have hreverse : edge ∈
        (first.secondPrefixToCrossSite second site).reverse.support :=
      List.mem_of_mem_tail hsecond
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hreverse

/-- Prefix and suffix reconstruct the complete first route. -/
theorem EvenKempePortPath.firstPrefix_append_firstSuffix
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).append
        (first.firstSuffixFromCrossSite second site) =
      first.ambientPath :=
  first.ambientPath.take_spec site.2.1

/-- Prefix and suffix likewise reconstruct the complete second route. -/
theorem EvenKempePortPath.secondPrefix_append_secondSuffix
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).append
        (first.secondSuffixFromCrossSite second site) =
      second.ambientPath :=
  second.ambientPath.take_spec site.2.2

/-- Simplicity of the first route separates the prefix from the strict
suffix after the selected site. -/
theorem EvenKempePortPath.firstPrefix_disjoint_firstSuffix_tail
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).support.Disjoint
      (first.firstSuffixFromCrossSite second site).support.tail := by
  have hnodup :
      ((first.firstPrefixToCrossSite second site).support ++
        (first.firstSuffixFromCrossSite second site).support.tail).Nodup := by
    rw [← SimpleGraph.Walk.support_append,
      first.firstPrefix_append_firstSuffix second site]
    exact first.ambientPath_isPath.support_nodup
  exact hnodup.disjoint

/-- The same strict prefix--suffix separation holds on the second route. -/
theorem EvenKempePortPath.secondPrefix_disjoint_secondSuffix_tail
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).support.Disjoint
      (first.secondSuffixFromCrossSite second site).support.tail := by
  have hnodup :
      ((first.secondPrefixToCrossSite second site).support ++
        (first.secondSuffixFromCrossSite second site).support.tail).Nodup := by
    rw [← SimpleGraph.Walk.support_append,
      first.secondPrefix_append_secondSuffix second site]
    exact second.ambientPath_isPath.support_nodup
  exact hnodup.disjoint

/-- If the selected site is the only common route edge, the strict first
suffix is disjoint from the entire prefix splice. -/
theorem EvenKempePortPath.firstSuffix_tail_disjoint_crossSplice_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second)
    (hunique : ∀ edge : G.edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1) :
    (first.firstSuffixFromCrossSite second site).support.tail.Disjoint
      (first.crossSplice second site).support := by
  rw [List.disjoint_left]
  intro edge hsuffix hsplice
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirstPrefix | hsecondReverseTail
  · exact (List.disjoint_left.mp
      (first.firstPrefix_disjoint_firstSuffix_tail second site))
        hfirstPrefix hsuffix
  · have hsecondPrefix : edge ∈
        (first.secondPrefixToCrossSite second site).support := by
      have hreverse : edge ∈
          (first.secondPrefixToCrossSite second site).reverse.support :=
        List.mem_of_mem_tail hsecondReverseTail
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        hreverse
    have hfirstSupport : edge ∈ first.ambientPath.support :=
      first.ambientPath.support_dropUntil_subset_support site.2.1
        (List.mem_of_mem_tail hsuffix)
    have hsecondSupport : edge ∈ second.ambientPath.support :=
      first.secondPrefixToCrossSite_support_subset second site hsecondPrefix
    have heq : edge = site.1 := hunique edge hfirstSupport hsecondSupport
    have hsitePrefix : site.1 ∈
        (first.firstPrefixToCrossSite second site).support :=
      (first.firstPrefixToCrossSite second site).end_mem_support
    exact (List.disjoint_left.mp
      (first.firstPrefix_disjoint_firstSuffix_tail second site))
        hsitePrefix (heq ▸ hsuffix)

/-- Under the same unique-intersection hypothesis, the strict second suffix
also avoids the complete prefix splice. -/
theorem EvenKempePortPath.secondSuffix_tail_disjoint_crossSplice_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second)
    (hunique : ∀ edge : G.edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1) :
    (first.secondSuffixFromCrossSite second site).support.tail.Disjoint
      (first.crossSplice second site).support := by
  rw [List.disjoint_left]
  intro edge hsuffix hsplice
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.support_append] at hsplice
  rcases List.mem_append.mp hsplice with hfirstPrefix | hsecondReverseTail
  · have hfirstSupport : edge ∈ first.ambientPath.support :=
      first.firstPrefixToCrossSite_support_subset second site hfirstPrefix
    have hsecondSupport : edge ∈ second.ambientPath.support :=
      second.ambientPath.support_dropUntil_subset_support site.2.2
        (List.mem_of_mem_tail hsuffix)
    have heq : edge = site.1 := hunique edge hfirstSupport hsecondSupport
    have hsitePrefix : site.1 ∈
        (first.secondPrefixToCrossSite second site).support :=
      (first.secondPrefixToCrossSite second site).end_mem_support
    exact (List.disjoint_left.mp
      (first.secondPrefix_disjoint_secondSuffix_tail second site))
        hsitePrefix (heq ▸ hsuffix)
  · have hsecondPrefix : edge ∈
        (first.secondPrefixToCrossSite second site).support := by
      have hreverse : edge ∈
          (first.secondPrefixToCrossSite second site).reverse.support :=
        List.mem_of_mem_tail hsecondReverseTail
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        hreverse
    exact (List.disjoint_left.mp
      (first.secondPrefix_disjoint_secondSuffix_tail second site))
        hsecondPrefix hsuffix

/-- When the first cross-channel list has length at most one, a selected
cross site is its unique common route edge. -/
theorem EvenKempeFusionLens.bcCrossSite_eq_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (edge : G.edgeSet)
    (hfirst : edge ∈ lens01.bRoute.ambientPath.support)
    (hsecond : edge ∈ lens23.cRoute.ambientPath.support) :
    edge = site.1 := by
  have hedge : edge ∈ lens01.bcCrossSites lens23 :=
    (lens01.mem_bcCrossSites_iff lens23 edge).2 ⟨hfirst, hsecond⟩
  have hsite : site.1 ∈ lens01.bcCrossSites lens23 :=
    (lens01.mem_bcCrossSites_iff lens23 site.1).2 site.2
  cases hlist : lens01.bcCrossSites lens23 with
  | nil =>
      rw [hlist] at hsite
      simp at hsite
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            rw [hlist] at hcount
            simp only [List.length_cons] at hcount
            omega
      subst tail
      rw [hlist] at hedge hsite
      simp only [List.mem_singleton] at hedge hsite
      exact hedge.trans hsite.symm

/-- The analogous uniqueness law for the complementary cross channel. -/
theorem EvenKempeFusionLens.cbCrossSite_eq_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (edge : G.edgeSet)
    (hfirst : edge ∈ lens01.cRoute.ambientPath.support)
    (hsecond : edge ∈ lens23.bRoute.ambientPath.support) :
    edge = site.1 := by
  have hedge : edge ∈ lens01.cbCrossSites lens23 :=
    (lens01.mem_cbCrossSites_iff lens23 edge).2 ⟨hfirst, hsecond⟩
  have hsite : site.1 ∈ lens01.cbCrossSites lens23 :=
    (lens01.mem_cbCrossSites_iff lens23 site.1).2 site.2
  cases hlist : lens01.cbCrossSites lens23 with
  | nil =>
      rw [hlist] at hsite
      simp at hsite
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            rw [hlist] at hcount
            simp only [List.length_cons] at hcount
            omega
      subst tail
      rw [hlist] at hedge hsite
      simp only [List.mem_singleton] at hedge hsite
      exact hedge.trans hsite.symm

/-- A nonempty route intersection has a site encountered first along the
first route. Its first prefix contains no other edge of the second route. -/
theorem EvenKempePortPath.exists_leftmostCrossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hcross : ∃ edge : G.edgeSet,
      edge ∈ first.ambientPath.support ∧
        edge ∈ second.ambientPath.support) :
    ∃ site : first.CrossSite second,
      ∀ edge : G.edgeSet,
        edge ∈ (first.firstPrefixToCrossSite second site).support →
        edge ∈ second.ambientPath.support →
        edge = site.1 := by
  let sites : List G.edgeSet :=
    first.ambientPath.support.filter fun edge ↦
      edge ∈ second.ambientPath.support
  rcases hcross with ⟨edge, hfirst, hsecond⟩
  have hedgeSites : edge ∈ sites := by
    simp only [sites, List.mem_filter, decide_eq_true_eq]
    exact ⟨hfirst, hsecond⟩
  rcases first.ambientPath.exists_mem_support_forall_mem_support_imp_eq
      sites.toFinset (by
        refine ⟨edge, ?_⟩
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨hedgeSites, hfirst⟩) with
    ⟨siteEdge, hsiteFinset, hsiteSupport, hleftmost⟩
  have hsiteList : siteEdge ∈ sites := by
    simpa only [List.mem_toFinset] using hsiteFinset
  have hsiteBoth :
      siteEdge ∈ first.ambientPath.support ∧
        siteEdge ∈ second.ambientPath.support := by
    simpa only [sites, List.mem_filter, decide_eq_true_eq] using hsiteList
  let site : first.CrossSite second := ⟨siteEdge, hsiteBoth⟩
  refine ⟨site, ?_⟩
  intro candidate hprefix hsecondSupport
  have hfirstSupport : candidate ∈ first.ambientPath.support :=
    first.firstPrefixToCrossSite_support_subset second site hprefix
  have hcandidateSites : candidate ∈ sites := by
    simp only [sites, List.mem_filter, decide_eq_true_eq]
    exact ⟨hfirstSupport, hsecondSupport⟩
  have hcandidateFinset : candidate ∈ sites.toFinset := by
    simpa only [List.mem_toFinset]
  have hprefix' : candidate ∈
      (first.ambientPath.takeUntil siteEdge hsiteSupport).support := by
    simpa only [site, EvenKempePortPath.firstPrefixToCrossSite] using
      hprefix
  simpa only [site] using
    hleftmost candidate hcandidateFinset hprefix'

/-- Prefixes meeting at a leftmost cross site form a simple open path between
the two boundary-terminal edges. -/
theorem EvenKempePortPath.crossSplice_isPath_of_leftmost
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (first.firstPrefixToCrossSite second site).support →
      edge ∈ second.ambientPath.support →
      edge = site.1) :
    (first.crossSplice second site).IsPath := by
  let firstPrefix := first.firstPrefixToCrossSite second site
  let secondReverse :=
    (first.secondPrefixToCrossSite second site).reverse
  have hfirstPath : firstPrefix.IsPath := by
    exact first.firstPrefixToCrossSite_isPath second site
  have hsecondPath : secondReverse.IsPath := by
    exact (first.secondPrefixToCrossSite_isPath second site).reverse
  have hsiteNotMemSecondTail : site.1 ∉ secondReverse.support.tail := by
    have hnodup := hsecondPath.support_nodup
    rw [← secondReverse.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      firstPrefix.support.Disjoint secondReverse.support.tail := by
    rw [List.disjoint_left]
    intro edge hfirstPrefix hsecondTail
    have hsecondReverseSupport : edge ∈ secondReverse.support :=
      List.mem_of_mem_tail hsecondTail
    have hsecondPrefix :
        edge ∈ (first.secondPrefixToCrossSite second site).support := by
      simpa only [secondReverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hsecondReverseSupport
    have hsecondSupport : edge ∈ second.ambientPath.support :=
      first.secondPrefixToCrossSite_support_subset second site hsecondPrefix
    have hedge : edge = site.1 := hleftmost edge hfirstPrefix hsecondSupport
    exact hsiteNotMemSecondTail (hedge ▸ hsecondTail)
  rw [EvenKempePortPath.crossSplice,
    SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hfirstPath.support_nodup, hsecondPath.support_nodup.tail,
    hdisjoint⟩

/-- Distinct second colors make every cross splice nontrivial. -/
theorem EvenKempePortPath.crossSplice_length_pos
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hbc : b ≠ c) (site : first.CrossSite second) :
    0 < (first.crossSplice second site).length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply SimpleGraph.Walk.not_nil_of_ne
  exact edge_ne_of_color_eq_of_color_eq_of_ne C
    first.leftColor second.leftColor hbc

/-- A nonempty `b(0,1)`--`c(2,3)` channel yields a nontrivial simple
line-graph path from port 0 to port 2. -/
theorem EvenKempeFusionLens.exists_bcCrossSplice_isPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c) (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ site : lens01.bRoute.CrossSite lens23.cRoute,
      (lens01.bRoute.crossSplice lens23.cRoute site).IsPath ∧
      0 < (lens01.bRoute.crossSplice lens23.cRoute site).length := by
  rcases List.exists_mem_of_ne_nil _ hnonempty with ⟨edge, hedge⟩
  have hcross := (lens01.mem_bcCrossSites_iff lens23 edge).1 hedge
  rcases lens01.bRoute.exists_leftmostCrossSite lens23.cRoute
      ⟨edge, hcross⟩ with ⟨site, hleftmost⟩
  exact ⟨site,
    lens01.bRoute.crossSplice_isPath_of_leftmost
      lens23.cRoute site hleftmost,
    lens01.bRoute.crossSplice_length_pos lens23.cRoute hbc site⟩

/-- A nonempty `c(0,1)`--`b(2,3)` channel yields the complementary simple
line-graph path from port 0 to port 2. -/
theorem EvenKempeFusionLens.exists_cbCrossSplice_isPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c) (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
      (lens01.cRoute.crossSplice lens23.bRoute site).IsPath ∧
      0 < (lens01.cRoute.crossSplice lens23.bRoute site).length := by
  rcases List.exists_mem_of_ne_nil _ hnonempty with ⟨edge, hedge⟩
  have hcross := (lens01.mem_cbCrossSites_iff lens23 edge).1 hedge
  rcases lens01.cRoute.exists_leftmostCrossSite lens23.bRoute
      ⟨edge, hcross⟩ with ⟨site, hleftmost⟩
  exact ⟨site,
    lens01.cRoute.crossSplice_isPath_of_leftmost
      lens23.bRoute site hleftmost,
    lens01.cRoute.crossSplice_length_pos lens23.bRoute hbc.symm site⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
