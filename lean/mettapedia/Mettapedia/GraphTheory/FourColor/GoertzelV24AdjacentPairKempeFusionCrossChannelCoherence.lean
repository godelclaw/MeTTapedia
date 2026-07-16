import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenCoherentShortcut

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelCoherenceGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A cross site of routes with distinct second colors has their common
first color. -/
theorem EvenKempePortPath.color_eq_first_of_crossSite
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hbc : b ≠ c) (site : first.CrossSite second) :
    C site.1 = a := by
  rcases (first.mem_ambientPath_support_iff site.1).1 site.2.1 with
    ⟨hfirstColor, _⟩
  rcases (second.mem_ambientPath_support_iff site.1).1 site.2.2 with
    ⟨hsecondColor, _⟩
  exact C.color_eq_of_mem_two_bicoloredSets
    hbc hfirstColor hsecondColor

theorem EvenKempePortPath.firstPrefixToCrossSite_length_pos
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second) :
    0 < (first.firstPrefixToCrossSite second site).length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply SimpleGraph.Walk.not_nil_of_ne
  exact edge_ne_of_color_eq_of_color_eq_of_ne C first.leftColor
    (first.color_eq_first_of_crossSite second hbc site) hab.symm

theorem EvenKempePortPath.secondPrefixToCrossSite_length_pos
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second) :
    0 < (first.secondPrefixToCrossSite second site).length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply SimpleGraph.Walk.not_nil_of_ne
  exact edge_ne_of_color_eq_of_color_eq_of_ne C second.leftColor
    (first.color_eq_first_of_crossSite second hbc site) hac.symm

/-- Every first-route prefix is internally primal-coherent. -/
theorem EvenKempePortPath.firstPrefixToCrossSite_isPrimalCoherent
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := first.firstPrefixToCrossSite second site)
    (hpath := first.firstPrefixToCrossSite_isPath second site)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ first.ambientPath.support :=
        first.firstPrefixToCrossSite_support_subset second site hedge
      exact (first.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- The reversed second-route prefix is internally primal-coherent. -/
theorem EvenKempePortPath.secondPrefixToCrossSite_reverse_isPrimalCoherent
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := (first.secondPrefixToCrossSite second site).reverse)
    (hpath := (first.secondPrefixToCrossSite second site).isPath_reverse_iff.mpr
      (first.secondPrefixToCrossSite_isPath second site))
    (hcolors := by
      intro edge hedge
      have hprefix : edge ∈
          (first.secondPrefixToCrossSite second site).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
          hedge
      have hambient : edge ∈ second.ambientPath.support :=
        first.secondPrefixToCrossSite_support_subset second site hprefix
      exact (second.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- If the two prefix junctions use opposite endpoints of the cross edge,
the uncontracted cross splice is primal-coherent. -/
theorem EvenKempePortPath.crossSplice_isPrimalCoherent_of_seam_ne
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hseam :
      (first.firstPrefixToCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstPrefixToCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstPrefixToCrossSite_length_pos
                second hab hbc site) Nat.zero_lt_one⟩ ≠
        (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
          ⟨0, by
            simpa only [SimpleGraph.Walk.length_reverse] using
              (first.secondPrefixToCrossSite_length_pos
                second hac hbc site)⟩) :
    (first.crossSplice second site).IsPrimalCoherent := by
  rw [EvenKempePortPath.crossSplice]
  apply (first.firstPrefixToCrossSite_isPrimalCoherent second site).append
    (first.secondPrefixToCrossSite_reverse_isPrimalCoherent second site)
  intro hfirstPositive hsecondPositive
  simpa only [Subsingleton.elim hfirstPositive
      (first.firstPrefixToCrossSite_length_pos second hab hbc site),
    Subsingleton.elim hsecondPositive
      (by simpa only [SimpleGraph.Walk.length_reverse] using
        first.secondPrefixToCrossSite_length_pos second hac hbc site)] using
    hseam

/-- At a leftmost cross site, opposite endpoint attachments give the
ordinary splice and equal endpoint attachments give its one-edge triangle
contraction. In either case the two ports are joined by a nontrivial simple,
primal-coherent line-graph path. -/
theorem EvenKempePortPath.exists_primalCoherentCrossPath_of_leftmost
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (first.firstPrefixToCrossSite second site).support →
      edge ∈ second.ambientPath.support →
      edge = site.1) :
    ∃ joined : G.lineGraph.Walk first.leftEdge.1 second.leftEdge.1,
      joined.IsPath ∧ joined.IsPrimalCoherent ∧
        0 < joined.length ∧
        joined.length ≤ (first.crossSplice second site).length ∧
        joined.support ⊆
          first.ambientPath.support ++ second.ambientPath.support := by
  let firstPrefix := first.firstPrefixToCrossSite second site
  let secondReverse :=
    (first.secondPrefixToCrossSite second site).reverse
  have hfirstPath : firstPrefix.IsPath :=
    first.firstPrefixToCrossSite_isPath second site
  have hsecondPath : secondReverse.IsPath :=
    (first.secondPrefixToCrossSite_isPath second site).reverse
  have hfirstCoherent : firstPrefix.IsPrimalCoherent :=
    first.firstPrefixToCrossSite_isPrimalCoherent second site
  have hsecondCoherent : secondReverse.IsPrimalCoherent :=
    first.secondPrefixToCrossSite_reverse_isPrimalCoherent second site
  have hfirstPositive : 0 < firstPrefix.length :=
    first.firstPrefixToCrossSite_length_pos second hab hbc site
  have hsecondPositive : 0 < secondReverse.length := by
    simpa only [secondReverse, SimpleGraph.Walk.length_reverse] using
      first.secondPrefixToCrossSite_length_pos second hac hbc site
  have happendPath : (firstPrefix.append secondReverse).IsPath := by
    simpa only [firstPrefix, secondReverse,
      EvenKempePortPath.crossSplice] using
      first.crossSplice_isPath_of_leftmost second site hleftmost
  rcases
      SimpleGraph.Walk.exists_isPath_isPrimalCoherent_length_le_of_append_isPath
        firstPrefix secondReverse hfirstPath hsecondPath
        hfirstCoherent hsecondCoherent hfirstPositive hsecondPositive
        happendPath with
    ⟨joined, hjoinedPath, hjoinedCoherent, hjoinedPositive,
      hjoinedLength, hjoinedSupport⟩
  refine ⟨joined, hjoinedPath, hjoinedCoherent, hjoinedPositive, ?_, ?_⟩
  · simpa only [firstPrefix, secondReverse,
      EvenKempePortPath.crossSplice] using hjoinedLength
  · intro edge hedge
    have hsource := hjoinedSupport hedge
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hsource
    rw [List.mem_append]
    rcases hsource with hfirst | hsecond
    · exact Or.inl
        (first.firstPrefixToCrossSite_support_subset second site hfirst)
    · have hsecondReverse : edge ∈ secondReverse.support :=
        List.mem_of_mem_tail hsecond
      have hsecondPrefix : edge ∈
          (first.secondPrefixToCrossSite second site).support := by
        simpa only [secondReverse, SimpleGraph.Walk.support_reverse,
          List.mem_reverse] using hsecondReverse
      exact Or.inr
        (first.secondPrefixToCrossSite_support_subset second site
          hsecondPrefix)

/-- A nonempty first cross channel supplies a coherent opposite-port path. -/
theorem EvenKempeFusionLens.exists_bcPrimalCoherentCrossPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ joined : G.lineGraph.Walk
        lens01.bRoute.leftEdge.1 lens23.cRoute.leftEdge.1,
      joined.IsPath ∧ joined.IsPrimalCoherent ∧ 0 < joined.length ∧
        joined.support ⊆
          lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support := by
  rcases List.exists_mem_of_ne_nil _ hnonempty with ⟨edge, hedge⟩
  have hcross := (lens01.mem_bcCrossSites_iff lens23 edge).1 hedge
  rcases lens01.bRoute.exists_leftmostCrossSite lens23.cRoute
      ⟨edge, hcross⟩ with ⟨site, hleftmost⟩
  rcases lens01.bRoute.exists_primalCoherentCrossPath_of_leftmost
      lens23.cRoute hab hac hbc site hleftmost with
    ⟨joined, hpath, hcoherent, hpositive, _, hsupport⟩
  exact ⟨joined, hpath, hcoherent, hpositive, hsupport⟩

/-- A nonempty second cross channel supplies the complementary coherent
opposite-port path. -/
theorem EvenKempeFusionLens.exists_cbPrimalCoherentCrossPath
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ joined : G.lineGraph.Walk
        lens01.cRoute.leftEdge.1 lens23.bRoute.leftEdge.1,
      joined.IsPath ∧ joined.IsPrimalCoherent ∧ 0 < joined.length ∧
        joined.support ⊆
          lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support := by
  rcases List.exists_mem_of_ne_nil _ hnonempty with ⟨edge, hedge⟩
  have hcross := (lens01.mem_cbCrossSites_iff lens23 edge).1 hedge
  rcases lens01.cRoute.exists_leftmostCrossSite lens23.bRoute
      ⟨edge, hcross⟩ with ⟨site, hleftmost⟩
  rcases lens01.cRoute.exists_primalCoherentCrossPath_of_leftmost
      lens23.bRoute hac hab hbc.symm site hleftmost with
    ⟨joined, hpath, hcoherent, hpositive, _, hsupport⟩
  exact ⟨joined, hpath, hcoherent, hpositive, hsupport⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
