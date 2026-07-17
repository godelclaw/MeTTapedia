import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelLocalState

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelLocalDartsGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The selected cross edge is the unordered pair of the first route's
entry and exit endpoints. -/
theorem EvenKempePortPath.crossSite_eq_firstEntry_exit
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (site.1.1 : Sym2 V) =
      s(first.firstCrossEntryVertex second hab hbc site,
        (first.firstCrossExitDart second hab hbc site).fst) := by
  apply (Sym2.mem_and_mem_iff
    (first.firstCrossEntryVertex_ne_firstCrossExitDart_fst
      second hab hbc site)).1
  exact ⟨first.firstCrossEntryVertex_mem_site second hab hbc site,
    first.firstCrossExitDart_fst_mem_site second hab hbc site⟩

/-- The same edge in the second route's orientation. -/
theorem EvenKempePortPath.crossSite_eq_secondEntry_exit
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (site.1.1 : Sym2 V) =
      s(first.secondCrossEntryVertex second hac hbc site,
        (first.secondCrossExitDart second hac hbc site).fst) := by
  apply (Sym2.mem_and_mem_iff
    (first.secondCrossEntryVertex_ne_secondCrossExitDart_fst
      second hac hbc site)).1
  exact ⟨first.secondCrossEntryVertex_mem_site second hac hbc site,
    first.secondCrossExitDart_fst_mem_site second hac hbc site⟩

/-- The shared edge oriented in the first route's direction. -/
def EvenKempePortPath.firstCrossDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  ⟨(first.firstCrossEntryVertex second hab hbc site,
      (first.firstCrossExitDart second hab hbc site).fst), by
    rw [← SimpleGraph.mem_edgeSet,
      ← first.crossSite_eq_firstEntry_exit second hab hbc site]
    exact site.1.2⟩

/-- The same edge oriented in the second route's direction. -/
def EvenKempePortPath.secondCrossDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  ⟨(first.secondCrossEntryVertex second hac hbc site,
      (first.secondCrossExitDart second hac hbc site).fst), by
    rw [← SimpleGraph.mem_edgeSet,
      ← first.crossSite_eq_secondEntry_exit second hac hbc site]
    exact site.1.2⟩

@[simp] theorem EvenKempePortPath.firstCrossDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossDart second hab hbc site).fst =
      first.firstCrossEntryVertex second hab hbc site :=
  rfl

@[simp] theorem EvenKempePortPath.firstCrossDart_snd
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossDart second hab hbc site).snd =
      (first.firstCrossExitDart second hab hbc site).fst :=
  rfl

@[simp] theorem EvenKempePortPath.secondCrossDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossDart second hac hbc site).fst =
      first.secondCrossEntryVertex second hac hbc site :=
  rfl

@[simp] theorem EvenKempePortPath.secondCrossDart_snd
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossDart second hac hbc site).snd =
      (first.secondCrossExitDart second hac hbc site).fst :=
  rfl

@[simp] theorem EvenKempePortPath.firstCrossDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossDart second hab hbc site).edge = site.1.1 :=
  (first.crossSite_eq_firstEntry_exit second hab hbc site).symm

@[simp] theorem EvenKempePortPath.secondCrossDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossDart second hac hbc site).edge = site.1.1 :=
  (first.crossSite_eq_secondEntry_exit second hac hbc site).symm

/-- In the reversed pairing state the two route-oriented cross darts are
literal reversals. -/
theorem EvenKempePortPath.secondCrossDart_eq_firstCrossDart_symm_of_pairing_false
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hpairing : first.crossPairingBit second hab hac hbc site = false) :
    first.secondCrossDart second hac hbc site =
      (first.firstCrossDart second hab hbc site).symm := by
  have hedge :
      (first.secondCrossDart second hac hbc site).edge =
        (first.firstCrossDart second hab hbc site).edge := by
    simp
  rcases (SimpleGraph.dart_edge_eq_iff _ _).1 hedge with
    hsame | hreversed
  · have hexits := congrArg (fun dart : G.Dart ↦ dart.snd) hsame
    have hne := (first.crossPairingBit_eq_false_iff
      second hab hac hbc site).1 hpairing
    exact False.elim (hne hexits.symm)
  · exact hreversed

/-- The first outgoing edge after the common `a`-colored edge has the
first route's secondary color. -/
theorem EvenKempePortPath.firstCrossExitEdge_color
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    C ((first.firstSuffixFromCrossSite second site).getVert 1) = b := by
  have hadj :=
    (first.firstSuffixFromCrossSite second site).adj_getVert_succ
      (i := 0)
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
  have hne := C.valid hadj
  have hsite : C site.1 = a :=
    first.color_eq_first_of_crossSite second hbc site
  have hcolors := (first.mem_ambientPath_support_iff
    ((first.firstSuffixFromCrossSite second site).getVert 1)).1
      (first.firstSuffixFromCrossSite_support_subset second site
        ((first.firstSuffixFromCrossSite second site).getVert_mem_support 1))
  rcases hcolors.1 with hfirst | hsecond
  · exfalso
    apply hne
    simpa only [SimpleGraph.Walk.getVert_zero] using
      hsite.trans hfirst.symm
  · exact hsecond

/-- The second outgoing edge analogously has color `c`. -/
theorem EvenKempePortPath.secondCrossExitEdge_color
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    C ((first.secondSuffixFromCrossSite second site).getVert 1) = c := by
  have hadj :=
    (first.secondSuffixFromCrossSite second site).adj_getVert_succ
      (i := 0)
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
  have hne := C.valid hadj
  have hsite : C site.1 = a :=
    first.color_eq_first_of_crossSite second hbc site
  have hcolors := (second.mem_ambientPath_support_iff
    ((first.secondSuffixFromCrossSite second site).getVert 1)).1
      (first.secondSuffixFromCrossSite_support_subset second site
        ((first.secondSuffixFromCrossSite second site).getVert_mem_support 1))
  rcases hcolors.1 with hfirst | hsecond
  · exfalso
    apply hne
    simpa only [SimpleGraph.Walk.getVert_zero] using
      hsite.trans hfirst.symm
  · exact hsecond

/-- The first outgoing edge is the first strict-tail support element. -/
theorem EvenKempePortPath.firstCrossExitEdge_mem_tail_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstSuffixFromCrossSite second site).getVert 1 ∈
      (first.firstSuffixFromCrossSite second site).support.tail := by
  apply SimpleGraph.Walk.getVert_mem_tail_support
  · rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact first.firstSuffixFromCrossSite_length_pos second hab hbc site
  · omega

/-- The second outgoing edge is analogously the first element of its
strict-tail support. -/
theorem EvenKempePortPath.secondCrossExitEdge_mem_tail_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondSuffixFromCrossSite second site).getVert 1 ∈
      (first.secondSuffixFromCrossSite second site).support.tail := by
  apply SimpleGraph.Walk.getVert_mem_tail_support
  · rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact first.secondSuffixFromCrossSite_length_pos second hac hbc site
  · omega

/-- The two outgoing cross darts are distinct because their edges have
the distinct secondary colors. -/
theorem EvenKempePortPath.firstCrossExitDart_ne_secondCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossExitDart second hab hbc site ≠
      first.secondCrossExitDart second hac hbc site := by
  apply dart_ne_of_edge_colors_ne C
    (first.firstCrossExitDart_edge second hab hbc site)
    (first.secondCrossExitDart_edge second hac hbc site)
  rw [first.firstCrossExitEdge_color second hab hbc site,
    first.secondCrossExitEdge_color second hac hbc site]
  exact hbc

/-- The central cross dart is distinct from its first outgoing arm. -/
theorem EvenKempePortPath.firstCrossDart_ne_firstCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossDart second hab hbc site ≠
      first.firstCrossExitDart second hab hbc site := by
  apply dart_ne_of_edge_colors_ne C
    (first.firstCrossDart_edge second hab hbc site)
    (first.firstCrossExitDart_edge second hab hbc site)
  rw [first.color_eq_first_of_crossSite second hbc site,
    first.firstCrossExitEdge_color second hab hbc site]
  exact hab

/-- Its reverse is based at the exit endpoint and is also distinct from
the outgoing arm there. -/
theorem EvenKempePortPath.firstCrossDart_symm_ne_firstCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossDart second hab hbc site).symm ≠
      first.firstCrossExitDart second hab hbc site := by
  apply dart_ne_of_edge_colors_ne C
    (firstEdge := site.1)
    (secondEdge :=
      (first.firstSuffixFromCrossSite second site).getVert 1)
    (by
      rw [SimpleGraph.Dart.edge_symm]
      exact first.firstCrossDart_edge second hab hbc site)
    (first.firstCrossExitDart_edge second hab hbc site)
  rw [first.color_eq_first_of_crossSite second hbc site,
    first.firstCrossExitEdge_color second hab hbc site]
  exact hab

/-- The central dart is likewise distinct from the second outgoing arm. -/
theorem EvenKempePortPath.firstCrossDart_ne_secondCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossDart second hab hbc site ≠
      first.secondCrossExitDart second hac hbc site := by
  apply dart_ne_of_edge_colors_ne C
    (first.firstCrossDart_edge second hab hbc site)
    (first.secondCrossExitDart_edge second hac hbc site)
  rw [first.color_eq_first_of_crossSite second hbc site,
    first.secondCrossExitEdge_color second hac hbc site]
  exact hac

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
