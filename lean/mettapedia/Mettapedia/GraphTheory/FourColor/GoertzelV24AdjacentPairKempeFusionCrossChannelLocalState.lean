import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTailSegments

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace SimpleGraph.Walk

universe u

variable {W : Type u} {H : SimpleGraph W}

/-- Primal coherence of an appended positive line-graph walk forces its
two pieces to use opposite endpoints of their common primal edge. -/
theorem IsPrimalCoherent.ne_seam_of_append
    {first middle last : H.edgeSet}
    {left : H.lineGraph.Walk first middle}
    {right : H.lineGraph.Walk middle last}
    (hcoherent : (left.append right).IsPrimalCoherent)
    (hleftPositive : 0 < left.length)
    (hrightPositive : 0 < right.length) :
    left.lineGraphJunctionAt
        ⟨left.length - 1,
          Nat.sub_lt hleftPositive Nat.zero_lt_one⟩ ≠
      right.lineGraphJunctionAt ⟨0, hrightPositive⟩ := by
  let leftLast : Fin left.length :=
    ⟨left.length - 1,
      Nat.sub_lt hleftPositive Nat.zero_lt_one⟩
  let rightFirst : Fin right.length := ⟨0, hrightPositive⟩
  have hposition : left.length - 1 + 1 <
      (left.append right).length := by
    simp only [SimpleGraph.Walk.length_append]
    omega
  have hne := hcoherent (left.length - 1) hposition
  have hfirst :
      (left.append right).lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        left.lineGraphJunctionAt leftLast := by
    simpa only [leftLast] using
      left.lineGraphJunctionAt_append_left right leftLast
  have hsecond :
      (left.append right).lineGraphJunctionAt
          ⟨(left.length - 1) + 1, hposition⟩ =
        right.lineGraphJunctionAt rightFirst := by
    have hmapped :=
      left.lineGraphJunctionAt_append_right right rightFirst
    have hindex :
        (⟨(left.length - 1) + 1, hposition⟩ :
            Fin (left.append right).length) =
          ⟨left.length + rightFirst.val, by simp⟩ := by
      apply Fin.ext
      dsimp only [rightFirst]
      omega
    rw [hindex]
    exact hmapped
  intro hsame
  exact hne (hfirst.trans (hsame.trans hsecond.symm))

end SimpleGraph.Walk

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelLocalStateGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every simple bicolored port route is internally primal-coherent. -/
theorem EvenKempePortPath.ambientPath_isPrimalCoherent
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.ambientPath.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := route.ambientPath)
    (hpath := route.ambientPath_isPath)
    (hcolors := by
      intro edge hedge
      exact (route.mem_ambientPath_support_iff edge).1 hedge |>.1)
    (position := position) hposition

/-- The endpoint of the cross edge at which the first route enters from
its prefix. -/
def EvenKempePortPath.firstCrossEntryVertex
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) : V :=
  (first.firstPrefixToCrossSite second site).lineGraphJunctionAt
    ⟨(first.firstPrefixToCrossSite second site).length - 1,
      Nat.sub_lt
        (first.firstPrefixToCrossSite_length_pos second hab hbc site)
        Nat.zero_lt_one⟩

/-- The corresponding prefix-entry endpoint for the second route. -/
def EvenKempePortPath.secondCrossEntryVertex
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : V :=
  (first.secondPrefixToCrossSite second site).lineGraphJunctionAt
    ⟨(first.secondPrefixToCrossSite second site).length - 1,
      Nat.sub_lt
        (first.secondPrefixToCrossSite_length_pos second hac hbc site)
        Nat.zero_lt_one⟩

/-- The first prefix enters through an endpoint of the selected cross
edge. -/
theorem EvenKempePortPath.firstCrossEntryVertex_mem_site
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossEntryVertex second hab hbc site ∈
      (site.1.1 : Sym2 V) := by
  let initial := first.firstPrefixToCrossSite second site
  let finalPosition : Fin initial.length :=
    ⟨initial.length - 1,
      Nat.sub_lt
        (first.firstPrefixToCrossSite_length_pos second hab hbc site)
        Nat.zero_lt_one⟩
  have hmem := initial.lineGraphJunctionAt_mem_right finalPosition
  have hlast : initial.length - 1 + 1 = initial.length := by
    have hpositive : 0 < initial.length := by
      simpa only [initial] using
        first.firstPrefixToCrossSite_length_pos second hab hbc site
    omega
  simpa only [EvenKempePortPath.firstCrossEntryVertex, initial,
    finalPosition, hlast, SimpleGraph.Walk.getVert_length] using hmem

/-- The second prefix enters through an endpoint of the same edge. -/
theorem EvenKempePortPath.secondCrossEntryVertex_mem_site
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.secondCrossEntryVertex second hac hbc site ∈
      (site.1.1 : Sym2 V) := by
  let initial := first.secondPrefixToCrossSite second site
  let finalPosition : Fin initial.length :=
    ⟨initial.length - 1,
      Nat.sub_lt
        (first.secondPrefixToCrossSite_length_pos second hac hbc site)
        Nat.zero_lt_one⟩
  have hmem := initial.lineGraphJunctionAt_mem_right finalPosition
  have hlast : initial.length - 1 + 1 = initial.length := by
    have hpositive : 0 < initial.length := by
      simpa only [initial] using
        first.secondPrefixToCrossSite_length_pos second hac hbc site
    omega
  simpa only [EvenKempePortPath.secondCrossEntryVertex, initial,
    finalPosition, hlast, SimpleGraph.Walk.getVert_length] using hmem

/-- The first suffix leaves through an endpoint of the selected cross
edge. -/
theorem EvenKempePortPath.firstCrossExitDart_fst_mem_site
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossExitDart second hab hbc site).fst ∈
      (site.1.1 : Sym2 V) := by
  have hmem :=
    (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt_mem_left
      ⟨0, first.firstSuffixFromCrossSite_length_pos
        second hab hbc site⟩
  simpa only [EvenKempePortPath.firstCrossExitDart_fst,
    SimpleGraph.Walk.getVert_zero] using hmem

/-- The second suffix leaves through an endpoint of the same edge. -/
theorem EvenKempePortPath.secondCrossExitDart_fst_mem_site
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossExitDart second hac hbc site).fst ∈
      (site.1.1 : Sym2 V) := by
  have hmem :=
    (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt_mem_left
      ⟨0, first.secondSuffixFromCrossSite_length_pos
        second hac hbc site⟩
  simpa only [EvenKempePortPath.secondCrossExitDart_fst,
    SimpleGraph.Walk.getVert_zero] using hmem

/-- The first route enters and leaves the shared edge at opposite
endpoints. -/
theorem EvenKempePortPath.firstCrossEntryVertex_ne_firstCrossExitDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossEntryVertex second hab hbc site ≠
      (first.firstCrossExitDart second hab hbc site).fst := by
  let initial := first.firstPrefixToCrossSite second site
  let suffix := first.firstSuffixFromCrossSite second site
  have hinitialPositive : 0 < initial.length := by
    simpa only [initial] using
      first.firstPrefixToCrossSite_length_pos second hab hbc site
  have hsuffixPositive : 0 < suffix.length := by
    simpa only [suffix] using
      first.firstSuffixFromCrossSite_length_pos second hab hbc site
  have hcoherent : (initial.append suffix).IsPrimalCoherent := by
    rw [first.firstPrefix_append_firstSuffix second site]
    exact first.ambientPath_isPrimalCoherent
  have hseam :=
    SimpleGraph.Walk.IsPrimalCoherent.ne_seam_of_append
      hcoherent hinitialPositive hsuffixPositive
  simpa only [EvenKempePortPath.firstCrossEntryVertex,
    EvenKempePortPath.firstCrossExitDart_fst, initial, suffix] using hseam

/-- The same nondegenerate endpoint passage holds for the second route. -/
theorem EvenKempePortPath.secondCrossEntryVertex_ne_secondCrossExitDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.secondCrossEntryVertex second hac hbc site ≠
      (first.secondCrossExitDart second hac hbc site).fst := by
  let initial := first.secondPrefixToCrossSite second site
  let suffix := first.secondSuffixFromCrossSite second site
  have hinitialPositive : 0 < initial.length := by
    simpa only [initial] using
      first.secondPrefixToCrossSite_length_pos second hac hbc site
  have hsuffixPositive : 0 < suffix.length := by
    simpa only [suffix] using
      first.secondSuffixFromCrossSite_length_pos second hac hbc site
  have hcoherent : (initial.append suffix).IsPrimalCoherent := by
    rw [first.secondPrefix_append_secondSuffix second site]
    exact second.ambientPath_isPrimalCoherent
  have hseam :=
    SimpleGraph.Walk.IsPrimalCoherent.ne_seam_of_append
      hcoherent hinitialPositive hsuffixPositive
  simpa only [EvenKempePortPath.secondCrossEntryVertex,
    EvenKempePortPath.secondCrossExitDart_fst, initial, suffix] using hseam

/-- The two routes induce the same pairing of the two endpoints of their
common edge: their entries agree exactly when their exits agree. -/
theorem EvenKempePortPath.firstCrossEntryVertex_eq_second_iff_exit_fst_eq
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.firstCrossEntryVertex second hab hbc site =
        first.secondCrossEntryVertex second hac hbc site ↔
      (first.firstCrossExitDart second hab hbc site).fst =
        (first.secondCrossExitDart second hac hbc site).fst := by
  let firstEntry := first.firstCrossEntryVertex second hab hbc site
  let firstExit := (first.firstCrossExitDart second hab hbc site).fst
  let secondEntry := first.secondCrossEntryVertex second hac hbc site
  let secondExit := (first.secondCrossExitDart second hac hbc site).fst
  have hfirstNe : firstEntry ≠ firstExit := by
    simpa only [firstEntry, firstExit] using
      first.firstCrossEntryVertex_ne_firstCrossExitDart_fst
        second hab hbc site
  have hsecondNe : secondEntry ≠ secondExit := by
    simpa only [secondEntry, secondExit] using
      first.secondCrossEntryVertex_ne_secondCrossExitDart_fst
        second hac hbc site
  have hfirstEntryMem : firstEntry ∈ (site.1.1 : Sym2 V) := by
    simpa only [firstEntry] using
      first.firstCrossEntryVertex_mem_site second hab hbc site
  have hfirstExitMem : firstExit ∈ (site.1.1 : Sym2 V) := by
    simpa only [firstExit] using
      first.firstCrossExitDart_fst_mem_site second hab hbc site
  have hsecondEntryMem : secondEntry ∈ (site.1.1 : Sym2 V) := by
    simpa only [secondEntry] using
      first.secondCrossEntryVertex_mem_site second hac hbc site
  have hsecondExitMem : secondExit ∈ (site.1.1 : Sym2 V) := by
    simpa only [secondExit] using
      first.secondCrossExitDart_fst_mem_site second hac hbc site
  have hfirstPair : (site.1.1 : Sym2 V) =
      s(firstEntry, firstExit) :=
    (Sym2.mem_and_mem_iff hfirstNe).1
      ⟨hfirstEntryMem, hfirstExitMem⟩
  have hsecondPair : (site.1.1 : Sym2 V) =
      s(secondEntry, secondExit) :=
    (Sym2.mem_and_mem_iff hsecondNe).1
      ⟨hsecondEntryMem, hsecondExitMem⟩
  have hpairs : s(firstEntry, firstExit) =
      s(secondEntry, secondExit) :=
    hfirstPair.symm.trans hsecondPair
  change firstEntry = secondEntry ↔ firstExit = secondExit
  rcases Sym2.eq_iff.mp hpairs with hparallel | hreversed
  · exact ⟨fun _ => hparallel.2, fun _ => hparallel.1⟩
  · constructor
    · intro hentries
      exfalso
      apply hfirstNe
      exact hentries.trans hreversed.2.symm
    · intro hexits
      exfalso
      apply hfirstNe
      exact hreversed.1.trans hexits.symm

/-- Reversing the second prefix exposes its entry endpoint as the first
junction of the reversed walk. -/
theorem EvenKempePortPath.secondPrefix_reverse_firstJunction
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
        ⟨0, by
          simpa only [SimpleGraph.Walk.length_reverse] using
            first.secondPrefixToCrossSite_length_pos
              second hac hbc site⟩ =
      first.secondCrossEntryVertex second hac hbc site := by
  simpa only [EvenKempePortPath.secondCrossEntryVertex] using
    SimpleGraph.Walk.lineGraphJunctionAt_reverse_zero
      (first.secondPrefixToCrossSite second site)
      (first.secondPrefixToCrossSite_length_pos second hac hbc site)

/-- The uncontracted cross-splice seam is equal precisely in the
parallel endpoint-pairing state, equivalently when the two outgoing
cross darts have the same base vertex. -/
theorem EvenKempePortPath.crossSplice_seam_eq_iff_exit_fst_eq
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstPrefixToCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstPrefixToCrossSite_length_pos
                second hab hbc site) Nat.zero_lt_one⟩ =
        (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
          ⟨0, by
            simpa only [SimpleGraph.Walk.length_reverse] using
              first.secondPrefixToCrossSite_length_pos
                second hac hbc site⟩ ↔
      (first.firstCrossExitDart second hab hbc site).fst =
        (first.secondCrossExitDart second hac hbc site).fst := by
  change first.firstCrossEntryVertex second hab hbc site =
      (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
        ⟨0, by
          simpa only [SimpleGraph.Walk.length_reverse] using
            first.secondPrefixToCrossSite_length_pos
              second hac hbc site⟩ ↔ _
  rw [first.secondPrefix_reverse_firstJunction second hac hbc site]
  exact first.firstCrossEntryVertex_eq_second_iff_exit_fst_eq
    second hab hac hbc site

/-- Thus the coherent uncontracted splice branch is detected equally
well at the prefix seam or at the two outgoing cross darts. -/
theorem EvenKempePortPath.crossSplice_seam_ne_iff_exit_fst_ne
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstPrefixToCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstPrefixToCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstPrefixToCrossSite_length_pos
                second hab hbc site) Nat.zero_lt_one⟩ ≠
        (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
          ⟨0, by
            simpa only [SimpleGraph.Walk.length_reverse] using
              first.secondPrefixToCrossSite_length_pos
                second hac hbc site⟩ ↔
      (first.firstCrossExitDart second hab hbc site).fst ≠
        (first.secondCrossExitDart second hac hbc site).fst := by
  exact not_congr
    (first.crossSplice_seam_eq_iff_exit_fst_eq
      second hab hac hbc site)

/-- The finite endpoint-pairing state of a cross site. `true` means the
two routes traverse the shared edge in parallel; `false` means their
orientations are reversed. -/
def EvenKempePortPath.crossPairingBit
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : Bool :=
  decide ((first.firstCrossExitDart second hab hbc site).fst =
    (first.secondCrossExitDart second hac hbc site).fst)

@[simp] theorem EvenKempePortPath.crossPairingBit_eq_true_iff
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.crossPairingBit second hab hac hbc site = true ↔
      (first.firstCrossExitDart second hab hbc site).fst =
        (first.secondCrossExitDart second hac hbc site).fst := by
  simp [EvenKempePortPath.crossPairingBit]

@[simp] theorem EvenKempePortPath.crossPairingBit_eq_false_iff
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.crossPairingBit second hab hac hbc site = false ↔
      (first.firstCrossExitDart second hab hbc site).fst ≠
        (first.secondCrossExitDart second hac hbc site).fst := by
  rw [Bool.eq_false_iff]
  exact not_congr
    (first.crossPairingBit_eq_true_iff second hab hac hbc site)

/-- The Boolean state also detects the two branches of the existing
cross-splice construction. -/
theorem EvenKempePortPath.crossPairingBit_eq_false_iff_seam_ne
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    first.crossPairingBit second hab hac hbc site = false ↔
      (first.firstPrefixToCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstPrefixToCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstPrefixToCrossSite_length_pos
                second hab hbc site) Nat.zero_lt_one⟩ ≠
        (first.secondPrefixToCrossSite second site).reverse.lineGraphJunctionAt
          ⟨0, by
            simpa only [SimpleGraph.Walk.length_reverse] using
              first.secondPrefixToCrossSite_length_pos
                second hac hbc site⟩ := by
  rw [first.crossPairingBit_eq_false_iff second hab hac hbc site]
  exact (first.crossSplice_seam_ne_iff_exit_fst_ne
    second hab hac hbc site).symm

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
