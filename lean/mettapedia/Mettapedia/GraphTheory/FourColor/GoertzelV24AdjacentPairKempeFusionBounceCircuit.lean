import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionReturnCircuit

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Junction coordinates are unchanged when the final step of a line-graph
walk is removed. -/
theorem lineGraphJunctionAt_dropLast {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (position : Fin walk.dropLast.length) :
    walk.dropLast.lineGraphJunctionAt position =
      walk.lineGraphJunctionAt ⟨position, by
        have hposition : position.val < walk.length - 1 := by
          simpa only [SimpleGraph.Walk.length_dropLast] using position.isLt
        omega⟩ := by
  have hposition : position < walk.length - 1 := by
    simpa only [SimpleGraph.Walk.length_dropLast] using position.isLt
  have hpositionLe : position ≤ walk.length - 1 := by omega
  have hpositionSuccLe : position + 1 ≤ walk.length - 1 := by omega
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_left ⟨position, by omega⟩
    simpa only [SimpleGraph.Walk.dropLast,
      SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right hpositionLe] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_right ⟨position, by omega⟩
    simpa only [SimpleGraph.Walk.dropLast,
      SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right hpositionSuccLe] using hmem

/-- Removing the final step of an open coherent line-graph walk preserves
coherence at every remaining primal edge. -/
theorem IsPrimalCoherent.dropLast {first last : G.edgeSet}
    {walk : G.lineGraph.Walk first last}
    (hcoherent : walk.IsPrimalCoherent) :
    walk.dropLast.IsPrimalCoherent := by
  intro position hposition
  have hwalkPosition : position + 1 < walk.length := by
    rw [SimpleGraph.Walk.length_dropLast] at hposition
    omega
  have hfirst := walk.lineGraphJunctionAt_dropLast
    ⟨position, by omega⟩
  have hsecond := walk.lineGraphJunctionAt_dropLast
    ⟨position + 1, hposition⟩
  intro heq
  exact hcoherent position hwalkPosition
    (hfirst.symm.trans (heq.trans hsecond))

/-- Removing the first step shifts every remaining junction coordinate by
one. -/
theorem lineGraphJunctionAt_tail {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (position : Fin walk.tail.length) :
    walk.tail.lineGraphJunctionAt position =
      walk.lineGraphJunctionAt ⟨position + 1, by
        have htailPositive : 0 < walk.tail.length :=
          Nat.zero_lt_of_lt position.isLt
        have hwalkNotNil : ¬walk.Nil := by
          intro hnil
          have hzero := (SimpleGraph.Walk.Nil.tail hnil).length_eq_zero
          omega
        have hlength := SimpleGraph.Walk.length_tail_add_one hwalkNotNil
        omega⟩ := by
  have htailPositive : 0 < walk.tail.length :=
    Nat.zero_lt_of_lt position.isLt
  have hwalkNotNil : ¬walk.Nil := by
    intro hnil
    have hzero := (SimpleGraph.Walk.Nil.tail hnil).length_eq_zero
    omega
  have hlength := SimpleGraph.Walk.length_tail_add_one hwalkNotNil
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_left
        ⟨position + 1, by omega⟩
    simpa only [SimpleGraph.Walk.getVert_tail] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_right
        ⟨position + 1, by omega⟩
    simpa only [SimpleGraph.Walk.getVert_tail, Nat.add_assoc] using hmem

/-- Removing the first step of an open coherent line-graph walk preserves
coherence. -/
theorem IsPrimalCoherent.tail {first last : G.edgeSet}
    {walk : G.lineGraph.Walk first last}
    (hcoherent : walk.IsPrimalCoherent) :
    walk.tail.IsPrimalCoherent := by
  intro position hposition
  have htailPositive : 0 < walk.tail.length := by omega
  have hwalkNotNil : ¬walk.Nil := by
    intro hnil
    have hzero := (SimpleGraph.Walk.Nil.tail hnil).length_eq_zero
    omega
  have hlength := SimpleGraph.Walk.length_tail_add_one hwalkNotNil
  have hwalkPosition : position + 1 + 1 < walk.length := by omega
  have hfirst := walk.lineGraphJunctionAt_tail ⟨position, by omega⟩
  have hsecond := walk.lineGraphJunctionAt_tail
    ⟨position + 1, hposition⟩
  intro heq
  exact hcoherent (position + 1) hwalkPosition
    (hfirst.symm.trans (heq.trans hsecond))

/-- Prepending one line-graph step preserves open primal coherence when
the new first junction differs from the old first junction. -/
theorem IsPrimalCoherent.cons_of_firstJunction_ne
    {first second last : G.edgeSet}
    {walk : G.lineGraph.Walk second last}
    (hcoherent : walk.IsPrimalCoherent)
    (hadj : G.lineGraph.Adj first second)
    (hfirst : ∀ hpositive : 0 < walk.length,
      SimpleGraph.lineGraphCommonVertex hadj ≠
        walk.lineGraphJunctionAt ⟨0, hpositive⟩) :
    (SimpleGraph.Walk.cons hadj walk).IsPrimalCoherent := by
  intro position hposition
  by_cases hzero : position = 0
  · subst position
    have hpositive : 0 < walk.length := by
      simp only [SimpleGraph.Walk.length_cons] at hposition
      omega
    have hzeroJunction :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_zero hadj walk
    have honeJunction :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_succ hadj walk
        ⟨0, hpositive⟩
    intro heq
    apply hfirst hpositive
    exact hzeroJunction.symm.trans (heq.trans honeJunction)
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hzero
    have hwalkPosition : previous + 1 < walk.length := by
      simp only [SimpleGraph.Walk.length_cons] at hposition
      omega
    have hfirstJunction :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_succ hadj walk
        ⟨previous, by omega⟩
    have hsecondJunction :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_succ hadj walk
        ⟨previous + 1, hwalkPosition⟩
    intro heq
    exact hcoherent previous hwalkPosition
      (hfirstJunction.symm.trans (heq.trans hsecondJunction))

/-- Replacing the first vertex of a positive line-graph walk by another
neighbor with the same common primal junction leaves its final junction
unchanged. -/
theorem lineGraphJunctionAt_cons_tail_last
    {first second last : G.edgeSet}
    (walk : G.lineGraph.Walk second last)
    (hpositive : 0 < walk.length)
    (hadj : G.lineGraph.Adj first walk.snd)
    (hfirst : SimpleGraph.lineGraphCommonVertex hadj =
      walk.lineGraphJunctionAt ⟨0, hpositive⟩) :
    let altered := SimpleGraph.Walk.cons hadj walk.tail
    altered.lineGraphJunctionAt
        ⟨altered.length - 1,
          Nat.sub_lt (by
            change 0 < walk.tail.length + 1
            omega) Nat.zero_lt_one⟩ =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
  dsimp only
  have hnotNil : ¬walk.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hpositive
  have htailLength := SimpleGraph.Walk.length_tail_add_one hnotNil
  by_cases hone : walk.length = 1
  · have htailZero : walk.tail.length = 0 := by omega
    have halteredLength :
        (SimpleGraph.Walk.cons hadj walk.tail).length = 1 := by simp [htailZero]
    have hzero :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_zero hadj walk.tail
    have halteredPosition :
        (⟨(SimpleGraph.Walk.cons hadj walk.tail).length - 1,
            Nat.sub_lt (by simp) Nat.zero_lt_one⟩ :
          Fin (SimpleGraph.Walk.cons hadj walk.tail).length) =
        ⟨0, by simp [halteredLength]⟩ := by
      apply Fin.ext
      simp [halteredLength]
    have horiginalPosition :
        (⟨walk.length - 1,
            Nat.sub_lt hpositive Nat.zero_lt_one⟩ : Fin walk.length) =
        ⟨0, by simp [hone]⟩ := by
      apply Fin.ext
      simp [hone]
    rw [halteredPosition, horiginalPosition, hzero]
    exact hfirst
  · have htailPositive : 0 < walk.tail.length := by omega
    let tailLast : Fin walk.tail.length :=
      ⟨walk.tail.length - 1,
        Nat.sub_lt htailPositive Nat.zero_lt_one⟩
    have hcons :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_succ hadj walk.tail tailLast
    have htail := walk.lineGraphJunctionAt_tail tailLast
    have halteredPosition :
        (⟨(SimpleGraph.Walk.cons hadj walk.tail).length - 1,
            Nat.sub_lt (by simp) Nat.zero_lt_one⟩ :
          Fin (SimpleGraph.Walk.cons hadj walk.tail).length) =
        ⟨tailLast.val + 1, by simp⟩ := by
      apply Fin.ext
      dsimp only [tailLast]
      simp only [SimpleGraph.Walk.length_cons]
      omega
    have horiginalPosition :
        (⟨walk.length - 1,
            Nat.sub_lt hpositive Nat.zero_lt_one⟩ : Fin walk.length) =
        ⟨tailLast.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [tailLast]
      omega
    rw [halteredPosition, horiginalPosition]
    exact hcons.trans htail

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionBounceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Positive chirality makes the two predecessor edges meet at the same
endpoint of their shared fusion edge.  Their distinct route colors therefore
give a direct line-graph shortcut past that fusion edge. -/
theorem EvenKempeFusionLens.cPreviousEdge_adj_bPreviousEdge_of_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    G.lineGraph.Adj (lens.cPreviousVertex site).1
      (lens.bPreviousVertex site).1 := by
  have hagree :=
    (lens.fusionChirality_eq_true_iff_endpoints_agree
      hab hac site).1 hpositive
  apply lineGraph_adj_of_common_vertex_of_ne
    (vertex := lens.cEntryVertex hac site)
  · exact lens.cEntryVertex_mem_previousEdge hac site
  · rw [hagree.1]
    exact lens.bEntryVertex_mem_previousEdge hab site
  · exact edge_ne_of_color_eq_of_color_eq_of_ne C
      (lens.cPreviousColor hac site) (lens.bPreviousColor hab site) hbc.symm

/-- The shortcut adjacency packaged for reuse in the contracted walk. -/
def EvenKempeFusionLens.positiveFusionShortcutAdj
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    G.lineGraph.Adj (lens.cPreviousVertex site).1
      (lens.bPreviousVertex site).1 :=
  lens.cPreviousEdge_adj_bPreviousEdge_of_chirality_eq_true
    hab hac hbc site hpositive

/-- The common primal junction of the shortcut is the common entry endpoint
of the positively oriented fusion edge. -/
theorem EvenKempeFusionLens.lineGraphCommonVertex_positiveFusionShortcutAdj
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    SimpleGraph.lineGraphCommonVertex
        (lens.positiveFusionShortcutAdj hab hac hbc site hpositive) =
      lens.cEntryVertex hac site := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · exact lens.cEntryVertex_mem_previousEdge hac site
  · have hagree :=
      (lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hpositive
    rw [hagree.1]
    exact lens.bEntryVertex_mem_previousEdge hab site

/-- Contract the bounced shared edge in the positive-chirality return loop.
The `c` prefix stops one edge early, crosses directly to the `b` predecessor,
and then follows the tail of the reversed `b` prefix. -/
def EvenKempeFusionLens.positiveFusionBounceShortcut
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 lens.bRoute.leftEdge.1 :=
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  let shortcutAdj : G.lineGraph.Adj cPrefix.penultimate bReverse.snd := by
    simpa only [cPrefix, bReverse, SimpleGraph.Walk.snd_reverse,
      lens.cLeftConnectedPrefixToFusion_getVert_penultimate hab hac site,
      lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using
        lens.positiveFusionShortcutAdj hab hac hbc site hpositive
  cPrefix.dropLast.append
    (SimpleGraph.Walk.cons shortcutAdj bReverse.tail)

@[simp] theorem EvenKempeFusionLens.positiveFusionBounceShortcut_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    (lens.positiveFusionBounceShortcut hab hac hbc site hpositive).length + 1 =
      (lens.fusionSiteLeftReturnOppositeLoop site).length := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  have hcNotNil : ¬cPrefix.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact lens.cLeftConnectedPrefixToFusion_length_pos site
  have hbNotNil : ¬bReverse.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simpa only [bReverse, SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  rw [EvenKempeFusionLens.positiveFusionBounceShortcut,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_dropLast]
  have hcLength := SimpleGraph.Walk.length_dropLast_add_one hcNotNil
  have hbLength := SimpleGraph.Walk.length_tail_add_one hbNotNil
  rw [EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop,
    SimpleGraph.Walk.length_append]
  dsimp only [cPrefix, bReverse] at hcLength hbLength ⊢
  omega

/-- Contracting a positive fusion bounce removes the only incoherent shared
edge.  The resulting closed line-graph walk is primal-coherent. -/
theorem EvenKempeFusionLens.positiveFusionBounceShortcut_isPrimalCoherentClosed
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    (lens.positiveFusionBounceShortcut hab hac hbc site hpositive).IsPrimalCoherentClosed := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  let shortcutAdj : G.lineGraph.Adj cPrefix.penultimate bReverse.snd := by
    simpa only [cPrefix, bReverse, SimpleGraph.Walk.snd_reverse,
      lens.cLeftConnectedPrefixToFusion_getVert_penultimate hab hac site,
      lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using
        lens.positiveFusionShortcutAdj hab hac hbc site hpositive
  let bShortcut := SimpleGraph.Walk.cons shortcutAdj bReverse.tail
  have hcPositive : 0 < cPrefix.length := by
    dsimp only [cPrefix]
    exact lens.cLeftConnectedPrefixToFusion_length_pos site
  have hcTwo : 2 ≤ cPrefix.length := by
    dsimp only [cPrefix]
    rw [lens.cLeftConnectedPrefixToFusion_length site]
    have hcAmbient := lens.cAmbientPrefixToFusion_length_pos hab hac site
    omega
  have hcDropPositive : 0 < cPrefix.dropLast.length := by
    rw [SimpleGraph.Walk.length_dropLast]
    omega
  have hbPositive : 0 < bReverse.length := by
    dsimp only [bReverse]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  have hbNotNil : ¬bReverse.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hbPositive
  have hbTailLength := SimpleGraph.Walk.length_tail_add_one hbNotNil
  have hagree :=
    (lens.fusionChirality_eq_true_iff_endpoints_agree
      hab hac site).1 hpositive
  have hshortcutCommonC :
      SimpleGraph.lineGraphCommonVertex shortcutAdj =
        lens.cEntryVertex hac site := by
    symm
    apply SimpleGraph.lineGraphCommonVertex_unique
    · simpa only [cPrefix,
        lens.cLeftConnectedPrefixToFusion_getVert_penultimate hab hac site] using
          lens.cEntryVertex_mem_previousEdge hac site
    · rw [hagree.1]
      simpa only [bReverse, SimpleGraph.Walk.snd_reverse,
        lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using
          lens.bEntryVertex_mem_previousEdge hab site
  have hshortcutCommonB :
      SimpleGraph.lineGraphCommonVertex shortcutAdj =
        lens.bEntryVertex hab site :=
    hshortcutCommonC.trans hagree.1
  have hbFirstExplicit :
      bReverse.lineGraphJunctionAt ⟨0, hbPositive⟩ =
        lens.bEntryVertex hab site := by
    dsimp only [bReverse]
    exact lens.bAmbientPrefixToFusion_reverse_firstJunction hab hac site
  have hshortcutCommonBReverse :
      SimpleGraph.lineGraphCommonVertex shortcutAdj =
        bReverse.lineGraphJunctionAt ⟨0, hbPositive⟩ :=
    hshortcutCommonB.trans hbFirstExplicit.symm
  have hcCoherent : cPrefix.IsPrimalCoherent := by
    dsimp only [cPrefix]
    exact lens.cLeftConnectedPrefixToFusion_isPrimalCoherent
      hdata hab hac site
  have hbCoherent : bReverse.IsPrimalCoherent := by
    dsimp only [bReverse]
    exact lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site
  have hbShortcutCoherent : bShortcut.IsPrimalCoherent := by
    dsimp only [bShortcut]
    apply hbCoherent.tail.cons_of_firstJunction_ne shortcutAdj
    intro htailPositive
    have hbStep :
        bReverse.lineGraphJunctionAt ⟨0, hbPositive⟩ ≠
          bReverse.lineGraphJunctionAt ⟨1, by omega⟩ :=
      hbCoherent 0 (by omega)
    have htailJunction :=
      bReverse.lineGraphJunctionAt_tail ⟨0, htailPositive⟩
    intro heq
    apply hbStep
    exact hshortcutCommonBReverse.symm.trans
      (heq.trans htailJunction)
  have hseam :
      cPrefix.dropLast.lineGraphJunctionAt
          ⟨cPrefix.dropLast.length - 1,
            Nat.sub_lt hcDropPositive Nat.zero_lt_one⟩ ≠
        bShortcut.lineGraphJunctionAt
          ⟨0, by simp [bShortcut]⟩ := by
    let cBeforeLast : Fin cPrefix.length :=
      ⟨cPrefix.length - 2, by omega⟩
    let cLast : Fin cPrefix.length :=
      ⟨cPrefix.length - 1,
        Nat.sub_lt hcPositive Nat.zero_lt_one⟩
    let cDropLast : Fin cPrefix.dropLast.length :=
      ⟨cPrefix.dropLast.length - 1,
        Nat.sub_lt hcDropPositive Nat.zero_lt_one⟩
    have hcStep :
        cPrefix.lineGraphJunctionAt cBeforeLast ≠
          cPrefix.lineGraphJunctionAt cLast := by
      have hraw := hcCoherent (cPrefix.length - 2) (by omega)
      intro heq
      apply hraw
      let rawFirst : Fin cPrefix.length :=
        ⟨cPrefix.length - 2, by omega⟩
      let rawSecond : Fin cPrefix.length :=
        ⟨cPrefix.length - 2 + 1, by omega⟩
      have hfirstPosition : rawFirst = cBeforeLast := by
        apply Fin.ext
        rfl
      have hsecondPosition : rawSecond = cLast := by
        apply Fin.ext
        dsimp only [rawSecond, cLast]
        omega
      exact (congrArg cPrefix.lineGraphJunctionAt hfirstPosition).trans
        (heq.trans
          (congrArg cPrefix.lineGraphJunctionAt hsecondPosition.symm))
    have hdrop := cPrefix.lineGraphJunctionAt_dropLast cDropLast
    let cDropLifted : Fin cPrefix.length :=
      ⟨cDropLast.val, by
        have hposition : cDropLast.val < cPrefix.length - 1 := by
          simpa only [SimpleGraph.Walk.length_dropLast] using cDropLast.isLt
        omega⟩
    have hdropLifted :
        cPrefix.dropLast.lineGraphJunctionAt cDropLast =
          cPrefix.lineGraphJunctionAt cDropLifted := by
      simpa only [cDropLifted] using hdrop
    have hdropPosition : cDropLifted = cBeforeLast := by
      apply Fin.ext
      dsimp only [cDropLifted, cDropLast, cBeforeLast]
      rw [SimpleGraph.Walk.length_dropLast]
      omega
    have hdropExact :
        cPrefix.dropLast.lineGraphJunctionAt cDropLast =
          cPrefix.lineGraphJunctionAt cBeforeLast := by
      exact hdropLifted.trans
        (congrArg cPrefix.lineGraphJunctionAt hdropPosition)
    have hcLast : cPrefix.lineGraphJunctionAt cLast =
        lens.cEntryVertex hac site := by
      dsimp only [cPrefix, cLast]
      exact lens.cLeftConnectedPrefixToFusion_lastJunction hab hac site
    have hbFirst :=
      SimpleGraph.Walk.lineGraphJunctionAt_cons_zero shortcutAdj bReverse.tail
    change cPrefix.dropLast.lineGraphJunctionAt cDropLast ≠
      bShortcut.lineGraphJunctionAt ⟨0, by simp [bShortcut]⟩
    intro heq
    apply hcStep
    exact hdropExact.symm.trans
      (heq.trans (hbFirst.trans
        (hshortcutCommonC.trans hcLast.symm)))
  have hclosing :
      bShortcut.lineGraphJunctionAt
          ⟨bShortcut.length - 1,
            Nat.sub_lt (by simp [bShortcut]) Nat.zero_lt_one⟩ ≠
        cPrefix.dropLast.lineGraphJunctionAt
          ⟨0, hcDropPositive⟩ := by
    have hbLast := SimpleGraph.Walk.lineGraphJunctionAt_cons_tail_last
      bReverse hbPositive shortcutAdj hshortcutCommonBReverse
    have hcFirst := cPrefix.lineGraphJunctionAt_dropLast
      ⟨0, hcDropPositive⟩
    have hbLastExplicit :=
      lens.bAmbientPrefixToFusion_reverse_lastJunction hab hac site
    have hcFirstExplicit :=
      lens.cLeftConnectedPrefixToFusion_firstJunction site
    intro heq
    apply (lens.leftConnectorVertex_ne_bPrefixFirstJunction
      hdata hab hac site).symm
    exact hbLastExplicit.symm.trans
      (hbLast.symm.trans (heq.trans
        (hcFirst.trans hcFirstExplicit)))
  change (cPrefix.dropLast.append bShortcut).IsPrimalCoherentClosed
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    hcCoherent.dropLast hbShortcutCoherent hcDropPositive
    (by simp [bShortcut]) hseam hclosing

/-- The contracted positive-bounce walk is nonempty. -/
theorem EvenKempeFusionLens.positiveFusionBounceShortcut_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    0 < (lens.positiveFusionBounceShortcut
      hab hac hbc site hpositive).length := by
  rw [EvenKempeFusionLens.positiveFusionBounceShortcut,
    SimpleGraph.Walk.length_append]
  have hcTwo : 2 ≤
      (lens.cLeftConnectedPrefixToFusion site).length := by
    rw [lens.cLeftConnectedPrefixToFusion_length site]
    have hcAmbient := lens.cAmbientPrefixToFusion_length_pos hab hac site
    omega
  rw [SimpleGraph.Walk.length_dropLast]
  omega

/-- A positive fusion bounce therefore gives a strictly shorter primal
cycle after contracting the bounced shared edge. -/
theorem EvenKempeFusionLens.exists_shorter_primalCycle_of_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true) :
    ∃ (start : V) (cycle : G.Walk start start),
      cycle.IsCycle ∧ cycle.length < lens.closedWalk.length := by
  let shortcut :=
    lens.positiveFusionBounceShortcut hab hac hbc site hpositive
  have hshortcutPositive : 0 < shortcut.length := by
    dsimp only [shortcut]
    exact lens.positiveFusionBounceShortcut_length_pos
      hab hac hbc site hpositive
  have hshortcutCoherent : shortcut.IsPrimalCoherentClosed := by
    dsimp only [shortcut]
    exact lens.positiveFusionBounceShortcut_isPrimalCoherentClosed
      hdata hab hac hbc site hpositive
  rcases shortcut.exists_primal_isCycle_length_le_of_primalCoherentClosed
      hshortcutPositive hshortcutCoherent with
    ⟨start, cycle, hcycle, hcycleLength⟩
  refine ⟨start, cycle, hcycle, lt_of_le_of_lt hcycleLength ?_⟩
  have hcontracted := lens.positiveFusionBounceShortcut_length
    hab hac hbc site hpositive
  have hreturnShorter :=
    lens.fusionSiteLeftReturnOppositeLoop_length_lt_closedWalk
      hab hac site
  dsimp only [shortcut] at hcycleLength ⊢
  omega

/-- Every fusion site, of either chirality, yields a strictly shorter primal
circuit.  Negative chirality closes the original return lift; positive
chirality closes its one-edge bounce contraction. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_fusionSite
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length := by
  by_cases hpositive : lens.fusionChirality hab hac site = true
  · rcases lens.exists_shorter_primalCycle_of_chirality_eq_true
      hdata hab hac hbc site hpositive with
      ⟨start, cycle, hcycle, hshorter⟩
    exact ⟨start, cycle, hcycle.isCircuit, hshorter⟩
  · have hnegative : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hpositive
    have hreturn : lens.ReturnSpliceCoherent hab hac site :=
      (lens.returnSpliceCoherent_iff_chirality_eq_false
        hab hac site).2 hnegative
    rcases lens.exists_shorter_primalCycle_of_coherentReturn
      hdata hab hac site hreturn with
      ⟨start, cycle, hcycle, hshorter⟩
    exact ⟨start, cycle, hcycle.isCircuit, hshorter⟩

/-- A nonempty fusion-site list has a shorter primal circuit, with no
monodromy or chirality hypothesis. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_fusionSiteCount_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : 0 < lens.fusionSiteCount) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length := by
  exact lens.exists_shorter_primalCircuit_of_fusionSite
    hdata hab hac hbc (lens.bFusionSiteAt ⟨0, hcount⟩)

/-- In particular, the formerly residual identity signed-monodromy branch
shortens whenever it contains a physical fusion site. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_signedMonodromy_eq_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : 0 < lens.fusionSiteCount)
    (_hidentity : lens.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length :=
  lens.exists_shorter_primalCircuit_of_fusionSiteCount_pos
    hdata hab hac hbc hcount

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
