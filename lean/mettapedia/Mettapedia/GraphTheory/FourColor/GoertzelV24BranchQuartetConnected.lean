import Mettapedia.GraphTheory.FourColor.GoertzelV24BranchQuartetTree

/-!
# Quartet-free trees of 2-edge-connected graphs are connected

A vertex-disjoint pair of directions at a fork is pushed across the third
direction: quartet-freeness at that tree edge forces the merged pair to be
vertex-disjoint from one of the two directions beyond it, which is strictly
smaller.  Pairs involving the up-set are pushed downwards (a structural
induction from the leaves), sibling pairs are pushed upwards (a structural
induction from the root, carrying what the parent fork guarantees).  Both
inductions bottom out at a single edge, where 2-edge-connectedness
forbids the split.  Once every fork has pairwise-touching directions, both
shores of every cut are connected.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BranchQuartetConnected

open GoertzelV24BranchQuartetCalculus
open GoertzelV24BranchQuartetTree
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedEdgeShoreMajority
open EdgeLeafTree

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At every fork, both child shores meet the up-set. -/
def NoUpPair : EdgeLeafTree G.edgeSet → Finset G.edgeSet → Prop
  | .leaf _, _ => True
  | .fork a b, up =>
      bd (G := G) a.shore up ≠ ∅ ∧ bd (G := G) b.shore up ≠ ∅ ∧
        NoUpPair a (up ∪ b.shore) ∧ NoUpPair b (up ∪ a.shore)

/-- At every fork, the two child shores meet. -/
def NoSiblingPair : EdgeLeafTree G.edgeSet → Prop
  | .leaf _ => True
  | .fork a b => bd (G := G) a.shore b.shore ≠ ∅ ∧ NoSiblingPair a ∧ NoSiblingPair b

theorem bd_union_ne_empty_iff (X Y Z : Finset G.edgeSet) :
    bd (G := G) X (Y ∪ Z) ≠ ∅ ↔ bd (G := G) X Y ≠ ∅ ∨ bd (G := G) X Z ≠ ∅ := by
  rw [bd_union_right, Ne, Finset.union_eq_empty, not_and_or]

theorem union_eq_sdiff_singleton {X Y : Finset G.edgeSet} {edge : G.edgeSet}
    (hcover : X ∪ {edge} ∪ Y = Finset.univ) (hX : edge ∉ X) (hY : edge ∉ Y) :
    X ∪ Y = Finset.univ \ {edge} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
    true_and]
  constructor
  · rintro (hx | hx) <;> rintro rfl <;> contradiction
  · intro hne
    have hx : x ∈ X ∪ {edge} ∪ Y := by rw [hcover]; exact Finset.mem_univ x
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    tauto

/-! ## Pairs with the up-set are pushed downwards -/

/-- The local step for a child shore and the up-set: the pair is pushed into
the sibling, where the induction hypothesis forbids it. -/
theorem bd_up_ne_empty_of_siteFree (h₂ : G.IsEdgeConnected 2)
    {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (hg : Genuine (G := G) (fork a b) up)
    (hsite : SiteFree (G := G) b a.shore up)
    (hb : NoUpPair (G := G) b (up ∪ a.shore)) :
    bd (G := G) a.shore up ≠ ∅ := by
  intro hAU
  have hAn : a.shore.Nonempty := shore_nonempty a
  have hUn : up.Nonempty := hg.upNonempty
  cases b with
  | leaf edge =>
      have hcover := hg.cover
      rw [shore_fork, shore_leaf] at hcover
      have hedgeA : edge ∉ a.shore := by
        have := hg.disjoint_children
        rw [shore_leaf, Finset.disjoint_singleton_right] at this
        exact this
      have hedgeU : edge ∉ up := by
        have := hg.disjoint
        rw [shore_fork, shore_leaf, Finset.disjoint_union_left,
          Finset.disjoint_singleton_left] at this
        exact this.2
      exact bd_ne_empty_of_isEdgeConnected_two h₂ hAn hUn edge
        (union_eq_sdiff_singleton hcover hedgeA hedgeU) hAU
  | fork b₁ b₂ =>
      have hpre := preconnected_of_isEdgeConnected_two h₂
      have hcover := hg.cover
      simp only [shore_fork] at hcover
      have hA : bd (G := G) a.shore b₁.shore ≠ ∅ ∨ bd (G := G) a.shore b₂.shore ≠ ∅ := by
        have hne : bd (G := G) a.shore (up ∪ (b₁.shore ∪ b₂.shore)) ≠ ∅ := by
          refine bd_ne_empty_of_preconnected hpre hAn
            (Finset.Nonempty.mono Finset.subset_union_left hUn) ?_
          rw [← hcover]; ext x; simp only [Finset.mem_union]; tauto
        rw [bd_union_ne_empty_iff, bd_union_ne_empty_iff] at hne
        rcases hne with hne | hne
        · exact (hne hAU).elim
        · exact hne
      have hU : bd (G := G) up b₁.shore ≠ ∅ ∨ bd (G := G) up b₂.shore ≠ ∅ := by
        have hne : bd (G := G) up (a.shore ∪ (b₁.shore ∪ b₂.shore)) ≠ ∅ := by
          refine bd_ne_empty_of_preconnected hpre hUn
            (Finset.Nonempty.mono Finset.subset_union_left hAn) ?_
          rw [← hcover]; ext x; simp only [Finset.mem_union]; tauto
        rw [bd_union_ne_empty_iff, bd_union_ne_empty_iff] at hne
        rcases hne with hne | hne
        · exact (hne (by rwa [bd_comm])).elim
        · exact hne
      simp only [SiteFree, QuartetAt, not_or] at hsite
      obtain ⟨hb₁, hb₂, -, -⟩ := hb
      rcases rePair_empty_of_not_quartetPairs hAU hA hU hsite.2 with h | h
      · exact hb₁ (by rwa [bd_comm, Finset.union_comm] at h)
      · exact hb₂ (by rwa [bd_comm, Finset.union_comm] at h)

theorem noUpPair_of_quartetFree (h₂ : G.IsEdgeConnected 2) :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet),
      Genuine (G := G) t up → QuartetFree (G := G) t up → NoUpPair (G := G) t up
  | .leaf _, _, _, _ => trivial
  | .fork a b, up, hg, hqf => by
      obtain ⟨hsa, hsb, hqa, hqb⟩ := hqf
      have iha := noUpPair_of_quartetFree h₂ a (up ∪ b.shore) hg.left hqa
      have ihb := noUpPair_of_quartetFree h₂ b (up ∪ a.shore) hg.right hqb
      exact ⟨bd_up_ne_empty_of_siteFree h₂ hg hsb ihb,
        bd_up_ne_empty_of_siteFree h₂ hg.flip hsa iha, iha, ihb⟩

/-! ## Sibling pairs are pushed upwards -/

/-- What the parent fork guarantees about a subtree's up-set: either the
up-set is the single root leaf, or it splits into the sibling shore and the
parent's up-set, both met by the subtree, with no quartet on the tree edge
between them. -/
def UpContext (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet) : Prop :=
  up.card = 1 ∨
    ∃ sibling parentUp : Finset G.edgeSet,
      up = sibling ∪ parentUp ∧
        bd (G := G) t.shore sibling ≠ ∅ ∧ bd (G := G) t.shore parentUp ≠ ∅ ∧
          ∀ p q : EdgeLeafTree G.edgeSet, t = fork p q →
            ¬ QuartetPairs (G := G) p.shore q.shore sibling parentUp

theorem bd_children_ne_empty (h₂ : G.IsEdgeConnected 2)
    {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (hg : Genuine (G := G) (fork a b) up)
    (hctx : UpContext (G := G) (fork a b) up) :
    bd (G := G) a.shore b.shore ≠ ∅ := by
  intro hAB
  have hAn : a.shore.Nonempty := shore_nonempty a
  have hBn : b.shore.Nonempty := shore_nonempty b
  rcases hctx with hcard | ⟨S, Up, hup, hS, hUp, hnq⟩
  · obtain ⟨edge, rfl⟩ := Finset.card_eq_one.1 hcard
    have hcover := hg.cover
    rw [shore_fork, Finset.union_right_comm] at hcover
    have hd := hg.disjoint
    rw [shore_fork, Finset.disjoint_singleton_right, Finset.mem_union, not_or] at hd
    exact bd_ne_empty_of_isEdgeConnected_two h₂ hAn hBn edge
      (union_eq_sdiff_singleton hcover hd.1 hd.2) hAB
  · have hpre := preconnected_of_isEdgeConnected_two h₂
    have hcover := hg.cover
    rw [shore_fork, hup] at hcover
    have hA : bd (G := G) a.shore S ≠ ∅ ∨ bd (G := G) a.shore Up ≠ ∅ := by
      have hne : bd (G := G) a.shore (b.shore ∪ (S ∪ Up)) ≠ ∅ := by
        refine bd_ne_empty_of_preconnected hpre hAn
          (Finset.Nonempty.mono Finset.subset_union_left hBn) ?_
        rw [← hcover, Finset.union_assoc]
      rw [bd_union_ne_empty_iff, bd_union_ne_empty_iff] at hne
      rcases hne with hne | hne
      · exact (hne hAB).elim
      · exact hne
    have hB : bd (G := G) b.shore S ≠ ∅ ∨ bd (G := G) b.shore Up ≠ ∅ := by
      have hne : bd (G := G) b.shore (a.shore ∪ (S ∪ Up)) ≠ ∅ := by
        refine bd_ne_empty_of_preconnected hpre hBn
          (Finset.Nonempty.mono Finset.subset_union_left hAn) ?_
        rw [← hcover]; ext x; simp only [Finset.mem_union]; tauto
      rw [bd_union_ne_empty_iff, bd_union_ne_empty_iff] at hne
      rcases hne with hne | hne
      · exact (hne (by rwa [bd_comm])).elim
      · exact hne
    rw [shore_fork] at hS hUp
    rcases rePair_empty_of_not_quartetPairs hAB hA hB (hnq a b rfl) with h | h
    · exact hS h
    · exact hUp h

theorem noSiblingPair_of_quartetFree (h₂ : G.IsEdgeConnected 2) :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet),
      Genuine (G := G) t up → QuartetFree (G := G) t up → NoUpPair (G := G) t up →
      UpContext (G := G) t up → NoSiblingPair (G := G) t
  | .leaf _, _, _, _, _, _ => trivial
  | .fork a b, up, hg, hqf, hnu, hctx => by
      obtain ⟨hsa, hsb, hqa, hqb⟩ := hqf
      obtain ⟨hau, hbu, hnua, hnub⟩ := hnu
      have hAB := bd_children_ne_empty h₂ hg hctx
      refine ⟨hAB, ?_, ?_⟩
      · refine noSiblingPair_of_quartetFree h₂ a (up ∪ b.shore) hg.left hqa hnua
          (Or.inr ⟨b.shore, up, Finset.union_comm _ _, hAB, hau, ?_⟩)
        intro p q hpq
        subst hpq
        simp only [SiteFree, QuartetAt, not_or] at hsa
        exact hsa.1
      · refine noSiblingPair_of_quartetFree h₂ b (up ∪ a.shore) hg.right hqb hnub
          (Or.inr ⟨a.shore, up, Finset.union_comm _ _, by rwa [bd_comm], hbu, ?_⟩)
        intro p q hpq
        subst hpq
        simp only [SiteFree, QuartetAt, not_or] at hsb
        exact hsb.1

/-! ## Pairwise-touching directions give connected shores -/

theorem edgeShoreConnected_shore_of_noSiblingPair :
    ∀ t : EdgeLeafTree G.edgeSet, NoSiblingPair (G := G) t → EdgeShoreConnected G t.shore
  | .leaf edge, _ => by
      rw [shore_leaf]
      exact edgeShoreConnected_singleton edge
  | .fork a b, h => by
      obtain ⟨hab, ha, hb⟩ := h
      rw [shore_fork]
      exact edgeShoreConnected_union (edgeShoreConnected_shore_of_noSiblingPair a ha)
        (edgeShoreConnected_shore_of_noSiblingPair b hb) hab

theorem cutConnected_of_noPairs :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet),
      NoUpPair (G := G) t up → NoSiblingPair (G := G) t → EdgeShoreConnected G up →
      CutConnected (G := G) t up
  | .leaf edge, _, _, _, hup => ⟨edgeShoreConnected_singleton edge, hup⟩
  | .fork a b, up, hnu, hns, hup => by
      obtain ⟨hau, hbu, hnua, hnub⟩ := hnu
      obtain ⟨hab, hnsa, hnsb⟩ := hns
      have ha := edgeShoreConnected_shore_of_noSiblingPair a hnsa
      have hb := edgeShoreConnected_shore_of_noSiblingPair b hnsb
      refine ⟨edgeShoreConnected_union ha hb hab, hup, ?_, ?_⟩
      · exact cutConnected_of_noPairs a _ hnua hnsa
          (edgeShoreConnected_union hup hb (by rwa [bd_comm]))
      · exact cutConnected_of_noPairs b _ hnub hnsb
          (edgeShoreConnected_union hup ha (by rwa [bd_comm]))

/-- **Claim 2**: a quartet-free genuine tree of a 2-edge-connected graph,
rooted at a single root leaf, has both shores of every cut connected. -/
theorem cutConnected_of_quartetFree (h₂ : G.IsEdgeConnected 2)
    (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet)
    (hg : Genuine (G := G) t up) (hqf : QuartetFree (G := G) t up)
    (hcard : up.card = 1) (hup : EdgeShoreConnected G up) :
    CutConnected (G := G) t up :=
  have hnu := noUpPair_of_quartetFree h₂ t up hg hqf
  cutConnected_of_noPairs t up hnu
    (noSiblingPair_of_quartetFree h₂ t up hg hqf hnu (Or.inl hcard)) hup

end

end GoertzelV24BranchQuartetConnected

end Mettapedia.GraphTheory.FourColor
