import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedEdgeShoreMajority

/-!
# The boundary calculus behind quartet replacement

A branch decomposition is made connected by repeatedly replacing a *quartet*:
four edge shores `P, Q, R, T` hanging off one tree edge, with `P` and `Q`
vertex-disjoint and with `P` touching `R` and `Q` touching `T`.  The
replacement re-pairs the shores across that tree edge.  Two facts make this
work, and both are statements about boundaries of finite edge sets alone:

* the re-paired cut is no wider than the wider of the two shores `R`, `T`
  (in one of the two possible re-pairings), and
* a potential summed over the tree's internal vertices strictly decreases.

This file proves those two facts.  Nothing here mentions trees or graphs
beyond edge incidence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BranchQuartetCalculus

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24SphereCutMaterial

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Boundaries between edge sets -/

/-- Vertices incident with an edge of `X` and with an edge of `Y`. -/
def bd (X Y : Finset G.edgeSet) : Finset V :=
  Finset.univ.filter fun vertex =>
    (∃ edge ∈ X, vertex ∈ (edge : Sym2 V)) ∧
      ∃ edge ∈ Y, vertex ∈ (edge : Sym2 V)

theorem mem_bd_iff (X Y : Finset G.edgeSet) (vertex : V) :
    vertex ∈ bd (G := G) X Y ↔
      (∃ edge ∈ X, vertex ∈ (edge : Sym2 V)) ∧
        ∃ edge ∈ Y, vertex ∈ (edge : Sym2 V) := by
  simp [bd]

theorem bd_comm (X Y : Finset G.edgeSet) :
    bd (G := G) X Y = bd (G := G) Y X := by
  ext vertex
  simp only [mem_bd_iff]
  exact and_comm

theorem bd_union_left (X X' Y : Finset G.edgeSet) :
    bd (G := G) (X ∪ X') Y = bd (G := G) X Y ∪ bd (G := G) X' Y := by
  ext vertex
  simp only [mem_bd_iff, Finset.mem_union]
  constructor
  · rintro ⟨⟨edge, hedge, hv⟩, hY⟩
    rcases hedge with hedge | hedge
    · exact Or.inl ⟨⟨edge, hedge, hv⟩, hY⟩
    · exact Or.inr ⟨⟨edge, hedge, hv⟩, hY⟩
  · rintro (⟨⟨edge, hedge, hv⟩, hY⟩ | ⟨⟨edge, hedge, hv⟩, hY⟩)
    · exact ⟨⟨edge, Or.inl hedge, hv⟩, hY⟩
    · exact ⟨⟨edge, Or.inr hedge, hv⟩, hY⟩

theorem bd_union_right (X Y Y' : Finset G.edgeSet) :
    bd (G := G) X (Y ∪ Y') = bd (G := G) X Y ∪ bd (G := G) X Y' := by
  rw [bd_comm, bd_union_left, bd_comm X Y, bd_comm X Y']

theorem bd_subset_bd {X X' Y Y' : Finset G.edgeSet}
    (hX : X ⊆ X') (hY : Y ⊆ Y') :
    bd (G := G) X Y ⊆ bd (G := G) X' Y' := by
  intro vertex hvertex
  rw [mem_bd_iff] at hvertex ⊢
  obtain ⟨⟨e, he, hv⟩, ⟨f, hf, hw⟩⟩ := hvertex
  exact ⟨⟨e, hX he, hv⟩, ⟨f, hY hf, hw⟩⟩

theorem bd_mono_right (X : Finset G.edgeSet) {Y Y' : Finset G.edgeSet}
    (hY : Y ⊆ Y') : bd (G := G) X Y ⊆ bd (G := G) X Y' :=
  bd_subset_bd (subset_refl X) hY

/-- The middle set of a shore is its boundary against the complement. -/
theorem edgeShoreMiddleVertices_eq_bd (X : Finset G.edgeSet) :
    edgeShoreMiddleVertices G X = bd (G := G) X (Finset.univ \ X) := by
  ext vertex
  simp [edgeShoreMiddleVertices, mem_middleVertices_iff, mem_bd_iff]

theorem bd_eq_empty_iff (X Y : Finset G.edgeSet) :
    bd (G := G) X Y = ∅ ↔
      ∀ vertex : V,
        (∃ edge ∈ X, vertex ∈ (edge : Sym2 V)) →
          ¬ ∃ edge ∈ Y, vertex ∈ (edge : Sym2 V) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_bd_iff, not_and]

theorem bd_empty_left (Y : Finset G.edgeSet) : bd (G := G) ∅ Y = ∅ := by
  ext vertex
  simp [mem_bd_iff]

theorem bd_empty_right (X : Finset G.edgeSet) : bd (G := G) X ∅ = ∅ := by
  rw [bd_comm, bd_empty_left]

/-! ## Width of the re-paired cut -/

/-- `vertex` is incident with some edge of `X`. -/
def Touch (X : Finset G.edgeSet) (vertex : V) : Prop :=
  ∃ edge ∈ X, vertex ∈ (edge : Sym2 V)

theorem mem_bd_iff_touch (X Y : Finset G.edgeSet) (vertex : V) :
    vertex ∈ bd (G := G) X Y ↔ Touch (G := G) X vertex ∧ Touch (G := G) Y vertex :=
  mem_bd_iff X Y vertex

theorem touch_union (X Y : Finset G.edgeSet) (vertex : V) :
    Touch (G := G) (X ∪ Y) vertex ↔
      Touch (G := G) X vertex ∨ Touch (G := G) Y vertex := by
  simp only [Touch, Finset.mem_union]
  constructor
  · rintro ⟨e, he | he, hv⟩
    · exact Or.inl ⟨e, he, hv⟩
    · exact Or.inr ⟨e, he, hv⟩
  · rintro (⟨e, he, hv⟩ | ⟨e, he, hv⟩)
    · exact ⟨e, Or.inl he, hv⟩
    · exact ⟨e, Or.inr he, hv⟩

theorem not_touch_both_of_bd_eq_empty {X Y : Finset G.edgeSet}
    (h : bd (G := G) X Y = ∅) (vertex : V) :
    ¬ (Touch (G := G) X vertex ∧ Touch (G := G) Y vertex) := by
  intro hboth
  have : vertex ∈ bd (G := G) X Y := (mem_bd_iff_touch X Y vertex).2 hboth
  rw [h] at this
  simp at this

section Width

variable (P Q R T : Finset G.edgeSet)

/-- Re-pairing `P` with `R`: when `P` does not touch `T`, the new cut lies
inside the middle set of `R`. -/
theorem bd_rePair_subset_of_bd_eq_empty
    (hPQ : bd (G := G) P Q = ∅) (hPT : bd (G := G) P T = ∅) :
    bd (G := G) (P ∪ R) (Q ∪ T) ⊆ bd (G := G) R (P ∪ Q ∪ T) := by
  intro v hv
  have hPQ' := not_touch_both_of_bd_eq_empty hPQ v
  have hPT' := not_touch_both_of_bd_eq_empty hPT v
  simp only [mem_bd_iff_touch, touch_union] at hv ⊢
  tauto

/-- Re-pairing `P` with `R`: when `R` does not touch `Q`, the new cut lies
inside the middle set of `T`. -/
theorem bd_rePair_subset_of_bd_eq_empty'
    (hPQ : bd (G := G) P Q = ∅) (hRQ : bd (G := G) R Q = ∅) :
    bd (G := G) (P ∪ R) (Q ∪ T) ⊆ bd (G := G) T (P ∪ Q ∪ R) := by
  intro v hv
  have hPQ' := not_touch_both_of_bd_eq_empty hPQ v
  have hRQ' := not_touch_both_of_bd_eq_empty hRQ v
  simp only [mem_bd_iff_touch, touch_union] at hv ⊢
  tauto

/-- **The two re-pairings together are no wider than the two old shores.** -/
theorem card_bd_rePair_add_le (hPQ : bd (G := G) P Q = ∅) :
    (bd (G := G) (P ∪ R) (Q ∪ T)).card +
        (bd (G := G) (P ∪ T) (Q ∪ R)).card ≤
      (bd (G := G) R (P ∪ Q ∪ T)).card +
        (bd (G := G) T (P ∪ Q ∪ R)).card := by
  set L₁ := bd (G := G) (P ∪ R) (Q ∪ T)
  set L₂ := bd (G := G) (P ∪ T) (Q ∪ R)
  set M₁ := bd (G := G) R (P ∪ Q ∪ T)
  set M₂ := bd (G := G) T (P ∪ Q ∪ R)
  have hunion : L₁ ∪ L₂ ⊆ M₁ ∪ M₂ := by
    intro v hv
    have hPQ' := not_touch_both_of_bd_eq_empty hPQ v
    simp only [L₁, L₂, M₁, M₂, Finset.mem_union, mem_bd_iff_touch,
      touch_union] at hv ⊢
    tauto
  have hinter : L₁ ∩ L₂ ⊆ M₁ ∩ M₂ := by
    intro v hv
    have hPQ' := not_touch_both_of_bd_eq_empty hPQ v
    simp only [L₁, L₂, M₁, M₂, Finset.mem_inter, mem_bd_iff_touch,
      touch_union] at hv ⊢
    tauto
  have hcard := Finset.card_union_add_card_inter L₁ L₂
  have hcard' := Finset.card_union_add_card_inter M₁ M₂
  have h₁ := Finset.card_le_card hunion
  have h₂ := Finset.card_le_card hinter
  omega

end Width

/-! ## The vertex potential -/

/-- The potential of one internal tree vertex with the three edge shores
`S₁, S₂, S₃` in its three directions: for each pair of directions that share
no vertex, the size (minus one) of the remaining direction.  Summed over all
internal vertices this strictly decreases under quartet replacement. -/
def psi (S₁ S₂ S₃ : Finset G.edgeSet) : Nat :=
  (if bd (G := G) S₁ S₂ = ∅ then S₃.card - 1 else 0) +
    (if bd (G := G) S₁ S₃ = ∅ then S₂.card - 1 else 0) +
      (if bd (G := G) S₂ S₃ = ∅ then S₁.card - 1 else 0)

theorem psi_swap₂₃ (S₁ S₂ S₃ : Finset G.edgeSet) :
    psi (G := G) S₁ S₂ S₃ = psi (G := G) S₁ S₃ S₂ := by
  unfold psi
  rw [bd_comm (G := G) S₃ S₂]
  omega

theorem psi_swap₁₂ (S₁ S₂ S₃ : Finset G.edgeSet) :
    psi (G := G) S₁ S₂ S₃ = psi (G := G) S₂ S₁ S₃ := by
  unfold psi
  rw [bd_comm (G := G) S₂ S₁]
  omega

theorem union_ne_empty_left {X Y : Finset G.edgeSet} (h : bd (G := G) X Y ≠ ∅)
    (Z : Finset G.edgeSet) : bd (G := G) X (Y ∪ Z) ≠ ∅ := by
  rw [bd_union_right]
  intro hcon
  exact h (Finset.union_eq_empty.1 hcon).1

theorem union_ne_empty_right {X Z : Finset G.edgeSet} (h : bd (G := G) X Z ≠ ∅)
    (Y : Finset G.edgeSet) : bd (G := G) X (Y ∪ Z) ≠ ∅ := by
  rw [bd_union_right]
  intro hcon
  exact h (Finset.union_eq_empty.1 hcon).2

section Potential

variable (P Q R T : Finset G.edgeSet)

/-- **Quartet replacement strictly decreases the potential.**  Only the two
vertices incident with the replaced tree edge change; before, they see
`(P, Q, R ∪ T)` and `(P ∪ Q, R, T)`, after re-pairing `P` with `R` they see
`(P, R, Q ∪ T)` and `(P ∪ R, Q, T)`. -/
theorem psi_rePair_lt
    (hPQ : bd (G := G) P Q = ∅) (hPR : bd (G := G) P R ≠ ∅)
    (hQT : bd (G := G) Q T ≠ ∅)
    (hR : R.Nonempty) (hT : T.Nonempty)
    (hPQd : Disjoint P Q) (hRTd : Disjoint R T) :
    psi (G := G) P R (Q ∪ T) + psi (G := G) (P ∪ R) Q T <
      psi (G := G) P Q (R ∪ T) + psi (G := G) (P ∪ Q) R T := by
  have hPcard : 1 ≤ P.card := by
    refine Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 ?_)
    rintro rfl
    exact hPR (bd_empty_left R)
  have hQcard : 1 ≤ Q.card := by
    refine Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 ?_)
    rintro rfl
    exact hQT (bd_empty_left T)
  have hRcard : 1 ≤ R.card := Finset.card_pos.2 hR
  have hTcard : 1 ≤ T.card := Finset.card_pos.2 hT
  have hRT : (R ∪ T).card = R.card + T.card := Finset.card_union_of_disjoint hRTd
  have hPQc : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hPQd
  -- old vertex 1 : (P, Q, R ∪ T)
  have h1 : psi (G := G) P Q (R ∪ T) = R.card + T.card - 1 := by
    unfold psi
    rw [if_pos hPQ, if_neg (union_ne_empty_left hPR T),
      if_neg (union_ne_empty_right hQT R), hRT]
    omega
  -- old vertex 2 : (P ∪ Q, R, T)
  have h2 : psi (G := G) (P ∪ Q) R T =
      if bd (G := G) R T = ∅ then P.card + Q.card - 1 else 0 := by
    unfold psi
    have hR' : bd (G := G) (P ∪ Q) R ≠ ∅ := by
      rw [bd_union_left]; intro hcon; exact hPR (Finset.union_eq_empty.1 hcon).1
    have hT' : bd (G := G) (P ∪ Q) T ≠ ∅ := by
      rw [bd_union_left]; intro hcon; exact hQT (Finset.union_eq_empty.1 hcon).2
    rw [if_neg hR', if_neg hT', hPQc]
    omega
  -- new vertex 1 : (P, R, Q ∪ T)
  have h3 : psi (G := G) P R (Q ∪ T) =
      (if bd (G := G) P T = ∅ then R.card - 1 else 0) +
        (if bd (G := G) R Q = ∅ ∧ bd (G := G) R T = ∅ then P.card - 1 else 0) := by
    unfold psi
    simp only [if_neg hPR, bd_union_right, hPQ, Finset.empty_union,
      Finset.union_eq_empty, zero_add]
  -- new vertex 2 : (P ∪ R, Q, T)
  have h4 : psi (G := G) (P ∪ R) Q T =
      (if bd (G := G) R Q = ∅ then T.card - 1 else 0) +
        (if bd (G := G) P T = ∅ ∧ bd (G := G) R T = ∅ then Q.card - 1 else 0) := by
    unfold psi
    simp only [if_neg hQT, bd_union_left, hPQ, Finset.empty_union,
      Finset.union_eq_empty, add_zero]
  rw [h1, h2, h3, h4]
  clear h1 h2 h3 h4
  by_cases hRT' : bd (G := G) R T = ∅ <;> by_cases hPT : bd (G := G) P T = ∅ <;>
    by_cases hRQ : bd (G := G) R Q = ∅ <;>
    simp only [hRT', hPT, hRQ, and_self, and_false, false_and, if_true, if_false] <;>
    omega

/-- The mirror statement for re-pairing `P` with `T` and `Q` with `R`. -/
theorem psi_rePair_lt'
    (hPQ : bd (G := G) P Q = ∅) (hPT : bd (G := G) P T ≠ ∅)
    (hQR : bd (G := G) Q R ≠ ∅)
    (hR : R.Nonempty) (hT : T.Nonempty)
    (hPQd : Disjoint P Q) (hRTd : Disjoint R T) :
    psi (G := G) P T (Q ∪ R) + psi (G := G) (P ∪ T) Q R <
      psi (G := G) P Q (R ∪ T) + psi (G := G) (P ∪ Q) R T := by
  have := psi_rePair_lt (G := G) P Q T R hPQ hPT hQR hT hR hPQd hRTd.symm
  rw [Finset.union_comm T R, psi_swap₂₃ (G := G) (P ∪ Q) T R] at this
  exact this

end Potential


end

end GoertzelV24BranchQuartetCalculus

end Mettapedia.GraphTheory.FourColor
