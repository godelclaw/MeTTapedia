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

theorem psi_swap₁₃ (S₁ S₂ S₃ : Finset G.edgeSet) :
    psi (G := G) S₁ S₂ S₃ = psi (G := G) S₃ S₂ S₁ := by
  rw [psi_swap₁₂, psi_swap₂₃, psi_swap₁₂]

/-! ## Quartets at a site -/

/-- The four shores `P, Q | R, T` around a tree edge form a quartet with
`P, Q` as the vertex-disjoint pair: `P` and `Q` share no vertex, and the two
shores across the edge can be matched to them with non-empty boundaries. -/
def QuartetPairs (P Q R T : Finset G.edgeSet) : Prop :=
  bd (G := G) P Q = ∅ ∧
    ((bd (G := G) P R ≠ ∅ ∧ bd (G := G) Q T ≠ ∅) ∨
      (bd (G := G) P T ≠ ∅ ∧ bd (G := G) Q R ≠ ∅))

section Site

variable {P Q R T : Finset G.edgeSet} {w : ℕ}

/-- Claim 1 of the connectedization lemma at one site: when re-pairing `P`
with `R` is a quartet replacement, either that replacement keeps the width,
or the other re-pairing is also a quartet replacement and keeps the width. -/
theorem rePair_width_choice
    (hPQ : bd (G := G) P Q = ∅) (hPR : bd (G := G) P R ≠ ∅)
    (hQT : bd (G := G) Q T ≠ ∅)
    (hR : (bd (G := G) R (P ∪ Q ∪ T)).card ≤ w)
    (hT : (bd (G := G) T (P ∪ Q ∪ R)).card ≤ w) :
    (bd (G := G) (P ∪ R) (Q ∪ T)).card ≤ w ∨
      (bd (G := G) P T ≠ ∅ ∧ bd (G := G) Q R ≠ ∅ ∧
        (bd (G := G) (P ∪ T) (Q ∪ R)).card ≤ w) := by
  by_cases hPT : bd (G := G) P T = ∅
  · exact Or.inl (le_trans (Finset.card_le_card
      (bd_rePair_subset_of_bd_eq_empty P Q R T hPQ hPT)) hR)
  by_cases hRQ : bd (G := G) R Q = ∅
  · exact Or.inl (le_trans (Finset.card_le_card
      (bd_rePair_subset_of_bd_eq_empty' P Q R T hPQ hRQ)) hT)
  have hsum := card_bd_rePair_add_le (G := G) P Q R T hPQ
  by_cases hone : (bd (G := G) (P ∪ R) (Q ∪ T)).card ≤ w
  · exact Or.inl hone
  · refine Or.inr ⟨hPT, ?_, by omega⟩
    rwa [bd_comm]

/-- Every quartet admits a width-preserving quartet replacement. -/
theorem rePair_choice_of_quartetPairs (hq : QuartetPairs (G := G) P Q R T)
    (hR : (bd (G := G) R (P ∪ Q ∪ T)).card ≤ w)
    (hT : (bd (G := G) T (P ∪ Q ∪ R)).card ≤ w) :
    (bd (G := G) P R ≠ ∅ ∧ bd (G := G) Q T ≠ ∅ ∧
        (bd (G := G) (P ∪ R) (Q ∪ T)).card ≤ w) ∨
      (bd (G := G) P T ≠ ∅ ∧ bd (G := G) Q R ≠ ∅ ∧
        (bd (G := G) (P ∪ T) (Q ∪ R)).card ≤ w) := by
  obtain ⟨hPQ, hcross⟩ := hq
  rcases hcross with ⟨hPR, hQT⟩ | ⟨hPT, hQR⟩
  · rcases rePair_width_choice hPQ hPR hQT hR hT with hleft | hright
    · exact Or.inl ⟨hPR, hQT, hleft⟩
    · exact Or.inr hright
  · rcases rePair_width_choice hPQ hPT hQR hT hR with hleft | hright
    · exact Or.inr ⟨hPT, hQR, hleft⟩
    · exact Or.inl hright

/-- Claim 2's local step: at a quartet-free site whose `A, U` pair is
vertex-disjoint, the merged shore `A ∪ U` is vertex-disjoint from one of the
two shores across the edge. -/
theorem rePair_empty_of_not_quartetPairs {A U B₁ B₂ : Finset G.edgeSet}
    (hAU : bd (G := G) A U = ∅)
    (hA : bd (G := G) A B₁ ≠ ∅ ∨ bd (G := G) A B₂ ≠ ∅)
    (hU : bd (G := G) U B₁ ≠ ∅ ∨ bd (G := G) U B₂ ≠ ∅)
    (hnq : ¬ QuartetPairs (G := G) A U B₁ B₂) :
    bd (G := G) (A ∪ U) B₁ = ∅ ∨ bd (G := G) (A ∪ U) B₂ = ∅ := by
  simp only [QuartetPairs, bd_union_left, Finset.union_eq_empty] at *
  tauto

end Site

/-! ## Boundaries and walks -/

theorem touch_of_mem {X : Finset G.edgeSet} {edge : G.edgeSet} (hedge : edge ∈ X)
    {vertex : V} (hvertex : vertex ∈ (edge : Sym2 V)) : Touch (G := G) X vertex :=
  ⟨edge, hedge, hvertex⟩

/-- A walk whose edges all lie in `S₁ ∪ S₂`, started at a vertex of `S₁`,
stays on `S₁` when the two shores share no vertex. -/
theorem touch_end_of_walk {S₁ S₂ : Finset G.edgeSet} (hbd : bd (G := G) S₁ S₂ = ∅) :
    ∀ {u v : V} (walk : G.Walk u v),
      (∀ f : G.edgeSet, (f : Sym2 V) ∈ walk.edges → f ∈ S₁ ∪ S₂) →
      Touch (G := G) S₁ u → Touch (G := G) S₁ v
  | _, _, .nil, _, hu => hu
  | u, v, .cons (v := x) hadj rest, hedges, hu => by
      have hf : (⟨s(u, x), hadj⟩ : G.edgeSet) ∈ S₁ ∪ S₂ :=
        hedges _ (by simp [SimpleGraph.Walk.edges_cons])
      refine touch_end_of_walk hbd rest (fun f hf' => hedges f ?_) ?_
      · simp [SimpleGraph.Walk.edges_cons, hf']
      · rcases Finset.mem_union.1 hf with h₁ | h₂
        · exact ⟨_, h₁, by simp⟩
        · exfalso
          have hmem : u ∈ bd (G := G) S₁ S₂ :=
            (mem_bd_iff_touch S₁ S₂ u).2 ⟨hu, ⟨_, h₂, by simp⟩⟩
          rw [hbd] at hmem
          exact Finset.notMem_empty u hmem

theorem bd_ne_empty_of_walk {S₁ S₂ : Finset G.edgeSet} {u v : V}
    (walk : G.Walk u v)
    (hedges : ∀ f : G.edgeSet, (f : Sym2 V) ∈ walk.edges → f ∈ S₁ ∪ S₂)
    (hu : Touch (G := G) S₁ u) (hv : Touch (G := G) S₂ v) :
    bd (G := G) S₁ S₂ ≠ ∅ := by
  intro hbd
  have hv' := touch_end_of_walk hbd walk hedges hu
  have hmem : v ∈ bd (G := G) S₁ S₂ := (mem_bd_iff_touch S₁ S₂ v).2 ⟨hv', hv⟩
  rw [hbd] at hmem
  exact Finset.notMem_empty v hmem

theorem exists_touch_of_nonempty {X : Finset G.edgeSet} (hX : X.Nonempty) :
    ∃ vertex : V, Touch (G := G) X vertex := by
  obtain ⟨edge, hedge⟩ := hX
  exact ⟨(edge : Sym2 V).out.1, edge, hedge, Sym2.out_fst_mem _⟩

/-- In a preconnected graph, two non-empty shores covering every edge share
a vertex. -/
theorem bd_ne_empty_of_preconnected (hpre : G.Preconnected)
    {X Y : Finset G.edgeSet} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hcover : X ∪ Y = Finset.univ) : bd (G := G) X Y ≠ ∅ := by
  obtain ⟨u, hu⟩ := exists_touch_of_nonempty (G := G) hX
  obtain ⟨v, hv⟩ := exists_touch_of_nonempty (G := G) hY
  obtain ⟨walk⟩ := hpre u v
  exact bd_ne_empty_of_walk walk (fun f _ => by rw [hcover]; exact Finset.mem_univ f) hu hv

/-- In a 2-edge-connected graph, two non-empty shores covering every edge but
one share a vertex. -/
theorem bd_ne_empty_of_isEdgeConnected_two (h₂ : G.IsEdgeConnected 2)
    {X Y : Finset G.edgeSet} (hX : X.Nonempty) (hY : Y.Nonempty)
    (edge : G.edgeSet) (hcover : X ∪ Y = Finset.univ \ {edge}) :
    bd (G := G) X Y ≠ ∅ := by
  obtain ⟨u, hu⟩ := exists_touch_of_nonempty (G := G) hX
  obtain ⟨v, hv⟩ := exists_touch_of_nonempty (G := G) hY
  obtain ⟨walk⟩ := (SimpleGraph.isEdgeConnected_two.1 h₂ (edge : Sym2 V)) u v
  refine bd_ne_empty_of_walk (walk.mapLe (SimpleGraph.deleteEdges_le _)) ?_ hu hv
  intro f hf
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hf
  have hf' := walk.edges_subset_edgeSet hf
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff] at hf'
  rw [hcover, Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨Finset.mem_univ f, fun heq => hf'.2 (by rw [heq])⟩

theorem preconnected_of_isEdgeConnected_two (h₂ : G.IsEdgeConnected 2) :
    G.Preconnected :=
  h₂.preconnected (by decide)

/-! ## Connected shores -/

theorem edgeShoreConnected_singleton (edge : G.edgeSet) :
    EdgeShoreConnected G {edge} := by
  intro u v hu hv
  obtain ⟨e, he, hue⟩ := hu
  obtain ⟨e', he', hve⟩ := hv
  rw [Finset.mem_singleton] at he he'
  rw [he] at hue
  rw [he'] at hve
  by_cases huv : u = v
  · subst huv
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · have hedge : (edge : Sym2 V) = s(u, v) := (Sym2.mem_and_mem_iff huv).1 ⟨hue, hve⟩
    have hadj : G.Adj u v := by
      have := edge.2
      rw [hedge] at this
      exact this
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro f hf
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton] at hf
    rw [Finset.mem_singleton]
    exact Subtype.ext (by rw [hf, hedge])

/-- Two connected shores sharing a vertex have a connected union. -/
theorem edgeShoreConnected_union {X Y : Finset G.edgeSet}
    (hX : EdgeShoreConnected G X) (hY : EdgeShoreConnected G Y)
    (hbd : bd (G := G) X Y ≠ ∅) : EdgeShoreConnected G (X ∪ Y) := by
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hbd
  rw [mem_bd_iff] at hz
  intro u v hu hv
  -- a walk from `u` to `z`, then from `z` to `v`, each inside one shore
  have step : ∀ {a : V}, (∃ edge ∈ X ∪ Y, a ∈ (edge : Sym2 V)) →
      ∃ walk : G.Walk a z, ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
        edge ∈ X ∪ Y := by
    intro a ha
    obtain ⟨edge, hedge, hae⟩ := ha
    rcases Finset.mem_union.1 hedge with hedge | hedge
    · obtain ⟨walk, hwalk⟩ := hX ⟨edge, hedge, hae⟩ hz.1
      exact ⟨walk, fun f hf => Finset.mem_union_left _ (hwalk f hf)⟩
    · obtain ⟨walk, hwalk⟩ := hY ⟨edge, hedge, hae⟩ hz.2
      exact ⟨walk, fun f hf => Finset.mem_union_right _ (hwalk f hf)⟩
  obtain ⟨walk₁, hwalk₁⟩ := step hu
  obtain ⟨walk₂, hwalk₂⟩ := step hv
  refine ⟨walk₁.append walk₂.reverse, ?_⟩
  intro f hf
  rw [SimpleGraph.Walk.edges_append, List.mem_append,
    SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hf
  rcases hf with hf | hf
  · exact hwalk₁ f hf
  · exact hwalk₂ f hf

/-- Deleting one edge from a 2-edge-connected graph leaves a connected shore. -/
theorem edgeShoreConnected_compl_singleton (h₂ : G.IsEdgeConnected 2)
    (edge : G.edgeSet) : EdgeShoreConnected G (Finset.univ \ {edge}) := by
  intro u v _ _
  obtain ⟨walk⟩ := (SimpleGraph.isEdgeConnected_two.1 h₂ (edge : Sym2 V)) u v
  refine ⟨walk.mapLe (SimpleGraph.deleteEdges_le _), ?_⟩
  intro f hf
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hf
  have hf' := walk.edges_subset_edgeSet hf
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff] at hf'
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨Finset.mem_univ f, fun heq => hf'.2 (by rw [heq])⟩


end

end GoertzelV24BranchQuartetCalculus

end Mettapedia.GraphTheory.FourColor
