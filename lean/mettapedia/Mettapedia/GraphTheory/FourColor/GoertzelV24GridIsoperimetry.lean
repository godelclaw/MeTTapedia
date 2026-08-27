import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grid isoperimetry, and why bounded cut chains die in a wall

A large grid has no small cuts.  Precisely: if a vertex set `S` of the `r × r`
grid has at most `k < r` boundary edges, then either `S` or its complement has at
most `k²` vertices.

The proof is the row/column argument.  A row that is neither wholly inside nor
wholly outside `S` contains a horizontal boundary edge, and a column likewise a
vertical one, so there are at most `k` partial rows and at most `k` partial
columns.  If some row is full and some column is full then every complement
vertex sits at a partial row and a partial column, so the complement has at
most `k²` vertices; if no row is full and no column is full the same holds for
`S`; and the mixed cases force every row or every column to be partial, which
needs `r ≤ k` boundary edges.

The consequence for the descent is the point of this file.  A nested chain of
vertex sets, each with at most `k` boundary edges, alternates between "small
inside" and "small outside" only once, and each regime is strictly increasing
within a set of size at most `k²`.  So the chain has at most `2k²` steps.  The
direct Count descent needs more than `2^(3^k)` steps to force a repeated
support, and `2k² < 2^(3^k)` for every `k ≥ 1`.  Hence, **inside a grid region,
the linear pumping never has enough cut positions** — not because the cuts are
hard to find, but because they do not exist.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GridIsoperimetry

variable {r : ℕ}

/-- A vertex of the `r × r` grid: a row and a column. -/
abbrev GridVertex (r : ℕ) := Fin r × Fin r

/-- Grid adjacency: same row and consecutive columns, or same column and
consecutive rows. -/
def Adjacent (u v : GridVertex r) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
    (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

instance : DecidableRel (Adjacent (r := r)) := fun _ _ => by
  unfold Adjacent; infer_instance

/-- The boundary of `S`: ordered pairs `(u, v)` with `u ∈ S`, `v ∉ S`, adjacent.
Each boundary edge is recorded once, oriented outward. -/
def edgeBoundary (S : Finset (GridVertex r)) : Finset (GridVertex r × GridVertex r) :=
  Finset.univ.filter fun p => p.1 ∈ S ∧ p.2 ∉ S ∧ Adjacent p.1 p.2

/-- Boundary edges lying within a row. -/
def horizontalBoundary (S : Finset (GridVertex r)) : Finset (GridVertex r × GridVertex r) :=
  (edgeBoundary S).filter fun p => p.1.1 = p.2.1

/-- Boundary edges lying within a column. -/
def verticalBoundary (S : Finset (GridVertex r)) : Finset (GridVertex r × GridVertex r) :=
  (edgeBoundary S).filter fun p => p.1.2 = p.2.2

/-- Rows meeting both `S` and its complement. -/
def partialRows (S : Finset (GridVertex r)) : Finset (Fin r) :=
  Finset.univ.filter fun i => (∃ j, (i, j) ∈ S) ∧ ∃ j, (i, j) ∉ S

/-- Columns meeting both `S` and its complement. -/
def partialCols (S : Finset (GridVertex r)) : Finset (Fin r) :=
  Finset.univ.filter fun j => (∃ i, (i, j) ∈ S) ∧ ∃ i, (i, j) ∉ S

/-! ## A change of status happens at consecutive positions -/

/-- Along a line, a predicate that holds at `a` and fails `d` steps later fails
for the first time right after some position where it still held. -/
theorem exists_change (P : ℕ → Prop) : ∀ (d a : ℕ), P a → ¬ P (a + d) →
    ∃ t, t < d ∧ P (a + t) ∧ ¬ P (a + t + 1) := by
  intro d
  induction d with
  | zero => intro a ha hna; exact absurd ha hna
  | succ d ih =>
      intro a ha hna
      by_cases hmid : P (a + d)
      · exact ⟨d, Nat.lt_succ_self d, hmid, by simpa [Nat.add_assoc] using hna⟩
      · obtain ⟨t, ht, h1, h2⟩ := ih a ha hmid
        exact ⟨t, Nat.lt_succ_of_lt ht, h1, h2⟩

/-- A partial row carries a horizontal boundary edge. -/
theorem exists_horizontal_of_partialRow (S : Finset (GridVertex r)) {i : Fin r}
    (hi : i ∈ partialRows S) :
    ∃ p ∈ horizontalBoundary S, p.1.1 = i := by
  classical
  simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩ := hi
  -- the status along row `i`, as a predicate on natural column indices
  let P : ℕ → Prop := fun t => ∃ h : t < r, (i, ⟨t, h⟩) ∈ S
  have hP₁ : P j₁.val := ⟨j₁.isLt, by simpa using hj₁⟩
  have hP₂ : ¬ P j₂.val := by
    rintro ⟨h, hmem⟩
    exact hj₂ (by simpa using hmem)
  rcases Nat.lt_or_ge j₁.val j₂.val with hlt | hge
  · obtain ⟨t, ht, ⟨hlt₁, hin⟩, hout⟩ :=
      exists_change P (j₂.val - j₁.val) j₁.val hP₁ (by
        have : j₁.val + (j₂.val - j₁.val) = j₂.val := by omega
        rw [this]; exact hP₂)
    have hb : j₁.val + t + 1 < r := by omega
    refine ⟨((i, ⟨j₁.val + t, hlt₁⟩), (i, ⟨j₁.val + t + 1, hb⟩)), ?_, rfl⟩
    simp only [horizontalBoundary, edgeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hin, fun hmem => hout ⟨hb, hmem⟩, ?_⟩, trivial⟩
    exact Or.inl ⟨rfl, Or.inl rfl⟩
  · -- the status flips the other way: run the argument on the negation
    have hQ₂ : (fun t => ¬ P t) j₂.val := hP₂
    have hQ₁ : ¬ (fun t => ¬ P t) j₁.val := fun h => h hP₁
    have hne : j₂.val < j₁.val := by
      rcases Nat.lt_or_ge j₂.val j₁.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega) : j₁ = j₂) (fun h => hj₂ (h ▸ hj₁))
    obtain ⟨t, ht, hout, hin⟩ :=
      exists_change (fun t => ¬ P t) (j₁.val - j₂.val) j₂.val hQ₂ (by
        have : j₂.val + (j₁.val - j₂.val) = j₁.val := by omega
        rw [this]; exact hQ₁)
    have hb : j₂.val + t + 1 < r := by omega
    have hb' : j₂.val + t < r := by omega
    obtain ⟨_, hinS⟩ : P (j₂.val + t + 1) := Classical.byContradiction hin
    refine ⟨((i, ⟨j₂.val + t + 1, hb⟩), (i, ⟨j₂.val + t, hb'⟩)), ?_, rfl⟩
    simp only [horizontalBoundary, edgeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hinS, fun hmem => hout ⟨hb', hmem⟩, ?_⟩, trivial⟩
    exact Or.inl ⟨rfl, Or.inr rfl⟩

/-- A partial column carries a vertical boundary edge. -/
theorem exists_vertical_of_partialCol (S : Finset (GridVertex r)) {j : Fin r}
    (hj : j ∈ partialCols S) :
    ∃ p ∈ verticalBoundary S, p.1.2 = j := by
  classical
  simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := hj
  let P : ℕ → Prop := fun t => ∃ h : t < r, (⟨t, h⟩, j) ∈ S
  have hP₁ : P i₁.val := ⟨i₁.isLt, by simpa using hi₁⟩
  have hP₂ : ¬ P i₂.val := by
    rintro ⟨h, hmem⟩
    exact hi₂ (by simpa using hmem)
  rcases Nat.lt_or_ge i₁.val i₂.val with hlt | hge
  · obtain ⟨t, ht, ⟨hlt₁, hin⟩, hout⟩ :=
      exists_change P (i₂.val - i₁.val) i₁.val hP₁ (by
        have : i₁.val + (i₂.val - i₁.val) = i₂.val := by omega
        rw [this]; exact hP₂)
    have hb : i₁.val + t + 1 < r := by omega
    refine ⟨((⟨i₁.val + t, hlt₁⟩, j), (⟨i₁.val + t + 1, hb⟩, j)), ?_, rfl⟩
    simp only [verticalBoundary, edgeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hin, fun hmem => hout ⟨hb, hmem⟩, ?_⟩, trivial⟩
    exact Or.inr ⟨rfl, Or.inl rfl⟩
  · have hQ₂ : (fun t => ¬ P t) i₂.val := hP₂
    have hQ₁ : ¬ (fun t => ¬ P t) i₁.val := fun h => h hP₁
    have hne : i₂.val < i₁.val := by
      rcases Nat.lt_or_ge i₂.val i₁.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega) : i₁ = i₂) (fun h => hi₂ (h ▸ hi₁))
    obtain ⟨t, ht, hout, hin⟩ :=
      exists_change (fun t => ¬ P t) (i₁.val - i₂.val) i₂.val hQ₂ (by
        have : i₂.val + (i₁.val - i₂.val) = i₁.val := by omega
        rw [this]; exact hQ₁)
    have hb : i₂.val + t + 1 < r := by omega
    have hb' : i₂.val + t < r := by omega
    obtain ⟨_, hinS⟩ : P (i₂.val + t + 1) := Classical.byContradiction hin
    refine ⟨((⟨i₂.val + t + 1, hb⟩, j), (⟨i₂.val + t, hb'⟩, j)), ?_, rfl⟩
    simp only [verticalBoundary, edgeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hinS, fun hmem => hout ⟨hb', hmem⟩, ?_⟩, trivial⟩
    exact Or.inr ⟨rfl, Or.inr rfl⟩

/-! ## Counting partial rows and columns -/

/-- Partial rows inject into horizontal boundary edges. -/
theorem card_partialRows_le (S : Finset (GridVertex r)) :
    (partialRows S).card ≤ (horizontalBoundary S).card := by
  classical
  have hsub : partialRows S ⊆ (horizontalBoundary S).image fun p => p.1.1 := by
    intro i hi
    obtain ⟨p, hp, hpi⟩ := exists_horizontal_of_partialRow S hi
    exact Finset.mem_image.2 ⟨p, hp, hpi⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Partial columns inject into vertical boundary edges. -/
theorem card_partialCols_le (S : Finset (GridVertex r)) :
    (partialCols S).card ≤ (verticalBoundary S).card := by
  classical
  have hsub : partialCols S ⊆ (verticalBoundary S).image fun p => p.1.2 := by
    intro j hj
    obtain ⟨p, hp, hpj⟩ := exists_vertical_of_partialCol S hj
    exact Finset.mem_image.2 ⟨p, hp, hpj⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Horizontal and vertical boundary edges are disjoint: an edge in both would
join a vertex to itself. -/
theorem disjoint_horizontal_vertical (S : Finset (GridVertex r)) :
    Disjoint (horizontalBoundary S) (verticalBoundary S) := by
  rw [Finset.disjoint_left]
  intro p hh hv
  simp only [horizontalBoundary, verticalBoundary, edgeBoundary, Finset.mem_filter,
    Finset.mem_univ, true_and] at hh hv
  have heq : p.1 = p.2 := Prod.ext hh.2 hv.2
  exact hh.1.2.1 (heq ▸ hh.1.1)

/-- Both counts together are bounded by the boundary. -/
theorem card_partialRows_add_card_partialCols_le (S : Finset (GridVertex r)) :
    (partialRows S).card + (partialCols S).card ≤ (edgeBoundary S).card := by
  classical
  have h1 := card_partialRows_le S
  have h2 := card_partialCols_le S
  have hunion : (horizontalBoundary S ∪ verticalBoundary S).card ≤ (edgeBoundary S).card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [Finset.card_union_of_disjoint (disjoint_horizontal_vertical S)] at hunion
  omega

/-! ## The isoperimetric inequality -/

/-- A vertex whose row and column are both partial lies in the product of the
partial sets; hence a set of such vertices has at most `a · b` elements. -/
theorem card_le_mul_of_partial (S T : Finset (GridVertex r))
    (h : ∀ v ∈ T, v.1 ∈ partialRows S ∧ v.2 ∈ partialCols S) :
    T.card ≤ (partialRows S).card * (partialCols S).card := by
  classical
  have hsub : T ⊆ partialRows S ×ˢ partialCols S := by
    intro v hv
    exact Finset.mem_product.2 (h v hv)
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product])

/-- **Grid isoperimetry.**  With fewer than `r` boundary edges, one side of the
cut has at most `k²` vertices. -/
theorem card_le_or_compl_card_le (S : Finset (GridVertex r)) {k : ℕ} (hk : k < r)
    (hb : (edgeBoundary S).card ≤ k) :
    S.card ≤ k * k ∨ Sᶜ.card ≤ k * k := by
  classical
  have hsum := card_partialRows_add_card_partialCols_le S
  have ha : (partialRows S).card ≤ k := by omega
  have hbc : (partialCols S).card ≤ k := by omega
  have hmul : (partialRows S).card * (partialCols S).card ≤ k * k :=
    Nat.mul_le_mul ha hbc
  by_cases hrow : ∃ i₀ : Fin r, ∀ j, (i₀, j) ∈ S
  · obtain ⟨i₀, hi₀⟩ := hrow
    by_cases hcol : ∃ j₀ : Fin r, ∀ i, (i, j₀) ∈ S
    · obtain ⟨j₀, hj₀⟩ := hcol
      -- every complement vertex sits at a partial row and a partial column
      refine Or.inr ((card_le_mul_of_partial S Sᶜ ?_).trans hmul)
      intro v hv
      rw [Finset.mem_compl] at hv
      constructor
      · simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨j₀, hj₀ v.1⟩, ⟨v.2, hv⟩⟩
      · simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨i₀, hi₀ v.2⟩, ⟨v.1, hv⟩⟩
    · -- every column is partial, so the boundary has at least `r` edges
      exfalso
      push_neg at hcol
      have hall : partialCols S = Finset.univ := by
        ext j
        simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨⟨i₀, hi₀ j⟩, hcol j⟩
      have := hbc
      rw [hall, Finset.card_univ, Fintype.card_fin] at this
      omega
  · push_neg at hrow
    by_cases hcol : ∃ j₀ : Fin r, ∀ i, (i, j₀) ∈ S
    · exfalso
      obtain ⟨j₀, hj₀⟩ := hcol
      have hall : partialRows S = Finset.univ := by
        ext i
        simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨⟨j₀, hj₀ i⟩, hrow i⟩
      have := ha
      rw [hall, Finset.card_univ, Fintype.card_fin] at this
      omega
    · push_neg at hcol
      refine Or.inl ((card_le_mul_of_partial S S ?_).trans hmul)
      intro v hv
      constructor
      · simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨v.2, hv⟩, hrow v.1⟩
      · simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨v.1, hv⟩, hcol v.2⟩

/-! ## No long bounded chain in a grid -/

/-- A strictly increasing chain of finsets grows by at least one per step. -/
theorem le_card_of_chain {α : Type*} [DecidableEq α] {m : ℕ}
    (S : Fin (m + 1) → Finset α) (hmono : ∀ i j, i < j → S i ⊂ S j) (j : Fin (m + 1)) :
    j.val ≤ (S j).card := by
  induction j using Fin.induction with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have := Finset.card_lt_card (hmono i.castSucc i.succ Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.coe_castSucc] at ih ⊢
      omega

/-- Complements of a strictly increasing chain shrink by at least one per step. -/
theorem le_card_compl_of_chain {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Fin (m + 1) → Finset α) (hmono : ∀ i j, i < j → S i ⊂ S j) (j : Fin (m + 1)) :
    m - j.val ≤ (S j)ᶜ.card := by
  induction j using Fin.reverseInduction with
  | last => simp
  | cast i ih =>
      have hi := i.isLt
      have hlt := Finset.card_lt_card (hmono i.castSucc i.succ Fin.castSucc_lt_succ)
      have h1 := Finset.card_compl (S i.castSucc)
      have h2 := Finset.card_compl (S i.succ)
      have hle1 := Finset.card_le_univ (S i.castSucc)
      have hle2 := Finset.card_le_univ (S i.succ)
      simp only [Fin.val_succ, Fin.coe_castSucc] at ih ⊢
      omega

/-- **A nested chain of bounded cuts in a grid is short.**  If each set has at
most `k < r` boundary edges then the chain has at most `2k² + 1` steps.  The
direct descent needs more than `2^(3^k)`. -/
theorem chain_length_le {m k : ℕ} (hk : k < r)
    (S : Fin (m + 1) → Finset (GridVertex r))
    (hmono : ∀ i j, i < j → S i ⊂ S j)
    (hb : ∀ j, (edgeBoundary (S j)).card ≤ k) :
    m ≤ 2 * (k * k) + 1 := by
  classical
  by_contra hcon
  -- the index just past `k²` is neither small-inside nor small-outside
  have hmid : k * k + 1 < m + 1 := by omega
  rcases card_le_or_compl_card_le (S ⟨k * k + 1, hmid⟩) hk (hb _) with hsmall | hsmall
  · have := le_card_of_chain S hmono ⟨k * k + 1, hmid⟩
    change k * k + 1 ≤ _ at this
    omega
  · have := le_card_compl_of_chain S hmono ⟨k * k + 1, hmid⟩
    change m - (k * k + 1) ≤ _ at this
    omega

/-! ## The descent needs more positions than a grid can supply -/

/-- `2k + 1 ≤ 3^k` for `k ≥ 1`. -/
theorem two_mul_add_one_le_three_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have := ih hn
        rw [Nat.pow_succ]
        omega

/-- `k² < 4^k`. -/
theorem sq_lt_four_pow (k : ℕ) : k * k < 4 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have h4 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      nlinarith [ih, h4]

/-- **The gap.**  For every `k ≥ 1`, `2k² + 1 < 2^(3^k)`: a grid never offers
as many nested bounded cut positions as the pigeonhole on supports demands. -/
theorem two_mul_sq_add_one_lt_two_pow_three_pow {k : ℕ} (hk : 1 ≤ k) :
    2 * (k * k) + 1 < 2 ^ (3 ^ k) := by
  have h1 : 2 ^ (2 * k + 1) ≤ 2 ^ (3 ^ k) :=
    Nat.pow_le_pow_right (by decide) (two_mul_add_one_le_three_pow hk)
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [Nat.pow_succ, Nat.pow_mul]
    have h22 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h22]
    omega
  have h3 := sq_lt_four_pow k
  omega

end GoertzelV24GridIsoperimetry

end Mettapedia.GraphTheory.FourColor
