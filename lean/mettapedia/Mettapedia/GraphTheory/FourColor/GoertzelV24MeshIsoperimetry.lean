import Mettapedia.GraphTheory.FourColor.GoertzelV24GridIsoperimetry
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryEssentialGluing

/-!
# Mesh isoperimetry: the wall obstruction on the real object

The grid theorem is stated on an abstract grid.  What the grid-minor theorem
supplies inside a cubic graph is a *subdivided wall*: `r` horizontal paths and
`r` vertical paths, internally disjoint, with a branch vertex wherever a row
meets a column — and arbitrary further material attached anywhere.  The
isoperimetric argument only ever used the rows, the columns and the branch
vertices, so it transfers verbatim to that object.

A *mesh* is exactly those data: a family of row paths, a family of column paths,
edge-disjoint within each family, and a branch vertex on every row–column pair.
Nothing is assumed about the rest of the graph.  A vertex set with at most
`k < min(a, b)` boundary edges then has a side containing at most `k²` branch
vertices, and a nested chain of bounded cuts moves the branch set at most
`2k² + 1` times.

That is the precise obstruction for case (B) of the branchwidth dichotomy.  A
long chain of bounded nested cuts can exist in a graph with a large wall — but
only if its slabs avoid the wall's branch vertices, i.e. only if the chain lives
in a tube hanging off the wall.  The wall itself offers no cut positions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MeshIsoperimetry

open GoertzelV24GridIsoperimetry (exists_change)
open GoertzelV24BoundaryEssentialGluing

variable {Vtx Edg : Type*} [DecidableEq Vtx] [DecidableEq Edg] [Fintype Edg]

/-- A path in a multigraph, presented by its vertex sequence and the edges
joining consecutive vertices. -/
structure MeshPath (g : Multigraph Vtx Edg) where
  len : ℕ
  vert : Fin (len + 1) → Vtx
  edge : Fin len → Edg
  edge_ends : ∀ t : Fin len,
    (g.fst (edge t) = vert t.castSucc ∧ g.snd (edge t) = vert t.succ) ∨
      (g.fst (edge t) = vert t.succ ∧ g.snd (edge t) = vert t.castSucc)

/-- An edge with exactly one end in `S`. -/
def IsBoundaryEdge (g : Multigraph Vtx Edg) (S : Finset Vtx) (e : Edg) : Prop :=
  (g.fst e ∈ S ∧ g.snd e ∉ S) ∨ (g.fst e ∉ S ∧ g.snd e ∈ S)

instance (g : Multigraph Vtx Edg) (S : Finset Vtx) (e : Edg) :
    Decidable (IsBoundaryEdge g S e) := by unfold IsBoundaryEdge; infer_instance

/-- The boundary of `S`. -/
def boundaryEdges (g : Multigraph Vtx Edg) (S : Finset Vtx) : Finset Edg :=
  Finset.univ.filter (IsBoundaryEdge g S)

/-- **A path with one end in `S` and one out crosses the boundary.** -/
theorem MeshPath.exists_boundary_edge {g : Multigraph Vtx Edg} (p : MeshPath g)
    (S : Finset Vtx) {s s' : Fin (p.len + 1)}
    (hs : p.vert s ∈ S) (hs' : p.vert s' ∉ S) :
    ∃ t : Fin p.len, IsBoundaryEdge g S (p.edge t) := by
  classical
  let P : ℕ → Prop := fun n => ∃ h : n < p.len + 1, p.vert ⟨n, h⟩ ∈ S
  have hP : P s.val := ⟨s.isLt, by simpa using hs⟩
  have hP' : ¬ P s'.val := by
    rintro ⟨h, hmem⟩
    exact hs' (by simpa using hmem)
  -- a boundary edge sits where the status changes along the path
  have key : ∀ n : ℕ, n < p.len → P n → ¬ P (n + 1) →
      ∃ t : Fin p.len, IsBoundaryEdge g S (p.edge t) := by
    intro n hn ⟨_, hin⟩ hout
    refine ⟨⟨n, hn⟩, ?_⟩
    have hout' : p.vert ⟨n + 1, by omega⟩ ∉ S := fun hmem => hout ⟨by omega, hmem⟩
    rcases p.edge_ends ⟨n, hn⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1]; exact hin, by rw [h2]; exact hout'⟩
    · exact Or.inr ⟨by rw [h1]; exact hout', by rw [h2]; exact hin⟩
  have key' : ∀ n : ℕ, n < p.len → ¬ P n → P (n + 1) →
      ∃ t : Fin p.len, IsBoundaryEdge g S (p.edge t) := by
    intro n hn hout ⟨_, hin⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    have hout' : p.vert ⟨n, by omega⟩ ∉ S := fun hmem => hout ⟨by omega, hmem⟩
    rcases p.edge_ends ⟨n, hn⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by rw [h1]; exact hout', by rw [h2]; exact hin⟩
    · exact Or.inl ⟨by rw [h1]; exact hin, by rw [h2]; exact hout'⟩
  rcases Nat.lt_or_ge s.val s'.val with hlt | hge
  · obtain ⟨t, ht, h1, h2⟩ := exists_change P (s'.val - s.val) s.val hP (by
      have : s.val + (s'.val - s.val) = s'.val := by omega
      rw [this]; exact hP')
    exact key (s.val + t) (by omega) h1 h2
  · have hne : s'.val < s.val := by
      rcases Nat.lt_or_ge s'.val s.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega) : s = s') (fun h => hs' (h ▸ hs))
    obtain ⟨t, ht, h1, h2⟩ := exists_change (fun n => ¬ P n) (s.val - s'.val) s'.val hP' (by
      have : s'.val + (s.val - s'.val) = s.val := by omega
      rw [this]; exact fun h => h hP)
    exact key' (s'.val + t) (by omega) h1 (Classical.byContradiction h2)

/-- **A mesh**: rows, columns, and a branch vertex on every row–column pair.
Only edge-disjointness within each family is required. -/
structure Mesh (g : Multigraph Vtx Edg) (a b : ℕ) where
  row : Fin a → MeshPath g
  col : Fin b → MeshPath g
  branch : Fin a → Fin b → Vtx
  branch_mem_row : ∀ i j, ∃ t, (row i).vert t = branch i j
  branch_mem_col : ∀ i j, ∃ t, (col j).vert t = branch i j
  row_edges_disjoint : ∀ i i', i ≠ i' → ∀ t t', (row i).edge t ≠ (row i').edge t'
  col_edges_disjoint : ∀ j j', j ≠ j' → ∀ t t', (col j).edge t ≠ (col j').edge t'

namespace Mesh

variable {g : Multigraph Vtx Edg} {a b : ℕ} (M : Mesh g a b) (S : Finset Vtx)

/-- Rows whose branch vertices meet both `S` and its complement. -/
def partialRows : Finset (Fin a) :=
  Finset.univ.filter fun i => (∃ j, M.branch i j ∈ S) ∧ ∃ j, M.branch i j ∉ S

/-- Columns whose branch vertices meet both `S` and its complement. -/
def partialCols : Finset (Fin b) :=
  Finset.univ.filter fun j => (∃ i, M.branch i j ∈ S) ∧ ∃ i, M.branch i j ∉ S

/-- A partial row carries a boundary edge of its own. -/
theorem exists_row_boundary {i : Fin a} (hi : i ∈ M.partialRows S) :
    ∃ t, IsBoundaryEdge g S ((M.row i).edge t) := by
  simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩ := hi
  obtain ⟨t₁, ht₁⟩ := M.branch_mem_row i j₁
  obtain ⟨t₂, ht₂⟩ := M.branch_mem_row i j₂
  exact (M.row i).exists_boundary_edge S (ht₁ ▸ hj₁) (ht₂ ▸ hj₂)

theorem exists_col_boundary {j : Fin b} (hj : j ∈ M.partialCols S) :
    ∃ t, IsBoundaryEdge g S ((M.col j).edge t) := by
  simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := hj
  obtain ⟨t₁, ht₁⟩ := M.branch_mem_col i₁ j
  obtain ⟨t₂, ht₂⟩ := M.branch_mem_col i₂ j
  exact (M.col j).exists_boundary_edge S (ht₁ ▸ hi₁) (ht₂ ▸ hi₂)

/-- Partial rows inject into boundary edges. -/
theorem card_partialRows_le [Nonempty Edg] :
    (M.partialRows S).card ≤ (boundaryEdges g S).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun i => if h : i ∈ M.partialRows S then
      (M.row i).edge (M.exists_row_boundary S h).choose else Classical.arbitrary Edg) ?_ ?_
  · intro i hi
    have hi' : i ∈ M.partialRows S := Finset.mem_coe.1 hi
    simp only [boundaryEdges, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dif_pos hi']
    exact (M.exists_row_boundary S hi').choose_spec
  · intro i hi i' hi' heq
    have hi₁ : i ∈ M.partialRows S := Finset.mem_coe.1 hi
    have hi₂ : i' ∈ M.partialRows S := Finset.mem_coe.1 hi'
    dsimp only at heq
    rw [dif_pos hi₁, dif_pos hi₂] at heq
    by_contra hne
    exact M.row_edges_disjoint i i' hne _ _ heq

theorem card_partialCols_le [Nonempty Edg] :
    (M.partialCols S).card ≤ (boundaryEdges g S).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun j => if h : j ∈ M.partialCols S then
      (M.col j).edge (M.exists_col_boundary S h).choose else Classical.arbitrary Edg) ?_ ?_
  · intro j hj
    have hj' : j ∈ M.partialCols S := Finset.mem_coe.1 hj
    simp only [boundaryEdges, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dif_pos hj']
    exact (M.exists_col_boundary S hj').choose_spec
  · intro j hj j' hj' heq
    have hj₁ : j ∈ M.partialCols S := Finset.mem_coe.1 hj
    have hj₂ : j' ∈ M.partialCols S := Finset.mem_coe.1 hj'
    dsimp only at heq
    rw [dif_pos hj₁, dif_pos hj₂] at heq
    by_contra hne
    exact M.col_edges_disjoint j j' hne _ _ heq

/-- The branch positions inside `S`. -/
def branchIn : Finset (Fin a × Fin b) :=
  Finset.univ.filter fun p => M.branch p.1 p.2 ∈ S

/-- The branch positions outside `S`. -/
def branchOut : Finset (Fin a × Fin b) :=
  Finset.univ.filter fun p => M.branch p.1 p.2 ∉ S

theorem card_le_mul_of_partial (T : Finset (Fin a × Fin b))
    (h : ∀ p ∈ T, p.1 ∈ M.partialRows S ∧ p.2 ∈ M.partialCols S) :
    T.card ≤ (M.partialRows S).card * (M.partialCols S).card := by
  classical
  have hsub : T ⊆ M.partialRows S ×ˢ M.partialCols S := fun p hp =>
    Finset.mem_product.2 (h p hp)
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product])

/-- **Mesh isoperimetry.**  A cut with fewer boundary edges than the mesh has
rows and columns leaves at most `k²` branch vertices on one side. -/
theorem branchIn_card_le_or_branchOut_card_le [Nonempty Edg] {k : ℕ}
    (hka : k < a) (hkb : k < b) (hb : (boundaryEdges g S).card ≤ k) :
    (M.branchIn S).card ≤ k * k ∨ (M.branchOut S).card ≤ k * k := by
  classical
  have ha : (M.partialRows S).card ≤ k := (M.card_partialRows_le S).trans hb
  have hbc : (M.partialCols S).card ≤ k := (M.card_partialCols_le S).trans hb
  have hmul : (M.partialRows S).card * (M.partialCols S).card ≤ k * k :=
    Nat.mul_le_mul ha hbc
  by_cases hrow : ∃ i₀ : Fin a, ∀ j, M.branch i₀ j ∈ S
  · obtain ⟨i₀, hi₀⟩ := hrow
    by_cases hcol : ∃ j₀ : Fin b, ∀ i, M.branch i j₀ ∈ S
    · obtain ⟨j₀, hj₀⟩ := hcol
      refine Or.inr ((M.card_le_mul_of_partial S _ ?_).trans hmul)
      intro p hp
      simp only [branchOut, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      constructor
      · simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨j₀, hj₀ p.1⟩, ⟨p.2, hp⟩⟩
      · simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨i₀, hi₀ p.2⟩, ⟨p.1, hp⟩⟩
    · exfalso
      push_neg at hcol
      have hall : M.partialCols S = Finset.univ := by
        ext j
        simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨⟨i₀, hi₀ j⟩, hcol j⟩
      have := hbc
      rw [hall, Finset.card_univ, Fintype.card_fin] at this
      omega
  · push_neg at hrow
    by_cases hcol : ∃ j₀ : Fin b, ∀ i, M.branch i j₀ ∈ S
    · exfalso
      obtain ⟨j₀, hj₀⟩ := hcol
      have hall : M.partialRows S = Finset.univ := by
        ext i
        simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨⟨j₀, hj₀ i⟩, hrow i⟩
      have := ha
      rw [hall, Finset.card_univ, Fintype.card_fin] at this
      omega
    · push_neg at hcol
      refine Or.inl ((M.card_le_mul_of_partial S _ ?_).trans hmul)
      intro p hp
      simp only [branchIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      constructor
      · simp only [partialRows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨p.2, hp⟩, hrow p.1⟩
      · simp only [partialCols, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨p.1, hp⟩, hcol p.2⟩

/-- `branchIn` and `branchOut` partition the positions. -/
theorem card_branchIn_add_card_branchOut :
    (M.branchIn S).card + (M.branchOut S).card = a * b := by
  classical
  have := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin a × Fin b))) (fun p => M.branch p.1 p.2 ∈ S)
  simpa [branchIn, branchOut, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using this

/-- **The chain obstruction on a mesh.**  A nested chain of bounded cuts whose
branch sets strictly grow has at most `2k² + 1` steps. -/
theorem chain_length_le [Nonempty Edg] {m k : ℕ} (hka : k < a) (hkb : k < b)
    (Ss : Fin (m + 1) → Finset Vtx)
    (hmono : ∀ i j, i < j → M.branchIn (Ss i) ⊂ M.branchIn (Ss j))
    (hbd : ∀ j, (boundaryEdges g (Ss j)).card ≤ k) :
    m ≤ 2 * (k * k) + 1 := by
  classical
  by_contra hcon
  have hmid : k * k + 1 < m + 1 := by omega
  rcases M.branchIn_card_le_or_branchOut_card_le (Ss ⟨k * k + 1, hmid⟩) hka hkb (hbd _)
    with hsmall | hsmall
  · have := GoertzelV24GridIsoperimetry.le_card_of_chain
      (fun t => M.branchIn (Ss t)) hmono ⟨k * k + 1, hmid⟩
    change k * k + 1 ≤ _ at this
    omega
  · -- the outside count is the complement count
    have hpart := M.card_branchIn_add_card_branchOut (Ss ⟨k * k + 1, hmid⟩)
    have hcompl := GoertzelV24GridIsoperimetry.le_card_compl_of_chain
      (fun t => M.branchIn (Ss t)) hmono ⟨k * k + 1, hmid⟩
    change m - (k * k + 1) ≤ _ at hcompl
    rw [Finset.card_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcompl
    omega

end Mesh

end GoertzelV24MeshIsoperimetry

end Mettapedia.GraphTheory.FourColor
