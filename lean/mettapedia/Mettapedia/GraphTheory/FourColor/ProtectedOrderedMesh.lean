import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization
import Mathlib.Data.Finset.Sort

/-!
# Ordered submeshes avoiding a finite edge set

The rows and columns are retained as whole paths, not just their designated
branch vertices. Edge-disjointness within each family bounds the number of
blocked paths. The selected indices preserve their order. No facial-disk,
complete-separator, or colouring-reduction conclusion is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.ProtectedOrderedMesh

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization

noncomputable section
universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] [Fintype E]
  {g : Multigraph V E} {a b p q : Nat}

def blocked {n : Nat} (paths : Fin n → MeshPath g) (F : Finset E) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ t, (paths i).edge t ∈ F

theorem card_blocked_le {n : Nat} (paths : Fin n → MeshPath g)
    (hd : ∀ i j, i ≠ j → ∀ t t', (paths i).edge t ≠ (paths j).edge t')
    (F : Finset E) : (blocked paths F).card ≤ F.card := by
  classical
  have hex (i : blocked paths F) : ∃ t, (paths i.1).edge t ∈ F := by
    simpa only [blocked, Finset.mem_filter, Finset.mem_univ, true_and] using i.2
  let f : blocked paths F → F := fun i =>
    ⟨(paths i.1).edge (hex i).choose, (hex i).choose_spec⟩
  have hinj : Function.Injective f := by
    intro i j heq
    apply Subtype.ext
    by_contra hne
    exact hd i.1 j.1 hne _ _ (congrArg Subtype.val heq)
  simpa using Fintype.card_le_of_injective f hinj

theorem exists_clean_indices {n m : Nat} (paths : Fin n → MeshPath g)
    (hd : ∀ i j, i ≠ j → ∀ t t', (paths i).edge t ≠ (paths j).edge t')
    (F : Finset E) (hsize : m + F.card ≤ n) :
    ∃ r : Fin m ↪o Fin n, ∀ i t, (paths (r i)).edge t ∉ F := by
  classical
  let bad := blocked paths F
  let good := Finset.univ \ bad
  have hb : bad.card ≤ F.card := card_blocked_le paths hd F
  have hbal : good.card + bad.card = n := by
    simpa [good] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  have hg : m ≤ good.card := by omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hg
  refine ⟨s.orderEmbOfFin hcard, ?_⟩
  intro i t hmem
  have hgood := hs (s.orderEmbOfFin_mem hcard i)
  have hnot := (Finset.mem_sdiff.mp hgood).2
  apply hnot
  simp only [bad, blocked, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t, hmem⟩

/-- Keep the literal paths while restricting the two ordered index sets. -/
def restrict (M : OrderedInjectiveMesh g a b)
    (r : Fin p ↪o Fin a) (c : Fin q ↪o Fin b) : OrderedInjectiveMesh g p q where
  toMesh := {
    row := fun i => M.toMesh.row (r i)
    col := fun j => M.toMesh.col (c j)
    branch := fun i j => M.toMesh.branch (r i) (c j)
    branch_mem_row := fun i j => M.toMesh.branch_mem_row (r i) (c j)
    branch_mem_col := fun i j => M.toMesh.branch_mem_col (r i) (c j)
    row_edges_disjoint := fun i j h => M.toMesh.row_edges_disjoint (r i) (r j)
      (fun heq => h (r.injective heq))
    col_edges_disjoint := fun i j h => M.toMesh.col_edges_disjoint (c i) (c j)
      (fun heq => h (c.injective heq)) }
  rowVertexInjective := fun i => M.rowVertexInjective (r i)
  colVertexInjective := fun j => M.colVertexInjective (c j)
  branchInjective := by
    intro s t h
    have heq := @M.branchInjective (r s.1, c s.2) (r t.1, c t.2) h
    exact Prod.ext (r.injective (congrArg Prod.fst heq))
      (c.injective (congrArg Prod.snd heq))
  rowBranchPosition := fun i j => M.rowBranchPosition (r i) (c j)
  colBranchPosition := fun i j => M.colBranchPosition (r i) (c j)
  rowBranchPosition_spec := fun i j => M.rowBranchPosition_spec (r i) (c j)
  colBranchPosition_spec := fun i j => M.colBranchPosition_spec (r i) (c j)
  rowBranchPosition_strictMono := fun i =>
    (M.rowBranchPosition_strictMono (r i)).comp c.strictMono
  colBranchPosition_strictMono := fun j =>
    (M.colBranchPosition_strictMono (c j)).comp r.strictMono

def AvoidsEdges (M : OrderedInjectiveMesh g a b) (F : Finset E) : Prop :=
  (∀ i t, (M.toMesh.row i).edge t ∉ F) ∧
  (∀ j t, (M.toMesh.col j).edge t ∉ F)

theorem exists_restriction_avoiding_edges (M : OrderedInjectiveMesh g a b)
    (F : Finset E) (ha : p + F.card ≤ a) (hb : q + F.card ≤ b) :
    ∃ (r : Fin p ↪o Fin a) (c : Fin q ↪o Fin b), AvoidsEdges (restrict M r c) F := by
  obtain ⟨r, hr⟩ := exists_clean_indices M.toMesh.row M.toMesh.row_edges_disjoint F ha
  obtain ⟨c, hc⟩ := exists_clean_indices M.toMesh.col M.toMesh.col_edges_disjoint F hb
  exact ⟨r, c, hr, hc⟩

def starEdges (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => g.fst e ∈ S ∨ g.snd e ∈ S

def AvoidsVertices (M : OrderedInjectiveMesh g a b) (S : Finset V) : Prop :=
  (∀ i t, (M.toMesh.row i).vert t ∉ S) ∧
  (∀ j t, (M.toMesh.col j).vert t ∉ S)

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem path_vertex_incident (P : MeshPath g) (hp : 0 < P.len)
    (t : Fin (P.len + 1)) :
    ∃ s, g.fst (P.edge s) = P.vert t ∨ g.snd (P.edge s) = P.vert t := by
  by_cases ht : t.val < P.len
  · let s : Fin P.len := ⟨t.val, ht⟩
    have heq : s.castSucc = t := Fin.ext rfl
    rcases P.edge_ends s with h | h
    · exact ⟨s, Or.inl (h.1.trans (congrArg P.vert heq))⟩
    · exact ⟨s, Or.inr (h.2.trans (congrArg P.vert heq))⟩
  · let s : Fin P.len := ⟨P.len - 1, by omega⟩
    have heq : s.succ = t := Fin.ext (by dsimp [s]; omega)
    rcases P.edge_ends s with h | h
    · exact ⟨s, Or.inr (h.2.trans (congrArg P.vert heq))⟩
    · exact ⟨s, Or.inl (h.1.trans (congrArg P.vert heq))⟩

theorem row_len_pos (M : OrderedInjectiveMesh g a b) (hb : 2 ≤ b) (i : Fin a) :
    0 < (M.toMesh.row i).len := by
  have h := M.rowBranchPosition_strictMono i
    (show (⟨0, by omega⟩ : Fin b) < ⟨1, by omega⟩ from by change (0 : Nat) < 1; omega)
  have hl := (M.rowBranchPosition i ⟨1, by omega⟩).isLt
  change (M.rowBranchPosition i ⟨0, by omega⟩).val <
    (M.rowBranchPosition i ⟨1, by omega⟩).val at h
  omega

theorem col_len_pos (M : OrderedInjectiveMesh g a b) (ha : 2 ≤ a) (j : Fin b) :
    0 < (M.toMesh.col j).len := by
  have h := M.colBranchPosition_strictMono j
    (show (⟨0, by omega⟩ : Fin a) < ⟨1, by omega⟩ from by change (0 : Nat) < 1; omega)
  have hl := (M.colBranchPosition ⟨1, by omega⟩ j).isLt
  change (M.colBranchPosition ⟨0, by omega⟩ j).val <
    (M.colBranchPosition ⟨1, by omega⟩ j).val at h
  omega

theorem avoids_vertices_of_avoids_star (M : OrderedInjectiveMesh g a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (S : Finset V)
    (h : AvoidsEdges M (starEdges (g := g) S)) : AvoidsVertices M S := by
  have key (P : MeshPath g) (hp : 0 < P.len)
      (hn : ∀ t, P.edge t ∉ starEdges (g := g) S) :
      ∀ t, P.vert t ∉ S := by
    intro t ht
    obtain ⟨s, hs⟩ := path_vertex_incident P hp t
    apply hn s
    simp only [starEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs with hs | hs
    · exact Or.inl (hs ▸ ht)
    · exact Or.inr (hs ▸ ht)
  exact ⟨fun i => key _ (row_len_pos M hb i) (h.1 i),
    fun j => key _ (col_len_pos M ha j) (h.2 j)⟩

/-- A whole ordered path carrier disjoint from the forbidden vertices.
The loss in each dimension is the number of ambient incident edges. -/
theorem exists_restriction_avoiding_vertices (M : OrderedInjectiveMesh g a b)
    (S : Finset V) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (ha : p + (starEdges (g := g) S).card ≤ a)
    (hb : q + (starEdges (g := g) S).card ≤ b) :
    ∃ (r : Fin p ↪o Fin a) (c : Fin q ↪o Fin b),
      AvoidsVertices (restrict M r c) S := by
  obtain ⟨r, c, h⟩ := exists_restriction_avoiding_edges M (starEdges (g := g) S) ha hb
  exact ⟨r, c, avoids_vertices_of_avoids_star _ hp hq S h⟩

end
end Mettapedia.GraphTheory.FourColor.ProtectedOrderedMesh
