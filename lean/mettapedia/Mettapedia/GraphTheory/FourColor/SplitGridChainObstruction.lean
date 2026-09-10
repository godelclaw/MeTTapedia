import Mettapedia.GraphTheory.FourColor.SplitGridMesh

/-!
# No width makes generic support pigeonholing work on split grids

The bound concerns every strictly nested chain of complete vertex sets,
not only chains whose designated branch sets strictly grow. Matching
edges charge the extra partner vertices to the complete cut. The result
holds for all mesh sizes and all widths. It does not assert that supports
cannot repeat earlier, or refute a reduction using non-colourability.
-/

namespace Mettapedia.GraphTheory.FourColor.SplitGridMesh

open GoertzelV24MeshIsoperimetry GoertzelV24GridIsoperimetry

variable {n : Nat}

def selected (S : Finset (Vertex n)) : Finset (Position n) :=
  Finset.univ.filter fun p => (p, 0) ∈ S

def extra (S : Finset (Vertex n)) : Finset (Position n) :=
  Finset.univ.filter fun p => (p, 0) ∉ S ∧ (p, 1) ∈ S

theorem extra_card_le_cut (S : Finset (Vertex n)) :
    (extra S).card ≤ (boundaryEdges (graph n) S).card := by
  have hsub : (extra S).image (fun p => (Sum.inl p : Edge n)) ⊆
      boundaryEdges (graph n) S := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    simp only [extra, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hp⟩
  calc
    (extra S).card = ((extra S).image (fun p => (Sum.inl p : Edge n))).card :=
      (Finset.card_image_of_injective _ Sum.inl_injective).symm
    _ ≤ (boundaryEdges (graph n) S).card := Finset.card_le_card hsub

/-- Charge each unselected-branch partner to its own crossing matching edge. -/
theorem card_le_twice_selected_add_cut (S : Finset (Vertex n)) :
    S.card ≤ 2 * (selected S).card + (boundaryEdges (graph n) S).card := by
  have hsub : S ⊆ (selected S ×ˢ Finset.univ) ∪ (extra S ×ˢ {1}) := by
    rintro ⟨p, b⟩ hv
    fin_cases b
    · apply Finset.mem_union_left
      simp [selected]
      exact hv
    · by_cases hp : (p, (0 : Fin 2)) ∈ S
      · apply Finset.mem_union_left
        simp [selected, hp]
      · apply Finset.mem_union_right
        simp [extra, hp]
        exact hv
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have he := extra_card_le_cut S
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_singleton, Nat.mul_one] at hc
  omega

theorem boundary_compl (S : Finset (Vertex n)) :
    boundaryEdges (graph n) Sᶜ = boundaryEdges (graph n) S := by
  ext e
  simp only [boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    IsBoundaryEdge, Finset.mem_compl, not_not]
  tauto

/-- This is a full-vertex bound, with no branch-growth assumption. -/
theorem small_side_of_cut (S : Finset (Vertex n)) {k : Nat} (hk : k < n + 1)
    (hcut : (boundaryEdges (graph n) S).card ≤ k) :
    S.card ≤ 2 * (k * k) + k ∨ Sᶜ.card ≤ 2 * (k * k) + k := by
  have hi := card_le_twice_selected_add_cut S
  have ho := card_le_twice_selected_add_cut Sᶜ
  rw [boundary_compl] at ho
  rcases (mesh n).branchIn_card_le_or_branchOut_card_le S hk hk hcut with hin | hout
  · have hs : (selected S).card ≤ k * k := hin
    exact Or.inl (by omega)
  · have hs : (selected Sᶜ).card ≤ k * k := by
      simpa only [selected, Mesh.branchOut, mesh, Finset.mem_compl] using hout
    exact Or.inr (by omega)

/-- Every cut width, every mesh size, and every strictly nested chain. -/
theorem full_chain_length_le {m k : Nat}
    (S : Fin (m + 1) → Finset (Vertex n))
    (hmono : ∀ i j, i < j → S i ⊂ S j)
    (hcut : ∀ i, (boundaryEdges (graph n) (S i)).card ≤ k) :
    m ≤ 4 * (k * k) + 2 * k + 1 := by
  by_cases hk : k < n + 1
  · by_contra hfail
    let b := 2 * (k * k) + k
    have hmid : b + 1 < m + 1 := by dsimp [b]; omega
    let mid : Fin (m + 1) := ⟨b + 1, hmid⟩
    rcases small_side_of_cut (S mid) hk (hcut mid) with hs | hs
    · have hg := le_card_of_chain S hmono mid
      dsimp [mid, b] at hg hs
      omega
    · have hg := le_card_compl_of_chain S hmono mid
      dsimp [mid, b] at hg hs
      omega
  · have hg := (le_card_of_chain S hmono (Fin.last m)).trans (Finset.card_le_univ _)
    rw [vertex_card] at hg
    have hn : n + 1 ≤ k := by omega
    have hsq := Nat.mul_le_mul hn hn
    change m ≤ _ at hg
    omega

theorem polynomial_lt_support_carrier {k : Nat} (hk : 1 ≤ k) :
    4 * (k * k) + 2 * k + 1 < 2 ^ (3 ^ k) := by
  have hpoly : ∀ t : Nat, 1 ≤ t → 4 * (t * t) + 2 * t + 1 < 2 * 4 ^ t := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      intro ht
      by_cases hz : t = 0
      · subst t; norm_num
      · have hi := ih (by omega)
        rw [pow_succ]
        nlinarith
  have hexp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (two_mul_add_one_le_three_pow hk)
  have heq : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    omega
  rw [heq] at hexp
  exact (hpoly k hk).trans_le hexp

/-- Choosing a larger grid OR a different positive width cannot reach the
generic full-support pigeonhole threshold in this family. This does not
rule out earlier support repetition or non-pumping reductions. -/
theorem no_full_support_pigeonhole_chain {m k : Nat} (hk : 1 ≤ k)
    (S : Fin (m + 1) → Finset (Vertex n))
    (hmono : ∀ i j, i < j → S i ⊂ S j)
    (hcut : ∀ i, (boundaryEdges (graph n) (S i)).card ≤ k) :
    m < 2 ^ (3 ^ k) :=
  (full_chain_length_le S hmono hcut).trans_lt (polynomial_lt_support_carrier hk)

/-- At width five even the number of sets, rather than inclusions, is at
most 112. No admissibility constraints were needed to get this upper bound. -/
theorem width_five_chain_sets {m : Nat}
    (S : Fin (m + 1) → Finset (Vertex n))
    (hmono : ∀ i j, i < j → S i ⊂ S j)
    (hcut : ∀ i, (boundaryEdges (graph n) (S i)).card ≤ 5) :
    m + 1 ≤ 112 := by
  have h := full_chain_length_le S hmono hcut
  omega

/-- No largeness threshold repairs generic support pigeonholing on this
explicit family, even when an actual ordered mesh is included in the output. -/
theorem arbitrarily_large_no_full_support_chain (N k : Nat) (hk : 1 ≤ k) :
    ∃ n, N < Fintype.card (Vertex n) ∧
      Nonempty (GoertzelV24OrderedInjectiveMeshWidthFactorization.OrderedInjectiveMesh
        (graph n) (n + 1) (n + 1)) ∧
      ¬ ∃ (m : Nat) (S : Fin (m + 1) → Finset (Vertex n)),
        (∀ i j, i < j → S i ⊂ S j) ∧
        (∀ i, (boundaryEdges (graph n) (S i)).card ≤ k) ∧
        2 ^ (3 ^ k) ≤ m := by
  refine ⟨N, ?_, ⟨ordered N⟩, ?_⟩
  · rw [vertex_card]
    nlinarith [Nat.zero_le (N * N)]
  · rintro ⟨m, S, hmono, hcut, hlong⟩
    exact Nat.not_le_of_lt (no_full_support_pigeonhole_chain hk S hmono hcut) hlong

end Mettapedia.GraphTheory.FourColor.SplitGridMesh
