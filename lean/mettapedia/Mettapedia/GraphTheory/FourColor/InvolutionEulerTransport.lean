import Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect

/-!
# Carrier changes and disjoint unions preserve the Euler bookkeeping

Word orbits of a permutation pair transport along an equivariant bijection
and split over disjoint unions. These are the two carrier changes used by
literal vertex attachment; no planarity premise is involved.
-/

namespace Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect

open Equiv Equiv.Perm GoertzelV24WordReachability
open GoertzelV24InvolutionEdgeList GoertzelV24PermutationOrbitSurgery GoertzelV24OrbitCountCongr

noncomputable section
attribute [local instance] Classical.propDecidable

theorem pair_map {D E : Type*} (f : D → E) (r a : Perm D) (s b : Perm E)
    (hr : ∀ d, f (r d) = s (f d)) (ha : ∀ d, f (a d) = b (f d))
    {x y : D} (h : WordReachable [r, a] x y) : WordReachable [s, b] (f x) (f y) := by
  induction h with
  | refl => exact .refl _ _
  | tail _ ht ih =>
    obtain ⟨g, hg, rfl⟩ := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [hr]; exact ih.trans (wordReachable_step (by simp) _)
    · rw [ha]; exact ih.trans (wordReachable_step (by simp) _)

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

omit [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
theorem pair_congr (e : D ≃ E) (r a : Perm D) (x y : D) :
    WordReachable [e.permCongr r, e.permCongr a] (e x) (e y) ↔
      WordReachable [r, a] x y := by
  constructor
  · intro h
    have hh := pair_map e.symm _ _ r a (by intro d; simp) (by intro d; simp) h
    simpa using hh
  · exact pair_map e r a _ _ (by intro d; simp) (by intro d; simp)

omit [DecidableEq D] [DecidableEq E] in
theorem pair_count_congr (e : D ≃ E) (r a : Perm D) :
    wordOrbitCount [e.permCongr r, e.permCongr a] = wordOrbitCount [r, a] := by
  unfold wordOrbitCount
  exact (Fintype.card_congr (Quotient.congr e (fun x y => (pair_congr e r a x y).symm))).symm

theorem moved_count_congr (e : D ≃ E) (a : Perm D) :
    (movedFinset (e.permCongr a)).card = (movedFinset a).card := by
  have he : movedFinset (e.permCongr a) = (movedFinset a).map e.toEmbedding := by
    ext d
    obtain ⟨x, rfl⟩ := e.surjective d
    simp [movedFinset]
  rw [he, Finset.card_map]

theorem defect_congr (e : D ≃ E) (r a : Perm D) :
    defect (e.permCongr r) (e.permCongr a) = defect r a := by
  have ho (p : Perm D) : orbitCount (e.permCongr p) = orbitCount p :=
    orbitCount_conjEquiv e p
  unfold defect
  rw [moved_count_congr, pair_count_congr, ← Equiv.permCongr_mul]
  rw [ho, ho]

def pairSumLabel (r a : Perm D) (s b : Perm E) :
    D ⊕ E → Quotient (wordSetoid [r, a]) ⊕ Quotient (wordSetoid [s, b]) :=
  Sum.map (Quotient.mk _) (Quotient.mk _)

omit [DecidableEq D] [DecidableEq E] in
theorem pair_sum_label_step (r a : Perm D) (s b : Perm E) (d : D ⊕ E)
    (g : Perm (D ⊕ E)) (hg : g ∈ [Equiv.sumCongr r s, Equiv.sumCongr a b]) :
    pairSumLabel r a s b d = pairSumLabel r a s b (g d) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> rcases d with d | d
  · exact congrArg Sum.inl (Quotient.sound (wordReachable_step (by simp) d))
  · exact congrArg Sum.inr (Quotient.sound (wordReachable_step (by simp) d))
  · exact congrArg Sum.inl (Quotient.sound (wordReachable_step (by simp) d))
  · exact congrArg Sum.inr (Quotient.sound (wordReachable_step (by simp) d))

omit [DecidableEq D] [DecidableEq E] in
theorem pair_sum_label (r a : Perm D) (s b : Perm E) {x y : D ⊕ E}
    (h : WordReachable [Equiv.sumCongr r s, Equiv.sumCongr a b] x y) :
    pairSumLabel r a s b x = pairSumLabel r a s b y := by
  induction h with
  | refl => rfl
  | tail _ ht ih =>
    obtain ⟨g, hg, rfl⟩ := ht
    exact ih.trans (pair_sum_label_step r a s b _ g hg)

omit [DecidableEq D] [DecidableEq E] in
theorem pair_sum_iff (r a : Perm D) (s b : Perm E) (x y : D ⊕ E) :
    WordReachable [Equiv.sumCongr r s, Equiv.sumCongr a b] x y ↔
      pairSumLabel r a s b x = pairSumLabel r a s b y := by
  refine ⟨pair_sum_label r a s b, ?_⟩
  intro h
  rcases x with x | x <;> rcases y with y | y
  · exact pair_map Sum.inl r a _ _ (fun _ => rfl) (fun _ => rfl)
      (Quotient.exact (Sum.inl.inj h))
  · exact (Sum.inl_ne_inr h).elim
  · exact (Sum.inr_ne_inl h).elim
  · exact pair_map Sum.inr s b _ _ (fun _ => rfl) (fun _ => rfl)
      (Quotient.exact (Sum.inr.inj h))

def pairSumEquiv (r a : Perm D) (s b : Perm E) :
    Quotient (wordSetoid [Equiv.sumCongr r s, Equiv.sumCongr a b]) ≃
      Quotient (wordSetoid [r, a]) ⊕ Quotient (wordSetoid [s, b]) :=
  Equiv.ofBijective (Quotient.lift (pairSumLabel r a s b)
    (fun _ _ h => pair_sum_label r a s b h)) (by
      constructor
      · intro x y
        obtain ⟨x, rfl⟩ := Quotient.exists_rep x
        obtain ⟨y, rfl⟩ := Quotient.exists_rep y
        exact fun h => Quotient.sound ((pair_sum_iff r a s b x y).mpr h)
      · rintro (q | q)
        · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
          exact ⟨Quotient.mk _ (.inl x), rfl⟩
        · obtain ⟨y, rfl⟩ := Quotient.exists_rep q
          exact ⟨Quotient.mk _ (.inr y), rfl⟩)

omit [DecidableEq D] [DecidableEq E] in
theorem pair_count_sum (r a : Perm D) (s b : Perm E) :
    wordOrbitCount [Equiv.sumCongr r s, Equiv.sumCongr a b] =
      wordOrbitCount [r, a] + wordOrbitCount [s, b] := by
  unfold wordOrbitCount
  rw [Fintype.card_congr (pairSumEquiv r a s b), Fintype.card_sum]

theorem moved_count_sum (a : Perm D) (b : Perm E) :
    (movedFinset (Equiv.sumCongr a b)).card = (movedFinset a).card + (movedFinset b).card := by
  have he : movedFinset (Equiv.sumCongr a b) = (movedFinset a).disjSum (movedFinset b) := by
    ext d
    rcases d with d | d <;> simp [movedFinset]
  rw [he, Finset.card_disjSum]

theorem defect_sum (r a : Perm D) (s b : Perm E) :
    defect (Equiv.sumCongr r s) (Equiv.sumCongr a b) = defect r a + defect s b := by
  have hp : Equiv.sumCongr r s * Equiv.sumCongr a b = Equiv.sumCongr (r * a) (s * b) := by
    ext d; cases d <;> rfl
  simp only [defect, moved_count_sum, pair_count_sum, hp, orbitCount_sumCongr, Nat.cast_add]
  ring

end
end Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect
