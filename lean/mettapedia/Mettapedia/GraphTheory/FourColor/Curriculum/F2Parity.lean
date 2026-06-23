import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor.Curriculum

theorem even_of_natCast_f2_eq_zero (n : ℕ) (h : (n : F2) = 0) : Even n := by
  rw [even_iff_two_dvd]
  exact (ZMod.natCast_eq_zero_iff n 2).mp h

theorem list_length_even_of_sum_eq_zero_of_all_one (xs : List F2)
    (h : xs.sum = 0) (h_all_one : ∀ x ∈ xs, x = 1) :
    Even xs.length := by
  have hsum_eq :
      ∀ ys : List F2, (∀ x ∈ ys, x = 1) → ys.sum = (ys.length : F2) := by
    intro ys
    induction ys with
    | nil =>
        intro _hys
        simp
    | cons x xs ih =>
        intro hys
        simp only [List.sum_cons, List.length_cons]
        rw [hys x (by simp)]
        rw [ih]
        · simp only [Nat.cast_add, Nat.cast_one]
          ring
        · intro y hy
          exact hys y (List.mem_cons_of_mem x hy)
  rw [hsum_eq xs h_all_one] at h
  exact even_of_natCast_f2_eq_zero xs.length h

theorem finset_card_even_of_sum_eq_zero_of_all_one {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → F2)
    (h : (∑ a ∈ S, weight a) = 0) (h_all_one : ∀ a ∈ S, weight a = 1) :
    Even S.card := by
  classical
  have hsum_eq :
      ∀ T : Finset α, (∀ a ∈ T, weight a = 1) →
        (∑ a ∈ T, weight a) = (T.card : F2) := by
    intro T
    induction T using Finset.induction with
    | empty =>
        intro _hT
        simp
    | insert a S ha ih =>
        intro hT
        have hS : ∀ b ∈ S, weight b = 1 := fun b hb =>
          hT b (Finset.mem_insert_of_mem hb)
        calc
          ∑ b ∈ insert a S, weight b
              = weight a + ∑ b ∈ S, weight b := by simp [Finset.sum_insert ha]
          _ = 1 + (S.card : F2) := by
                rw [hT a (Finset.mem_insert_self a S), ih hS]
          _ = ((insert a S).card : F2) := by
                simp [Finset.card_insert_of_notMem ha, add_comm]
  rw [hsum_eq S h_all_one] at h
  exact even_of_natCast_f2_eq_zero S.card h

end Mettapedia.GraphTheory.FourColor.Curriculum
