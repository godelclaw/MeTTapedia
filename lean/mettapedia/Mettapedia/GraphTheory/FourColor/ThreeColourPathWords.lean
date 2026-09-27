import Mathlib.Data.Fin.Basic

/-!
# Three-colour words with prescribed ends

The parameter counts adjacent pairs. A word with no adjacent pair forces
equal ends; one adjacent pair forces different ends. With at least two
adjacent pairs, every pair of end colours is possible. The proof extends
words inductively and does not enumerate path lengths.
-/

namespace Mettapedia.GraphTheory.FourColor.ThreeColourPathWords

/-- Only the entries from zero through `n` are constrained. -/
def Admits (n : ℕ) (a b : Fin 3) : Prop :=
  ∃ w : ℕ → Fin 3, w 0 = a ∧ w n = b ∧ ∀ i < n, w i ≠ w (i + 1)

theorem admits_zero_iff (a b : Fin 3) : Admits 0 a b ↔ a = b := by
  constructor
  · rintro ⟨w, ha, hb, _⟩
    exact ha.symm.trans hb
  · intro h
    exact ⟨fun _ => a, rfl, h, by omega⟩

theorem admits_succ_iff (n : ℕ) (a b : Fin 3) :
    Admits (n + 1) a b ↔ ∃ c, a ≠ c ∧ Admits n c b := by
  constructor
  · rintro ⟨w, ha, hb, hnext⟩
    refine ⟨w 1, ?_, fun i => w (i + 1), rfl, hb, ?_⟩
    · simpa only [ha] using hnext 0 (by omega)
    · intro i hi
      exact hnext (i + 1) (by omega)
  · rintro ⟨c, hac, w, hw0, hwn, hnext⟩
    let w' : ℕ → Fin 3
      | 0 => a
      | i + 1 => w i
    refine ⟨w', rfl, hwn, ?_⟩
    intro i hi
    cases i with
    | zero => simpa only [w', hw0] using hac
    | succ i => exact hnext i (by omega)

theorem admits_one_iff (a b : Fin 3) : Admits 1 a b ↔ a ≠ b := by
  rw [show 1 = 0 + 1 from rfl, admits_succ_iff]
  simp only [admits_zero_iff, exists_eq_right]

theorem admits_two (a b : Fin 3) : Admits 2 a b := by
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by decide)
  exact (admits_succ_iff 1 a b).mpr ⟨c, hca.symm, (admits_one_iff c b).mpr hcb⟩

theorem admits_of_two_le {n : ℕ} (hn : 2 ≤ n) (a b : Fin 3) : Admits n a b := by
  induction n generalizing a b with
  | zero => omega
  | succ n ih =>
    by_cases hn1 : n = 1
    · subst n
      exact admits_two a b
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨c, hca, _⟩ := Fin.exists_ne_and_ne_of_two_lt a a (by decide)
      exact (admits_succ_iff n a b).mpr ⟨c, hca.symm, ih hn2 c b⟩

/-- The exact transfer relation of every nonempty three-colour word. -/
theorem admits_iff (n : ℕ) (a b : Fin 3) :
    Admits n a b ↔ (n = 0 ∧ a = b) ∨ (n = 1 ∧ a ≠ b) ∨ 2 ≤ n := by
  cases n with
  | zero => simp [admits_zero_iff]
  | succ n =>
    cases n with
    | zero => simp [admits_one_iff]
    | succ n =>
      constructor
      · intro _
        right
        right
        omega
      · intro _
        exact admits_of_two_le (by omega) a b

end Mettapedia.GraphTheory.FourColor.ThreeColourPathWords
