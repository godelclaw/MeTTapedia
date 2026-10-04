import MettapediaFourColor.KempeMatchingReconstruction

/-!
# Interval exclusion for adaptive chord choice

An unsuccessful set of chord choices can be tested by its interval
decomposition. If it admits no noncrossing matching, every actual
noncrossing exterior has a successful chord. Fixed ports are retained.
The statement is uniform in boundary length and does not enumerate
exterior matchings.
-/

namespace FourColor.KempeIntervalMatching

open Mettapedia.GraphTheory.NoncrossingMatchingStack

/-- Whether an interval admits a matching using only the permitted pairs.
Inactive ports are fixed; active ports must have a distinct partner. -/
def possible (active : ℕ → Bool) (bad : ℕ → ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 =>
    if active lo then
      (List.finRange n).any fun k =>
        bad lo (lo + k.val + 1) && active (lo + k.val + 1) &&
          possible active bad (lo + 1) k.val &&
          possible active bad (lo + k.val + 2) (n - k.val - 1)
    else possible active bad (lo + 1) n
termination_by _lo n => n
decreasing_by all_goals omega

/-- A matching restricted to one interval has no unmatched outgoing ends. -/
def Closed (mate : ℕ → ℕ) (lo n : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < lo + n → lo ≤ mate i ∧ mate i < lo + n

theorem possible_of_matching (mate : ℕ → ℕ)
    (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (active : ℕ → Bool) (bad : ℕ → ℕ → Bool) (lo n : ℕ)
    (closed : Closed mate lo n)
    (fixed : ∀ i, lo ≤ i → i < lo + n → (mate i = i ↔ active i = false))
    (failed : ∀ i, lo ≤ i → i < lo + n → active i = true → bad i (mate i) = true) :
    possible active bad lo n = true := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    cases n with
    | zero => simp [possible]
    | succ n =>
      cases ha : active lo with
      | false =>
        have hself : mate lo = lo := (fixed lo (by omega) (by omega)).mpr ha
        have tail : Closed mate (lo + 1) n := by
          intro i hlo hhi
          have h := closed i (by omega) (by omega)
          have ne : mate i ≠ lo := by
            intro he
            have := hinv.injective (he.trans hself.symm)
            omega
          constructor <;> omega
        simpa only [possible, ha, Bool.false_eq_true, ↓reduceIte] using
          ih n (by omega) (lo + 1) tail
            (fun i hlo hhi => fixed i (by omega) (by omega))
            (fun i hlo hhi => failed i (by omega) (by omega))
      | true =>
        have hb := closed lo (by omega) (by omega)
        have hne : mate lo ≠ lo := by
          intro he
          have := (fixed lo (by omega) (by omega)).mp he
          simp_all
        have hlt : lo < mate lo := by omega
        have hba : active (mate lo) = true := by
          cases he : active (mate lo) with
          | true => rfl
          | false =>
            have hs := (fixed (mate lo) hb.1 hb.2).mpr he
            rw [hinv] at hs
            omega
        let k : Fin n := ⟨mate lo - lo - 1, by omega⟩
        have hk : lo + k.val + 1 = mate lo := by dsimp [k]; omega
        have left : Closed mate (lo + 1) k.val := by
          intro i hlo hhi
          have h := closed i (by omega) (by omega)
          have ne₀ : mate i ≠ lo := by
            intro he
            have hi := congrArg mate he
            rw [hinv] at hi
            omega
          have ne₁ : mate i ≠ mate lo := by
            intro he
            have := hinv.injective he
            omega
          have top : mate i ≤ mate lo := by
            by_contra hg
            exact hnc lo i (by omega) (by omega) (by omega)
          constructor <;> omega
        have right : Closed mate (lo + k.val + 2) (n - k.val - 1) := by
          intro i hlo hhi
          have h := closed i (by omega) (by omega)
          have ne₀ : mate i ≠ lo := by
            intro he
            have hi := congrArg mate he
            rw [hinv] at hi
            omega
          have ne₁ : mate i ≠ mate lo := by
            intro he
            have := hinv.injective he
            omega
          have bot : mate lo ≤ mate i := by
            by_contra hg
            apply hnc lo (mate i) (by omega) (by omega)
            rw [hinv]
            omega
          constructor <;> omega
        have hl := ih k.val (by omega) (lo + 1) left
          (fun i hlo hhi => fixed i (by omega) (by omega))
          (fun i hlo hhi => failed i (by omega) (by omega))
        have hr := ih (n - k.val - 1) (by omega) (lo + k.val + 2) right
          (fun i hlo hhi => fixed i (by omega) (by omega))
          (fun i hlo hhi => failed i (by omega) (by omega))
        simp only [possible, ha, ↓reduceIte]
        apply List.any_eq_true.mpr
        refine ⟨k, List.mem_finRange k, ?_⟩
        simp only [hk, failed lo (by omega) (by omega) ha, hba, hl, hr, Bool.and_self]

/-- A rejected interval forces one successful chord of this same matching. -/
theorem successful_chord (mate : ℕ → ℕ)
    (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (active : ℕ → Bool) (bad : ℕ → ℕ → Bool) (lo n : ℕ)
    (closed : Closed mate lo n)
    (fixed : ∀ i, lo ≤ i → i < lo + n → (mate i = i ↔ active i = false))
    (reject : possible active bad lo n = false) :
    ∃ i, lo ≤ i ∧ i < lo + n ∧ active i = true ∧ bad i (mate i) = false := by
  by_contra hn
  have all : ∀ i, lo ≤ i → i < lo + n → active i = true → bad i (mate i) = true := by
    intro i hlo hhi ha
    cases he : bad i (mate i) with
    | true => rfl
    | false => exact False.elim (hn ⟨i,hlo,hhi,ha,he⟩)
  have := possible_of_matching mate hinv hnc active bad lo n closed fixed all
  simp_all

end FourColor.KempeIntervalMatching
