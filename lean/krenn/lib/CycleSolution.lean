import Mathlib
import ColourPerMatching
import EvenCycle

/-!
# Two colours at every even vertex count

The conjecture asserts that beyond four vertices no more than two colours are
possible.  Two are, at every even count: colour the edges of a cycle by which of
its two alternating matchings they belong to, and leave the chords uncoloured.

Every hypothesis of the colouring construction is supplied by the cycle.  A
matching all of whose edges are coloured is cyclic, hence one of the two
alternating ones, hence monochromatic; and each colour is worn by exactly that one
matching.  So the bound of two colours is attained, not merely permitted.
-/

namespace CycleSolution

open Amplitude ColourPerMatching EvenCycle

variable {n : ℕ}

/-- The alternating matchings as permutations. -/
def altEquiv (n : ℕ) (b : ZMod 2) : Equiv.Perm (ZMod (2 * n)) :=
  Function.Involutive.toPerm _ (altPerm_involutive (n := n) b)

@[simp] theorem altEquiv_apply (b : ZMod 2) (i : ZMod (2 * n)) :
    altEquiv n b i = altPerm n b i := rfl

/-- The two alternating matchings never agree: one steps forward where the other
steps back. -/
theorem altPerm_ne_altPerm (hm : 3 ≤ 2 * n) (i : ZMod (2 * n)) :
    altPerm n 0 i ≠ altPerm n 1 i := by
  have hone := one_ne_neg_one (m := 2 * n) hm
  have hstep : (i + 1 : ZMod (2 * n)) ≠ i - 1 := by
    intro hh
    exact hone (by linear_combination hh)
  have hcases : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  unfold altPerm
  by_cases h : par n i = 0
  · rw [if_pos h, if_neg (by rw [h]; decide)]
    exact hstep
  · have h1 : par n i = 1 := by
      rcases hcases (par n i) with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [if_neg h, if_pos h1]
    exact fun hh => hstep hh.symm

/-- The cycle's edge colouring: an edge wears the colour of the alternating
matching it belongs to; chords stay uncoloured. -/
def cycEc (n : ℕ) (i j : ZMod (2 * n)) : Option (ZMod 2) :=
  if j = altPerm n 0 i then some 0 else if j = altPerm n 1 i then some 1 else none

theorem cycEc_eq_some_iff (hm : 3 ≤ 2 * n) (i j : ZMod (2 * n)) (b : ZMod 2) :
    cycEc n i j = some b ↔ j = altPerm n b i := by
  unfold cycEc
  by_cases h0 : j = altPerm n 0 i
  · rw [if_pos h0]
    constructor
    · rintro h
      have : b = 0 := (Option.some_inj.mp h).symm
      rw [this, h0]
    · intro hb
      rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) b with rfl | rfl
      · rfl
      · exact absurd (h0.symm.trans hb) (altPerm_ne_altPerm hm i)
  · rw [if_neg h0]
    by_cases h1 : j = altPerm n 1 i
    · rw [if_pos h1]
      constructor
      · rintro h
        have : b = 1 := (Option.some_inj.mp h).symm
        rw [this, h1]
      · intro hb
        rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) b with rfl | rfl
        · exact absurd hb h0
        · rfl
    · rw [if_neg h1]
      constructor
      · intro h; exact absurd h (by simp)
      · intro hb
        rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) b with rfl | rfl
        · exact absurd hb h0
        · exact absurd hb h1

theorem cycEc_comm (hm : 3 ≤ 2 * n) (i j : ZMod (2 * n)) : cycEc n i j = cycEc n j i := by
  have key : ∀ (a b : ZMod (2 * n)) (c : ZMod 2),
      cycEc n a b = some c → cycEc n b a = some c := by
    intro a b c hab
    rw [cycEc_eq_some_iff hm] at hab ⊢
    rw [hab, altPerm_involutive (n := n) c a]
  rcases hij : cycEc n i j with _ | b
  · rcases hji : cycEc n j i with _ | b'
    · rfl
    · rw [key j i b' hji] at hij
      exact absurd hij (by simp)
  · rw [key i j b hij]

/-- The alternating matchings are perfect matchings. -/
theorem altEquiv_mem [NeZero (2 * n)] (hn : 1 ≤ n) (b : ZMod 2) :
    altEquiv n b ∈ pairings (ZMod (2 * n)) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_, fun x => ?_⟩
  · exact altPerm_involutive b x
  · exact altPerm_ne hn b x

/-- The colour of an edge determines which alternating matching it belongs to. -/
theorem altPerm_inj (hm : 3 ≤ 2 * n) {k b : ZMod 2} {x : ZMod (2 * n)}
    (h : altPerm n k x = altPerm n b x) : k = b := by
  have hcases : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  rcases hcases k with rfl | rfl <;> rcases hcases b with rfl | rfl
  · rfl
  · exact absurd h (altPerm_ne_altPerm hm x)
  · exact absurd h.symm (altPerm_ne_altPerm hm x)
  · rfl

/-- A totally coloured matching uses only cycle edges. -/
theorem cyc_isCyclic (hm : 3 ≤ 2 * n) {σ : Equiv.Perm (ZMod (2 * n))}
    (h : ∀ x, (cycEc n x (σ x)).isSome) : IsCyclic σ := by
  intro i
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i)
  rw [cycEc_eq_some_iff hm] at hb
  rw [hb]
  unfold altPerm
  by_cases hp : par n i = b
  · exact Or.inl (by rw [if_pos hp])
  · exact Or.inr (by rw [if_neg hp])

/-- **No totally coloured matching mixes colours**: it is one of the two
alternating ones, and each of those wears a single colour throughout. -/
theorem cyc_mono [NeZero (2 * n)] (hm : 3 ≤ 2 * n) :
    ∀ σ ∈ pairings (ZMod (2 * n)), (∀ x, (cycEc n x (σ x)).isSome) →
      ∀ x y : ZMod (2 * n), ∀ k l : ZMod 2,
        cycEc n x (σ x) = some k → cycEc n y (σ y) = some l → k = l := by
  intro σ hσ hall x y k l hk hl
  obtain ⟨hinv, -⟩ := (Finset.mem_filter.mp hσ).2
  obtain ⟨b, hb⟩ := eq_altPerm hm hinv (cyc_isCyclic hm hall)
  rw [cycEc_eq_some_iff hm] at hk hl
  have hkb : k = b := altPerm_inj hm (hk.symm.trans (hb x))
  have hlb : l = b := altPerm_inj hm (hl.symm.trans (hb y))
  rw [hkb, hlb]

/-- **Each colour is worn by exactly one matching.** -/
theorem cyc_uniq [NeZero (2 * n)] (hm : 3 ≤ 2 * n) (hn : 1 ≤ n) (b : ZMod 2) :
    ((pairings (ZMod (2 * n))).filter
      (fun σ => ∀ x, cycEc n x (σ x) = some b)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨altEquiv n b, ?_⟩
  ext σ
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    ext i
    have hi := h i
    rw [cycEc_eq_some_iff hm] at hi
    rw [hi, altEquiv_apply]
  · rintro rfl
    exact ⟨altEquiv_mem hn b, fun x => by rw [cycEc_eq_some_iff hm, altEquiv_apply]⟩

/-- **Two colours at every even vertex count.**  On six or more vertices the cycle
colouring gives every constant colouring amplitude one and every other colouring
amplitude zero.  So the conjecture's bound of two colours is attained. -/
theorem spec [NeZero (2 * n)] (hm : 3 ≤ 2 * n) (hn : 1 ≤ n) :
    (∀ k : ZMod 2,
        amplitude (weightOf (cycEc n) (cycEc_comm hm)) (Amplitude.const k) = 1) ∧
      (∀ c : ZMod (2 * n) → ZMod 2, ¬ (∀ x y : ZMod (2 * n), c x = c y) →
        amplitude (weightOf (cycEc n) (cycEc_comm hm)) c = 0) :=
  amplitude_spec _ _ (cyc_mono hm) (cyc_uniq hm hn)

end CycleSolution
