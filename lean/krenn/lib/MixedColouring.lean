import Mathlib

/-!
# A fourth matching

Three pairwise disjoint perfect matchings assign to every site three partners, one per
colour.  A colouring is *compatible* when each site's colour points at a partner wearing
the same colour; the constant colourings are compatible, and a non-constant compatible
colouring is exactly a fourth perfect matching inside the union.

When the union of two of the matchings is disconnected a fourth matching is immediate:
colour one component with the first matching and its complement with the second.  So the
live case is a single alternating cycle, and there the sites are indexed by `ZMod m × Bool`
— `(i, true)` is `xᵢ`, `(i, false)` is `yᵢ`, the first matching joins `xᵢ` to `yᵢ` and the
second joins `xᵢ` to `yᵢ₊₁`.  This file settles the case where the third matching carries a
chord between the two classes.
-/

namespace MixedColouring

open Equiv

/-- Sites of the cycle model. -/
abbrev Site (m : ℕ) := ZMod m × Bool

variable {m : ℕ}

/-- The matching `xᵢ — yᵢ`. -/
def s0 : Perm (Site m) where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The matching `xᵢ — yᵢ₊₁`. -/
def s1 : Perm (Site m) where
  toFun p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  invFun p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  left_inv p := by obtain ⟨i, b⟩ := p; cases b <;> simp
  right_inv p := by obtain ⟨i, b⟩ := p; cases b <;> simp

@[simp] lemma s0_apply (p : Site m) : s0 p = (p.1, !p.2) := rfl

@[simp] lemma s1_apply (p : Site m) :
    s1 p = if p.2 then (p.1 + 1, false) else (p.1 - 1, true) := rfl

/-! ### Positions along the cycle -/

lemma val_add_one (hm : 1 < m) (u : ZMod m) (h : u.val + 1 < m) : (u + 1).val = u.val + 1 := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt h]

lemma val_sub_one (hm : 1 < m) (v : ZMod m) (h : v.val ≠ 0) : (v - 1).val = v.val - 1 := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  have h1 : (v - 1) + 1 = v := by ring
  have hlt := ZMod.val_lt (v - 1)
  rcases Nat.lt_or_ge ((v - 1).val + 1) m with h2 | h2
  · have := val_add_one hm (v - 1) h2
    rw [h1] at this; omega
  · exfalso
    have hval : (v - 1).val + 1 = m := by omega
    have hv : ((v - 1) + 1).val = ((v - 1).val + 1) % m := by
      rw [ZMod.val_add, ZMod.val_one]
    rw [h1, hval, Nat.mod_self] at hv
    exact h hv

lemma eq_of_val_sub_eq (hm : 1 < m) {a b j : ZMod m} (h : (a - j).val = (b - j).val) : a = b := by
  haveI : NeZero m := ⟨by omega⟩
  have := ZMod.val_injective m h
  linear_combination this

lemma eq_of_val_sub_eq_zero {a j : ZMod m} (h : (a - j).val = 0) : a = j := by
  have := (ZMod.val_eq_zero _).mp h
  linear_combination this

/-! ### The colouring cut out by a crossing chord -/

/-- The colouring cut out by a chord `xᵢ — y_j` crossing the two classes: the chord wears
colour `2`, the arc running forward from `y_j` to `xᵢ` wears colour `1` on its
second-matching edges, and the arc running back wears colour `0` on its first-matching
edges.  Positions are measured by `(· - j).val`, so `y_j` sits at `0` and `xᵢ` at `d`. -/
def cross (i j : ZMod m) (p : Site m) : Fin 3 :=
  if p.2 then
    (if (p.1 - j).val = (i - j).val then 2 else if (p.1 - j).val < (i - j).val then 1 else 0)
  else
    (if (p.1 - j).val = 0 then 2 else if (p.1 - j).val ≤ (i - j).val then 1 else 0)

lemma cross_true_eq_two {i j k : ZMod m} (h : (k - j).val = (i - j).val) :
    cross i j (k, true) = 2 := by simp [cross, h]

lemma cross_true_eq_one {i j k : ZMod m} (h : (k - j).val < (i - j).val) :
    cross i j (k, true) = 1 := by
  have hne : (k - j).val ≠ (i - j).val := by omega
  simp [cross, hne, h]

lemma cross_true_eq_zero {i j k : ZMod m} (h : (i - j).val < (k - j).val) :
    cross i j (k, true) = 0 := by
  have hne : (k - j).val ≠ (i - j).val := by omega
  have hnl : ¬ (k - j).val < (i - j).val := by omega
  simp [cross, hne, hnl]

lemma cross_false_eq_two {i j k : ZMod m} (h : (k - j).val = 0) :
    cross i j (k, false) = 2 := by simp [cross, h]

lemma cross_false_eq_one {i j k : ZMod m} (h0 : (k - j).val ≠ 0)
    (h : (k - j).val ≤ (i - j).val) : cross i j (k, false) = 1 := by
  simp [cross, h0, h]

lemma cross_false_eq_zero {i j k : ZMod m} (h : (i - j).val < (k - j).val) :
    cross i j (k, false) = 0 := by
  have h0 : (k - j).val ≠ 0 := by omega
  have hnl : ¬ (k - j).val ≤ (i - j).val := by omega
  simp [cross, h0, hnl]

lemma cross_eq_two_iff_true (hm : 1 < m) (i j k : ZMod m) :
    cross i j (k, true) = 2 ↔ k = i := by
  constructor
  · intro h
    rcases lt_trichotomy ((k - j).val) ((i - j).val) with hlt | heq | hgt
    · rw [cross_true_eq_one hlt] at h; exact absurd h (by decide)
    · exact eq_of_val_sub_eq hm heq
    · rw [cross_true_eq_zero hgt] at h; exact absurd h (by decide)
  · rintro rfl; exact cross_true_eq_two rfl

lemma cross_eq_two_iff_false (hm : 1 < m) (i j k : ZMod m) :
    cross i j (k, false) = 2 ↔ k = j := by
  haveI : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    by_cases h0 : (k - j).val = 0
    · exact eq_of_val_sub_eq_zero h0
    · rcases Nat.lt_or_ge ((i - j).val) ((k - j).val) with hgt | hle
      · rw [cross_false_eq_zero hgt] at h; exact absurd h (by decide)
      · rw [cross_false_eq_one h0 hle] at h; exact absurd h (by decide)
  · rintro rfl; exact cross_false_eq_two (by simp)

/-- **A crossing chord gives a fourth matching.**  If the third matching carries a chord
between the two classes of the alternating cycle, then `cross` is compatible with all three
matchings: every site's own colour points at a partner wearing that colour. -/
theorem cross_compatible (hm : 1 < m) (i j : ZMod m) (t : Perm (Site m))
    (h1 : t (i, true) = (j, false)) (h2 : t (j, false) = (i, true))
    (σ : Fin 3 → Perm (Site m)) (hσ0 : σ 0 = s0) (hσ1 : σ 1 = s1) (hσ2 : σ 2 = t)
    (p : Site m) : cross i j (σ (cross i j p) p) = cross i j p := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨k, b⟩ := p
  cases b
  case false =>
    by_cases h0 : (k - j).val = 0
    · have hkj : k = j := eq_of_val_sub_eq_zero h0
      rw [hkj, cross_false_eq_two (by simp : ((j : ZMod m) - j).val = 0), hσ2, h2]
      exact cross_true_eq_two rfl
    · rcases Nat.lt_or_ge ((i - j).val) ((k - j).val) with hgt | hle
      · rw [cross_false_eq_zero hgt, hσ0]
        have hs : (s0 : Perm (Site m)) (k, false) = (k, true) := by simp
        rw [hs]
        exact cross_true_eq_zero hgt
      · rw [cross_false_eq_one h0 hle, hσ1]
        have hs : (s1 : Perm (Site m)) (k, false) = (k - 1, true) := by simp
        rw [hs]
        have hval : (k - 1 - j).val = (k - j).val - 1 := by
          have hrw : k - 1 - j = (k - j) - 1 := by ring
          rw [hrw]; exact val_sub_one hm _ h0
        exact cross_true_eq_one (by omega)
  case true =>
    rcases lt_trichotomy ((k - j).val) ((i - j).val) with hlt | heq | hgt
    · rw [cross_true_eq_one hlt, hσ1]
      have hs : (s1 : Perm (Site m)) (k, true) = (k + 1, false) := by simp
      rw [hs]
      have hdm : (i - j).val < m := ZMod.val_lt _
      have hval : (k + 1 - j).val = (k - j).val + 1 := by
        have hrw : k + 1 - j = (k - j) + 1 := by ring
        rw [hrw]; exact val_add_one hm _ (by omega)
      exact cross_false_eq_one (by omega) (by omega)
    · have hki : k = i := eq_of_val_sub_eq hm heq
      rw [hki, cross_true_eq_two rfl, hσ2, h1]
      exact cross_false_eq_two (by simp)
    · rw [cross_true_eq_zero hgt, hσ0]
      have hs : (s0 : Perm (Site m)) (k, true) = (k, false) := by simp
      rw [hs]
      exact cross_false_eq_zero hgt

/-- The crossing colouring is not constant: the site one step past `xᵢ` misses colour `2`. -/
theorem cross_not_constant (hm : 1 < m) (i j : ZMod m) :
    cross i j (i, true) ≠ cross i j (i + 1, true) := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hv : (1 : ZMod m).val = (0 : ZMod m).val := by rw [h]
    rw [ZMod.val_one, ZMod.val_zero] at hv
    omega
  have hne : i + 1 ≠ i := fun h => hone (by linear_combination h)
  rw [(cross_eq_two_iff_true hm i j i).2 rfl]
  intro h
  exact hne ((cross_eq_two_iff_true hm i j (i + 1)).1 h.symm)

/-! ### Two interleaved chords -/

/-- Colour of the site at cycle position `r` on side `side`, for a pair of chords whose four
endpoints sit at positions `a < b ≤ a'` measured from the base `y`-site.  The chord
`x_a — x_a'` and the chord `y_0 — y_b` interleave, so the four arcs they cut out are all
even and each is matched by consecutive cycle edges. -/
def colOf (a b a' : ℕ) (r : ℕ) (side : Bool) : Fin 3 :=
  if side then
    (if r = a ∨ r = a' then 2 else if r < a ∨ (b ≤ r ∧ r < a') then 1 else 0)
  else
    (if r = 0 ∨ r = b then 2 else if (1 ≤ r ∧ r ≤ a) ∨ (b < r ∧ r ≤ a') then 1 else 0)

lemma colOf_true_two {a b a' r : ℕ} (h : r = a ∨ r = a') : colOf a b a' r true = 2 := by
  simp [colOf, h]

lemma colOf_true_one {a b a' r : ℕ} (h2 : ¬ (r = a ∨ r = a'))
    (h1 : r < a ∨ (b ≤ r ∧ r < a')) : colOf a b a' r true = 1 := by simp [colOf, h2, h1]

lemma colOf_true_zero {a b a' r : ℕ} (h2 : ¬ (r = a ∨ r = a'))
    (h1 : ¬ (r < a ∨ (b ≤ r ∧ r < a'))) : colOf a b a' r true = 0 := by simp [colOf, h2, h1]

lemma colOf_false_two {a b a' r : ℕ} (h : r = 0 ∨ r = b) : colOf a b a' r false = 2 := by
  simp [colOf, h]

lemma colOf_false_one {a b a' r : ℕ} (h2 : ¬ (r = 0 ∨ r = b))
    (h1 : (1 ≤ r ∧ r ≤ a) ∨ (b < r ∧ r ≤ a')) : colOf a b a' r false = 1 := by
  simp [colOf, h2, h1]

lemma colOf_false_zero {a b a' r : ℕ} (h2 : ¬ (r = 0 ∨ r = b))
    (h1 : ¬ ((1 ≤ r ∧ r ≤ a) ∨ (b < r ∧ r ≤ a'))) : colOf a b a' r false = 0 := by
  simp [colOf, h2, h1]

/-- The colouring cut out by two interleaved chords. -/
def inter (j : ZMod m) (a b a' : ℕ) (p : Site m) : Fin 3 :=
  colOf a b a' (p.1 - j).val p.2

lemma inter_apply (j : ZMod m) (a b a' : ℕ) (k : ZMod m) (side : Bool) :
    inter j a b a' (k, side) = colOf a b a' (k - j).val side := rfl

/-- **Interleaved chords give a fourth matching.**  If the third matching carries a chord on
each class and the two interleave around the alternating cycle, then `inter` is compatible
with all three matchings: every site's own colour points at a partner wearing that colour. -/
theorem inter_compatible (hm : 1 < m) {j i i' j' : ZMod m} {a b a' : ℕ}
    (hab : a < b) (hba : b ≤ a') (ham : a' < m)
    (hi : (i - j).val = a) (hi' : (i' - j).val = a') (hj' : (j' - j).val = b)
    (t : Perm (Site m))
    (e1 : t (i, true) = (i', true)) (e2 : t (i', true) = (i, true))
    (e3 : t (j, false) = (j', false)) (e4 : t (j', false) = (j, false))
    (σ : Fin 3 → Perm (Site m)) (hσ0 : σ 0 = s0) (hσ1 : σ 1 = s1) (hσ2 : σ 2 = t)
    (p : Site m) : inter j a b a' (σ (inter j a b a' p) p) = inter j a b a' p := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨k, side⟩ := p
  have hkm : (k - j).val < m := ZMod.val_lt _
  have hj0 : (j - j).val = 0 := by simp
  cases side
  case false =>
    by_cases c2 : (k - j).val = 0 ∨ (k - j).val = b
    · have hcol : inter j a b a' (k, false) = 2 := colOf_false_two c2
      rw [hcol, hσ2]
      rcases c2 with c2 | c2
      · have hkj : k = j := eq_of_val_sub_eq hm (by rw [c2, hj0])
        rw [hkj, e3]
        show colOf a b a' (j' - j).val false = 2
        rw [hj']; exact colOf_false_two (Or.inr rfl)
      · have hkj : k = j' := eq_of_val_sub_eq hm (by rw [c2, hj'])
        rw [hkj, e4]
        show colOf a b a' (j - j).val false = 2
        rw [hj0]; exact colOf_false_two (Or.inl rfl)
    · by_cases c1 : (1 ≤ (k - j).val ∧ (k - j).val ≤ a) ∨ (b < (k - j).val ∧ (k - j).val ≤ a')
      · have hcol : inter j a b a' (k, false) = 1 := colOf_false_one c2 c1
        rw [hcol, hσ1]
        have hs : (s1 : Perm (Site m)) (k, false) = (k - 1, true) := by simp
        rw [hs]
        have hval : (k - 1 - j).val = (k - j).val - 1 := by
          have hrw : k - 1 - j = (k - j) - 1 := by ring
          rw [hrw]; exact val_sub_one hm _ (by omega)
        show colOf a b a' (k - 1 - j).val true = 1
        rw [hval]; exact colOf_true_one (by omega) (by omega)
      · have hcol : inter j a b a' (k, false) = 0 := colOf_false_zero c2 c1
        rw [hcol, hσ0]
        have hs : (s0 : Perm (Site m)) (k, false) = (k, true) := by simp
        rw [hs]
        show colOf a b a' (k - j).val true = 0
        exact colOf_true_zero (by omega) (by omega)
  case true =>
    by_cases c2 : (k - j).val = a ∨ (k - j).val = a'
    · have hcol : inter j a b a' (k, true) = 2 := colOf_true_two c2
      rw [hcol, hσ2]
      rcases c2 with c2 | c2
      · have hki : k = i := eq_of_val_sub_eq hm (by rw [c2, hi])
        rw [hki, e1]
        show colOf a b a' (i' - j).val true = 2
        rw [hi']; exact colOf_true_two (Or.inr rfl)
      · have hki : k = i' := eq_of_val_sub_eq hm (by rw [c2, hi'])
        rw [hki, e2]
        show colOf a b a' (i - j).val true = 2
        rw [hi]; exact colOf_true_two (Or.inl rfl)
    · by_cases c1 : (k - j).val < a ∨ (b ≤ (k - j).val ∧ (k - j).val < a')
      · have hcol : inter j a b a' (k, true) = 1 := colOf_true_one c2 c1
        rw [hcol, hσ1]
        have hs : (s1 : Perm (Site m)) (k, true) = (k + 1, false) := by simp
        rw [hs]
        have hval : (k + 1 - j).val = (k - j).val + 1 := by
          have hrw : k + 1 - j = (k - j) + 1 := by ring
          rw [hrw]; exact val_add_one hm _ (by omega)
        show colOf a b a' (k + 1 - j).val false = 1
        rw [hval]; exact colOf_false_one (by omega) (by omega)
      · have hcol : inter j a b a' (k, true) = 0 := colOf_true_zero c2 c1
        rw [hcol, hσ0]
        have hs : (s0 : Perm (Site m)) (k, true) = (k, false) := by simp
        rw [hs]
        show colOf a b a' (k - j).val false = 0
        exact colOf_false_zero (by omega) (by omega)

/-- The interleaved colouring is not constant: only four sites wear colour `2`. -/
theorem inter_not_constant (hm : 2 < m) (j : ZMod m) {a b a' : ℕ}
    (hab : a < b) (hba : b ≤ a') (ham : a' < m) :
    ∃ q : Site m, inter j a b a' q ≠ inter j a b a' (j, false) := by
  haveI : NeZero m := ⟨by omega⟩
  set r : ℕ := if b = 1 then 2 else 1 with hrdef
  have hrm : r < m := by rw [hrdef]; split <;> omega
  have hval : (j + (r : ZMod m) - j).val = r := by
    have hrw : j + (r : ZMod m) - j = (r : ZMod m) := by ring
    rw [hrw]
    first
      | exact ZMod.val_natCast_of_lt hrm
      | exact ZMod.val_cast_of_lt hrm
  refine ⟨(j + (r : ZMod m), false), ?_⟩
  have h0 : inter j a b a' (j, false) = 2 := by
    show colOf a b a' (j - j).val false = 2
    rw [(by simp : ((j : ZMod m) - j).val = 0)]
    exact colOf_false_two (Or.inl rfl)
  have hne : ¬ (r = 0 ∨ r = b) := by rw [hrdef]; split <;> omega
  have h1 : inter j a b a' (j + (r : ZMod m), false) ≠ 2 := by
    show colOf a b a' (j + (r : ZMod m) - j).val false ≠ 2
    rw [hval]
    by_cases c1 : (1 ≤ r ∧ r ≤ a) ∨ (b < r ∧ r ≤ a')
    · rw [colOf_false_one hne c1]; decide
    · rw [colOf_false_zero hne c1]; decide
  rw [h0]; exact h1

/-! ### Every third matching is of one of the two shapes -/

/-- **Some chord of one class interleaves with some chord of the other.**  Take the chord
of shortest forward span; the site just past its tail is the base.  Either the base's own
partner lands inside that span — and then the shortest chord's own two ends straddle it —
or it lands beyond, and then the base's chord straddles the shortest chord.  Minimality is
used once, to bound the span at the base from below. -/
theorem exists_chords (hm : 1 < m) (τ τ' : ZMod m → ZMod m)
    (hτ : ∀ i, τ (τ i) = i) (hτf : ∀ i, τ i ≠ i) (hτ'f : ∀ j, τ' j ≠ j) :
    ∃ i j : ZMod m, (τ i - j).val < (τ' j - j).val ∧ (τ' j - j).val ≤ (i - j).val := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ZMod m))
    (fun i => (τ i - i).val) ⟨0, Finset.mem_univ 0⟩
  set d := (τ i₀ - i₀).val with hd
  have hne : (τ i₀ - i₀).val ≠ 0 := fun h => hτf i₀ (eq_of_val_sub_eq_zero h)
  have hd1 : 1 ≤ d := by omega
  set w := i₀ + 1 with hw
  have hne' : (τ' w - w).val ≠ 0 := fun h => hτ'f w (eq_of_val_sub_eq_zero h)
  have hv1 : 1 ≤ (τ' w - w).val := by omega
  have hvm : (τ' w - w).val < m := ZMod.val_lt _
  by_cases hB : (τ' w - w).val < d
  · refine ⟨τ w, w, ?_, ?_⟩
    · rw [hτ w, sub_self, ZMod.val_zero]; omega
    · have := hmin w (Finset.mem_univ w); omega
  · refine ⟨i₀, w, ?_, ?_⟩
    · have hval : (τ i₀ - w).val = d - 1 := by
        have hrw : τ i₀ - w = (τ i₀ - i₀) - 1 := by rw [hw]; ring
        rw [hrw]; exact val_sub_one hm _ (by omega)
      omega
    · have hval : (i₀ - w).val = m - 1 := by
        have hrw : i₀ - w = ((m - 1 : ℕ) : ZMod m) := by
          have hc : ((m - 1 : ℕ) : ZMod m) = (m : ZMod m) - 1 := by
            push_cast [Nat.cast_sub (by omega : 1 ≤ m)]; ring
          rw [hc, ZMod.natCast_self, hw]; ring
        rw [hrw]
        first
          | exact ZMod.val_natCast_of_lt (by omega)
          | exact ZMod.val_cast_of_lt (by omega)
      omega

/-- **A fourth matching in the cycle model.**  A third matching, disjoint from the two that
form the alternating cycle, always admits a non-constant compatible colouring once there
are more than four sites. -/
theorem exists_mixed_model (hm : 2 < m) (t : Perm (Site m))
    (hinv : ∀ p, t (t p) = p) (hfp : ∀ p, t p ≠ p)
    (σ : Fin 3 → Perm (Site m)) (hσ0 : σ 0 = s0) (hσ1 : σ 1 = s1) (hσ2 : σ 2 = t) :
    ∃ c : Site m → Fin 3, (∃ p q : Site m, c p ≠ c q) ∧ ∀ p, c (σ (c p) p) = c p := by
  haveI : NeZero m := ⟨by omega⟩
  by_cases hcross : ∃ i j : ZMod m, t (i, true) = (j, false)
  · obtain ⟨i, j, hij⟩ := hcross
    have hji : t (j, false) = (i, true) := by rw [← hij, hinv]
    exact ⟨cross i j, ⟨_, _, cross_not_constant (by omega) i j⟩,
      cross_compatible (by omega) i j t hij hji σ hσ0 hσ1 hσ2⟩
  · push_neg at hcross
    have hx : ∀ i : ZMod m, ∃ k, t (i, true) = (k, true) := by
      intro i
      have he := Prod.mk.eta (p := t (i, true))
      rcases Bool.eq_false_or_eq_true ((t (i, true)).2) with hb | hb <;> rw [hb] at he
      · exact ⟨(t (i, true)).1, he.symm⟩
      · exact absurd he.symm (hcross i (t (i, true)).1)
    have hy : ∀ j : ZMod m, ∃ k, t (j, false) = (k, false) := by
      intro j
      have he := Prod.mk.eta (p := t (j, false))
      rcases Bool.eq_false_or_eq_true ((t (j, false)).2) with hb | hb <;> rw [hb] at he
      · exact absurd (by rw [he, hinv]) (hcross (t (j, false)).1 j)
      · exact ⟨(t (j, false)).1, he.symm⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : ZMod m → ZMod m, ∀ i, t (i, true) = (τ i, true) :=
      ⟨fun i => Classical.choose (hx i), fun i => Classical.choose_spec (hx i)⟩
    obtain ⟨τ', hτ'⟩ : ∃ τ' : ZMod m → ZMod m, ∀ j, t (j, false) = (τ' j, false) :=
      ⟨fun j => Classical.choose (hy j), fun j => Classical.choose_spec (hy j)⟩
    have hττ : ∀ i, τ (τ i) = i := by
      intro i
      have h1 : ((τ (τ i) : ZMod m), true) = ((i : ZMod m), true) := by
        rw [← hτ (τ i), ← hτ i, hinv]
      exact congrArg Prod.fst h1
    have hτ'τ' : ∀ j, τ' (τ' j) = j := by
      intro j
      have h1 : ((τ' (τ' j) : ZMod m), false) = ((j : ZMod m), false) := by
        rw [← hτ' (τ' j), ← hτ' j, hinv]
      exact congrArg Prod.fst h1
    have hτf : ∀ i, τ i ≠ i := fun i h => hfp (i, true) (by rw [hτ i, h])
    have hτ'f : ∀ j, τ' j ≠ j := fun j h => hfp (j, false) (by rw [hτ' j, h])
    obtain ⟨i, j, hab, hba⟩ := exists_chords (by omega) τ τ' hττ hτf hτ'f
    have ham : (i - j).val < m := ZMod.val_lt _
    refine ⟨inter j ((τ i - j).val) ((τ' j - j).val) ((i - j).val), ?_, ?_⟩
    · obtain ⟨q, hq⟩ := inter_not_constant hm j hab hba ham
      exact ⟨q, _, hq⟩
    · exact inter_compatible (by omega) hab hba ham rfl rfl rfl t
        (by rw [hτ (τ i), hττ i]) (hτ i) (hτ' j) (by rw [hτ' (τ' j), hτ'τ' j]) σ hσ0 hσ1 hσ2

end MixedColouring
