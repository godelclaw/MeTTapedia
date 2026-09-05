import Mettapedia.GraphTheory.FourColor.ZigzagRingTangle
import Mettapedia.GraphTheory.TubeRingOrbit

/-!
# The ring's support is the tabulated transition

`TubeRingOrbit` tabulates the zigzag ring's transition on base-3 numerals:
bit `Y` of `stepMask k X (2^k)` is set iff some choice mask `m` yields
out-word `Y` from in-word `X`.  `ZigzagRingTangle.accepts_iff` gives the same
transition semantically on colour words.  This file identifies the two:
`accepts_iff_testBit`.

Digits: `wordOf k X i = col (digit X i)` with `col 0 = red`, `col 1 = blue`,
`col 2 = purple`; the third colour of two distinct digits `p, q` is
`col (3 - p - q)`.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace ZigzagRing

open TubeRingOrbit

/-! ## Positional numerals -/

/-- `Σ_{i<n} f i · β^i` -/
def encB (β : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => encB β f n + f n * β ^ n

/-- digit `i` in base `β` -/
def digB (β w i : Nat) : Nat := (w / β ^ i) % β

theorem encB_lt {β : Nat} (hβ : 0 < β) {f : Nat → Nat} :
    ∀ n, (∀ i, i < n → f i < β) → encB β f n < β ^ n
  | 0, _ => by simp [encB]
  | n + 1, hf => by
    have ih := encB_lt hβ n (fun i hi => hf i (by omega))
    have h1 : f n * β ^ n ≤ (β - 1) * β ^ n :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (hf n (by omega)))
    have h2 : β ^ n + (β - 1) * β ^ n = β ^ (n + 1) := by
      rw [pow_succ]
      calc β ^ n + (β - 1) * β ^ n = (1 + (β - 1)) * β ^ n := by ring
        _ = β ^ n * β := by rw [Nat.add_sub_cancel' hβ, mul_comm]
    simp only [encB]
    omega

theorem digB_encB {β : Nat} (hβ : 1 < β) {f : Nat → Nat} :
    ∀ n, (∀ i, i < n → f i < β) → ∀ i, i < n → digB β (encB β f n) i = f i
  | 0, _, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, hf, i, h => by
    have hβ0 : 0 < β := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hi | rfl
    · have hsplit : β ^ n = β ^ (n - i - 1) * β * β ^ i := by
        rw [mul_assoc, ← pow_succ', ← pow_add]
        congr 1
        omega
      have hdiv : (encB β f n + f n * β ^ n) / β ^ i =
          encB β f n / β ^ i + f n * (β ^ (n - i - 1) * β) := by
        rw [hsplit, ← mul_assoc, Nat.add_mul_div_right _ _ (pow_pos hβ0 _)]
      have hmod : (encB β f n / β ^ i + f n * (β ^ (n - i - 1) * β)) % β =
          (encB β f n / β ^ i) % β := by
        rw [← mul_assoc, Nat.add_mul_mod_self_right]
      simp only [encB, digB]
      rw [hdiv, hmod]
      exact digB_encB hβ n (fun j hj => hf j (by omega)) i hi
    · simp only [encB, digB]
      rw [Nat.add_mul_div_right _ _ (pow_pos hβ0 _),
        Nat.div_eq_of_lt (encB_lt hβ0 i (fun j hj => hf j (by omega))), zero_add,
        Nat.mod_eq_of_lt (hf i (by omega))]

theorem encB_digB (β : Nat) : ∀ n X, encB β (digB β X) n = X % β ^ n
  | 0, X => by simp [encB, Nat.mod_one]
  | n + 1, X => by
    simp only [encB]
    rw [encB_digB β n X, Nat.mod_pow_succ]
    simp only [digB]
    ring

theorem encB_digB_of_lt {β n X : Nat} (h : X < β ^ n) : encB β (digB β X) n = X := by
  rw [encB_digB, Nat.mod_eq_of_lt h]

theorem digit_eq_digB (w i : Nat) : digit w i = digB 3 w i := rfl

theorem digit_lt (w i : Nat) : digit w i < 3 := Nat.mod_lt _ (by norm_num)

/-! ## Colours as digits -/

/-- `0 ↦ red`, `1 ↦ blue`, `2 ↦ purple` -/
def col : Nat → Color
  | 0 => red
  | 1 => blue
  | _ => purple

def idx (c : Color) : Nat := if c = red then 0 else if c = blue then 1 else 2

theorem col_ne_zero (n : Nat) : col n ≠ 0 := by
  match n with
  | 0 => exact red_ne_zero
  | 1 => exact blue_ne_zero
  | n + 2 => exact purple_ne_zero

theorem idx_lt (c : Color) : idx c < 3 := by
  unfold idx; split_ifs <;> omega

theorem col_idx {c : Color} (hc : c ≠ 0) : col (idx c) = c := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp [idx, col, Ne.symm red_ne_blue, Ne.symm red_ne_purple, Ne.symm blue_ne_purple]

theorem idx_col {n : Nat} (h : n < 3) : idx (col n) = n := by
  match n, h with
  | 0, _ => simp [idx, col]
  | 1, _ => simp [idx, col, Ne.symm red_ne_blue]
  | 2, _ => simp [idx, col, Ne.symm red_ne_purple, Ne.symm blue_ne_purple]

theorem col_inj {p q : Nat} (hp : p < 3) (hq : q < 3) (h : col p = col q) : p = q := by
  have := congrArg idx h
  rwa [idx_col hp, idx_col hq] at this

theorem col_third {p q : Nat} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q) :
    col (3 - p - q) = col p + col q := by
  match p, q, hp, hq, hpq with
  | 0, 1, _, _, _ => simp [col]
  | 0, 2, _, _, _ => simp [col]
  | 1, 0, _, _, _ => simp [col]
  | 1, 2, _, _, _ => simp [col]
  | 2, 0, _, _, _ => simp [col]
  | 2, 1, _, _, _ => simp [col]
  | 0, 0, _, _, h => exact absurd rfl h
  | 1, 1, _, _, h => exact absurd rfl h
  | 2, 2, _, _, h => exact absurd rfl h

/-- the colour word of a base-3 numeral -/
def wordOf (k : Nat) (X : Nat) : Fin k → Color := fun i => col (digit X i)

theorem wordOf_ne_zero (k X : Nat) (i : Fin k) : wordOf k X i ≠ 0 := col_ne_zero _

/-! ## Choices and masks -/

/-- the smaller colour digit different from `xi` -/
def lo (xi : Nat) : Nat := if xi = 0 then 1 else 0
/-- the larger colour digit different from `xi` -/
def hi (xi : Nat) : Nat := if xi = 2 then 1 else 2

theorem pick_eq (X m i : Nat) :
    pick X m i = if (m / 2 ^ i) % 2 = 1 then hi (digit X i) else lo (digit X i) := rfl

theorem lo_lt (xi : Nat) : lo xi < 3 := by unfold lo; split_ifs <;> omega
theorem hi_lt (xi : Nat) : hi xi < 3 := by unfold hi; split_ifs <;> omega
theorem lo_ne (xi : Nat) : lo xi ≠ xi := by unfold lo; split_ifs <;> omega
theorem hi_ne {xi : Nat} (_h : xi < 3) : hi xi ≠ xi := by unfold hi; split_ifs <;> omega

theorem pick_lt (X m i : Nat) : pick X m i < 3 := by
  rw [pick_eq]; split_ifs; exacts [hi_lt _, lo_lt _]

theorem pick_ne_digit (X m i : Nat) : pick X m i ≠ digit X i := by
  rw [pick_eq]; split_ifs; exacts [hi_ne (digit_lt X i), lo_ne _]

/-- every digit different from `xi` is `lo xi` or `hi xi` -/
theorem eq_lo_or_hi {xi v : Nat} (hxi : xi < 3) (hv : v < 3) (hne : v ≠ xi) :
    v = lo xi ∨ v = hi xi := by
  unfold lo hi
  split_ifs <;> omega

theorem aWord_eq_encB (X m : Nat) : ∀ n, aWord X m n = encB 3 (pick X m) n
  | 0 => rfl
  | n + 1 => by simp [aWord, encB, aWord_eq_encB X m n]

theorem digit_aWord (X m : Nat) {n i : Nat} (h : i < n) : digit (aWord X m n) i = pick X m i := by
  rw [aWord_eq_encB, digit_eq_digB]
  exact digB_encB (by norm_num) n (fun j _ => pick_lt X m j) i h

/-! ## The out-word computation -/

/-- the forced `b`-digit at position `i` -/
def bDig (k X A i : Nat) : Nat := 3 - digit X ((i + 1) % k) - digit A ((i + 1) % k)

/-- the out-digit at position `i` -/
def yDig (k X A i : Nat) : Nat := 3 - digit A i - bDig k X A i

theorem bDig_lt {k X A i : Nat} (h : digit A ((i + 1) % k) ≠ digit X ((i + 1) % k)) :
    bDig k X A i < 3 := by
  unfold bDig; have := digit_lt X ((i + 1) % k); have := digit_lt A ((i + 1) % k); omega

theorem yDig_lt {k X A i : Nat} (h : digit A i ≠ bDig k X A i) (hb : bDig k X A i < 3) :
    yDig k X A i < 3 := by
  unfold yDig; have := digit_lt A i; omega

theorem bDig_aWord_lt {k : Nat} (hk : 0 < k) (X m i : Nat) : bDig k X (aWord X m k) i < 3 :=
  bDig_lt (by rw [digit_aWord X m (Nat.mod_lt _ hk)]; exact pick_ne_digit X m _)

theorem outAux_eq_some_iff (k X A : Nat) :
    ∀ n Y, outAux k X A n = some Y ↔
      (∀ i, i < n → digit A i ≠ bDig k X A i) ∧ Y = encB 3 (yDig k X A) n
  | 0, Y => by simp [outAux, encB, eq_comm]
  | n + 1, Y => by
    have ih := outAux_eq_some_iff k X A n
    simp only [outAux]
    rcases hprev : outAux k X A n with _ | y
    · simp only [reduceCtorEq, false_iff]
      rintro ⟨hall, -⟩
      have := (ih (encB 3 (yDig k X A) n)).mpr ⟨fun i hi => hall i (by omega), rfl⟩
      rw [hprev] at this
      exact absurd this (by simp)
    · obtain ⟨hall, rfl⟩ := (ih y).mp hprev
      simp only
      split_ifs with heq
      · simp only [false_iff]
        rintro ⟨hall', -⟩
        exact hall' n (by omega) heq
      · simp only [Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨fun i hi => ?_, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hall i hi
          · exact heq
        · rintro ⟨-, rfl⟩
          rfl

theorem outWordN_eq_some_iff (k X A Y : Nat) :
    TubeRingOrbit.outWord k X A = some Y ↔
      (∀ i, i < k → digit A i ≠ bDig k X A i) ∧ Y = encB 3 (yDig k X A) k :=
  outAux_eq_some_iff k X A k Y

/-! ## Bits of the tabulated transition -/

theorem testBit_stepMask (k X Y : Nat) :
    ∀ n, (stepMask k X n).testBit Y = true ↔
      ∃ m, m < n ∧ TubeRingOrbit.outWord k X (aWord X m k) = some Y
  | 0 => by simp [stepMask]
  | n + 1 => by
    have ih := testBit_stepMask k X Y n
    simp only [stepMask]
    rcases hout : TubeRingOrbit.outWord k X (aWord X n k) with _ | y
    · rw [ih]
      constructor
      · rintro ⟨m, hm, h⟩; exact ⟨m, by omega, h⟩
      · rintro ⟨m, hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
        · exact ⟨m, hm, h⟩
        · rw [hout] at h; exact absurd h (by simp)
    · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨m, hm, h⟩ | h)
        · exact ⟨m, by omega, h⟩
        · exact ⟨n, by omega, by rw [hout, decide_eq_true_iff.mp h]⟩
      · rintro ⟨m, hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
        · exact Or.inl ⟨m, hm, h⟩
        · right
          rw [hout] at h
          exact decide_eq_true (Option.some.inj h)

/-! ## The identification -/

variable (k : Nat) [NeZero k]

theorem val_succ (i : Fin k) : ((i + 1 : Fin k) : Nat) = ((i : Nat) + 1) % k := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

theorem fin_succ_eq (i : Fin k) :
    (i + 1 : Fin k) = ⟨((i : Nat) + 1) % k, Nat.mod_lt _ (NeZero.pos k)⟩ :=
  Fin.ext (val_succ k i)

omit [NeZero k] in
theorem encB_congr {β n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    encB β f n = encB β g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encB]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- the forced colour of a mask choice is the colour of the forced digit -/
theorem bColor_wordOf (X m : Nat) (i : Fin k) :
    bColor k (wordOf k X) (fun j => col (pick X m j)) i =
      col (bDig k X (aWord X m k) i) := by
  simp only [bColor, wordOf, bDig, fin_succ_eq]
  rw [digit_aWord X m (Nat.mod_lt _ (NeZero.pos k)),
    col_third (digit_lt _ _) (pick_lt _ _ _) (pick_ne_digit X m _).symm]

/-- **The ring's support is the tabulated transition.** -/
theorem accepts_iff_testBit (X Y : Nat) (hY : Y < 3 ^ k) :
    (ring k).AcceptsBoundaryWords (wordOf k X) (wordOf k Y) ↔
      (stepMask k X (2 ^ k)).testBit Y = true := by
  have hk : 0 < k := NeZero.pos k
  have hj : ∀ i : Nat, (i + 1) % k < k := fun i => Nat.mod_lt _ hk
  rw [accepts_iff, testBit_stepMask]
  constructor
  · rintro ⟨a, hV, hy⟩
    -- the mask of the choice `a`
    let g : Nat → Nat := fun i =>
      if h : i < k then (if idx (a ⟨i, h⟩) = hi (digit X i) then 1 else 0) else 0
    have hg : ∀ i, g i < 2 := fun i => by simp only [g]; split_ifs <;> omega
    let m := encB 2 g k
    have hm : m < 2 ^ k := encB_lt (by norm_num) k (fun i _ => hg i)
    have hne : ∀ i (hi : i < k), idx (a ⟨i, hi⟩) ≠ digit X i := fun i hi h => by
      apply hV.a_ne_x ⟨i, hi⟩
      rw [← col_idx (hV.a_ne_zero ⟨i, hi⟩), h]; rfl
    -- the chosen digits are the digits of `a`
    have hpick : ∀ i (hi : i < k), pick X m i = idx (a ⟨i, hi⟩) := fun i hi => by
      rw [pick_eq]
      have hbit : (m / 2 ^ i) % 2 = g i := digB_encB (by norm_num) k (fun i _ => hg i) i hi
      rw [hbit]
      simp only [g, hi, dite_true]
      rcases eq_lo_or_hi (digit_lt X i) (idx_lt _) (hne i hi) with h | h
      · have : lo (digit X i) ≠ ZigzagRing.hi (digit X i) := by
          unfold lo ZigzagRing.hi; split_ifs <;> omega
        rw [h]; simp [this]
      · rw [h]; simp
    have hdA : ∀ i (hi : i < k), digit (aWord X m k) i = idx (a ⟨i, hi⟩) := fun i hi => by
      rw [digit_aWord X m hi, hpick i hi]
    have haw : (fun j : Fin k => col (pick X m (j : Nat))) = a := by
      funext j; rw [hpick j j.isLt, col_idx (hV.a_ne_zero j)]
    have hb : ∀ i : Fin k, col (bDig k X (aWord X m k) i) = bColor k (wordOf k X) a i := fun i => by
      rw [← bColor_wordOf k X m i, haw]
    have hab : ∀ i (hi : i < k), digit (aWord X m k) i ≠ bDig k X (aWord X m k) i :=
      fun i hi h => by
        apply hV.a_ne_b ⟨i, hi⟩
        rw [← hb ⟨i, hi⟩, ← h, hdA i hi, col_idx (hV.a_ne_zero _)]
    refine ⟨m, hm, ?_⟩
    rw [outWordN_eq_some_iff]
    refine ⟨hab, ?_⟩
    rw [← encB_digB_of_lt hY]
    apply encB_congr
    intro i hi
    rw [← digit_eq_digB]
    have hyi := congrFun hy ⟨i, hi⟩
    simp only [wordOf, outWord] at hyi
    rw [← hb ⟨i, hi⟩, ← col_idx (hV.a_ne_zero ⟨i, hi⟩), ← hdA i hi,
      ← col_third (digit_lt _ _) (bDig_aWord_lt hk X m i) (hab i hi)] at hyi
    exact col_inj (digit_lt _ _) (yDig_lt (hab i hi) (bDig_aWord_lt hk X m i)) hyi
  · rintro ⟨m, hm, hout⟩
    rw [outWordN_eq_some_iff] at hout
    obtain ⟨hall, rfl⟩ := hout
    refine ⟨fun i => col (pick X m i), ⟨fun i => wordOf_ne_zero k X i, fun i => col_ne_zero _,
      fun i h => pick_ne_digit X m i (col_inj (pick_lt _ _ _) (digit_lt _ _) h), ?_⟩, ?_⟩
    · intro i h
      rw [bColor_wordOf] at h
      exact hall i i.isLt (by
        rw [digit_aWord X m i.isLt]
        exact col_inj (pick_lt _ _ _) (bDig_aWord_lt hk X m i) h)
    · funext i
      simp only [wordOf, outWord]
      rw [bColor_wordOf, digit_eq_digB,
        digB_encB (by norm_num) k (fun j hj => yDig_lt (hall j hj) (bDig_aWord_lt hk X m j)) i i.isLt]
      simp only [yDig]
      rw [digit_aWord X m i.isLt,
        col_third (pick_lt _ _ _) (bDig_aWord_lt hk X m i)
          (by rw [← digit_aWord X m i.isLt]; exact hall i i.isLt)]

end ZigzagRing
end Mettapedia.GraphTheory.FourColor
