/-!
# Fields of a word

A word is a natural number below `2 ^ W`. The `n`-bit field at bit `s` is
read by `get` and replaced by `set`, both defined arithmetically. One lemma
describes every bit of `set` (`testBit_set`); the field laws follow from it:
reading after writing returns the value, writing what was read changes
nothing, a second write wins, and writing one field leaves every disjoint
field as it was.

`pack` writes a list of values into a list of slots and `unpack` reads them
back. For pairwise disjoint slots, unpacking a packing returns the values,
and when the slots also cover the word, packing an unpacking returns the
word. These are the laws a layout's fields obey; `LayoutCodes` builds the
layouts on them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutAlgebra

open Nat

/-! ## One field -/

/-- The `n`-bit field at bit `s` of `w`. -/
def get (w s n : Nat) : Nat := w / 2 ^ s % 2 ^ n

/-- `w` with its `n`-bit field at bit `s` replaced by `v`, reduced to `n` bits. -/
def set (w s n v : Nat) : Nat :=
  2 ^ (s + n) * (w / 2 ^ (s + n)) + (2 ^ s * (v % 2 ^ n) + w % 2 ^ s)

theorem testBit_get (w s n j : Nat) :
    (get w s n).testBit j = (decide (j < n) && w.testBit (j + s)) := by
  unfold get
  rw [testBit_mod_two_pow, testBit_div_two_pow]

theorem get_lt (w s n : Nat) : get w s n < 2 ^ n :=
  Nat.mod_lt _ (Nat.two_pow_pos n)

private theorem low_lt (w s n v : Nat) : 2 ^ s * (v % 2 ^ n) + w % 2 ^ s < 2 ^ (s + n) := by
  have hv : v % 2 ^ n + 1 ≤ 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hw : w % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
  have : 2 ^ s * (v % 2 ^ n + 1) ≤ 2 ^ s * 2 ^ n := Nat.mul_le_mul_left _ hv
  rw [Nat.pow_add]
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-- Every bit of `set`: below the field it is `w`'s, inside it is `v`'s,
above it is `w`'s again. -/
theorem testBit_set (w s n v j : Nat) :
    (set w s n v).testBit j =
      if j < s then w.testBit j else if j < s + n then v.testBit (j - s) else w.testBit j := by
  unfold set
  rw [testBit_two_pow_mul_add _ (low_lt w s n v)]
  by_cases h1 : j < s
  · have h2 : j < s + n := by omega
    rw [if_pos h2, testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos s)), if_pos h1,
      testBit_mod_two_pow, if_pos h1]
    simp [h1]
  · rw [if_neg h1]
    by_cases h2 : j < s + n
    · rw [if_pos h2, if_pos h2, testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos s)),
        if_neg h1, testBit_mod_two_pow]
      have : j - s < n := by omega
      simp [this]
    · rw [if_neg h2, if_neg h2, testBit_div_two_pow]
      congr 1
      omega

theorem get_set (w s n v : Nat) : get (set w s n v) s n = v % 2 ^ n := by
  apply eq_of_testBit_eq
  intro j
  rw [testBit_get, testBit_set, testBit_mod_two_pow]
  by_cases h : j < n
  · have h1 : ¬ j + s < s := by omega
    have h2 : j + s < s + n := by omega
    simp [h, h1, h2]
  · simp [h]

theorem set_get (w s n : Nat) : set w s n (get w s n) = w := by
  apply eq_of_testBit_eq
  intro j
  rw [testBit_set]
  by_cases h1 : j < s
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : j < s + n
    · rw [if_pos h2, testBit_get]
      have : j - s < n := by omega
      simp only [this, decide_true, Bool.true_and]
      congr 1
      omega
    · rw [if_neg h2]

theorem set_set (w s n v u : Nat) : set (set w s n v) s n u = set w s n u := by
  apply eq_of_testBit_eq
  intro j
  rw [testBit_set, testBit_set, testBit_set]
  by_cases h1 : j < s
  · simp [h1]
  · by_cases h2 : j < s + n <;> simp [h1, h2]

/-- Two fields are disjoint when one ends where or before the other begins. -/
def Disjoint (s n t m : Nat) : Prop := s + n ≤ t ∨ t + m ≤ s

theorem get_set_other {w s n v t m : Nat} (h : Disjoint s n t m) :
    get (set w s n v) t m = get w t m := by
  apply eq_of_testBit_eq
  intro j
  rw [testBit_get, testBit_get, testBit_set]
  by_cases hj : j < m
  · unfold Disjoint at h
    by_cases h1 : j + t < s
    · simp [hj, h1]
    · have h2 : ¬ j + t < s + n := by omega
      simp [hj, h1, h2]
  · simp [hj]

theorem set_comm {w s n v t m u : Nat} (h : Disjoint s n t m) :
    set (set w s n v) t m u = set (set w t m u) s n v := by
  apply eq_of_testBit_eq
  intro j
  simp only [testBit_set]
  unfold Disjoint at h
  by_cases a : j < s <;> by_cases b : j < s + n <;> by_cases c : j < t <;>
    by_cases d : j < t + m <;> simp [a, b, c, d] <;> omega

/-- Writing a field that lies inside the word keeps the word inside it. -/
theorem set_lt {w s n v W : Nat} (hw : w < 2 ^ W) (hf : s + n ≤ W) : set w s n v < 2 ^ W := by
  apply lt_pow_two_of_testBit
  intro i hi
  rw [testBit_set]
  have h1 : ¬ i < s := by omega
  have h2 : ¬ i < s + n := by omega
  rw [if_neg h1, if_neg h2]
  exact testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hi))

/-- The field in C's spelling: shift right, then mask. -/
theorem get_eq_shift_mask (w s n : Nat) : get w s n = (w >>> s) &&& (2 ^ n - 1) := by
  rw [and_two_pow_sub_one_eq_mod, shiftRight_eq_div_pow]
  rfl

/-! ## Slots -/

/-- A place for one field: its first bit and its width. -/
structure Slot where
  shift : Nat
  width : Nat
deriving DecidableEq, Repr

namespace Slot

/-- Bit `j` lies in the slot. -/
def holds (s : Slot) (j : Nat) : Bool := decide (s.shift ≤ j ∧ j < s.shift + s.width)

def disjoint (a b : Slot) : Bool := decide (a.shift + a.width ≤ b.shift ∨ b.shift + b.width ≤ a.shift)

theorem disjoint_spec {a b : Slot} (h : a.disjoint b = true) :
    Disjoint a.shift a.width b.shift b.width := by
  unfold disjoint at h
  unfold Disjoint
  exact of_decide_eq_true h

theorem not_holds_of_disjoint {a b : Slot} (h : a.disjoint b = true) {j : Nat}
    (ha : a.holds j = true) : b.holds j = false := by
  unfold disjoint at h
  unfold holds at *
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

end Slot

/-- Every slot is disjoint from every later one. -/
def pairwiseDisjoint : List Slot → Bool
  | [] => true
  | s :: rest => rest.all s.disjoint && pairwiseDisjoint rest

/-- Write the values into the slots of `base`, in order. -/
def pack : List Slot → List Nat → Nat → Nat
  | s :: slots, v :: values, base => pack slots values (set base s.shift s.width v)
  | _, _, base => base

/-- Read every slot. -/
def unpack (slots : List Slot) (w : Nat) : List Nat :=
  slots.map fun s => get w s.shift s.width

/-- The slot holding bit `j`, with the value written there. -/
def lookup : List Slot → List Nat → Nat → Option (Slot × Nat)
  | s :: slots, v :: values, j => if s.holds j then some (s, v) else lookup slots values j
  | _, _, _ => none

theorem lookup_none_of_disjoint {s : Slot} {j : Nat} (hj : s.holds j = true) :
    ∀ (slots : List Slot) (values : List Nat), slots.all s.disjoint = true →
      lookup slots values j = none
  | [], _, _ => by simp [lookup]
  | _ :: _, [], _ => by simp [lookup]
  | t :: slots, v :: values, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      have ht : t.holds j = false := Slot.not_holds_of_disjoint h.1 hj
      simp only [lookup, ht]
      exact lookup_none_of_disjoint hj slots values h.2

/-- Every bit of a packing: the value of the slot holding it, or the base. -/
theorem testBit_pack : ∀ (slots : List Slot) (values : List Nat) (base j : Nat),
    pairwiseDisjoint slots = true →
      (pack slots values base).testBit j =
        match lookup slots values j with
        | some (s, v) => v.testBit (j - s.shift)
        | none => base.testBit j
  | [], _, base, j, _ => by simp [pack, lookup]
  | _ :: _, [], base, j, _ => by simp [pack, lookup]
  | s :: slots, v :: values, base, j, h => by
      simp only [pairwiseDisjoint, Bool.and_eq_true] at h
      simp only [pack, lookup]
      rw [testBit_pack slots values _ j h.2]
      by_cases hj : s.holds j = true
      · rw [lookup_none_of_disjoint hj slots values h.1, if_pos hj, testBit_set]
        unfold Slot.holds at hj
        have h1 : ¬ j < s.shift := by simp at hj; omega
        have h2 : j < s.shift + s.width := by simp at hj; omega
        simp [h1, h2]
      · rw [if_neg hj]
        cases hl : lookup slots values j with
        | some p => rfl
        | none =>
            simp only
            rw [testBit_set]
            unfold Slot.holds at hj
            simp only [decide_eq_true_eq, not_and, Nat.not_lt] at hj
            by_cases h1 : j < s.shift
            · simp [h1]
            · have h2 : ¬ j < s.shift + s.width := by have := hj (by omega); omega
              simp [h1, h2]

/-- A field outside every slot keeps the base's value. -/
theorem get_pack_other {t : Slot} : ∀ (slots : List Slot) (values : List Nat) (base : Nat),
    slots.all t.disjoint = true →
      get (pack slots values base) t.shift t.width = get base t.shift t.width
  | [], _, _, _ => by simp [pack]
  | _ :: _, [], _, _ => by simp [pack]
  | s :: slots, v :: values, base, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [pack]
      rw [get_pack_other slots values _ h.2]
      have hd := Slot.disjoint_spec h.1
      exact get_set_other (by unfold Disjoint at hd ⊢; omega)

/-- Unpacking a packing returns the values, when each fits its slot. -/
theorem unpack_pack : ∀ (slots : List Slot) (values : List Nat) (base : Nat),
    pairwiseDisjoint slots = true → values.length = slots.length →
      (∀ p ∈ slots.zip values, p.2 < 2 ^ p.1.width) →
      unpack slots (pack slots values base) = values
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | s :: slots, v :: values, base, h, hl, hv => by
      simp only [pairwiseDisjoint, Bool.and_eq_true] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [unpack, List.map_cons, pack]
      have hfit : v < 2 ^ s.width := hv (s, v) (by simp)
      have hrest : ∀ p ∈ slots.zip values, p.2 < 2 ^ p.1.width :=
        fun p hp => hv p (by simp [hp])
      have hs : get (pack slots values (set base s.shift s.width v)) s.shift s.width = v := by
        rw [get_pack_other slots values _ h.1, get_set, Nat.mod_eq_of_lt hfit]
      rw [hs]
      have := unpack_pack slots values (set base s.shift s.width v) h.2 hl hrest
      unfold unpack at this
      rw [this]

/-- Every bit below `r` lies in some slot. -/
def covers (slots : List Slot) (r : Nat) : Bool :=
  (List.range r).all fun j => slots.any fun s => s.holds j

/-- Every slot lies below `r`. -/
def inside (slots : List Slot) (r : Nat) : Bool := slots.all fun s => decide (s.shift + s.width ≤ r)

theorem lookup_unpack_some : ∀ (slots : List Slot) (w j : Nat),
    slots.any (fun s => s.holds j) = true →
      ∃ s, s.holds j = true ∧ lookup slots (unpack slots w) j = some (s, get w s.shift s.width)
  | [], _, _, h => by simp at h
  | s :: slots, w, j, h => by
      simp only [unpack, List.map_cons, lookup]
      by_cases hj : s.holds j = true
      · exact ⟨s, hj, by rw [if_pos hj]⟩
      · rw [if_neg hj]
        simp only [List.any_cons, hj, Bool.false_or] at h
        exact lookup_unpack_some slots w j h

theorem lookup_unpack_none : ∀ (slots : List Slot) (w j : Nat),
    slots.any (fun s => s.holds j) = false → lookup slots (unpack slots w) j = none
  | [], _, _, _ => rfl
  | s :: slots, w, j, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      simp only [unpack, List.map_cons, lookup, h.1]
      exact lookup_unpack_none slots w j h.2

/-- Packing an unpacking returns the word, when the slots tile it. -/
theorem pack_unpack {slots : List Slot} {r w : Nat} (hd : pairwiseDisjoint slots = true)
    (hc : covers slots r = true) (hw : w < 2 ^ r) :
    pack slots (unpack slots w) 0 = w := by
  apply eq_of_testBit_eq
  intro j
  rw [testBit_pack slots _ 0 j hd]
  cases hany : slots.any (fun s => s.holds j) with
  | true =>
      obtain ⟨s, hs, hl⟩ := lookup_unpack_some slots w j hany
      rw [hl]
      dsimp only
      rw [testBit_get]
      unfold Slot.holds at hs
      simp only [decide_eq_true_eq] at hs
      have h1 : j - s.shift < s.width := by omega
      simp only [h1, decide_true, Bool.true_and]
      congr 1
      omega
  | false =>
      rw [lookup_unpack_none slots w j hany]
      dsimp only
      rw [Nat.zero_testBit]
      have hj : ¬ j < r := by
        intro hj
        unfold covers at hc
        rw [List.all_eq_true] at hc
        have := hc j (List.mem_range.mpr hj)
        rw [hany] at this
        exact Bool.false_ne_true this
      exact (testBit_lt_two_pow (Nat.lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by omega) (by omega)))).symm

/-- A packing into slots inside `r` stays below `2 ^ r`. -/
theorem pack_lt : ∀ (slots : List Slot) (values : List Nat) {base r : Nat},
    inside slots r = true → base < 2 ^ r → pack slots values base < 2 ^ r
  | [], _, _, _, _, hb => hb
  | _ :: _, [], _, _, _, hb => hb
  | s :: slots, v :: values, base, r, hi, hb => by
      simp only [inside, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact pack_lt slots values hi.2 (set_lt hb hi.1)

/-! ## Examples -/

/-- The bloom field of CeTTa's atom flags: 22 bits at bit 9. -/
example : get (set 0 9 22 5) 9 22 = 5 := by decide
example : get (set 0x80000000 9 22 0x3FFFFF) 31 1 = 1 := by decide
/-- Writing the bloom never disturbs the evaluated mark at bit 31. -/
example (w v : Nat) : get (set w 9 22 v) 31 1 = get w 31 1 := get_set_other (by unfold Disjoint; omega)
/-- A slot list that overlaps is refused. -/
example : pairwiseDisjoint [⟨9, 22⟩, ⟨30, 2⟩] = false := by decide
/-- A slot list that leaves bit 8 uncovered does not tile 32 bits. -/
example : covers [⟨0, 8⟩, ⟨9, 23⟩] 32 = false := by decide
example : covers [⟨0, 9⟩, ⟨9, 22⟩, ⟨31, 1⟩] 32 = true := by decide

end Mettapedia.GSLT.LanguageDef.LayoutAlgebra
