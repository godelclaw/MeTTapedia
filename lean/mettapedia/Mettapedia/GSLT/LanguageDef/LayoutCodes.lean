import Mettapedia.GSLT.LanguageDef.LayoutAlgebra

/-!
# Layouts: values presented in words

A layout presents a value, a list of natural numbers, in a word of `width`
bits. The top bits of the word select a case through a binary trie, so the
case prefixes are prefix-free and every word selects exactly one case. A case
places each field of the value in a slot of the remaining bits, storing the
value minus an offset, and admits the values between its bounds. A reserved
case admits none.

Three readings of a word:
- `parts` reads every word, as C code that decodes without checking does;
- `decode` reads only words whose case admits the value read;
- `encode` writes a value in the first case that admits it.

`wellFormed` is a Boolean check the kernel decides for a concrete layout.
When it holds:
- `decode_encode`: a written value reads back;
- `encode_decode` (canonicity): a word that reads as a value is the word that
  value is written as, so every valid value has exactly one word;
- `parts_injective`: distinct words have distinct total readings.

The check asks that the trie fits the word, that each case's slots tile the
bits below its prefix, that each case's bounds fit its slots, that the
bounds of two admitting cases are apart in some field, and that the slot
ranges of any two cases are apart in some field.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutCodes

open Nat
open Mettapedia.GSLT.LanguageDef.LayoutAlgebra

/-! ## Cases -/

/-- One field's place: its slot, the offset subtracted before storing, and the
inclusive bounds of the values a case admits. -/
structure Place where
  slot : Slot
  offset : Nat
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

structure Case where
  places : List Place
  reserved : Bool
deriving DecidableEq, Repr

def slotsOf (places : List Place) : List Slot := places.map Place.slot

/-- Read every field, adding its offset back. -/
def readPlaces (places : List Place) (low : Nat) : List Nat :=
  places.map fun p => get low p.slot.shift p.slot.width + p.offset

/-- The stored form of a value: each field minus its offset. -/
def storePlaces : List Place → List Nat → List Nat
  | p :: ps, x :: xs => (x - p.offset) :: storePlaces ps xs
  | _, _ => []

/-- Each field lies within its bounds, and there is one field per place. -/
def within : List Place → List Nat → Bool
  | p :: ps, x :: xs => decide (p.lo ≤ x ∧ x ≤ p.hi) && within ps xs
  | [], [] => true
  | _, _ => false

/-- Some field's bounds are apart. -/
def apart : List Place → List Place → Bool
  | p :: ps, q :: qs => decide (p.hi < q.lo ∨ q.hi < p.lo) || apart ps qs
  | _, _ => false

/-- Some field's stored ranges are apart. -/
def rangesApart : List Place → List Place → Bool
  | p :: ps, q :: qs =>
      decide (p.offset + 2 ^ p.slot.width ≤ q.offset ∨ q.offset + 2 ^ q.slot.width ≤ p.offset) ||
        rangesApart ps qs
  | _, _ => false

namespace Case

def admits (c : Case) (v : List Nat) : Bool := !c.reserved && within c.places v

/-- The slots tile the `r` bits below the prefix. -/
def tiles (c : Case) (r : Nat) : Bool :=
  pairwiseDisjoint (slotsOf c.places) && covers (slotsOf c.places) r && inside (slotsOf c.places) r

/-- The admitted values fit their slots. -/
def fits (c : Case) : Bool :=
  c.reserved || c.places.all fun p => decide (p.offset ≤ p.lo ∧ p.hi < p.offset + 2 ^ p.slot.width)

end Case

/-! ## Field lemmas -/

theorem length_readPlaces (ps : List Place) (low : Nat) : (readPlaces ps low).length = ps.length := by
  simp [readPlaces]

theorem length_storePlaces : ∀ (ps : List Place) (v : List Nat), v.length = ps.length →
    (storePlaces ps v).length = ps.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: ps, _ :: v, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [storePlaces, length_storePlaces ps v h]

theorem length_of_within : ∀ (ps : List Place) (v : List Nat), within ps v = true → v.length = ps.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [within] at h
  | _ :: _, [], h => by simp [within] at h
  | _ :: ps, _ :: v, h => by
      simp only [within, Bool.and_eq_true] at h
      simp [length_of_within ps v h.2]

theorem readPlaces_eq (ps : List Place) (low : Nat) :
    readPlaces ps low = List.zipWith (fun p g => g + p.offset) ps (unpack (slotsOf ps) low) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [readPlaces, unpack, slotsOf] at ih ⊢; exact ih

theorem storePlaces_readPlaces : ∀ (ps : List Place) (low : Nat),
    storePlaces ps (readPlaces ps low) = unpack (slotsOf ps) low
  | [], _ => rfl
  | p :: ps, low => by
      have := storePlaces_readPlaces ps low
      simp only [readPlaces, List.map_cons, storePlaces, Nat.add_sub_cancel, unpack, slotsOf] at this ⊢
      rw [this]

theorem readPlaces_of_unpack : ∀ (ps : List Place) (v : List Nat) (low : Nat),
    within ps v = true → (∀ p ∈ ps, p.offset ≤ p.lo) →
      unpack (slotsOf ps) low = storePlaces ps v → readPlaces ps low = v
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp [within] at h
  | _ :: _, [], _, h, _, _ => by simp [within] at h
  | p :: ps, x :: v, low, h, ho, hu => by
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [unpack, slotsOf, List.map_cons, storePlaces, List.cons.injEq] at hu
      have hp : p.offset ≤ p.lo := ho p (by simp)
      have := readPlaces_of_unpack ps v low h.2 (fun q hq => ho q (by simp [hq])) hu.2
      simp only [readPlaces, List.map_cons] at this ⊢
      rw [hu.1, this]
      congr 1
      omega

theorem zip_storePlaces : ∀ (ps : List Place) (v : List Nat),
    within ps v = true → (∀ p ∈ ps, p.offset ≤ p.lo ∧ p.hi < p.offset + 2 ^ p.slot.width) →
      ∀ q ∈ (slotsOf ps).zip (storePlaces ps v), q.2 < 2 ^ q.1.width
  | [], _, _, _, q, hq => by simp [slotsOf] at hq
  | _ :: _, [], h, _, _, _ => by simp [within] at h
  | p :: ps, x :: v, h, hf, q, hq => by
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [slotsOf, List.map_cons, storePlaces, List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst hq
        have := hf p (by simp)
        simp only
        omega
      · exact zip_storePlaces ps v h.2 (fun r hr => hf r (by simp [hr])) q hq

theorem not_within_both : ∀ (ps qs : List Place) (v : List Nat),
    apart ps qs = true → within ps v = true → within qs v = true → False
  | [], _, _, h, _, _ => by simp [apart] at h
  | _ :: _, [], _, h, _, _ => by simp [apart] at h
  | _ :: _, _ :: _, [], _, h, _ => by simp [within] at h
  | p :: ps, q :: qs, x :: v, ha, hp, hq => by
      simp only [apart, Bool.or_eq_true, decide_eq_true_eq] at ha
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at hp hq
      rcases ha with ha | ha
      · omega
      · exact not_within_both ps qs v ha hp.2 hq.2

theorem readPlaces_ne : ∀ (ps qs : List Place) (a b : Nat),
    rangesApart ps qs = true → readPlaces ps a ≠ readPlaces qs b
  | [], _, _, _, h => by simp [rangesApart] at h
  | _ :: _, [], _, _, h => by simp [rangesApart] at h
  | p :: ps, q :: qs, a, b, h => by
      simp only [rangesApart, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [readPlaces, List.map_cons, ne_eq, List.cons.injEq, not_and]
      intro he
      have ha := get_lt a p.slot.shift p.slot.width
      have hb := get_lt b q.slot.shift q.slot.width
      rcases h with (h | h) | h
      · omega
      · omega
      · exact readPlaces_ne ps qs a b h

/-! ## Tries -/

inductive Trie where
  | leaf (c : Case)
  | node (zero one : Trie)
deriving Repr

namespace Trie

def depth : Trie → Nat
  | .leaf _ => 0
  | .node z o => max z.depth o.depth + 1

/-- Every case with its prefix: the value of its path and the path's length. -/
def leaves : Trie → List (Case × Nat × Nat)
  | .leaf c => [(c, 0, 0)]
  | .node z o =>
      (z.leaves.map fun l => (l.1, l.2.1, l.2.2 + 1)) ++
        (o.leaves.map fun l => (l.1, 2 ^ l.2.2 + l.2.1, l.2.2 + 1))

/-- The case a word of `bits` bits selects, read from its top bit down. -/
def locate : Trie → Nat → Nat → Case × Nat × Nat
  | .leaf c, _, _ => (c, 0, 0)
  | .node z o, bits, w =>
      if w / 2 ^ (bits - 1) = 0 then
        let r := z.locate (bits - 1) (w % 2 ^ (bits - 1))
        (r.1, r.2.1, r.2.2 + 1)
      else
        let r := o.locate (bits - 1) (w % 2 ^ (bits - 1))
        (r.1, 2 ^ r.2.2 + r.2.1, r.2.2 + 1)

theorem leaves_spec : ∀ (t : Trie) (l : Case × Nat × Nat), l ∈ t.leaves →
    l.2.1 < 2 ^ l.2.2 ∧ l.2.2 ≤ t.depth
  | .leaf c, l, h => by simp [leaves] at h; subst h; simp [depth]
  | .node z o, l, h => by
      simp only [leaves, List.mem_append, List.mem_map] at h
      rcases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
      · have := leaves_spec z m hm
        refine ⟨?_, ?_⟩
        · simp only
          have : 2 ^ m.2.2 ≤ 2 ^ (m.2.2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        · simp only [depth]; omega
      · have := leaves_spec o m hm
        refine ⟨?_, ?_⟩
        · simp only [Nat.pow_succ]; omega
        · simp only [depth]; omega

private theorem split_pow {d k : Nat} (h : d ≤ k) : 2 ^ k = 2 ^ d * 2 ^ (k - d) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- The case `locate` finds is a leaf, and the word is its prefix followed by
the bits below. -/
theorem locate_spec : ∀ (t : Trie) (bits w : Nat), t.depth ≤ bits → w < 2 ^ bits →
    t.locate bits w ∈ t.leaves ∧ (t.locate bits w).2.2 ≤ bits ∧
      w = (t.locate bits w).2.1 * 2 ^ (bits - (t.locate bits w).2.2) +
        w % 2 ^ (bits - (t.locate bits w).2.2)
  | .leaf c, bits, w, _, hw => by
      simp [locate, leaves, Nat.mod_eq_of_lt hw]
  | .node z o, bits, w, hd, hw => by
      simp only [depth] at hd
      obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
      simp only [locate, Nat.add_sub_cancel]
      have hb : w / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]; rw [Nat.pow_succ] at hw; omega
      have hw' : w % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hsplit : w = 2 ^ k * (w / 2 ^ k) + w % 2 ^ k := (Nat.div_add_mod w (2 ^ k)).symm
      by_cases h0 : w / 2 ^ k = 0
      · rw [if_pos h0]
        obtain ⟨hm, hdk, hweq⟩ := locate_spec z k (w % 2 ^ k) (by omega) hw'
        generalize z.locate k (w % 2 ^ k) = r at hm hdk hweq ⊢
        refine ⟨?_, by simp only; omega, ?_⟩
        · simp only [leaves, List.mem_append, List.mem_map]
          exact Or.inl ⟨r, hm, rfl⟩
        · have hwk : w % 2 ^ k = w := by
            rw [h0, Nat.mul_zero, Nat.zero_add] at hsplit; exact hsplit.symm
          rw [hwk] at hweq
          simp only
          have : k + 1 - (r.2.2 + 1) = k - r.2.2 := by omega
          rw [this]
          exact hweq
      · rw [if_neg h0]
        have h1 : w / 2 ^ k = 1 := by
          generalize w / 2 ^ k = q at hb h0 ⊢; omega
        have hw1 : w = 2 ^ k + w % 2 ^ k := by rw [h1, Nat.mul_one] at hsplit; exact hsplit
        obtain ⟨hm, hdk, hweq⟩ := locate_spec o k (w % 2 ^ k) (by omega) hw'
        generalize o.locate k (w % 2 ^ k) = r at hm hdk hweq ⊢
        refine ⟨?_, by simp only; omega, ?_⟩
        · simp only [leaves, List.mem_append, List.mem_map]
          exact Or.inr ⟨r, hm, rfl⟩
        · simp only
          have : k + 1 - (r.2.2 + 1) = k - r.2.2 := by omega
          rw [this]
          have hp := split_pow hdk
          have hmod : w % 2 ^ (k - r.2.2) = w % 2 ^ k % 2 ^ (k - r.2.2) := by
            rw [Nat.mod_mod_of_dvd]
            exact ⟨2 ^ r.2.2, by rw [hp, Nat.mul_comm]⟩
          have hx : 2 ^ r.2.2 * 2 ^ (k - r.2.2) = 2 ^ k := hp.symm
          rw [hmod, Nat.add_mul]
          omega

/-- A word made of a leaf's prefix and bits below it selects that leaf. -/
theorem locate_leaf : ∀ (t : Trie) (bits : Nat) (l : Case × Nat × Nat) (low : Nat),
    l ∈ t.leaves → t.depth ≤ bits → low < 2 ^ (bits - l.2.2) →
      t.locate bits (l.2.1 * 2 ^ (bits - l.2.2) + low) = l
  | .leaf c, bits, l, low, h, _, _ => by simp [leaves] at h; subst h; simp [locate]
  | .node z o, bits, l, low, h, hd, hl => by
      simp only [depth] at hd
      obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
      simp only [locate, Nat.add_sub_cancel]
      simp only [leaves, List.mem_append, List.mem_map] at h
      rcases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
      · obtain ⟨hp, hdm⟩ := leaves_spec z m hm
        simp only at hl ⊢
        have he : k + 1 - (m.2.2 + 1) = k - m.2.2 := by omega
        rw [he] at hl ⊢
        have hs := split_pow (d := m.2.2) (k := k) (by omega)
        have hlt : m.2.1 * 2 ^ (k - m.2.2) + low < 2 ^ k := by
          have : (m.2.1 + 1) * 2 ^ (k - m.2.2) ≤ 2 ^ m.2.2 * 2 ^ (k - m.2.2) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        have h0 : (m.2.1 * 2 ^ (k - m.2.2) + low) / 2 ^ k = 0 := Nat.div_eq_of_lt hlt
        rw [if_pos h0, Nat.mod_eq_of_lt hlt]
        simp only [locate_leaf z k m low hm (by omega) hl]
      · obtain ⟨hp, hdm⟩ := leaves_spec o m hm
        simp only at hl ⊢
        have he : k + 1 - (m.2.2 + 1) = k - m.2.2 := by omega
        rw [he] at hl ⊢
        have hs := split_pow (d := m.2.2) (k := k) (by omega)
        have hlt : m.2.1 * 2 ^ (k - m.2.2) + low < 2 ^ k := by
          have : (m.2.1 + 1) * 2 ^ (k - m.2.2) ≤ 2 ^ m.2.2 * 2 ^ (k - m.2.2) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        have hw : (2 ^ m.2.2 + m.2.1) * 2 ^ (k - m.2.2) + low =
            2 ^ k * 1 + (m.2.1 * 2 ^ (k - m.2.2) + low) := by
          rw [Nat.add_mul, ← hs]; omega
        have h1 : ((2 ^ m.2.2 + m.2.1) * 2 ^ (k - m.2.2) + low) / 2 ^ k = 1 := by
          rw [hw, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]
        have hmod : ((2 ^ m.2.2 + m.2.1) * 2 ^ (k - m.2.2) + low) % 2 ^ k =
            m.2.1 * 2 ^ (k - m.2.2) + low := by
          rw [hw, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
        rw [if_neg (by omega), hmod]
        simp only [locate_leaf o k m low hm (by omega) hl]

end Trie

/-! ## Codes -/

structure Code where
  width : Nat
  trie : Trie
deriving Repr

/-- Every pair of list elements, the earlier first, satisfies `R`. -/
def pairwiseB {α : Type} (R : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (R a) && pairwiseB R l

namespace Code

/-- Two cases can be told apart: their admitted values never meet, and their
total readings never meet. -/
def separated (a b : Case × Nat × Nat) : Bool :=
  (a.1.reserved || b.1.reserved || apart a.1.places b.1.places) &&
    rangesApart a.1.places b.1.places

def wellFormed (k : Code) : Bool :=
  decide (k.trie.depth ≤ k.width) &&
    k.trie.leaves.all (fun l => l.1.tiles (k.width - l.2.2) && l.1.fits) &&
    pairwiseB separated k.trie.leaves

/-- The total reading: what every word says, valid or not. -/
def parts (k : Code) (w : Nat) : List Nat :=
  let l := k.trie.locate k.width w
  readPlaces l.1.places (w % 2 ^ (k.width - l.2.2))

/-- The checked reading: a word of the code whose case admits what it says. -/
def decode (k : Code) (w : Nat) : Option (List Nat) :=
  if w < 2 ^ k.width && (k.trie.locate k.width w).1.admits (k.parts w) then some (k.parts w) else none

/-- The case a value is written in: the first that admits it. -/
def choose (k : Code) (v : List Nat) : Option (Case × Nat × Nat) :=
  k.trie.leaves.find? fun l => l.1.admits v

def encode (k : Code) (v : List Nat) : Option Nat :=
  (k.choose v).map fun l => l.2.1 * 2 ^ (k.width - l.2.2) + pack (slotsOf l.1.places) (storePlaces l.1.places v) 0

structure Facts (k : Code) : Prop where
  depth : k.trie.depth ≤ k.width
  leaf : ∀ l ∈ k.trie.leaves, l.1.tiles (k.width - l.2.2) = true ∧ l.1.fits = true
  separated : ∀ a ∈ k.trie.leaves, ∀ b ∈ k.trie.leaves, a ≠ b → separated a b = true

private theorem pairwiseB_spec {α : Type} [DecidableEq α] {R : α → α → Bool}
    (hsym : ∀ a b, R a b = R b a) :
    ∀ (l : List α), pairwiseB R l = true → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b = true
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: l, h, a, ha, b, hb, hab => by
      simp only [pairwiseB, Bool.and_eq_true, List.all_eq_true] at h
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact h.1 b hb
      · rw [hsym]; exact h.1 a ha
      · exact pairwiseB_spec hsym l h.2 a ha b hb hab

private theorem apart_symm : ∀ (ps qs : List Place), apart ps qs = apart qs ps
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, q :: qs => by
      simp only [apart, apart_symm ps qs]
      congr 1
      simp only [decide_eq_decide]
      omega

private theorem rangesApart_symm : ∀ (ps qs : List Place), rangesApart ps qs = rangesApart qs ps
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, q :: qs => by
      simp only [rangesApart, rangesApart_symm ps qs]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem separated_symm (a b : Case × Nat × Nat) : separated a b = separated b a := by
  unfold separated
  rw [apart_symm, rangesApart_symm]
  cases a.1.reserved <;> cases b.1.reserved <;> simp

/-- What `wellFormed` guarantees. -/
theorem facts_of_wellFormed {k : Code} (h : k.wellFormed = true) : k.Facts := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, pairwiseB_spec separated_symm _ h.2⟩

private theorem find?_unique {α : Type} {P : α → Bool} :
    ∀ (l : List α) (x : α), x ∈ l → P x = true → (∀ y ∈ l, P y = true → y = x) →
      l.find? P = some x
  | [], _, hx, _, _ => by simp at hx
  | a :: l, x, hx, hp, hu => by
      by_cases ha : P a = true
      · rw [List.find?_cons_of_pos ha, hu a (by simp) ha]
      · rw [List.find?_cons_of_neg ha]
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hp ha
        · exact find?_unique l x hx hp (fun y hy => hu y (by simp [hy]))

theorem choose_spec {k : Code} {v : List Nat} {l : Case × Nat × Nat} (h : k.choose v = some l) :
    l ∈ k.trie.leaves ∧ l.1.admits v = true := by
  unfold choose at h
  exact ⟨List.mem_of_find?_eq_some h, by have := List.find?_some h; simpa using this⟩

/-- Two different cases never admit the same value. -/
theorem admits_unique {k : Code} (hk : k.Facts) {a b : Case × Nat × Nat} (ha : a ∈ k.trie.leaves)
    (hb : b ∈ k.trie.leaves) {v : List Nat} (hav : a.1.admits v = true) (hbv : b.1.admits v = true) :
    a = b := by
  by_cases hab : a = b
  · exact hab
  exfalso
  have hs := hk.separated a ha b hb hab
  unfold separated at hs
  unfold Case.admits at hav hbv
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hs hav hbv
  rcases hs.1 with (h | h) | h
  · rw [hav.1] at h; exact Bool.false_ne_true h
  · rw [hbv.1] at h; exact Bool.false_ne_true h
  · exact not_within_both _ _ v h hav.2 hbv.2

private theorem lt_of_prefix {p d W low : Nat} (hp : p < 2 ^ d) (hd : d ≤ W) (hl : low < 2 ^ (W - d)) :
    p * 2 ^ (W - d) + low < 2 ^ W := by
  have hs : 2 ^ W = 2 ^ d * 2 ^ (W - d) := by rw [← Nat.pow_add]; congr 1; omega
  have : (p + 1) * 2 ^ (W - d) ≤ 2 ^ d * 2 ^ (W - d) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

private theorem prefix_mod {p d W low : Nat} (hl : low < 2 ^ (W - d)) :
    (p * 2 ^ (W - d) + low) % 2 ^ (W - d) = low := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- A written value reads back. -/
theorem decode_encode {k : Code} (hk : k.Facts) {v : List Nat} {w : Nat} (h : k.encode v = some w) :
    k.decode w = some v := by
  unfold encode at h
  cases hc : k.choose v with
  | none => rw [hc] at h; simp at h
  | some l =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hl, hadm⟩ := choose_spec hc
      obtain ⟨hp, hdl⟩ := Trie.leaves_spec _ l hl
      obtain ⟨ht, hf⟩ := hk.leaf l hl
      unfold Case.tiles at ht
      simp only [Bool.and_eq_true] at ht
      unfold Case.admits at hadm
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm
      unfold Case.fits at hf
      rw [hadm.1, Bool.false_or, List.all_eq_true] at hf
      have hfit : ∀ p ∈ l.1.places, p.offset ≤ p.lo ∧ p.hi < p.offset + 2 ^ p.slot.width :=
        fun p hp => of_decide_eq_true (hf p hp)
      have hd : l.2.2 ≤ k.width := Nat.le_trans hdl hk.depth
      have hlow : pack (slotsOf l.1.places) (storePlaces l.1.places v) 0 < 2 ^ (k.width - l.2.2) :=
        pack_lt _ _ ht.2 (Nat.two_pow_pos _)
      have hloc : k.trie.locate k.width w = l := by
        rw [← h]; exact Trie.locate_leaf _ _ l _ hl hk.depth hlow
      have hwlt : w < 2 ^ k.width := by rw [← h]; exact lt_of_prefix hp hd hlow
      have hparts : k.parts w = v := by
        unfold parts
        rw [hloc]
        simp only
        rw [← h, prefix_mod hlow]
        apply readPlaces_of_unpack _ v _ hadm.2 (fun p hp => (hfit p hp).1)
        apply unpack_pack _ _ _ ht.1.1
        · rw [slotsOf, List.length_map]
          exact length_storePlaces _ _ (length_of_within _ _ hadm.2)
        · exact zip_storePlaces _ _ hadm.2 hfit
      unfold decode
      rw [hparts, hloc]
      unfold Case.admits
      simp [hwlt, hadm.1, hadm.2]

/-- Canonicity: a word that reads as a value is the word that value is written as. -/
theorem encode_decode {k : Code} (hk : k.Facts) {v : List Nat} {w : Nat} (h : k.decode w = some v) :
    k.encode v = some w := by
  unfold decode at h
  split at h
  · rename_i hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨hwlt, hadm⟩ := hcond
    obtain ⟨hl, hdl, hweq⟩ := Trie.locate_spec k.trie k.width w hk.depth hwlt
    have hparts : k.parts w = readPlaces (k.trie.locate k.width w).1.places
        (w % 2 ^ (k.width - (k.trie.locate k.width w).2.2)) := rfl
    generalize hlr : k.trie.locate k.width w = l at hl hdl hweq hadm hparts
    have hchoose : k.choose (k.parts w) = some l := by
      unfold choose
      exact find?_unique _ l hl hadm (fun y hy hya => admits_unique hk hy hl hya hadm)
    obtain ⟨ht, _⟩ := hk.leaf l hl
    unfold Case.tiles at ht
    simp only [Bool.and_eq_true] at ht
    unfold encode
    rw [hchoose]
    simp only [Option.map_some, Option.some.injEq]
    have hstore : storePlaces l.1.places (k.parts w) = unpack (slotsOf l.1.places) (w % 2 ^ (k.width - l.2.2)) := by
      rw [hparts]
      exact storePlaces_readPlaces _ _
    rw [hstore, pack_unpack ht.1.1 ht.1.2 (Nat.mod_lt _ (Nat.two_pow_pos _))]
    exact hweq.symm
  · simp at h

/-- Distinct words of the code read as distinct values, valid or not. -/
theorem parts_injective {k : Code} (hk : k.Facts) {w w' : Nat} (hw : w < 2 ^ k.width)
    (hw' : w' < 2 ^ k.width) (h : k.parts w = k.parts w') : w = w' := by
  obtain ⟨hl, _, hweq⟩ := Trie.locate_spec k.trie k.width w hk.depth hw
  obtain ⟨hl', _, hweq'⟩ := Trie.locate_spec k.trie k.width w' hk.depth hw'
  have e1 : k.parts w = readPlaces (k.trie.locate k.width w).1.places
      (w % 2 ^ (k.width - (k.trie.locate k.width w).2.2)) := rfl
  have e2 : k.parts w' = readPlaces (k.trie.locate k.width w').1.places
      (w' % 2 ^ (k.width - (k.trie.locate k.width w').2.2)) := rfl
  generalize k.trie.locate k.width w = l at hl hweq e1
  generalize k.trie.locate k.width w' = l' at hl' hweq' e2
  by_cases hll : l = l'
  · subst hll
    have hu : unpack (slotsOf l.1.places) (w % 2 ^ (k.width - l.2.2)) =
        unpack (slotsOf l.1.places) (w' % 2 ^ (k.width - l.2.2)) := by
      rw [← storePlaces_readPlaces, ← storePlaces_readPlaces, ← e1, ← e2, h]
    obtain ⟨ht, _⟩ := hk.leaf l hl
    unfold Case.tiles at ht
    simp only [Bool.and_eq_true] at ht
    have hlow : w % 2 ^ (k.width - l.2.2) = w' % 2 ^ (k.width - l.2.2) := by
      rw [← pack_unpack ht.1.1 ht.1.2 (Nat.mod_lt w (Nat.two_pow_pos _)),
        ← pack_unpack ht.1.1 ht.1.2 (Nat.mod_lt w' (Nat.two_pow_pos _)), hu]
    rw [hweq, hweq', hlow]
  · exfalso
    have hs := hk.separated l hl l' hl' hll
    unfold separated at hs
    simp only [Bool.and_eq_true] at hs
    apply readPlaces_ne _ _ (w % 2 ^ (k.width - l.2.2)) (w' % 2 ^ (k.width - l'.2.2)) hs.2
    rw [← e1, ← e2, h]

/-- The checked reading agrees with the total one wherever it is defined. -/
theorem decode_parts {k : Code} {w : Nat} {v : List Nat} (h : k.decode w = some v) : k.parts w = v := by
  unfold decode at h
  split at h
  · simpa using h
  · simp at h

end Code

/-! ## Examples -/

/-- A one-case layout: two flags and a 6-bit count in a byte. -/
def byteFlags : Code :=
  ⟨8, .leaf ⟨[⟨⟨0, 1⟩, 0, 0, 1⟩, ⟨⟨1, 1⟩, 0, 0, 1⟩, ⟨⟨2, 6⟩, 0, 0, 63⟩], false⟩⟩

example : byteFlags.wellFormed = true := by decide
example : byteFlags.encode [1, 0, 5] = some 21 := by decide
example : byteFlags.decode 21 = some [1, 0, 5] := by decide
/-- A count too large for its slot has no word. -/
example : byteFlags.encode [1, 0, 64] = none := by decide

/-- Overlapping slots are refused. -/
example : (Code.mk 8 (.leaf ⟨[⟨⟨0, 2⟩, 0, 0, 3⟩, ⟨⟨1, 7⟩, 0, 0, 127⟩], false⟩)).wellFormed = false := by
  decide

/-- A bit no slot covers is refused: its value would be lost. -/
example : (Code.mk 8 (.leaf ⟨[⟨⟨0, 1⟩, 0, 0, 1⟩, ⟨⟨2, 6⟩, 0, 0, 63⟩], false⟩)).wellFormed = false := by
  decide

/-- Bounds that overflow the slot are refused. -/
example : (Code.mk 8 (.leaf ⟨[⟨⟨0, 2⟩, 0, 0, 4⟩, ⟨⟨2, 6⟩, 0, 0, 63⟩], false⟩)).wellFormed = false := by
  decide

/-- Two cases whose readings can meet are refused: here both read field 0
from the same range. -/
example : (Code.mk 8 (.node (.leaf ⟨[⟨⟨0, 7⟩, 0, 0, 127⟩], false⟩)
    (.leaf ⟨[⟨⟨0, 7⟩, 0, 0, 127⟩], false⟩))).wellFormed = false := by
  decide

end Mettapedia.GSLT.LanguageDef.LayoutCodes
