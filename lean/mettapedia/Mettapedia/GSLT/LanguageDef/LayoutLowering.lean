import Mettapedia.GSLT.LanguageDef.LayoutKinds

/-!
# Layout accessors as C expressions

Cesta writes a layout's accessors as `static inline` C functions whose body is
one expression over `uint64_t`: parameters, constants, `&`, `|`, `~`, shifts
by constant counts, `+`, `-`, `==`, `<=` and `?:`. `Expr` is that expression
language and `eval` its meaning: unsigned 64-bit arithmetic, with a shift by
64 or more undefined (`none`). The generated arithmetic and shift operands
use `uint64_t` (a narrower word parameter is converted first); the printer
casts each comparison's `int` result back to `uint64_t`, so every recorded
expression node has an unsigned 64-bit result.
The generic interpreter does not itself prove the typing or printing of
arbitrary C expressions.

The lowering builds each accessor from the layout. The theorems state, for
every well-formed layout, what each accessor computes:
- `eval_part`: the total reading of a field, `Code.parts`;
- `eval_valid`: whether the word decodes, `Code.decode`;
- `eval_encode`: the word a value is written as, `Code.encode`;
- `eval_set`: writing one field of a single-case word, `LayoutAlgebra.set`;
- the kind accessors: `derive` in steps, and the operations of `LayoutKinds`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutLowering

open Nat
open Mettapedia.GSLT.LanguageDef.LayoutAlgebra
open Mettapedia.GSLT.LanguageDef.LayoutCodes

/-! ## The expression language -/

inductive Expr where
  | var (index : Nat)
  | lit (value : Nat)
  | band (a b : Expr)
  | bor (a b : Expr)
  | bnot (a : Expr)
  | shl (a : Expr) (count : Nat)
  | shr (a : Expr) (count : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | eq (a b : Expr)
  | le (a b : Expr)
  | ite (c t e : Expr)
deriving DecidableEq, Repr

def top : Nat := 2 ^ 64

def lift2 (f : Nat → Nat → Nat) : Option Nat → Option Nat → Option Nat
  | some x, some y => some (f x y)
  | _, _ => none

@[simp] theorem lift2_some (f : Nat → Nat → Nat) (x y : Nat) : lift2 f (some x) (some y) = some (f x y) := rfl

def choose : Option Nat → Option Nat → Option Nat → Option Nat
  | some c, t, e => if c ≠ 0 then t else e
  | none, _, _ => none

@[simp] theorem choose_some (c : Nat) (t e : Option Nat) : choose (some c) t e = if c ≠ 0 then t else e := rfl

/-- C's meaning of the expression on `uint64_t` operands. -/
def eval (env : List Nat) : Expr → Option Nat
  | .var i => env[i]?
  | .lit n => if n < top then some n else none
  | .band a b => lift2 (· &&& ·) (eval env a) (eval env b)
  | .bor a b => lift2 (· ||| ·) (eval env a) (eval env b)
  | .bnot a => (eval env a).map ((top - 1) ^^^ ·)
  | .shl a n => if n < 64 then (eval env a).map (· * 2 ^ n % top) else none
  | .shr a n => if n < 64 then (eval env a).map (· / 2 ^ n) else none
  | .add a b => lift2 (fun x y => (x + y) % top) (eval env a) (eval env b)
  | .sub a b => lift2 (fun x y => (x + top - y) % top) (eval env a) (eval env b)
  | .eq a b => lift2 (fun x y => if x = y then 1 else 0) (eval env a) (eval env b)
  | .le a b => lift2 (fun x y => if x ≤ y then 1 else 0) (eval env a) (eval env b)
  | .ite c t e => choose (eval env c) (eval env t) (eval env e)

/-! ## Reading a field -/

/-- The `n`-bit field at `s` of `x`. -/
def fieldExpr (x : Expr) (s n : Nat) : Expr := .band (.shr x s) (.lit (2 ^ n - 1))

/-- A place's value, read from the word (parameter 0). -/
def readExpr (p : Place) : Expr :=
  if p.slot.width = 0 then .lit p.offset
  else .add (fieldExpr (.var 0) p.slot.shift p.slot.width) (.lit p.offset)

/-- A place is printable in 64 bits: a nonempty slot starts below bit 64 and
its values and bounds fit. An empty slot emits no shift, including at bit 64. -/
def fits64 (p : Place) : Bool :=
  decide ((p.slot.width = 0 ∨ p.slot.shift < 64) ∧ p.slot.width ≤ 64 ∧
    p.offset + 2 ^ p.slot.width ≤ top ∧ p.lo < top ∧ p.hi < top)

theorem get_mod {w s n r : Nat} (h : s + n ≤ r) :
    LayoutAlgebra.get (w % 2 ^ r) s n = LayoutAlgebra.get w s n := by
  apply eq_of_testBit_eq
  intro i
  rw [testBit_get, testBit_get, testBit_mod_two_pow]
  by_cases hi : i < n
  · have : i + s < r := by omega
    simp [hi, this]
  · simp [hi]

theorem mask_lt {n : Nat} (hn : n ≤ 64) : 2 ^ n - 1 < top := by
  unfold top
  have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hn
  have : 0 < 2 ^ n := Nat.two_pow_pos n
  omega

theorem eval_field {env : List Nat} {x : Expr} {w s n : Nat} (hx : eval env x = some w) (hs : s < 64)
    (hn : n ≤ 64) : eval env (fieldExpr x s n) = some (LayoutAlgebra.get w s n) := by
  simp [fieldExpr, eval, hx, hs, mask_lt hn, LayoutAlgebra.get_eq_shift_mask, shiftRight_eq_div_pow]

theorem eval_read {env : List Nat} {w : Nat} (hw : env[0]? = some w) {p : Place} (hp : fits64 p = true) :
    eval env (readExpr p) = some (LayoutAlgebra.get w p.slot.shift p.slot.width + p.offset) := by
  unfold fits64 at hp
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hs, hn, hoff, _, _⟩ := hp
  have hlit : p.offset < top := by
    have : 0 < 2 ^ p.slot.width := Nat.two_pow_pos _
    omega
  unfold readExpr
  split
  · rename_i h0
    have : LayoutAlgebra.get w p.slot.shift p.slot.width = 0 := by
      unfold LayoutAlgebra.get; rw [h0, Nat.pow_zero, Nat.mod_one]
    simp [eval, this, hlit]
  · rename_i h0
    have hs : p.slot.shift < 64 := hs.resolve_left h0
    have hg := LayoutAlgebra.get_lt w p.slot.shift p.slot.width
    simp only [eval, eval_field (env := env) (x := .var 0) (w := w) hw hs hn, hlit, if_true, lift2_some,
      Option.some.injEq]
    exact Nat.mod_eq_of_lt (by omega)

/-! ## Dispatch through the prefix -/

/-- 1 when bit `W - 1 - d` of the word is clear. -/
def bitClear (W d : Nat) : Expr := .eq (.band (.shr (.var 0) (W - 1 - d)) (.lit 1)) (.lit 0)

/-- An expression per case, chosen by the prefix bits of the word. -/
def walk (W : Nat) (leafExpr : Case → Expr) : Trie → Nat → Expr
  | .leaf c, _ => leafExpr c
  | .node z o, d => .ite (bitClear W d) (walk W leafExpr z (d + 1)) (walk W leafExpr o (d + 1))

/-- What a dispatch means: `f` of the case the word selects, on the bits below
its prefix. -/
def walkAt (f : Case → Nat → Nat) (t : Trie) (bits w : Nat) : Nat :=
  f (t.locate bits w).1 (w % 2 ^ (bits - (t.locate bits w).2.2))

theorem eval_walk (W : Nat) (hW : W ≤ 64) (leafExpr : Case → Expr) (f : Case → Nat → Nat) :
    ∀ (t : Trie) (d w : Nat), t.depth + d ≤ W →
      (∀ l ∈ t.leaves, ∀ v, v < 2 ^ W →
        eval [v] (leafExpr l.1) = some (f l.1 (v % 2 ^ (W - (d + l.2.2))))) →
      w < 2 ^ W → eval [w] (walk W leafExpr t d) = some (walkAt f t (W - d) (w % 2 ^ (W - d)))
  | .leaf c, d, w, _, hl, hw => by
      have := hl (c, 0, 0) (by simp [Trie.leaves]) w hw
      simp only [walk, walkAt, Trie.locate, Nat.sub_zero, Nat.mod_mod]
      simpa using this
  | .node z o, d, w, hd, hl, hw => by
      simp only [Trie.depth] at hd
      have hlz : ∀ l ∈ z.leaves, ∀ v, v < 2 ^ W →
          eval [v] (leafExpr l.1) = some (f l.1 (v % 2 ^ (W - ((d + 1) + l.2.2)))) := by
        intro l hm v hv
        have := hl (l.1, l.2.1, l.2.2 + 1)
          (by simp only [Trie.leaves, List.mem_append, List.mem_map]; exact Or.inl ⟨l, hm, rfl⟩) v hv
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
      have hlo : ∀ l ∈ o.leaves, ∀ v, v < 2 ^ W →
          eval [v] (leafExpr l.1) = some (f l.1 (v % 2 ^ (W - ((d + 1) + l.2.2)))) := by
        intro l hm v hv
        have := hl (l.1, 2 ^ l.2.2 + l.2.1, l.2.2 + 1)
          (by simp only [Trie.leaves, List.mem_append, List.mem_map]; exact Or.inr ⟨l, hm, rfl⟩) v hv
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
      have hk : W - d = (W - (d + 1)) + 1 := by omega
      have hbit : W - 1 - d = W - (d + 1) := by omega
      have hshift : W - (d + 1) < 64 := by omega
      have htest : eval [w] (bitClear W d) =
          some (if w / 2 ^ (W - (d + 1)) % 2 = 0 then 1 else 0) := by
        simp only [bitClear, eval, hbit, hshift, if_true, show (1 : Nat) < top by decide,
          show (0 : Nat) < top by decide, List.getElem?_cons_zero, Option.map_some, lift2_some,
          Nat.and_one_is_mod]
      have hlow : w % 2 ^ (W - d) % 2 ^ (W - d - 1) = w % 2 ^ (W - (d + 1)) := by
        rw [show W - d - 1 = W - (d + 1) by omega, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
      have hsel : w % 2 ^ (W - d) / 2 ^ (W - d - 1) = w / 2 ^ (W - (d + 1)) % 2 := by
        rw [show W - d - 1 = W - (d + 1) by omega, hk, Nat.pow_succ, Nat.mod_mul_right_div_self]
      unfold walk
      simp only [eval, htest]
      unfold walkAt
      simp only [Trie.locate, hsel, hlow]
      by_cases hb : w / 2 ^ (W - (d + 1)) % 2 = 0
      · rw [if_pos hb, if_pos hb]
        simp only [choose_some, ne_eq, Nat.one_ne_zero, not_false_eq_true, if_true]
        rw [eval_walk W hW leafExpr f z (d + 1) w (by omega) hlz hw]
        unfold walkAt
        rw [show W - d - 1 = W - (d + 1) by omega]
        have hd' := (Trie.locate_spec z (W - (d + 1)) (w % 2 ^ (W - (d + 1))) (by omega)
          (Nat.mod_lt _ (Nat.two_pow_pos _))).2.1
        generalize z.locate (W - (d + 1)) (w % 2 ^ (W - (d + 1))) = l at hd' ⊢
        rw [show W - d - (l.2.2 + 1) = W - (d + 1) - l.2.2 by omega,
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : W - (d + 1) - l.2.2 ≤ W - (d + 1))),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : W - (d + 1) - l.2.2 ≤ W - d))]
      · rw [if_neg hb, if_neg hb]
        simp only [choose_some, ne_eq, not_true_eq_false, if_false]
        rw [eval_walk W hW leafExpr f o (d + 1) w (by omega) hlo hw]
        unfold walkAt
        rw [show W - d - 1 = W - (d + 1) by omega]
        have hd' := (Trie.locate_spec o (W - (d + 1)) (w % 2 ^ (W - (d + 1))) (by omega)
          (Nat.mod_lt _ (Nat.two_pow_pos _))).2.1
        generalize o.locate (W - (d + 1)) (w % 2 ^ (W - (d + 1))) = l at hd' ⊢
        rw [show W - d - (l.2.2 + 1) = W - (d + 1) - l.2.2 by omega,
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : W - (d + 1) - l.2.2 ≤ W - (d + 1))),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : W - (d + 1) - l.2.2 ≤ W - d))]

/-- Every place of every leaf of `t`, which sits at depth `d`, lies inside
the bits below its leaf's prefix and fits in 64 bits. -/
def Placed (W : Nat) (t : Trie) (d : Nat) : Prop :=
  ∀ l ∈ t.leaves, ∀ p ∈ l.1.places, fits64 p = true ∧ p.slot.shift + p.slot.width ≤ W - (d + l.2.2)

/-! ## The total reading of a field -/

def partLeaf (j : Nat) (c : Case) : Expr :=
  match c.places[j]? with
  | some p => readExpr p
  | none => .lit 0

def partExpr (W j : Nat) (t : Trie) (d : Nat) : Expr := walk W (partLeaf j) t d

def partOf (j : Nat) (c : Case) (x : Nat) : Nat := (readPlaces c.places x).getD j 0

theorem readPlaces_getD {ps : List Place} {x j : Nat} :
    (readPlaces ps x).getD j 0 = match ps[j]? with
      | some p => LayoutAlgebra.get x p.slot.shift p.slot.width + p.offset
      | none => 0 := by
  unfold readPlaces
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[j]? <;> rfl

theorem eval_part (W j : Nat) (hW : W ≤ 64) (t : Trie) (d w : Nat) (hd : t.depth + d ≤ W)
    (hp : Placed W t d) (hw : w < 2 ^ W) :
    eval [w] (partExpr W j t d) = some (walkAt (partOf j) t (W - d) (w % 2 ^ (W - d))) := by
  apply eval_walk W hW _ _ t d w hd _ hw
  intro l hl v _
  simp only [partLeaf, partOf, readPlaces_getD]
  cases hj : l.1.places[j]? with
  | none => simp [eval, top]
  | some p =>
      obtain ⟨hf, hin⟩ := hp l hl p (List.mem_of_getElem? hj)
      rw [eval_read rfl hf]
      dsimp only
      rw [get_mod (by omega)]

/-! ## Whether a word decodes -/

def conj : List Expr → Expr
  | [] => .lit 1
  | e :: es => .band e (conj es)

theorem bit_and_bit (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then 1 else 0) &&& (if b then 1 else 0) : Nat) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- `lo ≤ x`; a lower bound of 0 always holds and is written as 1, since a C
compiler rejects the comparison of an unsigned value with 0 as vacuous. -/
def atLeast (lo : Nat) (x : Expr) : Expr := if lo = 0 then .lit 1 else .le (.lit lo) x

/-- `x ≤ hi`; the largest 64-bit bound always holds and is written as 1. -/
def atMost (x : Expr) (hi : Nat) : Expr := if hi = top - 1 then .lit 1 else .le x (.lit hi)

theorem eval_atLeast {env : List Nat} {x : Expr} {v lo : Nat} (hx : eval env x = some v) (hlo : lo < top) :
    eval env (atLeast lo x) = some (if lo ≤ v then 1 else 0) := by
  unfold atLeast
  split
  · rename_i h; subst h; simp [eval, top]
  · simp [eval, hx, hlo]

theorem eval_atMost {env : List Nat} {x : Expr} {v hi : Nat} (hx : eval env x = some v) (hv : v < top)
    (hhi : hi < top) : eval env (atMost x hi) = some (if v ≤ hi then 1 else 0) := by
  unfold atMost
  split
  · rename_i h
    have : v ≤ hi := by omega
    simp [eval, top, this]
  · simp [eval, hx, hhi]

def boundsExpr (p : Place) : Expr := .band (atLeast p.lo (readExpr p)) (atMost (readExpr p) p.hi)

def validLeaf (c : Case) : Expr := if c.reserved then .lit 0 else conj (c.places.map boundsExpr)

def validExpr (W : Nat) (t : Trie) (d : Nat) : Expr := walk W validLeaf t d

def validOf (c : Case) (x : Nat) : Nat := if c.admits (readPlaces c.places x) then 1 else 0

theorem eval_bounds {v r : Nat} : ∀ ps : List Place,
    (∀ p ∈ ps, fits64 p = true ∧ p.slot.shift + p.slot.width ≤ r) →
    eval [v] (conj (ps.map boundsExpr)) = some (if within ps (readPlaces ps (v % 2 ^ r)) = true then 1 else 0)
  | [], _ => by simp [conj, eval, within, readPlaces, top]
  | p :: ps, h => by
      obtain ⟨hf, hin⟩ := h p (by simp)
      have hrest := eval_bounds (v := v) (r := r) ps (fun q hq => h q (by simp [hq]))
      have hf' := hf
      unfold fits64 at hf'
      simp only [decide_eq_true_eq] at hf'
      have hr := eval_read (env := [v]) (w := v) rfl hf
      have hrv : LayoutAlgebra.get v p.slot.shift p.slot.width + p.offset < top := by
        have := LayoutAlgebra.get_lt v p.slot.shift p.slot.width; omega
      simp only [List.map_cons, conj, boundsExpr, eval, eval_atLeast hr hf'.2.2.2.1,
        eval_atMost hr hrv hf'.2.2.2.2, lift2_some, hrest]
      rw [bit_and_bit, bit_and_bit]
      have hx : readPlaces (p :: ps) (v % 2 ^ r) =
          (LayoutAlgebra.get v p.slot.shift p.slot.width + p.offset) :: readPlaces ps (v % 2 ^ r) := by
        simp only [readPlaces, List.map_cons, get_mod hin]
      rw [hx]
      simp only [within, Bool.and_eq_true, decide_eq_true_eq]

theorem eval_valid (W : Nat) (hW : W ≤ 64) (t : Trie) (d w : Nat) (hd : t.depth + d ≤ W)
    (hp : Placed W t d) (hw : w < 2 ^ W) :
    eval [w] (validExpr W t d) = some (walkAt validOf t (W - d) (w % 2 ^ (W - d))) := by
  apply eval_walk W hW _ _ t d w hd _ hw
  intro l hl v _
  simp only [validLeaf, validOf, Case.admits]
  by_cases hr : l.1.reserved = true
  · simp [hr, eval, top]
  · simp only [hr, Bool.not_false, Bool.true_and]
    exact eval_bounds _ (fun p hp' => hp l hl p hp')

/-! ## The code's accessors -/

/-- Every place fits 64 bits and the word does too. -/
def allFit64 (k : Code) : Bool := decide (k.width ≤ 64) && k.trie.leaves.all fun l => l.1.places.all fits64

theorem placed_of_facts {k : Code} (hk : k.Facts) (hf : allFit64 k = true) : Placed k.width k.trie 0 := by
  intro l hl p hp
  unfold allFit64 at hf
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  refine ⟨hf.2 l hl p hp, ?_⟩
  obtain ⟨ht, _⟩ := hk.leaf l hl
  unfold Case.tiles at ht
  simp only [Bool.and_eq_true] at ht
  have hin := ht.2
  unfold inside slotsOf at hin
  rw [List.all_eq_true] at hin
  have := hin p.slot (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [decide_eq_true_eq] at this
  omega

theorem width_le {k : Code} (hf : allFit64 k = true) : k.width ≤ 64 := by
  unfold allFit64 at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact hf.1

/-- The generated reading of field `j` is the code's total reading. -/
theorem eval_parts {k : Code} (hk : k.Facts) (hf : allFit64 k = true) (j : Nat) {w : Nat}
    (hw : w < 2 ^ k.width) : eval [w] (partExpr k.width j k.trie 0) = some ((k.parts w).getD j 0) := by
  rw [eval_part k.width j (width_le hf) k.trie 0 w (by have := hk.depth; omega) (placed_of_facts hk hf) hw]
  simp only [Nat.sub_zero, Nat.mod_eq_of_lt hw, walkAt, partOf, Code.parts]

/-- The generated validity test is the code's checked reading. -/
theorem eval_valid_code {k : Code} (hk : k.Facts) (hf : allFit64 k = true) {w : Nat}
    (hw : w < 2 ^ k.width) :
    eval [w] (validExpr k.width k.trie 0) = some (if (k.decode w).isSome then 1 else 0) := by
  rw [eval_valid k.width (width_le hf) k.trie 0 w (by have := hk.depth; omega) (placed_of_facts hk hf) hw]
  simp only [Nat.sub_zero, Nat.mod_eq_of_lt hw, walkAt, validOf, Code.decode, Code.parts]
  by_cases h : ((k.trie.locate k.width w).1.admits
      (readPlaces (k.trie.locate k.width w).1.places (w % 2 ^ (k.width - (k.trie.locate k.width w).2.2)))) = true
  · simp [h, hw]
  · simp [h]

/-! ## Writing a value -/

/-- 1 when value `j` lies within the place's bounds. -/
def inBounds (p : Place) (j : Nat) : Expr := .band (atLeast p.lo (.var j)) (atMost (.var j) p.hi)

def admitsFrom : List Place → Nat → List Expr
  | [], _ => []
  | p :: ps, j => inBounds p j :: admitsFrom ps (j + 1)

/-- 1 when the case admits the value (parameters `0 …`). -/
def admitsExpr (c : Case) : Expr := if c.reserved then .lit 0 else conj (admitsFrom c.places 0)

theorem eval_admitsFrom (env : List Nat) (henv : ∀ x ∈ env, x < top) : ∀ (ps : List Place) (j : Nat),
    (∀ p ∈ ps, fits64 p = true) → (env.drop j).length = ps.length →
    eval env (conj (admitsFrom ps j)) = some (if within ps (env.drop j) = true then 1 else 0)
  | [], j, _, hl => by
      have : env.drop j = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      simp [admitsFrom, conj, eval, top, this, within]
  | p :: ps, j, hf, hl => by
      have hj : j < env.length := by
        have := hl; simp only [List.length_drop, List.length_cons] at this; omega
      have hd : env.drop j = env[j] :: env.drop (j + 1) := List.drop_eq_getElem_cons hj
      have hf' := hf p (by simp)
      unfold fits64 at hf'
      simp only [decide_eq_true_eq] at hf'
      have hrest := eval_admitsFrom env henv ps (j + 1) (fun q hq => hf q (by simp [hq]))
        (by rw [hd] at hl; simp only [List.length_cons, Nat.add_right_cancel_iff] at hl; exact hl)
      have hx : eval env (.var j) = some env[j] := List.getElem?_eq_getElem hj
      have hxv : env[j] < top := henv _ (List.getElem_mem hj)
      simp only [admitsFrom, conj, inBounds, eval, eval_atLeast hx hf'.2.2.2.1,
        eval_atMost hx hxv hf'.2.2.2.2, lift2_some, hrest, hd, within]
      rw [bit_and_bit, bit_and_bit]
      simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem eval_admits (env : List Nat) (henv : ∀ x ∈ env, x < top) (c : Case) (hf : ∀ p ∈ c.places, fits64 p = true)
    (hl : env.length = c.places.length) : eval env (admitsExpr c) = some (if c.admits env = true then 1 else 0) := by
  unfold admitsExpr Case.admits
  by_cases hr : c.reserved = true
  · simp [hr, eval, top]
  · simp only [hr, Bool.not_false, Bool.true_and]
    have := eval_admitsFrom env henv c.places 0 hf (by simpa using hl)
    simpa using this

/-- The stored field `j`, shifted into its slot. -/
def writeExpr (p : Place) (j : Nat) : Expr :=
  if p.slot.width = 0 then .lit 0
  else .shl (.band (.sub (.var j) (.lit p.offset)) (.lit (2 ^ p.slot.width - 1))) p.slot.shift

def packFrom : List Place → Nat → Expr
  | [], _ => .lit 0
  | p :: ps, j => .bor (writeExpr p j) (packFrom ps (j + 1))

/-- The stored fields, each in its slot. -/
def orPack : List Place → List Nat → Nat
  | p :: ps, x :: xs => (x - p.offset) % 2 ^ p.slot.width * 2 ^ p.slot.shift ||| orPack ps xs
  | _, _ => 0

theorem eval_write {env : List Nat} {j x : Nat} (hx : env[j]? = some x) {p : Place} (hf : fits64 p = true)
    (hlo : p.offset ≤ x) (hhi : x ≤ p.hi) (hin : p.slot.shift + p.slot.width ≤ 64) :
    eval env (writeExpr p j) = some ((x - p.offset) % 2 ^ p.slot.width * 2 ^ p.slot.shift) := by
  unfold fits64 at hf
  simp only [decide_eq_true_eq] at hf
  obtain ⟨hs, hn, hoff, hlo', hhi'⟩ := hf
  unfold writeExpr
  split
  · rename_i h0
    rw [h0, Nat.pow_zero, Nat.mod_one, Nat.zero_mul]
    simp [eval, show (0 : Nat) < top by decide]
  · rename_i h0
    have hs : p.slot.shift < 64 := hs.resolve_left h0
    have hoffl : p.offset < top := by have := Nat.two_pow_pos p.slot.width; omega
    have hsub : (x + top - p.offset) % top = x - p.offset := by
      rw [show x + top - p.offset = (x - p.offset) + top by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hlt : (x - p.offset) % 2 ^ p.slot.width * 2 ^ p.slot.shift < top := by
      have h1 := Nat.mod_lt (x - p.offset) (Nat.two_pow_pos p.slot.width)
      have h2 : (x - p.offset) % 2 ^ p.slot.width * 2 ^ p.slot.shift < 2 ^ p.slot.width * 2 ^ p.slot.shift :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      have h3 : 2 ^ p.slot.width * 2 ^ p.slot.shift ≤ top := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp only [eval, hx, hoffl, mask_lt hn, hs, if_true, lift2_some, Option.map_some, hsub,
      and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

theorem eval_pack (env : List Nat) : ∀ (ps : List Place) (j : Nat),
    (∀ p ∈ ps, fits64 p = true ∧ p.offset ≤ p.lo ∧ p.slot.shift + p.slot.width ≤ 64) →
    (env.drop j).length = ps.length → within ps (env.drop j) = true →
    eval env (packFrom ps j) = some (orPack ps (env.drop j))
  | [], j, _, hl, _ => by
      have : env.drop j = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      simp [packFrom, eval, top, orPack]
  | p :: ps, j, hf, hl, hw => by
      have hj : j < env.length := by
        have := hl; simp only [List.length_drop, List.length_cons] at this; omega
      have hd : env.drop j = env[j] :: env.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [hd] at hl hw
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨hfp, hlo, hin⟩ := hf p (by simp)
      have hrest := eval_pack env ps (j + 1) (fun q hq => hf q (by simp [hq]))
        (by simp only [List.length_cons, Nat.add_right_cancel_iff] at hl; exact hl) hw.2
      rw [hd]
      simp only [packFrom, eval, eval_write (List.getElem?_eq_getElem hj) hfp (by omega) hw.1.2 hin, hrest,
        lift2_some, orPack]

/-- A list's bit `j`, through the slot holding it. -/
theorem testBit_orPack : ∀ (ps : List Place) (v : List Nat) (i : Nat),
    pairwiseDisjoint (slotsOf ps) = true →
      (orPack ps v).testBit i =
        match lookup (slotsOf ps) (storePlaces ps v) i with
        | some (s, x) => x.testBit (i - s.shift)
        | none => false
  | [], _, i, _ => by simp [orPack, slotsOf, lookup]
  | _ :: _, [], i, _ => by simp [orPack, slotsOf, storePlaces, lookup]
  | p :: ps, x :: xs, i, hd => by
      simp only [slotsOf, List.map_cons, pairwiseDisjoint, Bool.and_eq_true] at hd
      simp only [orPack, slotsOf, List.map_cons, storePlaces, lookup, testBit_or, testBit_mul_two_pow,
        testBit_mod_two_pow]
      have ih := testBit_orPack ps xs i (by simpa [slotsOf] using hd.2)
      simp only [slotsOf] at ih
      by_cases hh : p.slot.holds i = true
      · rw [if_pos hh, lookup_none_of_disjoint hh _ _ hd.1] at *
        simp only at ih
        rw [ih]
        unfold Slot.holds at hh
        simp only [decide_eq_true_eq] at hh
        have h1 : p.slot.shift ≤ i := hh.1
        have h2 : i - p.slot.shift < p.slot.width := by omega
        simp [h1, h2]
      · rw [if_neg hh, ih]
        unfold Slot.holds at hh
        simp only [decide_eq_true_eq, not_and, Nat.not_lt] at hh
        by_cases h1 : p.slot.shift ≤ i
        · have h2 : ¬ i - p.slot.shift < p.slot.width := by have := hh h1; omega
          simp [h1, h2]
        · simp [h1]

theorem pack_eq_orPack {ps : List Place} {v : List Nat} (hd : pairwiseDisjoint (slotsOf ps) = true) :
    pack (slotsOf ps) (storePlaces ps v) 0 = orPack ps v := by
  apply eq_of_testBit_eq
  intro i
  rw [testBit_pack _ _ 0 i hd, testBit_orPack ps v i hd]
  cases lookup (slotsOf ps) (storePlaces ps v) i <;> simp

/-- The word of a value in a case: its prefix, then its stored fields. -/
def wordExpr (W : Nat) (l : Case × Nat × Nat) : Expr :=
  .bor (.lit (l.2.1 * 2 ^ (W - l.2.2))) (packFrom l.1.places 0)

/-- The first case that admits the value writes it. -/
def encodeExpr (W : Nat) : List (Case × Nat × Nat) → Expr
  | [] => .lit 0
  | l :: ls => .ite (admitsExpr l.1) (wordExpr W l) (encodeExpr W ls)

/-- 1 when some case admits the value. -/
def admitsAnyExpr : List (Case × Nat × Nat) → Expr
  | [] => .lit 0
  | l :: ls => .bor (admitsExpr l.1) (admitsAnyExpr ls)

/-- What each case needs for its accessors to compute its words. -/
def Writable (W : Nat) (l : Case × Nat × Nat) : Prop :=
  (∀ p ∈ l.1.places, fits64 p = true ∧ p.slot.shift + p.slot.width ≤ W - l.2.2) ∧
  (l.1.reserved = false → ∀ p ∈ l.1.places, p.offset ≤ p.lo) ∧
  pairwiseDisjoint (slotsOf l.1.places) = true ∧ l.2.1 < 2 ^ l.2.2 ∧ l.2.2 ≤ W

/-- The word Lean's `encode` writes for a value in a case. -/
def wordOf (W : Nat) (v : List Nat) (l : Case × Nat × Nat) : Nat :=
  l.2.1 * 2 ^ (W - l.2.2) + pack (slotsOf l.1.places) (storePlaces l.1.places v) 0

theorem eval_word {W : Nat} (hW : W ≤ 64) {env : List Nat} {l : Case × Nat × Nat} (hl : Writable W l)
    (hlen : env.length = l.1.places.length) (hadm : l.1.admits env = true) :
    eval env (wordExpr W l) = some (wordOf W env l) := by
  obtain ⟨hplace, hoff, hdis, hp, hd⟩ := hl
  unfold Case.admits at hadm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm
  have hpack := eval_pack env l.1.places 0
    (fun q hq => ⟨(hplace q hq).1, hoff hadm.1 q hq, by have := (hplace q hq).2; omega⟩)
    (by simpa using hlen) (by simpa using hadm.2)
  simp only [List.drop_zero] at hpack
  have hlow : orPack l.1.places env < 2 ^ (W - l.2.2) := by
    rw [← pack_eq_orPack hdis]
    apply pack_lt _ _ _ (Nat.two_pow_pos _)
    unfold inside slotsOf
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    simpa using (hplace q hq).2
  have hpre : l.2.1 * 2 ^ (W - l.2.2) < top := by
    have : l.2.1 * 2 ^ (W - l.2.2) < 2 ^ l.2.2 * 2 ^ (W - l.2.2) := Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
    rw [← Nat.pow_add, show l.2.2 + (W - l.2.2) = W by omega] at this
    have : 2 ^ W ≤ top := Nat.pow_le_pow_right (by omega) hW
    omega
  simp only [wordExpr, eval, hpre, if_true, hpack, lift2_some, wordOf, pack_eq_orPack hdis, Option.some.injEq]
  rw [Nat.mul_comm, two_pow_add_eq_or_of_lt hlow]

theorem eval_encodeList {W : Nat} (hW : W ≤ 64) (env : List Nat) (henv : ∀ x ∈ env, x < top) :
    ∀ ls : List (Case × Nat × Nat),
    (∀ l ∈ ls, Writable W l ∧ l.1.places.length = env.length) →
    eval env (encodeExpr W ls) = some (((ls.find? fun l => l.1.admits env).map (wordOf W env)).getD 0)
  | [], _ => by simp [encodeExpr, eval, top]
  | l :: ls, h => by
      obtain ⟨hw, hlen⟩ := h l (by simp)
      have hrest := eval_encodeList hW env henv ls (fun m hm => h m (by simp [hm]))
      have hadm := eval_admits env henv l.1 (fun p hp => (hw.1 p hp).1) hlen.symm
      simp only [encodeExpr, eval, hadm, choose_some, List.find?_cons]
      by_cases ha : l.1.admits env = true
      · simp only [ha, if_true, ne_eq, Nat.one_ne_zero, not_false_eq_true, Option.map_some, Option.getD_some]
        exact eval_word hW hw hlen.symm ha
      · simp only [ha, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
        simpa using hrest

theorem eval_admitsAnyList (env : List Nat) (henv : ∀ x ∈ env, x < top) : ∀ ls : List (Case × Nat × Nat),
    (∀ l ∈ ls, (∀ p ∈ l.1.places, fits64 p = true) ∧ l.1.places.length = env.length) →
    eval env (admitsAnyExpr ls) = some (if (ls.find? fun l => l.1.admits env).isSome then 1 else 0)
  | [], _ => by simp [admitsAnyExpr, eval, top]
  | l :: ls, h => by
      obtain ⟨hf, hlen⟩ := h l (by simp)
      have hrest := eval_admitsAnyList env henv ls (fun m hm => h m (by simp [hm]))
      simp only [admitsAnyExpr, eval, eval_admits env henv l.1 hf hlen.symm, hrest, lift2_some, List.find?_cons]
      by_cases ha : l.1.admits env = true <;>
        by_cases hb : (ls.find? fun l => l.1.admits env).isSome = true <;> simp [ha, hb]

theorem writable_of_facts {k : Code} (hk : k.Facts) (hf : allFit64 k = true) :
    ∀ l ∈ k.trie.leaves, Writable k.width l := by
  intro l hl
  have hp := placed_of_facts hk hf l hl
  obtain ⟨ht, hfits⟩ := hk.leaf l hl
  obtain ⟨hpre, hd⟩ := Trie.leaves_spec _ l hl
  unfold Case.tiles at ht
  simp only [Bool.and_eq_true] at ht
  refine ⟨fun p hpm => by have := hp p hpm; simpa using this, ?_, ht.1.1, hpre, by have := hk.depth; omega⟩
  intro hr p hpm
  unfold Case.fits at hfits
  rw [hr, Bool.false_or, List.all_eq_true] at hfits
  exact (of_decide_eq_true (hfits p hpm)).1

/-- The generated encoder writes what the code's `encode` writes, and the
generated test says whether it writes anything. -/
theorem eval_encode {k : Code} (hk : k.Facts) (hf : allFit64 k = true) {v : List Nat}
    (hv : ∀ x ∈ v, x < top) (hlen : ∀ l ∈ k.trie.leaves, l.1.places.length = v.length) :
    eval v (encodeExpr k.width k.trie.leaves) = some ((k.encode v).getD 0) ∧
    eval v (admitsAnyExpr k.trie.leaves) = some (if (k.encode v).isSome then 1 else 0) := by
  have hw := writable_of_facts hk hf
  constructor
  · rw [eval_encodeList (width_le hf) v hv _ (fun l hl => ⟨hw l hl, hlen l hl⟩)]
    rfl
  · rw [eval_admitsAnyList v hv _ (fun l hl => ⟨fun p hp => (hw l hl).1 p hp |>.1, hlen l hl⟩)]
    have hm : ∀ (o : Option (Case × Nat × Nat)) (f : Case × Nat × Nat → Nat), (o.map f).isSome = o.isSome := by
      intro o f; cases o <;> rfl
    simp only [Code.encode, Code.choose, hm]

/-! ## Writing one field of a single-case word -/

/-- The word (parameter 0) with the place's field replaced by the stored form
of the value (parameter 1). -/
def setExpr (p : Place) : Expr :=
  if p.slot.width = 0 then .var 0
  else .bor (.band (.var 0) (.bnot (.lit ((2 ^ p.slot.width - 1) * 2 ^ p.slot.shift)))) (writeExpr p 1)

theorem set_zero (w s v : Nat) : LayoutAlgebra.set w s 0 v = w := by
  apply eq_of_testBit_eq
  intro i
  rw [testBit_set]
  by_cases h : i < s <;> simp [h]

theorem eval_set {w x : Nat} {p : Place} (hf : fits64 p = true) (hw : w < top)
    (hlo : p.offset ≤ x) (hhi : x ≤ p.hi) (hin : p.slot.shift + p.slot.width ≤ 64) :
    eval [w, x] (setExpr p) = some (LayoutAlgebra.set w p.slot.shift p.slot.width (x - p.offset)) := by
  unfold setExpr
  split
  · rename_i h0
    rw [h0, set_zero]
    rfl
  · have hm : (2 ^ p.slot.width - 1) * 2 ^ p.slot.shift < top := by
      have : (2 ^ p.slot.width - 1) * 2 ^ p.slot.shift < 2 ^ p.slot.width * 2 ^ p.slot.shift :=
        Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos p.slot.width; omega) (Nat.two_pow_pos _)
      have h2 : 2 ^ p.slot.width * 2 ^ p.slot.shift ≤ top := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hwr := eval_write (env := [w, x]) (j := 1) rfl hf hlo hhi hin
    simp only [eval, hm, if_true, List.getElem?_cons_zero, Option.map_some, lift2_some, hwr, Option.some.injEq]
    apply eq_of_testBit_eq
    intro i
    simp only [testBit_or, testBit_and, testBit_xor, testBit_set, testBit_mul_two_pow, testBit_mod_two_pow,
      testBit_two_pow_sub_one]
    have htop : (top - 1).testBit i = decide (i < 64) := by
      unfold top; rw [testBit_two_pow_sub_one]
    rw [htop]
    by_cases h64 : i < 64
    · by_cases h1 : i < p.slot.shift
      · simp [h64, h1, Nat.not_le.mpr h1]
      · by_cases h2 : i < p.slot.shift + p.slot.width
        · have : i - p.slot.shift < p.slot.width := by omega
          simp [h64, h1, h2, this, Nat.not_lt.mp h1]
        · have : ¬ i - p.slot.shift < p.slot.width := by omega
          simp [h64, h1, h2, this]
    · have hwi : w.testBit i = false := testBit_lt_two_pow (Nat.lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by omega) (by omega)))
      have h1 : ¬ i < p.slot.shift := by omega
      have h2 : ¬ i < p.slot.shift + p.slot.width := by omega
      have h3 : ¬ i - p.slot.shift < p.slot.width := by omega
      simp [h64, h1, h2, h3, hwi]

/-! ## Kind accessors -/

open Mettapedia.GSLT.LanguageDef.LayoutKinds (Masks Kind kindAt maskOf masksOf derive)

/-- One child folded into the accumulated summaries. -/
def step (m : Masks) (acc c : Nat) : Nat := ((acc ||| c) &&& m.any) ||| (acc &&& c &&& m.all)

def deriveInit (m : Masks) : Expr := .lit m.all
def deriveChild (m : Masks) : Expr :=
  .bor (.band (.bor (.var 0) (.var 1)) (.lit m.any)) (.band (.band (.var 0) (.var 1)) (.lit m.all))
def deriveFinish (m : Masks) : Expr :=
  .bor (.band (.var 0) (.lit (m.any ||| m.all))) (.band (.var 1) (.lit m.own))

theorem fold_step (m : Masks) (hdis : m.any &&& m.all = 0) (i : Nat) :
    ∀ (cs : List Nat) (acc : Nat) (a b : Bool),
      acc.testBit i = ((m.any.testBit i && a) || (m.all.testBit i && b)) →
      (cs.foldl (step m) acc).testBit i =
        ((m.any.testBit i && (a || cs.any (·.testBit i))) || (m.all.testBit i && (b && cs.all (·.testBit i))))
  | [], acc, a, b, h => by simp [h]
  | c :: cs, acc, a, b, h => by
      have hd : (m.any.testBit i && m.all.testBit i) = false := by
        have := congrArg (·.testBit i) hdis
        simpa [testBit_and] using this
      rw [List.foldl_cons]
      rw [fold_step m hdis i cs (step m acc c) (a || c.testBit i) (b && c.testBit i)]
      · simp only [List.any_cons, List.all_cons, Bool.or_assoc, Bool.and_assoc]
      · unfold step
        simp only [testBit_or, testBit_and, h]
        cases ha : m.any.testBit i <;> cases hb : m.all.testBit i <;> simp_all

/-- Folding the children from `deriveInit` with `deriveChild`, then
`deriveFinish`, gives the derived word. -/
theorem fold_derive (m : Masks) (hdis : m.any &&& m.all = 0) (cs : List Nat) (own : Nat) :
    ((cs.foldl (step m) m.all) &&& (m.any ||| m.all)) ||| (own &&& m.own) = derive m cs own := by
  apply eq_of_testBit_eq
  intro i
  have h := fold_step m hdis i cs m.all false true (by cases m.any.testBit i <;> cases m.all.testBit i <;> rfl)
  rw [LayoutKinds.testBit_derive]
  simp only [testBit_or, testBit_and, h]
  cases m.any.testBit i <;> cases m.all.testBit i <;> cases m.own.testBit i <;>
    cases own.testBit i <;> cases cs.any (·.testBit i) <;> cases cs.all (·.testBit i) <;> rfl

theorem eval_deriveChild {m : Masks} (ha : m.any < top) (hb : m.all < top) (acc c : Nat) :
    eval [acc, c] (deriveChild m) = some (step m acc c) := by
  simp [deriveChild, eval, ha, hb, step, Nat.and_assoc]

theorem eval_deriveFinish {m : Masks} (hab : m.any ||| m.all < top) (ho : m.own < top) (acc own : Nat) :
    eval [acc, own] (deriveFinish m) = some ((acc &&& (m.any ||| m.all)) ||| (own &&& m.own)) := by
  simp [deriveFinish, eval, hab, ho]

theorem eval_deriveInit {m : Masks} (hb : m.all < top) : eval [] (deriveInit m) = some m.all := by
  simp [deriveInit, eval, hb]

/-- A word kept to the kinds an operation keeps. -/
def applyExpr (keep : Nat) : Expr := .band (.var 0) (.lit keep)

theorem eval_apply {fields : List (Slot × Kind)} {W : Nat} (op : LayoutKinds.Operation) (hW : W ≤ 64)
    (hm : maskOf fields (LayoutKinds.keeps op) < 2 ^ W) {w : Nat} :
    eval [w] (applyExpr (maskOf fields (LayoutKinds.keeps op))) = some (LayoutKinds.apply fields W op w) := by
  have htop : maskOf fields (LayoutKinds.keeps op) < top :=
    Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hW)
  simp only [applyExpr, eval, htop, if_true, List.getElem?_cons_zero, lift2_some, LayoutKinds.apply,
    Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.and_lt_two_pow _ hm)]

theorem maskOf_lt {W : Nat} (p : Kind → Bool) : ∀ fields : List (Slot × Kind),
    inside (fields.map (·.1)) W = true → maskOf fields p < 2 ^ W
  | [], _ => by simp [maskOf, Nat.two_pow_pos]
  | f :: fields, h => by
      simp only [List.map_cons, inside, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      have hrest := maskOf_lt p fields (by unfold inside; exact h.2)
      unfold maskOf at hrest ⊢
      simp only [List.foldr_cons]
      split
      · apply Nat.or_lt_two_pow _ hrest
        unfold LayoutKinds.slotMask
        have : (2 ^ f.1.width - 1) * 2 ^ f.1.shift < 2 ^ f.1.width * 2 ^ f.1.shift :=
          Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.1.width; omega) (Nat.two_pow_pos _)
        have h2 : 2 ^ f.1.width * 2 ^ f.1.shift ≤ 2 ^ W := by
          rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · exact hrest

theorem masks_disjoint {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true) :
    (masksOf fields).any &&& (masksOf fields).all = 0 := by
  apply eq_of_testBit_eq
  intro i
  simp only [masksOf, testBit_and, LayoutKinds.testBit_maskOf_kind hd, Nat.zero_testBit]
  cases kindAt fields i with
  | none => rfl
  | some k => cases k <;> rfl

/-! ## The accessors of a declared layout -/

open Mettapedia.GSLT.LanguageDef.LayoutDeclarations (Declaration Field decodeLayout admitted facts_of_admitted)
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)

/-- A generated C function: its name, its parameters (the word is `word`), what
it returns (`word`, `value` or `bool`) and its body. -/
structure Function where
  name : String
  params : List String
  result : String
  body : Expr
deriving DecidableEq, Repr

def partFunctions (d : Declaration) : List Function :=
  ((List.range d.fields.length).zip d.fields).map fun (j, f) =>
    ⟨d.name ++ "_" ++ f.name, ["word"], "value", partExpr d.code.width j d.code.trie 0⟩

def setFunctions (d : Declaration) : List Function :=
  match d.code.trie with
  | .leaf c => (c.places.zip d.fields).map fun (p, f) =>
      ⟨d.name ++ "_set_" ++ f.name, ["word", "value"], "word", setExpr p⟩
  | .node _ _ => []

def derivedKind : Kind → Bool
  | .anyChild | .allChildren | .cache | .occurrence => true
  | _ => false

def kindFunctions (d : Declaration) : List Function :=
  match LayoutKinds.flagsOf d with
  | some fields =>
      if fields.any (fun f => derivedKind f.2) then
        let m := masksOf fields
        [⟨d.name ++ "_derive_init", [], "word", deriveInit m⟩,
         ⟨d.name ++ "_derive_child", ["acc", "child"], "word", deriveChild m⟩,
         ⟨d.name ++ "_derive_finish", ["acc", "own"], "word", deriveFinish m⟩,
         ⟨d.name ++ "_value_copy", ["word"], "word", applyExpr (maskOf fields (LayoutKinds.keeps .valueCopy))⟩,
         ⟨d.name ++ "_store", ["word"], "word", applyExpr (maskOf fields (LayoutKinds.keeps .storage))⟩,
         ⟨d.name ++ "_relocate", ["word"], "word", applyExpr (maskOf fields (LayoutKinds.keeps .relocation))⟩]
      else []
  | none => []

/-- Every accessor Cesta generates for a layout, in the order it prints them. -/
def lowerLayout (d : Declaration) : List Function :=
  partFunctions d ++
  [⟨d.name ++ "_valid", ["word"], "bool", validExpr d.code.width d.code.trie 0⟩,
   ⟨d.name ++ "_admits", d.fields.map (·.name), "bool", admitsAnyExpr d.code.trie.leaves⟩,
   ⟨d.name ++ "_encode", d.fields.map (·.name), "word", encodeExpr d.code.width d.code.trie.leaves⟩] ++
  setFunctions d ++ kindFunctions d

/-! ## Accessors as Cesta records them -/

def decodeExpr : Atom → Option Expr
  | .list [.symbol "var", n] => do pure (.var (← LayoutDeclarations.number n))
  | .list [.symbol "lit", n] => do pure (.lit (← LayoutDeclarations.number n))
  | .list [.symbol "and", a, b] => do pure (.band (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "or", a, b] => do pure (.bor (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "not", a] => do pure (.bnot (← decodeExpr a))
  | .list [.symbol "shl", a, n] => do pure (.shl (← decodeExpr a) (← LayoutDeclarations.number n))
  | .list [.symbol "shr", a, n] => do pure (.shr (← decodeExpr a) (← LayoutDeclarations.number n))
  | .list [.symbol "add", a, b] => do pure (.add (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "sub", a, b] => do pure (.sub (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "eq", a, b] => do pure (.eq (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "le", a, b] => do pure (.le (← decodeExpr a) (← decodeExpr b))
  | .list [.symbol "ite", c, a, b] => do pure (.ite (← decodeExpr c) (← decodeExpr a) (← decodeExpr b))
  | _ => none

def textOf : Atom → Option String
  | .text s => some s
  | _ => none

def decodeFunction : Atom → Option Function
  | .list [.symbol "Function", .text name, .list (.symbol "Params" :: params), .text result, body] => do
      pure ⟨name, ← params.mapM textOf, result, ← decodeExpr body⟩
  | _ => none

/-- `(cesta-layout-functions/1 NAME (Function …) …)`, as `cesta layout functions` prints it. -/
def decodeFunctions : Atom → Option (String × List Function)
  | .list (.symbol "cesta-layout-functions/1" :: .symbol name :: functions) => do
      pure (name, ← functions.mapM decodeFunction)
  | _ => none

/-- A layout's recorded accessors are admitted when the layout is, its places
print in 64 bits, and the recorded functions are exactly its lowering. -/
def functionsAdmitted (layout functions : Atom) : Bool :=
  match decodeLayout layout, decodeFunctions functions with
  | some d, some (name, fs) => admitted layout && allFit64 d.code && name == d.name && fs == lowerLayout d
  | _, _ => false

theorem lowering_of_admitted {la fa : Atom} (h : functionsAdmitted la fa = true) :
    ∃ d fs, decodeLayout la = some d ∧ decodeFunctions fa = some (d.name, fs) ∧ fs = lowerLayout d ∧
      d.code.Facts ∧ allFit64 d.code = true := by
  unfold functionsAdmitted at h
  cases hd : decodeLayout la with
  | none => rw [hd] at h; simp at h
  | some d =>
      cases hf : decodeFunctions fa with
      | none => rw [hd, hf] at h; simp at h
      | some p =>
          rw [hd, hf] at h
          obtain ⟨name, fs⟩ := p
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨⟨hadm, hfit⟩, hname⟩, hfs⟩ := h
          obtain ⟨d', hd', facts⟩ := facts_of_admitted hadm
          rw [hd] at hd'
          cases hd'
          exact ⟨d, fs, rfl, by rw [hname], hfs, facts, hfit⟩

/-- An empty field at the end of the word is a constant reading and an
identity update; neither operation evaluates a shift by the word width. -/
theorem empty_slot_at_word_end (w : Nat) :
    let p : Place := ⟨⟨64, 0⟩, 7, 7, 7⟩
    fits64 p = true ∧ eval [w] (readExpr p) = some 7 ∧ eval [w, 7] (setExpr p) = some w := by
  exact ⟨by decide, rfl, rfl⟩

/-- A real shift by the full width is undefined, even when its operand is zero. -/
theorem full_width_shift_undefined : eval [] (.shl (.lit 0) 64) = none := by decide

end Mettapedia.GSLT.LanguageDef.LayoutLowering
