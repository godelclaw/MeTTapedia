import Mettapedia.GSLT.LanguageDef.LayoutLowering

/-!
# Views of a layout by case and by key

The accessors of `LayoutLowering` read one field at a time. Code that uses a
prefix-coded word also asks about its cases: the bounds a word's case puts on
a field, the case a value belongs to, and the word of a value already known to
be admitted. These views are generated from the same declaration, so a user of
the layout keeps no copy of its case boundaries or bounds.

- `eval_wordBound`: the bound of a field in the case a word selects;
  `wordBound_spec`: a word's checked value lies within those bounds.
- A layout may declare a key field whose ranges ascend through its admitting
  cases in prefix order (`LayoutDeclarations.keyAscending`). Then the case of
  an admitted value is decided by its key: `encode_isSome_iff`.
  `eval_byKey` computes, from the key alone, the bounds of every field in the
  key's case and whether some case holds the key.
- `eval_pack`: for an admitted value, the unchecked encoder, which dispatches
  on the key with one comparison per case, writes the value's word.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutViews

open Nat
open Mettapedia.GSLT.LanguageDef.LayoutCodes
open Mettapedia.GSLT.LanguageDef.LayoutLowering
open Mettapedia.GSLT.LanguageDef.LayoutDeclarations
  (Declaration decodeLayout admitted facts_of_admitted admitting below keyAscending keyOf constantsOf)
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)

/-! ## Places -/

theorem fits_bounds {p : Place} (h : fits64 p = true) : p.lo < top ∧ p.hi < top := by
  unfold fits64 at h
  simp only [decide_eq_true_eq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

theorem within_getElem : ∀ (ps : List Place) (v : List Nat), within ps v = true →
    ∀ (j : Nat) (p : Place) (x : Nat), ps[j]? = some p → v[j]? = some x → p.lo ≤ x ∧ x ≤ p.hi
  | [], _, _, _, _, _, hp, _ => by simp at hp
  | _ :: _, [], h, _, _, _, _, _ => by simp [within] at h
  | q :: ps, y :: v, h, j, p, x, hp, hx => by
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at h
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hx
          subst hp hx
          exact h.1
      | succ j =>
          simp only [List.getElem?_cons_succ] at hp hx
          exact within_getElem ps v h.2 j p x hp hx

/-- An admitting case has field `j` when the value it admits does. -/
theorem place_of_admits {c : Case} {v : List Nat} (h : c.admits v = true) {j x : Nat} (hx : v[j]? = some x) :
    ∃ p, c.places[j]? = some p ∧ p.lo ≤ x ∧ x ≤ p.hi := by
  unfold Case.admits at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hlen := length_of_within _ _ h.2
  have hj : j < c.places.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨c.places[j], List.getElem?_eq_getElem hj, ?_⟩
  exact within_getElem _ _ h.2 j _ x (List.getElem?_eq_getElem hj) hx

theorem fits_of_leaf {k : Code} (hf : allFit64 k = true) {l : Case × Nat × Nat} (hl : l ∈ k.trie.leaves) :
    ∀ p ∈ l.1.places, fits64 p = true := by
  unfold allFit64 at hf
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  exact hf.2 l hl

/-! ## The bounds of the word's case -/

def bound (upper : Bool) (p : Place) : Nat := if upper then p.hi else p.lo

/-- Field `j`'s lower or upper bound in a case; 0 for a case without field `j`. -/
def caseBound (upper : Bool) (j : Nat) (c : Case) : Nat := (c.places[j]?.map (bound upper)).getD 0

def boundLeaf (upper : Bool) (j : Nat) (c : Case) : Expr := .lit (caseBound upper j c)

def boundExpr (W : Nat) (upper : Bool) (j : Nat) (t : Trie) (d : Nat) : Expr := walk W (boundLeaf upper j) t d

/-- Field `j`'s bound in the case the word selects. -/
def wordBound (k : Code) (upper : Bool) (j w : Nat) : Nat := caseBound upper j (k.trie.locate k.width w).1

theorem caseBound_lt {c : Case} (hc : ∀ p ∈ c.places, fits64 p = true) (upper : Bool) (j : Nat) :
    caseBound upper j c < top := by
  unfold caseBound
  cases hp : c.places[j]? with
  | none => simp [top]
  | some p =>
      have := fits_bounds (hc p (List.mem_of_getElem? hp))
      cases upper <;> simp [bound, this.1, this.2]

theorem eval_wordBound {k : Code} (hk : k.Facts) (hf : allFit64 k = true) (upper : Bool) (j : Nat) {w : Nat}
    (hw : w < 2 ^ k.width) : eval [w] (boundExpr k.width upper j k.trie 0) = some (wordBound k upper j w) := by
  rw [boundExpr, eval_walk k.width (width_le hf) (boundLeaf upper j) (fun c _ => caseBound upper j c) k.trie 0 w
    (by have := hk.depth; omega) ?_ hw]
  · simp only [walkAt, Nat.sub_zero, Nat.mod_eq_of_lt hw, wordBound]
  · intro l hl v _
    simp [boundLeaf, eval, caseBound_lt (fits_of_leaf hf hl) upper j]

/-- A word's checked value lies within the bounds of its case. -/
theorem wordBound_spec {k : Code} {w : Nat} {v : List Nat} (h : k.decode w = some v) {j x : Nat}
    (hx : v[j]? = some x) : wordBound k false j w ≤ x ∧ x ≤ wordBound k true j w := by
  have hv : k.parts w = v := Code.decode_parts h
  unfold Code.decode at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    rw [hv] at hcond
    obtain ⟨p, hp, hlo, hhi⟩ := place_of_admits hcond.2 hx
    simp [wordBound, caseBound, hp, bound, hlo, hhi]
  · simp at h

/-! ## Keys -/

/-- An admitting case whose field-`j` range holds `x`. -/
def holds (j x : Nat) (l : Case × Nat × Nat) : Bool :=
  !l.1.reserved && match l.1.places[j]? with
    | some p => decide (p.lo ≤ x ∧ x ≤ p.hi)
    | none => false

/-- The case whose key range holds the key `x`. -/
def keyCase (k : Code) (j x : Nat) : Option (Case × Nat × Nat) := k.trie.leaves.find? (holds j x)

theorem find?_unique {α : Type} {P : α → Bool} :
    ∀ (l : List α) (x : α), x ∈ l → P x = true → (∀ y ∈ l, P y = true → y = x) → l.find? P = some x
  | [], _, hx, _, _ => by simp at hx
  | a :: l, x, hx, hp, hu => by
      by_cases ha : P a = true
      · rw [List.find?_cons_of_pos ha, hu a (by simp) ha]
      · rw [List.find?_cons_of_neg ha]
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hp ha
        · exact find?_unique l x hx hp (fun y hy => hu y (by simp [hy]))

/-- Two different elements of a list ordered by `R` are related one way or the other. -/
theorem pairwiseB_order {α : Type} {R : α → α → Bool} :
    ∀ (l : List α) (a b : α), pairwiseB R l = true → a ∈ l → b ∈ l → a ≠ b → R a b = true ∨ R b a = true
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, a, b, h, ha, hb, hab => by
      rw [pairwiseB, Bool.and_eq_true, List.all_eq_true] at h
      rcases List.mem_cons.mp ha with hac | hal
      · rcases List.mem_cons.mp hb with hbc | hbl
        · exact absurd (hac.trans hbc.symm) hab
        · rw [hac]; exact Or.inl (h.1 b hbl)
      · rcases List.mem_cons.mp hb with hbc | hbl
        · rw [hbc]; exact Or.inr (h.1 a hal)
        · exact pairwiseB_order l a b h.2 hal hbl hab

theorem mem_admitting {k : Code} {l : Case × Nat × Nat} :
    l ∈ admitting k ↔ l ∈ k.trie.leaves ∧ l.1.reserved = false := by
  simp [admitting, List.mem_filter]

theorem holds_spec {j x : Nat} {l : Case × Nat × Nat} (h : holds j x l = true) :
    l.1.reserved = false ∧ ∃ p, l.1.places[j]? = some p ∧ p.lo ≤ x ∧ x ≤ p.hi := by
  unfold holds at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, ?_⟩
  cases hp : l.1.places[j]? with
  | none => rw [hp] at h; simp at h
  | some p =>
      rw [hp] at h
      simp only [decide_eq_true_eq] at h
      exact ⟨p, rfl, h.2⟩

/-- Under an ascending key, at most one admitting case holds a key. -/
theorem holds_unique {k : Code} {j x : Nat} (hkey : keyAscending k j = true) {a b : Case × Nat × Nat}
    (ha : a ∈ k.trie.leaves) (hb : b ∈ k.trie.leaves) (hax : holds j x a = true) (hbx : holds j x b = true) :
    a = b := by
  by_cases hab : a = b
  · exact hab
  exfalso
  obtain ⟨har, p, hp, hplo, hphi⟩ := holds_spec hax
  obtain ⟨hbr, q, hq, hqlo, hqhi⟩ := holds_spec hbx
  have hma : a ∈ admitting k := mem_admitting.mpr ⟨ha, har⟩
  have hmb : b ∈ admitting k := mem_admitting.mpr ⟨hb, hbr⟩
  rcases pairwiseB_order _ a b hkey hma hmb hab with h | h
  · simp only [below, hp, hq, decide_eq_true_eq] at h; omega
  · simp only [below, hp, hq, decide_eq_true_eq] at h; omega

/-- The case a value is written in is the case its key selects. -/
theorem keyCase_of_choose {k : Code} {j : Nat} (hkey : keyAscending k j = true) {v : List Nat} {x : Nat}
    (hx : v[j]? = some x) {l : Case × Nat × Nat} (h : k.choose v = some l) : keyCase k j x = some l := by
  obtain ⟨hl, hadm⟩ := Code.choose_spec h
  obtain ⟨p, hp, hlo, hhi⟩ := place_of_admits hadm hx
  have hr : l.1.reserved = false := by
    unfold Case.admits at hadm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm
    exact hadm.1
  have hlx : holds j x l = true := by simp [holds, hr, hp, hlo, hhi]
  exact find?_unique _ l hl hlx (fun m hm hmx => holds_unique hkey hm hl hmx hlx)

/-- A value is written in the case its key selects when that case admits it. -/
theorem choose_of_keyCase {k : Code} (hk : k.Facts) {j : Nat} {v : List Nat} {x : Nat}
    {l : Case × Nat × Nat} (h : keyCase k j x = some l) (hadm : l.1.admits v = true) : k.choose v = some l := by
  have hl : l ∈ k.trie.leaves := List.mem_of_find?_eq_some h
  exact find?_unique _ l hl hadm (fun m hm hma => Code.admits_unique hk hm hl hma hadm)

/-- Under an ascending key, a value has a word exactly when the case its key
selects admits it. -/
theorem encode_isSome_iff {k : Code} (hk : k.Facts) {j : Nat} (hkey : keyAscending k j = true)
    {v : List Nat} {x : Nat} (hx : v[j]? = some x) :
    (k.encode v).isSome = true ↔ ∃ l, keyCase k j x = some l ∧ l.1.admits v = true := by
  constructor
  · intro h
    unfold Code.encode at h
    cases hc : k.choose v with
    | none => rw [hc] at h; simp at h
    | some l => exact ⟨l, keyCase_of_choose hkey hx hc, (Code.choose_spec hc).2⟩
  · rintro ⟨l, hl, hadm⟩
    unfold Code.encode
    rw [choose_of_keyCase hk hl hadm]
    rfl

/-! ## Views by key -/

/-- An expression per case, chosen by the key (parameter 0): the first
admitting case whose key range holds it, or 0. -/
def byKey (j : Nat) (leafExpr : Case → Expr) : List (Case × Nat × Nat) → Expr
  | [] => .lit 0
  | l :: ls =>
      if l.1.reserved then byKey j leafExpr ls
      else match l.1.places[j]? with
        | some p => .ite (inBounds p 0) (leafExpr l.1) (byKey j leafExpr ls)
        | none => byKey j leafExpr ls

theorem eval_inBounds {p : Place} (hp : fits64 p = true) {x : Nat} (hx : x < top) :
    eval [x] (inBounds p 0) = some (if p.lo ≤ x ∧ x ≤ p.hi then 1 else 0) := by
  have hb := fits_bounds hp
  have hv : eval [x] (.var 0) = some x := rfl
  simp only [inBounds, eval, eval_atLeast hv hb.1, eval_atMost hv hx hb.2, lift2_some, bit_and_bit]

theorem eval_byKey (j : Nat) (leafExpr : Case → Expr) (g : Case → Nat) {x : Nat} (hx : x < top) :
    ∀ ls : List (Case × Nat × Nat),
      (∀ l ∈ ls, (∀ p ∈ l.1.places, fits64 p = true) ∧ eval [x] (leafExpr l.1) = some (g l.1)) →
      eval [x] (byKey j leafExpr ls) = some (((ls.find? (holds j x)).map (g ·.1)).getD 0)
  | [], _ => by simp [byKey, eval, top]
  | l :: ls, h => by
      have hrest := eval_byKey j leafExpr g hx ls (fun m hm => h m (by simp [hm]))
      obtain ⟨hf, hg⟩ := h l (by simp)
      by_cases hr : l.1.reserved = true
      · have : holds j x l = false := by simp [holds, hr]
        simp only [byKey, hr, if_true, hrest, List.find?_cons, this]
      · have hr' : l.1.reserved = false := by simpa using hr
        cases hp : l.1.places[j]? with
        | none =>
            have : holds j x l = false := by simp [holds, hp]
            simp [byKey, hr', hp, hrest, this]
        | some p =>
            have hin := eval_inBounds (hf p (List.mem_of_getElem? hp)) hx
            by_cases hb : p.lo ≤ x ∧ x ≤ p.hi
            · have : holds j x l = true := by simp [holds, hr', hp, hb]
              simp [byKey, hr', hp, eval, hin, hb, hg, this]
            · have : holds j x l = false := by simp [holds, hr', hp, hb]
              simp [byKey, hr', hp, eval, hin, hb, hrest, this]

/-- The bounds of field `i` in the case that holds the key. -/
def keyBound (k : Code) (upper : Bool) (i j x : Nat) : Nat :=
  ((keyCase k j x).map (caseBound upper i ·.1)).getD 0

theorem eval_keyBound {k : Code} (hf : allFit64 k = true) (upper : Bool) (i j : Nat) {x : Nat} (hx : x < top) :
    eval [x] (byKey j (boundLeaf upper i) k.trie.leaves) = some (keyBound k upper i j x) := by
  apply eval_byKey j _ _ hx
  intro l hl
  exact ⟨fits_of_leaf hf hl, by simp [boundLeaf, eval, caseBound_lt (fits_of_leaf hf hl) upper i]⟩

theorem eval_keyAdmits {k : Code} (hf : allFit64 k = true) (j : Nat) {x : Nat} (hx : x < top) :
    eval [x] (byKey j (fun _ => .lit 1) k.trie.leaves) = some (if (keyCase k j x).isSome then 1 else 0) := by
  rw [eval_byKey j _ (fun _ => 1) hx]
  · unfold keyCase
    cases k.trie.leaves.find? (holds j x) <;> rfl
  · intro l hl
    exact ⟨fits_of_leaf hf hl, by simp [eval, top]⟩

/-- An admitted value lies within the bounds its key selects. -/
theorem keyBound_spec {k : Code} {j : Nat} (hkey : keyAscending k j = true) {v : List Nat} {x : Nat}
    (hx : v[j]? = some x) (hv : (k.encode v).isSome = true) {i y : Nat} (hy : v[i]? = some y) :
    keyBound k false i j x ≤ y ∧ y ≤ keyBound k true i j x := by
  unfold Code.encode at hv
  cases hc : k.choose v with
  | none => rw [hc] at hv; simp at hv
  | some l =>
      have hkc := keyCase_of_choose hkey hx hc
      obtain ⟨p, hp, hlo, hhi⟩ := place_of_admits (Code.choose_spec hc).2 hy
      simp [keyBound, hkc, caseBound, hp, bound, hlo, hhi]

/-! ## Writing an admitted value -/

/-- The stored field `j` shifted into its slot, without truncating it to the
slot: exact for a value within the place's bounds. -/
def placeExpr (p : Place) (j : Nat) : Expr :=
  if p.slot.width = 0 then .lit 0
  else .shl (if p.offset = 0 then .var j else .sub (.var j) (.lit p.offset)) p.slot.shift

def packedFrom : List Place → Nat → Expr
  | [], _ => .lit 0
  | p :: ps, j => .bor (placeExpr p j) (packedFrom ps (j + 1))

/-- The word of an admitted value in a case: its prefix, then its fields. -/
def packedWord (W : Nat) (l : Case × Nat × Nat) : Expr :=
  .bor (.lit (l.2.1 * 2 ^ (W - l.2.2))) (packedFrom l.1.places 0)

theorem eval_place {env : List Nat} {j x : Nat} (hx : env[j]? = some x) {p : Place} (hf : fits64 p = true)
    (hlo : p.offset ≤ x) (hle : x ≤ p.hi) (hfit : p.hi < p.offset + 2 ^ p.slot.width)
    (hin : p.slot.shift + p.slot.width ≤ 64) :
    eval env (placeExpr p j) = eval env (writeExpr p j) := by
  have hhi : x < p.offset + 2 ^ p.slot.width := by omega
  rw [eval_write hx hf hlo hle hin]
  unfold fits64 at hf
  simp only [decide_eq_true_eq] at hf
  obtain ⟨hs, hn, hoff, _, _⟩ := hf
  have hmod : (x - p.offset) % 2 ^ p.slot.width = x - p.offset := Nat.mod_eq_of_lt (by omega)
  unfold placeExpr
  split
  · rename_i h0
    simp [eval, top, h0, Nat.mod_one]
  · rename_i h0
    have hs' : p.slot.shift < 64 := hs.resolve_left h0
    have hfit : (x - p.offset) * 2 ^ p.slot.shift < top := by
      have h1 : (x - p.offset) * 2 ^ p.slot.shift < 2 ^ p.slot.width * 2 ^ p.slot.shift :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      have h2 : 2 ^ p.slot.width * 2 ^ p.slot.shift ≤ top := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hoffl : p.offset < top := by have := Nat.two_pow_pos p.slot.width; omega
    have hsub : (x + top - p.offset) % top = x - p.offset := by
      rw [show x + top - p.offset = (x - p.offset) + top by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    split
    · rename_i hz
      have hfit0 : x * 2 ^ p.slot.shift < top := by simpa [hz] using hfit
      simp [eval, hs', hx, hz, Nat.mod_eq_of_lt hfit0]
    · simp [eval, hs', hx, hoffl, hsub, Nat.mod_eq_of_lt hfit]

theorem eval_packedFrom (env : List Nat) : ∀ (ps : List Place) (j : Nat),
    (∀ p ∈ ps, fits64 p = true ∧ p.offset ≤ p.lo ∧ p.hi < p.offset + 2 ^ p.slot.width ∧
      p.slot.shift + p.slot.width ≤ 64) →
    (env.drop j).length = ps.length → within ps (env.drop j) = true →
    eval env (packedFrom ps j) = eval env (packFrom ps j)
  | [], _, _, _, _ => rfl
  | p :: ps, j, hf, hl, hw => by
      have hj : j < env.length := by
        have := hl; simp only [List.length_drop, List.length_cons] at this; omega
      have hd : env.drop j = env[j] :: env.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [hd] at hl hw
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨hfp, hlo, hhi, hin⟩ := hf p (by simp)
      have hrest := eval_packedFrom env ps (j + 1) (fun q hq => hf q (by simp [hq]))
        (by simp only [List.length_cons, Nat.add_right_cancel_iff] at hl; exact hl) hw.2
      simp only [packedFrom, packFrom, eval,
        eval_place (List.getElem?_eq_getElem hj) hfp (by omega) hw.1.2 hhi hin, hrest]

theorem eval_packedWord {W : Nat} (hW : W ≤ 64) {env : List Nat} {l : Case × Nat × Nat} (hl : Writable W l)
    (hfit : ∀ p ∈ l.1.places, p.hi < p.offset + 2 ^ p.slot.width)
    (hlen : env.length = l.1.places.length) (hadm : l.1.admits env = true) :
    eval env (packedWord W l) = some (wordOf W env l) := by
  rw [← eval_word hW hl hlen hadm]
  have hadm' := hadm
  unfold Case.admits at hadm'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm'
  obtain ⟨hplace, hoff, _, _, _⟩ := hl
  have h := eval_packedFrom env l.1.places 0
    (fun p hp => ⟨(hplace p hp).1, hoff hadm'.1 p hp, hfit p hp, by have := (hplace p hp).2; omega⟩)
    (by simpa using hlen) (by simpa using hadm'.2)
  simp only [packedWord, wordExpr, eval, h]

/-- One comparison of the key (field `j`) per admitting case, in prefix order;
the last case takes every remaining value. -/
def packChain (W j : Nat) : List (Case × Nat × Nat) → Expr
  | [] => .lit 0
  | [l] => packedWord W l
  | l :: ls =>
      match l.1.places[j]? with
      | some p => .ite (atMost (.var j) p.hi) (packedWord W l) (packChain W j ls)
      | none => .lit 0

/-- The unchecked encoder: correct for admitted values only. -/
def packExpr (k : Code) (j : Nat) : Expr := packChain k.width j (admitting k)

theorem eval_packChain {W : Nat} (hW : W ≤ 64) (j : Nat) {v : List Nat} (hv : ∀ x ∈ v, x < top)
    {l : Case × Nat × Nat} (hwl : Writable W l) (hfit : ∀ p ∈ l.1.places, p.hi < p.offset + 2 ^ p.slot.width)
    (hlen : v.length = l.1.places.length) (hadm : l.1.admits v = true) :
    ∀ ls : List (Case × Nat × Nat), l ∈ ls → pairwiseB (below j) ls = true →
      (∀ m ∈ ls, ∀ p ∈ m.1.places, fits64 p = true) → eval v (packChain W j ls) = some (wordOf W v l)
  | [], hl, _, _ => by simp at hl
  | [m], hl, _, _ => by
      simp only [List.mem_singleton] at hl
      subst hl
      exact eval_packedWord hW hwl hfit hlen hadm
  | m :: r :: rs, hl, hp, hf => by
      rw [pairwiseB, Bool.and_eq_true, List.all_eq_true] at hp
      have hj : j < v.length := by
        have := hp.1 r (by simp)
        unfold below at this
        by_cases hm : m = l
        · subst hm
          cases hq : m.1.places[j]? with
          | none => rw [hq] at this; simp at this
          | some q => rw [hlen]; exact (List.getElem?_eq_some_iff.mp hq).1
        · have hlr : l ∈ r :: rs := by
            rcases List.mem_cons.mp hl with h | h
            · exact absurd h.symm hm
            · exact h
          have hb := hp.1 l hlr
          unfold below at hb
          cases hq : l.1.places[j]? with
          | none => rw [hq] at hb; cases m.1.places[j]? <;> simp at hb
          | some q => rw [hlen]; exact (List.getElem?_eq_some_iff.mp hq).1
      have hxj : v[j]? = some v[j] := List.getElem?_eq_getElem hj
      have hvar : eval v (.var j) = some v[j] := hxj
      have hxt : v[j] < top := hv _ (List.getElem_mem hj)
      obtain ⟨q, hq, hqlo, hqhi⟩ := place_of_admits hadm hxj
      by_cases hm : m = l
      · subst hm
        have hqf := fits_bounds (hf m (by simp) q (List.mem_of_getElem? hq))
        have hle : eval v (atMost (.var j) q.hi) = some 1 := by
          rw [eval_atMost hvar hxt hqf.2]; simp [hqhi]
        simp only [packChain, hq, eval, hle, choose_some, ne_eq, Nat.one_ne_zero, not_false_eq_true, if_true]
        exact eval_packedWord hW hwl hfit hlen hadm
      · have hlr : l ∈ r :: rs := by
          rcases List.mem_cons.mp hl with h | h
          · exact absurd h.symm hm
          · exact h
        have hb := hp.1 l hlr
        cases hp' : m.1.places[j]? with
        | none => simp [below, hp'] at hb
        | some p =>
            simp only [below, hp', hq, decide_eq_true_eq] at hb
            have hpf := fits_bounds (hf m (by simp) p (List.mem_of_getElem? hp'))
            have hgt : eval v (atMost (.var j) p.hi) = some 0 := by
              rw [eval_atMost hvar hxt hpf.2]
              have : ¬ v[j] ≤ p.hi := by omega
              simp [this]
            simp only [packChain, hp', eval, hgt, choose_some, ne_eq, not_true_eq_false, if_false]
            exact eval_packChain hW j hv hwl hfit hlen hadm (r :: rs) hlr hp.2
              (fun m' hm' => hf m' (List.mem_cons_of_mem _ hm'))

/-- For an admitted value, the unchecked encoder writes the value's word. -/
theorem eval_pack {k : Code} (hk : k.Facts) (hf : allFit64 k = true) {j : Nat} (hkey : keyAscending k j = true)
    {v : List Nat} (hv : ∀ x ∈ v, x < top) (hlen : ∀ l ∈ k.trie.leaves, l.1.places.length = v.length)
    {w : Nat} (he : k.encode v = some w) : eval v (packExpr k j) = some w := by
  unfold Code.encode at he
  cases hc : k.choose v with
  | none => rw [hc] at he; simp at he
  | some l =>
      rw [hc] at he
      simp only [Option.map_some, Option.some.injEq] at he
      obtain ⟨hl, hadm⟩ := Code.choose_spec hc
      have hr : l.1.reserved = false := by
        unfold Case.admits at hadm
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm
        exact hadm.1
      rw [← he]
      have hfit : ∀ p ∈ l.1.places, p.hi < p.offset + 2 ^ p.slot.width := by
        intro p hp
        have hc := (hk.leaf l hl).2
        unfold Case.fits at hc
        rw [hr, Bool.false_or, List.all_eq_true] at hc
        exact (of_decide_eq_true (hc p hp)).2
      exact eval_packChain (width_le hf) j hv (writable_of_facts hk hf l hl) hfit (hlen l hl).symm hadm
        (admitting k) (mem_admitting.mpr ⟨hl, hr⟩) hkey
        (fun m hm => fits_of_leaf hf (mem_admitting.mp hm).1)

/-- A layout with one admitting case needs no key to pack. -/
theorem keyAscending_single {k : Code} (j : Nat) (h : (admitting k).length = 1) : keyAscending k j = true := by
  unfold keyAscending
  match hk : admitting k, h with
  | [_], _ => simp [pairwiseB]

/-! ## The views of a declared layout -/

open Mettapedia.GSLT.LanguageDef.LayoutDeclarations (Field)

def indexed (d : Declaration) : List (Nat × Field) := (List.range d.fields.length).zip d.fields

/-- For a word with several cases: each field's bounds in the word's case. -/
def boundFunctions (d : Declaration) : List Function :=
  match d.code.trie with
  | .leaf _ => []
  | .node _ _ => (indexed d).flatMap fun (j, f) =>
      [⟨d.name ++ "_" ++ f.name ++ "_lo", ["word"], "value", boundExpr d.code.width false j d.code.trie 0⟩,
       ⟨d.name ++ "_" ++ f.name ++ "_hi", ["word"], "value", boundExpr d.code.width true j d.code.trie 0⟩]

/-- For a keyed layout: each field's bounds in the key's case, and whether
some case holds the key. -/
def keyFunctions (d : Declaration) : Option Nat → List Function
  | none => []
  | some j =>
      let key := (d.fields[j]?.map (·.name)).getD ""
      (indexed d).flatMap (fun (i, f) =>
        [⟨d.name ++ "_" ++ f.name ++ "_lo_for_" ++ key, [key], "value", byKey j (boundLeaf false i) d.code.trie.leaves⟩,
         ⟨d.name ++ "_" ++ f.name ++ "_hi_for_" ++ key, [key], "value", byKey j (boundLeaf true i) d.code.trie.leaves⟩]) ++
      [⟨d.name ++ "_admits_" ++ key, [key], "bool", byKey j (fun _ => .lit 1) d.code.trie.leaves⟩]

/-- The unchecked encoder, for a keyed layout or one with a single admitting case. -/
def packFunctions (d : Declaration) (key : Option Nat) : List Function :=
  if key.isSome || (admitting d.code).length == 1 then
    [⟨d.name ++ "_pack", d.fields.map (·.name), "word", packExpr d.code (key.getD 0)⟩]
  else []

/-- Every view Cesta generates for a layout, in the order it prints them. -/
def lowerViews (d : Declaration) (key : Option Nat) : List Function :=
  boundFunctions d ++ keyFunctions d key ++ packFunctions d key

/-! ## Views as Cesta records them -/

def decodeConstant : Atom → Option (String × Nat)
  | .list [.text name, value] => do pure (name, ← LayoutDeclarations.number value)
  | _ => none

/-- `(cesta-layout-views/1 NAME (Constants ("C_NAME" VALUE) …) (Function …) …)`. -/
def decodeViews : Atom → Option (String × List (String × Nat) × List Function)
  | .list (.symbol "cesta-layout-views/1" :: .symbol name :: .list (.symbol "Constants" :: cs) :: fs) => do
      pure (name, ← cs.mapM decodeConstant, ← fs.mapM decodeFunction)
  | _ => none

/-- The printed constants: the declared ones, named after their layout. -/
def exportedConstants (d : Declaration) (a : Atom) : List (String × Nat) :=
  (constantsOf a).map fun c => (d.name ++ "_" ++ c.1, c.2)

/-- A layout's recorded views are admitted when the layout is, its places
print in 64 bits, its key ascends, its constants are the declared ones and the
recorded functions are exactly its views. -/
def viewsAdmitted (layout views : Atom) : Bool :=
  match decodeLayout layout, decodeViews views with
  | some d, some (name, cs, fs) =>
      admitted layout && allFit64 d.code && name == d.name && cs == exportedConstants d layout &&
        (match keyOf layout with
          | some j => keyAscending d.code j && decide (j < d.fields.length)
          | none => true) &&
        fs == lowerViews d (keyOf layout)
  | _, _ => false

theorem views_of_admitted {la va : Atom} (h : viewsAdmitted la va = true) :
    ∃ d cs fs, decodeLayout la = some d ∧ decodeViews va = some (d.name, cs, fs) ∧
      cs = exportedConstants d la ∧ fs = lowerViews d (keyOf la) ∧ d.code.Facts ∧ allFit64 d.code = true ∧
      (∀ j, keyOf la = some j → keyAscending d.code j = true ∧ j < d.fields.length) := by
  unfold viewsAdmitted at h
  cases hd : decodeLayout la with
  | none => rw [hd] at h; simp at h
  | some d =>
      cases hv : decodeViews va with
      | none => rw [hd, hv] at h; simp at h
      | some r =>
          rw [hd, hv] at h
          obtain ⟨name, cs, fs⟩ := r
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨⟨⟨⟨hadm, hfit⟩, hname⟩, hcs⟩, hkey⟩, hfs⟩ := h
          obtain ⟨d', hd', facts⟩ := facts_of_admitted hadm
          rw [hd] at hd'
          cases hd'
          refine ⟨d, cs, fs, rfl, by rw [hname], hcs, hfs, facts, hfit, ?_⟩
          intro j hj
          rw [hj] at hkey
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hkey
          exact hkey

/-- A packed view is emitted only where the key ascends. -/
theorem pack_key {d : Declaration} {key : Option Nat} (hkey : ∀ j, key = some j → keyAscending d.code j = true)
    (h : packFunctions d key ≠ []) : keyAscending d.code (key.getD 0) = true := by
  unfold packFunctions at h
  cases key with
  | some j => exact hkey j rfl
  | none =>
      simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at h
      by_cases h1 : (admitting d.code).length = 1
      · exact keyAscending_single 0 h1
      · simp [h1] at h

/-! ## Examples -/

/-- A byte keyed by its first field: case `0` holds keys 1–15 with a 3-bit
tag, case `1` keys 16–79 with a 1-bit tag. -/
def keyedByte : Code :=
  ⟨8, .node (.leaf ⟨[⟨⟨0, 4⟩, 0, 1, 15⟩, ⟨⟨4, 3⟩, 0, 0, 7⟩], false⟩)
            (.leaf ⟨[⟨⟨0, 6⟩, 16, 16, 79⟩, ⟨⟨6, 1⟩, 0, 0, 1⟩], false⟩)⟩

example : keyedByte.wellFormed = true := by decide
example : keyAscending keyedByte 0 = true := by decide
/-- The tag field does not key it: both cases hold tag 0. -/
example : keyAscending keyedByte 1 = false := by decide
example : eval [20, 1] (packExpr keyedByte 0) = keyedByte.encode [20, 1] := by decide
example : eval [3] (byKey 0 (boundLeaf true 1) keyedByte.trie.leaves) = some 7 := by decide
example : eval [40] (byKey 0 (boundLeaf true 1) keyedByte.trie.leaves) = some 1 := by decide
/-- No case holds key 0. -/
example : eval [0] (byKey 0 (fun _ => .lit 1) keyedByte.trie.leaves) = some 0 := by decide
/-- The unchecked encoder trusts its caller: a key beyond every case is
written into the last case regardless. -/
example : eval [200, 0] (packExpr keyedByte 0) ≠ keyedByte.encode [200, 0] := by decide

end Mettapedia.GSLT.LanguageDef.LayoutViews
