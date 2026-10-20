import Mettapedia.GSLT.LanguageDef.LayoutDeclarations

/-!
# Field kinds: how a word is derived and how it travels

A flags word of a term node packs facts of different kinds. The kind of a
field decides how a parent's word is derived from its children's:

- `anyChild`: the parent has it when some child has it (a summary such as
  "has variables", or a Bloom filter of the variables);
- `allChildren`: the parent has it when every child has it ("hash stable");
- `value`, `fact`, `reference`: the node's own, supplied when it is built;
- `cache`, `occurrence`: never inherited; a new parent starts without them.

`derive` builds the parent's word from three masks computed from the
declaration, by allowlist: only bits of the first five kinds can be set, so
an occurrence mark (HE's "this value was evaluated") cannot leak from a child,
and a field added later gets its kind's behaviour instead of whatever the old
word held.

The theorems:
- `testBit_derive`: each bit of a derived word, by the kind of its field;
- `summary_any` and `summary_all`: over a whole term, a summary bit is set
  exactly when some (every) leaf has it, so a missing summary bit proves
  absence (`absent_of_summary`);
- `summary_occurrence`: an occurrence mark is never set on a derived node;
- `testBit_apply`: an operation (copy, storage, relocation) keeps exactly the
  kinds its table keeps, so storing drops occurrence marks
  (`store_drops_occurrence`);
- `exactly_one_kind`: in a well-formed flags word every bit belongs to
  exactly one field, hence has exactly one kind.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutKinds

open Nat
open Mettapedia.GSLT.LanguageDef.LayoutAlgebra
open Mettapedia.GSLT.LanguageDef.LayoutCodes

inductive Kind where
  | value | anyChild | allChildren | fact | cache | occurrence | reference
deriving DecidableEq, Repr

def Kind.ofString : String → Option Kind
  | "value" => some .value
  | "any-child" => some .anyChild
  | "all-children" => some .allChildren
  | "fact" => some .fact
  | "cache" => some .cache
  | "occurrence" => some .occurrence
  | "reference" => some .reference
  | _ => none

/-- The node supplies these kinds itself. -/
def Kind.own : Kind → Bool
  | .value | .fact | .reference => true
  | _ => false

def Kind.isAny : Kind → Bool
  | .anyChild => true
  | _ => false

def Kind.isAll : Kind → Bool
  | .allChildren => true
  | _ => false

/-! ## Masks -/

/-- The bits of a slot. -/
def slotMask (s : Slot) : Nat := (2 ^ s.width - 1) * 2 ^ s.shift

theorem testBit_slotMask (s : Slot) (i : Nat) : (slotMask s).testBit i = s.holds i := by
  unfold slotMask Slot.holds
  rw [testBit_mul_two_pow, testBit_two_pow_sub_one]
  by_cases h : s.shift ≤ i
  · simp only [h, decide_true, Bool.true_and, true_and]
    exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩
  · simp [h]

/-- The bits of every field whose kind satisfies `p`. -/
def maskOf (fields : List (Slot × Kind)) (p : Kind → Bool) : Nat :=
  fields.foldr (fun f m => if p f.2 then slotMask f.1 ||| m else m) 0

theorem testBit_maskOf (fields : List (Slot × Kind)) (p : Kind → Bool) (i : Nat) :
    (maskOf fields p).testBit i = fields.any fun f => p f.2 && f.1.holds i := by
  induction fields with
  | nil => simp [maskOf]
  | cons f fields ih =>
      unfold maskOf at ih ⊢
      simp only [List.foldr_cons, List.any_cons]
      by_cases hp : p f.2 = true
      · rw [if_pos hp, testBit_or, testBit_slotMask, ih, hp, Bool.true_and]
      · rw [if_neg hp, ih]
        simp [hp]

/-! ## Deriving a parent's word -/

def orAll (words : List Nat) : Nat := words.foldr (· ||| ·) 0
def andAll (top : Nat) (words : List Nat) : Nat := words.foldr (· &&& ·) top

theorem testBit_orAll (words : List Nat) (i : Nat) :
    (orAll words).testBit i = words.any (·.testBit i) := by
  induction words with
  | nil => simp [orAll]
  | cons w ws ih => unfold orAll at ih ⊢; simp [ih]

theorem testBit_andAll (top : Nat) (words : List Nat) (i : Nat) :
    (andAll top words).testBit i = (words.all (·.testBit i) && top.testBit i) := by
  induction words with
  | nil => simp [andAll]
  | cons w ws ih => unfold andAll at ih ⊢; simp [ih, Bool.and_assoc]

/-- The masks a flags word's kinds give. -/
structure Masks where
  any : Nat
  all : Nat
  own : Nat

def masksOf (fields : List (Slot × Kind)) : Masks :=
  ⟨maskOf fields Kind.isAny, maskOf fields Kind.isAll, maskOf fields Kind.own⟩

/-- A parent's word, from its children's words and its own: summaries from the
children, its own kinds from `own`, and nothing else. -/
def derive (m : Masks) (children : List Nat) (own : Nat) : Nat :=
  (orAll children &&& m.any) ||| (andAll m.all children &&& m.all) ||| (own &&& m.own)

theorem testBit_derive (m : Masks) (children : List Nat) (own i : Nat) :
    (derive m children own).testBit i =
      ((m.any.testBit i && children.any (·.testBit i)) ||
        (m.all.testBit i && children.all (·.testBit i)) || (m.own.testBit i && own.testBit i)) := by
  unfold derive
  simp only [testBit_or, testBit_and, testBit_orAll, testBit_andAll]
  cases m.any.testBit i <;> cases m.all.testBit i <;> cases m.own.testBit i <;>
    cases own.testBit i <;> cases children.any (·.testBit i) <;> cases children.all (·.testBit i) <;> rfl

/-! ## Every bit has one kind -/

/-- The kind of the field holding bit `i`, if any. -/
def kindAt (fields : List (Slot × Kind)) (i : Nat) : Option Kind :=
  (fields.find? fun f => f.1.holds i).map (·.2)

theorem any_eq_kindAt {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (p : Kind → Bool) (i : Nat) :
    (fields.any fun f => p f.2 && f.1.holds i) = ((kindAt fields i).map p).getD false := by
  induction fields with
  | nil => simp [kindAt]
  | cons f fields ih =>
      simp only [List.map_cons, pairwiseDisjoint, Bool.and_eq_true] at hd
      simp only [List.any_cons, kindAt, List.find?_cons]
      by_cases hf : f.1.holds i = true
      · simp only [hf, Bool.and_true, Option.map_some, Option.getD_some]
        have none : (fields.any fun g => p g.2 && g.1.holds i) = false := by
          rw [List.any_eq_false]
          intro g hg
          have hdis : (fields.map (·.1)).all f.1.disjoint = true := hd.1
          rw [List.all_eq_true] at hdis
          have := Slot.not_holds_of_disjoint (hdis g.1 (List.mem_map.mpr ⟨g, hg, rfl⟩)) hf
          simp [this]
        rw [none, Bool.or_false]
      · have hf' : f.1.holds i = false := by simpa using hf
        simp only [hf', Bool.and_false, Bool.false_or]
        exact ih hd.2

/-- A mask's bit, by the kind of the field holding the bit. -/
theorem testBit_maskOf_kind {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (p : Kind → Bool) (i : Nat) : (maskOf fields p).testBit i = ((kindAt fields i).map p).getD false := by
  rw [testBit_maskOf, any_eq_kindAt hd]

/-- In a flags word whose slots tile `W` bits, every bit below `W` belongs to
exactly one field, and so has exactly one kind. -/
theorem exactly_one_kind {fields : List (Slot × Kind)} {W : Nat}
    (hc : covers (fields.map (·.1)) W = true)
    {i : Nat} (hi : i < W) : ∃ k, kindAt fields i = some k := by
  unfold covers at hc
  rw [List.all_eq_true] at hc
  have := hc i (List.mem_range.mpr hi)
  rw [List.any_map] at this
  obtain ⟨f, hf, hfi⟩ := List.any_eq_true.mp this
  unfold kindAt
  cases h : fields.find? (fun f => f.1.holds i) with
  | none =>
      exact absurd (List.find?_eq_none.mp h f hf) (by simpa using hfi)
  | some g => exact ⟨g.2, rfl⟩

/-- The derived word, bit by bit, by the kind of the bit's field. -/
theorem testBit_derive_kind {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (children : List Nat) (own i : Nat) :
    (derive (masksOf fields) children own).testBit i =
      match kindAt fields i with
      | some .anyChild => children.any (·.testBit i)
      | some .allChildren => children.all (·.testBit i)
      | some .value | some .fact | some .reference => own.testBit i
      | some .cache | some .occurrence | none => false := by
  rw [testBit_derive]
  simp only [masksOf, testBit_maskOf_kind hd]
  cases kindAt fields i with
  | none => simp
  | some k => cases k <;> simp [Kind.own, Kind.isAny, Kind.isAll]

/-! ## Over a whole term -/

/-- A term as its nodes' words: a leaf's word is computed where it is built; a
node's word is derived from its children's. -/
inductive Term where
  | leaf (word : Nat)
  | node (children : List Term)

mutual
  def Term.word (m : Masks) : Term → Nat
    | .leaf w => w
    | .node cs => derive m (Term.words m cs) 0
  def Term.words (m : Masks) : List Term → List Nat
    | [] => []
    | c :: cs => c.word m :: Term.words m cs
end

mutual
  def Term.leaves : Term → List Nat
    | .leaf w => [w]
    | .node cs => Term.leavesMany cs
  def Term.leavesMany : List Term → List Nat
    | [] => []
    | c :: cs => c.leaves ++ Term.leavesMany cs
end

mutual
  theorem summary_any (m : Masks) {i : Nat} (hi : m.any.testBit i = true) (hall : m.all.testBit i = false) :
      ∀ t : Term, (t.word m).testBit i = t.leaves.any (·.testBit i)
    | .leaf _ => by simp [Term.word, Term.leaves]
    | .node cs => by
        simp only [Term.word, Term.leaves, testBit_derive, hi, hall, Bool.true_and, Bool.false_and,
          Bool.or_false, Nat.zero_testBit, Bool.and_false]
        exact summary_any_many m hi hall cs
  theorem summary_any_many (m : Masks) {i : Nat} (hi : m.any.testBit i = true)
      (hall : m.all.testBit i = false) :
      ∀ cs : List Term, (Term.words m cs).any (·.testBit i) = (Term.leavesMany cs).any (·.testBit i)
    | [] => by simp [Term.words, Term.leavesMany]
    | c :: cs => by
        simp only [Term.words, Term.leavesMany, List.any_cons, List.any_append]
        rw [summary_any m hi hall c, summary_any_many m hi hall cs]
end

mutual
  theorem summary_all (m : Masks) {i : Nat} (hi : m.all.testBit i = true) (hany : m.any.testBit i = false) :
      ∀ t : Term, (t.word m).testBit i = t.leaves.all (·.testBit i)
    | .leaf _ => by simp [Term.word, Term.leaves]
    | .node cs => by
        simp only [Term.word, Term.leaves, testBit_derive, hi, hany, Bool.true_and, Bool.false_and,
          Bool.false_or, Nat.zero_testBit, Bool.and_false, Bool.or_false]
        exact summary_all_many m hi hany cs
  theorem summary_all_many (m : Masks) {i : Nat} (hi : m.all.testBit i = true)
      (hany : m.any.testBit i = false) :
      ∀ cs : List Term, (Term.words m cs).all (·.testBit i) = (Term.leavesMany cs).all (·.testBit i)
    | [] => by simp [Term.words, Term.leavesMany]
    | c :: cs => by
        simp only [Term.words, Term.leavesMany, List.all_cons, List.all_append]
        rw [summary_all m hi hany c, summary_all_many m hi hany cs]
end

/-- A missing summary bit proves that no leaf has it: when each leaf's bits
cover the hashed bits of its variables, a variable whose bit is missing from
a term's summary does not occur in the term. -/
theorem absent_of_summary (m : Masks) {i : Nat} (hi : m.any.testBit i = true) (hall : m.all.testBit i = false)
    (t : Term) (h : (t.word m).testBit i = false) : ∀ w ∈ t.leaves, w.testBit i = false := by
  rw [summary_any m hi hall t, List.any_eq_false] at h
  intro w hw
  simpa using h w hw

/-- A derived node never carries an occurrence mark or a cache bit. -/
theorem summary_occurrence {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    {i : Nat} (hk : kindAt fields i = some .occurrence ∨ kindAt fields i = some .cache) (cs : List Term) :
    ((Term.node cs).word (masksOf fields)).testBit i = false := by
  simp only [Term.word]
  rw [testBit_derive_kind hd]
  rcases hk with hk | hk <;> rw [hk]

/-! ## Operations on a word -/

inductive Operation where
  | valueCopy | storage | relocation
deriving DecidableEq, Repr

/-- What an operation keeps: a stored atom is syntax, so it drops the marks of
an evaluated occurrence; copies and relocations keep everything. -/
def keeps : Operation → Kind → Bool
  | .storage, .occurrence => false
  | _, _ => true

/-- An operation on a word of `W` bits: the bits of the kinds it keeps. -/
def apply (fields : List (Slot × Kind)) (W : Nat) (op : Operation) (w : Nat) : Nat :=
  w &&& maskOf fields (keeps op) &&& (2 ^ W - 1)

theorem testBit_apply {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (W : Nat) (op : Operation) (w i : Nat) :
    (apply fields W op w).testBit i =
      (decide (i < W) && w.testBit i && ((kindAt fields i).map (keeps op)).getD false) := by
  unfold apply
  rw [testBit_and, testBit_and, testBit_maskOf_kind hd, testBit_two_pow_sub_one]
  cases decide (i < W) <;> cases w.testBit i <;> cases ((kindAt fields i).map (keeps op)).getD false <;> rfl

theorem store_drops_occurrence {fields : List (Slot × Kind)} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (W w : Nat) {i : Nat} (hk : kindAt fields i = some .occurrence) :
    (apply fields W .storage w).testBit i = false := by
  rw [testBit_apply hd, hk]
  simp [keeps]

theorem copy_keeps {fields : List (Slot × Kind)} {W w : Nat} (hd : pairwiseDisjoint (fields.map (·.1)) = true)
    (hc : covers (fields.map (·.1)) W = true) (hw : w < 2 ^ W) : apply fields W .valueCopy w = w := by
  apply eq_of_testBit_eq
  intro i
  rw [testBit_apply hd]
  by_cases hi : i < W
  · obtain ⟨k, hk⟩ := exactly_one_kind hc hi
    rw [hk]
    cases k <;> simp [keeps, hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact (testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))).symm

/-! ## Declared flags words -/

open Mettapedia.GSLT.LanguageDef.LayoutDeclarations

/-- A declared single-case layout's fields with their kinds. -/
def flagsOf (d : Declaration) : Option (List (Slot × Kind)) :=
  match d.code.trie with
  | .leaf c => do
      let kinds ← d.fields.mapM fun f => Kind.ofString f.kind
      if kinds.length = c.places.length then some ((c.places.map (·.slot)).zip kinds) else none
  | .node _ _ => none

/-- An admitted flags word's fields tile it, so every bit has exactly one kind
and the derivation and operation laws above apply to it. -/
theorem flags_tile {a : Mettapedia.GSLT.LanguageDef.MacroExportPlan.Atom} {d : Declaration}
    {fields : List (Slot × Kind)} (ha : admitted a = true) (hd : decodeLayout a = some d)
    (hf : flagsOf d = some fields) :
    pairwiseDisjoint (fields.map (·.1)) = true ∧ covers (fields.map (·.1)) d.code.width = true := by
  obtain ⟨d', hd', facts⟩ := facts_of_admitted ha
  rw [hd] at hd'
  cases hd'
  unfold flagsOf at hf
  cases ht : d.code.trie with
  | node _ _ => rw [ht] at hf; simp at hf
  | leaf c =>
      rw [ht] at hf
      simp only [Option.bind_eq_bind] at hf
      cases hk : d.fields.mapM (fun f => Kind.ofString f.kind) with
      | none => rw [hk] at hf; simp at hf
      | some kinds =>
          rw [hk] at hf
          simp only [Option.bind_some] at hf
          split at hf
          · rename_i hlen
            simp only [Option.some.injEq] at hf
            subst hf
            have hmap : ((c.places.map (·.slot)).zip kinds).map (·.1) = c.places.map (·.slot) := by
              rw [List.map_fst_zip]; simp [hlen]
            have hl : (c, 0, 0) ∈ d.code.trie.leaves := by rw [ht]; simp [Trie.leaves]
            obtain ⟨htile, _⟩ := facts.leaf _ hl
            unfold Case.tiles at htile
            simp only [Bool.and_eq_true, Nat.sub_zero] at htile
            rw [hmap]
            exact ⟨htile.1.1, htile.1.2⟩
          · simp at hf

/-! ## Examples -/

/-- Three flags: a summary, a stability bit, and HE's evaluated mark. -/
def demo : List (Slot × Kind) := [(⟨0, 1⟩, .anyChild), (⟨1, 1⟩, .allChildren), (⟨2, 1⟩, .occurrence)]

/-- Children `0b101` (has variables, evaluated) and `0b011` (has variables,
stable): the parent has variables, is not stable, and is not evaluated. -/
example : derive (masksOf demo) [0b101, 0b011] 0 = 0b001 := by decide
/-- Storing drops the evaluated mark and keeps the rest. -/
example : apply demo 3 .storage 0b111 = 0b011 := by decide
/-- A copy keeps the mark. -/
example : apply demo 3 .valueCopy 0b111 = 0b111 := by decide
/-- Starting the parent from a child's word, as a hand-written constructor
might, would keep the mark; the derivation does not. -/
example : (derive (masksOf demo) [0b100] 0).testBit 2 = false := by decide

end Mettapedia.GSLT.LanguageDef.LayoutKinds
