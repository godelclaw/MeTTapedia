import Mettapedia.OSLF.MeTTaIL.CanonicalBags

/-!
# Comparing patterns field by field

`cmp table` compares two patterns in the lexicographic order of their serializations (`ser`,
`lexLe`) without building them: every field is serialized by a prefix-free code, so the first
field that differs decides. Names are compared by their position in a table that lists them in
the order of their serializations (`NameOrdered`). On patterns whose names are in the table
(`Covered`):

- `cmp_eq_lexCmp`: `cmp` is the lexicographic comparison of serializations;
- `patternLe_iff`: `cmp left right ≠ .gt` exactly when `PatternLe left right`;
- `sortBy_eq_sortLex`, `canonBy_eq_canon`: insertion sort by `cmp`, and the canonical form built
  with it, are `sortLex` and `canon`.

A MeTTa runtime computes `cmp` with comparisons of numbers and string equality only.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare

open Syntax PatternLexOrder CanonicalBags

/-! ## Lexicographic comparison of number lists -/

/-- Lexicographic comparison of number lists; a proper prefix comes first. -/
def lexCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (compare x y).then (lexCmp xs ys)

theorem then_assoc (first second third : Ordering) :
    (first.then second).then third = first.then (second.then third) := by
  cases first <;> rfl

theorem eq_then (second : Ordering) : Ordering.eq.then second = second := rfl

theorem compare_refl (n : Nat) : compare n n = .eq := Nat.compare_eq_eq.mpr rfl

theorem then_eq_eq {first second : Ordering} : first.then second = .eq ↔ first = .eq ∧ second = .eq := by
  cases first <;> simp [Ordering.then]

theorem lexLe_eq : ∀ xs ys : List Nat, lexLe xs ys = (lexCmp xs ys != .gt)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    rw [lexLe, lexCmp, lexLe_eq xs ys]
    rcases Nat.lt_trichotomy x y with less | same | more
    · simp [less, Nat.compare_eq_lt.mpr less, Ordering.then]
    · subst same
      simp [Ordering.then]
    · simp [Nat.not_lt.mpr (Nat.le_of_lt more), Nat.ne_of_gt more, Nat.compare_eq_gt.mpr more,
        Ordering.then]

theorem lexCmp_refl : ∀ xs : List Nat, lexCmp xs xs = .eq
  | [] => rfl
  | x :: xs => by simp [lexCmp, lexCmp_refl xs, Ordering.then]

theorem lexCmp_eq_iff : ∀ {xs ys : List Nat}, lexCmp xs ys = .eq ↔ xs = ys
  | [], [] => by simp [lexCmp]
  | [], _ :: _ => by simp [lexCmp]
  | _ :: _, [] => by simp [lexCmp]
  | x :: xs, y :: ys => by
    rw [lexCmp, then_eq_eq, lexCmp_eq_iff, Nat.compare_eq_eq, List.cons.injEq]

theorem lexCmp_swap : ∀ xs ys : List Nat, lexCmp ys xs = (lexCmp xs ys).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    rw [lexCmp, lexCmp, lexCmp_swap xs ys]
    rcases Nat.lt_trichotomy x y with less | same | more
    · rw [Nat.compare_eq_lt.mpr less, Nat.compare_eq_gt.mpr less]; rfl
    · subst same
      rw [compare_refl]
      rfl
    · rw [Nat.compare_eq_gt.mpr more, Nat.compare_eq_lt.mpr more]; rfl

/-- Equal-length blocks: the first block decides unless it ties. -/
theorem lexCmp_append_of_length : ∀ {xs ys : List Nat} (rest rest' : List Nat), xs.length = ys.length →
    lexCmp (xs ++ rest) (ys ++ rest') = (lexCmp xs ys).then (lexCmp rest rest')
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, lengths => by simp at lengths
  | _ :: _, [], _, _, lengths => by simp at lengths
  | x :: xs, y :: ys, rest, rest', lengths => by
    simp only [List.cons_append, lexCmp]
    rw [lexCmp_append_of_length rest rest' (by simpa using lengths), then_assoc]

/-- A code whose comparison is decided block by block. -/
def Decides {α : Type} (code : α → List Nat) (compareBy : α → α → Ordering) (left right : α) : Prop :=
  ∀ rest rest' : List Nat, lexCmp (code left ++ rest) (code right ++ rest') =
    (compareBy left right).then (lexCmp rest rest')

theorem decides_cons {head head' : Nat} {rest rest' : List Nat} :
    lexCmp (head :: rest) (head' :: rest') = (compare head head').then (lexCmp rest rest') := rfl

/-! ## Names -/

/-- Two names, in the order of their serializations. -/
def strCmp (left right : String) : Ordering := lexCmp (serString left) (serString right)

theorem codes_length (name : String) : (name.toList.map Char.toNat).length = name.length := by
  simp [String.length_toList]

theorem serString_decides (left right : String) : Decides serString strCmp left right := by
  intro rest rest'
  simp only [strCmp, serString, List.cons_append, lexCmp]
  by_cases lengths : left.length = right.length
  · rw [lengths, compare_refl]
    simp only [eq_then]
    exact lexCmp_append_of_length rest rest' (by rw [codes_length, codes_length, lengths])
  · have different : compare left.length right.length ≠ .eq := fun same => lengths (Nat.compare_eq_eq.mp same)
    revert different
    cases compare left.length right.length <;> simp [Ordering.then]

theorem strCmp_eq_iff {left right : String} : strCmp left right = .eq ↔ left = right := by
  constructor
  · intro same
    exact (serString_prefix (rest := []) (rest' := []) (by simpa using lexCmp_eq_iff.mp same)).1
  · rintro rfl
    exact lexCmp_refl _

/-- A table that lists names in the order of their serializations, each once. -/
def NameOrdered (table : List String) : Prop := table.Pairwise fun left right => strCmp left right = .lt

/-- Two names, by their position in the table; names outside the table have no answer. -/
def nameScan : List String → String → String → Ordering
  | [], _, _ => .eq
  | name :: rest, left, right => if name = left then .lt else if name = right then .gt else nameScan rest left right

def nameCmp (table : List String) (left right : String) : Ordering :=
  if left = right then .eq else nameScan table left right

theorem nameScan_eq : ∀ {table : List String}, NameOrdered table → ∀ {left right : String},
    left ∈ table → right ∈ table → left ≠ right → nameScan table left right = strCmp left right
  | [], _, _, _, member, _, _ => absurd member List.not_mem_nil
  | name :: rest, ordered, left, right, leftIn, rightIn, different => by
    have pairs := List.pairwise_cons.mp ordered
    rw [nameScan]
    by_cases first : name = left
    · subst first
      rw [if_pos rfl]
      rcases List.mem_cons.mp rightIn with same | later
      · exact absurd same.symm different
      · exact (pairs.1 right later).symm
    · rw [if_neg first]
      by_cases second : name = right
      · subst second
        rw [if_pos rfl]
        rcases List.mem_cons.mp leftIn with same | later
        · exact absurd same.symm first
        · rw [strCmp, lexCmp_swap, ← strCmp, pairs.1 left later]
          rfl
      · rw [if_neg second]
        exact nameScan_eq pairs.2 ((List.mem_cons.mp leftIn).resolve_left (Ne.symm first))
          ((List.mem_cons.mp rightIn).resolve_left (Ne.symm second)) different

theorem nameCmp_eq {table : List String} (ordered : NameOrdered table) {left right : String}
    (leftIn : left ∈ table) (rightIn : right ∈ table) : nameCmp table left right = strCmp left right := by
  unfold nameCmp
  by_cases same : left = right
  · subst same
    rw [if_pos rfl, strCmp_eq_iff.mpr rfl]
  · rw [if_neg same]
    exact nameScan_eq ordered leftIn rightIn same

theorem nameCmp_decides {table : List String} (ordered : NameOrdered table) {left right : String}
    (leftIn : left ∈ table) (rightIn : right ∈ table) : Decides serString (nameCmp table) left right := by
  intro rest rest'
  rw [nameCmp_eq ordered leftIn rightIn]
  exact serString_decides left right rest rest'

/-- Optional names (binders and collection tails): none first. -/
def optCmp (table : List String) : Option String → Option String → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some left, some right => nameCmp table left right

theorem optCmp_decides {table : List String} (ordered : NameOrdered table) :
    ∀ {left right : Option String}, (∀ name ∈ left.toList, name ∈ table) → (∀ name ∈ right.toList, name ∈ table) →
      Decides serOptString (optCmp table) left right
  | none, none, _, _ => fun _ _ => rfl
  | none, some _, _, _ => fun _ _ => rfl
  | some _, none, _, _ => fun _ _ => rfl
  | some left, some right, leftIn, rightIn => fun rest rest' => by
    simp only [serOptString, List.cons_append, decides_cons, compare_refl, optCmp]
    exact nameCmp_decides ordered (leftIn left (by simp)) (rightIn right (by simp)) rest rest'

/-- Lists of names: the length first, then the names in order. -/
def namesPairwise (table : List String) : List String → List String → Ordering
  | [], [] => .eq
  | left :: lefts, right :: rights => (nameCmp table left right).then (namesPairwise table lefts rights)
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt

def namesCmp (table : List String) (left right : List String) : Ordering :=
  (compare left.length right.length).then (namesPairwise table left right)

theorem namesPairwise_decides {table : List String} (ordered : NameOrdered table) :
    ∀ {left right : List String}, left.length = right.length → (∀ name ∈ left, name ∈ table) →
      (∀ name ∈ right, name ∈ table) → ∀ rest rest' : List Nat,
      lexCmp (left.flatMap serString ++ rest) (right.flatMap serString ++ rest') =
        (namesPairwise table left right).then (lexCmp rest rest')
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, lengths, _, _, _, _ => by simp at lengths
  | _ :: _, [], lengths, _, _, _, _ => by simp at lengths
  | left :: lefts, right :: rights, lengths, leftIn, rightIn, rest, rest' => by
    simp only [List.flatMap_cons, List.append_assoc, namesPairwise]
    rw [nameCmp_decides ordered (leftIn left (by simp)) (rightIn right (by simp)),
      namesPairwise_decides ordered (by simpa using lengths) (fun name member => leftIn name (by simp [member]))
        (fun name member => rightIn name (by simp [member])), then_assoc]

theorem namesCmp_decides {table : List String} (ordered : NameOrdered table) {left right : List String}
    (leftIn : ∀ name ∈ left, name ∈ table) (rightIn : ∀ name ∈ right, name ∈ table) :
    Decides serStringList (namesCmp table) left right := by
  intro rest rest'
  simp only [serStringList, List.cons_append, decides_cons, namesCmp]
  by_cases lengths : left.length = right.length
  · rw [lengths, compare_refl]
    simp only [eq_then]
    exact namesPairwise_decides ordered lengths leftIn rightIn rest rest'
  · have different : compare left.length right.length ≠ .eq := fun same => lengths (Nat.compare_eq_eq.mp same)
    revert different
    cases compare left.length right.length <;> simp [Ordering.then]

/-! ## Patterns -/

mutual
  /-- Every name of a pattern: free names, constructors, binder names and collection tails. -/
  def names : Pattern → List String
    | .bvar _ => []
    | .fvar name => [name]
    | .apply label arguments => label :: namesList arguments
    | .lambda binder body => binder.toList ++ names body
    | .multiLambda _ binders body => binders ++ names body
    | .subst body replacement => names body ++ names replacement
    | .collection _ elements rest => namesList elements ++ rest.toList

  def namesList : List Pattern → List String
    | [] => []
    | pattern :: patterns => names pattern ++ namesList patterns
end

/-- A pattern whose names are all in the table. -/
def Covered (table : List String) (pattern : Pattern) : Prop := ∀ name ∈ names pattern, name ∈ table

theorem mem_namesList {name : String} : ∀ {patterns : List Pattern},
    name ∈ namesList patterns ↔ ∃ pattern ∈ patterns, name ∈ names pattern
  | [] => by simp [namesList]
  | pattern :: patterns => by simp [namesList, mem_namesList]

theorem covered_elements {table : List String} {patterns : List Pattern} :
    (∀ name ∈ namesList patterns, name ∈ table) ↔ ∀ pattern ∈ patterns, Covered table pattern := by
  constructor
  · intro covered pattern member name named
    exact covered name (mem_namesList.mpr ⟨pattern, member, named⟩)
  · intro covered name named
    obtain ⟨pattern, member, inside⟩ := mem_namesList.mp named
    exact covered pattern member name inside

/-- The first number of a pattern's serialization. -/
def tag : Pattern → Nat
  | .bvar _ => 0
  | .fvar _ => 1
  | .apply _ _ => 2
  | .lambda _ _ => 3
  | .multiLambda _ _ _ => 4
  | .subst _ _ => 5
  | .collection _ _ _ => 6

mutual
  /-- Two patterns, field by field. -/
  def cmp (table : List String) : Pattern → Pattern → Ordering
    | .bvar index, .bvar other => compare index other
    | .fvar name, .fvar other => nameCmp table name other
    | .apply label arguments, .apply other others =>
        (nameCmp table label other).then ((compare arguments.length others.length).then (cmpList table arguments others))
    | .lambda binder body, .lambda other otherBody => (optCmp table binder other).then (cmp table body otherBody)
    | .multiLambda arity binders body, .multiLambda otherArity otherBinders otherBody =>
        (compare arity otherArity).then ((namesCmp table binders otherBinders).then (cmp table body otherBody))
    | .subst body replacement, .subst otherBody otherReplacement =>
        (cmp table body otherBody).then (cmp table replacement otherReplacement)
    | .collection kind elements rest, .collection otherKind others otherRest =>
        (compare (collectionTag kind) (collectionTag otherKind)).then ((compare elements.length others.length).then
          ((cmpList table elements others).then (optCmp table rest otherRest)))
    | left, right => compare (tag left) (tag right)

  /-- Two lists of patterns of the same length, in order. -/
  def cmpList (table : List String) : List Pattern → List Pattern → Ordering
    | [], [] => .eq
    | left :: lefts, right :: rights => (cmp table left right).then (cmpList table lefts rights)
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
end

theorem ser_tag (pattern : Pattern) : ∃ rest, ser pattern = tag pattern :: rest := by
  cases pattern <;> simp [ser, tag]

theorem cmp_of_tag {table : List String} {left right : Pattern} (different : tag left ≠ tag right) :
    cmp table left right = compare (tag left) (tag right) := by
  cases left <;> cases right <;> simp_all [cmp, tag]

theorem decides_of_tag {table : List String} {left right : Pattern} (different : tag left ≠ tag right) :
    Decides ser (cmp table) left right := by
  intro rest rest'
  obtain ⟨tail, leftSer⟩ := ser_tag left
  obtain ⟨tail', rightSer⟩ := ser_tag right
  rw [leftSer, rightSer, List.cons_append, List.cons_append, decides_cons, cmp_of_tag different]
  have unequal : compare (tag left) (tag right) ≠ .eq := fun same => different (Nat.compare_eq_eq.mp same)
  revert unequal
  cases compare (tag left) (tag right) <;> simp [Ordering.then]

mutual
  theorem cmp_decides {table : List String} (ordered : NameOrdered table) :
      ∀ (left right : Pattern), Covered table left → Covered table right → Decides ser (cmp table) left right
    | .bvar index, .bvar other, _, _ => fun rest rest' => by
      simp only [ser, List.cons_append, List.nil_append, decides_cons, compare_refl, cmp, eq_then]
    | .fvar name, .fvar other, leftIn, rightIn => fun rest rest' => by
      simp only [ser, List.cons_append, decides_cons, compare_refl, cmp, eq_then]
      exact nameCmp_decides ordered (leftIn name (by simp [names])) (rightIn other (by simp [names])) rest rest'
    | .apply label arguments, .apply other others, leftIn, rightIn => fun rest rest' => by
      simp only [ser, List.cons_append, List.append_assoc, decides_cons, compare_refl, cmp, eq_then]
      rw [nameCmp_decides ordered (leftIn label (by simp [names])) (rightIn other (by simp [names])), then_assoc]
      congr 1
      simp only [decides_cons]
      rw [then_assoc]
      by_cases lengths : arguments.length = others.length
      · rw [lengths, compare_refl]
        simp only [eq_then]
        exact cmpList_decides ordered arguments others lengths
          (covered_elements.mp fun name member => leftIn name (by simp [names, member]))
          (covered_elements.mp fun name member => rightIn name (by simp [names, member])) rest rest'
      · have different : compare arguments.length others.length ≠ .eq :=
          fun same => lengths (Nat.compare_eq_eq.mp same)
        revert different
        cases compare arguments.length others.length <;> simp [Ordering.then]
    | .lambda binder body, .lambda other otherBody, leftIn, rightIn => fun rest rest' => by
      simp only [ser, List.cons_append, List.append_assoc, decides_cons, compare_refl, cmp, eq_then]
      rw [optCmp_decides ordered (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])),
        cmp_decides ordered body otherBody (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])), then_assoc]
    | .multiLambda arity binders body, .multiLambda otherArity otherBinders otherBody, leftIn, rightIn =>
      fun rest rest' => by
      simp only [ser, List.cons_append, List.append_assoc, decides_cons, compare_refl, cmp, eq_then]
      rw [namesCmp_decides ordered (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])),
        cmp_decides ordered body otherBody (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])), then_assoc, then_assoc]
    | .subst body replacement, .subst otherBody otherReplacement, leftIn, rightIn => fun rest rest' => by
      simp only [ser, List.cons_append, List.append_assoc, decides_cons, compare_refl, cmp, eq_then]
      rw [cmp_decides ordered body otherBody (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])),
        cmp_decides ordered replacement otherReplacement (fun name member => leftIn name (by simp [names, member]))
          (fun name member => rightIn name (by simp [names, member])), then_assoc]
    | .collection kind elements tail, .collection otherKind others otherTail, leftIn, rightIn => fun rest rest' => by
      simp only [ser, List.cons_append, List.append_assoc, decides_cons, compare_refl, cmp, eq_then]
      rw [then_assoc]
      congr 1
      rw [then_assoc]
      by_cases lengths : elements.length = others.length
      · rw [lengths, compare_refl]
        simp only [eq_then]
        rw [cmpList_decides ordered elements others lengths
            (covered_elements.mp fun name member => leftIn name (by simp [names, member]))
            (covered_elements.mp fun name member => rightIn name (by simp [names, member])),
          optCmp_decides ordered (fun name member => leftIn name (by simp [names, member]))
            (fun name member => rightIn name (by simp [names, member])), then_assoc]
      · have different : compare elements.length others.length ≠ .eq :=
          fun same => lengths (Nat.compare_eq_eq.mp same)
        revert different
        cases compare elements.length others.length <;> simp [Ordering.then]
    | .bvar _, .fvar _, _, _ | .bvar _, .apply _ _, _, _ | .bvar _, .lambda _ _, _, _
    | .bvar _, .multiLambda _ _ _, _, _ | .bvar _, .subst _ _, _, _ | .bvar _, .collection _ _ _, _, _
    | .fvar _, .bvar _, _, _ | .fvar _, .apply _ _, _, _ | .fvar _, .lambda _ _, _, _
    | .fvar _, .multiLambda _ _ _, _, _ | .fvar _, .subst _ _, _, _ | .fvar _, .collection _ _ _, _, _
    | .apply _ _, .bvar _, _, _ | .apply _ _, .fvar _, _, _ | .apply _ _, .lambda _ _, _, _
    | .apply _ _, .multiLambda _ _ _, _, _ | .apply _ _, .subst _ _, _, _ | .apply _ _, .collection _ _ _, _, _
    | .lambda _ _, .bvar _, _, _ | .lambda _ _, .fvar _, _, _ | .lambda _ _, .apply _ _, _, _
    | .lambda _ _, .multiLambda _ _ _, _, _ | .lambda _ _, .subst _ _, _, _ | .lambda _ _, .collection _ _ _, _, _
    | .multiLambda _ _ _, .bvar _, _, _ | .multiLambda _ _ _, .fvar _, _, _ | .multiLambda _ _ _, .apply _ _, _, _
    | .multiLambda _ _ _, .lambda _ _, _, _ | .multiLambda _ _ _, .subst _ _, _, _
    | .multiLambda _ _ _, .collection _ _ _, _, _
    | .subst _ _, .bvar _, _, _ | .subst _ _, .fvar _, _, _ | .subst _ _, .apply _ _, _, _
    | .subst _ _, .lambda _ _, _, _ | .subst _ _, .multiLambda _ _ _, _, _ | .subst _ _, .collection _ _ _, _, _
    | .collection _ _ _, .bvar _, _, _ | .collection _ _ _, .fvar _, _, _ | .collection _ _ _, .apply _ _, _, _
    | .collection _ _ _, .lambda _ _, _, _ | .collection _ _ _, .multiLambda _ _ _, _, _
    | .collection _ _ _, .subst _ _, _, _ => decides_of_tag (by simp [tag])

  theorem cmpList_decides {table : List String} (ordered : NameOrdered table) :
      ∀ (left right : List Pattern), left.length = right.length → (∀ pattern ∈ left, Covered table pattern) →
        (∀ pattern ∈ right, Covered table pattern) → ∀ rest rest' : List Nat,
        lexCmp (serList left ++ rest) (serList right ++ rest') = (cmpList table left right).then (lexCmp rest rest')
    | [], [], _, _, _, _, _ => rfl
    | [], _ :: _, lengths, _, _, _, _ => by simp at lengths
    | _ :: _, [], lengths, _, _, _, _ => by simp at lengths
    | left :: lefts, right :: rights, lengths, leftIn, rightIn, rest, rest' => by
      simp only [serList, List.append_assoc, cmpList]
      rw [cmp_decides ordered left right (leftIn left (by simp)) (rightIn right (by simp)),
        cmpList_decides ordered lefts rights (by simpa using lengths) (fun pattern member => leftIn pattern (by simp [member]))
          (fun pattern member => rightIn pattern (by simp [member])), then_assoc]
end

/-- **`cmp` is the lexicographic comparison of serializations** on covered patterns. -/
theorem cmp_eq_lexCmp {table : List String} (ordered : NameOrdered table) {left right : Pattern}
    (leftIn : Covered table left) (rightIn : Covered table right) :
    cmp table left right = lexCmp (ser left) (ser right) := by
  have decided := cmp_decides ordered left right leftIn rightIn [] []
  simp only [List.append_nil] at decided
  rw [decided]
  cases cmp table left right <;> rfl

theorem patternLe_iff {table : List String} (ordered : NameOrdered table) {left right : Pattern}
    (leftIn : Covered table left) (rightIn : Covered table right) :
    PatternLe left right ↔ cmp table left right ≠ .gt := by
  rw [PatternLe, lexLe_eq, cmp_eq_lexCmp ordered leftIn rightIn]
  cases lexCmp (ser left) (ser right) <;> simp

/-! ## Sorting and canonical forms -/

theorem orderedInsert_congr {α : Type} {first second : α → α → Prop} [DecidableRel first] [DecidableRel second]
    (pattern : α) : ∀ (sorted : List α), (∀ other ∈ sorted, first pattern other ↔ second pattern other) →
      sorted.orderedInsert first pattern = sorted.orderedInsert second pattern
  | [], _ => rfl
  | other :: rest, agree => by
    simp only [List.orderedInsert]
    by_cases holds : first pattern other
    · rw [if_pos holds, if_pos ((agree other (by simp)).mp holds)]
    · rw [if_neg holds, if_neg (fun held => holds ((agree other (by simp)).mpr held)),
        orderedInsert_congr pattern rest (fun other' member => agree other' (by simp [member]))]

theorem insertionSort_congr {α : Type} {first second : α → α → Prop} [DecidableRel first] [DecidableRel second] :
    ∀ (items : List α), (∀ left ∈ items, ∀ right ∈ items, first left right ↔ second left right) →
      items.insertionSort first = items.insertionSort second
  | [], _ => rfl
  | item :: rest, agree => by
    rw [List.insertionSort_cons, List.insertionSort_cons, insertionSort_congr rest (fun left leftIn right rightIn => agree left (by simp [leftIn]) right (by simp [rightIn]))]
    exact orderedInsert_congr item _ fun other member =>
      agree item (by simp) other (by simp [(List.perm_insertionSort second rest).mem_iff.mp member])

/-- The order a runtime sorts by: `cmp` is not `.gt`. -/
def CmpLe (table : List String) (left right : Pattern) : Prop := cmp table left right ≠ .gt

instance (table : List String) : DecidableRel (CmpLe table) := fun left right =>
  inferInstanceAs (Decidable (cmp table left right ≠ .gt))

/-- Insertion sort by `cmp`. -/
def sortBy (table : List String) (patterns : List Pattern) : List Pattern := patterns.insertionSort (CmpLe table)

theorem sortBy_eq_sortLex {table : List String} (ordered : NameOrdered table) {patterns : List Pattern}
    (covered : ∀ pattern ∈ patterns, Covered table pattern) : sortBy table patterns = sortLex patterns :=
  insertionSort_congr patterns fun left leftIn right rightIn =>
    (patternLe_iff ordered (covered left leftIn) (covered right rightIn)).symm

/-- `arrange`, sorted by `cmp`: a set's elements lose their repetitions after the sort. -/
def arrangeBy (table : List String) (kind : CollType) (elements : List Pattern) : List Pattern :=
  match kind with
  | .vec => elements
  | .hashBag => sortBy table elements
  | .hashSet => (sortBy table elements).dedup

/-- The canonical form, sorted by `cmp`. -/
def canonBy (table : List String) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map (canonBy table))
  | .lambda binder body => .lambda binder (canonBy table body)
  | .multiLambda arity binders body => .multiLambda arity binders (canonBy table body)
  | .subst body replacement => .subst (canonBy table body) (canonBy table replacement)
  | .collection kind elements rest => .collection kind (arrangeBy table kind (elements.map (canonBy table))) rest
decreasing_by all_goals sizeOf_pattern_dec

theorem namesList_perm {left right : List Pattern} (permutation : left.Perm right) (name : String) :
    name ∈ namesList left ↔ name ∈ namesList right := by
  simp only [mem_namesList]
  exact ⟨fun ⟨pattern, member, inside⟩ => ⟨pattern, permutation.mem_iff.mp member, inside⟩,
    fun ⟨pattern, member, inside⟩ => ⟨pattern, permutation.mem_iff.mpr member, inside⟩⟩

/-- **The canonical form sorted by `cmp` is `canon`** on covered patterns, and it stays covered. -/
theorem canonBy_eq_canon {table : List String} (ordered : NameOrdered table) :
    ∀ pattern : Pattern, Covered table pattern → canonBy table pattern = canon pattern ∧ Covered table (canon pattern)
  | .bvar index, _ => by
    refine ⟨by rw [canonBy, canon], ?_⟩
    rw [canon]
    intro name member
    simp [names] at member
  | .fvar name, covered => by
    refine ⟨by rw [canonBy, canon], ?_⟩
    rw [canon]
    exact covered
  | .apply label arguments, covered => by
    have each : ∀ argument ∈ arguments, canonBy table argument = canon argument ∧ Covered table (canon argument) :=
      fun argument member => canonBy_eq_canon ordered argument
        (covered_elements.mp (fun name inside => covered name (by simp [names, inside])) argument member)
    refine ⟨?_, ?_⟩
    · rw [canonBy, canon_apply, List.map_congr_left (fun argument member => (each argument member).1)]
    · rw [canon_apply]
      intro name member
      simp only [names, List.mem_cons] at member
      rcases member with rfl | inside
      · exact covered name (by simp [names])
      · obtain ⟨changed, changedIn, named⟩ := mem_namesList.mp inside
        obtain ⟨argument, argumentIn, rfl⟩ := List.mem_map.mp changedIn
        exact (each argument argumentIn).2 name named
  | .lambda binder body, covered => by
    have inner := canonBy_eq_canon ordered body (fun name inside => covered name (by simp [names, inside]))
    refine ⟨by rw [canonBy, canon, inner.1], ?_⟩
    rw [canon]
    intro name member
    simp only [names, List.mem_append] at member
    rcases member with binderIn | inside
    · exact covered name (by simp [names, binderIn])
    · exact inner.2 name inside
  | .multiLambda arity binders body, covered => by
    have inner := canonBy_eq_canon ordered body (fun name inside => covered name (by simp [names, inside]))
    refine ⟨by rw [canonBy, canon, inner.1], ?_⟩
    rw [canon]
    intro name member
    simp only [names, List.mem_append] at member
    rcases member with binderIn | inside
    · exact covered name (by simp [names, binderIn])
    · exact inner.2 name inside
  | .subst body replacement, covered => by
    have first := canonBy_eq_canon ordered body (fun name inside => covered name (by simp [names, inside]))
    have second := canonBy_eq_canon ordered replacement (fun name inside => covered name (by simp [names, inside]))
    refine ⟨by rw [canonBy, canon, first.1, second.1], ?_⟩
    rw [canon]
    intro name member
    simp only [names, List.mem_append] at member
    rcases member with inside | inside
    · exact first.2 name inside
    · exact second.2 name inside
  | .collection kind elements rest, covered => by
    have each : ∀ element ∈ elements, canonBy table element = canon element ∧ Covered table (canon element) :=
      fun element member => canonBy_eq_canon ordered element
        (covered_elements.mp (fun name inside => covered name (by simp [names, inside])) element member)
    have mapped : elements.map (canonBy table) = elements.map canon :=
      List.map_congr_left fun element member => (each element member).1
    have canonCovered : ∀ element ∈ elements.map canon, Covered table element := by
      intro changed member
      obtain ⟨element, elementIn, rfl⟩ := List.mem_map.mp member
      exact (each element elementIn).2
    have arranged : arrangeBy table kind (elements.map canon) = arrange kind (elements.map canon) := by
      cases kind with
      | vec => rfl
      | hashBag => exact sortBy_eq_sortLex ordered canonCovered
      | hashSet => simp only [arrangeBy, arrange_set, sortBy_eq_sortLex ordered canonCovered]
    refine ⟨by rw [canonBy, canon_collection, mapped, arranged], ?_⟩
    rw [canon_collection]
    intro name member
    simp only [names, List.mem_append] at member
    rcases member with inside | restIn
    · obtain ⟨changed, changedIn, named⟩ := mem_namesList.mp inside
      exact canonCovered changed ((arrange_mem changed).mp changedIn) name named
    · exact covered name (by simp [names, restIn])
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare
