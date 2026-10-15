import Mettapedia.Logic.HostingStyles.NameEquality.Renaming
import Mettapedia.Logic.HostingStyles.StoredPrograms.Comparison
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running

/-!
# Numbers: a numeral written as one constant computes nothing

A number may be written as one constant, its decimal writing
(`numeralConstant`).  Then a numeral is a name like any other, and a theory
sees of it what it sees of a name.

**A theory that is closed under the injective renamings fixing a list of
names computes, on numerals written as constants, only functions each of whose
values is the argument or a numeral of the list**
(`computed_value_argument_or_listed`): if the theory computes `f`, then
`f n = n` or the numeral of `f n` is in the list, for every `n`.  The reason
is a swap: two numerals outside the list, neither the argument, are exchanged
by a renaming that the theory does not see, so a result outside the list
could be any of them.

* So **no finite table computes the successor** (`no_table_computes_successor`):
  the theory of a finite table is closed under every renaming that fixes the
  names of its rules.
* **The test of names does not help** (`withNames_no_successor`): the theory
  of a table with the family of the equality of names is closed under the
  injective renamings, and the swap is one.

So a number is data built by constructors, where a table computes with rules,
or each operation on numerals is a clause of the evaluator.

## Numbers as data: binary numerals

A number is written in binary digits, least first and without a last nought
(`digits`, `digitsTerm`).

* **Three rules compute the successor** (`binarySuccessorRules`): the helper
  on the writing of a number reduces to the writing of the next number
  (`binarySuccessor_number`; on any digits `binarySuccessor_reduces`, and the
  next digits of a writing are the writing of the next number,
  `nextDigits_digits`).
* **The nine rules that compare two letters compare two numbers**
  (`binaryComparison_reduces`): the comparison of the writings of two numbers
  reduces to the truth value of their equality.

Twelve rules, which pass the test for stored tables (`binaryRules_stored`).
In unary the successor is a constructor and needs no rule.

Positive: the three rules take the successor of three, `one one end`, to four,
`nought nought one end`, in three steps (`binarySuccessor_example`).
Negative: the successor of the constant `3` has no step by the three rules
(`binarySuccessor_constant_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory rootStep_program_inv)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## A numeral as one constant -/

/-- **A numeral written as one constant**: the decimal writing of the number. -/
def numeralConstant (value : Nat) : LF.Term := .con value.repr

/-- Two numbers have one numeral only when they are one number. -/
theorem numeralConstant_injective : Function.Injective numeralConstant :=
  fun _ _ same => Nat.repr_injective (LF.Term.con.inj same)

/-- **Positive**: the numeral of twelve is the constant `12`.  **Negative**:
it is not the numeral of thirteen. -/
theorem numeralConstant_examples :
    numeralConstant 12 = .con "12" ∧ numeralConstant 12 ≠ numeralConstant 13 := by
  refine ⟨by decide +kernel, fun same => ?_⟩
  exact absurd (numeralConstant_injective same) (by decide)

/-- Outside every list of names and every list of numbers there is a
numeral. -/
theorem exists_numeral_outside (fixed : List String) (avoid : List Nat) :
    ∃ value : Nat, value.repr ∉ fixed ∧ value ∉ avoid := by
  obtain ⟨value, fresh⟩ := Infinite.exists_notMem_finset
    ((fixed.filterMap String.toNat?).toFinset ∪ avoid.toFinset)
  refine ⟨value, fun member => fresh ?_, fun member => fresh ?_⟩
  · exact Finset.mem_union_left _ (List.mem_toFinset.mpr
      (List.mem_filterMap.mpr ⟨value.repr, member, Nat.toNat?_repr value⟩))
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr member)

/-- Above some number no numeral is in a list of names. -/
theorem exists_bound_of_numerals (fixed : List String) :
    ∃ bound : Nat, ∀ value : Nat, bound < value → value.repr ∉ fixed := by
  refine ⟨(fixed.filterMap String.toNat?).toFinset.sup id, fun value above member => ?_⟩
  have listed : value ∈ (fixed.filterMap String.toNat?).toFinset :=
    List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨value.repr, member, Nat.toNat?_repr value⟩)
  have below : value ≤ (fixed.filterMap String.toNat?).toFinset.sup id :=
    Finset.le_sup (f := id) listed
  omega

/-! ## What a theory computes on numerals written as constants -/

/-- **A theory closed under the injective renamings that fix a list computes,
on numerals written as constants, only functions each of whose values is the
argument or a numeral of the list.**  The term asked of an argument is natural
in the names of the argument. -/
theorem computed_value_argument_or_listed {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, Function.Injective naming →
      (∀ name ∈ fixed, naming name = name) → ClosedUnder theory naming)
    {probe : LF.Term → LF.Term}
    (natural : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ∀ term, renameConstants naming (probe term) = probe (renameConstants naming term))
    {compute : Nat → Nat}
    (computes : ∀ value result : Nat,
      Reduces theory (probe (numeralConstant value)) (numeralConstant result) ↔
        result = compute value)
    (value : Nat) : compute value = value ∨ (compute value).repr ∈ fixed := by
  by_contra neither
  have moved : compute value ≠ value := fun same => neither (.inl same)
  have resultOutside : (compute value).repr ∉ fixed := fun member => neither (.inr member)
  obtain ⟨other, otherOutside, otherNew⟩ := exists_numeral_outside fixed [value, compute value]
  have otherNotValue : other ≠ value := fun same => otherNew (by simp [same])
  have otherNotResult : other ≠ compute value := fun same => otherNew (by simp [same])
  have fixes : ∀ name ∈ fixed, Equiv.swap (compute value).repr other.repr name = name :=
    fun name member => Equiv.swap_apply_of_ne_of_ne
      (fun same => resultOutside (same ▸ member)) (fun same => otherOutside (same ▸ member))
  have keeps : Equiv.swap (compute value).repr other.repr value.repr = value.repr :=
    Equiv.swap_apply_of_ne_of_ne (fun same => moved (Nat.repr_injective same).symm)
      (fun same => otherNotValue (Nat.repr_injective same).symm)
  have renamed := reduces_renamed
    (closed _ (Equiv.swap (compute value).repr other.repr).injective fixes)
    ((computes value (compute value)).mpr rfl)
  rw [natural _ fixes] at renamed
  have source : renameConstants (Equiv.swap (compute value).repr other.repr)
      (numeralConstant value) = numeralConstant value := by
    simp only [numeralConstant, renameConstants, keeps]
  have target : renameConstants (Equiv.swap (compute value).repr other.repr)
      (numeralConstant (compute value)) = numeralConstant other := by
    simp only [numeralConstant, renameConstants, Equiv.swap_apply_left]
  rw [source, target] at renamed
  exact otherNotResult ((computes value other).mp renamed)

/-- **Such a theory does not compute the successor** on numerals written as
constants. -/
theorem no_successor_of_closedUnder {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, Function.Injective naming →
      (∀ name ∈ fixed, naming name = name) → ClosedUnder theory naming)
    {probe : LF.Term → LF.Term}
    (natural : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ∀ term, renameConstants naming (probe term) = probe (renameConstants naming term)) :
    ¬ ∀ value result : Nat,
      Reduces theory (probe (numeralConstant value)) (numeralConstant result) ↔
        result = value + 1 := by
  intro computes
  obtain ⟨bound, above⟩ := exists_bound_of_numerals fixed
  rcases computed_value_argument_or_listed closed natural (compute := fun value => value + 1)
    computes bound with same | member
  · exact absurd same (Nat.succ_ne_self _)
  · exact above (bound + 1) (Nat.lt_succ_self bound) member

/-- The call of the head `succ` on one term, as a question about that term. -/
def successorCall (term : LF.Term) : LF.Term := callTerm "succ" [term]

/-- A renaming that fixes the four constants of the call carries the call on
a term to the call on the renamed term. -/
theorem renameConstants_successorCall {naming : String → String}
    (fixes : ∀ name ∈ ["call", "succ", "cons", "nil"], naming name = name) (term : LF.Term) :
    renameConstants naming (successorCall term) = successorCall (renameConstants naming term) := by
  simp [successorCall, callTerm, cells, renameConstants, fixes "call" (by decide),
    fixes "succ" (by decide), fixes "cons" (by decide), fixes "nil" (by decide)]

/-- **No finite table computes the successor of a numeral written as one
constant.** -/
theorem no_table_computes_successor (table : List RewriteRule) :
    ¬ ∀ value result : Nat,
      Reduces (programTheory table) (successorCall (numeralConstant value))
          (numeralConstant result) ↔
        result = value + 1 :=
  no_successor_of_closedUnder (fixed := constantsOfRules table ++ ["call", "succ", "cons", "nil"])
    (fun _ _ fixes => programTheory_closedUnder fun name member =>
      fixes name (List.mem_append_left _ member))
    (fun _ fixes term => renameConstants_successorCall
      (fun name member => fixes name (List.mem_append_right _ member)) term)

/-- **The test of names does not help**: no finite table with the family of
the equality of names computes the successor of a numeral written as one
constant. -/
theorem withNames_no_successor (table : List RewriteRule) :
    ¬ ∀ value result : Nat,
      Reduces (withNames table) (successorCall (numeralConstant value))
          (numeralConstant result) ↔
        result = value + 1 :=
  no_successor_of_closedUnder (fixed := fixedNames table ++ ["call", "succ", "cons", "nil"])
    (fun _ injective fixes => withNames_closedUnder injective fun name member =>
      fixes name (List.mem_append_left _ member))
    (fun _ fixes term => renameConstants_successorCall
      (fun name member => fixes name (List.mem_append_right _ member)) term)

/-! ## Binary numerals: the successor in three rules -/

/-- **The digits of the next number**, least digit first. -/
def nextDigits : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: nextDigits rest

/-- They write the next number. -/
theorem undigits_nextDigits : ∀ digits : List Bool,
    undigits (nextDigits digits) = undigits digits + 1
  | [] => rfl
  | false :: rest => by simp [nextDigits, undigits]; omega
  | true :: rest => by
      simp only [nextDigits, undigits, undigits_nextDigits rest]
      simp
      omega

/-- The call of the helper of the successor on a numeral. -/
abbrev nextTerm (number : LF.Term) : LF.Term := libTerm "bin-succ" [number]

namespace BinarySuccessor

/-- After the last digit: the next number of nought is one. -/
def atEnd : RewriteRule := ⟨nextTerm (.con "end"), .app (.con "one") (.con "end")⟩

/-- At a digit nought: it becomes one, and the rest stays. -/
def atNought : RewriteRule :=
  ⟨nextTerm (.app (.con "nought") (.var 0)), .app (.con "one") (.var 0)⟩

/-- At a digit one: it becomes nought, and the carry goes to the rest. -/
def atOne : RewriteRule :=
  ⟨nextTerm (.app (.con "one") (.var 0)), .app (.con "nought") (nextTerm (.var 0))⟩

end BinarySuccessor

/-- **The rules of the successor of a binary numeral**: three rules. -/
def binarySuccessorRules : List RewriteRule :=
  [BinarySuccessor.atEnd, BinarySuccessor.atNought, BinarySuccessor.atOne]

/-- **The three rules compute the successor**: the helper on the digits of a
number reduces to the digits of the next. -/
theorem binarySuccessor_reduces {theory : Theory} (holds : Holds theory binarySuccessorRules) :
    ∀ digits : List Bool,
      Reduces theory (nextTerm (digitsTerm digits)) (digitsTerm (nextDigits digits))
  | [] =>
      fires (rule := BinarySuccessor.atEnd) (holds _ (by simp [binarySuccessorRules])) []
        (by side [BinarySuccessor.atEnd]) (by side [BinarySuccessor.atEnd])
  | false :: rest =>
      fires (rule := BinarySuccessor.atNought) (holds _ (by simp [binarySuccessorRules]))
        [digitsTerm rest] (by side [BinarySuccessor.atNought])
        (by side [BinarySuccessor.atNought])
  | true :: rest => by
      have step : Reduces theory (nextTerm (digitsTerm (true :: rest)))
          (.app (.con "nought") (nextTerm (digitsTerm rest))) :=
        fires (rule := BinarySuccessor.atOne) (holds _ (by simp [binarySuccessorRules]))
          [digitsTerm rest] (by side [BinarySuccessor.atOne]) (by side [BinarySuccessor.atOne])
      exact step.trans (Dedukti.Reduces.app .refl (binarySuccessor_reduces holds rest))

/-- A writing of a number that fits in fewer digits is the same writing. -/
theorem digits_widen : ∀ (width value : Nat), value < 2 ^ width →
    digits (width + 1) value = digits width value
  | 0, value, small => by
      have isZero : value = 0 := by simpa using small
      simp [digits, isZero]
  | width + 1, value, small => by
      by_cases isZero : value = 0
      · simp [digits, isZero]
      · have half : value / 2 < 2 ^ width := by
          rw [Nat.pow_succ] at small
          omega
        show (if value = 0 then [] else decide (value % 2 = 1) :: digits (width + 1) (value / 2)) =
          (if value = 0 then [] else decide (value % 2 = 1) :: digits width (value / 2))
        rw [if_neg isZero, if_neg isZero, digits_widen width (value / 2) half]

/-- **The next digits of the writing of a number are the writing of the next
number.** -/
theorem nextDigits_digits : ∀ (width value : Nat), value < 2 ^ width →
    nextDigits (digits width value) = digits (width + 1) (value + 1)
  | 0, value, small => by
      have isZero : value = 0 := by simpa using small
      subst isZero
      decide
  | width + 1, value, small => by
      by_cases isZero : value = 0
      · subst isZero
        simp [digits, nextDigits]
      · have half : value / 2 < 2 ^ width := by
          rw [Nat.pow_succ] at small
          omega
        have unfolded : digits (width + 1) value =
            decide (value % 2 = 1) :: digits width (value / 2) := by
          show (if value = 0 then [] else _) = _
          rw [if_neg isZero]
        have next : digits (width + 2) (value + 1) =
            decide ((value + 1) % 2 = 1) :: digits (width + 1) ((value + 1) / 2) := by
          show (if value + 1 = 0 then [] else _) = _
          rw [if_neg (Nat.succ_ne_zero value)]
        rw [unfolded, next]
        rcases Nat.mod_two_eq_zero_or_one value with even | odd
        · have head : decide (value % 2 = 1) = false := by simp [even]
          have nextHead : decide ((value + 1) % 2 = 1) = true := by
            simp only [decide_eq_true_eq]
            omega
          have sameHalf : (value + 1) / 2 = value / 2 := by omega
          rw [head, nextHead, sameHalf, nextDigits, digits_widen width (value / 2) half]
        · have head : decide (value % 2 = 1) = true := by simp [odd]
          have nextHead : decide ((value + 1) % 2 = 1) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          have nextHalf : (value + 1) / 2 = value / 2 + 1 := by omega
          rw [head, nextHead, nextHalf, nextDigits, nextDigits_digits width (value / 2) half]

/-- **The three rules compute the successor of a number in binary**: the
helper on the writing of a number below `2 ^ width` reduces to the writing of
the next number. -/
theorem binarySuccessor_number {theory : Theory} (holds : Holds theory binarySuccessorRules)
    {width value : Nat} (small : value < 2 ^ width) :
    Reduces theory (nextTerm (digitsTerm (digits width value)))
      (digitsTerm (digits (width + 1) (value + 1))) := by
  rw [← nextDigits_digits width value small]
  exact binarySuccessor_reduces holds _

/-- **The nine rules that compare two letters compare two numbers in binary**:
the comparison of the writings of two numbers below `2 ^ width` reduces to the
truth value of their equality. -/
theorem binaryComparison_reduces {theory : Theory} (holds : Holds theory sameLetterRules)
    {width first second : Nat} (firstSmall : first < 2 ^ width)
    (secondSmall : second < 2 ^ width) :
    Reduces theory (sameLetter (digitsTerm (digits width first)) (digitsTerm (digits width second)))
      (truth letterSpelling (decide (first = second))) := by
  have compared := sameLetter_reduces holds (digits width first) (digits width second)
  have same : decide (digits width first = digits width second) = decide (first = second) := by
    refine decide_eq_decide.mpr ⟨fun equal => ?_, fun equal => by rw [equal]⟩
    have read := congrArg undigits equal
    rwa [undigits_digits width first firstSmall, undigits_digits width second secondSmall] at read
  rwa [same] at compared

/-- **The successor and the comparison of binary numerals are a stored
table**: the three rules of the successor and the nine that compare two
numerals digit by digit, twelve rules. -/
theorem binaryRules_stored :
    StoredTable (binarySuccessorRules ++ sameLetterRules) ∧
      (binarySuccessorRules ++ sameLetterRules).length = 12 :=
  ⟨storedTable_of_check (by decide +kernel), by decide⟩

/-- **Positive**: the three rules take the successor of three, written
`one one end`, to four, written `nought nought one end`, in three steps and
not in two. -/
theorem binarySuccessor_example :
    run binarySuccessorRules 3 (nextTerm (digitsTerm [true, true])) =
        digitsTerm [false, false, true] ∧
      run binarySuccessorRules 2 (nextTerm (digitsTerm [true, true])) ≠
        digitsTerm [false, false, true] ∧
      undigits [true, true] = 3 ∧ undigits [false, false, true] = 4 := by
  decide +kernel

/-- **Negative**: the three rules do not rewrite the successor of a numeral
written as one constant: the helper on the constant `3` has no step. -/
theorem binarySuccessor_constant_stuck :
    IsNormal (Step (programTheory binarySuccessorRules)) (nextTerm (numeralConstant 3)) := by
  have rooted : ∀ rule, (programTheory binarySuccessorRules).rule rule →
      rewritesCall rule = true := by
    intro rule member
    have listed : ∀ candidate ∈ binarySuccessorRules, rewritesCall candidate = true := by decide
    exact listed rule member
  intro target step
  have applied : Step (programTheory binarySuccessorRules)
      (.app (.app (.con "lib") (.con "bin-succ")) (cells [numeralConstant 3])) target := step
  rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
  · rcases rootStep_program_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, -⟩
    · simp at shape
    · simp only [binarySuccessorRules, List.mem_cons, List.not_mem_nil, or_false] at member
      have numeral : numeralConstant 3 = .con "3" := by decide +kernel
      rw [numeral] at shape
      rcases member with rfl | rfl | rfl <;>
        simp [BinarySuccessor.atEnd, BinarySuccessor.atNought, BinarySuccessor.atOne, libTerm,
          cells] at shape
  · exact passive_normal (fun _ => rfl) rooted _ rfl _ inner
  · exact passive_normal (fun _ => rfl) rooted _
      (passive_cells (by simp [numeralConstant, passive])) _ inner

#print axioms computed_value_argument_or_listed
#print axioms no_successor_of_closedUnder
#print axioms no_table_computes_successor
#print axioms withNames_no_successor
#print axioms undigits_nextDigits
#print axioms binarySuccessor_reduces
#print axioms nextDigits_digits
#print axioms binarySuccessor_number
#print axioms binaryComparison_reduces
#print axioms binaryRules_stored
#print axioms binarySuccessor_constant_stuck

end Mettapedia.Logic.HostingStyles.NameEquality
