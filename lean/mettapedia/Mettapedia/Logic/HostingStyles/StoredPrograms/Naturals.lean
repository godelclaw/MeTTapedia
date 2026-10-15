import Mettapedia.Logic.HostingStyles.StoredPrograms.Firing

/-!
# The arithmetic that the kernel uses, as rules on numbers in unary

The shared host computes on the numbers that literals spell.  A table
computes on the reading of such a literal: the number in unary with the mark
of its spelling (`numbered`).  The rules read the number and never the mark,
and a result is marked as canonically written, as the host writes it.

The primitives that the programs of MM0's kernel call (`Inventory.lean`):

| primitive | rules | what they compute |
|---|---|---|
| `nik:nat-zero` | `zeroTestRules` | whether the number is zero |
| `nik:nat-pred` | `predecessorRules` | the predecessor, zero for zero |
| `nik:nat-eq` | `equalityTestRules`, `equalNumbersRules` | whether two numbers are equal |
| `nik:nat-add` | `sumRules` | the sum |
| `nik:nat-lt` | `lessRules` | whether the first is less than the second |

Each agrees with the host on all data: if the host returns a value for the
call of the primitive on data, the call on the readings of the data reduces
to the reading of that value (`naturals_realized`).  A literal that spells a
number in another way than the host writes it is read as that number too, so
no condition on the data is needed.

The sixteen rules are orthogonal (`naturalRules_orthogonal`).  Negative: on
a datum that is no number the call has no step (`sum_stuck`), where the host
faults.

Not given: `nik:nat-monus`, `nik:nat-max`, `nik:nat-le`, and the product and
division of the larger host; no program of the kernel calls them.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Host natural natural? boolean computationalHost NaturalBinary PrimitiveResult)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst orthogonalCheck)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-- A datum that the host reads as a number is read as that number, with a
mark. -/
theorem datum_of_natural {N : Spelling} {term : EngineTerm} {value : Nat}
    (isNumber : natural? term = some value) : ∃ mark, datum N term = numbered (unary value) mark := by
  cases term with
  | lit spelling =>
      have spelled : spelledNumber spelling = some value :=
        (spelledNumber_eq_toNat? spelling).trans isNumber
      simp only [datum, literal, spelled]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | sym _ => cases isNumber
  | var _ => cases isNumber
  | expr _ => cases isNumber
  | list _ => cases isNumber

/-! ## The zero test -/

namespace ZeroTest

def zero (N : Spelling) : RewriteRule :=
  ⟨callTerm "nik:nat-zero" [numbered (.con "zero") (.var 0)], truth N true⟩

def successor (N : Spelling) : RewriteRule :=
  ⟨callTerm "nik:nat-zero" [numbered (.app (.con "succ") (.var 0)) (.var 1)], truth N false⟩

end ZeroTest

/-- **The rules of `nik:nat-zero`.** -/
def zeroTestRules (N : Spelling) : List RewriteRule := [ZeroTest.zero N, ZeroTest.successor N]

/-- The zero test of a number, whatever its mark. -/
theorem zeroTest_reduces (N : Spelling) {theory : Theory} (holds : Holds theory (zeroTestRules N))
    (value : Nat) (mark : LF.Term) :
    Reduces theory (callTerm "nik:nat-zero" [numbered (unary value) mark])
      (truth N (decide (value = 0))) := by
  cases value with
  | zero =>
      exact fires (rule := ZeroTest.zero N) (holds _ (by simp [zeroTestRules])) [mark]
        (by simp only [ZeroTest.zero]; instances; rfl) (by simp only [ZeroTest.zero]; instances; rfl)
  | succ value =>
      exact fires (rule := ZeroTest.successor N) (holds _ (by simp [zeroTestRules]))
        [unary value, mark] (by simp only [ZeroTest.successor]; instances; rfl)
        (by simp only [ZeroTest.successor]; instances; rfl)

/-! ## The predecessor -/

namespace Predecessor

def zero : RewriteRule :=
  ⟨callTerm "nik:nat-pred" [numbered (.con "zero") (.var 0)], numeral 0⟩

def successor : RewriteRule :=
  ⟨callTerm "nik:nat-pred" [numbered (.app (.con "succ") (.var 0)) (.var 1)],
    numbered (.var 0) (.con "canon")⟩

end Predecessor

/-- **The rules of `nik:nat-pred`.** -/
def predecessorRules : List RewriteRule := [Predecessor.zero, Predecessor.successor]

/-- The predecessor of a number, whatever its mark, canonically written. -/
theorem predecessor_reduces {theory : Theory} (holds : Holds theory predecessorRules)
    (value : Nat) (mark : LF.Term) :
    Reduces theory (callTerm "nik:nat-pred" [numbered (unary value) mark]) (numeral value.pred) := by
  cases value with
  | zero =>
      exact fires (rule := Predecessor.zero) (holds _ (by simp [predecessorRules])) [mark]
        (by simp only [Predecessor.zero]; instances; rfl)
        (by simp only [Predecessor.zero]; instances; rfl)
  | succ value =>
      exact fires (rule := Predecessor.successor) (holds _ (by simp [predecessorRules]))
        [unary value, mark] (by simp only [Predecessor.successor]; instances; rfl)
        (by simp only [Predecessor.successor]; instances; rfl)

/-! ## Equality of numbers -/

namespace EqualNumbers

def zeroZero (N : Spelling) : RewriteRule :=
  ⟨libTerm "nat-eq" [.con "zero", .con "zero"], truth N true⟩

def zeroSuccessor (N : Spelling) : RewriteRule :=
  ⟨libTerm "nat-eq" [.con "zero", .app (.con "succ") (.var 0)], truth N false⟩

def successorZero (N : Spelling) : RewriteRule :=
  ⟨libTerm "nat-eq" [.app (.con "succ") (.var 0), .con "zero"], truth N false⟩

def successors : RewriteRule :=
  ⟨libTerm "nat-eq" [.app (.con "succ") (.var 0), .app (.con "succ") (.var 1)],
    libTerm "nat-eq" [.var 0, .var 1]⟩

def test : RewriteRule :=
  ⟨callTerm "nik:nat-eq" [numbered (.var 0) (.var 1), numbered (.var 2) (.var 3)],
    libTerm "nat-eq" [.var 0, .var 2]⟩

end EqualNumbers

/-- **The rules that compare two numbers in unary**: the helper `nat-eq`. -/
def equalNumbersRules (N : Spelling) : List RewriteRule :=
  [EqualNumbers.zeroZero N, EqualNumbers.zeroSuccessor N, EqualNumbers.successorZero N,
    EqualNumbers.successors]

/-- **The rule of `nik:nat-eq`**: it hands the two numbers to the helper. -/
def equalityTestRules : List RewriteRule := [EqualNumbers.test]

/-- **The helper decides the equality of two numbers in unary.** -/
theorem equalNumbers_reduces (N : Spelling) {theory : Theory}
    (holds : Holds theory (equalNumbersRules N)) :
    ∀ first second : Nat, Reduces theory (libTerm "nat-eq" [unary first, unary second])
      (truth N (decide (first = second)))
  | 0, 0 =>
      fires (rule := EqualNumbers.zeroZero N) (holds _ (by simp [equalNumbersRules])) []
        (by simp only [EqualNumbers.zeroZero]; instances; rfl)
        (by simp only [EqualNumbers.zeroZero]; instances; rfl)
  | 0, second + 1 =>
      fires (rule := EqualNumbers.zeroSuccessor N) (holds _ (by simp [equalNumbersRules]))
        [unary second] (by simp only [EqualNumbers.zeroSuccessor]; instances; rfl)
        (by simp only [EqualNumbers.zeroSuccessor]; instances; rfl)
  | first + 1, 0 =>
      fires (rule := EqualNumbers.successorZero N) (holds _ (by simp [equalNumbersRules]))
        [unary first] (by simp only [EqualNumbers.successorZero]; instances; rfl)
        (by simp only [EqualNumbers.successorZero]; instances; rfl)
  | first + 1, second + 1 => by
      have step : Reduces theory (libTerm "nat-eq" [unary (first + 1), unary (second + 1)])
          (libTerm "nat-eq" [unary first, unary second]) :=
        fires (rule := EqualNumbers.successors) (holds _ (by simp [equalNumbersRules]))
          [unary first, unary second] (by simp only [EqualNumbers.successors]; instances; rfl)
          (by simp only [EqualNumbers.successors]; instances)
      have rest := equalNumbers_reduces N holds first second
      have same : decide (first + 1 = second + 1) = decide (first = second) := by simp
      rw [same]
      exact step.trans rest

/-- The equality test of two numbers, whatever their marks. -/
theorem equalityTest_reduces (N : Spelling) {theory : Theory}
    (holds : Holds theory (equalityTestRules ++ equalNumbersRules N)) (first second : Nat)
    (firstMark secondMark : LF.Term) :
    Reduces theory
      (callTerm "nik:nat-eq" [numbered (unary first) firstMark, numbered (unary second) secondMark])
      (truth N (decide (first = second))) :=
  (fires (rule := EqualNumbers.test) (holds.left _ (by simp [equalityTestRules]))
      [unary first, firstMark, unary second, secondMark]
      (by simp only [EqualNumbers.test]; instances) (by simp only [EqualNumbers.test]; instances)).trans
    (equalNumbers_reduces N holds.right first second)

/-! ## The sum -/

namespace Sum

def test : RewriteRule :=
  ⟨callTerm "nik:nat-add" [numbered (.var 0) (.var 1), numbered (.var 2) (.var 3)],
    numbered (libTerm "nat-add" [.var 0, .var 2]) (.con "canon")⟩

def zero : RewriteRule := ⟨libTerm "nat-add" [.con "zero", .var 0], .var 0⟩

def successor : RewriteRule :=
  ⟨libTerm "nat-add" [.app (.con "succ") (.var 0), .var 1],
    .app (.con "succ") (libTerm "nat-add" [.var 0, .var 1])⟩

end Sum

/-- **The rules of `nik:nat-add`**, with the helper `nat-add` on numbers in
unary. -/
def sumRules : List RewriteRule := [Sum.test, Sum.zero, Sum.successor]

/-- **The helper adds two numbers in unary.** -/
theorem unarySum_reduces {theory : Theory} (holds : Holds theory sumRules) (second : Nat) :
    ∀ first : Nat, Reduces theory (libTerm "nat-add" [unary first, unary second])
      (unary (first + second))
  | 0 => by
      rw [Nat.zero_add]
      exact fires (rule := Sum.zero) (holds _ (by simp [sumRules])) [unary second]
        (by simp only [Sum.zero]; instances; rfl) (by simp only [Sum.zero]; instances)
  | first + 1 => by
      have step : Reduces theory (libTerm "nat-add" [unary (first + 1), unary second])
          (.app (.con "succ") (libTerm "nat-add" [unary first, unary second])) :=
        fires (rule := Sum.successor) (holds _ (by simp [sumRules])) [unary first, unary second]
          (by simp only [Sum.successor]; instances; rfl) (by simp only [Sum.successor]; instances)
      rw [Nat.succ_add]
      exact step.trans (Dedukti.Reduces.app .refl (unarySum_reduces holds second first))

/-- The sum of two numbers, whatever their marks, canonically written. -/
theorem sum_reduces {theory : Theory} (holds : Holds theory sumRules) (first second : Nat)
    (firstMark secondMark : LF.Term) :
    Reduces theory
      (callTerm "nik:nat-add" [numbered (unary first) firstMark, numbered (unary second) secondMark])
      (numeral (first + second)) :=
  (fires (rule := Sum.test) (holds _ (by simp [sumRules]))
      [unary first, firstMark, unary second, secondMark]
      (by simp only [Sum.test]; instances) (by simp only [Sum.test]; instances; rfl)).trans
    (Dedukti.Reduces.app (Dedukti.Reduces.app .refl (unarySum_reduces holds second first)) .refl)

/-! ## The strict order -/

namespace Less

def test : RewriteRule :=
  ⟨callTerm "nik:nat-lt" [numbered (.var 0) (.var 1), numbered (.var 2) (.var 3)],
    libTerm "nat-lt" [.var 0, .var 2]⟩

def anyZero (N : Spelling) : RewriteRule :=
  ⟨libTerm "nat-lt" [.var 0, .con "zero"], truth N false⟩

def zeroSuccessor (N : Spelling) : RewriteRule :=
  ⟨libTerm "nat-lt" [.con "zero", .app (.con "succ") (.var 0)], truth N true⟩

def successors : RewriteRule :=
  ⟨libTerm "nat-lt" [.app (.con "succ") (.var 0), .app (.con "succ") (.var 1)],
    libTerm "nat-lt" [.var 0, .var 1]⟩

end Less

/-- **The rules of `nik:nat-lt`**, with the helper `nat-lt` on numbers in
unary. -/
def lessRules (N : Spelling) : List RewriteRule :=
  [Less.test, Less.anyZero N, Less.zeroSuccessor N, Less.successors]

/-- **The helper decides the strict order of two numbers in unary.** -/
theorem unaryLess_reduces (N : Spelling) {theory : Theory} (holds : Holds theory (lessRules N)) :
    ∀ first second : Nat, Reduces theory (libTerm "nat-lt" [unary first, unary second])
      (truth N (decide (first < second)))
  | first, 0 =>
      fires (rule := Less.anyZero N) (holds _ (by simp [lessRules])) [unary first]
        (by simp only [Less.anyZero]; instances; rfl)
        (by simp only [Less.anyZero]; instances; rfl)
  | 0, second + 1 =>
      fires (rule := Less.zeroSuccessor N) (holds _ (by simp [lessRules])) [unary second]
        (by simp only [Less.zeroSuccessor]; instances; rfl)
        (by simp only [Less.zeroSuccessor]; instances; rfl)
  | first + 1, second + 1 => by
      have step : Reduces theory (libTerm "nat-lt" [unary (first + 1), unary (second + 1)])
          (libTerm "nat-lt" [unary first, unary second]) :=
        fires (rule := Less.successors) (holds _ (by simp [lessRules]))
          [unary first, unary second] (by simp only [Less.successors]; instances; rfl)
          (by simp only [Less.successors]; instances)
      have rest := unaryLess_reduces N holds first second
      have same : decide (first + 1 < second + 1) = decide (first < second) := by simp
      rw [same]
      exact step.trans rest

/-- The strict order of two numbers, whatever their marks. -/
theorem less_reduces (N : Spelling) {theory : Theory} (holds : Holds theory (lessRules N))
    (first second : Nat) (firstMark secondMark : LF.Term) :
    Reduces theory
      (callTerm "nik:nat-lt" [numbered (unary first) firstMark, numbered (unary second) secondMark])
      (truth N (decide (first < second))) :=
  (fires (rule := Less.test) (holds _ (by simp [lessRules]))
      [unary first, firstMark, unary second, secondMark]
      (by simp only [Less.test]; instances) (by simp only [Less.test]; instances)).trans
    (unaryLess_reduces N holds first second)

/-! ## The table, and agreement with the host -/

/-- **The arithmetic that the kernel uses, as rules**: sixteen rules. -/
def naturalRules (N : Spelling) : List RewriteRule :=
  zeroTestRules N ++ (predecessorRules ++ (equalityTestRules ++ equalNumbersRules N ++
    (sumRules ++ lessRules N)))

/-- The primitives that these rules compute. -/
def naturalPrimitives : List String :=
  ["nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:nat-add", "nik:nat-lt"]

theorem naturalRules_length (N : Spelling) : (naturalRules N).length = 16 := by
  simp [naturalRules, zeroTestRules, predecessorRules, equalityTestRules, equalNumbersRules,
    sumRules, lessRules]

theorem zeroTest_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:nat-zero" arguments =
      (match arguments with
        | [argument] =>
            match natural? argument with
            | some value => .value (.sym (if value = 0 then "True" else "False"))
            | none => .fault
        | _ => .fault) := rfl

theorem predecessor_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:nat-pred" arguments =
      (match arguments with
        | [argument] =>
            match natural? argument with
            | some value => .value (natural value.pred)
            | none => .fault
        | _ => .fault) := rfl

theorem equalityTest_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:nat-eq" arguments =
      (match arguments with
        | [left, right] =>
            match natural? left, natural? right with
            | some first, some second => .value (boolean (decide (first = second)))
            | _, _ => .fault
        | _ => .fault) := rfl

theorem sum_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:nat-add" arguments =
      (match arguments with
        | [left, right] =>
            match natural? left, natural? right with
            | some first, some second => .value (natural (first + second))
            | _, _ => .fault
        | _ => .fault) := rfl

theorem less_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:nat-lt" arguments =
      (match arguments with
        | [left, right] =>
            match natural? left, natural? right with
            | some first, some second => .value (boolean (decide (first < second)))
            | _, _ => .fault
        | _ => .fault) := rfl

/-- **The rules of arithmetic agree with the shared host**: when the host
returns a value for the call of one of the five primitives on data, the call
on the readings of the data reduces to the reading of that value. -/
theorem naturals_realized (N : Spelling) {theory : Theory} (holds : Holds theory (naturalRules N)) :
    RealizesPrimitives N theory computationalHost naturalPrimitives := by
  intro head member arguments result returned
  simp only [naturalPrimitives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [zeroTest_unfold] at returned
    split at returned
    · next argument =>
      split at returned
      · next value isNumber =>
        obtain rfl := (PrimitiveResult.value.inj returned)
        obtain ⟨mark, shape⟩ := datum_of_natural (N := N) isNumber
        have reduced := zeroTest_reduces N holds.left value mark
        simp only [data, shape]
        by_cases isZero : value = 0 <;> simpa [datum, truth, isZero] using reduced
      · cases returned
    · cases returned
  · rw [predecessor_unfold] at returned
    split at returned
    · next argument =>
      split at returned
      · next value isNumber =>
        obtain rfl := (PrimitiveResult.value.inj returned)
        obtain ⟨mark, shape⟩ := datum_of_natural (N := N) isNumber
        simp only [data, shape, datum_natural]
        exact predecessor_reduces holds.right.left value mark
      · cases returned
    · cases returned
  · rw [equalityTest_unfold] at returned
    split at returned
    · next left right =>
      split at returned
      · next first second isFirst isSecond =>
        obtain rfl := (PrimitiveResult.value.inj returned)
        obtain ⟨firstMark, firstShape⟩ := datum_of_natural (N := N) isFirst
        obtain ⟨secondMark, secondShape⟩ := datum_of_natural (N := N) isSecond
        simp only [data, firstShape, secondShape, datum_boolean_eq_truth]
        exact equalityTest_reduces N holds.right.right.left first second firstMark secondMark
      · cases returned
    · cases returned
  · rw [sum_unfold] at returned
    split at returned
    · next left right =>
      split at returned
      · next first second isFirst isSecond =>
        obtain rfl := (PrimitiveResult.value.inj returned)
        obtain ⟨firstMark, firstShape⟩ := datum_of_natural (N := N) isFirst
        obtain ⟨secondMark, secondShape⟩ := datum_of_natural (N := N) isSecond
        simp only [data, firstShape, secondShape, datum_natural]
        exact sum_reduces holds.right.right.right.left first second firstMark secondMark
      · cases returned
    · cases returned
  · rw [less_unfold] at returned
    split at returned
    · next left right =>
      split at returned
      · next first second isFirst isSecond =>
        obtain rfl := (PrimitiveResult.value.inj returned)
        obtain ⟨firstMark, firstShape⟩ := datum_of_natural (N := N) isFirst
        obtain ⟨secondMark, secondShape⟩ := datum_of_natural (N := N) isSecond
        simp only [data, firstShape, secondShape, datum_boolean_eq_truth]
        exact less_reduces N holds.right.right.right.right first second firstMark secondMark
      · cases returned
    · cases returned

/-- The host handles each of the five primitives. -/
theorem naturals_handled : ∀ head ∈ naturalPrimitives, ∀ arguments : List EngineTerm,
    computationalHost.primitive head arguments ≠ .unhandled := by
  intro head member arguments
  simp only [naturalPrimitives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [zeroTest_unfold]; split <;> (try split) <;> simp
  · rw [predecessor_unfold]; split <;> (try split) <;> simp
  · rw [equalityTest_unfold]; split <;> (try split) <;> simp
  · rw [sum_unfold]; split <;> (try split) <;> simp
  · rw [less_unfold]; split <;> (try split) <;> simp

/-! ## With names written as constants -/

/-- **The sixteen rules are orthogonal.** -/
theorem naturalRules_orthogonal : orthogonalCheck (naturalRules constantSpelling) = true := by
  decide

/-- They are first-order rules with bound right sides. -/
theorem naturalRules_runnable : RunnableEquations (naturalRules constantSpelling) := by
  constructor <;> decide

/-- Each rewrites a call. -/
theorem naturalRules_rewriteCalls :
    ∀ rule ∈ naturalRules constantSpelling, rewritesCall rule = true := by
  decide

/-- **Positive**: two plus one is three, by the rules. -/
theorem two_plus_one :
    Reduces (programTheory (naturalRules constantSpelling))
      (callTerm "nik:nat-add" [numeral 2, numeral 1]) (numeral 3) :=
  sum_reduces (holds_programTheory _).right.right.right.left 2 1 _ _

/-- **Negative**: the sum of a symbol and a number has no step, where the
host faults. -/
theorem sum_stuck :
    computationalHost.primitive "nik:nat-add" [.sym "a", natural 1] = .fault ∧
      IsNormal (Step (programTheory (naturalRules constantSpelling)))
        (callTerm "nik:nat-add" (data constantSpelling [.sym "a", natural 1])) := by
  have reading : data constantSpelling [.sym "a", natural 1] =
      [tag "sym" (.con "a"), numeral 1] := by
    simp [data, datum, datum_natural, constantSpelling]
  rw [reading]
  exact ⟨rfl, Dedukti.normal_of_normalTest
    (Mettapedia.Logic.HostingStyles.AtomsReduce.programCover (naturalRules constantSpelling)) _
    (by decide)⟩

#print axioms datum_of_natural
#print axioms zeroTest_reduces
#print axioms predecessor_reduces
#print axioms equalNumbers_reduces
#print axioms equalityTest_reduces
#print axioms unarySum_reduces
#print axioms sum_reduces
#print axioms unaryLess_reduces
#print axioms less_reduces
#print axioms naturals_realized
#print axioms naturals_handled
#print axioms naturalRules_orthogonal
#print axioms naturalRules_runnable
#print axioms two_plus_one
#print axioms sum_stuck

end Mettapedia.Logic.HostingStyles.StoredPrograms
