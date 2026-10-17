import Mettapedia.GSLT.LanguageDef.RegexSourceProjection

/-!
# Symbolic Unicode character classes

Class operations are interpreted over Unicode scalar values, not the host
locale. Property and simple-fold tables are explicit dependencies. The set
meaning is independent of the Boolean interpreter, including the existential
meaning of simple-fold closure. This file does not certify a Unicode database.

Case-insensitive negation means complementing the fold-closed positive class.
Closing the complement instead is a different operation, as the controls show.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexClassInterpretation

open Mettapedia.GSLT.Parsing.ParserProfileSemantics (isUnicodeScalar)
open RegexSourceProjection (InRanges complementRanges)
open RegexSelection (ScalarRange)

/-- Versioned data supplied by the language's character interpretation. -/
structure Provider where
  version : String
  property : String → Nat → Bool
  equivalents : Nat → List Nat

/-- Simple folding is an equivalence on scalars. This is an obligation of a
provider; the executable interpretation below does not manufacture the laws. -/
structure FoldLaws (provider : Provider) : Prop where
  reflexive : ∀ scalar, isUnicodeScalar scalar = true → scalar ∈ provider.equivalents scalar
  symmetric : ∀ a b, b ∈ provider.equivalents a → a ∈ provider.equivalents b
  transitive : ∀ a b c, b ∈ provider.equivalents a → c ∈ provider.equivalents b →
    c ∈ provider.equivalents a
  scalar : ∀ a b, isUnicodeScalar a = true → b ∈ provider.equivalents a →
    isUnicodeScalar b = true

inductive Expr where
  | empty
  | universe
  | range (low high : Nat)
  | property (name : String)
  | union (left right : Expr)
  | intersection (left right : Expr)
  | difference (left right : Expr)
  | complement (body : Expr)
  | fold (body : Expr)
  deriving DecidableEq, Repr

def Scalar : Set Nat := { scalar | isUnicodeScalar scalar = true }

/-- Set-theoretic character meaning. Fold closure uses a witness in the
declared equivalence class, rather than a case conversion of the input. -/
def meaning (provider : Provider) : Expr → Set Nat
  | .empty => ∅
  | .universe => Scalar
  | .range low high => Scalar ∩ Set.Icc low high
  | .property name => Scalar ∩ { scalar | provider.property name scalar = true }
  | .union left right => meaning provider left ∪ meaning provider right
  | .intersection left right => meaning provider left ∩ meaning provider right
  | .difference left right => meaning provider left \ meaning provider right
  | .complement body => Scalar \ meaning provider body
  | .fold body => Scalar ∩ { scalar | ∃ representative ∈ provider.equivalents scalar,
      representative ∈ meaning provider body }

/-- Recursive membership without expanding the scalar universe. -/
def test (provider : Provider) : Expr → Nat → Bool
  | .empty, _ => false
  | .universe, scalar => isUnicodeScalar scalar
  | .range low high, scalar => isUnicodeScalar scalar && decide (low ≤ scalar ∧ scalar ≤ high)
  | .property name, scalar => isUnicodeScalar scalar && provider.property name scalar
  | .union left right, scalar => test provider left scalar || test provider right scalar
  | .intersection left right, scalar => test provider left scalar && test provider right scalar
  | .difference left right, scalar => test provider left scalar && !test provider right scalar
  | .complement body, scalar => isUnicodeScalar scalar && !test provider body scalar
  | .fold body, scalar => isUnicodeScalar scalar &&
      (provider.equivalents scalar).any (test provider body)

/-- Preservation and reflection of the declared set meaning. -/
theorem test_iff (provider : Provider) (expression : Expr) (scalar : Nat) :
    test provider expression scalar = true ↔ scalar ∈ meaning provider expression := by
  induction expression generalizing scalar with
  | empty => simp [test, meaning]
  | «universe» => rfl
  | range low high => simp [test, meaning, Scalar]
  | property name => simp [test, meaning, Scalar]
  | union left right before after => simp [test, meaning, before, after]
  | intersection left right before after => simp [test, meaning, before, after]
  | difference left right before after => simp [test, meaning, Bool.eq_false_iff, before, after]
  | complement body ih => simp [test, meaning, Scalar, Bool.eq_false_iff, ih]
  | fold body ih => simp [test, meaning, Scalar, ih]

theorem meaning_scalar (provider : Provider) (expression : Expr) :
    meaning provider expression ⊆ Scalar := by
  intro scalar member
  induction expression with
  | empty => exact False.elim member
  | «universe» => exact member
  | range | property | complement | fold => exact member.1
  | union _ _ before after => exact member.elim before after
  | intersection _ _ before _ => exact before member.1
  | difference _ _ before _ => exact before member.1

theorem rejects_non_scalar (provider : Provider) (expression : Expr) (scalar : Nat)
    (notScalar : isUnicodeScalar scalar = false) : test provider expression scalar = false := by
  cases result : test provider expression scalar with
  | false => rfl
  | true =>
      have valid := meaning_scalar provider expression ((test_iff provider expression scalar).1 result)
      simp [Scalar, notScalar] at valid

theorem complement_twice (provider : Provider) (body : Expr) :
    meaning provider (.complement (.complement body)) = meaning provider body := by
  ext scalar
  have subset := meaning_scalar provider body
  simp only [meaning, Set.mem_sdiff]
  exact ⟨fun member => by tauto, fun member => ⟨subset member, by tauto⟩⟩

theorem fold_extensive (provider : Provider) (laws : FoldLaws provider) (body : Expr) :
    meaning provider body ⊆ meaning provider (.fold body) := by
  intro scalar member
  have valid := meaning_scalar provider body member
  exact ⟨valid, scalar, laws.reflexive scalar valid, member⟩

theorem fold_idempotent (provider : Provider) (laws : FoldLaws provider) (body : Expr) :
    meaning provider (.fold (.fold body)) = meaning provider (.fold body) := by
  apply Set.Subset.antisymm
  · rintro scalar ⟨valid, representative, related, _, witness, relatedWitness, member⟩
    exact ⟨valid, witness, laws.transitive scalar representative witness related relatedWitness, member⟩
  · exact fold_extensive provider laws (.fold body)

theorem fold_membership_invariant (provider : Provider) (laws : FoldLaws provider)
    (body : Expr) {a b : Nat} (valid : isUnicodeScalar a = true)
    (related : b ∈ provider.equivalents a) :
    a ∈ meaning provider (.fold body) ↔ b ∈ meaning provider (.fold body) := by
  constructor
  · rintro ⟨_, witness, atA, member⟩
    exact ⟨laws.scalar a b valid related, witness,
      laws.transitive b a witness (laws.symmetric a b related) atA, member⟩
  · rintro ⟨_, witness, atB, member⟩
    exact ⟨valid, witness, laws.transitive a b witness related atB, member⟩

/-- Unicode-off changes shorthand/word interpretation and simple folding,
not the scalar alphabet or an explicitly named Unicode property. -/
structure Flags where
  insensitive : Bool := false
  unicode : Bool := true
  extended : Bool := false
  deriving DecidableEq, Repr

def selectProvider (unicode ascii : Provider) (flags : Flags) : Provider :=
  if flags.unicode then unicode else { unicode with equivalents := ascii.equivalents }

def interpretedClass (flags : Flags) (negative : Bool) (positive : Expr) : Expr :=
  let closed := if flags.insensitive then .fold positive else positive
  if negative then .complement closed else closed

theorem negative_insensitive (provider : Provider) (flags : Flags) (positive : Expr)
    (insensitive : flags.insensitive = true) (scalar : Nat) :
    test provider (interpretedClass flags true positive) scalar = true ↔
      isUnicodeScalar scalar = true ∧
      ∀ representative ∈ provider.equivalents scalar,
        representative ∉ meaning provider positive := by
  rw [test_iff]
  simp [interpretedClass, insensitive, meaning, Scalar]

/-- Finite interval materializations are judged by the same set observation.
The range membership is a separate executable fold. -/
def testRanges (ranges : List ScalarRange) (scalar : Nat) : Bool :=
  ranges.any (fun range => decide (range.1 ≤ scalar ∧ scalar ≤ range.2))

theorem testRanges_iff (ranges : List ScalarRange) (scalar : Nat) :
    testRanges ranges scalar = true ↔ InRanges scalar ranges := by
  simp [testRanges, InRanges]

theorem materialization_exact (provider : Provider) (body : Expr) (ranges : List ScalarRange)
    (describes : ∀ scalar, InRanges scalar ranges ↔ scalar ∈ meaning provider body)
    (scalar : Nat) : testRanges ranges scalar = test provider body scalar := by
  apply Bool.eq_iff_iff.mpr
  rw [testRanges_iff, test_iff]
  exact describes scalar

theorem negated_materialization (provider : Provider) (body : Expr) (ranges : List ScalarRange)
    (describes : ∀ scalar, InRanges scalar ranges ↔ scalar ∈ meaning provider body)
    (scalar : Nat) :
    testRanges (complementRanges ranges) scalar = test provider (.complement body) scalar := by
  apply Bool.eq_iff_iff.mpr
  rw [testRanges_iff, test_iff]
  rw [RegexSourceProjection.complementRanges_correct]
  simp only [meaning, Set.mem_sdiff, Scalar, Set.mem_ofPred_eq]
  rw [describes]

namespace Controls

private def latinExample : Provider where
  version := "example-A-a"
  property := fun name scalar => name == "Latin" && (scalar == 65 || scalar == 97)
  equivalents := fun scalar => if scalar == 65 || scalar == 97 then [65, 97] else [scalar]

theorem folded_literal_matches_both_cases :
    test latinExample (.fold (.range 97 97)) 65 = true ∧
    test latinExample (.fold (.range 97 97)) 97 = true := by decide

theorem negative_folded_literal_excludes_both_cases :
    test latinExample (interpretedClass ⟨true, true, false⟩ true (.range 97 97)) 65 = false ∧
    test latinExample (interpretedClass ⟨true, true, false⟩ true (.range 97 97)) 98 = true := by decide

/-- Closing a negative class instead of negating its closure is observably wrong. -/
theorem fold_of_complement_is_not_negated_fold :
    test latinExample (.fold (.complement (.range 97 97))) 65 = true ∧
    test latinExample (.complement (.fold (.range 97 97))) 65 = false := by decide

theorem symbolic_set_operations :
    test latinExample (.intersection (.property "Latin") (.complement (.range 97 97))) 65 = true ∧
    test latinExample (.difference (.range 65 100) (.union (.range 66 96) (.range 98 100))) 97 = true := by decide

theorem complement_never_admits_surrogates :
    test latinExample (.complement .empty) 55296 = false ∧
    test latinExample (.complement .empty) 1114112 = false := by decide

end Controls

#print axioms test_iff
#print axioms fold_idempotent
#print axioms fold_membership_invariant
#print axioms negative_insensitive
#print axioms negated_materialization

end Mettapedia.GSLT.LanguageDef.RegexClassInterpretation
