import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalEquivalence
import Mathlib.Data.Sym.Sym2

/-!
# Actual unordered name pairs in the rho source quotient

Quoting the parallel composition of two dropped names is a genuine constructor
of unordered pairs, including repeated members. Its canonical pattern has two
drop components and preserves their multiplicity. Equality of the result
therefore recovers exactly the original pair up to swapping. The constructor
does not identify either the quoted null or the quoted output seed with a
compound pair.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCanonicalNamePairs

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

theorem encode_drop {context : Ctx sig} (name : Name context) :
    encodeEquationClass (drop name) = .apply "PDrop" [encodeEquationClass name] := by
  induction name using Quotient.inductionOn with
  | _ name =>
    change canonicalize (.apply "PDrop" [encodeTerm name]) =
      .apply "PDrop" [canonicalize (encodeTerm name)]
    rw [canonicalize_apply_general "PDrop" [encodeTerm name] (by simp)]
    rfl

theorem encode_quote {context : Ctx sig} (process : Process context) :
    encodeEquationClass (quote process) = normalizeQuote (encodeEquationClass process) := by
  induction process using Quotient.inductionOn with
  | _ process => rfl

theorem encode_join {context : Ctx sig} (first second : Process context) :
    encodeEquationClass (join first second) =
      collapseBag (normalizeBagElements [encodeEquationClass first, encodeEquationClass second]) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second => rfl

def combine {context : Ctx sig} (first second : Name context) : Name context :=
  quote (join (drop first) (drop second))

theorem combine_commutes {context : Ctx sig} (first second : Name context) :
    combine first second = combine second first := congrArg quote (join_commutes _ _)

theorem normalize_drop_pair (first second : Pattern) :
    normalizeBagElements [.apply "PDrop" [first], .apply "PDrop" [second]] =
      sortPatterns [.apply "PDrop" [first], .apply "PDrop" [second]] := by
  apply congrArg sortPatterns
  simp [bagSplice]

theorem combine_encoding {context : Ctx sig} (first second : Name context) :
    encodeEquationClass (combine first second) = .apply "NQuote"
      [.collection .hashBag
        (sortPatterns [.apply "PDrop" [encodeEquationClass first],
          .apply "PDrop" [encodeEquationClass second]]) none] := by
  unfold combine
  rw [encode_quote, encode_join, encode_drop, encode_drop, normalize_drop_pair]
  have pairLength : 2 ≤ (sortPatterns [.apply "PDrop" [encodeEquationClass first],
      .apply "PDrop" [encodeEquationClass second]]).length := by
    rw [← (sortPatterns_perm _).length_eq]
    exact Nat.le_refl _
  rw [collapseBag_eq_bag_of_length_ge_two pairLength]
  rfl

private theorem pair_permutation {first second third fourth : Pattern}
    (permutation : [first, second].Perm [third, fourth]) :
    (first = third ∧ second = fourth) ∨ (first = fourth ∧ second = third) := by
  have membership : first ∈ [third, fourth] := permutation.mem_iff.mp (by simp)
  rcases List.mem_cons.mp membership with direct | rest
  · have remaining : [second].Perm [fourth] := by
      rw [direct] at permutation
      exact List.Perm.cons_inv permutation
    exact Or.inl ⟨direct, by simpa using remaining⟩
  · have swapped : first = fourth := List.mem_singleton.mp rest
    have remaining : [second].Perm [third] := by
      have reversed := permutation.trans (List.Perm.swap fourth third [])
      rw [swapped] at reversed
      exact List.Perm.cons_inv reversed
    exact Or.inr ⟨swapped, by simpa using remaining⟩

theorem sort_pair_cases (first second : Pattern) :
    sortPatterns [first, second] = [first, second] ∨
      sortPatterns [first, second] = [second, first] := by
  have length : (sortPatterns [first, second]).length = 2 :=
    (sortPatterns_perm _).length_eq.symm
  obtain ⟨third, fourth, presentation⟩ :
      ∃ third fourth, sortPatterns [first, second] = [third, fourth] := by
    cases sorted : sortPatterns [first, second] with
    | nil => simp [sorted] at length
    | cons third rest =>
      cases rest with
      | nil => simp [sorted] at length
      | cons fourth tail =>
        have empty : tail = [] := by simpa [sorted] using length
        exact ⟨third, fourth, by simp [empty]⟩
  have permutation := sortPatterns_perm [first, second]
  rw [presentation] at permutation
  rcases pair_permutation permutation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl presentation
  · exact Or.inr presentation

private theorem drop_pattern_injective {context : Ctx sig} {first second : Name context}
    (same : Pattern.apply "PDrop" [encodeEquationClass first] =
      .apply "PDrop" [encodeEquationClass second]) : first = second :=
  canonical_encoding_injective context Srt.nm
    ((List.cons.inj (Pattern.apply.inj same).2).1)

theorem combine_equality_iff {context : Ctx sig} (first second third fourth : Name context) :
    combine first second = combine third fourth ↔
      (first = third ∧ second = fourth) ∨ (first = fourth ∧ second = third) := by
  constructor
  · intro same
    have encoded := congrArg encodeEquationClass same
    rw [combine_encoding, combine_encoding] at encoded
    have sorted : sortPatterns [.apply "PDrop" [encodeEquationClass first],
        .apply "PDrop" [encodeEquationClass second]] =
        sortPatterns [.apply "PDrop" [encodeEquationClass third],
          .apply "PDrop" [encodeEquationClass fourth]] :=
      (Pattern.collection.inj ((List.cons.inj (Pattern.apply.inj encoded).2).1)).2.1
    have permutation : [Pattern.apply "PDrop" [encodeEquationClass first],
        .apply "PDrop" [encodeEquationClass second]].Perm
        [.apply "PDrop" [encodeEquationClass third], .apply "PDrop" [encodeEquationClass fourth]] := by
      apply (sortPatterns_perm _).trans
      rw [sorted]
      exact (sortPatterns_perm _).symm
    rcases pair_permutation permutation with ⟨left, right⟩ | ⟨left, right⟩
    · exact Or.inl ⟨drop_pattern_injective left, drop_pattern_injective right⟩
    · exact Or.inr ⟨drop_pattern_injective left, drop_pattern_injective right⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact combine_commutes _ _

def pairConstructor {context : Ctx sig} : Sym2 (Name context) → Name context :=
  Sym2.lift ⟨combine, combine_commutes⟩

theorem pairConstructor_mk {context : Ctx sig} (first second : Name context) :
    pairConstructor (Sym2.mk first second) = combine first second := rfl

theorem pairConstructor_injective (context : Ctx sig) :
    Function.Injective (pairConstructor (context := context)) := by
  intro first second
  refine Sym2.inductionOn₂ first second ?_
  intro first second third fourth same
  exact Sym2.eq_iff.mpr ((combine_equality_iff _ _ _ _).mp same)

theorem combine_ne_null {context : Ctx sig} (first second : Name context) :
    combine first second ≠ quote (zero context) := by
  intro same
  have encoded := congrArg encodeEquationClass same
  rw [combine_encoding] at encoded
  change Pattern.apply "NQuote" [.collection .hashBag _ none] =
    .apply "NQuote" [.apply "PZero" []] at encoded
  have impossible := (List.cons.inj (Pattern.apply.inj encoded).2).1
  cases impossible

theorem combine_ne_output (first second : Name []) : combine first second ≠ quote visible := by
  intro same
  have encoded := congrArg encodeEquationClass same
  rw [combine_encoding] at encoded
  change Pattern.apply "NQuote" [.collection .hashBag _ none] =
    .apply "NQuote" [.apply "POutput" [_, _]] at encoded
  have impossible := (List.cons.inj (Pattern.apply.inj encoded).2).1
  cases impossible

end Mettapedia.OSLF.Binding.RhoCanonicalNamePairs
