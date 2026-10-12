import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

/-!
# Disjoint name scopes can retain distinct process decompositions

The left process scope is null. The right process scope contains the actual
closed output and its suspended quotation. Their name images are disjoint,
and their complete canonical channel supports are disjoint. Nevertheless the
same quoted parallel composition has two distinct right process components.

These are predicates on the actual sorted source equation classes, not on
chosen raw representatives. The support reading uses the existing canonical
encoding and channel inventory. The control isolates the missing faithfulness
of quotation: the name eta equation does not imply process beta. It also
shows that equality of quoted codes need not survive adjoining a process.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopeQuotientControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def leftScope (process : Process []) : Prop := process = zero []

def rightScope (process : Process []) : Prop := process = visible ∨ process = suspended

def nameImage (scope : Process [] → Prop) (name : Name []) : Prop :=
  ∃ process, scope process ∧ quote process = name

def channelSupport (process : Process []) := freeNames (encodeEquationClass process)

theorem left_image (name : Name []) : nameImage leftScope name ↔ name = quote (zero []) := by
  constructor
  · rintro ⟨process, rfl, readout⟩
    exact readout.symm
  · intro same
    exact ⟨zero [], rfl, same.symm⟩

theorem right_image (name : Name []) : nameImage rightScope name ↔ name = quote visible := by
  constructor
  · rintro ⟨process, admitted, readout⟩
    rcases admitted with rfl | rfl
    · exact readout.symm
    · exact readout.symm.trans same_actual_name
  · intro same
    exact ⟨visible, Or.inl rfl, same.symm⟩

theorem quoted_output_not_null : quote visible ≠ quote (zero []) := by
  intro same
  have counts := congrArg RhoSourceOutputPredicate.count same
  change (1 : Nat) = 0 at counts
  cases counts

theorem disjoint_name_extensions (name : Name []) :
    ¬ (nameImage leftScope name ∧ nameImage rightScope name) := by
  rintro ⟨left, right⟩
  exact quoted_output_not_null
    (((right_image name).mp right).symm.trans ((left_image name).mp left))

theorem null_support_empty : channelSupport (zero []) = ∅ := by
  change freeNames (canonicalize (.apply "PZero" [])) = ∅
  rw [canonicalize_apply_general "PZero" [] (by simp)]
  change freeNames (.apply "PZero" []) = ∅
  unfold freeNames
  split <;> simp_all

theorem whole_scope_supports_disjoint :
    ∀ first second, leftScope first → rightScope second →
      Disjoint (channelSupport first) (channelSupport second) := by
  intro first second left _right
  cases left
  rw [null_support_empty]
  exact disjoint_bot_left

structure Decomposition (name : Name []) where
  first : Process []
  second : Process []
  first_admitted : leftScope first
  second_admitted : rightScope second
  readout : quote (join first second) = name

def outputDecomposition : Decomposition (quote visible) where
  first := zero []
  second := visible
  first_admitted := rfl
  second_admitted := Or.inl rfl
  readout := congrArg quote (join_zero_left visible)

def suspendedDecomposition : Decomposition (quote visible) where
  first := zero []
  second := suspended
  first_admitted := rfl
  second_admitted := Or.inr rfl
  readout := (congrArg quote (join_zero_left suspended)).trans same_actual_name

theorem same_name_distinct_decompositions : outputDecomposition ≠ suspendedDecomposition := by
  intro same
  exact suspended_not_visible (congrArg Decomposition.second same).symm

theorem right_components_not_equation_equal :
    outputDecomposition.second ≠ suspendedDecomposition.second := suspended_not_visible.symm

theorem scope_disjointness_and_support_do_not_give_unique_components :
    ¬ ∀ name : Name [], ∀ first second : Decomposition name,
      first.first = second.first ∧ first.second = second.second := by
  intro unique
  exact right_components_not_equation_equal
    (unique (quote visible) outputDecomposition suspendedDecomposition).2

theorem quoted_equality_not_stable_under_parallel :
    quote (join suspended visible) ≠ quote (join visible visible) := by
  intro same
  have encoded := congrArg encodeEquationClass same
  change canonicalize (encodeTerm (quoteRaw (parallel suspendedRaw RhoSourceOutputPredicate.output))) =
    canonicalize (encodeTerm (quoteRaw (parallel RhoSourceOutputPredicate.output
      RhoSourceOutputPredicate.output))) at encoded
  let outputPattern := encodeTerm RhoSourceOutputPredicate.output
  let suspendedPattern := encodeTerm suspendedRaw
  change normalizeQuote (collapseBag (normalizeBagElements [suspendedPattern, outputPattern])) =
    normalizeQuote (collapseBag (normalizeBagElements [outputPattern, outputPattern])) at encoded
  rw [normalizeBagElements_eq_sort_bagContents,
    normalizeBagElements_eq_sort_bagContents] at encoded
  change normalizeQuote (collapseBag (sortPatterns [suspendedPattern, outputPattern])) =
    normalizeQuote (collapseBag (sortPatterns [outputPattern, outputPattern])) at encoded
  have leftLength : 2 ≤ (sortPatterns [suspendedPattern, outputPattern]).length := by
    rw [← (sortPatterns_perm [suspendedPattern, outputPattern]).length_eq]
    exact Nat.le_refl 2
  have rightLength : 2 ≤ (sortPatterns [outputPattern, outputPattern]).length := by
    rw [← (sortPatterns_perm [outputPattern, outputPattern]).length_eq]
    exact Nat.le_refl 2
  rw [collapseBag_eq_bag_of_length_ge_two leftLength,
    collapseBag_eq_bag_of_length_ge_two rightLength] at encoded
  change MeTTaIL.Syntax.Pattern.apply "NQuote"
      [.collection .hashBag (sortPatterns [suspendedPattern, outputPattern]) none] =
    MeTTaIL.Syntax.Pattern.apply "NQuote"
      [.collection .hashBag (sortPatterns [outputPattern, outputPattern]) none] at encoded
  have bags := (List.cons.inj (MeTTaIL.Syntax.Pattern.apply.inj encoded).2).1
  have lists := (MeTTaIL.Syntax.Pattern.collection.inj bags).2.1
  have member : suspendedPattern ∈ sortPatterns [suspendedPattern, outputPattern] :=
    sortPatterns_mem_iff.mpr List.mem_cons_self
  rw [lists] at member
  have samePattern : suspendedPattern = outputPattern := by
    simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_self] using
      (sortPatterns_mem_iff.mp member)
  have different : suspendedPattern ≠ outputPattern := by decide +kernel
  exact different samePattern

end Mettapedia.OSLF.Binding.RhoScopeQuotientControls
