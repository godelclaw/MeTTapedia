import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMeasures
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Finite equation bounds under arbitrary binding-aware contexts

Replacing one selected redex by a size-preserving equation instance preserves
the whole source's node bound. Contexts contribute their existing symbols;
instantiated equation targets contribute only the source/schema/provider
alphabet. No finite depth or selected three-phase carrier is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts

open Syntax RuleBinding ScopedRuleMatching DerivedContexts PatternTreeSize
open GeneralEquationMeasures GeneralEquationAdmission GeneralEquationSupport GeneralEquationCanonical
open GeneralScopedMatch GeneralScopedMatchMeasures GeneralEquationCaptureDomain
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem listNodes_append (first second : List Pattern) :
    listNodes (first ++ second) = listNodes first + listNodes second := by
  induction first with
  | nil => simp only [List.nil_append, listNodes, Nat.zero_add]
  | cons pattern rest ih => simp only [List.cons_append, listNodes, ih]; omega

/-- Every syntactic context contributes the same static measure on each side. -/
theorem fill_preserves_nodes (context : OneHoleContext) (source target : Pattern)
    (same : nodes source = nodes target) : nodes (context.fill source) = nodes (context.fill target) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
      simp only [OneHoleContext.fill, nodes, listNodes_append, listNodes, ih]
  | lambda display inner ih => simp only [OneHoleContext.fill, nodes, ih]
  | multiLambda arity display inner ih => simp only [OneHoleContext.fill, nodes, ih]
  | substBody inner replacement ih => simp only [OneHoleContext.fill, nodes, ih]
  | substReplacement body inner ih => simp only [OneHoleContext.fill, nodes, ih]
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill, nodes, listNodes_append, listNodes, ih]

/-- Filling introduces only symbols already present in the context or target. -/
theorem fill_support_sources (context : OneHoleContext) (source target : Pattern) :
    (∀ label ∈ constructors (context.fill target),
      label ∈ constructors (context.fill source) ∨ label ∈ constructors target) ∧
    (∀ name ∈ (context.fill target).freeFvarNames,
      name ∈ (context.fill source).freeFvarNames ∨ name ∈ target.freeFvarNames) ∧
    (∀ arity ∈ arities (context.fill target),
      arity ∈ arities (context.fill source) ∨ arity ∈ arities target) := by
  induction context with
  | hole => exact ⟨fun _ member => Or.inr member, fun _ member => Or.inr member, fun _ member => Or.inr member⟩
  | apply label before inner after ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities,
        List.flatMap_append, List.flatMap_cons, List.mem_cons, List.mem_append] at *
      refine ⟨?_, ?_, ?_⟩
      · intro label member
        have available := ih.1 label
        tauto
      · intro name member
        have available := ih.2.1 name
        tauto
      · intro arity member
        have available := ih.2.2 arity
        tauto
  | lambda display inner ih => simpa only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities] using ih
  | multiLambda arity display inner ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_cons] at *
      refine ⟨?_, ?_, ?_⟩
      · intro label member
        have available := ih.1 label
        tauto
      · intro name member
        have available := ih.2.1 name
        tauto
      · intro arity member
        have available := ih.2.2 arity
        tauto
  | substBody inner replacement ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_append] at *
      refine ⟨?_, ?_, ?_⟩
      · intro label member
        have available := ih.1 label
        tauto
      · intro name member
        have available := ih.2.1 name
        tauto
      · intro arity member
        have available := ih.2.2 arity
        tauto
  | substReplacement body inner ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_append] at *
      refine ⟨?_, ?_, ?_⟩
      · intro label member
        have available := ih.1 label
        tauto
      · intro name member
        have available := ih.2.1 name
        tauto
      · intro arity member
        have available := ih.2.2 arity
        tauto
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities,
        List.flatMap_append, List.flatMap_cons, List.mem_append] at *
      refine ⟨?_, ?_, ?_⟩
      · intro label member
        have available := ih.1 label
        tauto
      · intro name member
        have available := ih.2.1 name
        tauto
      · intro arity member
        have available := ih.2.2 arity
        tauto

theorem fill_contains_source (context : OneHoleContext) (source : Pattern) :
    (∀ label ∈ constructors source, label ∈ constructors (context.fill source)) ∧
    (∀ name ∈ source.freeFvarNames, name ∈ (context.fill source).freeFvarNames) ∧
    (∀ arity ∈ arities source, arity ∈ arities (context.fill source)) := by
  induction context with
  | hole => exact ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩
  | apply label before inner after ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities,
        List.flatMap_append, List.flatMap_cons, List.mem_cons, List.mem_append] at *
      aesop
  | lambda display inner ih => simpa only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities] using ih
  | multiLambda arity display inner ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_cons] at *
      aesop
  | substBody inner replacement ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_append] at *
      aesop
  | substReplacement body inner ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities, List.mem_append] at *
      aesop
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill, constructors, Pattern.freeFvarNames, arities,
        List.flatMap_append, List.flatMap_cons, List.mem_append] at *
      aesop

theorem supported_redex {alphabet : Alphabet} {context : OneHoleContext} {source : Pattern}
    (support : Supported alphabet (context.fill source)) : Supported alphabet source := by
  have contains := fill_contains_source context source
  exact ⟨fun label member => support.1 label (contains.1 label member),
    fun name member => support.2.1 name (contains.2.1 name member),
    fun arity member => support.2.2 arity (contains.2.2 arity member)⟩

/-- A selected subterm of a canonical caller is canonical as well; binder
display metadata cannot reappear merely by descending through a context. -/
theorem canonical_redex (context : OneHoleContext) (source : Pattern)
    (canonical : (context.fill source).hasCanonicalBinderMetadata = true) :
    source.hasCanonicalBinderMetadata = true := by
  induction context with
  | hole => exact canonical
  | apply label before inner after ih =>
      apply ih
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
  | lambda display inner ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      exact ih canonical.2
  | multiLambda arity display inner ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      exact ih canonical.2
  | substBody inner replacement ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      exact ih canonical.1
  | substReplacement body inner ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      exact ih canonical.2
  | collection kind before inner after rest ih =>
      apply ih
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self))

theorem fill_preserves_support {alphabet : Alphabet} (context : OneHoleContext) (source target : Pattern)
    (before : Supported alphabet (context.fill source)) (after : Supported alphabet target) :
    Supported alphabet (context.fill target) := by
  have contains := fill_support_sources context source target
  refine ⟨?_, ?_, ?_⟩
  · intro label member
    exact (contains.1 label member).elim (before.1 label) (after.1 label)
  · intro name member
    exact (contains.2.1 name member).elim (before.2.1 name) (after.2.1 name)
  · intro arity member
    exact (contains.2.2 arity member).elim (before.2.2 arity) (after.2.2 arity)

/-- Balanced equation substitution and arbitrary context placement preserve
both whole-source bounds, even when premises introduce additional captures. -/
theorem balanced_contextual_preserves {alphabet : Alphabet}
    (context : OneHoleContext) (redex target : Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (captured completed : ScopedRuleMatching.Assignment)
    (accepted : checkRule rule spec = true) (support : Supported alphabet (context.fill redex))
    (template : Supported alphabet rule.right) (matched : captured ∈ matchRuleAt rule spec ambient redex)
    (extension : Extends captured completed) (reduct : reduct? rule spec ambient completed = some target) :
    nodes (context.fill redex) = nodes (context.fill target) ∧
      Supported alphabet (context.fill target).eraseBinderMetadata := by
  exact ⟨fill_preserves_nodes context redex target
    (matched_reduct_preserves_nodes accepted matched extension reduct),
    supported_erase (fill_preserves_support context redex target support
      (balanced_reduct_supported accepted (supported_redex support) template matched extension reduct))⟩

/-- Membership in the source-derived carrier is earned from independent
scope/sort checking and the structural bounds of the actual instance. -/
theorem contextual_equation_in_sourceUniverse (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (providerTerms : List Pattern)
    (context : OneHoleContext) (redex target : Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (captured completed : ScopedRuleMatching.Assignment)
    (selected : context.fill redex = source) (accepted : checkRule rule spec = true)
    (matched : captured ∈ matchRuleAt rule spec ambient redex)
    (extension : Extends captured completed) (reduct : reduct? rule spec ambient completed = some target)
    (templateSupport : Supported (alphabet language source providerTerms) rule.right)
    (bodies : SupportedBodies (alphabet language source providerTerms) completed)
    (typed : OpenPatternWellSorted language free bound type (context.fill target).eraseBinderMetadata) :
    (context.fill target).eraseBinderMetadata ∈ sourceUniverse language free bound type source providerTerms := by
  have ready := checkRule_sides rule spec accepted
  have same := fill_preserves_nodes context redex target
    (matched_reduct_preserves_nodes accepted matched extension reduct)
  have localSupport := instantiate_supported _ rule spec ambient .right [] 0 completed rule.right target
    ready.2.2.1 templateSupport bodies reduct
  have sourceSupport : Supported (alphabet language source providerTerms) (context.fill redex) := by
    rw [selected]
    exact source_supported language source providerTerms
  have targetSupport := supported_erase (fill_preserves_support context redex target sourceSupport localSupport)
  have small : nodes (context.fill target).eraseBinderMetadata ≤ nodes source := by
    rw [eraseBinderMetadata_nodes, ← same, selected]
  apply typedUniverse_complete _ _ _ language free bound type _ typed small targetSupport
  exact scoped_indices _ _ bound.length (nodes source) small typed.2.2.2
    (fun arity member => arity_le_maximum _ arity (targetSupport.2.2 arity member))

end Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts
