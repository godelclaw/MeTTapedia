import Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical
import Mettapedia.OSLF.NativeTypes.Instances.Local.Structural
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Finite root constructor decomposition modulo the original rho equations

Every original process constructor is inspected through its authored grammar
declaration. Canonical heads supply ordinary constructors; an actual singleton
parallel introduction supplies the parallel constructor even when unit or
singleton equations erased its syntactic root. Each returned value retains its
complete ordered arguments and typing evidence.

The coverage theorem concerns the complete constructor image with unrestricted
top input predicates. Ordered input-predicate coverage is a separate property:
one root introduction must not be mistaken for its full equation fibre.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Structural
open Mettapedia.OSLF.NativeTypes.Instances.Local.Structural

abbrev DeclarationIndex := Fin rhoCalc.terms.length

def declaration (index : DeclarationIndex) : GrammarRule := rhoCalc.terms[index]

abbrev Value (index : DeclarationIndex) :=
  ConstructorValue rhoCalc FreeTypeContext.empty [] (declaration index)

def representatives (source : Pattern) : List Pattern :=
  [canonicalize source, .collection .hashBag [canonicalize source] none]

def values (budget : Nat) (index : DeclarationIndex) (source : Pattern) : List (Value index) :=
  ((representatives source).take budget).flatMap
    (decompositions rhoCalc FreeTypeContext.empty [] (declaration index))

def closed (budget : Nat) (source : Pattern) : Bool :=
  decide ((representatives source).length ≤ budget)

def completionBudget (source : Pattern) : Nat := (representatives source).length

def Holds (index : DeclarationIndex) (source : Pattern) : Prop :=
  (declaration index).category = "Proc" ∧
    ∃ value : Value index, canonicalize source = canonicalize value.pattern

theorem representatives_sound {source representative : Pattern}
    (listed : representative ∈ representatives source) :
    canonicalize source = canonicalize representative := by
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · exact (canonicalize_idempotent source).symm
  · rw [canonicalize_parallel_singleton, canonicalize_idempotent]

theorem values_sound {budget : Nat} {index : DeclarationIndex} {source : Pattern}
    {value : Value index} (listed : value ∈ values budget index source) :
    canonicalize source = canonicalize value.pattern := by
  obtain ⟨representative, represented, member⟩ := List.mem_flatMap.mp listed
  rw [decomposition_sound member]
  exact representatives_sound (List.mem_of_mem_take represented)

private theorem canonical_source_typed (source : RhoProcess) :
    HasType rhoCalc FreeTypeContext.empty [] (canonicalize source.1) (.base "Proc") :=
  ((closed_process_wellSorted_iff _).mpr source.canonicalize.2).1.1

private theorem canonical_source_object (source : RhoProcess) :
    isObjectPattern (canonicalize source.1) = true :=
  ((closed_process_wellSorted_iff _).mpr source.canonicalize.2).1.2.2.2.1

private theorem introduction_of_typed_application {rule : GrammarRule}
    (member : rule ∈ rhoCalc.terms) {arguments : List Pattern}
    (typed : HasType rhoCalc FreeTypeContext.empty [] (.apply rule.label arguments)
      (.base rule.category)) :
    ∃ value : ConstructorValue rhoCalc FreeTypeContext.empty [] rule,
      value.pattern = .apply rule.label arguments := by
  generalize typeEq : (.base rule.category : TypeExpr) = type at typed
  generalize patternEq : (.apply rule.label arguments : Pattern) = pattern at typed
  cases typed with
  | bvar lookup => cases patternEq
  | fvar lookup => cases patternEq
  | lambda body => cases patternEq
  | multiLambda body => cases patternEq
  | subst body replacement => cases patternEq
  | collection elements => cases patternEq
  | collectionConstructor member shape elements => cases patternEq
  | @constructor _ selected actual membership ordinary argumentsTyped =>
      have shape := Pattern.apply.inj patternEq
      have same : selected = rule :=
        List.inj_on_of_nodup_map
          (LanguageDef.constructorLabels_nodup_of_validate_eq_nil rhoCalc rhoCalc_validate_eq_nil)
          membership member shape.1.symm
      subst selected
      exact ⟨.ordinary actual ordinary argumentsTyped, rfl⟩

private theorem ordinary_coverage (source : RhoProcess) {rule : GrammarRule}
    (member : rule ∈ rhoCalc.terms) (category : rule.category = "Proc")
    (ordinary : ¬ UsesBareCollection rule) (notQuote : rule.label ≠ "NQuote")
    (value : ConstructorValue rhoCalc FreeTypeContext.empty [] rule)
    (related : canonicalize source.1 = canonicalize value.pattern) :
    ∃ candidate ∈ decompositions rhoCalc FreeTypeContext.empty [] rule (canonicalize source.1),
      canonicalize source.1 = canonicalize candidate.pattern := by
  cases value with
  | ordinary arguments _ _ =>
      have shape : canonicalize source.1 = .apply rule.label (canonicalizeList arguments) := by
        rw [related, ConstructorValue.pattern,
          canonicalize_apply_general rule.label arguments (fun quoted => notQuote quoted.1)]
      have typed : HasType rhoCalc FreeTypeContext.empty []
          (.apply rule.label (canonicalizeList arguments)) (.base rule.category) := by
        rw [category, ← shape]
        exact canonical_source_typed source
      obtain ⟨candidate, rawShape⟩ := introduction_of_typed_application member typed
      have patternEq : candidate.pattern = canonicalize source.1 := rawShape.trans shape.symm
      refine ⟨candidate, decomposition_complete (canonical_source_object source) candidate patternEq, ?_⟩
      rw [patternEq, canonicalize_idempotent]
  | collection name kind elementType elements rest shape _ =>
      exact False.elim (ordinary ⟨name, kind, elementType, shape⟩)

private theorem parallel_coverage (source : RhoProcess) :
    ∃ candidate ∈ decompositions rhoCalc FreeTypeContext.empty [] pparRule
      (.collection .hashBag [canonicalize source.1] none),
      canonicalize source.1 = canonicalize candidate.pattern := by
  let candidate : ConstructorValue rhoCalc FreeTypeContext.empty [] pparRule :=
    .collection "ps" .hashBag TypeExpr.proc [canonicalize source.1] none rfl
      (.cons (canonical_source_typed source) (.nil _ _))
  refine ⟨candidate, decomposition_complete ?_ candidate rfl, ?_⟩
  · simp [isObjectPattern, isObjectPatternList, canonical_source_object source]
  · exact representatives_sound (source := source.1) (by simp [representatives, candidate,
      ConstructorValue.pattern])

/-- Whole-language constructor-image coverage, for every admitted process. -/
theorem values_complete (source : RhoProcess) (index : DeclarationIndex)
    (holds : Holds index source.1) :
    ∃ value ∈ values (completionBudget source.1) index source.1,
      canonicalize source.1 = canonicalize value.pattern := by
  obtain ⟨category, value, related⟩ := holds
  have member : declaration index ∈ rhoCalc.terms := List.getElem_mem index.isLt
  have covered :
      (∃ candidate ∈ decompositions rhoCalc FreeTypeContext.empty [] (declaration index)
        (canonicalize source.1), canonicalize source.1 = canonicalize candidate.pattern) ∨
      (∃ candidate ∈ decompositions rhoCalc FreeTypeContext.empty [] (declaration index)
        (.collection .hashBag [canonicalize source.1] none),
        canonicalize source.1 = canonicalize candidate.pattern) := by
    simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with zero | drop | quote | parallel | output | input
    · exact Or.inl (ordinary_coverage source (zero ▸ (by simp [rhoCalc])) category
        (by rw [zero]; simp [UsesBareCollection]) (by rw [zero]; decide) value related)
    · exact Or.inl (ordinary_coverage source (drop ▸ (by simp [rhoCalc])) category
        (by rw [drop]; simp [UsesBareCollection, TypeExpr.name, TypeExpr.baseType]) (by rw [drop]; decide) value related)
    · rw [quote] at category
      contradiction
    · have equal : declaration index = pparRule := parallel
      rw [equal]
      exact Or.inr (parallel_coverage source)
    · exact Or.inl (ordinary_coverage source (output ▸ (by simp [rhoCalc])) category
        (by rw [output]; simp [UsesBareCollection]) (by rw [output]; decide) value related)
    · exact Or.inl (ordinary_coverage source (input ▸ (by simp [rhoCalc])) category
        (by rw [input]; simp [UsesBareCollection]) (by rw [input]; decide) value related)
  rcases covered with ⟨candidate, listed, equal⟩ | ⟨candidate, listed, equal⟩
  · refine ⟨candidate, List.mem_flatMap.mpr ?_, equal⟩
    exact ⟨canonicalize source.1, by simp [completionBudget, representatives], listed⟩
  · refine ⟨candidate, List.mem_flatMap.mpr ?_, equal⟩
    exact ⟨.collection .hashBag [canonicalize source.1] none,
      by simp [completionBudget, representatives], listed⟩

theorem completed_exact (source : RhoProcess) (index : DeclarationIndex) :
    Holds index source.1 ↔
      (declaration index).category = "Proc" ∧
        ∃ value ∈ values (completionBudget source.1) index source.1,
          canonicalize source.1 = canonicalize value.pattern := by
  constructor
  · intro holds
    exact ⟨holds.1, values_complete source index holds⟩
  · rintro ⟨category, value, _, related⟩
    exact ⟨category, value, related⟩

theorem complete_at (source : Pattern) : closed (completionBudget source) source = true := by
  simp [closed, completionBudget]

theorem values_at_complete {budget : Nat} {source : Pattern}
    (complete : closed budget source = true) (index : DeclarationIndex) :
    values budget index source = values (completionBudget source) index source := by
  unfold values
  rw [List.take_of_length_le (of_decide_eq_true complete)]
  simp [completionBudget]

def readout (budget : Nat) (index : DeclarationIndex) (source : Pattern) : Bool :=
  ((declaration index).category == "Proc") && !(values budget index source).isEmpty

theorem readout_exact (source : RhoProcess) (index : DeclarationIndex) (budget : Nat)
    (complete : closed budget source.1 = true) :
    readout budget index source.1 = true ↔ Holds index source.1 := by
  simp only [readout, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨category, value, listed⟩
    exact ⟨category, value, values_sound listed⟩
  · intro holds
    obtain ⟨value, listed, _⟩ := values_complete source index holds
    rw [← values_at_complete complete index] at listed
    exact ⟨holds.1, value, listed⟩

theorem holds_equation_invariant (index : DeclarationIndex)
    {source target : rhoReflectiveGSLT.Term}
    (related : rhoReflectiveGSLT.Equiv source target) :
    Holds index source.1 ↔ Holds index target.1 := by
  have canonical := (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_equations_exact source target).mp related
  unfold Holds
  rw [canonical]

def evaluate (budget : Nat) (index : DeclarationIndex) (source : Pattern) : Option Bool :=
  if closed budget source then some (readout budget index source) else none

def test (index : DeclarationIndex) : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Test rhoReflectiveGSLT
    (fun source => Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source.1 = true) where
  predicate := ⟨fun source => Holds index source.1,
    fun {_ _} related => holds_equation_invariant index related⟩
  evaluate budget source := evaluate budget index source.1
  positive budget source read := by
    unfold evaluate at read
    split at read
    next complete =>
      exact (readout_exact (presentedRhoProcessEquiv source) index budget complete).mp
        (Option.some.inj read)
    next => cases read
  negative budget source read := by
    unfold evaluate at read
    split at read
    next complete =>
      intro holds
      have positive := (readout_exact (presentedRhoProcessEquiv source) index budget complete).mpr holds
      change readout budget index source.1 = true at positive
      have negative := Option.some.inj read
      rw [positive] at negative
      cases negative
    next => cases read
  completionBudget source := completionBudget source.1
  complete_at source _ := ⟨readout (completionBudget source.1) index source.1,
    by simp [evaluate, complete_at]⟩
  complete_above source _ budget enough :=
    ⟨readout budget index source.1, by
      have completed : closed budget source.1 = true := decide_eq_true enough
      simp [evaluate, completed]⟩

#print axioms values_complete
#print axioms completed_exact
#print axioms readout_exact
#print axioms test

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Structural
