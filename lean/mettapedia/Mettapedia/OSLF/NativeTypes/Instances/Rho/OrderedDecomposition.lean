import Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations
import Mettapedia.OSLF.NativeTypes.Instances.Local.Structural
import Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition

open Mettapedia.OSLF.Framework

/-!
# Complete ordered constructor fibres for the original rho object carrier

The algorithm returns actual typed constructor introductions. Ordinary heads
preserve their ordered argument classes. Parallel introductions retain the
collection-valued argument. Quotation has both process-body origins required
by QuoteDrop; a visible body alone does not cover its fibre.

Only object introductions enter the independent image. Pending schema
substitution nodes and open collection tails are not terms of this carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.OSLF.NativeTypes.Structural
open Mettapedia.OSLF.NativeTypes.Instances.Local.Structural
open Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations

abbrev Value (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule) :=
  {value : ConstructorValue rhoCalc free bound rule // isObjectPattern value.pattern = true}

def objectDecompositions (free : FreeTypeContext) (bound : List TypeExpr)
    (rule : GrammarRule) (term : Pattern) : List (Value free bound rule) :=
  if object : isObjectPattern term = true then
    match inspect rhoCalc free bound rule term with
    | none => []
    | some value => [⟨value.val, by rw [value.property]; exact object⟩]
  else []

theorem object_decomposition_sound {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {term : Pattern} {value : Value free bound rule}
    (listed : value ∈ objectDecompositions free bound rule term) : value.val.pattern = term := by
  unfold objectDecompositions at listed
  split at listed
  · cases found : inspect rhoCalc free bound rule term with
    | none => simp [found] at listed
    | some result =>
      simp only [found, List.mem_singleton] at listed
      cases listed
      exact result.property
  · contradiction

theorem object_decomposition_complete (free : FreeTypeContext) (bound : List TypeExpr)
    (rule : GrammarRule) (value : Value free bound rule) {term : Pattern}
    (same : value.val.pattern = term) : value ∈ objectDecompositions free bound rule term := by
  subst term
  simp [objectDecompositions, value.property,
    inspect_complete rhoCalc free bound rule value.val value.property]

def representatives (source : Pattern) : List Pattern :=
  [canonicalize source, .collection .hashBag [canonicalize source] none,
    .apply "NQuote" [.apply "PDrop" [canonicalize source]]]

def values (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (budget : Nat) (source : Pattern) : List (Value free bound rule) :=
  ((representatives source).take budget).flatMap (objectDecompositions free bound rule)

def closed (budget : Nat) (source : Pattern) : Bool :=
  decide ((representatives source).length ≤ budget)

def completionBudget (source : Pattern) : Nat := (representatives source).length

theorem canonical_arguments (arguments : List Pattern) :
    List.Forall₂ canonicalEquations.r arguments (canonicalizeList arguments) := by
  induction arguments with
  | nil => exact .nil
  | cons first rest ih => exact .cons (canonicalize_idempotent first).symm ih

theorem representatives_sound {source representative : Pattern}
    (listed : representative ∈ representatives source) :
    canonicalize source = canonicalize representative := by
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact (canonicalize_idempotent source).symm
  · rw [canonicalize_parallel_singleton, canonicalize_idempotent]
  · change canonicalize source = normalizeQuote
      (.apply "PDrop" [canonicalize (canonicalize source)])
    rw [canonicalize_idempotent]
    rfl

theorem values_sound {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    {budget : Nat} {source : Pattern} {value : Value free bound rule}
    (listed : value ∈ values free bound rule budget source) :
    canonicalEquations.r source value.val.pattern := by
  obtain ⟨representative, represented, decoded⟩ := List.mem_flatMap.mp listed
  rw [object_decomposition_sound decoded]
  exact representatives_sound (List.mem_of_mem_take represented)

private theorem typed_arguments {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} (member : rule ∈ rhoCalc.terms) {arguments : List Pattern}
    (typed : HasType rhoCalc free bound (.apply rule.label arguments) (.base rule.category)) :
    ArgumentsHaveTypes rhoCalc free bound arguments rule.params := by
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
      cases shape.2
      exact argumentsTyped

private theorem ordinary_coverage {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} (member : rule ∈ rhoCalc.terms) (category : rule.category = "Proc")
    (ordinary : ¬ UsesBareCollection rule) (notQuote : rule.label ≠ "NQuote")
    (value : Value free bound rule) {source : Pattern}
    (related : canonicalize source = canonicalize value.val.pattern) :
    ∃ candidate ∈ objectDecompositions free bound rule (canonicalize source),
      List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments := by
  rcases value with ⟨value, object⟩
  cases value with
  | ordinary arguments _ argumentsTyped =>
      have typed : HasSort rhoCalc free bound (.apply rule.label arguments) "Proc" := by
        rw [← category]
        exact .constructor member ordinary argumentsTyped
      have converted := canonicalize_proc_hasSort typed object
      have shape : canonicalize source = .apply rule.label (canonicalizeList arguments) := by
        rw [related, ConstructorValue.pattern,
          canonicalize_apply_general rule.label arguments (fun quoted => notQuote quoted.1)]
      have convertedArguments :
          ArgumentsHaveTypes rhoCalc free bound (canonicalizeList arguments) rule.params := by
        apply typed_arguments member
        rw [category]
        simpa only [canonicalize_apply_general rule.label arguments
          (fun quoted => notQuote quoted.1)] using converted
      let candidate : Value free bound rule :=
        ⟨.ordinary (canonicalizeList arguments) ordinary convertedArguments,
          by
            change isObjectPattern (.apply rule.label (canonicalizeList arguments)) = true
            rw [← shape, related]
            exact canonicalize_isObjectPattern object⟩
      refine ⟨candidate, object_decomposition_complete free bound rule candidate shape.symm, ?_⟩
      change List.Forall₂ canonicalEquations.r arguments (canonicalizeList arguments)
      exact canonical_arguments arguments
  | collection name kind elementType elements rest shape _ =>
      exact False.elim (ordinary ⟨name, kind, elementType, shape⟩)

private theorem parallel_coverage {free : FreeTypeContext} {bound : List TypeExpr}
    (value : Value free bound pparRule) {source : Pattern}
    (related : canonicalize source = canonicalize value.val.pattern) :
    ∃ candidate ∈ objectDecompositions free bound pparRule
      (.collection .hashBag [canonicalize source] none),
      List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments := by
  have typed := value.val.typed pparRule_mem
  have converted := canonicalize_proc_hasSort typed value.property
  have convertedSource : HasSort rhoCalc free bound (canonicalize source) "Proc" := by
    rw [related]
    exact converted
  have sourceObject : isObjectPattern (canonicalize source) = true := by
    rw [related]
    exact canonicalize_isObjectPattern value.property
  let candidate : Value free bound pparRule :=
    ⟨.collection "ps" .hashBag TypeExpr.proc [canonicalize source] none rfl
      (.cons convertedSource (.nil _ _)), by
        simp [ConstructorValue.pattern, isObjectPattern, isObjectPatternList, sourceObject]⟩
  refine ⟨candidate, object_decomposition_complete free bound pparRule candidate rfl, ?_⟩
  rcases value with ⟨value, object⟩
  cases value with
  | ordinary arguments notBare _ => exact False.elim (notBare ⟨"ps", .hashBag, TypeExpr.proc, rfl⟩)
  | collection name kind elem elements rest shape typed =>
      have params := List.cons.inj shape
      have parameter := TermParam.simple.inj params.1
      have types := TypeExpr.collection.inj parameter.2
      cases types.1
      cases types.2
      change List.Forall₂ canonicalEquations.r [.collection .hashBag elements rest]
        [.collection .hashBag [canonicalize source] none]
      refine .cons ?_ .nil
      change canonicalize (.collection .hashBag elements rest) =
        canonicalize (.collection .hashBag [canonicalize source] none)
      rw [canonicalize_parallel_singleton, canonicalize_idempotent]
      exact related.symm

def quoteRule : GrammarRule := rhoCalc.terms[2]

theorem quote_rule_mem : quoteRule ∈ rhoCalc.terms := List.getElem_mem (by decide)

/-- The two alternatives are process-body classes, rather than two identical
quotation answers. The drop alternative can differ from the visible body. -/
theorem quotation_fibre_cases {source body : Pattern}
    (related : canonicalize source = canonicalize (.apply "NQuote" [body])) :
    canonicalize body = .apply "PDrop" [canonicalize source] ∨
      canonicalize source = .apply "NQuote" [canonicalize body] := by
  change canonicalize source = normalizeQuote (canonicalize body) at related
  by_cases isDrop : ∃ name, canonicalize body = .apply "PDrop" [name]
  · obtain ⟨name, shape⟩ := isDrop
    have sourceShape : canonicalize source = name := by
      simpa only [shape, normalizeQuote] using related
    exact Or.inl (shape.trans (congrArg (fun n => Pattern.apply "PDrop" [n]) sourceShape.symm))
  · have kept : normalizeQuote (canonicalize body) = .apply "NQuote" [canonicalize body] := by
      unfold normalizeQuote
      split
      · rename_i name shape
        exact False.elim (isDrop ⟨name, shape⟩)
      · rfl
    exact Or.inr (related.trans kept)

private theorem quotation_coverage {free : FreeTypeContext} {bound : List TypeExpr}
    (value : Value free bound quoteRule) {source : Pattern}
    (related : canonicalize source = canonicalize value.val.pattern) :
    (∃ candidate ∈ objectDecompositions free bound quoteRule (canonicalize source),
      List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments) ∨
    (∃ candidate ∈ objectDecompositions free bound quoteRule
      (.apply "NQuote" [.apply "PDrop" [canonicalize source]]),
      List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments) := by
  rcases value with ⟨value, object⟩
  cases value with
  | collection name kind elementType elements rest shape typed =>
      change [TermParam.simple "p" TypeExpr.proc] =
        [TermParam.simple name (.collection kind elementType)] at shape
      have parameter := TermParam.simple.inj (List.cons.inj shape).1
      cases parameter.2
  | ordinary arguments ordinary typed =>
      change ArgumentsHaveTypes rhoCalc free bound arguments [.simple "p" TypeExpr.proc] at typed
      cases typed with
      | @cons _ body tail param params expected representation parameterType bodyTyped tailTyped =>
        cases tailTyped
        have expectedEq : expected = TypeExpr.proc := by
          simpa [parameterType?] using parameterType.symm
        subst expected
        change isObjectPatternList [body] = true at object
        have bodyObject : isObjectPattern body = true := by simpa [isObjectPatternList] using object
        have bodyConverted := canonicalize_proc_hasSort bodyTyped bodyObject
        have bodyConvertedObject := canonicalize_isObjectPattern bodyObject
        change canonicalize source = canonicalize (.apply "NQuote" [body]) at related
        rcases quotation_fibre_cases related with dropped | visible
        · have sourceTyped : HasSort rhoCalc free bound (canonicalize source) "Name" := by
            rw [related]
            exact canonicalize_name_hasSort (rho_quote_hasSort bodyTyped)
              (by simpa [isObjectPattern, isObjectPatternList] using bodyObject)
          have sourceObject : isObjectPattern (canonicalize source) = true := by
            rw [related]
            exact canonicalize_isObjectPattern
              (by simpa [isObjectPattern, isObjectPatternList] using bodyObject)
          have dropTyped := rho_drop_hasSort sourceTyped
          let candidate : Value free bound quoteRule :=
            ⟨.ordinary [.apply "PDrop" [canonicalize source]] ordinary
              (.cons trivial rfl dropTyped .nil), by
                simp [ConstructorValue.pattern, quoteRule, isObjectPattern, isObjectPatternList, sourceObject]⟩
          refine Or.inr ⟨candidate, object_decomposition_complete free bound quoteRule candidate rfl, ?_⟩
          change List.Forall₂ canonicalEquations.r [body] [.apply "PDrop" [canonicalize source]]
          refine .cons ?_ .nil
          change canonicalize body = canonicalize (.apply "PDrop" [canonicalize source])
          change canonicalize body = .apply "PDrop" [canonicalize (canonicalize source)]
          rw [canonicalize_idempotent]
          exact dropped
        · let candidate : Value free bound quoteRule :=
            ⟨.ordinary [canonicalize body] ordinary (.cons trivial rfl bodyConverted .nil), by
                simp [ConstructorValue.pattern, quoteRule, isObjectPattern, isObjectPatternList,
                  bodyConvertedObject]⟩
          refine Or.inl ⟨candidate, object_decomposition_complete free bound quoteRule candidate visible.symm, ?_⟩
          exact .cons (canonicalize_idempotent body).symm .nil

/-- Every object introduction in the authored signature has a listed
introduction preserving the complete ordered argument classes. This includes
all ambient typing contexts and both quotation origins. -/
theorem values_ordered_complete (free : FreeTypeContext) (bound : List TypeExpr)
    (rule : GrammarRule) (member : rule ∈ rhoCalc.terms) (source : Pattern)
    (value : Value free bound rule)
    (related : canonicalEquations.r source value.val.pattern) :
    ∃ candidate ∈ values free bound rule (completionBudget source) source,
      List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments := by
  have covered :
      (∃ candidate ∈ objectDecompositions free bound rule (canonicalize source),
        List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments) ∨
      (∃ candidate ∈ objectDecompositions free bound rule
        (.collection .hashBag [canonicalize source] none),
        List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments) ∨
      (∃ candidate ∈ objectDecompositions free bound rule
        (.apply "NQuote" [.apply "PDrop" [canonicalize source]]),
        List.Forall₂ canonicalEquations.r value.val.arguments candidate.val.arguments) := by
    simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with zero | drop | quote | parallel | output | input
    · exact Or.inl (ordinary_coverage (zero ▸ (by simp [rhoCalc]))
        (by rw [zero]) (by rw [zero]; simp [UsesBareCollection])
        (by rw [zero]; decide) value related)
    · exact Or.inl (ordinary_coverage (drop ▸ (by simp [rhoCalc]))
        (by rw [drop]) (by rw [drop]; simp [UsesBareCollection, TypeExpr.name, TypeExpr.baseType])
        (by rw [drop]; decide) value related)
    · have same : rule = quoteRule := quote
      subst rule
      rcases quotation_coverage value related with visible | dropped
      · exact Or.inl visible
      · exact Or.inr (Or.inr dropped)
    · have same : rule = pparRule := parallel
      subst rule
      exact Or.inr (Or.inl (parallel_coverage value related))
    · exact Or.inl (ordinary_coverage (output ▸ (by simp [rhoCalc]))
        (by rw [output]) (by rw [output]; simp [UsesBareCollection])
        (by rw [output]; decide) value related)
    · exact Or.inl (ordinary_coverage (input ▸ (by simp [rhoCalc]))
        (by rw [input]) (by rw [input]; simp [UsesBareCollection])
        (by rw [input]; decide) value related)
  rcases covered with ⟨candidate, listed, ordered⟩ |
    ⟨candidate, listed, ordered⟩ | ⟨candidate, listed, ordered⟩
  · exact ⟨candidate, List.mem_flatMap.mpr ⟨canonicalize source,
      by simp [completionBudget, representatives], listed⟩, ordered⟩
  · exact ⟨candidate, List.mem_flatMap.mpr ⟨.collection .hashBag [canonicalize source] none,
      by simp [completionBudget, representatives], listed⟩, ordered⟩
  · exact ⟨candidate, List.mem_flatMap.mpr ⟨.apply "NQuote" [.apply "PDrop" [canonicalize source]],
      by simp [completionBudget, representatives], listed⟩, ordered⟩

def inputEquations (rule : GrammarRule) (position : Fin rule.params.length) : Setoid Pattern :=
  if parameterType? rule.params[position.val] = some (TypeExpr.bag TypeExpr.proc) then
    bagEquations else canonicalEquations

theorem input_equations_of_canonical (rule : GrammarRule) (position : Fin rule.params.length)
    {first second : Pattern} (related : canonicalEquations.r first second) :
    (inputEquations rule position).r first second := by
  by_cases bag : parameterType? rule.params[position.val] = some (TypeExpr.bag TypeExpr.proc)
  · have selected : inputEquations rule position = bagEquations := by simp [inputEquations, bag]
    rw [selected]
    exact (bag_argument_eq_iff first second).mpr related
  · have selected : inputEquations rule position = canonicalEquations := by simp [inputEquations, bag]
    rw [selected]
    exact related

theorem input_equations_iff_canonical (rule : GrammarRule) (position : Fin rule.params.length)
    (first second : Pattern) :
    (inputEquations rule position).r first second ↔ canonicalEquations.r first second := by
  constructor
  · intro related
    by_cases bag : parameterType? rule.params[position.val] = some (TypeExpr.bag TypeExpr.proc)
    · have selected : inputEquations rule position = bagEquations := by simp [inputEquations, bag]
      rw [selected] at related
      exact (bag_argument_eq_iff first second).mp related
    · have selected : inputEquations rule position = canonicalEquations := by simp [inputEquations, bag]
      rw [selected] at related
      exact related
  · exact input_equations_of_canonical rule position

def argument {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    (value : Value free bound rule) (position : Fin rule.params.length) : Pattern :=
  value.val.arguments[position.val]'(by rw [value.val.arguments_length]; exact position.isLt)

theorem ordered_arguments {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    {first second : Value free bound rule}
    (related : List.Forall₂ canonicalEquations.r first.val.arguments second.val.arguments)
    (position : Fin rule.params.length) :
    (inputEquations rule position).r (argument first position) (argument second position) := by
  apply input_equations_of_canonical rule position
  exact related.get (by rw [first.val.arguments_length]; exact position.isLt)
    (by rw [second.val.arguments_length]; exact position.isLt)

theorem values_stable (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (source : Pattern) (budget : Nat) (enough : completionBudget source ≤ budget) :
    values free bound rule budget source = values free bound rule (completionBudget source) source := by
  unfold values completionBudget at *
  rw [List.take_of_length_le enough, List.take_of_length_le (Nat.le_refl _)]

theorem complete_at (source : Pattern) : closed (completionBudget source) source = true := by
  simp [closed, completionBudget]

theorem closed_stable (source : Pattern) (budget : Nat) (enough : completionBudget source ≤ budget) :
    closed budget source = closed (completionBudget source) source := by
  rw [complete_at]
  exact decide_eq_true enough

def backend (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (member : rule ∈ rhoCalc.terms) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.Backend (Value free bound rule) rule.params.length
      (fun value => value.val.pattern) argument canonicalEquations (inputEquations rule)
      (fun source => isObjectPattern source = true) where
  values := values free bound rule
  closed := closed
  sound := fun _ _ _ listed => values_sound listed
  ordered_coverage budget source completed value related := by
    obtain ⟨candidate, listed, ordered⟩ := values_ordered_complete free bound rule member source value related
    refine ⟨candidate, ?_, ordered_arguments ordered⟩
    rw [values_stable free bound rule source budget (of_decide_eq_true completed)]
    exact listed
  completionBudget := completionBudget
  complete_at source _ := complete_at source
  values_stable := values_stable free bound rule
  closed_stable := closed_stable

#print axioms ordinary_coverage
#print axioms parallel_coverage
#print axioms quotation_coverage
#print axioms values_ordered_complete
#print axioms backend

end Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition
