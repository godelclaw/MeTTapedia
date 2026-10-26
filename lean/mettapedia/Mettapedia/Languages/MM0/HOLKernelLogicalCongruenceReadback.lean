import Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
/-!
# Readback of the seven native logical-congruence constructors

Each actual constructor expands to the declared logical function, applies
checked native congruence, and folds the stored definition back. Independent
admission is preserved by reconstructing those function values and composing
their explicit source beta reductions with the native conversion witnesses.
Quantified congruence retains each native binder name and its extended source
frame. No equality between the source bodies is assumed beyond the admitted
input equality receipt.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback
open HOLKernelRuleInstances HOLKernelProofReadback
open HOLKernelStructuralRules (CheckedProof)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}
variable (signature : Signature sorts terms)
variable (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
variable (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
variable (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
variable (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
local notation "R" => HOLKernelLogicalFunctionReadback.reader profile constants parameters
local notation "expand" => expandEquivalence signature.symbol abbreviation.reference
include distinct

theorem conjunction_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) second second'))))
    (g : Judgment Const gamma) (p p' q q' : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (firstRead' : R names (expand first') = some ⟨.prop, p'⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (secondRead' : R names (expand second') = some ⟨.prop, q'⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFirst fuelSecond : Nat}
    (firstAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFirst names
  firstEquality.val (.imp g.formula (.eq p p')))
    (secondAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSecond names
  secondEquality.val (.imp g.formula (.eq q q'))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.conjunctionCongruence signature profile rules binding antecedent first first' second second'
        antecedentSorted firstSorted firstSorted' secondSorted secondSorted' firstEquality secondEquality).val
      (.imp g.formula (.eq (.and p q) (.and p' q')))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .conjunction)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .conjunction)
  let F : Term Const gamma (.prop ⇒ .prop ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .conjunction .prop).term
  have operationRead : R names (expand (.term (profile.reference .conjunction))) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_nullary profile constants parameters names .conjunction (by simp)
  let constantTyping := HOLKernelLogicalOperationProofs.conjunctionTyping (hypotheses := []) signature profile antecedent antecedentSorted
  let expanded := HOLKernelCongruence.binaryApplication signature rules binding antecedent
    (HOLKernelTypingRules.boolType signature.symbol) (HOLKernelTypingRules.boolType signature.symbol)
    (HOLKernelTypingRules.boolType signature.symbol) (.term (profile.reference .conjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  obtain ⟨fuel, ⟨expandedAdmitted⟩⟩ := binaryApplication_admitted signature abbreviation profile distinct constants parameters
    rules binding names antecedent _ _ _ (.term (profile.reference .conjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted firstSorted firstSorted' secondSorted secondSorted'
    constantTyping firstEquality secondEquality g F p p' q q' contextRead boolRead boolRead boolRead operationRead
    firstRead firstRead' secondRead secondRead' ruleAt bindingAt selected firstAdmitted secondAdmitted
  have nativeRead (one two : Preterm) (a b : Formula Const gamma)
      (oneRead : R names (expand one) = some ⟨.prop, a⟩)
      (twoRead : R names (expand two) = some ⟨.prop, b⟩) :
      R names (expand (applySymbol signature.symbol .andc [one, two])) = some ⟨.prop, .and a b⟩ := by
    have decoded := readTermWith_and (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand one) (expand two) a b oneRead twoRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .andc)] using decoded
  let left := HOLKernelLogicalOperationProofs.conjunctionUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.conjunctionUnfolding signature profile first' second' firstSorted' secondSorted'
  refine ⟨fuel + 1, ?_⟩
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app (.app F p) q) (.and p q) (.app (.app F p') q') (.and p' q') contextRead boolRead
    (nativeRead first second p q firstRead secondRead)
    (nativeRead first' second' p' q' firstRead' secondRead')
    (HOLKernelLogicalFunctionReadback.conjunction_reduces p q)
    (HOLKernelLogicalFunctionReadback.conjunction_reduces p' q') ruleAt bindingAt expandedAdmitted

theorem disjunction_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) second second'))))
    (g : Judgment Const gamma) (p p' q q' : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (firstRead' : R names (expand first') = some ⟨.prop, p'⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (secondRead' : R names (expand second') = some ⟨.prop, q'⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFirst fuelSecond : Nat}
    (firstAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFirst names
  firstEquality.val (.imp g.formula (.eq p p')))
    (secondAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSecond names
  secondEquality.val (.imp g.formula (.eq q q'))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.disjunctionCongruence signature profile rules binding antecedent first first' second second'
        antecedentSorted firstSorted firstSorted' secondSorted secondSorted' firstEquality secondEquality).val
      (.imp g.formula (.eq (.or p q) (.or p' q')))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .disjunction)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .disjunction)
  let F : Term Const gamma (.prop ⇒ .prop ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .disjunction .prop).term
  have operationRead : R names (expand (.term (profile.reference .disjunction))) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_nullary profile constants parameters names .disjunction (by simp)
  let constantTyping := HOLKernelLogicalOperationProofs.disjunctionTyping (hypotheses := []) signature profile antecedent antecedentSorted
  let expanded := HOLKernelCongruence.binaryApplication signature rules binding antecedent
    (HOLKernelTypingRules.boolType signature.symbol) (HOLKernelTypingRules.boolType signature.symbol)
    (HOLKernelTypingRules.boolType signature.symbol) (.term (profile.reference .disjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  obtain ⟨fuel, ⟨expandedAdmitted⟩⟩ := binaryApplication_admitted signature abbreviation profile distinct constants parameters
    rules binding names antecedent _ _ _ (.term (profile.reference .disjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted firstSorted firstSorted' secondSorted secondSorted'
    constantTyping firstEquality secondEquality g F p p' q q' contextRead boolRead boolRead boolRead operationRead
    firstRead firstRead' secondRead secondRead' ruleAt bindingAt selected firstAdmitted secondAdmitted
  have nativeRead (one two : Preterm) (a b : Formula Const gamma)
      (oneRead : R names (expand one) = some ⟨.prop, a⟩)
      (twoRead : R names (expand two) = some ⟨.prop, b⟩) :
      R names (expand (applySymbol signature.symbol .orc [one, two])) = some ⟨.prop, .or a b⟩ := by
    have decoded := readTermWith_or (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand one) (expand two) a b oneRead twoRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .orc)] using decoded
  let left := HOLKernelLogicalOperationProofs.disjunctionUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.disjunctionUnfolding signature profile first' second' firstSorted' secondSorted'
  refine ⟨fuel + 1, ?_⟩
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app (.app F p) q) (.or p q) (.app (.app F p') q') (.or p' q') contextRead boolRead
    (nativeRead first second p q firstRead secondRead)
    (nativeRead first' second' p' q' firstRead' secondRead')
    (HOLKernelLogicalFunctionReadback.disjunction_reduces p q)
    (HOLKernelLogicalFunctionReadback.disjunction_reduces p' q') ruleAt bindingAt expandedAdmitted

theorem implication_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) second second'))))
    (g : Judgment Const gamma) (p p' q q' : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (firstRead' : R names (expand first') = some ⟨.prop, p'⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (secondRead' : R names (expand second') = some ⟨.prop, q'⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFirst fuelSecond : Nat}
    (firstAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFirst names
  firstEquality.val (.imp g.formula (.eq p p')))
    (secondAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSecond names
  secondEquality.val (.imp g.formula (.eq q q'))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.implicationCongruence signature profile rules binding antecedent first first' second second'
        antecedentSorted firstSorted firstSorted' secondSorted secondSorted' firstEquality secondEquality).val
      (.imp g.formula (.eq (.imp p q) (.imp p' q')))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .implication)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .implication)
  let F : Term Const gamma (.prop ⇒ .prop ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .implication .prop).term
  have operationRead : R names (expand (.term (profile.reference .implication))) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_nullary profile constants parameters names .implication (by simp)
  let constantTyping := HOLKernelLogicalOperationProofs.implicationTyping (hypotheses := []) signature profile antecedent antecedentSorted
  let expanded := HOLKernelCongruence.binaryApplication signature rules binding antecedent
    (HOLKernelTypingRules.boolType signature.symbol) (HOLKernelTypingRules.boolType signature.symbol)
    (HOLKernelTypingRules.boolType signature.symbol) (.term (profile.reference .implication)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  obtain ⟨fuel, ⟨expandedAdmitted⟩⟩ := binaryApplication_admitted signature abbreviation profile distinct constants parameters
    rules binding names antecedent _ _ _ (.term (profile.reference .implication)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted firstSorted firstSorted' secondSorted secondSorted'
    constantTyping firstEquality secondEquality g F p p' q q' contextRead boolRead boolRead boolRead operationRead
    firstRead firstRead' secondRead secondRead' ruleAt bindingAt selected firstAdmitted secondAdmitted
  have nativeRead (one two : Preterm) (a b : Formula Const gamma)
      (oneRead : R names (expand one) = some ⟨.prop, a⟩)
      (twoRead : R names (expand two) = some ⟨.prop, b⟩) :
      R names (expand (applySymbol signature.symbol .impc [one, two])) = some ⟨.prop, .imp a b⟩ := by
    have decoded := readTermWith_imp (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand one) (expand two) a b oneRead twoRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .impc)] using decoded
  let left := HOLKernelLogicalOperationProofs.implicationUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.implicationUnfolding signature profile first' second' firstSorted' secondSorted'
  refine ⟨fuel + 1, ?_⟩
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app (.app F p) q) (.imp p q) (.app (.app F p') q') (.imp p' q') contextRead boolRead
    (nativeRead first second p q firstRead secondRead)
    (nativeRead first' second' p' q' firstRead' secondRead')
    (HOLKernelLogicalFunctionReadback.implication_reduces p q)
    (HOLKernelLogicalFunctionReadback.implication_reduces p' q') ruleAt bindingAt expandedAdmitted


theorem equality_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol typeCode first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
  (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol
    (HOLKernelInferenceRules.equality signature.symbol typeCode second second'))))
    (g : Judgment Const gamma) {domain : Ty Unit} (p p' q q' : Term Const gamma domain)
    (typeRead : readType signature.symbol (expand typeCode) = some domain)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨domain, p⟩)
    (firstRead' : R names (expand first') = some ⟨domain, p'⟩)
    (secondRead : R names (expand second) = some ⟨domain, q⟩)
    (secondRead' : R names (expand second') = some ⟨domain, q'⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFirst fuelSecond : Nat}
    (firstAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFirst names
  firstEquality.val (.imp g.formula (.eq p p')))
    (secondAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSecond names
  secondEquality.val (.imp g.formula (.eq q q'))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.equalityCongruence signature profile rules binding antecedent typeCode first first' second second'
        antecedentSorted typeSorted firstSorted firstSorted' secondSorted secondSorted' firstEquality secondEquality).val
      (.imp g.formula (.eq (.eq p q) (.eq p' q')))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have operationSorted : Preterm.HasType terms context (.app (.term (profile.reference .equality)) typeCode) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .equality)) typeSorted
  let F : Term Const gamma (domain ⇒ domain ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .equality domain).term
  have operationRead : R names (expand (.app (.term (profile.reference .equality)) typeCode)) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_parameterized profile constants parameters names .equality (by simp)
        (expand typeCode) domain typeRead
  let constantTyping := HOLKernelLogicalOperationProofs.equalityTyping (hypotheses := []) signature profile antecedent typeCode antecedentSorted typeSorted
  let expanded := HOLKernelCongruence.binaryApplication signature rules binding antecedent typeCode typeCode
    (HOLKernelTypingRules.boolType signature.symbol) (.app (.term (profile.reference .equality)) typeCode) first first' second second'
    antecedentSorted typeSorted typeSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  obtain ⟨fuel, ⟨expandedAdmitted⟩⟩ := binaryApplication_admitted signature abbreviation profile distinct constants parameters
    rules binding names antecedent typeCode typeCode _ (.app (.term (profile.reference .equality)) typeCode) first first' second second'
    antecedentSorted typeSorted typeSorted boolSorted operationSorted firstSorted firstSorted' secondSorted secondSorted'
    constantTyping firstEquality secondEquality g F p p' q q' contextRead typeRead typeRead boolRead operationRead
    firstRead firstRead' secondRead secondRead' ruleAt bindingAt selected firstAdmitted secondAdmitted
  have nativeRead (one two : Preterm) (a b : Term Const gamma domain)
      (oneRead : R names (expand one) = some ⟨domain, a⟩)
      (twoRead : R names (expand two) = some ⟨domain, b⟩) :
      R names (expand (applySymbol signature.symbol .eqc [typeCode, one, two])) = some ⟨.prop, .eq a b⟩ := by
    have decoded := readTermWith_equality (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand typeCode) (expand one) (expand two)
      domain a b typeRead oneRead twoRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .eqc)] using decoded
  let left := HOLKernelLogicalOperationProofs.equalityUnfolding signature profile typeCode first second typeSorted firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.equalityUnfolding signature profile typeCode first' second' typeSorted firstSorted' secondSorted'
  refine ⟨fuel + 1, ?_⟩
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app (.app F p) q) (.eq p q) (.app (.app F p') q') (.eq p' q') contextRead boolRead
    (nativeRead first second p q firstRead secondRead)
    (nativeRead first' second' p' q' firstRead' secondRead')
    (HOLKernelLogicalFunctionReadback.equality_reduces p q)
    (HOLKernelLogicalFunctionReadback.equality_reduces p' q') ruleAt bindingAt expandedAdmitted

theorem negation_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) first second))))
    (g : Judgment Const gamma) (p q : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .applicationArgument) = some (.inference .applicationArgument))
    {fuel : Nat}
    (equalAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      equal.val (.imp g.formula (.eq p q))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max 1 fuel + 2) names
      (HOLKernelCongruence.negationCongruence signature profile rules antecedent first second
        antecedentSorted firstSorted secondSorted equal).val (.imp g.formula (.eq (.not p) (.not q)))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .negation)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .negation)
  let F : Term Const gamma (.prop ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .negation .prop).term
  have operationRead : R names (expand (.term (profile.reference .negation))) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_nullary profile constants parameters names .negation (by simp)
  let constantTyping := HOLKernelLogicalOperationProofs.negationTyping (hypotheses := []) signature profile antecedent antecedentSorted
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (HOLKernelTypingRules.boolType signature.symbol) (HOLKernelTypingRules.boolType signature.symbol) antecedent first second
    (.term (profile.reference .negation)) boolSorted boolSorted antecedentSorted firstSorted secondSorted operationSorted constantTyping equal
  obtain ⟨expandedAdmitted⟩ := applicationArgument_admitted signature abbreviation profile distinct constants parameters rules names
    _ _ antecedent first second (.term (profile.reference .negation)) boolSorted boolSorted antecedentSorted firstSorted secondSorted
    operationSorted constantTyping equal g p q F contextRead boolRead boolRead firstRead secondRead operationRead ruleAt bindingAt selected equalAdmitted
  have nativeRead (native : Preterm) (body : Formula Const gamma)
      (bodyRead : R names (expand native) = some ⟨.prop, body⟩) :
      R names (expand (applySymbol signature.symbol .notc [native])) = some ⟨.prop, .not body⟩ := by
    have decoded := readTermWith_not (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand native) body bodyRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs, expandEquivalence] using decoded
  let left := HOLKernelLogicalOperationProofs.negationUnfolding signature profile first firstSorted
  let right := HOLKernelLogicalOperationProofs.negationUnfolding signature profile second secondSorted
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app F p) (.not p) (.app F q) (.not q) contextRead boolRead
    (nativeRead first p firstRead) (nativeRead second q secondRead)
    (HOLKernelLogicalFunctionReadback.negation_reduces p)
    (HOLKernelLogicalFunctionReadback.negation_reduces q) ruleAt bindingAt expandedAdmitted

open NamedElaboration (BinderNames)

theorem universal_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode first second : Preterm) (firstName secondName : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstDeclared : context[firstName]? = some (.bound signature.ids.object))
    (secondDeclared : context[secondName]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol
          (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))
          (applySymbol signature.symbol .lam [.var firstName, typeCode, first])
          (applySymbol signature.symbol .lam [.var secondName, typeCode, second])))))
    (g : Judgment Const gamma) {domain : Ty Unit} (p q : Formula Const (domain :: gamma))
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some domain)
    (firstBeyond : parameters ≤ firstName) (secondBeyond : parameters ≤ secondName)
    (firstRead : R (BinderNames.cons (type := domain) firstName names) (expand first) = some ⟨.prop, p⟩)
    (secondRead : R (BinderNames.cons (type := domain) secondName names) (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .applicationArgument) = some (.inference .applicationArgument))
    {fuel : Nat}
    (equalAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      equal.val (.imp g.formula (.eq (.lam p) (.lam q)))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max 1 fuel + 2) names
      (HOLKernelCongruence.universalCongruence signature profile rules antecedent typeCode first second firstName secondName
        antecedentSorted typeSorted firstDeclared secondDeclared firstSorted secondSorted equal).val
      (.imp g.formula (.eq (.all p) (.all q)))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have predicateSorted := signature.application context .function [typeCode, HOLKernelTypingRules.boolType signature.symbol]
    (.cons (.regular typeSorted) (.cons (.regular boolSorted) .nil))
  have predicateRead : readType signature.symbol
      (expand (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))) =
      some (domain ⇒ .prop) := by
    simp [HOLKernelTypingRules.functionType, HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs,
      expandEquivalence, distinct, readType, readHead_reference signature.symbol signature.symbol_injective, typeRead]
  have operationSorted : Preterm.HasType terms context (.app (.term (profile.reference .universal)) typeCode) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .universal)) typeSorted
  let F : Term Const gamma ((domain ⇒ .prop) ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .universal domain).term
  have operationRead : R names (expand (.app (.term (profile.reference .universal)) typeCode)) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_parameterized profile constants parameters names .universal (by simp)
        (expand typeCode) domain typeRead
  have lamRead (name : Nat) (native : Preterm) (body : Formula Const (domain :: gamma))
      (beyond : parameters ≤ name)
      (bodyRead : R (BinderNames.cons (type := domain) name names) (expand native) = some ⟨.prop, body⟩) :
      R names (expand (applySymbol signature.symbol .lam [.var name, typeCode, native])) = some ⟨domain ⇒ .prop, .lam body⟩ := by
    have decoded := readTermWith_lambda (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand typeCode) (expand native)
      domain .prop name body beyond typeRead bodyRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .lam)] using decoded
  let constantTyping := HOLKernelLogicalOperationProofs.universalTyping (hypotheses := []) signature profile antecedent typeCode antecedentSorted typeSorted
  have firstLamSorted := signature.application context .lam _ (.cons (.bound firstDeclared)
    (.cons (.regular typeSorted) (.cons (.regular firstSorted) .nil)))
  have secondLamSorted := signature.application context .lam _ (.cons (.bound secondDeclared)
    (.cons (.regular typeSorted) (.cons (.regular secondSorted) .nil)))
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))
    (HOLKernelTypingRules.boolType signature.symbol) antecedent
    (applySymbol signature.symbol .lam [.var firstName, typeCode, first])
    (applySymbol signature.symbol .lam [.var secondName, typeCode, second])
    (.app (.term (profile.reference .universal)) typeCode) predicateSorted boolSorted antecedentSorted
    firstLamSorted secondLamSorted operationSorted constantTyping equal
  obtain ⟨expandedAdmitted⟩ := applicationArgument_admitted signature abbreviation profile distinct constants parameters rules names
    _ _ antecedent _ _ (.app (.term (profile.reference .universal)) typeCode) predicateSorted boolSorted antecedentSorted
    firstLamSorted secondLamSorted operationSorted constantTyping equal g (.lam p) (.lam q) F contextRead predicateRead boolRead
    (lamRead firstName first p firstBeyond firstRead) (lamRead secondName second q secondBeyond secondRead)
    operationRead ruleAt bindingAt selected equalAdmitted
  have nativeRead (name : Nat) (native : Preterm) (body : Formula Const (domain :: gamma))
      (beyond : parameters ≤ name)
      (bodyRead : R (BinderNames.cons (type := domain) name names) (expand native) = some ⟨.prop, body⟩) :
      R names (expand (applySymbol signature.symbol .allc [.var name, typeCode, native])) = some ⟨.prop, .all body⟩ := by
    have decoded := readTermWith_universal (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand typeCode) (expand native)
      domain name body beyond typeRead bodyRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .allc)] using decoded
  let left := HOLKernelLogicalOperationProofs.universalUnfolding signature profile typeCode first firstName firstDeclared typeSorted firstSorted
  let right := HOLKernelLogicalOperationProofs.universalUnfolding signature profile typeCode second secondName secondDeclared typeSorted secondSorted
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app F (.lam p)) (.all p) (.app F (.lam q)) (.all q) contextRead boolRead
    (nativeRead firstName first p firstBeyond firstRead) (nativeRead secondName second q secondBeyond secondRead)
    (HOLKernelLogicalFunctionReadback.universal_reduces p)
    (HOLKernelLogicalFunctionReadback.universal_reduces q) ruleAt bindingAt expandedAdmitted

theorem existential_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode first second : Preterm) (firstName secondName : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstDeclared : context[firstName]? = some (.bound signature.ids.object))
    (secondDeclared : context[secondName]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol
          (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))
          (applySymbol signature.symbol .lam [.var firstName, typeCode, first])
          (applySymbol signature.symbol .lam [.var secondName, typeCode, second])))))
    (g : Judgment Const gamma) {domain : Ty Unit} (p q : Formula Const (domain :: gamma))
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some domain)
    (firstBeyond : parameters ≤ firstName) (secondBeyond : parameters ≤ secondName)
    (firstRead : R (BinderNames.cons (type := domain) firstName names) (expand first) = some ⟨.prop, p⟩)
    (secondRead : R (BinderNames.cons (type := domain) secondName names) (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .applicationArgument) = some (.inference .applicationArgument))
    {fuel : Nat}
    (equalAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      equal.val (.imp g.formula (.eq (.lam p) (.lam q)))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max 1 fuel + 2) names
      (HOLKernelCongruence.existentialCongruence signature profile rules antecedent typeCode first second firstName secondName
        antecedentSorted typeSorted firstDeclared secondDeclared firstSorted secondSorted equal).val
      (.imp g.formula (.eq (.ex p) (.ex q)))) := by
  have boolSorted := signature.application context .bool [] .nil
  have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
    simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
      readType, readHead_reference signature.symbol signature.symbol_injective]
  have predicateSorted := signature.application context .function [typeCode, HOLKernelTypingRules.boolType signature.symbol]
    (.cons (.regular typeSorted) (.cons (.regular boolSorted) .nil))
  have predicateRead : readType signature.symbol
      (expand (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))) =
      some (domain ⇒ .prop) := by
    simp [HOLKernelTypingRules.functionType, HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs,
      expandEquivalence, distinct, readType, readHead_reference signature.symbol signature.symbol_injective, typeRead]
  have operationSorted : Preterm.HasType terms context (.app (.term (profile.reference .existential)) typeCode) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using Preterm.HasType.term (profile.declared .existential)) typeSorted
  let F : Term Const gamma ((domain ⇒ .prop) ⇒ .prop) := (HOLKernelLogicalFunctionReadback.value .existential domain).term
  have operationRead : R names (expand (.app (.term (profile.reference .existential)) typeCode)) = some ⟨_, F⟩ := by
    simpa only [expandEquivalence, HOLKernelLogicalFunctionReadback.value, F] using
      HOLKernelLogicalFunctionReadback.reader_parameterized profile constants parameters names .existential (by simp)
        (expand typeCode) domain typeRead
  have lamRead (name : Nat) (native : Preterm) (body : Formula Const (domain :: gamma))
      (beyond : parameters ≤ name)
      (bodyRead : R (BinderNames.cons (type := domain) name names) (expand native) = some ⟨.prop, body⟩) :
      R names (expand (applySymbol signature.symbol .lam [.var name, typeCode, native])) = some ⟨domain ⇒ .prop, .lam body⟩ := by
    have decoded := readTermWith_lambda (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand typeCode) (expand native)
      domain .prop name body beyond typeRead bodyRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .lam)] using decoded
  let constantTyping := HOLKernelLogicalOperationProofs.existentialTyping (hypotheses := []) signature profile antecedent typeCode antecedentSorted typeSorted
  have firstLamSorted := signature.application context .lam _ (.cons (.bound firstDeclared)
    (.cons (.regular typeSorted) (.cons (.regular firstSorted) .nil)))
  have secondLamSorted := signature.application context .lam _ (.cons (.bound secondDeclared)
    (.cons (.regular typeSorted) (.cons (.regular secondSorted) .nil)))
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (HOLKernelTypingRules.functionType signature.symbol typeCode (HOLKernelTypingRules.boolType signature.symbol))
    (HOLKernelTypingRules.boolType signature.symbol) antecedent
    (applySymbol signature.symbol .lam [.var firstName, typeCode, first])
    (applySymbol signature.symbol .lam [.var secondName, typeCode, second])
    (.app (.term (profile.reference .existential)) typeCode) predicateSorted boolSorted antecedentSorted
    firstLamSorted secondLamSorted operationSorted constantTyping equal
  obtain ⟨expandedAdmitted⟩ := applicationArgument_admitted signature abbreviation profile distinct constants parameters rules names
    _ _ antecedent _ _ (.app (.term (profile.reference .existential)) typeCode) predicateSorted boolSorted antecedentSorted
    firstLamSorted secondLamSorted operationSorted constantTyping equal g (.lam p) (.lam q) F contextRead predicateRead boolRead
    (lamRead firstName first p firstBeyond firstRead) (lamRead secondName second q secondBeyond secondRead)
    operationRead ruleAt bindingAt selected equalAdmitted
  have nativeRead (name : Nat) (native : Preterm) (body : Formula Const (domain :: gamma))
      (beyond : parameters ≤ name)
      (bodyRead : R (BinderNames.cons (type := domain) name names) (expand native) = some ⟨.prop, body⟩) :
      R names (expand (applySymbol signature.symbol .exc [.var name, typeCode, native])) = some ⟨.prop, .ex body⟩ := by
    have decoded := readTermWith_existential (HOLKernelLogicalFunctionReadback.atoms profile)
      signature.symbol signature.symbol_injective constants parameters names (expand typeCode) (expand native)
      domain name body beyond typeRead bodyRead
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
      expandEquivalence, if_neg (distinct .exc)] using decoded
  let left := HOLKernelLogicalOperationProofs.existentialUnfolding signature profile typeCode first firstName firstDeclared typeSorted firstSorted
  let right := HOLKernelLogicalOperationProofs.existentialUnfolding signature profile typeCode second secondName secondDeclared typeSorted secondSorted
  exact convertEquality_admitted signature abbreviation profile distinct constants parameters names antecedent
    (HOLKernelTypingRules.boolType signature.symbol) _ _ _ _ antecedentSorted boolSorted
    ⟨.symm left.val, .symm left.property⟩ ⟨.symm right.val, .symm right.property⟩ expanded g
    (.app F (.lam p)) (.ex p) (.app F (.lam q)) (.ex q) contextRead boolRead
    (nativeRead firstName first p firstBeyond firstRead) (nativeRead secondName second q secondBeyond secondRead)
    (HOLKernelLogicalFunctionReadback.existential_reduces p)
    (HOLKernelLogicalFunctionReadback.existential_reduces q) ruleAt bindingAt expandedAdmitted

#print axioms equality_admitted
#print axioms negation_admitted
#print axioms universal_admitted
#print axioms existential_admitted
end Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
