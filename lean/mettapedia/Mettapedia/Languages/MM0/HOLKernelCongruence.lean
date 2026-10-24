import Mettapedia.Languages.MM0.HOLKernelLogicalOperationProofs
import Mettapedia.Languages.MM0.HOLKernelInferenceProofs
import Mettapedia.Languages.MM0.HOLKernelBindingProofs

/-!
# Checked application and logical congruence in maintained MM0 HOL

Application congruence is derived from the maintained function- and
argument-congruence rules, equality typing and transitivity. Logical
constructor congruence uses the actual function constants and checked stored
definition conversions. Changing binder names additionally requires a proved
abstraction equality; constructor unfolding does not provide one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelCongruence

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

def convertEquality (signature : Signature sorts terms)
    (antecedent type first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (firstConversion : { witness : ConvWitness // ConvWitness.Checks terms definitions context
      witness first first' signature.ids.object })
    (secondConversion : { witness : ConvWitness // ConvWitness.Checks terms definitions context
      witness second second' signature.ids.object })
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol type first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol type first' second'))) := by
  have firstSorted := firstConversion.property.typed
  have secondSorted := secondConversion.property.typed
  let inner : ConvWitness := .congruence (signature.symbol .eqc)
    [.refl type, firstConversion.val, secondConversion.val]
  have checkedInner : ConvWitness.Checks terms definitions context inner
      (equality signature.symbol type first second)
      (equality signature.symbol type first' second') signature.ids.object :=
    .congruence (signature.declared .eqc)
      (.cons (.regular typeSorted) (.regular typeSorted) (.refl typeSorted)
        (.cons (.regular firstSorted.1) (.regular firstSorted.2) firstConversion.property
          (.cons (.regular secondSorted.1) (.regular secondSorted.2) secondConversion.property .nil)))
  let asserted : ConvWitness := .congruence (signature.symbol .thm) [inner]
  have checkedAsserted : ConvWitness.Checks terms definitions context asserted
      (holds signature.symbol (equality signature.symbol type first second))
      (holds signature.symbol (equality signature.symbol type first' second')) signature.ids.wff :=
    .congruence (signature.declared .thm)
      (.cons (.regular checkedInner.typed.1) (.regular checkedInner.typed.2) checkedInner .nil)
  let conversion : ConvWitness := .congruence (signature.symbol .im) [.refl antecedent, asserted]
  have checked : ConvWitness.Checks terms definitions context conversion
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol type first second)))
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol type first' second'))) signature.ids.wff :=
    .congruence (signature.declared .im)
      (.cons (.regular antecedentSorted) (.regular antecedentSorted) (.refl antecedentSorted)
        (.cons (.regular checkedAsserted.typed.1) (.regular checkedAsserted.typed.2)
          checkedAsserted .nil))
  exact ⟨.conversion conversion source.val, .conversion checked source.property⟩

def application (signature : Signature sorts terms)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent domain result firstFunction secondFunction firstArgument secondArgument : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (firstFunctionSorted : Preterm.HasType terms context firstFunction [] signature.ids.object)
    (secondFunctionSorted : Preterm.HasType terms context secondFunction [] signature.ids.object)
    (firstArgumentSorted : Preterm.HasType terms context firstArgument [] signature.ids.object)
    (secondArgumentSorted : Preterm.HasType terms context secondArgument [] signature.ids.object)
    (functions : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (functionType signature.symbol domain result)
          firstFunction secondFunction))))
    (arguments : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol domain firstArgument secondArgument)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol result
        (applySymbol signature.symbol .app [firstFunction, firstArgument])
        (applySymbol signature.symbol .app [secondFunction, secondArgument])))) := by
  have functionTypeSorted := signature.application context .function [domain, result]
    (.cons (.regular domainSorted) (.cons (.regular resultSorted) .nil))
  let argumentTyping := HOLKernelBindingProofs.Native.equalityLeftTyping signature binding
    domain antecedent firstArgument secondArgument domainSorted antecedentSorted
    firstArgumentSorted secondArgumentSorted arguments
  let functionTyping := HOLKernelBindingProofs.Native.equalityRightTyping signature binding
    (functionType signature.symbol domain result) antecedent firstFunction secondFunction
    functionTypeSorted antecedentSorted firstFunctionSorted secondFunctionSorted functions
  let changeFunction := HOLKernelInferenceProofs.Native.applicationFunction signature rules
    domain result antecedent firstArgument firstFunction secondFunction domainSorted resultSorted
    antecedentSorted firstArgumentSorted firstFunctionSorted secondFunctionSorted functions argumentTyping
  let changeArgument := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    domain result antecedent firstArgument secondArgument secondFunction domainSorted resultSorted
    antecedentSorted firstArgumentSorted secondArgumentSorted secondFunctionSorted functionTyping arguments
  exact HOLKernelInferenceProofs.Native.transitivity signature rules antecedent result _ _ _
    antecedentSorted resultSorted
    (signature.application context .app _
      (.cons (.regular firstFunctionSorted) (.cons (.regular firstArgumentSorted) .nil)))
    (signature.application context .app _
      (.cons (.regular secondFunctionSorted) (.cons (.regular firstArgumentSorted) .nil)))
    (signature.application context .app _
      (.cons (.regular secondFunctionSorted) (.cons (.regular secondArgumentSorted) .nil)))
    changeFunction changeArgument

def binaryApplication (signature : Signature sorts terms)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent firstDomain secondDomain result function first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstDomainSorted : Preterm.HasType terms context firstDomain [] signature.ids.type)
    (secondDomainSorted : Preterm.HasType terms context secondDomain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (functionTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent function (functionType signature.symbol firstDomain
        (functionType signature.symbol secondDomain result))))
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol firstDomain first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol secondDomain second second')))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol result
        (applySymbol signature.symbol .app [applySymbol signature.symbol .app [function, first], second])
        (applySymbol signature.symbol .app [applySymbol signature.symbol .app [function, first'], second'])))) := by
  have partialTypeSorted := signature.application context .function [secondDomain, result]
    (.cons (.regular secondDomainSorted) (.cons (.regular resultSorted) .nil))
  let functions := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    firstDomain (functionType signature.symbol secondDomain result) antecedent first first' function
    firstDomainSorted partialTypeSorted antecedentSorted firstSorted firstSorted' functionSorted
    functionTyping firstEquality
  exact application signature rules binding antecedent secondDomain result _ _ second second'
    antecedentSorted secondDomainSorted resultSorted
    (signature.application context .app _
      (.cons (.regular functionSorted) (.cons (.regular firstSorted) .nil)))
    (signature.application context .app _
      (.cons (.regular functionSorted) (.cons (.regular firstSorted') .nil)))
    secondSorted secondSorted' functions secondEquality

def conjunctionCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) second second'))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .andc [first, second]) (applySymbol signature.symbol .andc [first', second'])))) := by
  have boolSorted := signature.application context .bool [] .nil
  let left := HOLKernelLogicalOperationProofs.conjunctionUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.conjunctionUnfolding signature profile first' second' firstSorted' secondSorted'
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .conjunction)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .conjunction)
  let constantTyping := HOLKernelLogicalOperationProofs.conjunctionTyping (hypotheses := hypotheses) signature profile antecedent antecedentSorted
  let expanded := binaryApplication signature rules binding antecedent (boolType signature.symbol) (boolType signature.symbol)
    (boolType signature.symbol) (.term (profile.reference .conjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def disjunctionCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) second second'))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .orc [first, second]) (applySymbol signature.symbol .orc [first', second'])))) := by
  have boolSorted := signature.application context .bool [] .nil
  let left := HOLKernelLogicalOperationProofs.disjunctionUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.disjunctionUnfolding signature profile first' second' firstSorted' secondSorted'
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .disjunction)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .disjunction)
  let constantTyping := HOLKernelLogicalOperationProofs.disjunctionTyping (hypotheses := hypotheses) signature profile antecedent antecedentSorted
  let expanded := binaryApplication signature rules binding antecedent (boolType signature.symbol) (boolType signature.symbol)
    (boolType signature.symbol) (.term (profile.reference .disjunction)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def implicationCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) second second'))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .impc [first, second]) (applySymbol signature.symbol .impc [first', second'])))) := by
  have boolSorted := signature.application context .bool [] .nil
  let left := HOLKernelLogicalOperationProofs.implicationUnfolding signature profile first second firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.implicationUnfolding signature profile first' second' firstSorted' secondSorted'
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .implication)) [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .implication)
  let constantTyping := HOLKernelLogicalOperationProofs.implicationTyping (hypotheses := hypotheses) signature profile antecedent antecedentSorted
  let expanded := binaryApplication signature rules binding antecedent (boolType signature.symbol) (boolType signature.symbol)
    (boolType signature.symbol) (.term (profile.reference .implication)) first first' second second'
    antecedentSorted boolSorted boolSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def equalityCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent domain first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol domain first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol domain second second'))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .eqc [domain, first, second]) (applySymbol signature.symbol .eqc [domain, first', second'])))) := by
  have boolSorted := signature.application context .bool [] .nil
  let left := HOLKernelLogicalOperationProofs.equalityUnfolding signature profile domain first second domainSorted firstSorted secondSorted
  let right := HOLKernelLogicalOperationProofs.equalityUnfolding signature profile domain first' second' domainSorted firstSorted' secondSorted'
  have operationSorted : Preterm.HasType terms context (.app (.term (profile.reference .equality)) domain) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .equality)) domainSorted
  let constantTyping := HOLKernelLogicalOperationProofs.equalityTyping (hypotheses := hypotheses) signature profile antecedent domain antecedentSorted domainSorted
  let expanded := binaryApplication signature rules binding antecedent domain domain
    (boolType signature.symbol) (.app (.term (profile.reference .equality)) domain) first first' second second'
    antecedentSorted domainSorted domainSorted boolSorted operationSorted
    firstSorted firstSorted' secondSorted secondSorted' constantTyping firstEquality secondEquality
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def negationCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .notc [first]) (applySymbol signature.symbol .notc [second])))) := by
  have boolSorted := signature.application context .bool [] .nil
  let left := HOLKernelLogicalOperationProofs.negationUnfolding signature profile first firstSorted
  let right := HOLKernelLogicalOperationProofs.negationUnfolding signature profile second secondSorted
  have operationSorted : Preterm.HasType terms context (.term (profile.reference .negation))
      [] signature.ids.object := by
    simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .negation)
  let constantTyping := HOLKernelLogicalOperationProofs.negationTyping (hypotheses := hypotheses) signature profile
    antecedent antecedentSorted
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (boolType signature.symbol) (boolType signature.symbol) antecedent first second
    (.term (profile.reference .negation)) boolSorted boolSorted antecedentSorted firstSorted
    secondSorted operationSorted constantTyping equal
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def universalCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent domain first second : Preterm) (firstBound secondBound : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (firstBoundDeclared : context[firstBound]? = some (.bound signature.ids.object))
    (secondBoundDeclared : context[secondBound]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (abstractionsEqual : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (applySymbol signature.symbol .lam [.var firstBound, domain, first]) (applySymbol signature.symbol .lam [.var secondBound, domain, second]))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .allc [.var firstBound, domain, first]) (applySymbol signature.symbol .allc [.var secondBound, domain, second])))) := by
  have boolSorted := signature.application context .bool [] .nil
  have predicateTypeSorted := signature.application context .function [domain, boolType signature.symbol]
    (.cons (.regular domainSorted) (.cons (.regular boolSorted) .nil))
  let left := HOLKernelLogicalOperationProofs.universalUnfolding signature profile domain first
    firstBound firstBoundDeclared domainSorted firstSorted
  let right := HOLKernelLogicalOperationProofs.universalUnfolding signature profile domain second
    secondBound secondBoundDeclared domainSorted secondSorted
  have operationSorted : Preterm.HasType terms context
      (.app (.term (profile.reference .universal)) domain) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .universal)) domainSorted
  let constantTyping := HOLKernelLogicalOperationProofs.universalTyping (hypotheses := hypotheses) signature profile
    antecedent domain antecedentSorted domainSorted
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol)
    antecedent (applySymbol signature.symbol .lam [.var firstBound, domain, first])
    (applySymbol signature.symbol .lam [.var secondBound, domain, second])
    (.app (.term (profile.reference .universal)) domain) predicateTypeSorted boolSorted antecedentSorted
    (signature.application context .lam _ (.cons (.bound firstBoundDeclared)
      (.cons (.regular domainSorted) (.cons (.regular firstSorted) .nil))))
    (signature.application context .lam _ (.cons (.bound secondBoundDeclared)
      (.cons (.regular domainSorted) (.cons (.regular secondSorted) .nil))))
    operationSorted constantTyping abstractionsEqual
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

def existentialCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent domain first second : Preterm) (firstBound secondBound : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (firstBoundDeclared : context[firstBound]? = some (.bound signature.ids.object))
    (secondBoundDeclared : context[secondBound]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (abstractionsEqual : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (applySymbol signature.symbol .lam [.var firstBound, domain, first]) (applySymbol signature.symbol .lam [.var secondBound, domain, second]))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (equality signature.symbol (boolType signature.symbol) (applySymbol signature.symbol .exc [.var firstBound, domain, first]) (applySymbol signature.symbol .exc [.var secondBound, domain, second])))) := by
  have boolSorted := signature.application context .bool [] .nil
  have predicateTypeSorted := signature.application context .function [domain, boolType signature.symbol]
    (.cons (.regular domainSorted) (.cons (.regular boolSorted) .nil))
  let left := HOLKernelLogicalOperationProofs.existentialUnfolding signature profile domain first
    firstBound firstBoundDeclared domainSorted firstSorted
  let right := HOLKernelLogicalOperationProofs.existentialUnfolding signature profile domain second
    secondBound secondBoundDeclared domainSorted secondSorted
  have operationSorted : Preterm.HasType terms context
      (.app (.term (profile.reference .existential)) domain) [] signature.ids.object :=
    .regular (by simpa [HOLKernelLogicalOperations.Operator.declaration] using
      Preterm.HasType.term (profile.declared .existential)) domainSorted
  let constantTyping := HOLKernelLogicalOperationProofs.existentialTyping (hypotheses := hypotheses) signature profile
    antecedent domain antecedentSorted domainSorted
  let expanded := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol)
    antecedent (applySymbol signature.symbol .lam [.var firstBound, domain, first])
    (applySymbol signature.symbol .lam [.var secondBound, domain, second])
    (.app (.term (profile.reference .existential)) domain) predicateTypeSorted boolSorted antecedentSorted
    (signature.application context .lam _ (.cons (.bound firstBoundDeclared)
      (.cons (.regular domainSorted) (.cons (.regular firstSorted) .nil))))
    (signature.application context .lam _ (.cons (.bound secondBoundDeclared)
      (.cons (.regular domainSorted) (.cons (.regular secondSorted) .nil))))
    operationSorted constantTyping abstractionsEqual
  exact convertEquality signature antecedent (boolType signature.symbol) _ _ _ _
    antecedentSorted boolSorted ⟨.symm left.val, .symm left.property⟩
    ⟨.symm right.val, .symm right.property⟩ expanded

#print axioms convertEquality
#print axioms application
#print axioms binaryApplication
#print axioms conjunctionCongruence
#print axioms disjunctionCongruence
#print axioms implicationCongruence
#print axioms equalityCongruence
#print axioms negationCongruence
#print axioms universalCongruence
#print axioms existentialCongruence

end Mettapedia.Languages.MM0.HOLKernelCongruence
