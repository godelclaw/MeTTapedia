import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumFormation

/-!
# Native signature extensions preserving their authored declarations

An extension may add dependent declarations that use existing carriers.
The original declaration headers and ranks are compared explicitly.
Every local rule and all its payloads are transported into the extension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureExtension

open SignatureSum
open Mettapedia.TypeTheory

universe u
variable {S T : Symbols.{u}} (source : Signature S)
    (target : Signature (SignatureSum.symbols S T))

structure Preserves where
  typeParameters : ∀ symbol, target.typeParameters (.inl symbol) = contextLeft (source.typeParameters symbol)
  termParameters : ∀ symbol, target.termParameters (.inl symbol) = contextLeft (source.termParameters symbol)
  predicateParameters : ∀ symbol, target.predicateParameters (.inl symbol) = contextLeft (source.predicateParameters symbol)
  termResult : ∀ symbol, target.termResult (.inl symbol) = typeLeft (source.termResult symbol)
  typeRank : ∀ symbol, target.typeRank (.inl symbol) = source.typeRank symbol
  termRank : ∀ symbol, target.termRank (.inl symbol) = source.termRank symbol
  predicateRank : ∀ symbol, target.predicateRank (.inl symbol) = source.predicateRank symbol

def rule : RuleCode source → RuleCode target
  | .contextNil => .contextNil
  | .contextExtend context type => .contextExtend (contextLeft context) (typeLeft type)
  | .variable context index => .variable (contextLeft context) index
  | .typeFamily context symbol arguments => .typeFamily (contextLeft context) (Sum.inl symbol) (substitutionLeft arguments)
  | .primitive context symbol arguments => .primitive (contextLeft context) (Sum.inl symbol) (substitutionLeft arguments)
  | .piFormation context domain body => .piFormation (contextLeft context) (typeLeft domain) (typeLeft body)
  | .sigmaFormation context domain body => .sigmaFormation (contextLeft context) (typeLeft domain) (typeLeft body)
  | .lambda context domain body term => .lambda (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft term)
  | .application context domain body function argument => .application (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft function) (termLeft argument)
  | .pairIntroduction context domain body first second => .pairIntroduction (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .firstProjection context domain body pair => .firstProjection (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft pair)
  | .secondProjection context domain body pair => .secondProjection (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft pair)
  | .sigmaElimination context domain body motive branch pair => .sigmaElimination (contextLeft context) (typeLeft domain) (typeLeft body) (typeLeft motive) (termLeft branch) (termLeft pair)
  | .termConversion context term first second => .termConversion (contextLeft context) (termLeft term) (typeLeft first) (typeLeft second)
  | .substitutionNil context => .substitutionNil (contextLeft context)
  | .substitutionExtend source target type substitution term => .substitutionExtend (contextLeft source) (contextLeft target) (typeLeft type) (substitutionLeft substitution) (termLeft term)
  | .substitutionIdentity context => .substitutionIdentity (contextLeft context)
  | .substitutionCompose source middle target first second => .substitutionCompose (contextLeft source) (contextLeft middle) (contextLeft target) (substitutionLeft first) (substitutionLeft second)
  | .substitutionWeaken context type => .substitutionWeaken (contextLeft context) (typeLeft type)
  | .substituteType source target substitution type => .substituteType (contextLeft source) (contextLeft target) (substitutionLeft substitution) (typeLeft type)
  | .substituteTerm source target substitution term type => .substituteTerm (contextLeft source) (contextLeft target) (substitutionLeft substitution) (termLeft term) (typeLeft type)
  | .contextReflexivity context => .contextReflexivity (contextLeft context)
  | .contextSymmetry first second => .contextSymmetry (contextLeft first) (contextLeft second)
  | .contextTransitivity first middle last => .contextTransitivity (contextLeft first) (contextLeft middle) (contextLeft last)
  | .contextExtendEquality first second firstType secondType => .contextExtendEquality (contextLeft first) (contextLeft second) (typeLeft firstType) (typeLeft secondType)
  | .transportType first second type => .transportType (contextLeft first) (contextLeft second) (typeLeft type)
  | .transportTerm first second term type => .transportTerm (contextLeft first) (contextLeft second) (termLeft term) (typeLeft type)
  | .transportSubstitution source source' target target' substitution => .transportSubstitution (contextLeft source) (contextLeft source') (contextLeft target) (contextLeft target') (substitutionLeft substitution)
  | .typeReflexivity context type => .typeReflexivity (contextLeft context) (typeLeft type)
  | .typeSymmetry context first second => .typeSymmetry (contextLeft context) (typeLeft first) (typeLeft second)
  | .typeTransitivity context first middle last => .typeTransitivity (contextLeft context) (typeLeft first) (typeLeft middle) (typeLeft last)
  | .termReflexivity context term type => .termReflexivity (contextLeft context) (termLeft term) (typeLeft type)
  | .termSymmetry context first second type => .termSymmetry (contextLeft context) (termLeft first) (termLeft second) (typeLeft type)
  | .termTransitivity context first middle last type => .termTransitivity (contextLeft context) (termLeft first) (termLeft middle) (termLeft last) (typeLeft type)
  | .equalityConversion context first second firstType secondType => .equalityConversion (contextLeft context) (termLeft first) (termLeft second) (typeLeft firstType) (typeLeft secondType)
  | .transportTypeEquality source target first second => .transportTypeEquality (contextLeft source) (contextLeft target) (typeLeft first) (typeLeft second)
  | .transportTermEquality source target first second type => .transportTermEquality (contextLeft source) (contextLeft target) (termLeft first) (termLeft second) (typeLeft type)
  | .piCongruence context firstDomain secondDomain firstBody secondBody => .piCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody)
  | .sigmaCongruence context firstDomain secondDomain firstBody secondBody => .sigmaCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody)
  | .familyCongruence context symbol first second => .familyCongruence (contextLeft context) (Sum.inl symbol) (substitutionLeft first) (substitutionLeft second)
  | .primitiveCongruence context symbol first second => .primitiveCongruence (contextLeft context) (Sum.inl symbol) (substitutionLeft first) (substitutionLeft second)
  | .lambdaCongruence context domain body first second => .lambdaCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument => .applicationCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft firstFunction) (termLeft secondFunction) (termLeft firstArgument) (termLeft secondArgument)
  | .pairCongruence context domain body firstLeft secondLeft firstRight secondRight => .pairCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft firstLeft) (termLeft secondLeft) (termLeft firstRight) (termLeft secondRight)
  | .firstCongruence context domain body first second => .firstCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .secondCongruence context domain body first second => .secondCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair => .sigmaEliminationCongruence (contextLeft context) (typeLeft domain) (typeLeft body) (typeLeft motive) (termLeft firstBranch) (termLeft secondBranch) (termLeft firstPair) (termLeft secondPair)
  | .lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => .lambdaAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (termLeft first) (termLeft second)
  | .applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument => .applicationAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (termLeft firstFunction) (termLeft secondFunction) (termLeft firstArgument) (termLeft secondArgument)
  | .pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight => .pairAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (termLeft firstLeft) (termLeft secondLeft) (termLeft firstRight) (termLeft secondRight)
  | .firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => .firstAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (termLeft first) (termLeft second)
  | .secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => .secondAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (termLeft first) (termLeft second)
  | .sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair => .sigmaEliminationAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (typeLeft firstBody) (typeLeft secondBody) (typeLeft firstMotive) (typeLeft secondMotive) (termLeft firstBranch) (termLeft secondBranch) (termLeft firstPair) (termLeft secondPair)
  | .piBeta context domain body term argument => .piBeta (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft term) (termLeft argument)
  | .piEta context domain body function => .piEta (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft function)
  | .sigmaFirstBeta context domain body first second => .sigmaFirstBeta (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .sigmaSecondBeta context domain body first second => .sigmaSecondBeta (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | .sigmaEta context domain body pair => .sigmaEta (contextLeft context) (typeLeft domain) (typeLeft body) (termLeft pair)
  | .sigmaEliminationBeta context domain body motive branch first second => .sigmaEliminationBeta (contextLeft context) (typeLeft domain) (typeLeft body) (typeLeft motive) (termLeft branch) (termLeft first) (termLeft second)
  | .sigmaEliminationEta context domain body motive term pair => .sigmaEliminationEta (contextLeft context) (typeLeft domain) (typeLeft body) (typeLeft motive) (termLeft term) (termLeft pair)
  | .substituteTypeEquality source target substitution first second => .substituteTypeEquality (contextLeft source) (contextLeft target) (substitutionLeft substitution) (typeLeft first) (typeLeft second)
  | .substituteTermEquality source target substitution first second type => .substituteTermEquality (contextLeft source) (contextLeft target) (substitutionLeft substitution) (termLeft first) (termLeft second) (typeLeft type)
  | .substitutionReflexivity source target substitution => .substitutionReflexivity (contextLeft source) (contextLeft target) (substitutionLeft substitution)
  | .substitutionSymmetry source target first second => .substitutionSymmetry (contextLeft source) (contextLeft target) (substitutionLeft first) (substitutionLeft second)
  | .substitutionTransitivity source target first middle last => .substitutionTransitivity (contextLeft source) (contextLeft target) (substitutionLeft first) (substitutionLeft middle) (substitutionLeft last)
  | .substitutionExtendEquality source target type first second firstTerm secondTerm => .substitutionExtendEquality (contextLeft source) (contextLeft target) (typeLeft type) (substitutionLeft first) (substitutionLeft second) (termLeft firstTerm) (termLeft secondTerm)
  | .typeSubstitutionCongruence source target first second type => .typeSubstitutionCongruence (contextLeft source) (contextLeft target) (substitutionLeft first) (substitutionLeft second) (typeLeft type)
  | .termSubstitutionCongruence source target first second term type => .termSubstitutionCongruence (contextLeft source) (contextLeft target) (substitutionLeft first) (substitutionLeft second) (termLeft term) (typeLeft type)
  | .contextAssume context predicate => .contextAssume (contextLeft context) (propLeft predicate)
  | .propositionType context => .propositionType (contextLeft context)
  | .predicatePrimitive context symbol arguments => .predicatePrimitive (contextLeft context) (Sum.inl symbol) (substitutionLeft arguments)
  | .truthFormation context => .truthFormation (contextLeft context)
  | .falsehoodFormation context => .falsehoodFormation (contextLeft context)
  | .conjunctionFormation context first second => .conjunctionFormation (contextLeft context) (propLeft first) (propLeft second)
  | .disjunctionFormation context first second => .disjunctionFormation (contextLeft context) (propLeft first) (propLeft second)
  | .implicationFormation context first second => .implicationFormation (contextLeft context) (propLeft first) (propLeft second)
  | .universalFormation context domain predicate => .universalFormation (contextLeft context) (typeLeft domain) (propLeft predicate)
  | .existentialFormation context domain predicate => .existentialFormation (contextLeft context) (typeLeft domain) (propLeft predicate)
  | .holdsFormation context term => .holdsFormation (contextLeft context) (termLeft term)
  | .imageFormation context type => .imageFormation (contextLeft context) (typeLeft type)
  | .quote context predicate => .quote (contextLeft context) (propLeft predicate)
  | .comprehensionFormation context domain predicate => .comprehensionFormation (contextLeft context) (typeLeft domain) (propLeft predicate)
  | .comprehensionIntroduction context domain predicate value => .comprehensionIntroduction (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .comprehensionElimination context domain predicate value => .comprehensionElimination (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .comprehensionGuard context domain predicate value => .comprehensionGuard (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .comprehensionBeta context domain predicate value => .comprehensionBeta (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .comprehensionEta context domain predicate value => .comprehensionEta (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .quoteHolds context term => .quoteHolds (contextLeft context) (termLeft term)
  | .holdsQuote context predicate => .holdsQuote (contextLeft context) (propLeft predicate)
  | .hypothesis context predicate member => .hypothesis (contextLeft context) (propLeft predicate) (hypothesisLeft member)
  | .truthIntroduction context => .truthIntroduction (contextLeft context)
  | .falsehoodElimination context predicate => .falsehoodElimination (contextLeft context) (propLeft predicate)
  | .conjunctionIntroduction context first second => .conjunctionIntroduction (contextLeft context) (propLeft first) (propLeft second)
  | .conjunctionFirst context first second => .conjunctionFirst (contextLeft context) (propLeft first) (propLeft second)
  | .conjunctionSecond context first second => .conjunctionSecond (contextLeft context) (propLeft first) (propLeft second)
  | .disjunctionFirst context first second => .disjunctionFirst (contextLeft context) (propLeft first) (propLeft second)
  | .disjunctionSecond context first second => .disjunctionSecond (contextLeft context) (propLeft first) (propLeft second)
  | .disjunctionElimination context first second consequent => .disjunctionElimination (contextLeft context) (propLeft first) (propLeft second) (propLeft consequent)
  | .implicationIntroduction context first second => .implicationIntroduction (contextLeft context) (propLeft first) (propLeft second)
  | .implicationElimination context first second => .implicationElimination (contextLeft context) (propLeft first) (propLeft second)
  | .universalIntroduction context domain predicate => .universalIntroduction (contextLeft context) (typeLeft domain) (propLeft predicate)
  | .universalElimination context domain predicate value => .universalElimination (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .existentialIntroduction context domain predicate value => .existentialIntroduction (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft value)
  | .existentialElimination context domain predicate consequent => .existentialElimination (contextLeft context) (typeLeft domain) (propLeft predicate) (propLeft consequent)
  | .imageIntroduction context type value => .imageIntroduction (contextLeft context) (typeLeft type) (termLeft value)
  | .imageElimination context type predicate => .imageElimination (contextLeft context) (typeLeft type) (propLeft predicate)
  | .substitutionWeakenAssumption context predicate => .substitutionWeakenAssumption (contextLeft context) (propLeft predicate)
  | .substitutionIntoAssumption source target predicate substitution => .substitutionIntoAssumption (contextLeft source) (contextLeft target) (propLeft predicate) (substitutionLeft substitution)
  | .substitutionLift source target type substitution => .substitutionLift (contextLeft source) (contextLeft target) (typeLeft type) (substitutionLeft substitution)
  | .substitutionAssumptionLift source target predicate substitution => .substitutionAssumptionLift (contextLeft source) (contextLeft target) (propLeft predicate) (substitutionLeft substitution)
  | .substitutePredicate source target substitution predicate => .substitutePredicate (contextLeft source) (contextLeft target) (substitutionLeft substitution) (propLeft predicate)
  | .substituteEntailment source target substitution predicate => .substituteEntailment (contextLeft source) (contextLeft target) (substitutionLeft substitution) (propLeft predicate)
  | .transportPredicate first second predicate => .transportPredicate (contextLeft first) (contextLeft second) (propLeft predicate)
  | .transportEntailment first second predicate => .transportEntailment (contextLeft first) (contextLeft second) (propLeft predicate)
  | .predicateReflexivity context predicate => .predicateReflexivity (contextLeft context) (propLeft predicate)
  | .predicateSymmetry context first second => .predicateSymmetry (contextLeft context) (propLeft first) (propLeft second)
  | .predicateTransitivity context first middle last => .predicateTransitivity (contextLeft context) (propLeft first) (propLeft middle) (propLeft last)
  | .predicateExtensionality context first second => .predicateExtensionality (contextLeft context) (propLeft first) (propLeft second)
  | .entailmentConversion context first second => .entailmentConversion (contextLeft context) (propLeft first) (propLeft second)
  | .contextAssumeEquality first second firstPredicate secondPredicate => .contextAssumeEquality (contextLeft first) (contextLeft second) (propLeft firstPredicate) (propLeft secondPredicate)
  | .comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate => .comprehensionCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (propLeft firstPredicate) (propLeft secondPredicate)
  | .quoteCongruence context first second => .quoteCongruence (contextLeft context) (propLeft first) (propLeft second)
  | .holdsCongruence context first second => .holdsCongruence (contextLeft context) (termLeft first) (termLeft second)
  | .imageCongruence context first second => .imageCongruence (contextLeft context) (typeLeft first) (typeLeft second)
  | .refineCongruence context domain predicate first second => .refineCongruence (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft first) (termLeft second)
  | .forgetCongruence context domain predicate first second => .forgetCongruence (contextLeft context) (typeLeft domain) (propLeft predicate) (termLeft first) (termLeft second)
  | .predicatePrimitiveCongruence context symbol first second => .predicatePrimitiveCongruence (contextLeft context) (Sum.inl symbol) (substitutionLeft first) (substitutionLeft second)
  | .conjunctionCongruence context first second third fourth => .conjunctionCongruence (contextLeft context) (propLeft first) (propLeft second) (propLeft third) (propLeft fourth)
  | .disjunctionCongruence context first second third fourth => .disjunctionCongruence (contextLeft context) (propLeft first) (propLeft second) (propLeft third) (propLeft fourth)
  | .implicationCongruence context first second third fourth => .implicationCongruence (contextLeft context) (propLeft first) (propLeft second) (propLeft third) (propLeft fourth)
  | .universalCongruence context firstDomain secondDomain firstPredicate secondPredicate => .universalCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (propLeft firstPredicate) (propLeft secondPredicate)
  | .existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate => .existentialCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (propLeft firstPredicate) (propLeft secondPredicate)
  | .substitutePredicateEquality source target substitution first second => .substitutePredicateEquality (contextLeft source) (contextLeft target) (substitutionLeft substitution) (propLeft first) (propLeft second)
  | .predicateSubstitutionCongruence source target first second predicate => .predicateSubstitutionCongruence (contextLeft source) (contextLeft target) (substitutionLeft first) (substitutionLeft second) (propLeft predicate)
  | .refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second => .refineAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (propLeft firstPredicate) (propLeft secondPredicate) (termLeft first) (termLeft second)
  | .forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second => .forgetAnnotationCongruence (contextLeft context) (typeLeft firstDomain) (typeLeft secondDomain) (propLeft firstPredicate) (propLeft secondPredicate) (termLeft first) (termLeft second)
  | .substitutionIntoAssumptionEquality source target predicate first second => .substitutionIntoAssumptionEquality (contextLeft source) (contextLeft target) (propLeft predicate) (substitutionLeft first) (substitutionLeft second)

attribute [local simp] rule RuleCode.conclusion RuleCode.premises judgmentLeft
  contextLeft typeLeft termLeft propLeft

theorem conclusion (comparison : Preserves source target) (original : RuleCode source) :
    (rule source target original).conclusion = judgmentLeft original.conclusion := by
  cases original <;> first | rfl | simp [comparison.termResult]

theorem premises (comparison : Preserves source target) (original : RuleCode source) :
    (rule source target original).premises = original.premises.map judgmentLeft := by
  cases original <;> first | rfl | simp [comparison.typeParameters, comparison.termParameters,
    comparison.predicateParameters, comparison.termResult]

def map (comparison : Preserves source target) :
    JudgmentDerivation.SignatureMap (judgmentSignature source) (judgmentSignature target) where
  judgment := judgmentLeft
  rule := fun original =>
    ⟨rule source target original.val,
      (conclusion source target comparison _).trans (congrArg judgmentLeft original.property)⟩
  position := fun original position =>
    ⟨⟨position.down.val, by
      simpa only [premises source target comparison original.val, List.length_map] using position.down.isLt⟩⟩
  hypothesis := by
    intro judgment original position
    change judgmentLeft (original.val.premises[position.down.val]'_) =
      (rule source target original.val).premises[position.down.val]
    simp only [premises source target comparison original.val, List.getElem_map]

def derivation (comparison : Preserves source target) {judgment : Judgment S}
    (tree : Derivation source judgment) : Derivation target (judgmentLeft judgment) :=
  (map source target comparison).translate tree

theorem premise_index (comparison : Preserves source target) {judgment : Judgment S}
    (original : (judgmentSignature source).Rule judgment)
    (position : (judgmentSignature target).Premise ((map source target comparison).rule original)) :
    ((map source target comparison).position original position).down.val = position.down.val := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureExtension
