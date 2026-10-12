import Mettapedia.OSLF.NativeTypes.Certificates.HypothesisCoding

/-!
# Exact native rule-payload coding

Every independently declared native rule constructor has a distinct wire tag.
Scopes, declaration symbols, dependent annotations, argument order and complete
assumption-position paths are serialized and recovered. The codec does not
identify different proof origins merely because their conclusions agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.NativeWire

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable {S : Symbols} (symbols : SymbolCodecs S) (D : Signature S)

def putRule : RuleCode D → Data
  | @RuleCode.contextNil _ _ => .pair (.atom 0) (.atom 0)
  | @RuleCode.contextExtend _ _ n context type => .pair (.atom 1) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.atom 0))))
  | @RuleCode.variable _ _ n context index => .pair (.atom 2) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((Codec.fin n).put index) (.atom 0))))
  | @RuleCode.typeFamily _ _ n context symbol arguments => .pair (.atom 3) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.typeSymbol.put symbol) (.pair ((argumentsAt symbols n (S.typeArity symbol)).put arguments) (.atom 0)))))
  | @RuleCode.primitive _ _ n context symbol arguments => .pair (.atom 4) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.termSymbol.put symbol) (.pair ((argumentsAt symbols n (S.termArity symbol)).put arguments) (.atom 0)))))
  | @RuleCode.piFormation _ _ n context domain body => .pair (.atom 5) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.atom 0)))))
  | @RuleCode.sigmaFormation _ _ n context domain body => .pair (.atom 6) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.atom 0)))))
  | @RuleCode.lambda _ _ n context domain body term => .pair (.atom 7) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols (n + 1)).put term) (.atom 0))))))
  | @RuleCode.application _ _ n context domain body function argument => .pair (.atom 8) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put function) (.pair ((termAt symbols n).put argument) (.atom 0)))))))
  | @RuleCode.pairIntroduction _ _ n context domain body first second => .pair (.atom 9) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.firstProjection _ _ n context domain body pair => .pair (.atom 10) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put pair) (.atom 0))))))
  | @RuleCode.secondProjection _ _ n context domain body pair => .pair (.atom 11) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put pair) (.atom 0))))))
  | @RuleCode.sigmaElimination _ _ n context domain body motive branch pair => .pair (.atom 12) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((typeAt symbols (n + 1)).put motive) (.pair ((termAt symbols (n + 2)).put branch) (.pair ((termAt symbols n).put pair) (.atom 0))))))))
  | @RuleCode.termConversion _ _ n context term first second => .pair (.atom 13) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put term) (.pair ((typeAt symbols n).put first) (.pair ((typeAt symbols n).put second) (.atom 0))))))
  | @RuleCode.substitutionNil _ _ n context => .pair (.atom 14) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.substitutionExtend _ _ n m source target type substitution term => .pair (.atom 15) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((typeAt symbols m).put type) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((termAt symbols n).put term) (.atom 0))))))))
  | @RuleCode.substitutionIdentity _ _ n context => .pair (.atom 16) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.substitutionCompose _ _ n m k source middle target first second => .pair (.atom 17) (.pair (.atom n) (.pair (.atom m) (.pair (.atom k) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put middle) (.pair ((contextAt symbols k).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols m k).put second) (.atom 0)))))))))
  | @RuleCode.substitutionWeaken _ _ n context type => .pair (.atom 18) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.atom 0))))
  | @RuleCode.substituteType _ _ n m source target substitution type => .pair (.atom 19) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((typeAt symbols m).put type) (.atom 0)))))))
  | @RuleCode.substituteTerm _ _ n m source target substitution term type => .pair (.atom 20) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((termAt symbols m).put term) (.pair ((typeAt symbols m).put type) (.atom 0))))))))
  | @RuleCode.contextReflexivity _ _ n context => .pair (.atom 21) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.contextSymmetry _ _ n first second => .pair (.atom 22) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.atom 0))))
  | @RuleCode.contextTransitivity _ _ n first middle last => .pair (.atom 23) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put middle) (.pair ((contextAt symbols n).put last) (.atom 0)))))
  | @RuleCode.contextExtendEquality _ _ n first second firstType secondType => .pair (.atom 24) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((typeAt symbols n).put firstType) (.pair ((typeAt symbols n).put secondType) (.atom 0))))))
  | @RuleCode.transportType _ _ n first second type => .pair (.atom 25) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((typeAt symbols n).put type) (.atom 0)))))
  | @RuleCode.transportTerm _ _ n first second term type => .pair (.atom 26) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((termAt symbols n).put term) (.pair ((typeAt symbols n).put type) (.atom 0))))))
  | @RuleCode.transportSubstitution _ _ n m source source' target target' substitution => .pair (.atom 27) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols n).put source') (.pair ((contextAt symbols m).put target) (.pair ((contextAt symbols m).put target') (.pair ((argumentsAt symbols n m).put substitution) (.atom 0))))))))
  | @RuleCode.typeReflexivity _ _ n context type => .pair (.atom 28) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.atom 0))))
  | @RuleCode.typeSymmetry _ _ n context first second => .pair (.atom 29) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put first) (.pair ((typeAt symbols n).put second) (.atom 0)))))
  | @RuleCode.typeTransitivity _ _ n context first middle last => .pair (.atom 30) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put first) (.pair ((typeAt symbols n).put middle) (.pair ((typeAt symbols n).put last) (.atom 0))))))
  | @RuleCode.termReflexivity _ _ n context term type => .pair (.atom 31) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put term) (.pair ((typeAt symbols n).put type) (.atom 0)))))
  | @RuleCode.termSymmetry _ _ n context first second type => .pair (.atom 32) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.pair ((typeAt symbols n).put type) (.atom 0))))))
  | @RuleCode.termTransitivity _ _ n context first middle last type => .pair (.atom 33) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put middle) (.pair ((termAt symbols n).put last) (.pair ((typeAt symbols n).put type) (.atom 0)))))))
  | @RuleCode.equalityConversion _ _ n context first second firstType secondType => .pair (.atom 34) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.pair ((typeAt symbols n).put firstType) (.pair ((typeAt symbols n).put secondType) (.atom 0)))))))
  | @RuleCode.transportTypeEquality _ _ n source target first second => .pair (.atom 35) (.pair (.atom n) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols n).put target) (.pair ((typeAt symbols n).put first) (.pair ((typeAt symbols n).put second) (.atom 0))))))
  | @RuleCode.transportTermEquality _ _ n source target first second type => .pair (.atom 36) (.pair (.atom n) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols n).put target) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.pair ((typeAt symbols n).put type) (.atom 0)))))))
  | @RuleCode.piCongruence _ _ n context firstDomain secondDomain firstBody secondBody => .pair (.atom 37) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.atom 0)))))))
  | @RuleCode.sigmaCongruence _ _ n context firstDomain secondDomain firstBody secondBody => .pair (.atom 38) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.atom 0)))))))
  | @RuleCode.familyCongruence _ _ n context symbol first second => .pair (.atom 39) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.typeSymbol.put symbol) (.pair ((argumentsAt symbols n (S.typeArity symbol)).put first) (.pair ((argumentsAt symbols n (S.typeArity symbol)).put second) (.atom 0))))))
  | @RuleCode.primitiveCongruence _ _ n context symbol first second => .pair (.atom 40) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.termSymbol.put symbol) (.pair ((argumentsAt symbols n (S.termArity symbol)).put first) (.pair ((argumentsAt symbols n (S.termArity symbol)).put second) (.atom 0))))))
  | @RuleCode.lambdaCongruence _ _ n context domain body first second => .pair (.atom 41) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols (n + 1)).put first) (.pair ((termAt symbols (n + 1)).put second) (.atom 0)))))))
  | @RuleCode.applicationCongruence _ _ n context domain body firstFunction secondFunction firstArgument secondArgument => .pair (.atom 42) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put firstFunction) (.pair ((termAt symbols n).put secondFunction) (.pair ((termAt symbols n).put firstArgument) (.pair ((termAt symbols n).put secondArgument) (.atom 0)))))))))
  | @RuleCode.pairCongruence _ _ n context domain body firstLeft secondLeft firstRight secondRight => .pair (.atom 43) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put firstLeft) (.pair ((termAt symbols n).put secondLeft) (.pair ((termAt symbols n).put firstRight) (.pair ((termAt symbols n).put secondRight) (.atom 0)))))))))
  | @RuleCode.firstCongruence _ _ n context domain body first second => .pair (.atom 44) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.secondCongruence _ _ n context domain body first second => .pair (.atom 45) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.sigmaEliminationCongruence _ _ n context domain body motive firstBranch secondBranch firstPair secondPair => .pair (.atom 46) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((typeAt symbols (n + 1)).put motive) (.pair ((termAt symbols (n + 2)).put firstBranch) (.pair ((termAt symbols (n + 2)).put secondBranch) (.pair ((termAt symbols n).put firstPair) (.pair ((termAt symbols n).put secondPair) (.atom 0))))))))))
  | @RuleCode.lambdaAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody first second => .pair (.atom 47) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((termAt symbols (n + 1)).put first) (.pair ((termAt symbols (n + 1)).put second) (.atom 0)))))))))
  | @RuleCode.applicationAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument => .pair (.atom 48) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((termAt symbols n).put firstFunction) (.pair ((termAt symbols n).put secondFunction) (.pair ((termAt symbols n).put firstArgument) (.pair ((termAt symbols n).put secondArgument) (.atom 0)))))))))))
  | @RuleCode.pairAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight => .pair (.atom 49) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((termAt symbols n).put firstLeft) (.pair ((termAt symbols n).put secondLeft) (.pair ((termAt symbols n).put firstRight) (.pair ((termAt symbols n).put secondRight) (.atom 0)))))))))))
  | @RuleCode.firstAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody first second => .pair (.atom 50) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))))
  | @RuleCode.secondAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody first second => .pair (.atom 51) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))))
  | @RuleCode.sigmaEliminationAnnotationCongruence _ _ n context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair => .pair (.atom 52) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((typeAt symbols (n + 1)).put firstBody) (.pair ((typeAt symbols (n + 1)).put secondBody) (.pair ((typeAt symbols (n + 1)).put firstMotive) (.pair ((typeAt symbols (n + 1)).put secondMotive) (.pair ((termAt symbols (n + 2)).put firstBranch) (.pair ((termAt symbols (n + 2)).put secondBranch) (.pair ((termAt symbols n).put firstPair) (.pair ((termAt symbols n).put secondPair) (.atom 0)))))))))))))
  | @RuleCode.piBeta _ _ n context domain body term argument => .pair (.atom 53) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols (n + 1)).put term) (.pair ((termAt symbols n).put argument) (.atom 0)))))))
  | @RuleCode.piEta _ _ n context domain body function => .pair (.atom 54) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put function) (.atom 0))))))
  | @RuleCode.sigmaFirstBeta _ _ n context domain body first second => .pair (.atom 55) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.sigmaSecondBeta _ _ n context domain body first second => .pair (.atom 56) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.sigmaEta _ _ n context domain body pair => .pair (.atom 57) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((termAt symbols n).put pair) (.atom 0))))))
  | @RuleCode.sigmaEliminationBeta _ _ n context domain body motive branch first second => .pair (.atom 58) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((typeAt symbols (n + 1)).put motive) (.pair ((termAt symbols (n + 2)).put branch) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))))
  | @RuleCode.sigmaEliminationEta _ _ n context domain body motive term pair => .pair (.atom 59) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((typeAt symbols (n + 1)).put body) (.pair ((typeAt symbols (n + 1)).put motive) (.pair ((termAt symbols (n + 1)).put term) (.pair ((termAt symbols n).put pair) (.atom 0))))))))
  | @RuleCode.substituteTypeEquality _ _ n m source target substitution first second => .pair (.atom 60) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((typeAt symbols m).put first) (.pair ((typeAt symbols m).put second) (.atom 0))))))))
  | @RuleCode.substituteTermEquality _ _ n m source target substitution first second type => .pair (.atom 61) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((termAt symbols m).put first) (.pair ((termAt symbols m).put second) (.pair ((typeAt symbols m).put type) (.atom 0)))))))))
  | @RuleCode.substitutionReflexivity _ _ n m source target substitution => .pair (.atom 62) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.atom 0))))))
  | @RuleCode.substitutionSymmetry _ _ n m source target first second => .pair (.atom 63) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.atom 0)))))))
  | @RuleCode.substitutionTransitivity _ _ n m source target first middle last => .pair (.atom 64) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put middle) (.pair ((argumentsAt symbols n m).put last) (.atom 0))))))))
  | @RuleCode.substitutionExtendEquality _ _ n m source target type first second firstTerm secondTerm => .pair (.atom 65) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((typeAt symbols m).put type) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.pair ((termAt symbols n).put firstTerm) (.pair ((termAt symbols n).put secondTerm) (.atom 0))))))))))
  | @RuleCode.typeSubstitutionCongruence _ _ n m source target first second type => .pair (.atom 66) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.pair ((typeAt symbols m).put type) (.atom 0))))))))
  | @RuleCode.termSubstitutionCongruence _ _ n m source target first second term type => .pair (.atom 67) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.pair ((termAt symbols m).put term) (.pair ((typeAt symbols m).put type) (.atom 0)))))))))
  | @RuleCode.contextAssume _ _ n context predicate => .pair (.atom 68) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.propositionType _ _ n context => .pair (.atom 69) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.predicatePrimitive _ _ n context symbol arguments => .pair (.atom 70) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.predicateSymbol.put symbol) (.pair ((argumentsAt symbols n (S.predicateArity symbol)).put arguments) (.atom 0)))))
  | @RuleCode.truthFormation _ _ n context => .pair (.atom 71) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.falsehoodFormation _ _ n context => .pair (.atom 72) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.conjunctionFormation _ _ n context first second => .pair (.atom 73) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.disjunctionFormation _ _ n context first second => .pair (.atom 74) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.implicationFormation _ _ n context first second => .pair (.atom 75) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.universalFormation _ _ n context domain predicate => .pair (.atom 76) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.atom 0)))))
  | @RuleCode.existentialFormation _ _ n context domain predicate => .pair (.atom 77) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.atom 0)))))
  | @RuleCode.holdsFormation _ _ n context term => .pair (.atom 78) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put term) (.atom 0))))
  | @RuleCode.imageFormation _ _ n context type => .pair (.atom 79) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.atom 0))))
  | @RuleCode.quote _ _ n context predicate => .pair (.atom 80) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.comprehensionFormation _ _ n context domain predicate => .pair (.atom 81) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.atom 0)))))
  | @RuleCode.comprehensionIntroduction _ _ n context domain predicate value => .pair (.atom 82) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.comprehensionElimination _ _ n context domain predicate value => .pair (.atom 83) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.comprehensionGuard _ _ n context domain predicate value => .pair (.atom 84) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.comprehensionBeta _ _ n context domain predicate value => .pair (.atom 85) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.comprehensionEta _ _ n context domain predicate value => .pair (.atom 86) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.quoteHolds _ _ n context term => .pair (.atom 87) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put term) (.atom 0))))
  | @RuleCode.holdsQuote _ _ n context predicate => .pair (.atom 88) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.hypothesis _ _ n context predicate member => .pair (.atom 89) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.pair ((hypothesisAt symbols context predicate).put member) (.atom 0)))))
  | @RuleCode.truthIntroduction _ _ n context => .pair (.atom 90) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.atom 0)))
  | @RuleCode.falsehoodElimination _ _ n context predicate => .pair (.atom 91) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.conjunctionIntroduction _ _ n context first second => .pair (.atom 92) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.conjunctionFirst _ _ n context first second => .pair (.atom 93) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.conjunctionSecond _ _ n context first second => .pair (.atom 94) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.disjunctionFirst _ _ n context first second => .pair (.atom 95) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.disjunctionSecond _ _ n context first second => .pair (.atom 96) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.disjunctionElimination _ _ n context first second consequent => .pair (.atom 97) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.pair ((propAt symbols n).put consequent) (.atom 0))))))
  | @RuleCode.implicationIntroduction _ _ n context first second => .pair (.atom 98) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.implicationElimination _ _ n context first second => .pair (.atom 99) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.universalIntroduction _ _ n context domain predicate => .pair (.atom 100) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.atom 0)))))
  | @RuleCode.universalElimination _ _ n context domain predicate value => .pair (.atom 101) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.existentialIntroduction _ _ n context domain predicate value => .pair (.atom 102) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put value) (.atom 0))))))
  | @RuleCode.existentialElimination _ _ n context domain predicate consequent => .pair (.atom 103) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((propAt symbols n).put consequent) (.atom 0))))))
  | @RuleCode.imageIntroduction _ _ n context type value => .pair (.atom 104) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.pair ((termAt symbols n).put value) (.atom 0)))))
  | @RuleCode.imageElimination _ _ n context type predicate => .pair (.atom 105) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put type) (.pair ((propAt symbols n).put predicate) (.atom 0)))))
  | @RuleCode.substitutionWeakenAssumption _ _ n context predicate => .pair (.atom 106) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.substitutionIntoAssumption _ _ n m source target predicate substitution => .pair (.atom 107) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((propAt symbols m).put predicate) (.pair ((argumentsAt symbols n m).put substitution) (.atom 0)))))))
  | @RuleCode.substitutionLift _ _ n m source target type substitution => .pair (.atom 108) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((typeAt symbols m).put type) (.pair ((argumentsAt symbols n m).put substitution) (.atom 0)))))))
  | @RuleCode.substitutionAssumptionLift _ _ n m source target predicate substitution => .pair (.atom 109) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((propAt symbols m).put predicate) (.pair ((argumentsAt symbols n m).put substitution) (.atom 0)))))))
  | @RuleCode.substitutePredicate _ _ n m source target substitution predicate => .pair (.atom 110) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((propAt symbols m).put predicate) (.atom 0)))))))
  | @RuleCode.substituteEntailment _ _ n m source target substitution predicate => .pair (.atom 111) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((propAt symbols m).put predicate) (.atom 0)))))))
  | @RuleCode.transportPredicate _ _ n first second predicate => .pair (.atom 112) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((propAt symbols n).put predicate) (.atom 0)))))
  | @RuleCode.transportEntailment _ _ n first second predicate => .pair (.atom 113) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((propAt symbols n).put predicate) (.atom 0)))))
  | @RuleCode.predicateReflexivity _ _ n context predicate => .pair (.atom 114) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put predicate) (.atom 0))))
  | @RuleCode.predicateSymmetry _ _ n context first second => .pair (.atom 115) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.predicateTransitivity _ _ n context first middle last => .pair (.atom 116) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put middle) (.pair ((propAt symbols n).put last) (.atom 0))))))
  | @RuleCode.predicateExtensionality _ _ n context first second => .pair (.atom 117) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.entailmentConversion _ _ n context first second => .pair (.atom 118) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.contextAssumeEquality _ _ n first second firstPredicate secondPredicate => .pair (.atom 119) (.pair (.atom n) (.pair ((contextAt symbols n).put first) (.pair ((contextAt symbols n).put second) (.pair ((propAt symbols n).put firstPredicate) (.pair ((propAt symbols n).put secondPredicate) (.atom 0))))))
  | @RuleCode.comprehensionCongruence _ _ n context firstDomain secondDomain firstPredicate secondPredicate => .pair (.atom 120) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((propAt symbols (n + 1)).put firstPredicate) (.pair ((propAt symbols (n + 1)).put secondPredicate) (.atom 0)))))))
  | @RuleCode.quoteCongruence _ _ n context first second => .pair (.atom 121) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.atom 0)))))
  | @RuleCode.holdsCongruence _ _ n context first second => .pair (.atom 122) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))
  | @RuleCode.imageCongruence _ _ n context first second => .pair (.atom 123) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put first) (.pair ((typeAt symbols n).put second) (.atom 0)))))
  | @RuleCode.refineCongruence _ _ n context domain predicate first second => .pair (.atom 124) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.forgetCongruence _ _ n context domain predicate first second => .pair (.atom 125) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put domain) (.pair ((propAt symbols (n + 1)).put predicate) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))
  | @RuleCode.predicatePrimitiveCongruence _ _ n context symbol first second => .pair (.atom 126) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair (symbols.predicateSymbol.put symbol) (.pair ((argumentsAt symbols n (S.predicateArity symbol)).put first) (.pair ((argumentsAt symbols n (S.predicateArity symbol)).put second) (.atom 0))))))
  | @RuleCode.conjunctionCongruence _ _ n context first second third fourth => .pair (.atom 127) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.pair ((propAt symbols n).put third) (.pair ((propAt symbols n).put fourth) (.atom 0)))))))
  | @RuleCode.disjunctionCongruence _ _ n context first second third fourth => .pair (.atom 128) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.pair ((propAt symbols n).put third) (.pair ((propAt symbols n).put fourth) (.atom 0)))))))
  | @RuleCode.implicationCongruence _ _ n context first second third fourth => .pair (.atom 129) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((propAt symbols n).put first) (.pair ((propAt symbols n).put second) (.pair ((propAt symbols n).put third) (.pair ((propAt symbols n).put fourth) (.atom 0)))))))
  | @RuleCode.universalCongruence _ _ n context firstDomain secondDomain firstPredicate secondPredicate => .pair (.atom 130) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((propAt symbols (n + 1)).put firstPredicate) (.pair ((propAt symbols (n + 1)).put secondPredicate) (.atom 0)))))))
  | @RuleCode.existentialCongruence _ _ n context firstDomain secondDomain firstPredicate secondPredicate => .pair (.atom 131) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((propAt symbols (n + 1)).put firstPredicate) (.pair ((propAt symbols (n + 1)).put secondPredicate) (.atom 0)))))))
  | @RuleCode.substitutePredicateEquality _ _ n m source target substitution first second => .pair (.atom 132) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put substitution) (.pair ((propAt symbols m).put first) (.pair ((propAt symbols m).put second) (.atom 0))))))))
  | @RuleCode.predicateSubstitutionCongruence _ _ n m source target first second predicate => .pair (.atom 133) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.pair ((propAt symbols m).put predicate) (.atom 0))))))))
  | @RuleCode.refineAnnotationCongruence _ _ n context firstDomain secondDomain firstPredicate secondPredicate first second => .pair (.atom 134) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((propAt symbols (n + 1)).put firstPredicate) (.pair ((propAt symbols (n + 1)).put secondPredicate) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))))
  | @RuleCode.forgetAnnotationCongruence _ _ n context firstDomain secondDomain firstPredicate secondPredicate first second => .pair (.atom 135) (.pair (.atom n) (.pair ((contextAt symbols n).put context) (.pair ((typeAt symbols n).put firstDomain) (.pair ((typeAt symbols n).put secondDomain) (.pair ((propAt symbols (n + 1)).put firstPredicate) (.pair ((propAt symbols (n + 1)).put secondPredicate) (.pair ((termAt symbols n).put first) (.pair ((termAt symbols n).put second) (.atom 0)))))))))
  | @RuleCode.substitutionIntoAssumptionEquality _ _ n m source target predicate first second => .pair (.atom 136) (.pair (.atom n) (.pair (.atom m) (.pair ((contextAt symbols n).put source) (.pair ((contextAt symbols m).put target) (.pair ((propAt symbols m).put predicate) (.pair ((argumentsAt symbols n m).put first) (.pair ((argumentsAt symbols n m).put second) (.atom 0))))))))

def getPayload_contextNil : Data → Option (RuleCode D)
  | (.atom 0) => some .contextNil
  | _ => none

def getPayload_contextExtend : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      return .contextExtend context type
  | _ => none

def getPayload_variable : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (index) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let index ← (Codec.fin n).get index
      return .variable context index
  | _ => none

def getPayload_typeFamily : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (arguments) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.typeSymbol.get symbol
      let arguments ← (argumentsAt symbols n (S.typeArity symbol)).get arguments
      return .typeFamily context symbol arguments
  | _ => none

def getPayload_primitive : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (arguments) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.termSymbol.get symbol
      let arguments ← (argumentsAt symbols n (S.termArity symbol)).get arguments
      return .primitive context symbol arguments
  | _ => none

def getPayload_piFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      return .piFormation context domain body
  | _ => none

def getPayload_sigmaFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      return .sigmaFormation context domain body
  | _ => none

def getPayload_lambda : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (term) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let term ← (termAt symbols (n + 1)).get term
      return .lambda context domain body term
  | _ => none

def getPayload_application : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (function) (.pair (argument) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let function ← (termAt symbols n).get function
      let argument ← (termAt symbols n).get argument
      return .application context domain body function argument
  | _ => none

def getPayload_pairIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .pairIntroduction context domain body first second
  | _ => none

def getPayload_firstProjection : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (pair) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let pair ← (termAt symbols n).get pair
      return .firstProjection context domain body pair
  | _ => none

def getPayload_secondProjection : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (pair) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let pair ← (termAt symbols n).get pair
      return .secondProjection context domain body pair
  | _ => none

def getPayload_sigmaElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (motive) (.pair (branch) (.pair (pair) (.atom 0)))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let motive ← (typeAt symbols (n + 1)).get motive
      let branch ← (termAt symbols (n + 2)).get branch
      let pair ← (termAt symbols n).get pair
      return .sigmaElimination context domain body motive branch pair
  | _ => none

def getPayload_termConversion : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (term) (.pair (first) (.pair (second) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let term ← (termAt symbols n).get term
      let first ← (typeAt symbols n).get first
      let second ← (typeAt symbols n).get second
      return .termConversion context term first second
  | _ => none

def getPayload_substitutionNil : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .substitutionNil context
  | _ => none

def getPayload_substitutionExtend : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (type) (.pair (substitution) (.pair (term) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let type ← (typeAt symbols m).get type
      let substitution ← (argumentsAt symbols n m).get substitution
      let term ← (termAt symbols n).get term
      return .substitutionExtend source target type substitution term
  | _ => none

def getPayload_substitutionIdentity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .substitutionIdentity context
  | _ => none

def getPayload_substitutionCompose : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (.atom k) (.pair (source) (.pair (middle) (.pair (target) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let source ← (contextAt symbols n).get source
      let middle ← (contextAt symbols m).get middle
      let target ← (contextAt symbols k).get target
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols m k).get second
      return .substitutionCompose source middle target first second
  | _ => none

def getPayload_substitutionWeaken : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      return .substitutionWeaken context type
  | _ => none

def getPayload_substituteType : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (type) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let type ← (typeAt symbols m).get type
      return .substituteType source target substitution type
  | _ => none

def getPayload_substituteTerm : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (term) (.pair (type) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let term ← (termAt symbols m).get term
      let type ← (typeAt symbols m).get type
      return .substituteTerm source target substitution term type
  | _ => none

def getPayload_contextReflexivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .contextReflexivity context
  | _ => none

def getPayload_contextSymmetry : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.atom 0)))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      return .contextSymmetry first second
  | _ => none

def getPayload_contextTransitivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (middle) (.pair (last) (.atom 0))))) => do
      let first ← (contextAt symbols n).get first
      let middle ← (contextAt symbols n).get middle
      let last ← (contextAt symbols n).get last
      return .contextTransitivity first middle last
  | _ => none

def getPayload_contextExtendEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (firstType) (.pair (secondType) (.atom 0)))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let firstType ← (typeAt symbols n).get firstType
      let secondType ← (typeAt symbols n).get secondType
      return .contextExtendEquality first second firstType secondType
  | _ => none

def getPayload_transportType : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (type) (.atom 0))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let type ← (typeAt symbols n).get type
      return .transportType first second type
  | _ => none

def getPayload_transportTerm : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (term) (.pair (type) (.atom 0)))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let term ← (termAt symbols n).get term
      let type ← (typeAt symbols n).get type
      return .transportTerm first second term type
  | _ => none

def getPayload_transportSubstitution : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (source') (.pair (target) (.pair (target') (.pair (substitution) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let source' ← (contextAt symbols n).get source'
      let target ← (contextAt symbols m).get target
      let target' ← (contextAt symbols m).get target'
      let substitution ← (argumentsAt symbols n m).get substitution
      return .transportSubstitution source source' target target' substitution
  | _ => none

def getPayload_typeReflexivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      return .typeReflexivity context type
  | _ => none

def getPayload_typeSymmetry : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (typeAt symbols n).get first
      let second ← (typeAt symbols n).get second
      return .typeSymmetry context first second
  | _ => none

def getPayload_typeTransitivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (middle) (.pair (last) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (typeAt symbols n).get first
      let middle ← (typeAt symbols n).get middle
      let last ← (typeAt symbols n).get last
      return .typeTransitivity context first middle last
  | _ => none

def getPayload_termReflexivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (term) (.pair (type) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let term ← (termAt symbols n).get term
      let type ← (typeAt symbols n).get type
      return .termReflexivity context term type
  | _ => none

def getPayload_termSymmetry : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (type) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      let type ← (typeAt symbols n).get type
      return .termSymmetry context first second type
  | _ => none

def getPayload_termTransitivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (middle) (.pair (last) (.pair (type) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (termAt symbols n).get first
      let middle ← (termAt symbols n).get middle
      let last ← (termAt symbols n).get last
      let type ← (typeAt symbols n).get type
      return .termTransitivity context first middle last type
  | _ => none

def getPayload_equalityConversion : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (firstType) (.pair (secondType) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      let firstType ← (typeAt symbols n).get firstType
      let secondType ← (typeAt symbols n).get secondType
      return .equalityConversion context first second firstType secondType
  | _ => none

def getPayload_transportTypeEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.atom 0)))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols n).get target
      let first ← (typeAt symbols n).get first
      let second ← (typeAt symbols n).get second
      return .transportTypeEquality source target first second
  | _ => none

def getPayload_transportTermEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.pair (type) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols n).get target
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      let type ← (typeAt symbols n).get type
      return .transportTermEquality source target first second type
  | _ => none

def getPayload_piCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      return .piCongruence context firstDomain secondDomain firstBody secondBody
  | _ => none

def getPayload_sigmaCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      return .sigmaCongruence context firstDomain secondDomain firstBody secondBody
  | _ => none

def getPayload_familyCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (first) (.pair (second) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.typeSymbol.get symbol
      let first ← (argumentsAt symbols n (S.typeArity symbol)).get first
      let second ← (argumentsAt symbols n (S.typeArity symbol)).get second
      return .familyCongruence context symbol first second
  | _ => none

def getPayload_primitiveCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (first) (.pair (second) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.termSymbol.get symbol
      let first ← (argumentsAt symbols n (S.termArity symbol)).get first
      let second ← (argumentsAt symbols n (S.termArity symbol)).get second
      return .primitiveCongruence context symbol first second
  | _ => none

def getPayload_lambdaCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols (n + 1)).get first
      let second ← (termAt symbols (n + 1)).get second
      return .lambdaCongruence context domain body first second
  | _ => none

def getPayload_applicationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (firstFunction) (.pair (secondFunction) (.pair (firstArgument) (.pair (secondArgument) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let firstFunction ← (termAt symbols n).get firstFunction
      let secondFunction ← (termAt symbols n).get secondFunction
      let firstArgument ← (termAt symbols n).get firstArgument
      let secondArgument ← (termAt symbols n).get secondArgument
      return .applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument
  | _ => none

def getPayload_pairCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (firstLeft) (.pair (secondLeft) (.pair (firstRight) (.pair (secondRight) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let firstLeft ← (termAt symbols n).get firstLeft
      let secondLeft ← (termAt symbols n).get secondLeft
      let firstRight ← (termAt symbols n).get firstRight
      let secondRight ← (termAt symbols n).get secondRight
      return .pairCongruence context domain body firstLeft secondLeft firstRight secondRight
  | _ => none

def getPayload_firstCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .firstCongruence context domain body first second
  | _ => none

def getPayload_secondCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .secondCongruence context domain body first second
  | _ => none

def getPayload_sigmaEliminationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (motive) (.pair (firstBranch) (.pair (secondBranch) (.pair (firstPair) (.pair (secondPair) (.atom 0)))))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let motive ← (typeAt symbols (n + 1)).get motive
      let firstBranch ← (termAt symbols (n + 2)).get firstBranch
      let secondBranch ← (termAt symbols (n + 2)).get secondBranch
      let firstPair ← (termAt symbols n).get firstPair
      let secondPair ← (termAt symbols n).get secondPair
      return .sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair
  | _ => none

def getPayload_lambdaAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let first ← (termAt symbols (n + 1)).get first
      let second ← (termAt symbols (n + 1)).get second
      return .lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second
  | _ => none

def getPayload_applicationAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (firstFunction) (.pair (secondFunction) (.pair (firstArgument) (.pair (secondArgument) (.atom 0))))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let firstFunction ← (termAt symbols n).get firstFunction
      let secondFunction ← (termAt symbols n).get secondFunction
      let firstArgument ← (termAt symbols n).get firstArgument
      let secondArgument ← (termAt symbols n).get secondArgument
      return .applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument
  | _ => none

def getPayload_pairAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (firstLeft) (.pair (secondLeft) (.pair (firstRight) (.pair (secondRight) (.atom 0))))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let firstLeft ← (termAt symbols n).get firstLeft
      let secondLeft ← (termAt symbols n).get secondLeft
      let firstRight ← (termAt symbols n).get firstRight
      let secondRight ← (termAt symbols n).get secondRight
      return .pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight
  | _ => none

def getPayload_firstAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second
  | _ => none

def getPayload_secondAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second
  | _ => none

def getPayload_sigmaEliminationAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstBody) (.pair (secondBody) (.pair (firstMotive) (.pair (secondMotive) (.pair (firstBranch) (.pair (secondBranch) (.pair (firstPair) (.pair (secondPair) (.atom 0))))))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstBody ← (typeAt symbols (n + 1)).get firstBody
      let secondBody ← (typeAt symbols (n + 1)).get secondBody
      let firstMotive ← (typeAt symbols (n + 1)).get firstMotive
      let secondMotive ← (typeAt symbols (n + 1)).get secondMotive
      let firstBranch ← (termAt symbols (n + 2)).get firstBranch
      let secondBranch ← (termAt symbols (n + 2)).get secondBranch
      let firstPair ← (termAt symbols n).get firstPair
      let secondPair ← (termAt symbols n).get secondPair
      return .sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair
  | _ => none

def getPayload_piBeta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (term) (.pair (argument) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let term ← (termAt symbols (n + 1)).get term
      let argument ← (termAt symbols n).get argument
      return .piBeta context domain body term argument
  | _ => none

def getPayload_piEta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (function) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let function ← (termAt symbols n).get function
      return .piEta context domain body function
  | _ => none

def getPayload_sigmaFirstBeta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .sigmaFirstBeta context domain body first second
  | _ => none

def getPayload_sigmaSecondBeta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .sigmaSecondBeta context domain body first second
  | _ => none

def getPayload_sigmaEta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (pair) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let pair ← (termAt symbols n).get pair
      return .sigmaEta context domain body pair
  | _ => none

def getPayload_sigmaEliminationBeta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (motive) (.pair (branch) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let motive ← (typeAt symbols (n + 1)).get motive
      let branch ← (termAt symbols (n + 2)).get branch
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .sigmaEliminationBeta context domain body motive branch first second
  | _ => none

def getPayload_sigmaEliminationEta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (body) (.pair (motive) (.pair (term) (.pair (pair) (.atom 0)))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let body ← (typeAt symbols (n + 1)).get body
      let motive ← (typeAt symbols (n + 1)).get motive
      let term ← (termAt symbols (n + 1)).get term
      let pair ← (termAt symbols n).get pair
      return .sigmaEliminationEta context domain body motive term pair
  | _ => none

def getPayload_substituteTypeEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (first) (.pair (second) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let first ← (typeAt symbols m).get first
      let second ← (typeAt symbols m).get second
      return .substituteTypeEquality source target substitution first second
  | _ => none

def getPayload_substituteTermEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (first) (.pair (second) (.pair (type) (.atom 0))))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let first ← (termAt symbols m).get first
      let second ← (termAt symbols m).get second
      let type ← (typeAt symbols m).get type
      return .substituteTermEquality source target substitution first second type
  | _ => none

def getPayload_substitutionReflexivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.atom 0)))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      return .substitutionReflexivity source target substitution
  | _ => none

def getPayload_substitutionSymmetry : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      return .substitutionSymmetry source target first second
  | _ => none

def getPayload_substitutionTransitivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (first) (.pair (middle) (.pair (last) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let first ← (argumentsAt symbols n m).get first
      let middle ← (argumentsAt symbols n m).get middle
      let last ← (argumentsAt symbols n m).get last
      return .substitutionTransitivity source target first middle last
  | _ => none

def getPayload_substitutionExtendEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (type) (.pair (first) (.pair (second) (.pair (firstTerm) (.pair (secondTerm) (.atom 0)))))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let type ← (typeAt symbols m).get type
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      let firstTerm ← (termAt symbols n).get firstTerm
      let secondTerm ← (termAt symbols n).get secondTerm
      return .substitutionExtendEquality source target type first second firstTerm secondTerm
  | _ => none

def getPayload_typeSubstitutionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.pair (type) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      let type ← (typeAt symbols m).get type
      return .typeSubstitutionCongruence source target first second type
  | _ => none

def getPayload_termSubstitutionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.pair (term) (.pair (type) (.atom 0))))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      let term ← (termAt symbols m).get term
      let type ← (typeAt symbols m).get type
      return .termSubstitutionCongruence source target first second term type
  | _ => none

def getPayload_contextAssume : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .contextAssume context predicate
  | _ => none

def getPayload_propositionType : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .propositionType context
  | _ => none

def getPayload_predicatePrimitive : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (arguments) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.predicateSymbol.get symbol
      let arguments ← (argumentsAt symbols n (S.predicateArity symbol)).get arguments
      return .predicatePrimitive context symbol arguments
  | _ => none

def getPayload_truthFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .truthFormation context
  | _ => none

def getPayload_falsehoodFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .falsehoodFormation context
  | _ => none

def getPayload_conjunctionFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .conjunctionFormation context first second
  | _ => none

def getPayload_disjunctionFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .disjunctionFormation context first second
  | _ => none

def getPayload_implicationFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .implicationFormation context first second
  | _ => none

def getPayload_universalFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      return .universalFormation context domain predicate
  | _ => none

def getPayload_existentialFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      return .existentialFormation context domain predicate
  | _ => none

def getPayload_holdsFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (term) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let term ← (termAt symbols n).get term
      return .holdsFormation context term
  | _ => none

def getPayload_imageFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      return .imageFormation context type
  | _ => none

def getPayload_quote : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .quote context predicate
  | _ => none

def getPayload_comprehensionFormation : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      return .comprehensionFormation context domain predicate
  | _ => none

def getPayload_comprehensionIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .comprehensionIntroduction context domain predicate value
  | _ => none

def getPayload_comprehensionElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .comprehensionElimination context domain predicate value
  | _ => none

def getPayload_comprehensionGuard : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .comprehensionGuard context domain predicate value
  | _ => none

def getPayload_comprehensionBeta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .comprehensionBeta context domain predicate value
  | _ => none

def getPayload_comprehensionEta : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .comprehensionEta context domain predicate value
  | _ => none

def getPayload_quoteHolds : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (term) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let term ← (termAt symbols n).get term
      return .quoteHolds context term
  | _ => none

def getPayload_holdsQuote : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .holdsQuote context predicate
  | _ => none

def getPayload_hypothesis : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.pair (member) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      let member ← (hypothesisAt symbols context predicate).get member
      return .hypothesis context predicate member
  | _ => none

def getPayload_truthIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.atom 0))) => do
      let context ← (contextAt symbols n).get context
      return .truthIntroduction context
  | _ => none

def getPayload_falsehoodElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .falsehoodElimination context predicate
  | _ => none

def getPayload_conjunctionIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .conjunctionIntroduction context first second
  | _ => none

def getPayload_conjunctionFirst : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .conjunctionFirst context first second
  | _ => none

def getPayload_conjunctionSecond : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .conjunctionSecond context first second
  | _ => none

def getPayload_disjunctionFirst : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .disjunctionFirst context first second
  | _ => none

def getPayload_disjunctionSecond : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .disjunctionSecond context first second
  | _ => none

def getPayload_disjunctionElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (consequent) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      let consequent ← (propAt symbols n).get consequent
      return .disjunctionElimination context first second consequent
  | _ => none

def getPayload_implicationIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .implicationIntroduction context first second
  | _ => none

def getPayload_implicationElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .implicationElimination context first second
  | _ => none

def getPayload_universalIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      return .universalIntroduction context domain predicate
  | _ => none

def getPayload_universalElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .universalElimination context domain predicate value
  | _ => none

def getPayload_existentialIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (value) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let value ← (termAt symbols n).get value
      return .existentialIntroduction context domain predicate value
  | _ => none

def getPayload_existentialElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (consequent) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let consequent ← (propAt symbols n).get consequent
      return .existentialElimination context domain predicate consequent
  | _ => none

def getPayload_imageIntroduction : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.pair (value) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      let value ← (termAt symbols n).get value
      return .imageIntroduction context type value
  | _ => none

def getPayload_imageElimination : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (type) (.pair (predicate) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let type ← (typeAt symbols n).get type
      let predicate ← (propAt symbols n).get predicate
      return .imageElimination context type predicate
  | _ => none

def getPayload_substitutionWeakenAssumption : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .substitutionWeakenAssumption context predicate
  | _ => none

def getPayload_substitutionIntoAssumption : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (predicate) (.pair (substitution) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let predicate ← (propAt symbols m).get predicate
      let substitution ← (argumentsAt symbols n m).get substitution
      return .substitutionIntoAssumption source target predicate substitution
  | _ => none

def getPayload_substitutionLift : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (type) (.pair (substitution) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let type ← (typeAt symbols m).get type
      let substitution ← (argumentsAt symbols n m).get substitution
      return .substitutionLift source target type substitution
  | _ => none

def getPayload_substitutionAssumptionLift : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (predicate) (.pair (substitution) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let predicate ← (propAt symbols m).get predicate
      let substitution ← (argumentsAt symbols n m).get substitution
      return .substitutionAssumptionLift source target predicate substitution
  | _ => none

def getPayload_substitutePredicate : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (predicate) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let predicate ← (propAt symbols m).get predicate
      return .substitutePredicate source target substitution predicate
  | _ => none

def getPayload_substituteEntailment : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (predicate) (.atom 0))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let predicate ← (propAt symbols m).get predicate
      return .substituteEntailment source target substitution predicate
  | _ => none

def getPayload_transportPredicate : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (predicate) (.atom 0))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let predicate ← (propAt symbols n).get predicate
      return .transportPredicate first second predicate
  | _ => none

def getPayload_transportEntailment : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (predicate) (.atom 0))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let predicate ← (propAt symbols n).get predicate
      return .transportEntailment first second predicate
  | _ => none

def getPayload_predicateReflexivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (predicate) (.atom 0)))) => do
      let context ← (contextAt symbols n).get context
      let predicate ← (propAt symbols n).get predicate
      return .predicateReflexivity context predicate
  | _ => none

def getPayload_predicateSymmetry : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .predicateSymmetry context first second
  | _ => none

def getPayload_predicateTransitivity : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (middle) (.pair (last) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let middle ← (propAt symbols n).get middle
      let last ← (propAt symbols n).get last
      return .predicateTransitivity context first middle last
  | _ => none

def getPayload_predicateExtensionality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .predicateExtensionality context first second
  | _ => none

def getPayload_entailmentConversion : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .entailmentConversion context first second
  | _ => none

def getPayload_contextAssumeEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (first) (.pair (second) (.pair (firstPredicate) (.pair (secondPredicate) (.atom 0)))))) => do
      let first ← (contextAt symbols n).get first
      let second ← (contextAt symbols n).get second
      let firstPredicate ← (propAt symbols n).get firstPredicate
      let secondPredicate ← (propAt symbols n).get secondPredicate
      return .contextAssumeEquality first second firstPredicate secondPredicate
  | _ => none

def getPayload_comprehensionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstPredicate) (.pair (secondPredicate) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstPredicate ← (propAt symbols (n + 1)).get firstPredicate
      let secondPredicate ← (propAt symbols (n + 1)).get secondPredicate
      return .comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate
  | _ => none

def getPayload_quoteCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      return .quoteCongruence context first second
  | _ => none

def getPayload_holdsCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .holdsCongruence context first second
  | _ => none

def getPayload_imageCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.atom 0))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (typeAt symbols n).get first
      let second ← (typeAt symbols n).get second
      return .imageCongruence context first second
  | _ => none

def getPayload_refineCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .refineCongruence context domain predicate first second
  | _ => none

def getPayload_forgetCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (domain) (.pair (predicate) (.pair (first) (.pair (second) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let domain ← (typeAt symbols n).get domain
      let predicate ← (propAt symbols (n + 1)).get predicate
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .forgetCongruence context domain predicate first second
  | _ => none

def getPayload_predicatePrimitiveCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (symbol) (.pair (first) (.pair (second) (.atom 0)))))) => do
      let context ← (contextAt symbols n).get context
      let symbol ← symbols.predicateSymbol.get symbol
      let first ← (argumentsAt symbols n (S.predicateArity symbol)).get first
      let second ← (argumentsAt symbols n (S.predicateArity symbol)).get second
      return .predicatePrimitiveCongruence context symbol first second
  | _ => none

def getPayload_conjunctionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (third) (.pair (fourth) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      let third ← (propAt symbols n).get third
      let fourth ← (propAt symbols n).get fourth
      return .conjunctionCongruence context first second third fourth
  | _ => none

def getPayload_disjunctionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (third) (.pair (fourth) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      let third ← (propAt symbols n).get third
      let fourth ← (propAt symbols n).get fourth
      return .disjunctionCongruence context first second third fourth
  | _ => none

def getPayload_implicationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (first) (.pair (second) (.pair (third) (.pair (fourth) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let first ← (propAt symbols n).get first
      let second ← (propAt symbols n).get second
      let third ← (propAt symbols n).get third
      let fourth ← (propAt symbols n).get fourth
      return .implicationCongruence context first second third fourth
  | _ => none

def getPayload_universalCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstPredicate) (.pair (secondPredicate) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstPredicate ← (propAt symbols (n + 1)).get firstPredicate
      let secondPredicate ← (propAt symbols (n + 1)).get secondPredicate
      return .universalCongruence context firstDomain secondDomain firstPredicate secondPredicate
  | _ => none

def getPayload_existentialCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstPredicate) (.pair (secondPredicate) (.atom 0))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstPredicate ← (propAt symbols (n + 1)).get firstPredicate
      let secondPredicate ← (propAt symbols (n + 1)).get secondPredicate
      return .existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate
  | _ => none

def getPayload_substitutePredicateEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (substitution) (.pair (first) (.pair (second) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let substitution ← (argumentsAt symbols n m).get substitution
      let first ← (propAt symbols m).get first
      let second ← (propAt symbols m).get second
      return .substitutePredicateEquality source target substitution first second
  | _ => none

def getPayload_predicateSubstitutionCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (first) (.pair (second) (.pair (predicate) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      let predicate ← (propAt symbols m).get predicate
      return .predicateSubstitutionCongruence source target first second predicate
  | _ => none

def getPayload_refineAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstPredicate) (.pair (secondPredicate) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstPredicate ← (propAt symbols (n + 1)).get firstPredicate
      let secondPredicate ← (propAt symbols (n + 1)).get secondPredicate
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second
  | _ => none

def getPayload_forgetAnnotationCongruence : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (context) (.pair (firstDomain) (.pair (secondDomain) (.pair (firstPredicate) (.pair (secondPredicate) (.pair (first) (.pair (second) (.atom 0))))))))) => do
      let context ← (contextAt symbols n).get context
      let firstDomain ← (typeAt symbols n).get firstDomain
      let secondDomain ← (typeAt symbols n).get secondDomain
      let firstPredicate ← (propAt symbols (n + 1)).get firstPredicate
      let secondPredicate ← (propAt symbols (n + 1)).get secondPredicate
      let first ← (termAt symbols n).get first
      let second ← (termAt symbols n).get second
      return .forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second
  | _ => none

def getPayload_substitutionIntoAssumptionEquality : Data → Option (RuleCode D)
  | (.pair (.atom n) (.pair (.atom m) (.pair (source) (.pair (target) (.pair (predicate) (.pair (first) (.pair (second) (.atom 0)))))))) => do
      let source ← (contextAt symbols n).get source
      let target ← (contextAt symbols m).get target
      let predicate ← (propAt symbols m).get predicate
      let first ← (argumentsAt symbols n m).get first
      let second ← (argumentsAt symbols n m).get second
      return .substitutionIntoAssumptionEquality source target predicate first second
  | _ => none

def getRuleGroup0 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_contextNil D
  | 1 => getPayload_contextExtend symbols D
  | 2 => getPayload_variable symbols D
  | 3 => getPayload_typeFamily symbols D
  | 4 => getPayload_primitive symbols D
  | 5 => getPayload_piFormation symbols D
  | 6 => getPayload_sigmaFormation symbols D
  | 7 => getPayload_lambda symbols D
  | 8 => getPayload_application symbols D
  | 9 => getPayload_pairIntroduction symbols D
  | 10 => getPayload_firstProjection symbols D
  | 11 => getPayload_secondProjection symbols D
  | 12 => getPayload_sigmaElimination symbols D
  | 13 => getPayload_termConversion symbols D
  | 14 => getPayload_substitutionNil symbols D
  | 15 => getPayload_substitutionExtend symbols D
  | _ => fun _ => none

def getRuleGroup1 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_substitutionIdentity symbols D
  | 1 => getPayload_substitutionCompose symbols D
  | 2 => getPayload_substitutionWeaken symbols D
  | 3 => getPayload_substituteType symbols D
  | 4 => getPayload_substituteTerm symbols D
  | 5 => getPayload_contextReflexivity symbols D
  | 6 => getPayload_contextSymmetry symbols D
  | 7 => getPayload_contextTransitivity symbols D
  | 8 => getPayload_contextExtendEquality symbols D
  | 9 => getPayload_transportType symbols D
  | 10 => getPayload_transportTerm symbols D
  | 11 => getPayload_transportSubstitution symbols D
  | 12 => getPayload_typeReflexivity symbols D
  | 13 => getPayload_typeSymmetry symbols D
  | 14 => getPayload_typeTransitivity symbols D
  | 15 => getPayload_termReflexivity symbols D
  | _ => fun _ => none

def getRuleGroup2 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_termSymmetry symbols D
  | 1 => getPayload_termTransitivity symbols D
  | 2 => getPayload_equalityConversion symbols D
  | 3 => getPayload_transportTypeEquality symbols D
  | 4 => getPayload_transportTermEquality symbols D
  | 5 => getPayload_piCongruence symbols D
  | 6 => getPayload_sigmaCongruence symbols D
  | 7 => getPayload_familyCongruence symbols D
  | 8 => getPayload_primitiveCongruence symbols D
  | 9 => getPayload_lambdaCongruence symbols D
  | 10 => getPayload_applicationCongruence symbols D
  | 11 => getPayload_pairCongruence symbols D
  | 12 => getPayload_firstCongruence symbols D
  | 13 => getPayload_secondCongruence symbols D
  | 14 => getPayload_sigmaEliminationCongruence symbols D
  | 15 => getPayload_lambdaAnnotationCongruence symbols D
  | _ => fun _ => none

def getRuleGroup3 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_applicationAnnotationCongruence symbols D
  | 1 => getPayload_pairAnnotationCongruence symbols D
  | 2 => getPayload_firstAnnotationCongruence symbols D
  | 3 => getPayload_secondAnnotationCongruence symbols D
  | 4 => getPayload_sigmaEliminationAnnotationCongruence symbols D
  | 5 => getPayload_piBeta symbols D
  | 6 => getPayload_piEta symbols D
  | 7 => getPayload_sigmaFirstBeta symbols D
  | 8 => getPayload_sigmaSecondBeta symbols D
  | 9 => getPayload_sigmaEta symbols D
  | 10 => getPayload_sigmaEliminationBeta symbols D
  | 11 => getPayload_sigmaEliminationEta symbols D
  | 12 => getPayload_substituteTypeEquality symbols D
  | 13 => getPayload_substituteTermEquality symbols D
  | 14 => getPayload_substitutionReflexivity symbols D
  | 15 => getPayload_substitutionSymmetry symbols D
  | _ => fun _ => none

def getRuleGroup4 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_substitutionTransitivity symbols D
  | 1 => getPayload_substitutionExtendEquality symbols D
  | 2 => getPayload_typeSubstitutionCongruence symbols D
  | 3 => getPayload_termSubstitutionCongruence symbols D
  | 4 => getPayload_contextAssume symbols D
  | 5 => getPayload_propositionType symbols D
  | 6 => getPayload_predicatePrimitive symbols D
  | 7 => getPayload_truthFormation symbols D
  | 8 => getPayload_falsehoodFormation symbols D
  | 9 => getPayload_conjunctionFormation symbols D
  | 10 => getPayload_disjunctionFormation symbols D
  | 11 => getPayload_implicationFormation symbols D
  | 12 => getPayload_universalFormation symbols D
  | 13 => getPayload_existentialFormation symbols D
  | 14 => getPayload_holdsFormation symbols D
  | 15 => getPayload_imageFormation symbols D
  | _ => fun _ => none

def getRuleGroup5 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_quote symbols D
  | 1 => getPayload_comprehensionFormation symbols D
  | 2 => getPayload_comprehensionIntroduction symbols D
  | 3 => getPayload_comprehensionElimination symbols D
  | 4 => getPayload_comprehensionGuard symbols D
  | 5 => getPayload_comprehensionBeta symbols D
  | 6 => getPayload_comprehensionEta symbols D
  | 7 => getPayload_quoteHolds symbols D
  | 8 => getPayload_holdsQuote symbols D
  | 9 => getPayload_hypothesis symbols D
  | 10 => getPayload_truthIntroduction symbols D
  | 11 => getPayload_falsehoodElimination symbols D
  | 12 => getPayload_conjunctionIntroduction symbols D
  | 13 => getPayload_conjunctionFirst symbols D
  | 14 => getPayload_conjunctionSecond symbols D
  | 15 => getPayload_disjunctionFirst symbols D
  | _ => fun _ => none

def getRuleGroup6 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_disjunctionSecond symbols D
  | 1 => getPayload_disjunctionElimination symbols D
  | 2 => getPayload_implicationIntroduction symbols D
  | 3 => getPayload_implicationElimination symbols D
  | 4 => getPayload_universalIntroduction symbols D
  | 5 => getPayload_universalElimination symbols D
  | 6 => getPayload_existentialIntroduction symbols D
  | 7 => getPayload_existentialElimination symbols D
  | 8 => getPayload_imageIntroduction symbols D
  | 9 => getPayload_imageElimination symbols D
  | 10 => getPayload_substitutionWeakenAssumption symbols D
  | 11 => getPayload_substitutionIntoAssumption symbols D
  | 12 => getPayload_substitutionLift symbols D
  | 13 => getPayload_substitutionAssumptionLift symbols D
  | 14 => getPayload_substitutePredicate symbols D
  | 15 => getPayload_substituteEntailment symbols D
  | _ => fun _ => none

def getRuleGroup7 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_transportPredicate symbols D
  | 1 => getPayload_transportEntailment symbols D
  | 2 => getPayload_predicateReflexivity symbols D
  | 3 => getPayload_predicateSymmetry symbols D
  | 4 => getPayload_predicateTransitivity symbols D
  | 5 => getPayload_predicateExtensionality symbols D
  | 6 => getPayload_entailmentConversion symbols D
  | 7 => getPayload_contextAssumeEquality symbols D
  | 8 => getPayload_comprehensionCongruence symbols D
  | 9 => getPayload_quoteCongruence symbols D
  | 10 => getPayload_holdsCongruence symbols D
  | 11 => getPayload_imageCongruence symbols D
  | 12 => getPayload_refineCongruence symbols D
  | 13 => getPayload_forgetCongruence symbols D
  | 14 => getPayload_predicatePrimitiveCongruence symbols D
  | 15 => getPayload_conjunctionCongruence symbols D
  | _ => fun _ => none

def getRuleGroup8 : Nat → Data → Option (RuleCode D)
  | 0 => getPayload_disjunctionCongruence symbols D
  | 1 => getPayload_implicationCongruence symbols D
  | 2 => getPayload_universalCongruence symbols D
  | 3 => getPayload_existentialCongruence symbols D
  | 4 => getPayload_substitutePredicateEquality symbols D
  | 5 => getPayload_predicateSubstitutionCongruence symbols D
  | 6 => getPayload_refineAnnotationCongruence symbols D
  | 7 => getPayload_forgetAnnotationCongruence symbols D
  | 8 => getPayload_substitutionIntoAssumptionEquality symbols D
  | _ => fun _ => none

def getRule : Data → Option (RuleCode D)
  | .pair (.atom tag) payload =>
      if tag < 16 then getRuleGroup0 symbols D (tag - 0) payload
      else if tag < 32 then getRuleGroup1 symbols D (tag - 16) payload
      else if tag < 48 then getRuleGroup2 symbols D (tag - 32) payload
      else if tag < 64 then getRuleGroup3 symbols D (tag - 48) payload
      else if tag < 80 then getRuleGroup4 symbols D (tag - 64) payload
      else if tag < 96 then getRuleGroup5 symbols D (tag - 80) payload
      else if tag < 112 then getRuleGroup6 symbols D (tag - 96) payload
      else if tag < 128 then getRuleGroup7 symbols D (tag - 112) payload
      else getRuleGroup8 symbols D (tag - 128) payload
  | _ => none

theorem roundtrip_contextNil  :
    getRule symbols D (putRule symbols D (RuleCode.contextNil)) = some (RuleCode.contextNil) := by
  rfl

theorem roundtrip_contextExtend { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextExtend context type)) = some (RuleCode.contextExtend context type) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_contextExtend, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_variable { n : Nat } (context : ContextExpr S n) (index : Fin n) :
    getRule symbols D (putRule symbols D (RuleCode.variable context index)) = some (RuleCode.variable context index) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_variable, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_typeFamily { n : Nat } (context : ContextExpr S n) (symbol : S.TypeSymbol) (arguments : Substitution S (S.typeArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.typeFamily context symbol arguments)) = some (RuleCode.typeFamily context symbol arguments) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_typeFamily, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_primitive { n : Nat } (context : ContextExpr S n) (symbol : S.TermSymbol) (arguments : Substitution S (S.termArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.primitive context symbol arguments)) = some (RuleCode.primitive context symbol arguments) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_primitive, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_piFormation { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.piFormation context domain body)) = some (RuleCode.piFormation context domain body) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_piFormation, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaFormation { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaFormation context domain body)) = some (RuleCode.sigmaFormation context domain body) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_sigmaFormation, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_lambda { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (term : TermExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.lambda context domain body term)) = some (RuleCode.lambda context domain body term) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_lambda, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_application { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (function : TermExpr S n) (argument : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.application context domain body function argument)) = some (RuleCode.application context domain body function argument) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_application, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_pairIntroduction { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.pairIntroduction context domain body first second)) = some (RuleCode.pairIntroduction context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_pairIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_firstProjection { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (pair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.firstProjection context domain body pair)) = some (RuleCode.firstProjection context domain body pair) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_firstProjection, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_secondProjection { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (pair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.secondProjection context domain body pair)) = some (RuleCode.secondProjection context domain body pair) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_secondProjection, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaElimination { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (motive : TypeExpr S (n + 1)) (branch : TermExpr S (n + 2)) (pair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaElimination context domain body motive branch pair)) = some (RuleCode.sigmaElimination context domain body motive branch pair) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_sigmaElimination, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_termConversion { n : Nat } (context : ContextExpr S n) (term : TermExpr S n) (first : TypeExpr S n) (second : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.termConversion context term first second)) = some (RuleCode.termConversion context term first second) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_termConversion, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionNil { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionNil context)) = some (RuleCode.substitutionNil context) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_substitutionNil, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionExtend { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (type : TypeExpr S m) (substitution : Substitution S m n) (term : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionExtend source target type substitution term)) = some (RuleCode.substitutionExtend source target type substitution term) := by
  simp only [putRule, getRule, getRuleGroup0, getPayload_substitutionExtend, Nat.reduceLT, Nat.reduceSub, if_true, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionIdentity { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionIdentity context)) = some (RuleCode.substitutionIdentity context) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_substitutionIdentity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionCompose { n : Nat } { m : Nat } { k : Nat } (source : ContextExpr S n) (middle : ContextExpr S m) (target : ContextExpr S k) (first : Substitution S m n) (second : Substitution S k m) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionCompose source middle target first second)) = some (RuleCode.substitutionCompose source middle target first second) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_substitutionCompose, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionWeaken { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionWeaken context type)) = some (RuleCode.substitutionWeaken context type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_substitutionWeaken, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substituteType { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (type : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substituteType source target substitution type)) = some (RuleCode.substituteType source target substitution type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_substituteType, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substituteTerm { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (term : TermExpr S m) (type : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substituteTerm source target substitution term type)) = some (RuleCode.substituteTerm source target substitution term type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_substituteTerm, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextReflexivity { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextReflexivity context)) = some (RuleCode.contextReflexivity context) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_contextReflexivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextSymmetry { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextSymmetry first second)) = some (RuleCode.contextSymmetry first second) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_contextSymmetry, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextTransitivity { n : Nat } (first : ContextExpr S n) (middle : ContextExpr S n) (last : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextTransitivity first middle last)) = some (RuleCode.contextTransitivity first middle last) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_contextTransitivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextExtendEquality { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (firstType : TypeExpr S n) (secondType : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextExtendEquality first second firstType secondType)) = some (RuleCode.contextExtendEquality first second firstType secondType) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_contextExtendEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportType { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportType first second type)) = some (RuleCode.transportType first second type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_transportType, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportTerm { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportTerm first second term type)) = some (RuleCode.transportTerm first second term type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_transportTerm, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportSubstitution { n : Nat } { m : Nat } (source : ContextExpr S n) (source' : ContextExpr S n) (target : ContextExpr S m) (target' : ContextExpr S m) (substitution : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.transportSubstitution source source' target target' substitution)) = some (RuleCode.transportSubstitution source source' target target' substitution) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_transportSubstitution, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_typeReflexivity { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.typeReflexivity context type)) = some (RuleCode.typeReflexivity context type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_typeReflexivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_typeSymmetry { n : Nat } (context : ContextExpr S n) (first : TypeExpr S n) (second : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.typeSymmetry context first second)) = some (RuleCode.typeSymmetry context first second) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_typeSymmetry, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_typeTransitivity { n : Nat } (context : ContextExpr S n) (first : TypeExpr S n) (middle : TypeExpr S n) (last : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.typeTransitivity context first middle last)) = some (RuleCode.typeTransitivity context first middle last) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_typeTransitivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_termReflexivity { n : Nat } (context : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.termReflexivity context term type)) = some (RuleCode.termReflexivity context term type) := by
  simp only [putRule, getRule, getRuleGroup1, getPayload_termReflexivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_termSymmetry { n : Nat } (context : ContextExpr S n) (first : TermExpr S n) (second : TermExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.termSymmetry context first second type)) = some (RuleCode.termSymmetry context first second type) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_termSymmetry, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_termTransitivity { n : Nat } (context : ContextExpr S n) (first : TermExpr S n) (middle : TermExpr S n) (last : TermExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.termTransitivity context first middle last type)) = some (RuleCode.termTransitivity context first middle last type) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_termTransitivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_equalityConversion { n : Nat } (context : ContextExpr S n) (first : TermExpr S n) (second : TermExpr S n) (firstType : TypeExpr S n) (secondType : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.equalityConversion context first second firstType secondType)) = some (RuleCode.equalityConversion context first second firstType secondType) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_equalityConversion, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportTypeEquality { n : Nat } (source : ContextExpr S n) (target : ContextExpr S n) (first : TypeExpr S n) (second : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportTypeEquality source target first second)) = some (RuleCode.transportTypeEquality source target first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_transportTypeEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportTermEquality { n : Nat } (source : ContextExpr S n) (target : ContextExpr S n) (first : TermExpr S n) (second : TermExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportTermEquality source target first second type)) = some (RuleCode.transportTermEquality source target first second type) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_transportTermEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_piCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.piCongruence context firstDomain secondDomain firstBody secondBody)) = some (RuleCode.piCongruence context firstDomain secondDomain firstBody secondBody) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_piCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaCongruence context firstDomain secondDomain firstBody secondBody)) = some (RuleCode.sigmaCongruence context firstDomain secondDomain firstBody secondBody) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_sigmaCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_familyCongruence { n : Nat } (context : ContextExpr S n) (symbol : S.TypeSymbol) (first : Substitution S (S.typeArity symbol) n) (second : Substitution S (S.typeArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.familyCongruence context symbol first second)) = some (RuleCode.familyCongruence context symbol first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_familyCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_primitiveCongruence { n : Nat } (context : ContextExpr S n) (symbol : S.TermSymbol) (first : Substitution S (S.termArity symbol) n) (second : Substitution S (S.termArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.primitiveCongruence context symbol first second)) = some (RuleCode.primitiveCongruence context symbol first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_primitiveCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_lambdaCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S (n + 1)) (second : TermExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.lambdaCongruence context domain body first second)) = some (RuleCode.lambdaCongruence context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_lambdaCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_applicationCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (firstFunction : TermExpr S n) (secondFunction : TermExpr S n) (firstArgument : TermExpr S n) (secondArgument : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument)) = some (RuleCode.applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_applicationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_pairCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (firstLeft : TermExpr S n) (secondLeft : TermExpr S n) (firstRight : TermExpr S n) (secondRight : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.pairCongruence context domain body firstLeft secondLeft firstRight secondRight)) = some (RuleCode.pairCongruence context domain body firstLeft secondLeft firstRight secondRight) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_pairCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_firstCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.firstCongruence context domain body first second)) = some (RuleCode.firstCongruence context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_firstCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_secondCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.secondCongruence context domain body first second)) = some (RuleCode.secondCongruence context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_secondCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaEliminationCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (motive : TypeExpr S (n + 1)) (firstBranch : TermExpr S (n + 2)) (secondBranch : TermExpr S (n + 2)) (firstPair : TermExpr S n) (secondPair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair)) = some (RuleCode.sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_sigmaEliminationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_lambdaAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (first : TermExpr S (n + 1)) (second : TermExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second)) = some (RuleCode.lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second) := by
  simp only [putRule, getRule, getRuleGroup2, getPayload_lambdaAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_applicationAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (firstFunction : TermExpr S n) (secondFunction : TermExpr S n) (firstArgument : TermExpr S n) (secondArgument : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument)) = some (RuleCode.applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_applicationAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_pairAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (firstLeft : TermExpr S n) (secondLeft : TermExpr S n) (firstRight : TermExpr S n) (secondRight : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight)) = some (RuleCode.pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_pairAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_firstAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second)) = some (RuleCode.firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_firstAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_secondAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second)) = some (RuleCode.secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_secondAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaEliminationAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstBody : TypeExpr S (n + 1)) (secondBody : TypeExpr S (n + 1)) (firstMotive : TypeExpr S (n + 1)) (secondMotive : TypeExpr S (n + 1)) (firstBranch : TermExpr S (n + 2)) (secondBranch : TermExpr S (n + 2)) (firstPair : TermExpr S n) (secondPair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair)) = some (RuleCode.sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaEliminationAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_piBeta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (term : TermExpr S (n + 1)) (argument : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.piBeta context domain body term argument)) = some (RuleCode.piBeta context domain body term argument) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_piBeta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_piEta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (function : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.piEta context domain body function)) = some (RuleCode.piEta context domain body function) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_piEta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaFirstBeta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaFirstBeta context domain body first second)) = some (RuleCode.sigmaFirstBeta context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaFirstBeta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaSecondBeta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaSecondBeta context domain body first second)) = some (RuleCode.sigmaSecondBeta context domain body first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaSecondBeta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaEta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (pair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaEta context domain body pair)) = some (RuleCode.sigmaEta context domain body pair) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaEta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaEliminationBeta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (motive : TypeExpr S (n + 1)) (branch : TermExpr S (n + 2)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaEliminationBeta context domain body motive branch first second)) = some (RuleCode.sigmaEliminationBeta context domain body motive branch first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaEliminationBeta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_sigmaEliminationEta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (motive : TypeExpr S (n + 1)) (term : TermExpr S (n + 1)) (pair : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.sigmaEliminationEta context domain body motive term pair)) = some (RuleCode.sigmaEliminationEta context domain body motive term pair) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_sigmaEliminationEta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substituteTypeEquality { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (first : TypeExpr S m) (second : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substituteTypeEquality source target substitution first second)) = some (RuleCode.substituteTypeEquality source target substitution first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_substituteTypeEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substituteTermEquality { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (first : TermExpr S m) (second : TermExpr S m) (type : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substituteTermEquality source target substitution first second type)) = some (RuleCode.substituteTermEquality source target substitution first second type) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_substituteTermEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionReflexivity { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionReflexivity source target substitution)) = some (RuleCode.substitutionReflexivity source target substitution) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_substitutionReflexivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionSymmetry { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (first : Substitution S m n) (second : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionSymmetry source target first second)) = some (RuleCode.substitutionSymmetry source target first second) := by
  simp only [putRule, getRule, getRuleGroup3, getPayload_substitutionSymmetry, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionTransitivity { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (first : Substitution S m n) (middle : Substitution S m n) (last : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionTransitivity source target first middle last)) = some (RuleCode.substitutionTransitivity source target first middle last) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_substitutionTransitivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionExtendEquality { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (type : TypeExpr S m) (first : Substitution S m n) (second : Substitution S m n) (firstTerm : TermExpr S n) (secondTerm : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionExtendEquality source target type first second firstTerm secondTerm)) = some (RuleCode.substitutionExtendEquality source target type first second firstTerm secondTerm) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_substitutionExtendEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_typeSubstitutionCongruence { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (first : Substitution S m n) (second : Substitution S m n) (type : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.typeSubstitutionCongruence source target first second type)) = some (RuleCode.typeSubstitutionCongruence source target first second type) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_typeSubstitutionCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_termSubstitutionCongruence { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (first : Substitution S m n) (second : Substitution S m n) (term : TermExpr S m) (type : TypeExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.termSubstitutionCongruence source target first second term type)) = some (RuleCode.termSubstitutionCongruence source target first second term type) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_termSubstitutionCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextAssume { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextAssume context predicate)) = some (RuleCode.contextAssume context predicate) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_contextAssume, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_propositionType { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.propositionType context)) = some (RuleCode.propositionType context) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_propositionType, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicatePrimitive { n : Nat } (context : ContextExpr S n) (symbol : S.PredicateSymbol) (arguments : Substitution S (S.predicateArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.predicatePrimitive context symbol arguments)) = some (RuleCode.predicatePrimitive context symbol arguments) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_predicatePrimitive, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_truthFormation { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.truthFormation context)) = some (RuleCode.truthFormation context) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_truthFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_falsehoodFormation { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.falsehoodFormation context)) = some (RuleCode.falsehoodFormation context) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_falsehoodFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_conjunctionFormation { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.conjunctionFormation context first second)) = some (RuleCode.conjunctionFormation context first second) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_conjunctionFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_disjunctionFormation { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.disjunctionFormation context first second)) = some (RuleCode.disjunctionFormation context first second) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_disjunctionFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_implicationFormation { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.implicationFormation context first second)) = some (RuleCode.implicationFormation context first second) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_implicationFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_universalFormation { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.universalFormation context domain predicate)) = some (RuleCode.universalFormation context domain predicate) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_universalFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_existentialFormation { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.existentialFormation context domain predicate)) = some (RuleCode.existentialFormation context domain predicate) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_existentialFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_holdsFormation { n : Nat } (context : ContextExpr S n) (term : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.holdsFormation context term)) = some (RuleCode.holdsFormation context term) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_holdsFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_imageFormation { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.imageFormation context type)) = some (RuleCode.imageFormation context type) := by
  simp only [putRule, getRule, getRuleGroup4, getPayload_imageFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_quote { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.quote context predicate)) = some (RuleCode.quote context predicate) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_quote, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionFormation { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionFormation context domain predicate)) = some (RuleCode.comprehensionFormation context domain predicate) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionFormation, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionIntroduction { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionIntroduction context domain predicate value)) = some (RuleCode.comprehensionIntroduction context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionElimination { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionElimination context domain predicate value)) = some (RuleCode.comprehensionElimination context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionGuard { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionGuard context domain predicate value)) = some (RuleCode.comprehensionGuard context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionGuard, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionBeta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionBeta context domain predicate value)) = some (RuleCode.comprehensionBeta context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionBeta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionEta { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionEta context domain predicate value)) = some (RuleCode.comprehensionEta context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_comprehensionEta, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_quoteHolds { n : Nat } (context : ContextExpr S n) (term : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.quoteHolds context term)) = some (RuleCode.quoteHolds context term) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_quoteHolds, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_holdsQuote { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.holdsQuote context predicate)) = some (RuleCode.holdsQuote context predicate) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_holdsQuote, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_hypothesis { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) (member : Hypothesis context predicate) :
    getRule symbols D (putRule symbols D (RuleCode.hypothesis context predicate member)) = some (RuleCode.hypothesis context predicate member) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_hypothesis, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_truthIntroduction { n : Nat } (context : ContextExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.truthIntroduction context)) = some (RuleCode.truthIntroduction context) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_truthIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_falsehoodElimination { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.falsehoodElimination context predicate)) = some (RuleCode.falsehoodElimination context predicate) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_falsehoodElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_conjunctionIntroduction { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.conjunctionIntroduction context first second)) = some (RuleCode.conjunctionIntroduction context first second) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_conjunctionIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_conjunctionFirst { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.conjunctionFirst context first second)) = some (RuleCode.conjunctionFirst context first second) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_conjunctionFirst, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_conjunctionSecond { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.conjunctionSecond context first second)) = some (RuleCode.conjunctionSecond context first second) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_conjunctionSecond, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_disjunctionFirst { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.disjunctionFirst context first second)) = some (RuleCode.disjunctionFirst context first second) := by
  simp only [putRule, getRule, getRuleGroup5, getPayload_disjunctionFirst, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_disjunctionSecond { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.disjunctionSecond context first second)) = some (RuleCode.disjunctionSecond context first second) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_disjunctionSecond, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_disjunctionElimination { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) (consequent : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.disjunctionElimination context first second consequent)) = some (RuleCode.disjunctionElimination context first second consequent) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_disjunctionElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_implicationIntroduction { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.implicationIntroduction context first second)) = some (RuleCode.implicationIntroduction context first second) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_implicationIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_implicationElimination { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.implicationElimination context first second)) = some (RuleCode.implicationElimination context first second) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_implicationElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_universalIntroduction { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.universalIntroduction context domain predicate)) = some (RuleCode.universalIntroduction context domain predicate) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_universalIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_universalElimination { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.universalElimination context domain predicate value)) = some (RuleCode.universalElimination context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_universalElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_existentialIntroduction { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.existentialIntroduction context domain predicate value)) = some (RuleCode.existentialIntroduction context domain predicate value) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_existentialIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_existentialElimination { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (consequent : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.existentialElimination context domain predicate consequent)) = some (RuleCode.existentialElimination context domain predicate consequent) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_existentialElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_imageIntroduction { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) (value : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.imageIntroduction context type value)) = some (RuleCode.imageIntroduction context type value) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_imageIntroduction, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_imageElimination { n : Nat } (context : ContextExpr S n) (type : TypeExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.imageElimination context type predicate)) = some (RuleCode.imageElimination context type predicate) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_imageElimination, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionWeakenAssumption { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionWeakenAssumption context predicate)) = some (RuleCode.substitutionWeakenAssumption context predicate) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substitutionWeakenAssumption, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionIntoAssumption { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (predicate : PropExpr S m) (substitution : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionIntoAssumption source target predicate substitution)) = some (RuleCode.substitutionIntoAssumption source target predicate substitution) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substitutionIntoAssumption, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionLift { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (type : TypeExpr S m) (substitution : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionLift source target type substitution)) = some (RuleCode.substitutionLift source target type substitution) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substitutionLift, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionAssumptionLift { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (predicate : PropExpr S m) (substitution : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionAssumptionLift source target predicate substitution)) = some (RuleCode.substitutionAssumptionLift source target predicate substitution) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substitutionAssumptionLift, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutePredicate { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (predicate : PropExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substitutePredicate source target substitution predicate)) = some (RuleCode.substitutePredicate source target substitution predicate) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substitutePredicate, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substituteEntailment { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (predicate : PropExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substituteEntailment source target substitution predicate)) = some (RuleCode.substituteEntailment source target substitution predicate) := by
  simp only [putRule, getRule, getRuleGroup6, getPayload_substituteEntailment, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportPredicate { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportPredicate first second predicate)) = some (RuleCode.transportPredicate first second predicate) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_transportPredicate, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_transportEntailment { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.transportEntailment first second predicate)) = some (RuleCode.transportEntailment first second predicate) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_transportEntailment, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicateReflexivity { n : Nat } (context : ContextExpr S n) (predicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.predicateReflexivity context predicate)) = some (RuleCode.predicateReflexivity context predicate) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_predicateReflexivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicateSymmetry { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.predicateSymmetry context first second)) = some (RuleCode.predicateSymmetry context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_predicateSymmetry, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicateTransitivity { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (middle : PropExpr S n) (last : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.predicateTransitivity context first middle last)) = some (RuleCode.predicateTransitivity context first middle last) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_predicateTransitivity, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicateExtensionality { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.predicateExtensionality context first second)) = some (RuleCode.predicateExtensionality context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_predicateExtensionality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_entailmentConversion { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.entailmentConversion context first second)) = some (RuleCode.entailmentConversion context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_entailmentConversion, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_contextAssumeEquality { n : Nat } (first : ContextExpr S n) (second : ContextExpr S n) (firstPredicate : PropExpr S n) (secondPredicate : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.contextAssumeEquality first second firstPredicate secondPredicate)) = some (RuleCode.contextAssumeEquality first second firstPredicate secondPredicate) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_contextAssumeEquality, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_comprehensionCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstPredicate : PropExpr S (n + 1)) (secondPredicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate)) = some (RuleCode.comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_comprehensionCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_quoteCongruence { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.quoteCongruence context first second)) = some (RuleCode.quoteCongruence context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_quoteCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_holdsCongruence { n : Nat } (context : ContextExpr S n) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.holdsCongruence context first second)) = some (RuleCode.holdsCongruence context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_holdsCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_imageCongruence { n : Nat } (context : ContextExpr S n) (first : TypeExpr S n) (second : TypeExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.imageCongruence context first second)) = some (RuleCode.imageCongruence context first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_imageCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_refineCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.refineCongruence context domain predicate first second)) = some (RuleCode.refineCongruence context domain predicate first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_refineCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_forgetCongruence { n : Nat } (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.forgetCongruence context domain predicate first second)) = some (RuleCode.forgetCongruence context domain predicate first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_forgetCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicatePrimitiveCongruence { n : Nat } (context : ContextExpr S n) (symbol : S.PredicateSymbol) (first : Substitution S (S.predicateArity symbol) n) (second : Substitution S (S.predicateArity symbol) n) :
    getRule symbols D (putRule symbols D (RuleCode.predicatePrimitiveCongruence context symbol first second)) = some (RuleCode.predicatePrimitiveCongruence context symbol first second) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_predicatePrimitiveCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_conjunctionCongruence { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) (third : PropExpr S n) (fourth : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.conjunctionCongruence context first second third fourth)) = some (RuleCode.conjunctionCongruence context first second third fourth) := by
  simp only [putRule, getRule, getRuleGroup7, getPayload_conjunctionCongruence, Nat.reduceLT, Nat.reduceSub, if_true, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_disjunctionCongruence { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) (third : PropExpr S n) (fourth : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.disjunctionCongruence context first second third fourth)) = some (RuleCode.disjunctionCongruence context first second third fourth) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_disjunctionCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_implicationCongruence { n : Nat } (context : ContextExpr S n) (first : PropExpr S n) (second : PropExpr S n) (third : PropExpr S n) (fourth : PropExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.implicationCongruence context first second third fourth)) = some (RuleCode.implicationCongruence context first second third fourth) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_implicationCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_universalCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstPredicate : PropExpr S (n + 1)) (secondPredicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.universalCongruence context firstDomain secondDomain firstPredicate secondPredicate)) = some (RuleCode.universalCongruence context firstDomain secondDomain firstPredicate secondPredicate) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_universalCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_existentialCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstPredicate : PropExpr S (n + 1)) (secondPredicate : PropExpr S (n + 1)) :
    getRule symbols D (putRule symbols D (RuleCode.existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate)) = some (RuleCode.existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_existentialCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutePredicateEquality { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (substitution : Substitution S m n) (first : PropExpr S m) (second : PropExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.substitutePredicateEquality source target substitution first second)) = some (RuleCode.substitutePredicateEquality source target substitution first second) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_substitutePredicateEquality, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_predicateSubstitutionCongruence { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (first : Substitution S m n) (second : Substitution S m n) (predicate : PropExpr S m) :
    getRule symbols D (putRule symbols D (RuleCode.predicateSubstitutionCongruence source target first second predicate)) = some (RuleCode.predicateSubstitutionCongruence source target first second predicate) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_predicateSubstitutionCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_refineAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstPredicate : PropExpr S (n + 1)) (secondPredicate : PropExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second)) = some (RuleCode.refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_refineAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_forgetAnnotationCongruence { n : Nat } (context : ContextExpr S n) (firstDomain : TypeExpr S n) (secondDomain : TypeExpr S n) (firstPredicate : PropExpr S (n + 1)) (secondPredicate : PropExpr S (n + 1)) (first : TermExpr S n) (second : TermExpr S n) :
    getRule symbols D (putRule symbols D (RuleCode.forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second)) = some (RuleCode.forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_forgetAnnotationCongruence, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem roundtrip_substitutionIntoAssumptionEquality { n : Nat } { m : Nat } (source : ContextExpr S n) (target : ContextExpr S m) (predicate : PropExpr S m) (first : Substitution S m n) (second : Substitution S m n) :
    getRule symbols D (putRule symbols D (RuleCode.substitutionIntoAssumptionEquality source target predicate first second)) = some (RuleCode.substitutionIntoAssumptionEquality source target predicate first second) := by
  simp only [putRule, getRule, getRuleGroup8, getPayload_substitutionIntoAssumptionEquality, Nat.reduceLT, Nat.reduceSub, if_false, Codec.get_put, Bind.bind, Option.bind]
  rfl

theorem get_putRule (rule : RuleCode D) : getRule symbols D (putRule symbols D rule) = some rule := by
  cases rule with
  | contextNil => exact roundtrip_contextNil symbols D
  | contextExtend context type => exact roundtrip_contextExtend symbols D context type
  | «variable» context index => exact roundtrip_variable symbols D context index
  | typeFamily context symbol arguments => exact roundtrip_typeFamily symbols D context symbol arguments
  | primitive context symbol arguments => exact roundtrip_primitive symbols D context symbol arguments
  | piFormation context domain body => exact roundtrip_piFormation symbols D context domain body
  | sigmaFormation context domain body => exact roundtrip_sigmaFormation symbols D context domain body
  | lambda context domain body term => exact roundtrip_lambda symbols D context domain body term
  | application context domain body function argument => exact roundtrip_application symbols D context domain body function argument
  | pairIntroduction context domain body first second => exact roundtrip_pairIntroduction symbols D context domain body first second
  | firstProjection context domain body pair => exact roundtrip_firstProjection symbols D context domain body pair
  | secondProjection context domain body pair => exact roundtrip_secondProjection symbols D context domain body pair
  | sigmaElimination context domain body motive branch pair => exact roundtrip_sigmaElimination symbols D context domain body motive branch pair
  | termConversion context term first second => exact roundtrip_termConversion symbols D context term first second
  | substitutionNil context => exact roundtrip_substitutionNil symbols D context
  | substitutionExtend source target type substitution term => exact roundtrip_substitutionExtend symbols D source target type substitution term
  | substitutionIdentity context => exact roundtrip_substitutionIdentity symbols D context
  | substitutionCompose source middle target first second => exact roundtrip_substitutionCompose symbols D source middle target first second
  | substitutionWeaken context type => exact roundtrip_substitutionWeaken symbols D context type
  | substituteType source target substitution type => exact roundtrip_substituteType symbols D source target substitution type
  | substituteTerm source target substitution term type => exact roundtrip_substituteTerm symbols D source target substitution term type
  | contextReflexivity context => exact roundtrip_contextReflexivity symbols D context
  | contextSymmetry first second => exact roundtrip_contextSymmetry symbols D first second
  | contextTransitivity first middle last => exact roundtrip_contextTransitivity symbols D first middle last
  | contextExtendEquality first second firstType secondType => exact roundtrip_contextExtendEquality symbols D first second firstType secondType
  | transportType first second type => exact roundtrip_transportType symbols D first second type
  | transportTerm first second term type => exact roundtrip_transportTerm symbols D first second term type
  | transportSubstitution source source' target target' substitution => exact roundtrip_transportSubstitution symbols D source source' target target' substitution
  | typeReflexivity context type => exact roundtrip_typeReflexivity symbols D context type
  | typeSymmetry context first second => exact roundtrip_typeSymmetry symbols D context first second
  | typeTransitivity context first middle last => exact roundtrip_typeTransitivity symbols D context first middle last
  | termReflexivity context term type => exact roundtrip_termReflexivity symbols D context term type
  | termSymmetry context first second type => exact roundtrip_termSymmetry symbols D context first second type
  | termTransitivity context first middle last type => exact roundtrip_termTransitivity symbols D context first middle last type
  | equalityConversion context first second firstType secondType => exact roundtrip_equalityConversion symbols D context first second firstType secondType
  | transportTypeEquality source target first second => exact roundtrip_transportTypeEquality symbols D source target first second
  | transportTermEquality source target first second type => exact roundtrip_transportTermEquality symbols D source target first second type
  | piCongruence context firstDomain secondDomain firstBody secondBody => exact roundtrip_piCongruence symbols D context firstDomain secondDomain firstBody secondBody
  | sigmaCongruence context firstDomain secondDomain firstBody secondBody => exact roundtrip_sigmaCongruence symbols D context firstDomain secondDomain firstBody secondBody
  | familyCongruence context symbol first second => exact roundtrip_familyCongruence symbols D context symbol first second
  | primitiveCongruence context symbol first second => exact roundtrip_primitiveCongruence symbols D context symbol first second
  | lambdaCongruence context domain body first second => exact roundtrip_lambdaCongruence symbols D context domain body first second
  | applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument => exact roundtrip_applicationCongruence symbols D context domain body firstFunction secondFunction firstArgument secondArgument
  | pairCongruence context domain body firstLeft secondLeft firstRight secondRight => exact roundtrip_pairCongruence symbols D context domain body firstLeft secondLeft firstRight secondRight
  | firstCongruence context domain body first second => exact roundtrip_firstCongruence symbols D context domain body first second
  | secondCongruence context domain body first second => exact roundtrip_secondCongruence symbols D context domain body first second
  | sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair => exact roundtrip_sigmaEliminationCongruence symbols D context domain body motive firstBranch secondBranch firstPair secondPair
  | lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => exact roundtrip_lambdaAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody first second
  | applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument => exact roundtrip_applicationAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument
  | pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight => exact roundtrip_pairAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight
  | firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => exact roundtrip_firstAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody first second
  | secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second => exact roundtrip_secondAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody first second
  | sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair => exact roundtrip_sigmaEliminationAnnotationCongruence symbols D context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair
  | piBeta context domain body term argument => exact roundtrip_piBeta symbols D context domain body term argument
  | piEta context domain body function => exact roundtrip_piEta symbols D context domain body function
  | sigmaFirstBeta context domain body first second => exact roundtrip_sigmaFirstBeta symbols D context domain body first second
  | sigmaSecondBeta context domain body first second => exact roundtrip_sigmaSecondBeta symbols D context domain body first second
  | sigmaEta context domain body pair => exact roundtrip_sigmaEta symbols D context domain body pair
  | sigmaEliminationBeta context domain body motive branch first second => exact roundtrip_sigmaEliminationBeta symbols D context domain body motive branch first second
  | sigmaEliminationEta context domain body motive term pair => exact roundtrip_sigmaEliminationEta symbols D context domain body motive term pair
  | substituteTypeEquality source target substitution first second => exact roundtrip_substituteTypeEquality symbols D source target substitution first second
  | substituteTermEquality source target substitution first second type => exact roundtrip_substituteTermEquality symbols D source target substitution first second type
  | substitutionReflexivity source target substitution => exact roundtrip_substitutionReflexivity symbols D source target substitution
  | substitutionSymmetry source target first second => exact roundtrip_substitutionSymmetry symbols D source target first second
  | substitutionTransitivity source target first middle last => exact roundtrip_substitutionTransitivity symbols D source target first middle last
  | substitutionExtendEquality source target type first second firstTerm secondTerm => exact roundtrip_substitutionExtendEquality symbols D source target type first second firstTerm secondTerm
  | typeSubstitutionCongruence source target first second type => exact roundtrip_typeSubstitutionCongruence symbols D source target first second type
  | termSubstitutionCongruence source target first second term type => exact roundtrip_termSubstitutionCongruence symbols D source target first second term type
  | contextAssume context predicate => exact roundtrip_contextAssume symbols D context predicate
  | propositionType context => exact roundtrip_propositionType symbols D context
  | predicatePrimitive context symbol arguments => exact roundtrip_predicatePrimitive symbols D context symbol arguments
  | truthFormation context => exact roundtrip_truthFormation symbols D context
  | falsehoodFormation context => exact roundtrip_falsehoodFormation symbols D context
  | conjunctionFormation context first second => exact roundtrip_conjunctionFormation symbols D context first second
  | disjunctionFormation context first second => exact roundtrip_disjunctionFormation symbols D context first second
  | implicationFormation context first second => exact roundtrip_implicationFormation symbols D context first second
  | universalFormation context domain predicate => exact roundtrip_universalFormation symbols D context domain predicate
  | existentialFormation context domain predicate => exact roundtrip_existentialFormation symbols D context domain predicate
  | holdsFormation context term => exact roundtrip_holdsFormation symbols D context term
  | imageFormation context type => exact roundtrip_imageFormation symbols D context type
  | quote context predicate => exact roundtrip_quote symbols D context predicate
  | comprehensionFormation context domain predicate => exact roundtrip_comprehensionFormation symbols D context domain predicate
  | comprehensionIntroduction context domain predicate value => exact roundtrip_comprehensionIntroduction symbols D context domain predicate value
  | comprehensionElimination context domain predicate value => exact roundtrip_comprehensionElimination symbols D context domain predicate value
  | comprehensionGuard context domain predicate value => exact roundtrip_comprehensionGuard symbols D context domain predicate value
  | comprehensionBeta context domain predicate value => exact roundtrip_comprehensionBeta symbols D context domain predicate value
  | comprehensionEta context domain predicate value => exact roundtrip_comprehensionEta symbols D context domain predicate value
  | quoteHolds context term => exact roundtrip_quoteHolds symbols D context term
  | holdsQuote context predicate => exact roundtrip_holdsQuote symbols D context predicate
  | hypothesis context predicate member => exact roundtrip_hypothesis symbols D context predicate member
  | truthIntroduction context => exact roundtrip_truthIntroduction symbols D context
  | falsehoodElimination context predicate => exact roundtrip_falsehoodElimination symbols D context predicate
  | conjunctionIntroduction context first second => exact roundtrip_conjunctionIntroduction symbols D context first second
  | conjunctionFirst context first second => exact roundtrip_conjunctionFirst symbols D context first second
  | conjunctionSecond context first second => exact roundtrip_conjunctionSecond symbols D context first second
  | disjunctionFirst context first second => exact roundtrip_disjunctionFirst symbols D context first second
  | disjunctionSecond context first second => exact roundtrip_disjunctionSecond symbols D context first second
  | disjunctionElimination context first second consequent => exact roundtrip_disjunctionElimination symbols D context first second consequent
  | implicationIntroduction context first second => exact roundtrip_implicationIntroduction symbols D context first second
  | implicationElimination context first second => exact roundtrip_implicationElimination symbols D context first second
  | universalIntroduction context domain predicate => exact roundtrip_universalIntroduction symbols D context domain predicate
  | universalElimination context domain predicate value => exact roundtrip_universalElimination symbols D context domain predicate value
  | existentialIntroduction context domain predicate value => exact roundtrip_existentialIntroduction symbols D context domain predicate value
  | existentialElimination context domain predicate consequent => exact roundtrip_existentialElimination symbols D context domain predicate consequent
  | imageIntroduction context type value => exact roundtrip_imageIntroduction symbols D context type value
  | imageElimination context type predicate => exact roundtrip_imageElimination symbols D context type predicate
  | substitutionWeakenAssumption context predicate => exact roundtrip_substitutionWeakenAssumption symbols D context predicate
  | substitutionIntoAssumption source target predicate substitution => exact roundtrip_substitutionIntoAssumption symbols D source target predicate substitution
  | substitutionLift source target type substitution => exact roundtrip_substitutionLift symbols D source target type substitution
  | substitutionAssumptionLift source target predicate substitution => exact roundtrip_substitutionAssumptionLift symbols D source target predicate substitution
  | substitutePredicate source target substitution predicate => exact roundtrip_substitutePredicate symbols D source target substitution predicate
  | substituteEntailment source target substitution predicate => exact roundtrip_substituteEntailment symbols D source target substitution predicate
  | transportPredicate first second predicate => exact roundtrip_transportPredicate symbols D first second predicate
  | transportEntailment first second predicate => exact roundtrip_transportEntailment symbols D first second predicate
  | predicateReflexivity context predicate => exact roundtrip_predicateReflexivity symbols D context predicate
  | predicateSymmetry context first second => exact roundtrip_predicateSymmetry symbols D context first second
  | predicateTransitivity context first middle last => exact roundtrip_predicateTransitivity symbols D context first middle last
  | predicateExtensionality context first second => exact roundtrip_predicateExtensionality symbols D context first second
  | entailmentConversion context first second => exact roundtrip_entailmentConversion symbols D context first second
  | contextAssumeEquality first second firstPredicate secondPredicate => exact roundtrip_contextAssumeEquality symbols D first second firstPredicate secondPredicate
  | comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate => exact roundtrip_comprehensionCongruence symbols D context firstDomain secondDomain firstPredicate secondPredicate
  | quoteCongruence context first second => exact roundtrip_quoteCongruence symbols D context first second
  | holdsCongruence context first second => exact roundtrip_holdsCongruence symbols D context first second
  | imageCongruence context first second => exact roundtrip_imageCongruence symbols D context first second
  | refineCongruence context domain predicate first second => exact roundtrip_refineCongruence symbols D context domain predicate first second
  | forgetCongruence context domain predicate first second => exact roundtrip_forgetCongruence symbols D context domain predicate first second
  | predicatePrimitiveCongruence context symbol first second => exact roundtrip_predicatePrimitiveCongruence symbols D context symbol first second
  | conjunctionCongruence context first second third fourth => exact roundtrip_conjunctionCongruence symbols D context first second third fourth
  | disjunctionCongruence context first second third fourth => exact roundtrip_disjunctionCongruence symbols D context first second third fourth
  | implicationCongruence context first second third fourth => exact roundtrip_implicationCongruence symbols D context first second third fourth
  | universalCongruence context firstDomain secondDomain firstPredicate secondPredicate => exact roundtrip_universalCongruence symbols D context firstDomain secondDomain firstPredicate secondPredicate
  | existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate => exact roundtrip_existentialCongruence symbols D context firstDomain secondDomain firstPredicate secondPredicate
  | substitutePredicateEquality source target substitution first second => exact roundtrip_substitutePredicateEquality symbols D source target substitution first second
  | predicateSubstitutionCongruence source target first second predicate => exact roundtrip_predicateSubstitutionCongruence symbols D source target first second predicate
  | refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second => exact roundtrip_refineAnnotationCongruence symbols D context firstDomain secondDomain firstPredicate secondPredicate first second
  | forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second => exact roundtrip_forgetAnnotationCongruence symbols D context firstDomain secondDomain firstPredicate secondPredicate first second
  | substitutionIntoAssumptionEquality source target predicate first second => exact roundtrip_substitutionIntoAssumptionEquality symbols D source target predicate first second

def rule : Codec (RuleCode D) := ⟨putRule symbols D, getRule symbols D, get_putRule symbols D⟩

end Mettapedia.OSLF.NativeTypes.Certificates.NativeWire
