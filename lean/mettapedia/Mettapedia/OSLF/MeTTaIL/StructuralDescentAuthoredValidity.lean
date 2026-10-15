import Mettapedia.OSLF.NativeTypes.Instances.LetCase.Language

/-! # Validation of the sorted authored let/case presentation -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredValidity

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.NativeTypes.Instances.LetCase

theorem letCase_valid : language.validate = [] := by
  simp [LanguageDef.validate, language,
    LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.typeNames,
    TypeExpr.baseNames, TermParam.bodyName, TermParam.binderNames,
    TermParam.typeExpr, letRule, caseRule, letInitialCongruence,
    letBodyCongruence, caseBodyCongruence,
    letTerm, returnValue, caseTerm, pair, value, computation]
  decide +kernel

#print axioms letCase_valid

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.AuthoredValidity
