import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNativeSlice

/-! The actual compiler signature and every selected rewrite pass the shared
validator. Finite row certificates keep rule validation independent of the
whole compiled-plan and call-graph computations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.NativeSlice

open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem terms_valid : ∀ index : Fin language.terms.length,
    LanguageDef.validateTerm language (language.terms.get index) = [] := by
  intro index
  fin_cases index <;> decide +kernel

private theorem rewrites_valid : ∀ index : Fin language.rewrites.length,
    LanguageDef.validateRewrite language (language.rewrites.get index) = [] := by
  intro index
  fin_cases index
  all_goals
    conv_lhs => arg 2; cbv
    simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, Pattern.freeFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, List.attach_cons, List.attach_nil,
      List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
      List.append_nil, List.nil_append]
    decide +kernel

theorem language_valid : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro term member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact terms_valid ⟨index,inside⟩
  · intro equation member
    have none : language.equations = [] := rfl
    rw [none] at member
    cases member
  · intro rule member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact rewrites_valid ⟨index,inside⟩

#print axioms language_valid

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.NativeSlice
