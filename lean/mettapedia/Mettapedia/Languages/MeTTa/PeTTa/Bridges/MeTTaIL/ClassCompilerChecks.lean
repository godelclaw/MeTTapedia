import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! The class realization discharges child stratification. Its remaining
compiler checks can be certified independently, without evaluating the
stratification graph whose result the class profile erases. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ClassCompilerChecks

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem pending_of_checks (snapshot : Snapshot) (permissions : Permissions)
    (language : snapshot.language.validate = [])
    (free : checkFreeContext snapshot = true)
    (provider : GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider = true)
    (reflection : Reflection.validate snapshot.language permissions.reflection = [])
    (missingRules : missing permissions.ruleIndices snapshot.language.rewrites.length = [])
    (missingEquations : missing permissions.equationIndices snapshot.language.equations.length = [])
    (rules : ∀ entry ∈ selectedRules snapshot permissions, ruleObligations snapshot entry.2 entry.1 = [])
    (equations : ∀ entry ∈ selectedEquations snapshot permissions,
      equationObligations snapshot entry.2.1 entry.1 entry.2.2 = [])
    (derived : permissions.includeDerivedEquations = false)
    (sets : setDecompositionFree snapshot permissions = true) :
    CompleteEmission.pending (compile snapshot permissions) = [] := by
  have ruleRows : (selectedRules snapshot permissions).flatMap
      (fun entry => ruleObligations snapshot entry.2 entry.1) = [] := List.flatMap_eq_nil_iff.mpr rules
  have equationRows : (selectedEquations snapshot permissions).flatMap
      (fun entry => equationObligations snapshot entry.2.1 entry.1 entry.2.2) = [] :=
    List.flatMap_eq_nil_iff.mpr equations
  unfold CompleteEmission.pending compile
  simp only [language, List.isEmpty_nil, free, provider, reflection, missingRules, missingEquations,
    ruleRows, equationRows, derived, sets, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, List.map_nil, List.nil_append, List.append_nil]
  split <;> rfl

#print axioms pending_of_checks

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ClassCompilerChecks
