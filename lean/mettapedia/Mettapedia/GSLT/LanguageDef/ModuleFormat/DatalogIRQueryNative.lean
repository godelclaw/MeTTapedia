import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoinNative

/-! A finite snapshot provider realizes a compiled clause without child
rewrite searches. Admission is uniform in the fact snapshot, provided its
rows pass the existing typed provider check. The checker is unchanged. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query.Native

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

def compiledLanguage : LanguageDef := module_language_view%
  (some (language [lowerRule Join.Controls.pools Join.Controls.rule]))
theorem compiledLanguage_exact :
    compiledLanguage = language [lowerRule Join.Controls.pools Join.Controls.rule] := by rfl

def snapshot (known : List Pattern) : GeneralExecutionAdmission.Snapshot :=
  ⟨compiledLanguage,Join.Native.freeTypes,provider known⟩
def plan (known : List Pattern) := GeneralExecutionAdmission.compile (snapshot known) Join.Native.permissions
def spec (known : List Pattern) : CompleteEmission.Spec := ⟨plan known,[],.base "DlStatement",.standard⟩

private theorem terms_valid : ∀ index : Fin compiledLanguage.terms.length,
    LanguageDef.validateTerm compiledLanguage (compiledLanguage.terms.get index) = [] := by
  intro index
  fin_cases index <;> decide +kernel

private theorem rewrites_valid : ∀ index : Fin compiledLanguage.rewrites.length,
    LanguageDef.validateRewrite compiledLanguage (compiledLanguage.rewrites.get index) = [] := by
  intro index
  fin_cases index
  all_goals
    conv_lhs => arg 2; cbv
    simp only [LanguageDef.validateRewrite,LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames,Pattern.freeFvarNames,LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns,LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,List.attach_cons,List.attach_nil,
      List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.flatMap_append,
      List.append_nil,List.nil_append]
    decide +kernel

private theorem language_valid : compiledLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro term member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact terms_valid ⟨index,inside⟩
  · intro equation member
    have none : compiledLanguage.equations = [] := rfl
    rw [none] at member
    cases member
  · intro rule member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact rewrites_valid ⟨index,inside⟩

private theorem rule_rows (known : List Pattern) : ∀ index : Fin compiledLanguage.rewrites.length,
    GeneralExecutionAdmission.ruleObligations (snapshot known) index.val (compiledLanguage.rewrites.get index) = [] := by
  intro index
  fin_cases index
  decide_cbv

theorem pending_discharged (known : List Pattern)
    (closed : GeneralPremise.checkProviderClosed compiledLanguage (snapshot known).free (provider known) = true) :
    CompleteEmission.pendingFor (spec known) .classes = [] := by
  change CompleteEmission.pending (GeneralExecutionAdmission.compile (snapshot known) Join.Native.permissions) = []
  apply ClassCompilerChecks.pending_of_checks (snapshot known) Join.Native.permissions
  · exact language_valid
  · change GeneralExecutionAdmission.checkFreeContext (snapshot []) = true
    decide +kernel
  · exact closed
  · change Reflection.validate compiledLanguage Join.Native.permissions.reflection = []
    decide +kernel
  · rfl
  · rfl
  · intro entry member
    obtain ⟨row,index⟩ := entry
    have selected : (row,index) ∈ compiledLanguage.rewrites.zipIdx := by
      simpa [GeneralExecutionAdmission.selectedRules,Join.Native.permissions,GeneralExecutionAdmission.selected,snapshot] using member
    have found := List.mk_mem_zipIdx_iff_getElem?.mp selected
    obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
    subst row
    exact rule_rows known ⟨index,inside⟩
  · intro entry member
    have none : (snapshot known).language.equations = [] := rfl
    simp [GeneralExecutionAdmission.selectedEquations,none] at member
  · rfl
  · change GeneralExecutionAdmission.setDecompositionFree (snapshot []) Join.Native.permissions = true
    decide +kernel

theorem emission_admitted (known : List Pattern) (name : String)
    (closed : GeneralPremise.checkProviderClosed compiledLanguage (snapshot known).free (provider known) = true)
    (names : CompleteEmissionSupport.entryChecks name = true) :
    CompleteEmission.Emitted (spec known) name .classes := by
  constructor
  · exact pending_discharged known closed
  · change (plan known).equations.all _ = true
    rfl
  · rfl
  · exact CompleteEmissionSupport.namesFresh_of_entryChecks _ _ rfl names

def request : Pattern := call [.fvar "relation:edge",.fvar "relation:path"] [.fvar "value:a"]

theorem snapshot_controls :
    GeneralPremise.checkProviderClosed compiledLanguage (snapshot []).free
      (provider [Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "b" "c"]) = true ∧
    GeneralPremise.checkProviderClosed compiledLanguage (snapshot []).free
      (provider [.fvar "unregistered-value"]) = false := by decide_cbv

#print axioms compiledLanguage_exact
#print axioms pending_discharged
#print axioms emission_admitted
#print axioms snapshot_controls

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query.Native
