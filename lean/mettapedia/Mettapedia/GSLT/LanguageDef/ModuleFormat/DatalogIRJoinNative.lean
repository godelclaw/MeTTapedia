import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoinControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLookupNative

/-! A compiled two-atom clause on compact typed carrier references. Pool
matching pins relation and literal identities before premise search. The
dictionary expands the references back into canonical semantic IR. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Native

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.Datalog
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

def compiledLanguage : LanguageDef := module_language_view% (some (language [Controls.rule]))

theorem compiledLanguage_exact : compiledLanguage = language [Controls.rule] := by rfl

def freeTypes : List (String × TypeExpr) :=
  [("relation:edge",.base "DlRelation"),("relation:path",.base "DlRelation"),
   ("value:a",.base "DlValue"),("value:b",.base "DlValue"),("value:c",.base "DlValue"),
   ("value:d",.base "DlValue")]
def snapshot : GeneralExecutionAdmission.Snapshot :=
  ⟨compiledLanguage,freeTypes,{signatures := [],rows := []}⟩
def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .rootOnly,includeDerivedEquations := false}
def plan := GeneralExecutionAdmission.compile snapshot permissions
def spec : CompleteEmission.Spec := ⟨plan,[],.base "DlStatement",.standard⟩

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

private theorem language_valid : snapshot.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro term member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact terms_valid ⟨index,inside⟩
  · intro equation member
    have none : snapshot.language.equations = [] := rfl
    rw [none] at member
    cases member
  · intro rule member
    obtain ⟨index,inside,rfl⟩ := List.mem_iff_getElem.mp member
    exact rewrites_valid ⟨index,inside⟩

private theorem rule_rows : ∀ index : Fin snapshot.language.rewrites.length,
    GeneralExecutionAdmission.ruleObligations snapshot index.val (snapshot.language.rewrites.get index) = [] := by
  intro index
  fin_cases index <;> decide_cbv

theorem pending_discharged : CompleteEmission.pendingFor spec .classes = [] := by
  change CompleteEmission.pending (GeneralExecutionAdmission.compile snapshot permissions) = []
  apply ClassCompilerChecks.pending_of_checks snapshot permissions
  · exact language_valid
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · intro entry member
    obtain ⟨row,index⟩ := entry
    have selected : (row,index) ∈ snapshot.language.rewrites.zipIdx := by
      simpa [GeneralExecutionAdmission.selectedRules,permissions,GeneralExecutionAdmission.selected] using member
    have found := List.mk_mem_zipIdx_iff_getElem?.mp selected
    obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
    subst row
    exact rule_rows ⟨index,inside⟩
  · intro entry member
    have none : snapshot.language.equations = [] := rfl
    simp [GeneralExecutionAdmission.selectedEquations,none] at member
  · rfl
  · decide +kernel

theorem emission_admitted : CompleteEmission.Emitted spec "datalog-ir-join" .classes := by
  constructor
  · exact pending_discharged
  · change plan.equations.all _ = true
    rfl
  · rfl
  · apply CompleteEmissionSupport.namesFresh_of_entryChecks
    · rfl
    · decide +kernel

def fact (relation first second : String) : Pattern := .apply "GroundFact"
  [.fvar ("relation:" ++ relation),.apply "GroundTuple"
    [vector [.fvar ("value:" ++ first),.fvar ("value:" ++ second)]]]
def request (facts : List Pattern) : Pattern :=
  call [.fvar "relation:edge",.fvar "relation:path"] [.fvar "value:a"] facts
def literals : Bindings :=
  [("relation:edge",IRCodec.relation ["edge"]),("relation:path",IRCodec.relation ["path"]),
   ("value:a",IRCodec.value (.symbol "a")),("value:b",IRCodec.value (.symbol "b")),
   ("value:c",IRCodec.value (.symbol "c")),("value:d",IRCodec.value (.symbol "d"))]

theorem output_decodes : applyBindings literals (fact "path" "a" "c") =
    IRCodec.groundFact ⟨["path"],[.symbol "a",.symbol "c"]⟩ := by decide +kernel

#print axioms emission_admitted
#print axioms compiledLanguage_exact
#print axioms output_decodes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Native
