import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNative
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionValidation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ClassCompilerChecks
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport

/-! Concrete admission facts for the existing compiler class profile.
Language validation, rule obligations and runtime-name support are proved
separately and combined through the unchanged emitter contract. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.Admission

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def freeTypes : List (String × TypeExpr) :=
  [("i",.base "DlInteger"),("s",.base "DlSymbol"),("u",.base "DlUnsigned"),("f",.base "DlFloat")]

def expectedSpec (expected : TypeExpr) : CompleteEmission.Spec := spec freeTypes expected

def tupleSpec : CompleteEmission.Spec := expectedSpec (.base "DlGroundTuple")

def programSpec : CompleteEmission.Spec := expectedSpec (.base "DlProgramData")

private theorem rule_rows : ∀ index : Fin NativeSlice.language.rewrites.length,
    GeneralExecutionAdmission.ruleObligations (snapshot freeTypes) index.val
      (NativeSlice.language.rewrites.get index) = [] := by
  intro index
  fin_cases index <;> decide_cbv

theorem remaining_obligations_discharged : CompleteEmission.pendingFor tupleSpec .classes = [] := by
  change CompleteEmission.pending (GeneralExecutionAdmission.compile (snapshot freeTypes) permissions) = []
  apply ClassCompilerChecks.pending_of_checks
  · exact NativeSlice.language_valid
  · decide_cbv
  · decide_cbv
  · decide_cbv
  · rfl
  · rfl
  · intro entry member
    obtain ⟨row,index⟩ := entry
    have selected : (row,index) ∈ NativeSlice.language.rewrites.zipIdx := by
      simpa [GeneralExecutionAdmission.selectedRules,permissions,GeneralExecutionAdmission.selected,snapshot]
        using member
    have found := List.mk_mem_zipIdx_iff_getElem?.mp selected
    obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
    subst row
    exact rule_rows ⟨index,inside⟩
  · intro entry member
    have none : (snapshot freeTypes).language.equations = [] := rfl
    simp [GeneralExecutionAdmission.selectedEquations,none] at member
  · rfl
  · decide_cbv

theorem name_supported : CompleteEmission.namesFresh tupleSpec "datalog-projection" .classes = true := by
  apply CompleteEmissionSupport.namesFresh_of_entryChecks
  · rfl
  · decide +kernel

theorem emission_admitted : CompleteEmission.Emitted tupleSpec "datalog-projection" .classes := by
  constructor
  · exact remaining_obligations_discharged
  · change (Native.plan freeTypes).equations.all _ = true
    rfl
  · rfl
  · exact name_supported

/-- The existing class contract is independent of the selected result sort.
Each emitted name still discharges its actual fixed-runtime entry checks. -/
theorem emission_expected (expected : TypeExpr) (name : String)
    (names : CompleteEmissionSupport.entryChecks name = true) :
    CompleteEmission.Emitted (expectedSpec expected) name .classes := by
  constructor
  · exact remaining_obligations_discharged
  · change (Native.plan freeTypes).equations.all _ = true
    rfl
  · rfl
  · exact CompleteEmissionSupport.namesFresh_of_entryChecks _ _ rfl names

theorem program_emission_admitted :
    CompleteEmission.Emitted programSpec "datalog-program-projection" .classes :=
  emission_expected _ _ (by decide +kernel)

#print axioms remaining_obligations_discharged
#print axioms emission_admitted
#print axioms program_emission_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.Admission
