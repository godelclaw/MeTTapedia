import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNativeAdmission

/-! The compiler-only specialization uses the existing class emitter.
Controls exercise recursive vector preservation and refuse malformed tails.
The source module and general admission policy remain intact. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def freeTypes := Admission.freeTypes

def tupleSpec := Admission.tupleSpec

theorem remaining_obligations_discharged : CompleteEmission.pendingFor tupleSpec .classes = [] :=
  Admission.remaining_obligations_discharged

theorem emission_admitted : CompleteEmission.Emitted tupleSpec "datalog-projection" .classes :=
  Admission.emission_admitted

def trivia : Pattern := .apply "dl-src:trivia-empty" []

def integer : Pattern := .apply "dl-src:constant-integer" [.fvar "i"]

theorem duplicate_occurrences_kept (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment NativeSlice.language
      (ConstantLists.call (ConstantLists.more integer trivia trivia (ConstantLists.one integer trivia)))
      (Reference.groundTuple [.apply "IntegerValue" [.fvar "i"],.apply "IntegerValue" [.fvar "i"]]) := by
  rw [constant_lists_exact]
  rfl

theorem malformed_tail_refused (environment : Engine.RelationEnv) (target : Pattern) :
    ¬ReferenceStep.Step environment NativeSlice.language
      (ConstantLists.call (ConstantLists.more integer trivia trivia
        (.apply "dl-src:constants-one" []))) target := by
  rw [constant_lists_exact]
  change ¬(none = some target)
  intro impossible
  cases impossible

theorem whole_source_module_retained : NativeSlice.sourceLanguage.rewrites.length = 48 := authored_rule_count

theorem specialization_rule_count : NativeSlice.language.rewrites.length = 46 := by decide +kernel

#print axioms emission_admitted
#print axioms duplicate_occurrences_kept
#print axioms malformed_tail_refused
#print axioms whole_source_module_retained

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.Controls
