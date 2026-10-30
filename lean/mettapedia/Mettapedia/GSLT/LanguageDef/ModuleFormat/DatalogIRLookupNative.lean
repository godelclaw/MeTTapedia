import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLookup
import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ClassCompilerChecks
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport

/-! The independent IR lookup uses the established class emitter. An explicit
finite carrier environment supplies atomic payload references; expanding those
references recovers the compact semantic IR, with no source-syntax data. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Lookup.Native

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.Datalog

def freeTypes : List (String × TypeExpr) :=
  [("ir:id:edge",.base "DlIdentifier"),("ir:sym:a",.base "DlSymbol"),
   ("ir:sym:b",.base "DlSymbol"),("ir:sym:c",.base "DlSymbol")]

def snapshot : GeneralExecutionAdmission.Snapshot :=
  ⟨language,freeTypes,{signatures := [],rows := []}⟩
def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .rootOnly,includeDerivedEquations := false}
def plan := GeneralExecutionAdmission.compile snapshot permissions
def spec : CompleteEmission.Spec := ⟨plan,[],.base "DlStatement",.standard⟩

private theorem language_valid : language.validate = [] := by decide_cbv
private theorem rule_rows : ∀ index : Fin language.rewrites.length,
    GeneralExecutionAdmission.ruleObligations snapshot index.val (language.rewrites.get index) = [] := by
  intro index
  fin_cases index <;> decide_cbv

theorem pending_discharged : CompleteEmission.pendingFor spec .classes = [] := by
  change CompleteEmission.pending (GeneralExecutionAdmission.compile snapshot permissions) = []
  apply ClassCompilerChecks.pending_of_checks
  · exact language_valid
  · decide_cbv
  · decide_cbv
  · decide_cbv
  · rfl
  · rfl
  · intro entry member
    obtain ⟨row,index⟩ := entry
    have selected : (row,index) ∈ language.rewrites.zipIdx := by
      simpa [GeneralExecutionAdmission.selectedRules,permissions,GeneralExecutionAdmission.selected,snapshot] using member
    have found := List.mk_mem_zipIdx_iff_getElem?.mp selected
    obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
    subst row
    exact rule_rows ⟨index,inside⟩
  · intro entry member
    have none : snapshot.language.equations = [] := rfl
    simp [GeneralExecutionAdmission.selectedEquations,none] at member
  · rfl
  · decide_cbv

theorem emission_admitted : CompleteEmission.Emitted spec "datalog-ir-lookup" .classes := by
  constructor
  · exact pending_discharged
  · change plan.equations.all _ = true
    rfl
  · rfl
  · apply CompleteEmissionSupport.namesFresh_of_entryChecks
    · rfl
    · decide +kernel

def fact (first second : String) : Pattern := .apply "GroundFact"
  [.apply "Relation" [.apply "QualifiedName" [.collection .vec [.fvar "ir:id:edge"] none]],
   .apply "GroundTuple" [.collection .vec
      [.apply "SymbolValue" [.fvar ("ir:sym:" ++ first)],.apply "SymbolValue" [.fvar ("ir:sym:" ++ second)]] none]]

def literals : Bindings :=
  [("ir:id:edge",IRCodec.atom "edge"),("ir:sym:a",IRCodec.atom "a"),
   ("ir:sym:b",IRCodec.atom "b"),("ir:sym:c",IRCodec.atom "c")]

theorem payload_expansion :
    applyBindings literals (fact "a" "b") = IRCodec.groundFact ⟨["edge"],[.symbol "a",.symbol "b"]⟩ ∧
      applyBindings literals (fact "b" "c") = IRCodec.groundFact ⟨["edge"],[.symbol "b",.symbol "c"]⟩ := by
  decide +kernel

theorem no_invented_facts (environment : Engine.RelationEnv) (result : Pattern)
    (step : ReferenceStep.Step environment language (call [fact "a" "b",fact "b" "c",fact "a" "b"]) result) :
    result ∈ [fact "a" "b",fact "b" "c",fact "a" "b"] :=
  (reference_exact environment _ _).mp step

#print axioms emission_admitted
#print axioms payload_expansion

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Lookup.Native
