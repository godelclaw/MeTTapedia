import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogQueryKernel

/-! The lowered operation uses the established finite-provider profile.
These controls distinguish absent premises, repeated kept facts and an
incorrect provider snapshot. They do not qualify an ordinary-source frontend. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel.Controls

open Mettapedia.OSLF.MeTTaIL Syntax

def freeTypes : List (String × TypeExpr) :=
  [("a", .base "DlGroundAtomData"), ("b", .base "DlGroundAtomData"),
   ("c", .base "DlGroundAtomData"), ("id", .base "DlClauseOrdinal"), ("env", .base "DlGrounding")]

def known : List Pattern := [.fvar "a", .fvar "b"]

def compiled := plan freeTypes known

#guard compiled.obligations.isEmpty
#guard compiled.rules.length == 1
#guard !(GeneralExecutionAdmission.compile
    (snapshot [] known) permissions).obligations.isEmpty

theorem compiled_has_no_obligations : compiled.obligations = [] := by decide_cbv

def source (premises : List Pattern) : Pattern :=
  Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c") premises known

def result (premises : List Pattern) : Pattern :=
  Kernel.groundResult (.fvar "id") (.fvar "env") (.fvar "c") premises known

theorem two_kept_facts :
    ReferenceStep.Step (environment known) language (source known) (result known) := by
  apply application_step_of_all
  intro fact present
  exact present

theorem duplicate_premises_need_one_fact :
    ReferenceStep.Step (environment known) language (source [.fvar "a", .fvar "a"])
      (result [.fvar "a", .fvar "a"]) := by
  apply application_step_of_all
  simp [known]

theorem missing_fact_refused :
    ¬ ReferenceStep.Step (environment known) language (source [.fvar "c"]) (result [.fvar "c"]) := by
  unfold source result
  rw [application_step_exact]
  simp [known]

theorem empty_body_still_applies :
    ReferenceStep.Step (environment known) language (source []) (result []) := by
  apply application_step_of_all
  simp

theorem wrong_result_refused :
    ¬ ReferenceStep.Step (environment known) language (source known) (.apply "WrongConclusion" []) := by
  unfold source
  rw [application_step_exact]
  simp [Kernel.groundResult]

theorem provider_does_not_justify_unavailable_fact :
    ¬ ReferenceStep.Step (environment []) language
      (Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c") [.fvar "a"] [])
      (Kernel.groundResult (.fvar "id") (.fvar "env") (.fvar "c") [.fvar "a"] []) := by
  rw [application_step_exact]
  simp

#print axioms two_kept_facts
#print axioms duplicate_premises_need_one_fact
#print axioms missing_fact_refused
#print axioms wrong_result_refused
#print axioms compiled_has_no_obligations

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel.Controls
