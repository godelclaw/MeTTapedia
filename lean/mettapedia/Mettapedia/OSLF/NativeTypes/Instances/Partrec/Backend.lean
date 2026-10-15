import Mettapedia.OSLF.NativeTypes.Instances.Local.Backend
import Mettapedia.Languages.PartrecMachine.LanguageDef

open Mettapedia.OSLF.Framework

/-!
# The original partial-recursive language through the local native engine

All nineteen authored declarations remain selected in their original order.
This instance uses the generated typed matcher and premise jobs, their actual
receipts and the local coverage checker. Its completion laws quantify over
every open configuration in every supplied binder context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

def snapshot : Snapshot :=
  ⟨Mettapedia.Languages.PartrecMachine.partrecMachine, [], ⟨[], []⟩⟩

def permissions : Permissions := {sites := .rootOnly}

def plan : Plan := GeneralExecutionAdmission.compile snapshot permissions

theorem plan_original_language :
    plan.snapshot.language = Mettapedia.Languages.PartrecMachine.partrecMachine := rfl

theorem plan_foundation : plan.complete = true := by
  unfold plan GeneralExecutionAdmission.compile Plan.complete
  simp only [snapshot, Mettapedia.Languages.PartrecMachine.partrecMachine_validate_eq_nil,
    List.isEmpty_nil, if_true, List.nil_append]
  cbv

theorem plan_equations : plan.equations = [] := rfl

theorem plan_generic : GeneralExecutionTotalAdmission.checkGeneric plan = true := by
  cbv

theorem plan_all_authored_origins :
    plan.rules.map RulePlan.declarationIndex = List.range 19 := by
  cbv

def theory (bound : List TypeExpr) : Mettapedia.GSLT.GSLT :=
  GeneralOccurrenceSemantics.gslt plan bound (.base "Cfg")

def Source (bound : List TypeExpr) (source : Pattern) : Prop :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source plan bound (.base "Cfg") source

def request (bound : List TypeExpr) (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.request plan bound (.base "Cfg") source

def backend (bound : List TypeExpr) : Backend (theory bound) (Source bound) :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.backend plan bound (.base "Cfg") rfl
    plan_foundation plan_equations plan_generic

theorem whole_profile_complete (bound : List TypeExpr) (source : Pattern)
    (typed : Source bound source) :
    (backend bound).closed ((backend bound).completionBudget source) source = true :=
  (backend bound).complete_at source typed

theorem whole_profile_target_admitted (bound : List TypeExpr) (budget : Nat) (source : Pattern)
    (receipt : (backend bound).Receipt source)
    (listed : receipt ∈ (backend bound).frontier budget source) :
    Source bound ((backend bound).target source receipt) :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.frontier_target_admitted plan bound (.base "Cfg") budget source receipt listed

theorem whole_profile_successor_coverage (bound : List TypeExpr) (budget : Nat) (source : Pattern)
    (complete : (backend bound).closed budget source = true) (target : Pattern)
    (step : (theory bound).Step source target) :
    ∃ receipt, receipt ∈ (backend bound).frontier budget source ∧
      (theory bound).Equiv target ((backend bound).target source receipt) :=
  (backend bound).coverage budget source complete target step

theorem whole_profile_occurrence_coverage (bound : List TypeExpr) (source : Pattern)
    (typed : Source bound source) (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid plan bound (.base "Cfg") source) :
    ∃ answer ∈ (GeneralOccurrenceFrontier.LocalEquationFree.run (request bound source)
        (GeneralOccurrenceFrontier.LocalEquationFree.workBound (request bound source))).answers,
      answer.val.representative = source ∧ answer.val.firing = receipt := by
  have admitted := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.request_admitted plan bound (.base "Cfg")
    rfl plan_foundation typed
  have root := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.root_eq plan bound (.base "Cfg") typed
  have rootValid : receipt.Valid plan bound (.base "Cfg") (request bound source).root := by
    unfold request
    rw [root]
    exact valid
  obtain ⟨answer, listed, same, firing⟩ :=
    GeneralOccurrenceFrontier.LocalEquationFree.completed_occurrence_coverage admitted plan_equations
      (GeneralOccurrenceFrontier.LocalEquationFree.run_reachable _ _)
      (GeneralOccurrenceFrontier.LocalEquationFree.complete_at_workBound admitted plan_equations plan_generic)
      receipt rootValid
  exact ⟨answer, listed, same.trans root, firing⟩

theorem whole_profile_formula_complete {Leaf : Type} (tests : Leaf → Test (theory []) (Source []))
    (formula : Formula Leaf) (source : Pattern) (typed : Source [] source) :
    (check (backend []) tests formula source (workBound (backend []) tests formula source)).Decided :=
  checked_complete (backend []) tests formula source typed _ (Nat.le_refl _)

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend
