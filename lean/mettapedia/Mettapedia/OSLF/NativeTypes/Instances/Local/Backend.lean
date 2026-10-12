import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Native decisions from actual equation-free occurrence jobs

The backend retains the real occurrence receipts and checks their drained
archives. Source typing is a separate admission gate. Complete rule and
premise work is derived from the checked compiled profile, rather than supplied
as a completeness field for an unrelated successor function.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Local.Backend

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

def request (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨plan, bound, type, source⟩

def Source (source : Pattern) : Prop :=
  OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type source

def sourceChecked (source : Pattern) : Bool :=
  checkOpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type source

abbrev Receipt (source : Pattern) :=
  GeneralOccurrenceNativeReceipts.ReceiptFamily plan bound type source

theorem root_eq {source : Pattern} (typed : Source plan bound type source) :
    (request plan bound type source).root = source :=
  Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1

def transport {source : Pattern} (typed : Source plan bound type source)
    (receipt : GeneralOccurrenceFrontier.Answer (request plan bound type source)) :
    Receipt plan bound type source :=
  ⟨receipt.val, by
    simpa only [request, GeneralOccurrenceFrontier.Request.root,
      Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1] using receipt.property⟩

def frontier (budget : Nat) (source : Pattern) : List (Receipt plan bound type source) :=
  if checked : sourceChecked plan bound type source = true then
    let typed := checkOpenPatternWellSorted_sound checked
    ((GeneralOccurrenceFrontier.LocalEquationFree.run (request plan bound type source) budget).answers).map
      (transport plan bound type typed)
  else []

def closed (budget : Nat) (source : Pattern) : Bool :=
  sourceChecked plan bound type source &&
    GeneralOccurrenceFrontier.checkCertificate (request plan bound type source)
      (GeneralOccurrenceFrontier.LocalEquationFree.run (request plan bound type source) budget)

def completionBudget (source : Pattern) : Nat :=
  GeneralOccurrenceFrontier.LocalEquationFree.workBound (request plan bound type source)

theorem request_admitted
    (compiled : plan = GeneralExecutionAdmission.compile plan.snapshot plan.permissions)
    (foundation : plan.complete = true) {source : Pattern} (typed : Source plan bound type source) :
    GeneralOccurrenceFrontier.Admitted (request plan bound type source) := by
  refine ⟨compiled, foundation, ?_⟩
  rw [root_eq plan bound type typed]
  exact typed

theorem frontier_sound (budget : Nat) (source : Pattern)
    (receipt : Receipt plan bound type source) :
    receipt ∈ frontier plan bound type budget source →
      (GeneralOccurrenceSemantics.gslt plan bound type).Step source receipt.val.target := by
  intro _
  exact GeneralOccurrenceSemantics.Receipt.semantic_step plan bound type receipt.property

theorem frontier_target_admitted (budget : Nat) (source : Pattern)
    (receipt : Receipt plan bound type source) :
    receipt ∈ frontier plan bound type budget source → Source plan bound type receipt.val.target := by
  intro _
  exact GeneralOccurrenceSemantics.Receipt.target_sorted plan bound type receipt.property

theorem frontier_coverage
    (compiled : plan = GeneralExecutionAdmission.compile plan.snapshot plan.permissions)
    (foundation : plan.complete = true) (budget : Nat) (source : Pattern)
    (certified : closed plan bound type budget source = true) (target : Pattern)
    (stepped : (GeneralOccurrenceSemantics.gslt plan bound type).Step source target) :
    ∃ receipt, receipt ∈ frontier plan bound type budget source ∧
      (GeneralOccurrenceSemantics.gslt plan bound type).Equiv target receipt.val.target := by
  simp only [closed, Bool.and_eq_true] at certified
  have typed : Source plan bound type source := checkOpenPatternWellSorted_sound certified.1
  have admitted := request_admitted plan bound type compiled foundation typed
  have rootStep : (GeneralOccurrenceSemantics.gslt plan bound type).Step
      (request plan bound type source).root target := by
    rw [root_eq plan bound type typed]
    exact stepped
  obtain ⟨answer, listed, equivalent⟩ :=
    (GeneralOccurrenceFrontier.certified_successor_classes admitted certified.2 target).mpr rootStep
  refine ⟨transport plan bound type typed answer, ?_, equivalent.symm⟩
  simp only [frontier, certified.1, dite_true]
  exact List.mem_map.mpr ⟨answer, listed, rfl⟩

theorem closed_at_completion
    (compiled : plan = GeneralExecutionAdmission.compile plan.snapshot plan.permissions)
    (foundation : plan.complete = true) (equationFree : plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric plan = true)
    (source : Pattern) (typed : Source plan bound type source) :
    closed plan bound type (completionBudget plan bound type source) source = true := by
  have admitted := request_admitted plan bound type compiled foundation typed
  have checked := checkOpenPatternWellSorted_complete typed
  have certified := GeneralOccurrenceFrontier.LocalEquationFree.certificate_at_workBound
    admitted equationFree generic
  exact Bool.and_eq_true_iff.mpr ⟨checked, certified⟩

theorem frontier_stable (equationFree : plan.equations = [])
    (source : Pattern) (budget : Nat) (enough : completionBudget plan bound type source ≤ budget) :
    frontier plan bound type budget source =
      frontier plan bound type (completionBudget plan bound type source) source := by
  have stable := GeneralOccurrenceFrontier.LocalEquationFree.run_stable
    (request := request plan bound type source) equationFree budget enough
  simp only [frontier, completionBudget, stable]

theorem closed_stable (equationFree : plan.equations = [])
    (source : Pattern) (budget : Nat) (enough : completionBudget plan bound type source ≤ budget) :
    closed plan bound type budget source =
      closed plan bound type (completionBudget plan bound type source) source := by
  have stable := GeneralOccurrenceFrontier.LocalEquationFree.run_stable
    (request := request plan bound type source) equationFree budget enough
  simp only [closed, completionBudget, stable]

/-- All backend laws are instantiated by the actual local machine and its
finite work construction. The hypotheses are computable profile checks. -/
def backend
    (compiled : plan = GeneralExecutionAdmission.compile plan.snapshot plan.permissions)
    (foundation : plan.complete = true) (equationFree : plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric plan = true) :
    Backend (GeneralOccurrenceSemantics.gslt plan bound type) (Source plan bound type) where
  Receipt := Receipt plan bound type
  target _ receipt := receipt.val.target
  frontier := frontier plan bound type
  closed := closed plan bound type
  sound := frontier_sound plan bound type
  coverage := frontier_coverage plan bound type compiled foundation
  target_admitted := by
    intro budget source _ receipt listed
    exact frontier_target_admitted plan bound type budget source receipt listed
  completionBudget := completionBudget plan bound type
  complete_at := closed_at_completion plan bound type compiled foundation equationFree generic
  frontier_stable := frontier_stable plan bound type equationFree
  closed_stable := closed_stable plan bound type equationFree

end Mettapedia.OSLF.NativeTypes.Instances.Local.Backend
