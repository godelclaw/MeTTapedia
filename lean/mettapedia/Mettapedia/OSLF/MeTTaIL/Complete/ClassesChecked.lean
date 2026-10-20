import Mettapedia.OSLF.MeTTaIL.Complete.Classes

/-!
# Every published target of the search modulo equations is well-sorted

A rule firing is published only when its target passes the well-sortedness check (`Step.lift`),
so every receipt in the log of a reached state has a checked target (`LogChecked`): it holds at
the start (`logChecked_begin`) and rounds keep it (`logChecked_rounds`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- A target that passes the plan's well-sortedness check. -/
def Checked (pattern : Pattern) : Prop :=
  checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
    pattern = true

/-- Every logged receipt has a checked target. -/
def LogChecked (state : State plan) : Prop := ∀ receipt ∈ state.log, Checked plan bound expected receipt.target

variable {plan bound expected}

theorem lift_checked {job : GeneralRuleJobs.Job} {firing : DeepRoot.Firing} {receipt : GeneralRuleJobs.Receipt}
    (lifted : Step.lift plan bound expected job firing = some receipt) : Checked plan bound expected receipt.target := by
  unfold Step.lift at lifted
  split at lifted
  · rename_i accepted
    cases lifted
    exact (Bool.and_eq_true_iff.mp accepted).2
  · cases lifted

theorem firings_checked : ∀ (key : Key) (payloads : List (family plan key).Payload),
    ∀ receipt ∈ firings (events plan bound expected key payloads), Checked plan bound expected receipt.target
  | .rule rep job, payloads, receipt, member => by
    simp only [events] at member
    induction payloads with
    | nil => simp [firings] at member
    | cons payload rest ih =>
      simp only [List.filterMap_cons] at member
      split at member
      · exact ih member
      · rename_i lifted
        simp only [List.map_cons, firings, List.mem_cons] at member
        rcases member with rfl | later
        · exact lift_checked lifted
        · exact ih later
  | .forward rep lane, payloads, receipt, member => by
    simp only [events] at member
    generalize payloads.filterMap (EquationJob.lift plan bound expected lane) = items at member
    induction items with
    | nil => simp [firings] at member
    | cons _ rest ih => simp only [List.map_cons, firings] at member; exact ih member
  | .backward rep candidate lane, payloads, receipt, member => by
    simp only [events] at member
    generalize (payloads.filterMap (EquationJob.lift plan bound expected lane)).filter
        (fun receipt => receipt.target == rep.pattern) = items at member
    induction items with
    | nil => simp [firings] at member
    | cons _ rest ih => simp only [List.map_cons, firings] at member; exact ih member

theorem firings_append_mem {receipt : GeneralOccurrenceSemantics.Receipt} :
    ∀ first second : List Event, receipt ∈ firings (first ++ second) →
      receipt ∈ firings first ∨ receipt ∈ firings second
  | [], _, member => Or.inr member
  | .firing other :: rest, second, member => by
    simp only [List.cons_append, firings, List.mem_cons] at member ⊢
    rcases member with same | later
    · exact Or.inl (Or.inl same)
    · exact (firings_append_mem rest second later).imp Or.inr id
  | .discovery _ _ :: rest, second, member => by
    simp only [List.cons_append, firings] at member ⊢
    exact firings_append_mem rest second member

theorem logChecked_round {state : State plan} (checked : LogChecked plan bound expected state) :
    LogChecked plan bound expected (round plan bound expected state) := by
  intro receipt member
  simp only [round] at member
  rcases List.mem_append.mp member with old | new
  · exact checked receipt old
  · have flat : ∀ advanced : List (Entry plan × List Event),
        (∀ pair ∈ advanced, ∃ payloads, pair.2 = events plan bound expected pair.1.1 payloads) →
        receipt ∈ firings (advanced.flatMap Prod.snd) → Checked plan bound expected receipt.target := by
      intro advanced
      induction advanced with
      | nil => intro _ inside; simp [firings] at inside
      | cons pair rest ih =>
        intro shaped inside
        rw [List.flatMap_cons] at inside
        rcases firings_append_mem _ _ inside with here | later
        · obtain ⟨payloads, same⟩ := shaped pair (by simp)
          rw [same] at here
          exact firings_checked _ payloads receipt here
        · exact ih (fun other otherIn => shaped other (by simp [otherIn])) later
    refine flat _ ?_ new
    intro pair inside
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
    exact ⟨_, rfl⟩

theorem logChecked_rounds : ∀ (work : Nat) {state : State plan}, LogChecked plan bound expected state →
    LogChecked plan bound expected (rounds plan bound expected work state)
  | 0, _, checked => checked
  | work + 1, _, checked => logChecked_rounds work (logChecked_round checked)

theorem logChecked_begin (source : Pattern) : LogChecked plan bound expected (begin plan bound expected source) := by
  intro receipt member
  simp [begin] at member

end Mettapedia.OSLF.MeTTaIL.Complete.Classes
