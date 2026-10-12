import Mettapedia.OSLF.Syntax.RhoScopedParallelModalMetric

/-!
# Question-order controls on actual rho interaction states

Both enumerations cover every finite question. One asks about the missing
communication partner first; the other inserts an always-true question
before it. The same waiting input and zero have distances one and one half.
Their logical equivalence kernels nevertheless agree on every process pair.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelModalMetricControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedEquationEventControls RhoScopedParallelModalAdequacy
open RhoScopedParallelModalEnumeration RhoScopedParallelModalControls
open Mettapedia.GSLT.Logic

def interactionFirst : Nat → Finitary.Formula []
  | 0 => outputQuery
  | index + 1 => enumeration [] index

def truthFirst : Nat → Finitary.Formula []
  | 0 => .top
  | index + 1 => interactionFirst index

theorem interactionFirst_covers : Function.Surjective interactionFirst := by
  intro formula
  obtain ⟨index, readout⟩ := enumeration_covers [] formula
  exact ⟨index + 1, readout⟩

theorem truthFirst_covers : Function.Surjective truthFirst := by
  intro formula
  obtain ⟨index, readout⟩ := interactionFirst_covers formula
  exact ⟨index + 1, readout⟩

def questions (enumerate : Nat → Finitary.Formula []) : BudgetedObservations (Process []) :=
  enumeratedTests (fun index => Finitary.Holds sourceRules core (enumerate index))

theorem outputQuery_separates :
    ¬ (Finitary.Holds sourceRules core outputQuery (project waitingInput) ↔
      Finitary.Holds sourceRules core outputQuery (zero [])) :=
  fun same => zero_rejects_outputQuery (same.mp input_answers_outputQuery)

theorem interactionFirst_distance :
    (questions interactionFirst).distance (project waitingInput) (zero []) = 1 := by
  have result := enumerated_distance_first
    (fun index => Finitary.Holds sourceRules core (interactionFirst index))
    (project waitingInput) (zero []) 0 outputQuery_separates
    (fun index impossible => False.elim (Nat.not_lt_zero index impossible))
  simpa only [questions, pow_zero] using result

theorem truthFirst_distance :
    (questions truthFirst).distance (project waitingInput) (zero []) = 1 / 2 := by
  have result := enumerated_distance_first
    (fun index => Finitary.Holds sourceRules core (truthFirst index))
    (project waitingInput) (zero []) 1 outputQuery_separates (by
      intro index before
      have : index = 0 := by omega
      subst index
      constructor
      · intro _
        exact (Finitary.holds_iff_interface sourceRules core .top (zero [])).mpr trivial
      · intro _
        exact (Finitary.holds_iff_interface sourceRules core .top (project waitingInput)).mpr trivial)
  simpa only [questions, pow_one] using result

/-- Coverage fixes the zero kernel, although the numeric distance changes. -/
theorem kernels_agree (first second : Process []) :
    (questions interactionFirst).distance first second = 0 ↔
      (questions truthFirst).distance first second = 0 :=
  (enumerated_zero_iff (Finitary.Holds sourceRules core) interactionFirst
    interactionFirst_covers first second).trans
      (enumerated_zero_iff (Finitary.Holds sourceRules core) truthFirst
        truthFirst_covers first second).symm

theorem enumeration_changes_actual_distance :
    (questions interactionFirst).distance (project waitingInput) (zero []) ≠
      (questions truthFirst).distance (project waitingInput) (zero []) := by
  rw [interactionFirst_distance, truthFirst_distance]
  norm_num

end Mettapedia.OSLF.Binding.RhoScopedParallelModalMetricControls
