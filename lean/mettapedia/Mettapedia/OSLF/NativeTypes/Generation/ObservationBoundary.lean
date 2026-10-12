import Mettapedia.OSLF.NativeTypes.Generation.Checking
import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples
import Mettapedia.OSLF.NativeTypes.Structural.Controls

open Mettapedia.OSLF.Framework

/-!
# Observation and checkability boundaries of generated fragments

A chosen conjunctive fragment has genuine generated formation rules, but it
cannot distinguish two typed states with different operational capabilities.
Structural observation has a separate index. These are semantic separating
controls, not an unconditional adequacy assertion about generated systems.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Structural
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

def conjunctiveOnly : ConnectiveFragment :=
  {core := {top := true, conj := true, structural := false, modal := false, possibility := false}}

/-- Every formed question of this chosen fragment holds at every state. The
proof ranges over the independent formation derivation, not a hand formula list. -/
theorem conjunctive_questions_hold {language : LanguageDef}
    {atomSort : Nat → Option TypeExpr} {expected : TypeExpr} {formula : Formula}
    (formed : Formed language atomSort conjunctiveOnly expected formula)
    (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (equation : TypeExpr → Pattern → Pattern → Prop) (atom : TypeExpr → Nat → Pattern → Prop)
    (term : Pattern) : Holds language free bound equation atom expected formula term := by
  induction formed with
  | top => trivial
  | bottom expected enabled => cases enabled
  | atom index enabled sort => cases enabled
  | conj enabled first second ihFirst ihSecond => exact ⟨ihFirst, ihSecond⟩
  | disj enabled first second => cases enabled
  | imp enabled first second => cases enabled
  | neg enabled inner => cases enabled
  | root index declaration enabled lookup sort => cases enabled
  | split index declaration firstParam secondParam enabled lookup sort arity firstType secondType first second =>
      cases enabled
  | spatial index declaration shape enabled lookup sort spatial first second => cases enabled

private theorem done_class {source target : Pattern}
    (equivalent : Relation.EqvGen Eqv source target) : source = done ↔ target = done := by
  induction equivalent with
  | rel source target equated =>
      rcases equation_events equated with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [alpha, beta, done]
      · simp [alpha, beta, done]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem done_has_no_primitive {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid runtimePlan [] carrier done) : False := by
  have root := root_only_site valid.1.2
  have actualRule := receipt.job.selected_rule valid.1
  have firing := valid.2.1
  rw [root] at firing
  have selected : (receipt.job.declaration = firstDeclaration ∧ receipt.job.ordinal = 0) ∨
      (receipt.job.declaration = secondDeclaration ∧ receipt.job.ordinal = 1) := by
    simpa only [runtimePlan, List.zipIdx_cons, List.zipIdx_nil, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq, Nat.zero_add] using valid.1.1
  cases firing with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selectedRule _ _ _ matched _ _ _ _ =>
      have same : rule = receipt.job.declaration.rule := Option.some.inj (selectedRule.symm.trans actualRule)
      subst rule
      rcases selected with ⟨first, _⟩ | ⟨second, _⟩
      · rw [first] at matched
        exact (by decide +kernel : done ≠ beta) (nullary_matching matched)
      · rw [second] at matched
        exact (by decide +kernel : done ≠ other) (nullary_matching matched)

theorem done_has_no_step : ¬ ∃ target,
    (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step done target := by
  rintro ⟨target, representative, firing, before, fired, _⟩
  have same : representative = done := (done_class before).mp rfl
  subst representative
  exact done_has_no_primitive fired

/-- The selected fragment agrees on every independently formed question,
while the two actual systems disagree on enabled reduction. -/
theorem generated_fragment_need_not_be_adequate :
    (∀ atomSort formula, Formed language atomSort conjunctiveOnly carrier formula →
      ∀ atom, Holds language snapshot.free []
          (fun _ => Relation.EqvGen Eqv) atom carrier formula other ↔
        Holds language snapshot.free [] (fun _ => Relation.EqvGen Eqv) atom carrier formula done) ∧
      (∃ target, (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step other target) ∧
      ¬ ∃ target, (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step done target := by
  refine ⟨?_, ⟨alpha, other_steps_alpha⟩, done_has_no_step⟩
  intro atomSort formula formed atom
  exact ⟨fun _ => conjunctive_questions_hold formed _ _ _ _ done,
    fun _ => conjunctive_questions_hold formed _ _ _ _ other⟩

end Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary
