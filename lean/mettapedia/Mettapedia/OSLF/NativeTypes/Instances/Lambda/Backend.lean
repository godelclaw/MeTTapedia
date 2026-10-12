import Mettapedia.OSLF.NativeTypes.Instances.Lambda.EngineComparison
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# The original contextual lambda profile as a native decision backend

Intrinsic contexts enforce scope throughout each retained firing. The
authored comparison recovers exactly the original engine histories. The
finite frontier contains one receipt per physical beta occurrence and keeps
congruence history separate from that primitive event.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison LambdaPatternRendering
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier Mettapedia.OSLF.NativeTypes.Instances.Lambda.EngineComparison
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

def theory (selection : Selection) (Γ : Ctx sig) : Mettapedia.GSLT.GSLT where
  Term := Term sig Γ .term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SelectedStep selection Γ
  rewrites_resp_left := by intro source other target equal step; subst other; exact ⟨target, step, rfl⟩
  rewrites_resp_right := by intro source target other step equal; subst other; exact step

def Source (Γ : Ctx sig) (source : Term sig Γ .term) : Prop :=
  (encodeTerm source).isWellScopedAt Γ.length = true

theorem source_admitted {Γ : Ctx sig} (source : Term sig Γ .term) : Source Γ source :=
  encodeTerm_scoped source

def frontier (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  (firings selection source).take budget

def pending (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  (firings selection source).drop budget

def completionBudget (selection : Selection) {Γ : Ctx sig} (source : Term sig Γ .term) : Nat :=
  (firings selection source).length

def closed (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) : Bool :=
  decide (completionBudget selection source ≤ budget)

theorem frontier_complete {selection : Selection} {Γ : Ctx sig}
    {budget : Nat} {source : Term sig Γ .term} (complete : closed selection budget source = true) :
    frontier selection budget source = firings selection source :=
  List.take_of_length_le (of_decide_eq_true complete)

theorem frontier_partition (selection : Selection) {Γ : Ctx sig}
    (budget : Nat) (source : Term sig Γ .term) :
    frontier selection budget source ++ pending selection budget source = firings selection source :=
  List.take_append_drop budget _

theorem exact_resume (selection : Selection) {Γ : Ctx sig}
    (first more : Nat) (source : Term sig Γ .term) :
    frontier selection (first + more) source =
      frontier selection first source ++ (pending selection first source).take more :=
  List.take_add

def backend (selection : Selection) (Γ : Ctx sig) : Backend (theory selection Γ) (Source Γ) where
  Receipt source := Firing selection source
  target _ receipt := receipt.target
  frontier := frontier selection
  closed := closed selection
  sound _ _ receipt _ := receipt.sound
  coverage budget source complete target step := by
    obtain ⟨receipt, listed, targetEq⟩ := firings_complete step
    refine ⟨receipt, ?_, targetEq.symm⟩
    rw [frontier_complete complete]
    exact listed
  target_admitted _ _ _ receipt _ := source_admitted receipt.target
  completionBudget := completionBudget selection
  complete_at _ _ := decide_eq_true (Nat.le_refl _)
  frontier_stable source budget enough := by
    erw [frontier_complete (decide_eq_true enough),
      frontier_complete (decide_eq_true (Nat.le_refl _))]
  closed_stable source budget enough := by
    exact (decide_eq_true enough).trans (decide_eq_true (Nat.le_refl _)).symm

theorem full_theory_exact {Γ : Ctx sig} (source target : Term sig Γ .term) :
    (theory {} Γ).Step source target ↔ Step Γ source target := all_selected_exact

/-- Completeness is earned uniformly for every intrinsic context and every
selection of the original four operational declarations. -/
theorem whole_profile_complete (selection : Selection) (Γ : Ctx sig)
    (source : Term sig Γ .term) :
    (backend selection Γ).closed ((backend selection Γ).completionBudget source) source = true :=
  (backend selection Γ).complete_at source (source_admitted source)

/-- Every actual authored successor, and no additional successor, occurs in
the finite frontier; target equality is recovered by the checked decoder. -/
theorem authored_successors_exact {Γ : Ctx sig} (source target : Term sig Γ .term)
    (fuel : Nat) (enough : nodeCount source ≤ fuel) :
    (∃ history, (history, encodeTerm target) ∈
      rewriteAt RelationEnv.empty LambdaAuthoredFullRuleProfile.language fuel Γ.length
        (encodeTerm source)) ↔ Step Γ source target := by
  rw [engine_readout source fuel enough]
  constructor
  · rintro ⟨history, listed⟩
    obtain ⟨receipt, member, equal⟩ := List.mem_map.mp listed
    have targetEq : receipt.target = target :=
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_injective _ _ (congrArg Prod.snd equal)
    subst target
    exact selected_sound (firings_sound source receipt member)
  · intro step
    obtain ⟨receipt, member, targetEq⟩ := firings_complete (all_selected_exact.mpr step)
    refine ⟨receipt.history, List.mem_map.mpr ⟨receipt, member, ?_⟩⟩
    simp [targetEq]

theorem native_fragment_complete {Leaf : Type} (selection : Selection) (Γ : Ctx sig)
    (tests : Leaf → Test (theory selection Γ) (Source Γ))
    (formula : Formula Leaf) (source : Term sig Γ .term) :
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check (backend selection Γ) tests formula source
      (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.workBound (backend selection Γ) tests formula source)).Decided := by
  exact Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.checked_complete (backend selection Γ) tests formula source
    (source_admitted source) _ (Nat.le_refl _)

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend
