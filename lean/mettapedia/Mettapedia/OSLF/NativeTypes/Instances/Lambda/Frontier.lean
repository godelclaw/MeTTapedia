import Mettapedia.OSLF.Syntax.LambdaAuthoredCanonicalFreeComparison
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Finite contextual lambda frontiers

The four operational rules retain their authored declaration order. The
frontier follows only those rules' contexts; binder descent extends the
ambient context, and beta uses the existing capture-avoiding substitution.
Its coverage theorem concerns the independent contextual reduction relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier

open Mettapedia.OSLF.Binding
open LambdaContextualRung
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory PremiseEvent)

/-- Selected authored declarations, in the original source order. -/
structure Selection where
  beta : Bool := true
  lamCong : Bool := true
  appCongL : Bool := true
  appCongR : Bool := true
  deriving DecidableEq, Repr

/-- The least selected operational relation, specified independently of
frontier enumeration. -/
inductive SelectedStep (selection : Selection) : (Γ : Ctx sig) →
    Term sig Γ .term → Term sig Γ .term → Prop where
  | beta {Γ : Ctx sig} (enabled : selection.beta = true)
      (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term) :
      SelectedStep selection Γ (appT (lamT body) argument) (inst body argument)
  | lamCong {Γ : Ctx sig} (enabled : selection.lamCong = true)
      {source target : Term sig (.term :: Γ) .term}
      (child : SelectedStep selection (.term :: Γ) source target) :
      SelectedStep selection Γ (lamT source) (lamT target)
  | appCongL {Γ : Ctx sig} (enabled : selection.appCongL = true)
      {source target : Term sig Γ .term} (argument : Term sig Γ .term)
      (child : SelectedStep selection Γ source target) :
      SelectedStep selection Γ (appT source argument) (appT target argument)
  | appCongR {Γ : Ctx sig} (enabled : selection.appCongR = true)
      {source target : Term sig Γ .term} (function : Term sig Γ .term)
      (child : SelectedStep selection Γ source target) :
      SelectedStep selection Γ (appT function source) (appT function target)

theorem selected_sound {selection : Selection} {Γ : Ctx sig}
    {source target : Term sig Γ .term}
    (step : SelectedStep selection Γ source target) : Step Γ source target := by
  induction step with
  | beta _ body argument => exact .beta body argument
  | lamCong _ _ ih => exact .lamCong ih
  | appCongL _ argument _ ih => exact .appCongL argument ih
  | appCongR _ function _ ih => exact .appCongR function ih

theorem all_selected_exact {Γ : Ctx sig} {source target : Term sig Γ .term} :
    SelectedStep {} Γ source target ↔ Step Γ source target := by
  constructor
  · exact selected_sound
  · intro step
    induction step with
    | beta body argument => exact .beta rfl body argument
    | lamCong _ ih => exact .lamCong rfl ih
    | appCongL argument _ ih => exact .appCongL rfl argument ih
    | appCongR function _ ih => exact .appCongR rfl function ih

/-- Each entry keeps a complete context-indexed endpoint and its authored
history. Equal targets in different branches are not merged. -/
structure Firing (selection : Selection) {Γ : Ctx sig}
    (source : Term sig Γ .term) where
  target : Term sig Γ .term
  history : RuleHistory
  sound : SelectedStep selection Γ source target

def betaAtApp (selection : Selection) {Γ : Ctx sig}
    (function argument : Term sig Γ .term) : List (Firing selection (appT function argument)) :=
  match function with
  | .var _ => []
  | .op .app (.cons _ (.cons _ .nil)) => []
  | .op .lam (.cons body .nil) =>
      if enabled : selection.beta = true then
        [⟨inst body argument, .fire 0 [], .beta enabled body argument⟩]
      else []

def betaFirings (selection : Selection) {Γ : Ctx sig}
    (source : Term sig Γ .term) : List (Firing selection source) :=
  match source with
  | .var _ => []
  | .op .lam (.cons _ .nil) => []
  | .op .app (.cons function (.cons argument .nil)) => betaAtApp selection function argument

def liftLam {selection : Selection} (enabled : selection.lamCong = true)
    {Γ : Ctx sig} {body : Term sig (.term :: Γ) .term}
    (entry : Firing selection body) (ordinal : Nat) : Firing selection (lamT body) :=
  ⟨lamT entry.target, .fire 1 [.step 0 ordinal entry.history], .lamCong enabled entry.sound⟩

def liftAppL {selection : Selection} (enabled : selection.appCongL = true)
    {Γ : Ctx sig} {function : Term sig Γ .term} (argument : Term sig Γ .term)
    (entry : Firing selection function) (ordinal : Nat) : Firing selection (appT function argument) :=
  ⟨appT entry.target argument, .fire 2 [.step 0 ordinal entry.history],
    .appCongL enabled argument entry.sound⟩

def liftAppR {selection : Selection} (enabled : selection.appCongR = true)
    {Γ : Ctx sig} (function : Term sig Γ .term) {argument : Term sig Γ .term}
    (entry : Firing selection argument) (ordinal : Nat) : Firing selection (appT function argument) :=
  ⟨appT function entry.target, .fire 3 [.step 0 ordinal entry.history],
    .appCongR enabled function entry.sound⟩

mutual
def nodeCount : {Γ : Ctx sig} → {sort : Srt} → Term sig Γ sort → Nat
  | _, _, .var _ => 1
  | _, _, .op _ arguments => 1 + argumentNodeCount arguments
def argumentNodeCount : {Γ : Ctx sig} → {arity : List (List Srt × Srt)} →
    Args sig arity Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => nodeCount head + argumentNodeCount tail
end

/-- Structural recursion enumerates the finite legal redex positions. It
does not enumerate other terms of the source's size. -/
def firings (selection : Selection) : {Γ : Ctx sig} →
    (source : Term sig Γ .term) → List (Firing selection source)
  | _, .var _ => []
  | _, .op .lam (.cons body .nil) =>
      if enabled : selection.lamCong = true then
        (firings selection body).zipIdx.map fun (entry, ordinal) => liftLam enabled entry ordinal
      else []
  | _, .op .app (.cons function (.cons argument .nil)) =>
      betaFirings selection (appT function argument) ++
      (if enabled : selection.appCongL = true then
        (firings selection function).zipIdx.map fun (entry, ordinal) => liftAppL enabled argument entry ordinal
       else []) ++
      (if enabled : selection.appCongR = true then
        (firings selection argument).zipIdx.map fun (entry, ordinal) => liftAppR enabled function entry ordinal
       else [])
termination_by _ source => nodeCount source
decreasing_by all_goals simp only [nodeCount, argumentNodeCount]; omega

private theorem located_of_mem {Item : Type} {entry : Item} {entries : List Item}
    (member : entry ∈ entries) : ∃ ordinal, (entry, ordinal) ∈ entries.zipIdx := by
  obtain ⟨ordinal, found⟩ := List.mem_iff_getElem?.mp member
  exact ⟨ordinal, List.mk_mem_zipIdx_iff_getElem?.mpr found⟩

theorem firings_sound {selection : Selection} {Γ : Ctx sig}
    (source : Term sig Γ .term) (entry : Firing selection source)
    (_listed : entry ∈ firings selection source) :
    SelectedStep selection Γ source entry.target := entry.sound

theorem firings_complete {selection : Selection} {Γ : Ctx sig}
    {source target : Term sig Γ .term} (step : SelectedStep selection Γ source target) :
    ∃ entry ∈ firings selection source, entry.target = target := by
  induction step with
  | beta enabled body argument =>
      refine ⟨⟨inst body argument, .fire 0 [], .beta enabled body argument⟩, ?_, rfl⟩
      simp only [appT, firings, betaFirings, lamT, betaAtApp, enabled, dite_true]
      exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_singleton_self _))))
  | lamCong enabled child ih =>
      obtain ⟨entry, member, targetEq⟩ := ih
      obtain ⟨ordinal, located⟩ := located_of_mem member
      refine ⟨liftLam enabled entry ordinal, ?_, ?_⟩
      · simp only [lamT, firings, enabled, dite_true]
        exact List.mem_map.mpr ⟨(entry, ordinal), located, rfl⟩
      · exact congrArg lamT targetEq
  | appCongL enabled argument child ih =>
      obtain ⟨entry, member, targetEq⟩ := ih
      obtain ⟨ordinal, located⟩ := located_of_mem member
      refine ⟨liftAppL enabled argument entry ordinal, ?_, ?_⟩
      · simp only [appT, firings, enabled, dite_true]
        apply List.mem_append.mpr
        apply Or.inl
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨(entry, ordinal), located, rfl⟩)
      · exact congrArg (fun body => appT body argument) targetEq
  | appCongR enabled function child ih =>
      obtain ⟨entry, member, targetEq⟩ := ih
      obtain ⟨ordinal, located⟩ := located_of_mem member
      refine ⟨liftAppR enabled function entry ordinal, ?_, ?_⟩
      · simp only [appT, firings, enabled, dite_true]
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨(entry, ordinal), located, rfl⟩)
      · exact congrArg (appT function) targetEq

theorem full_frontier_exact {Γ : Ctx sig} (source target : Term sig Γ .term) :
    (∃ entry ∈ firings {} source, entry.target = target) ↔ Step Γ source target := by
  constructor
  · rintro ⟨entry, _, rfl⟩
    exact selected_sound entry.sound
  · intro step
    exact firings_complete (all_selected_exact.mpr step)

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier
