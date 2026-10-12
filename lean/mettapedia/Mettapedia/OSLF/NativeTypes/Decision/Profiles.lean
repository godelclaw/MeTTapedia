import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface
import Mettapedia.OSLF.NativeTypes.Decision.Stream.Attach
import Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver

open Mettapedia.OSLF.Framework

/-!
# Actual rho and scoped lambda streams for native formula execution

The cursor adapters consume the existing suspended matchers directly. Receipt
membership is attached without computing a complete list. Primitive structural
tests have fixed finite decomposition schedules: three quotient representatives
for rho, and the single local constructor inspection for equation-free lambda.
One leaf evaluation is a declared primitive job; its internal arithmetic and
typing checks are not machine-instruction counts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Profiles

open Mettapedia.GSLT
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling Mettapedia.OSLF.NativeTypes.Decision.Machine
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.OSLF.Binding LambdaContextualRung

/-- A fixed finite primitive test, delayed until its own job is advanced.
The fixed schedule is checked against the existing independent leaf theorem. -/
def fixedTest {system : GSLT.{0}} {admitted : system.Term → Prop}
    (test : Test system admitted) (bound : Nat)
    (schedule : ∀ source, test.completionBudget source ≤ bound) : LeafBackend system admitted where
  predicate := test.predicate
  tasks source := .pause fun _ => .yield (test.run bound source) fun _ => .done
  complete source sourceAdmitted :=
    ⟨test.run bound source, by simp [Stream.flatten],
      test.run_decided bound source sourceAdmitted (schedule source)⟩

def rhoTasks (source : rhoReflectiveGSLT.Term) :
    Stream (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source) :=
  (Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.tasks source.1).mapAttached fun item =>
    ⟨item.val, by rw [← Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.flatten_tasks]; exact item.property⟩

theorem rho_tasks_member (source : rhoReflectiveGSLT.Term)
    (receipt : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source) :
    receipt ∈ (rhoTasks source).flatten := by
  apply (Stream.mem_flatten_mapAttached _ _ receipt).mpr
  refine ⟨⟨receipt.val, ?_⟩, ?_⟩
  · rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.flatten_tasks]
    exact receipt.property
  · rfl

theorem rho_tasks_order (source : rhoReflectiveGSLT.Term) :
    ((rhoTasks source).flatten.map Subtype.val) = Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts source.1 := by
  rw [rhoTasks, Stream.flatten_mapAttached, List.map_map]
  change (Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.tasks source.1).flatten.attach.map Subtype.val = _
  rw [List.attach_map_subtype_val, Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.flatten_tasks]

theorem rho_tasks_work (source : rhoReflectiveGSLT.Term) :
    (rhoTasks source).workBound = (Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.tasks source.1).workBound :=
  Stream.workBound_mapAttached _ _

def rho : CursorBackend rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted where
  Receipt := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt
  target := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget
  tasks := rhoTasks
  sound source receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_sound source receipt
  coverage source _ actual step := by
    obtain ⟨item, listed, target⟩ :=
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_successors_exact source actual).mp step
    let receipt : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source := ⟨item, listed⟩
    refine ⟨receipt, rho_tasks_member source receipt, ?_⟩
    apply (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_equations_exact _ _).mpr
    rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_pattern]
    change canonicalize actual.1 = canonicalize item.target
    rw [target, canonicalize_idempotent]
  target_admitted source _ receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_admitted source receipt

def rhoLeaves (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf) :
    LeafBackend rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted :=
  fixedTest (Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.tests configuration leaf) 3 (fun _ => Nat.le_refl _)

def lambda (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (context : Ctx sig) :
    CursorBackend (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory selection context)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source context) where
  Receipt source := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Firing selection source
  target _ receipt := receipt.target
  tasks := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.tasks selection
  sound source receipt listed := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings_sound source receipt (by
    exact (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.flatten_tasks selection source) ▸ listed)
  coverage source _ target step := by
    obtain ⟨receipt, listed, same⟩ := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings_complete step
    exact ⟨receipt, (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.flatten_tasks selection source).symm ▸ listed, same.symm⟩
  target_admitted _ _ receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted receipt.target

def lambdaLeaves (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration) (context : Ctx sig)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Leaf) :
    LeafBackend (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory configuration.rules context)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source context) :=
  fixedTest (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.tests configuration context leaf) 0 (fun _ => Nat.le_refl _)

theorem rho_leaf_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf) :
    (rhoLeaves configuration leaf).predicate = (Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.tests configuration leaf).predicate := rfl

theorem lambda_leaf_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration)
    (context : Ctx sig) (leaf : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Leaf) :
    (lambdaLeaves configuration context leaf).predicate =
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.tests configuration context leaf).predicate := rfl

end Mettapedia.OSLF.NativeTypes.Decision.Profiles
