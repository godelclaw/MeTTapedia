import Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching
import Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend

open Mettapedia.OSLF.Framework

/-!
# Resumable matching on the original rho presentation

Canonicalization, primitive binding consistency and reflective substitution
are individual jobs. Pattern inspections and matching alternatives are
suspended separately. A work budget counts pauses and yielded receipts for
this cursor; it does not bound the internal cost of each primitive job.

The complete readout is proved equal to the original COMM matcher, including
every physical alternative and its ordinal. Original ParCong successor
coverage and the original authored equation relation remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled

open Mettapedia.OSLF.MeTTaIL Syntax Match ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

def equivalent : Pattern → Pattern → Bool :=
  ReflectiveCanonical.canonicalEquivalent rhoReflectivePresentation.toReflectivePresentationDecl

theorem original_alternatives (source : Pattern) :
    Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.alternatives source =
      matchPatternWith equivalent rhoCommRewrite.left (canonicalize source) := by
  unfold Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.alternatives ReflectiveCanonical.matchPatternForRuleUsing
  have selected : matchingPresentationForRule? rhoReflectionProfile rhoCommRewrite =
      some rhoReflectivePresentation.toReflectivePresentationDecl := by decide
  rw [selected]
  rfl

def tasks (source : Pattern) : Stream Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Receipt := .pause fun _ =>
  Stream.mapIdx (fun bindings ordinal => Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipt (bindings, ordinal))
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching.patternMatches equivalent rhoCommRewrite.left (canonicalize source))

theorem flatten_tasks (source : Pattern) :
    (tasks source).flatten = Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts source := by
  change (Stream.mapIdx _ _).flatten = _
  rw [Stream.flatten_mapIdx_zero, Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching.flatten_matches]
  rw [← original_alternatives]
  rfl

def state (budget : Nat) (source : Pattern) := Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (tasks source) budget
def frontier (budget : Nat) (source : Pattern) := (state budget source).outputs
def closed (budget : Nat) (source : Pattern) := (state budget source).closed
def completionBudget (source : Pattern) := (tasks source).workBound
def targets (budget : Nat) (source : Pattern) := (frontier budget source).map (·.target)

theorem exact_resume (first more : Nat) (source : Pattern) :
    state (first + more) source = resume more (state first source) :=
  run_resume _ _ _

theorem ordered_partition (budget : Nat) (source : Pattern) :
    frontier budget source ++ (state budget source).pending.flatten =
      Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts source :=
  (run_partition _ _).trans (flatten_tasks source)

theorem frontier_member {budget : Nat} {source : Pattern} {item : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Receipt}
    (listed : item ∈ frontier budget source) : item ∈ Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts source := by
  rw [← flatten_tasks source]
  exact listed_sound _ _ _ listed

theorem closed_frontier_exact (budget : Nat) (source : Pattern)
    (complete : closed budget source = true) :
    frontier budget source = Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts source :=
  (closed_readout _ _ complete).trans (flatten_tasks source)

theorem complete_at (source : Pattern) : closed (completionBudget source) source = true :=
  run_closed_at _ _ (Nat.le_refl _)

theorem frontier_stable (source : Pattern) (budget : Nat) (enough : completionBudget source ≤ budget) :
    frontier budget source = frontier (completionBudget source) source :=
  congrArg Cursor.outputs (run_stable _ _ enough)

theorem closed_stable (source : Pattern) (budget : Nat) (enough : completionBudget source ≤ budget) :
    closed budget source = closed (completionBudget source) source :=
  congrArg Cursor.closed (run_stable _ _ enough)

def originalFrontier (budget : Nat) (source : rhoReflectiveGSLT.Term) :
    List (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source) :=
  (frontier budget source.1).attach.map fun item => ⟨item.1, frontier_member item.2⟩

theorem originalFrontier_mem (budget : Nat) (source : rhoReflectiveGSLT.Term)
    (item : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source) :
    item ∈ originalFrontier budget source ↔ item.1 ∈ frontier budget source.1 := by
  constructor
  · intro listed
    obtain ⟨candidate, listed, same⟩ := List.mem_map.mp listed
    have equal : candidate.1 = item.1 := congrArg Subtype.val same
    rw [← equal]
    exact candidate.2
  · intro listed
    refine List.mem_map.mpr ⟨⟨item.1, listed⟩, List.mem_attach _ _, ?_⟩
    rfl

theorem originalFrontier_stable (source : rhoReflectiveGSLT.Term) (budget : Nat)
    (enough : completionBudget source.1 ≤ budget) :
    originalFrontier budget source = originalFrontier (completionBudget source.1) source := by
  apply (List.map_inj_right (fun left right same => Subtype.ext same)).mp
  simp only [originalFrontier, List.map_map, Function.comp_def]
  change (frontier budget source.1).attach.map Subtype.val =
    (frontier (completionBudget source.1) source.1).attach.map Subtype.val
  rw [List.attach_map_subtype_val, List.attach_map_subtype_val, frontier_stable source.1 budget enough]

def backend : Backend rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted where
  Receipt := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt
  target := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget
  frontier := originalFrontier
  closed budget source := closed budget source.1
  sound _ source receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_sound source receipt
  coverage budget source complete actual step := by
    obtain ⟨item, listed, target⟩ := (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_successors_exact source actual).mp step
    let owned : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt source := ⟨item, listed⟩
    refine ⟨owned, (originalFrontier_mem budget source owned).mpr ?_, ?_⟩
    · rw [closed_frontier_exact budget source.1 complete]
      exact listed
    · apply (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_equations_exact _ _).mpr
      rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_pattern]
      change canonicalize actual.1 = canonicalize item.target
      rw [target, canonicalize_idempotent]
  target_admitted _ source _ receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_admitted source receipt
  completionBudget source := completionBudget source.1
  complete_at source _ := complete_at source.1
  frontier_stable := originalFrontier_stable
  closed_stable source budget enough := closed_stable source.1 budget enough

theorem whole_formula_complete {Leaf : Type} (tests : Leaf → Test rhoReflectiveGSLT
    Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted) (formula : Formula Leaf) (source : rhoReflectiveGSLT.Term) :
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend tests formula source
      (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.workBound backend tests formula source)).Decided :=
  checked_complete backend tests formula source
    (Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted source) _ (Nat.le_refl _)

theorem zero_work_keeps_matching_suspended (source : Pattern) :
    frontier 0 source = [] ∧ closed 0 source = false := by
  constructor <;> rfl

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled
