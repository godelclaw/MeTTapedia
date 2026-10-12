import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMeasures
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mathlib.Data.List.Perm.Subperm

/-!
# Declaration-derived structural descent of recursive premises

A recursive premise can call every authored declaration, including itself,
when its instantiated source has fewer tree nodes than the enclosing matched
source. The admission check derives this fact from the authored schemas:
the source has a smaller constant contribution and uses no metavariable more
often than the left-hand side. Binder occurrence spines are checked variable
renamings, so their instantiation preserves captured body sizes.

Collection-rest splicing and explicit substitution in recursive sources are
excluded by the same executable side check. Quantified recursive premises
require a separate lexical-shadowing comparison and are not admitted here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent

open Syntax RuleBinding ScopedRuleMatching PatternTreeSize
open GeneralEquationMeasures GeneralEquationAdmission GeneralScopedMatchMeasures

/-- This check compares every variable multiplicity, rather than just raw
schema sizes. It is independent of rule order and declaration names. -/
def checkAffine (parent child : Pattern) : Bool :=
  decide (constantContribution child < constantContribution parent) &&
    decide (child.freeFvarNames.Subperm parent.freeFvarNames)

private theorem sublist_weight_le (weights : String → Nat) {first second : List String}
    (included : first.Sublist second) :
    (first.map weights).sum ≤ (second.map weights).sum := by
  induction included with
  | slnil => exact Nat.le_refl _
  | cons name _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons name _ ih => simp only [List.map_cons, List.sum_cons]; omega

theorem subperm_weight_le (weights : String → Nat) {first second : List String}
    (included : first.Subperm second) :
    (first.map weights).sum ≤ (second.map weights).sum := by
  obtain ⟨middle, permuted, sublist⟩ := included
  rw [← (permuted.map weights).sum_eq]
  exact sublist_weight_le weights sublist

/-- Independently quantified schema meaning: every assignment of captured
body sizes produces a strict decrease. -/
def AffineDescent (parent child : Pattern) : Prop :=
  ∀ weights : String → Nat, evaluate weights child < evaluate weights parent

theorem checkAffine_sound {parent child : Pattern}
    (checked : checkAffine parent child = true) : AffineDescent parent child := by
  simp only [checkAffine, Bool.and_eq_true, decide_eq_true_eq] at checked
  intro weights
  have smaller := subperm_weight_le weights checked.2
  rw [evaluate_affine, evaluate_affine]
  omega

def checkSource (rule : RewriteRule) (spec : RuleBindingSpec)
    (premiseIndex quantifierDepth localDepth : Nat) (source : Pattern) : Bool :=
  checkSide rule spec .left [] 0 rule.left &&
    checkSide rule spec (.premise premiseIndex quantifierDepth 0) [] localDepth source &&
      checkAffine rule.left source

def checkPremise (rule : RewriteRule) (spec : RuleBindingSpec)
    (premiseIndex quantifierDepth : Nat) : Premise → Bool
  | .congruence source _ => checkSource rule spec premiseIndex quantifierDepth 0 source
  | .scopedStep step =>
      checkSource rule spec premiseIndex quantifierDepth step.binders.length step.source
  | .forAll _ _ body => (GeneralPremise.stepSources body).isEmpty
  | _ => true

def checkPremises (rule : RewriteRule) (spec : RuleBindingSpec) :
    Nat → List Premise → Bool
  | _, [] => true
  | index, premise :: premises =>
      checkPremise rule spec index 0 premise && checkPremises rule spec (index + 1) premises

def checkRule (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  admittedFor rule spec && checkPremises rule spec 0 rule.premises

def checkEnvironment (environment : GeneralPremise.Environment) : Bool :=
  environment.language.rewrites.zipIdx.all fun (rule, index) =>
    match GeneralPremise.specification? environment index with
    | none => false
    | some spec => checkRule rule spec

theorem checkEnvironment_rule {environment : GeneralPremise.Environment}
    (checked : checkEnvironment environment = true) {index : Nat} {rule : RewriteRule}
    (declared : environment.language.rewrites[index]? = some rule) :
    ∃ spec, GeneralPremise.specification? environment index = some spec ∧
      checkRule rule spec = true := by
  have member : (rule, index) ∈ environment.language.rewrites.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr declared
  have entry := List.all_eq_true.mp checked (rule, index) member
  cases found : GeneralPremise.specification? environment index with
  | none => simp [found] at entry
  | some spec => exact ⟨spec, rfl, by simpa only [found] using entry⟩

/-- The actual caller match and premise instantiation are compared through
their independent semantics. Both may occur under arbitrary ambient binders.
Premises may extend an assignment, but cannot overwrite an earlier capture. -/
theorem actual_source_decreases {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient premiseIndex quantifierDepth localDepth : Nat}
    {captured assignment : Assignment} {parent child source : Pattern}
    (checked : checkSource rule spec premiseIndex quantifierDepth localDepth source = true)
    (matching : GeneralScopedMatch.Matches rule spec ambient .left [] 0 []
      rule.left parent captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule spec ambient
      (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source = some child) :
    nodes child < nodes parent := by
  simp only [checkSource, Bool.and_eq_true] at checked
  have parentCount := matched_nodes matching checked.1.1 extension
  have childCount := instantiate_nodes rule spec ambient
    (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source child
    checked.1.2 instantiated
  rw [parentCount, childCount]
  exact checkAffine_sound checked.2 (capturedWeight assignment)

/-- The source relation is independently well-founded, without supplying a
per-language execution rank. -/
def Smaller (child parent : Pattern) : Prop := nodes child < nodes parent

theorem smaller_wellFounded : WellFounded Smaller :=
  InvImage.wf nodes Nat.lt_wfRel.wf

theorem checked_call_wellFounded {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient premiseIndex quantifierDepth localDepth : Nat}
    {captured assignment : Assignment} {parent child source : Pattern}
    (checked : checkSource rule spec premiseIndex quantifierDepth localDepth source = true)
    (matching : GeneralScopedMatch.Matches rule spec ambient .left [] 0 []
      rule.left parent captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule spec ambient
      (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source = some child) :
    Smaller child parent :=
  actual_source_decreases checked matching extension instantiated

end Mettapedia.OSLF.MeTTaIL.StructuralDescent
