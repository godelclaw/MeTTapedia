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

The left-hand side may capture a collection rest, as a congruence through a bag
does (`{S, ...rest} ~> {T, ...rest}` with premise `S ~> T`): every captured
value has at least one node, so a metavariable of the left side that the source
leaves out is a strictly positive part of the parent. Collection-rest splicing
and explicit substitution in recursive sources are excluded by the same
executable side check. Quantified recursive premises require a separate
lexical-shadowing comparison and are not admitted here.
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

mutual
  /-- The number of metavariable occurrences, collection rests included, by structural
  recursion, so that the kernel evaluates it. -/
  def fvarCount : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 1
    | .apply _ arguments => fvarCountList arguments
    | .lambda _ body | .multiLambda _ _ body => fvarCount body
    | .subst body replacement => fvarCount body + fvarCount replacement
    | .collection _ elements rest => fvarCountList elements + rest.toList.length

  def fvarCountList : List Pattern → Nat
    | [] => 0
    | first :: rest => fvarCount first + fvarCountList rest
end

theorem fvarCount_eq (pattern : Pattern) : fvarCount pattern = pattern.freeFvarNames.length := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [fvarCount, Pattern.freeFvarNames]
  | hfvar name => simp [fvarCount, Pattern.freeFvarNames]
  | happly label arguments ih =>
    have lists : ∀ items : List Pattern, (∀ item ∈ items, fvarCount item = item.freeFvarNames.length) →
        fvarCountList items = (items.flatMap Pattern.freeFvarNames).length := by
      intro items each
      induction items with
      | nil => rfl
      | cons first rest tail =>
        simp only [fvarCountList, List.flatMap_cons, List.length_append, each first (by simp),
          tail (fun item member => each item (by simp [member]))]
    simp only [fvarCount, Pattern.freeFvarNames]
    exact lists arguments ih
  | hlambda binder body ih => simp [fvarCount, Pattern.freeFvarNames, ih]
  | hmultiLambda arity binders body ih => simp [fvarCount, Pattern.freeFvarNames, ih]
  | hsubst body replacement bodyIH replacementIH =>
    simp [fvarCount, Pattern.freeFvarNames, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    have lists : ∀ items : List Pattern, (∀ item ∈ items, fvarCount item = item.freeFvarNames.length) →
        fvarCountList items = (items.flatMap Pattern.freeFvarNames).length := by
      intro items each
      induction items with
      | nil => rfl
      | cons first rest tail =>
        simp only [fvarCountList, List.flatMap_cons, List.length_append, each first (by simp),
          tail (fun item member => each item (by simp [member]))]
    simp only [fvarCount, Pattern.freeFvarNames, List.length_append]
    rw [lists elements ih]

/-- Strict descent when every metavariable of the parent weighs at least one node: the child's
constant part, the parent's rests and one node per child metavariable stay below the parent's
constant part and one node per parent metavariable. -/
def checkDescent (parent child : Pattern) : Bool :=
  decide (constantContribution child + restCount parent + fvarCount child <
      constantContribution parent + fvarCount parent) &&
    decide (child.freeFvarNames.Subperm parent.freeFvarNames)

theorem checkDescent_sound {parent child : Pattern} (checked : checkDescent parent child = true)
    (weights : String → Nat) (positive : ∀ name ∈ parent.freeFvarNames, 1 ≤ weights name) :
    evaluate weights child + restCount parent < evaluate weights parent := by
  simp only [checkDescent, Bool.and_eq_true, decide_eq_true_eq, fvarCount_eq] at checked
  obtain ⟨counts, middle, reordered, sublist⟩ := checked
  obtain ⟨extra, permuted⟩ := sublist.exists_perm_append
  have sums : (parent.freeFvarNames.map weights).sum =
      (child.freeFvarNames.map weights).sum + (extra.map weights).sum := by
    rw [(permuted.map weights).sum_eq, List.map_append, List.sum_append, (reordered.map weights).sum_eq]
  have lengths : parent.freeFvarNames.length = child.freeFvarNames.length + extra.length := by
    rw [permuted.length_eq, List.length_append, reordered.length_eq]
  have heavy : extra.length ≤ (extra.map weights).sum := by
    have each : ∀ name ∈ extra, 1 ≤ weights name := fun name member =>
      positive name (permuted.symm.subset (List.mem_append_right _ member))
    clear sums lengths permuted counts
    induction extra with
    | nil => simp
    | cons head tail ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have first := each head (by simp)
      have rest := ih (fun name member => each name (by simp [member]))
      omega
  rw [evaluate_affine, evaluate_affine]
  omega

/-- A descending premise source: both sides are checked spines, the source has no collection rest,
and it is strictly smaller than the rule's left side (`checkDescent`). -/
def checkSource (rule : RewriteRule) (spec : RuleBindingSpec)
    (premiseIndex quantifierDepth localDepth : Nat) (source : Pattern) : Bool :=
  (checkSide rule spec .left [] 0 rule.left &&
    checkSide rule spec (.premise premiseIndex quantifierDepth 0) [] localDepth source &&
      restCount source == 0) &&
    checkDescent rule.left source

/-! ## Every free name of a matched pattern is captured -/

mutual
  theorem _root_.Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.Matches.captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
      {pattern target : Pattern}
      (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial pattern target final) :
      ∀ name ∈ pattern.freeFvarNames, ∃ value, lookup final name = some value := by
    cases matched with
    | capture captured =>
      intro name member
      simp only [Pattern.freeFvarNames, List.mem_singleton] at member
      subst member
      obtain ⟨_, _, value, _, _, _, found, _⟩ := GeneralScopedMatch.capture_interpretation captured
      exact ⟨value, found⟩
    | bound => intro name member; simp [Pattern.freeFvarNames] at member
    | constructor arguments =>
      intro name member
      simp only [Pattern.freeFvarNames] at member
      exact arguments.captures name member
    | binder body => intro name member; exact body.captures name (by simpa [Pattern.freeFvarNames] using member)
    | binders body => intro name member; exact body.captures name (by simpa [Pattern.freeFvarNames] using member)
    | substitution body replacement =>
      intro name member
      simp only [Pattern.freeFvarNames, List.mem_append] at member
      rcases member with inBody | inReplacement
      · obtain ⟨value, found⟩ := body.captures name inBody
        exact ⟨value, replacement.extends name value found⟩
      · exact replacement.captures name inReplacement
    | bag _ elements =>
      intro name member
      simp only [Pattern.freeFvarNames] at member
      exact elements.captures name member
    | vector arguments =>
      intro name member
      simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] at member
      exact arguments.captures name member
    | vectorRest arguments captured =>
      intro name member
      simp only [Pattern.freeFvarNames, Option.toList_some, List.mem_append, List.mem_singleton] at member
      rcases member with inElements | same
      · obtain ⟨value, found⟩ := arguments.captures name inElements
        exact ⟨value, GeneralScopedMatch.capture_extends captured name value found⟩
      · subst same
        obtain ⟨_, _, value, _, _, _, found, _⟩ := GeneralScopedMatch.capture_interpretation captured
        exact ⟨value, found⟩
  termination_by sizeOf pattern

  theorem _root_.Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.Arguments.captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern}
      (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index patterns targets final) :
      ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, ∃ value, lookup final name = some value := by
    cases matched with
    | nil => intro name member; simp at member
    | cons head tail =>
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with inHead | inTail
      · obtain ⟨value, found⟩ := head.captures name inHead
        exact ⟨value, tail.extends name value found⟩
      · exact tail.captures name inTail
  termination_by sizeOf patterns

  theorem _root_.Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.Bag.captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern} {rest : Option String} {kind : CollType}
      (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
      ∀ name ∈ patterns.flatMap Pattern.freeFvarNames ++ rest.toList, ∃ value, lookup final name = some value := by
    cases matched with
    | nil => intro name member; simp at member
    | rest captured =>
      intro name member
      simp only [List.flatMap_nil, Option.toList_some, List.nil_append, List.mem_singleton] at member
      subst member
      obtain ⟨_, _, value, _, _, _, found, _⟩ := GeneralScopedMatch.capture_interpretation captured
      exact ⟨value, found⟩
    | cons _ _ head tail =>
      intro name member
      simp only [List.flatMap_cons, List.append_assoc, List.mem_append] at member
      rcases member with inHead | inTail
      · obtain ⟨value, found⟩ := head.captures name inHead
        exact ⟨value, tail.extends name value found⟩
      · exact tail.captures name (by simpa only [List.mem_append] using inTail)
  termination_by sizeOf patterns
end

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
  simp only [checkSource, Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨⟨leftSide, sourceSide⟩, sourceRest⟩, descent⟩ := checked
  have parentCount := matched_nodes matching leftSide extension
  have childCount := instantiate_nodes rule spec ambient
    (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source child
    sourceSide instantiated
  have positive : ∀ name ∈ rule.left.freeFvarNames, 1 ≤ capturedWeight assignment name := by
    intro name member
    obtain ⟨value, found⟩ := matching.captures name member
    simp only [capturedWeight, extension name value found, Option.map_some, Option.getD_some]
    exact nodes_positive value.body
  have smaller := checkDescent_sound descent (capturedWeight assignment) positive
  omega

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
