import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NestedSetRules
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembership

/-!
# Controls: a set rule three sets deep

The rule `{ { {x, y, ...inner} } } ⇒ x` looks three sets deep: a set with one member, which has one member, which has
two members. Its bounds by depth are `[1, 1, 3]`. Under the set laws a set with one member may be presented with it
twice, so at `{{1}} = {{{0}}}` the rule fires two sets down, where the canonical form shows no set with two members:

- `{{1}}` steps to `0` (`deep_inner_copy`); without the canonical forms the step is not seen (`deep_without_forms`);
- `{{2}}` steps to `1`, found at the canonical form (`deep_two`);
- `{1}` has no step: two sets down is `0`, which has no members (`shallow_stuck`);
- `{{1}, 0}` has no step: the outer pattern has no rest, so the set must have exactly one member (`two_members_stuck`).

The same rule guarded by the relation `enabled`, which takes no argument: where the relation environment holds it,
`{{1}}` steps to `0` (`guarded_fires`); where it does not, `{{1}}` has no step (`guarded_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- `{ { {x, y, ...inner} } } ⇒ x`: a set steps to a member three sets down. -/
def deepRule : RewriteRule :=
  { name := "Deep", typeContext := [("x", .base "Set"), ("y", .base "Set"), ("inner", .collection .hashSet (.base "Set"))],
    premises := [],
    left := .collection .hashSet [.collection .hashSet [.collection .hashSet [.fvar "x", .fvar "y"] (some "inner")] none]
      none,
    right := .fvar "x", bindings := none }

def deepSets : LanguageDef :=
  { name := "SetReadings.Deep", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [], rewrites := [deepRule] }

theorem deep_hereditary : HereditaryLanguage deepSets hfRule :=
  ⟨rfl, by decide, ⟨by simp [deepSets], ⟨"members", rfl⟩, rfl⟩⟩

/-- **The deep rule's left side is a nested element pattern under the bounds `[1, 1, 3]`**, in any language. -/
theorem deepLeft_nested (language : LanguageDef) : NestedElement language hfRule.category [1, 1, 3] deepRule.left := by
  refine .set (by decide) fun outer outerMember => ?_
  rw [List.mem_singleton] at outerMember
  subst outerMember
  refine .set (by decide) fun middle middleMember => ?_
  rw [List.mem_singleton] at middleMember
  subst middleMember
  refine .set (by decide) fun element elementMember => ?_
  rcases List.mem_cons.mp elementMember with rfl | elementMember
  · exact .var _ _
  · rw [List.mem_singleton] at elementMember
    subst elementMember
    exact .var _ _

/-- **The language `deepSets` is a nested set language under the bounds `[1, 1, 3]`.** -/
theorem deep_nested : NestedSetLanguage deepSets hfRule [1, 1, 3] where
  hereditary := deep_hereditary
  rules := by
    intro rule member
    rw [show deepSets.rewrites = [deepRule] from rfl, List.mem_singleton] at member
    subst member
    exact ⟨deepLeft_nested deepSets, by decide, rfl⟩

abbrev deepForms : CanonicalForms RelationEnv.empty deepSets 2 := nestedForms deep_nested 2

/-- **At `{{1}} = {{{0}}}` the rule fires two sets down at a presentation with a copy**, and reaches `0`. -/
theorem deep_inner_copy :
    ask RelationEnv.empty [] deepSets 2 (.possibly .any (.is zero)) (set [set [one]]) none 4 (some deepForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the canonical forms the copy is not seen**, and the answer is unknown. -/
theorem deep_without_forms :
    ask RelationEnv.empty [] deepSets 2 (.possibly .any (.is zero)) (set [set [one]]) none 4 = .unknown 4 := by
  decide +kernel

/-- **At `{{2}} = {{{0, 1}}}` the canonical form shows two members two sets down**, and exploration reaches `1`. -/
theorem deep_two :
    ask RelationEnv.empty [] deepSets 2 (.possibly .any (.is one)) (set [set [two]]) none 4 (some deepForms) =
      .proved (.exploration 4) := by
  decide +kernel

/-- **At `{1}` there is nothing two sets down to match**, and no step is taken. -/
theorem shallow_stuck :
    ask RelationEnv.empty [] deepSets 2 (.possibly .any .top) (set [one]) none 4 (some deepForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **At `{{1}, 0}` the outer set has two members**, and the outer pattern, with no rest, takes exactly one. -/
theorem two_members_stuck :
    ask RelationEnv.empty [] deepSets 2 (.possibly .any .top) (set [set [one], zero]) none 4 (some deepForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-! ## A guarded rule -/

/-- The deep rule, guarded by `enabled`. -/
def guardedRule : RewriteRule := { deepRule with name := "GuardedDeep", premises := [.relationQuery "enabled" []] }

def guardedDeep : LanguageDef := { deepSets with name := "SetReadings.GuardedDeep", rewrites := [guardedRule] }

/-- A relation environment that holds `enabled`. -/
def enabling : RelationEnv := ⟨fun relation _ => if relation = "enabled" then [[]] else []⟩

theorem guardedDeep_nested (relEnv : RelationEnv) : NestedSetLanguageWith relEnv guardedDeep hfRule [1, 1, 3] where
  hereditary := ⟨rfl, by decide, ⟨by simp [guardedDeep, deepSets], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    rw [show guardedDeep.rewrites = [guardedRule] from rfl, List.mem_singleton] at member
    subst member
    exact ⟨deepLeft_nested guardedDeep, by decide, premisesTransfer_guards (by decide)⟩

/-- **Where `enabled` holds, the guarded rule fires at `{{1}}`**, at a presentation with a copy. -/
theorem guarded_fires :
    ask enabling [] guardedDeep 2 (.possibly .any (.is zero)) (set [set [one]]) none 4
      (some (nestedFormsWith (guardedDeep_nested enabling) 2)) = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Where it does not, `{{1}}` has no step.** -/
theorem guarded_refused :
    ask RelationEnv.empty [] guardedDeep 2 (.possibly .any .top) (set [set [one]]) none 4
      (some (nestedFormsWith (guardedDeep_nested RelationEnv.empty) 2)) = .refuted (.canonicalRegion 4) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
