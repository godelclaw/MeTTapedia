import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TwoLevelSetRules
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembership

/-!
# Controls: a set rule that looks inside a member

The rule `{ {x, y, ...inner}, ...rest } ⇒ x` steps from a set to a member of a member that has two members. Under the
set laws a member with one member may be presented with it twice, so the rule fires at `{1} = {{0}}`, although the
canonical form shows no member with two members. Exploration alone cannot find that step; the two-level canonical
forms list the presentation, and the front door proves it over the canonical region. At `{2} = {{0, 1}}` the step is
found by exploration, and at `{0}` the rule finds no member with members and every step is refuted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- `{ {x, y, ...inner}, ...rest } ⇒ x`: a set steps to a member of a member that has two members. -/
def pickRule : RewriteRule :=
  { name := "Pick", typeContext := [("x", .base "Set"), ("y", .base "Set"), ("inner", .collection .hashSet (.base "Set")),
      ("rest", .collection .hashSet (.base "Set"))],
    premises := [], left := .collection .hashSet [.collection .hashSet [.fvar "x", .fvar "y"] (some "inner")] (some "rest"),
    right := .fvar "x", bindings := none }

def picking : LanguageDef :=
  { name := "SetReadings.Picking", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [], rewrites := [pickRule] }

theorem picking_hereditary : HereditaryLanguage picking hfRule :=
  ⟨rfl, by decide, ⟨by simp [picking], ⟨"members", rfl⟩, rfl⟩⟩

/-- **The picking language is a two-level set language.** -/
theorem picking_twoLevel : TwoLevelSetLanguage picking hfRule 2 2 where
  hereditary := picking_hereditary
  rules := by
    intro rule member
    rw [show picking.rewrites = [pickRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨[.collection .hashSet [.fvar "x", .fvar "y"] (some "inner")], some "rest", rfl, by simp,
      fun pattern member => ?_, by decide, rfl⟩
    rw [List.mem_singleton] at member
    subst member
    refine Or.inr (Or.inr ⟨[.fvar "x", .fvar "y"], some "inner", rfl, by simp, fun element member => ?_⟩)
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨"x", rfl, by simp⟩
    · rw [List.mem_singleton] at member
      subst member
      exact Or.inl ⟨"y", rfl, by simp⟩

abbrev pickingForms : CanonicalForms RelationEnv.empty picking 2 := twoLevelForms picking_twoLevel 2

/-- **At `{1} = {{0}}` the rule fires at a presentation with an inner copy**, and reaches `0`. -/
theorem pick_inner_copy_answer :
    ask RelationEnv.empty [] picking 2 (.possibly .any (.is zero)) (set [one]) none 4 (some pickingForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the canonical forms the inner copy is not seen**, and the answer is unknown. -/
theorem pick_inner_copy_without_forms :
    ask RelationEnv.empty [] picking 2 (.possibly .any (.is zero)) (set [one]) none 4 = .unknown 4 := by
  decide +kernel

/-- **At `{2} = {{0, 1}}` the canonical form shows a member with two members**, and exploration reaches `1`. -/
theorem pick_two_answer :
    ask RelationEnv.empty [] picking 2 (.possibly .any (.is one)) (set [two]) none 4 (some pickingForms) =
      .proved (.exploration 4) := by
  decide +kernel

/-- **At `{0}` no member has members, and no step is taken.** -/
theorem pick_empty_answer :
    ask RelationEnv.empty [] picking 2 (.possibly .any .top) (set [zero]) none 4 (some pickingForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
