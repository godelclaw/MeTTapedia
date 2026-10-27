import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureSteps
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembership

/-!
# Controls: set rules whose premises read their captures

The relation `small` holds of a hereditary set with at most one member, read off its canonical form, so it respects
canonical forms (`smallEnv_respects`). Two rules query it:

- `{ {x, y, ...inner} } ⇒ x if small(x)`, under the bounds `[1, 3]`: at `{1} = {{0}}` the inner set is presented with
  its member twice, `x` captures `0`, which is small, and the step reaches `0` (`query_inner_copy`); without the
  canonical forms the step is not seen (`query_without_forms`). At `{{2, 3}}` the members two sets down, `2` and `3`,
  are not small, and no step is taken (`query_refused`).
- `{x, ...rest} ⇒ x if every y in rest is small`, under the bounds `[2]`: at `{0, 2}` the rule takes `2`, leaving
  `{0}` (`forAll_takes_two`), and not `0`, which leaves `{2}` (`forAll_not_zero`); at `{2, 3}` it takes neither
  (`forAll_refused`).

Two rules carry a freshness premise, under the bounds `[1, 3]`. The name `a` is not captured, so it resolves to itself:

- `{ {x, y, ...inner} } ⇒ x if a # inner`: at `{1} = {{0}}` the inner set is presented with its member twice, `inner`
  captures the empty set, in which `a` does not occur, and the step reaches `0` (`fresh_inner_copy`); without the
  canonical forms the step is not seen (`fresh_without_forms`).
- `{ {x, y, ...inner} } ⇒ x if a # Pair(inner, a)`: `a` occurs in the instantiated subject, and no step is taken
  (`fresh_refused`).

A rule steps a member it captures, beside a rule that fires only at a copy: with atoms `A` and `B`,
`{A, y} ⇒ B` and `{x, ...rest} ⇒ {y, ...rest} if x ⇒ y`, with presentations listed to the state's height:

- at `{{A}}` the member `{A}` steps to `B` at its presentation `{A, A}`, and the set steps to `{B}`
  (`member_step_copy`); without the canonical forms the step is not seen (`member_step_without_forms`);
- `{{A}}` does not step to `{A}` (`member_step_only`), and `{{B}}` does not step (`member_step_refused`);
- the premise written as a scoped step with no local binders steps alike (`scoped_member_step_copy`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_idempotent)

/-- A hereditary set with at most one member, read off its canonical form. -/
def smallTerm (term : Pattern) : Bool :=
  match BagForms.sortBags term with
  | .collection .hashSet values none => decide (values.length ≤ 1)
  | _ => false

/-- The relation `small`. -/
def smallEnv : RelationEnv :=
  ⟨fun relation arguments => if relation = "small" then
    (match arguments with
      | [term] => if smallTerm term then [[term]] else []
      | _ => [])
    else []⟩

theorem smallTerm_canon (term : Pattern) : smallTerm (canon term) = smallTerm term := by
  unfold smallTerm
  rw [BagForms.sortBags_eq_canon, canon_idempotent]

/-- **`small` respects canonical forms.** -/
theorem smallEnv_respects : BagForms.RespectsCanon smallEnv := by
  intro relation arguments tuple member
  simp only [smallEnv] at member ⊢
  split at member
  · rename_i isSmall
    rw [if_pos isSmall]
    match arguments, member with
    | [term], member =>
      simp only at member ⊢
      split at member
      · rename_i holds
        rw [List.mem_singleton.mp member]
        simp only [List.map_cons, List.map_nil]
        rw [if_pos (by rw [smallTerm_canon]; exact holds)]
        exact List.mem_singleton_self _
      · exact absurd member List.not_mem_nil
  · exact absurd member List.not_mem_nil

/-! ## A query two sets down -/

/-- `{ {x, y, ...inner} } ⇒ x if small(x)`. -/
def smallPickRule : RewriteRule :=
  { name := "SmallPick", typeContext := [("x", .base "Set"), ("y", .base "Set"), ("inner", .collection .hashSet (.base "Set"))],
    premises := [.relationQuery "small" [.fvar "x"]],
    left := .collection .hashSet [.collection .hashSet [.fvar "x", .fvar "y"] (some "inner")] none,
    right := .fvar "x", bindings := none }

def smallPicking : LanguageDef :=
  { name := "SetReadings.SmallPicking", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [],
    rewrites := [smallPickRule] }

theorem smallPicking_captures : CaptureSetLanguage smallEnv smallPicking hfRule [1, 3] where
  hereditary := ⟨rfl, by decide, ⟨by simp [smallPicking], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    rw [show smallPicking.rewrites = [smallPickRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨.set (by decide) fun outer outerMember => ?_, by decide,
      premisesCanon_queries smallEnv_respects (by decide)⟩
    rw [List.mem_singleton] at outerMember
    subst outerMember
    refine .set (by decide) fun element elementMember => ?_
    rcases List.mem_cons.mp elementMember with rfl | elementMember
    · exact .var _ _
    · rw [List.mem_singleton] at elementMember
      subst elementMember
      exact .var _ _

abbrev smallPickingForms : CanonicalForms smallEnv smallPicking 2 := captureForms smallPicking_captures 2

/-- **At `{1} = {{0}}` the inner set is presented with its member twice**, `x` captures the small `0`, and the step
reaches `0`. -/
theorem query_inner_copy :
    ask smallEnv [] smallPicking 2 (.possibly .any (.is zero)) (set [one]) none 4 (some smallPickingForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the canonical forms the step is not seen.** -/
theorem query_without_forms :
    ask smallEnv [] smallPicking 2 (.possibly .any (.is zero)) (set [one]) none 4 = .unknown 4 := by
  decide +kernel

/-- **At `{{2, 3}}` neither member two sets down is small**, and no step is taken. -/
theorem query_refused :
    ask smallEnv [] smallPicking 2 (.possibly .any .top) (set [set [two, three]]) none 4 (some smallPickingForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-! ## A universally quantified premise over the rest -/

/-- `{x, ...rest} ⇒ x if every y in rest is small`. -/
def smallRestRule : RewriteRule :=
  { name := "SmallRest", typeContext := [("x", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.forAll "rest" "y" (.relationQuery "small" [.fvar "y"])],
    left := .collection .hashSet [.fvar "x"] (some "rest"), right := .fvar "x", bindings := none }

def smallRest : LanguageDef :=
  { name := "SetReadings.SmallRest", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [],
    rewrites := [smallRestRule] }

theorem smallRest_captures : CaptureSetLanguage smallEnv smallRest hfRule [2] where
  hereditary := ⟨rfl, by decide, ⟨by simp [smallRest], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    rw [show smallRest.rewrites = [smallRestRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨.set (by decide) fun element elementMember => ?_, by decide,
      premisesCanon_of_each fun premise premiseMember => ?_⟩
    · rw [List.mem_singleton] at elementMember
      subst elementMember
      exact .var _ _
    · rw [show smallRestRule.premises = [.forAll "rest" "y" (.relationQuery "small" [.fvar "y"])] from rfl,
        List.mem_singleton] at premiseMember
      subst premiseMember
      exact premiseCanon_forAll (premiseCanon_query smallEnv_respects (by decide))

abbrev smallRestForms : CanonicalForms smallEnv smallRest 2 := captureForms smallRest_captures 2

/-- **At `{0, 2}` the rule takes `2`**, leaving the small `0`. -/
theorem forAll_takes_two :
    ask smallEnv [] smallRest 2 (.possibly .any (.is two)) (set [zero, two]) none 4 (some smallRestForms) =
      .proved (.exploration 4) := by
  decide +kernel

/-- **And not `0`**, which would leave `2`, which is not small. -/
theorem forAll_not_zero :
    ask smallEnv [] smallRest 2 (.possibly .any (.is zero)) (set [zero, two]) none 4 (some smallRestForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **At `{2, 3}` it takes neither.** -/
theorem forAll_refused :
    ask smallEnv [] smallRest 2 (.possibly .any .top) (set [two, three]) none 4 (some smallRestForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-! ## A freshness premise -/

/-- The left side of the freshness rules: `{ {x, y, ...inner} }`. -/
def innerPairLeft : Pattern :=
  .collection .hashSet [.collection .hashSet [.fvar "x", .fvar "y"] (some "inner")] none

/-- `{ {x, y, ...inner} } ⇒ x if a # inner`. -/
def freshPickRule : RewriteRule :=
  { name := "FreshPick", typeContext := [("x", .base "Set"), ("y", .base "Set"), ("inner", .collection .hashSet (.base "Set"))],
    premises := [.freshness ⟨"a", .fvar "inner"⟩], left := innerPairLeft, right := .fvar "x", bindings := none }

/-- `{ {x, y, ...inner} } ⇒ x if a # Pair(inner, a)`. -/
def stalePickRule : RewriteRule :=
  { name := "StalePick", typeContext := [("x", .base "Set"), ("y", .base "Set"), ("inner", .collection .hashSet (.base "Set"))],
    premises := [.freshness ⟨"a", .apply "Pair" [.fvar "inner", .fvar "a"]⟩], left := innerPairLeft, right := .fvar "x",
    bindings := none }

def freshPicking : LanguageDef :=
  { name := "SetReadings.FreshPicking", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [],
    rewrites := [freshPickRule] }

def stalePicking : LanguageDef :=
  { name := "SetReadings.StalePicking", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [],
    rewrites := [stalePickRule] }

theorem innerPairLeft_nested {language : LanguageDef} : NestedElement language "Set" [1, 3] innerPairLeft := by
  refine .set (by decide) fun outer outerMember => ?_
  rw [List.mem_singleton] at outerMember
  subst outerMember
  refine .set (by decide) fun element elementMember => ?_
  rcases List.mem_cons.mp elementMember with rfl | elementMember
  · exact .var _ _
  · rw [List.mem_singleton] at elementMember
    subst elementMember
    exact .var _ _

theorem freshPicking_captures : CaptureSetLanguage RelationEnv.empty freshPicking hfRule [1, 3] where
  hereditary := ⟨rfl, by decide, ⟨by simp [freshPicking], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    rw [show freshPicking.rewrites = [freshPickRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨innerPairLeft_nested, by decide, premisesCanon_of_each fun premise premiseMember => ?_⟩
    rw [show freshPickRule.premises = [.freshness ⟨"a", .fvar "inner"⟩] from rfl, List.mem_singleton] at premiseMember
    subst premiseMember
    exact premiseCanon_freshness (by decide)

theorem stalePicking_captures : CaptureSetLanguage RelationEnv.empty stalePicking hfRule [1, 3] where
  hereditary := ⟨rfl, by decide, ⟨by simp [stalePicking], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    rw [show stalePicking.rewrites = [stalePickRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨innerPairLeft_nested, by decide, premisesCanon_of_each fun premise premiseMember => ?_⟩
    rw [show stalePickRule.premises = [.freshness ⟨"a", .apply "Pair" [.fvar "inner", .fvar "a"]⟩] from rfl,
      List.mem_singleton] at premiseMember
    subst premiseMember
    exact premiseCanon_freshness (by decide)

abbrev freshPickingForms : CanonicalForms RelationEnv.empty freshPicking 2 := captureForms freshPicking_captures 2
abbrev stalePickingForms : CanonicalForms RelationEnv.empty stalePicking 2 := captureForms stalePicking_captures 2

/-- **At `{1} = {{0}}` the inner set is presented with its member twice**, `a` is fresh in the empty `inner`, and the
step reaches `0`. -/
theorem fresh_inner_copy :
    ask RelationEnv.empty [] freshPicking 2 (.possibly .any (.is zero)) (set [one]) none 4 (some freshPickingForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the canonical forms the step is not seen.** -/
theorem fresh_without_forms :
    ask RelationEnv.empty [] freshPicking 2 (.possibly .any (.is zero)) (set [one]) none 4 = .unknown 4 := by
  decide +kernel

/-- **`a` occurs in the instantiated subject**, and no step is taken. -/
theorem fresh_refused :
    ask RelationEnv.empty [] stalePicking 2 (.possibly .any .top) (set [one]) none 4 (some stalePickingForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-! ## A premise that steps a member -/

/-- An atom of sets. -/
def setAtom (label : String) : GrammarRule :=
  { label := label, category := "Set", params := [], syntaxPattern := [.terminal label] }

/-- `{A, y} ⇒ B`. -/
def doubleRule : RewriteRule :=
  { name := "Double", typeContext := [("y", .base "Set")], premises := [],
    left := .collection .hashSet [token "A", .fvar "y"] none, right := token "B", bindings := none }

/-- `{x, ...rest} ⇒ {y, ...rest} if x ⇒ y`. -/
def memberStepRule : RewriteRule :=
  { name := "MemberStep",
    typeContext := [("x", .base "Set"), ("y", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.congruence (.fvar "x") (.fvar "y")],
    left := .collection .hashSet [.fvar "x"] (some "rest"),
    right := .collection .hashSet [.fvar "y"] (some "rest"), bindings := none }

def memberSteps : LanguageDef :=
  { name := "SetReadings.MemberSteps", types := [⟨"Set", .ast⟩], terms := [hfRule, setAtom "A", setAtom "B"],
    equations := [], rewrites := [doubleRule, memberStepRule] }

theorem memberSteps_language : StepSetLanguage RelationEnv.empty memberSteps hfRule 2 1 where
  hereditary := ⟨rfl, by decide, ⟨by simp [memberSteps], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show memberSteps.rewrites = [doubleRule, memberStepRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide,
        Or.inl (premisesCanon_queries BagForms.respectsCanon_empty (by decide))⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at elementMember
      rcases elementMember with rfl | rfl
      · exact .closed _ (.atom ⟨setAtom "A", by simp [memberSteps], rfl, rfl, rfl⟩) rfl
      · exact .var _ _
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide,
        Or.inr ⟨_, "x", "y", ⟨rfl, rfl, by decide, by decide, by decide⟩⟩⟩
      rw [List.mem_singleton] at elementMember
      subst elementMember
      exact .var _ _

abbrev memberStepForms : CanonicalForms RelationEnv.empty memberSteps 2 := stepForms memberSteps_language 2

/-- **At `{{A}}` the member `{A}` steps to `B` at its presentation `{A, A}`**, and the set steps to `{B}`. -/
theorem member_step_copy :
    ask RelationEnv.empty [] memberSteps 2 (.possibly .any (.is (set [token "B"]))) (set [set [token "A"]]) none 4
      (some memberStepForms) = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the canonical forms the step is not seen.** -/
theorem member_step_without_forms :
    ask RelationEnv.empty [] memberSteps 2 (.possibly .any (.is (set [token "B"]))) (set [set [token "A"]]) none 4 =
      .unknown 4 := by
  decide +kernel

/-- **`{{A}}` does not step to `{A}`.** -/
theorem member_step_only :
    ask RelationEnv.empty [] memberSteps 2 (.possibly .any (.is (set [token "A"]))) (set [set [token "A"]]) none 4
      (some memberStepForms) = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **`{{B}}` does not step**: its member is an atom without steps. -/
theorem member_step_refused :
    ask RelationEnv.empty [] memberSteps 2 (.possibly .any .top) (set [set [token "B"]]) none 4
      (some memberStepForms) = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- `{x, ...rest} ⇒ {y, ...rest} if x ⇒ y`, its premise a scoped step with no local binders. -/
def scopedMemberStepRule : RewriteRule :=
  { memberStepRule with
    premises := [.scopedStep ⟨[], .base "Set", .fvar "x", .fvar "y"⟩] }

def scopedMemberSteps : LanguageDef := { memberSteps with rewrites := [doubleRule, scopedMemberStepRule] }

theorem scopedMemberSteps_language : StepSetLanguage RelationEnv.empty scopedMemberSteps hfRule 2 1 where
  hereditary := ⟨rfl, by decide, ⟨by simp [scopedMemberSteps, memberSteps], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show scopedMemberSteps.rewrites = [doubleRule, scopedMemberStepRule] from rfl, List.mem_cons,
      List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide,
        Or.inl (premisesCanon_queries BagForms.respectsCanon_empty (by decide))⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at elementMember
      rcases elementMember with rfl | rfl
      · exact .closed _ (.atom ⟨setAtom "A", by simp [scopedMemberSteps, memberSteps], rfl, rfl, rfl⟩) rfl
      · exact .var _ _
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide,
        Or.inr ⟨_, "x", "y", ⟨rfl, rfl, by decide, by decide, by decide⟩⟩⟩
      rw [List.mem_singleton] at elementMember
      subst elementMember
      exact .var _ _

/-- **The scoped spelling steps alike.** -/
theorem scoped_member_step_copy :
    ask RelationEnv.empty [] scopedMemberSteps 2 (.possibly .any (.is (set [token "B"]))) (set [set [token "A"]]) none 4
      (some (stepForms scopedMemberSteps_language 2)) = .proved (.canonicalRegion 4) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
