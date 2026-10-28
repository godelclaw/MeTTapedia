import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModulo
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls

/-!
# Controls: premises of every shape, modulo the set laws at every boundary

Hereditary set languages over atoms `A`, `B`, `C`, with the rule `{y} ⇒ C`, which fires only where a set is written
with one member. Each is asked at the front door with canonical forms of the reading modulo the set laws, evaluated by
the kernel, and each verdict holds in the either structure (`twice_verdicts`, …).

- **A step premise of a compound** (`twice`): `{x} ⇒ B if {x, x} ⇒ z`. The child `{A, A}` is a presentation of `{A}`,
  where `{y} ⇒ C` fires, so `{A}` reaches `B` (`twice_reaches`) and not `A` (`twice_not_A`).
- **A step premise of a rest** (`drain`): `{x, ...rest} ⇒ x if rest ⇒ w`. Written `{A, A}`, the set `{A}` leaves the
  rest `{A}`, which steps, so `{A}` reaches `A` (`drain_reaches`) and not `B` (`drain_not_B`). The premise written as a
  scoped step steps alike (`scopedDrain_reaches`).

A child of the class of its term (`{A, A}` of `{A}`; the rest `{A}` of `{A}` written `{A, A}`) lets derivations nest
without bound, so these are listed by one table of the region reached from the asked term, certified once
(`tabledFormsAt`), keeping the rule labels.

- **A query, a freshness condition and a step in one rule** (`guarded`):
  `{x, ...rest} ⇒ {z, ...rest} if small(x), a # rest, x ⇒ z`. At `{{A}}` the member is small and steps, so `{{A}}`
  reaches `{C}` (`guarded_reaches`); at `{{A, B}}` the member is not small, and `{C}` is not reached
  (`guarded_refused`).
- **A query with an output** (`relabelling`): `{x, ...rest} ⇒ {y, ...rest} if next(x, y)`, where `next` relabels `A`
  to `B` and `B` to `C` and its answer binds `y`. `{A}` reaches `{C}` (`relabelling_reaches`), and `{A, B}`, written
  `{A, A}` with a copy kept in the rest (`relabelling_keeps_copy`); `{C}` does not step (`relabelling_C_stuck`), and
  `{B}` never reaches `{A}` (`relabelling_B_not_A`).
- **A quantified premise whose body steps** (`allStep`), with the rule labels kept:
  `{x, ...rest} ⇒ x if every y in rest steps`. At `{A, {B}}` the rest `{{B}}` steps, so `A` is reached
  (`allStep_reaches`); `{B}` is not (`allStep_not_B`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.ModuloControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_idempotent)

def atoms : List GrammarRule := [hfRule, setAtom "A", setAtom "B", setAtom "C"]

/-- `{y} ⇒ C`. -/
def singleRule : RewriteRule :=
  { name := "Single", typeContext := [("y", .base "Set")], premises := [],
    left := .collection .hashSet [.fvar "y"] none, right := token "C", bindings := none }

theorem singleRule_modulo {language : LanguageDef} {deep : Bool} :
    ModuloRule language "Set" [2] deep singleRule :=
  ⟨.set (by decide) fun element member => by
      rw [List.mem_singleton] at member
      subst member
      exact .var _ _,
    by decide, by decide, fun _ inside => by simp [singleRule] at inside⟩

/-- The left side `{x, ...rest}` of the rules below, admitted. -/
theorem pickLeft {language : LanguageDef} :
    NestedElement language "Set" [2] (.collection .hashSet [.fvar "x"] (some "rest")) :=
  .set (by decide) fun element member => by
    rw [List.mem_singleton] at member
    subst member
    exact .var _ _

/-! ## A step premise of a compound -/

/-- `{x} ⇒ B if {x, x} ⇒ z`. -/
def twiceRule : RewriteRule :=
  { name := "Twice",
    typeContext := [("x", .base "Set"), ("z", .base "Set")],
    premises := [.congruence (.collection .hashSet [.fvar "x", .fvar "x"] none) (.fvar "z")],
    left := .collection .hashSet [.fvar "x"] none, right := token "B", bindings := none }

def twice : LanguageDef :=
  { name := "ModuloControls.Twice", types := [⟨"Set", .ast⟩], terms := atoms, equations := [],
    rewrites := [singleRule, twiceRule] }

theorem twice_modulo : ModuloSetLanguage RelationEnv.empty twice hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [twice, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show twice.rewrites = [singleRule, twiceRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · exact singleRule_modulo
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide, by decide, fun premise inside => ?_⟩
      · rw [List.mem_singleton] at elementMember
        subst elementMember
        exact .var _ _
      · rw [show twiceRule.premises = [.congruence (.collection .hashSet [.fvar "x", .fvar "x"] none) (.fvar "z")]
          from rfl, List.mem_singleton] at inside
        subst inside
        exact ⟨by decide, .var _ _, by decide⟩
  answers := answersAlike_empty

abbrev twiceForms : CanonicalForms RelationEnv.empty twice 1 := tabledFormsAt twice_modulo 1 (set [token "A"]) 6

/-- **`{A}` reaches `B`**: the child `{A, A}` is a presentation of `{A}`, where `{y} ⇒ C` fires. -/
theorem twice_reaches :
    ask RelationEnv.empty [] twice 1 (reaches (token "B")) (set [token "A"]) none 4 (some twiceForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

theorem twice_not_A :
    ask RelationEnv.empty [] twice 1 (reaches (token "A")) (set [token "A"]) none 4 (some twiceForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem twice_verdicts :
    (eitherStructure RelationEnv.empty twice).sat Env.closed (reaches (token "B")) (set [token "A"]) ∧
      ¬ (eitherStructure RelationEnv.empty twice).sat Env.closed (reaches (token "A")) (set [token "A"]) :=
  ⟨tabledFormsAt_structure twice_modulo 1 (set [token "A"]) 6 ▸ ask_proved twice_reaches,
    tabledFormsAt_structure twice_modulo 1 (set [token "A"]) 6 ▸ ask_refuted twice_not_A⟩

/-! ## A step premise of a rest -/

/-- `{x, ...rest} ⇒ x if rest ⇒ w`. -/
def drainRule : RewriteRule :=
  { name := "Drain",
    typeContext := [("x", .base "Set"), ("w", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.congruence (.fvar "rest") (.fvar "w")],
    left := .collection .hashSet [.fvar "x"] (some "rest"), right := .fvar "x", bindings := none }

def drain : LanguageDef :=
  { name := "ModuloControls.Drain", types := [⟨"Set", .ast⟩], terms := atoms, equations := [],
    rewrites := [singleRule, drainRule] }

theorem drain_modulo : ModuloSetLanguage RelationEnv.empty drain hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [drain, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show drain.rewrites = [singleRule, drainRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · exact singleRule_modulo
    · refine ⟨pickLeft, by decide, by decide, fun premise inside => ?_⟩
      rw [show drainRule.premises = [.congruence (.fvar "rest") (.fvar "w")] from rfl, List.mem_singleton] at inside
      subst inside
      exact ⟨by decide, .var _ _, by decide⟩
  answers := answersAlike_empty

abbrev drainForms : CanonicalForms RelationEnv.empty drain 1 := tabledFormsAt drain_modulo 1 (set [token "A"]) 6

/-- **`{A}` reaches `A`**: written `{A, A}`, it leaves the rest `{A}`, which steps. -/
theorem drain_reaches :
    ask RelationEnv.empty [] drain 1 (reaches (token "A")) (set [token "A"]) none 4 (some drainForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

theorem drain_not_B :
    ask RelationEnv.empty [] drain 1 (reaches (token "B")) (set [token "A"]) none 4 (some drainForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem drain_verdicts :
    (eitherStructure RelationEnv.empty drain).sat Env.closed (reaches (token "A")) (set [token "A"]) ∧
      ¬ (eitherStructure RelationEnv.empty drain).sat Env.closed (reaches (token "B")) (set [token "A"]) :=
  ⟨tabledFormsAt_structure drain_modulo 1 (set [token "A"]) 6 ▸ ask_proved drain_reaches,
    tabledFormsAt_structure drain_modulo 1 (set [token "A"]) 6 ▸ ask_refuted drain_not_B⟩

/-- `{x, ...rest} ⇒ x if rest ⇒ w`, the premise written as a scoped step with no local binders. -/
def scopedDrainRule : RewriteRule :=
  { drainRule with premises := [.scopedStep ⟨[], .base "Set", .fvar "rest", .fvar "w"⟩] }

def scopedDrain : LanguageDef :=
  { drain with name := "ModuloControls.ScopedDrain", rewrites := [singleRule, scopedDrainRule] }

theorem scopedDrain_modulo : ModuloSetLanguage RelationEnv.empty scopedDrain hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [scopedDrain, drain, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show scopedDrain.rewrites = [singleRule, scopedDrainRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · exact singleRule_modulo
    · refine ⟨pickLeft, by decide, by decide, fun premise inside => ?_⟩
      rw [show scopedDrainRule.premises = [.scopedStep ⟨[], .base "Set", .fvar "rest", .fvar "w"⟩] from rfl,
        List.mem_singleton] at inside
      subst inside
      exact ⟨by decide, .var _ _, by decide⟩
  answers := answersAlike_empty

/-- **The scoped spelling steps alike.** -/
theorem scopedDrain_reaches :
    ask RelationEnv.empty [] scopedDrain 1 (reaches (token "A")) (set [token "A"]) none 4
      (some (tabledFormsAt scopedDrain_modulo 1 (set [token "A"]) 6)) = .proved (.canonicalRegion 4) := by
  decide +kernel

/-! ## A query, a freshness condition and a step in one rule -/

/-- **`small` answers alike requests alike**: it reads the canonical form. -/
theorem answersAlike_small {language : LanguageDef} : AnswersAlike smallEnv language := by
  intro relation request request' objects same tuple member
  rcases List.mem_append.mp member with builtin | provided
  · obtain ⟨tupleObjects, tuple', member', sameTuple⟩ :=
      answersAlike_empty (language := language) relation request request' objects same tuple
        (by simpa [RelationEnv.empty] using builtin)
    exact ⟨tupleObjects, tuple', List.mem_append_left _ (by simpa [RelationEnv.empty] using member'), sameTuple⟩
  · simp only [smallEnv] at provided
    split at provided
    · rename_i isSmall
      match request, same, provided with
      | [term], .cons sameTerm .nil, provided =>
        simp only at provided
        split at provided
        · rename_i holds
          rw [List.mem_singleton.mp provided]
          rename_i term'
          refine ⟨fun value inside => ?_, [term'], List.mem_append_right _ ?_, .cons sameTerm .nil⟩
          · rw [List.mem_singleton.mp inside]
            exact objects term List.mem_cons_self
          · have smallSame : smallTerm term' = smallTerm term := by
              rw [← smallTerm_canon term', ← smallTerm_canon term]
              exact congrArg smallTerm sameTerm.symm
            simp only [smallEnv, if_pos isSmall, smallSame, holds, if_true, List.mem_singleton]
        · exact absurd provided List.not_mem_nil
    · exact absurd provided List.not_mem_nil

/-- `{x, ...rest} ⇒ {z, ...rest} if small(x), a # rest, x ⇒ z`. -/
def guardedRule : RewriteRule :=
  { name := "Guarded",
    typeContext := [("x", .base "Set"), ("z", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.relationQuery "small" [.fvar "x"], .freshness ⟨"a", .fvar "rest"⟩,
      .congruence (.fvar "x") (.fvar "z")],
    left := .collection .hashSet [.fvar "x"] (some "rest"),
    right := .collection .hashSet [.fvar "z"] (some "rest"), bindings := none }

def guarded : LanguageDef :=
  { name := "ModuloControls.Guarded", types := [⟨"Set", .ast⟩], terms := atoms, equations := [],
    rewrites := [singleRule, guardedRule] }

theorem guarded_modulo : ModuloSetLanguage smallEnv guarded hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [guarded, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show guarded.rewrites = [singleRule, guardedRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · exact singleRule_modulo
    · refine ⟨pickLeft, by decide, by decide, fun premise inside => ?_⟩
      simp only [guardedRule, List.mem_cons, List.mem_nil_iff, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact (by decide : [Pattern.fvar "x"].all BagForms.isMetavariable = true)
      · exact (by decide : substFree (Pattern.fvar "rest") = true)
      · exact ⟨by decide, .var _ _, by decide⟩
  answers := answersAlike_small

abbrev guardedForms : CanonicalForms smallEnv guarded 2 := moduloForms guarded_modulo 2

/-- **`{{A}}` reaches `{C}`**: its member is small, the name is fresh, and the member steps. -/
theorem guarded_reaches :
    ask smallEnv [] guarded 2 (reaches (set [token "C"])) (set [set [token "A"]]) none 4 (some guardedForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`{{A, B}}` does not reach `{C}`**: its member is not small. -/
theorem guarded_refused :
    ask smallEnv [] guarded 2 (reaches (set [token "C"])) (set [set [token "A", token "B"]]) none 4
      (some guardedForms) = .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem guarded_verdicts :
    (eitherStructure smallEnv guarded).sat Env.closed (reaches (set [token "C"])) (set [set [token "A"]]) ∧
      ¬ (eitherStructure smallEnv guarded).sat Env.closed (reaches (set [token "C"]))
        (set [set [token "A", token "B"]]) :=
  ⟨moduloForms_structure guarded_modulo 2 ▸ ask_proved guarded_reaches,
    moduloForms_structure guarded_modulo 2 ▸ ask_refuted guarded_refused⟩

/-! ## A query with an output -/

/-- The atom an atom is relabelled to. -/
def nextAtom : Pattern → Option Pattern
  | .apply "A" [] => some (token "B")
  | .apply "B" [] => some (token "C")
  | _ => none

/-- `next(x, y)` answers the atom `x` is relabelled to, read off the canonical form of `x`. -/
def nextEnv : RelationEnv := ⟨fun relation arguments =>
  match relation, arguments with
  | "next", [atom, _] =>
    match nextAtom (BagForms.sortBags atom) with
    | some next => [[BagForms.sortBags atom, next]]
    | none => []
  | _, _ => []⟩

theorem nextAtom_object {atom next : Pattern} (found : nextAtom atom = some next) : IsObject next := by
  unfold nextAtom at found
  split at found <;> cases found <;> decide

/-- **`next` answers alike requests alike**: it reads the canonical form. -/
theorem answersAlike_next {language : LanguageDef} : AnswersAlike nextEnv language := by
  intro relation request request' objects same tuple member
  rcases List.mem_append.mp member with builtin | provided
  · obtain ⟨tupleObjects, tuple', member', sameTuple⟩ :=
      answersAlike_empty (language := language) relation request request' objects same tuple
        (by simpa [RelationEnv.empty] using builtin)
    exact ⟨tupleObjects, tuple', List.mem_append_left _ (by simpa [RelationEnv.empty] using member'), sameTuple⟩
  · simp only [nextEnv] at provided
    split at provided
    · rename_i atom output
      cases same with
      | cons sameAtom rest =>
        cases rest with
        | cons sameOutput tail =>
          cases tail
          rename_i atom' output'
          have canonSame : BagForms.sortBags atom' = BagForms.sortBags atom := by
            rw [BagForms.sortBags_eq, BagForms.sortBags_eq]
            exact sameAtom.symm
          split at provided
          · rename_i next found
            rw [List.mem_singleton.mp provided]
            refine ⟨fun value inside => ?_, [BagForms.sortBags atom, next], List.mem_append_right _ ?_,
              List.forall₂_same.mpr fun _ _ => rfl⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · rw [BagForms.sortBags_eq]
                exact object_canon_iff.mpr (objects atom List.mem_cons_self)
              · exact nextAtom_object found
            · simp [nextEnv, canonSame, found]
          · exact absurd provided List.not_mem_nil
    · exact absurd provided List.not_mem_nil

/-- `{x, ...rest} ⇒ {y, ...rest} if next(x, y)`: the answer binds the output `y`. -/
def relabelRule : RewriteRule :=
  { name := "Relabel",
    typeContext := [("x", .base "Set"), ("y", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.relationQuery "next" [.fvar "x", .fvar "y"]],
    left := .collection .hashSet [.fvar "x"] (some "rest"),
    right := .collection .hashSet [.fvar "y"] (some "rest"), bindings := none }

def relabelling : LanguageDef :=
  { name := "ModuloControls.Relabelling", types := [⟨"Set", .ast⟩], terms := atoms, equations := [],
    rewrites := [relabelRule] }

theorem relabelling_modulo : ModuloSetLanguage nextEnv relabelling hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [relabelling, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show relabelling.rewrites = [relabelRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨pickLeft, by decide, by decide, fun premise inside => ?_⟩
    rw [show relabelRule.premises = [.relationQuery "next" [.fvar "x", .fvar "y"]] from rfl,
      List.mem_singleton] at inside
    subst inside
    exact (by decide : [Pattern.fvar "x", Pattern.fvar "y"].all BagForms.isMetavariable = true)
  answers := answersAlike_next

abbrev relabellingForms : CanonicalForms nextEnv relabelling 2 := moduloForms relabelling_modulo 2

/-- **`{A}` reaches `{C}`**: each answer binds the output. -/
theorem relabelling_reaches :
    ask nextEnv [] relabelling 2 (reaches (set [token "C"])) (set [token "A"]) none 4 (some relabellingForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`{A}` reaches `{A, B}`**: written `{A, A}`, it keeps a copy of `A` in the rest. -/
theorem relabelling_keeps_copy :
    ask nextEnv [] relabelling 2 (reaches (set [token "A", token "B"])) (set [token "A"]) none 4
      (some relabellingForms) = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`{C}` does not step**: `next` answers nothing for `C`. -/
theorem relabelling_C_stuck :
    ask nextEnv [] relabelling 2 (.possibly .any .top) (set [token "C"]) none 4 (some relabellingForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem relabelling_B_not_A :
    ask nextEnv [] relabelling 2 (reaches (set [token "A"])) (set [token "B"]) none 4 (some relabellingForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem relabelling_verdicts :
    (eitherStructure nextEnv relabelling).sat Env.closed (reaches (set [token "C"])) (set [token "A"]) ∧
      (eitherStructure nextEnv relabelling).sat Env.closed (reaches (set [token "A", token "B"])) (set [token "A"]) ∧
      ¬ (eitherStructure nextEnv relabelling).sat Env.closed (.possibly .any .top) (set [token "C"]) ∧
      ¬ (eitherStructure nextEnv relabelling).sat Env.closed (reaches (set [token "A"])) (set [token "B"]) :=
  ⟨moduloForms_structure relabelling_modulo 2 ▸ ask_proved relabelling_reaches,
    moduloForms_structure relabelling_modulo 2 ▸ ask_proved relabelling_keeps_copy,
    moduloForms_structure relabelling_modulo 2 ▸ ask_refuted relabelling_C_stuck,
    moduloForms_structure relabelling_modulo 2 ▸ ask_refuted relabelling_B_not_A⟩

/-! ## A quantified premise whose body steps -/

/-- `{x, ...rest} ⇒ x if every y in rest steps to some w`. -/
def allStepRule : RewriteRule :=
  { name := "AllStep",
    typeContext := [("x", .base "Set"), ("w", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [.forAll "rest" "y" (.congruence (.fvar "y") (.fvar "w"))],
    left := .collection .hashSet [.fvar "x"] (some "rest"), right := .fvar "x", bindings := none }

def allStep : LanguageDef :=
  { name := "ModuloControls.AllStep", types := [⟨"Set", .ast⟩], terms := atoms, equations := [],
    rewrites := [singleRule, allStepRule] }

theorem allStep_modulo : ModuloSetLanguage RelationEnv.empty allStep hfRule [2] false where
  hereditary := ⟨rfl, by decide, ⟨by simp [allStep, atoms], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show allStep.rewrites = [singleRule, allStepRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · exact singleRule_modulo
    · refine ⟨pickLeft, by decide, by decide, fun premise inside => ?_⟩
      rw [show allStepRule.premises = [.forAll "rest" "y" (.congruence (.fvar "y") (.fvar "w"))] from rfl,
        List.mem_singleton] at inside
      subst inside
      exact ⟨by decide, ⟨by decide, .var _ _, by decide⟩, fun deep => by cases deep⟩
  answers := answersAlike_empty

abbrev allStepForms : CanonicalForms RelationEnv.empty allStep 2 := moduloForms allStep_modulo 2

/-- **`{A, {B}}` reaches `A`**: every member of the rest `{{B}}` steps. -/
theorem allStep_reaches :
    ask RelationEnv.empty [] allStep 2 (reaches (token "A")) (set [token "A", set [token "B"]]) none 4
      (some allStepForms) = .proved (.canonicalRegion 4) := by
  decide +kernel

theorem allStep_not_B :
    ask RelationEnv.empty [] allStep 2 (reaches (set [token "B"])) (set [token "A", set [token "B"]]) none 4
      (some allStepForms) = .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem allStep_verdicts :
    (eitherStructure RelationEnv.empty allStep).sat Env.closed (reaches (token "A"))
        (set [token "A", set [token "B"]]) ∧
      ¬ (eitherStructure RelationEnv.empty allStep).sat Env.closed (reaches (set [token "B"]))
        (set [token "A", set [token "B"]]) :=
  ⟨moduloForms_structure allStep_modulo 2 ▸ ask_proved allStep_reaches,
    moduloForms_structure allStep_modulo 2 ▸ ask_refuted allStep_not_B⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.ModuloControls
