import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModulo
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModuloControls

/-!
# Controls: set languages under three declared readings

Each language is declared three ways and asked through the front door of a declared language (`askDeclared`),
evaluated by the kernel.

**At the top of a step.** The pool language (`SetReadings.pool`, the rule `{A, ...rest} ⇒ {B, ...rest}`), asked at
`{A}`:

| declared reading | some run reaches `{B}` | every run reaches `{B}` |
|---|---|---|
| consume | yes | yes |
| keep | no | no |
| either | yes | — |

The either reading's universal verdict is not settled by the front door's search within the budget; it is false
(`SetReadings.either_verdicts`), by a run that keeps copying `A`.

**At an internal boundary.** The member-step language (`SetReadings.memberSteps`: atoms `A`, `B`, the rules
`{A, y} ⇒ B` and `{x, ...rest} ⇒ {y, ...rest} if x ⇒ y`), asked at `{{A}}`. The congruence steps the member `{A}`,
and `{A, y} ⇒ B` fires only where `{A}` is written with a copy:

| declared reading | the member is stepped at | some run reaches `{B}` |
|---|---|---|
| consume | its canonical form `{A}` | no |
| keep | its saturated form `{A, A, A}` | no |
| either | any presentation, `{A, A}` among them | yes |

**At a premise's child.** The language `SetReadings.ModuloControls.twice` (the rules `{y} ⇒ C` and
`{x} ⇒ B if {x, x} ⇒ z`), asked at `{A}`:

| declared reading | the child `{A, A}` | some run reaches `B` |
|---|---|---|
| consume | is read at its canonical form `{A}`, where `{y} ⇒ C` fires | yes |
| keep | is never asked: `{A}` is written saturated, where no rule with one member matches | no |
| either | is read at `{A}` among its presentations | yes |

Under consume the child's canonical form is the term itself, so derivations nest without bound; the table of the
region decides it (`decidePresented`).

**At a rest.** The language `SetReadings.ModuloControls.drain` (the rules `{y} ⇒ C` and `{x, ...rest} ⇒ x if rest ⇒ w`),
asked at `{A}`:

| declared reading | `{A}` is written | its rest | some run reaches `A` |
|---|---|---|---|
| consume | `{A}` | `{}`, which does not step | no |
| keep | saturated, `{A, A}` | `{A}`, written `{A, A}` again: no derivation ends | no |
| either | `{A, A}` among its presentations | `{A}`, which steps by `{y} ⇒ C` | yes |
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open SetReadings (pool onlyA onlyB reaches eventually token set)

/-! ## At the top of a step -/

def consumePool : DeclaredLanguage := { language := pool, sets := .consume }
def keepPool : DeclaredLanguage := { language := pool, sets := .keep }
def eitherPool : DeclaredLanguage := { language := pool }

theorem consume_reaches : askDeclared RelationEnv.empty consumePool 2 3 (reaches onlyB) onlyA = some true := by
  decide +kernel

theorem consume_eventually : askDeclared RelationEnv.empty consumePool 2 3 (eventually onlyB) onlyA = some true := by
  decide +kernel

theorem keep_reaches : askDeclared RelationEnv.empty keepPool 2 3 (reaches onlyB) onlyA = some false := by
  decide +kernel

theorem keep_eventually : askDeclared RelationEnv.empty keepPool 2 3 (eventually onlyB) onlyA = some false := by
  decide +kernel

theorem either_reaches : askDeclared RelationEnv.empty eitherPool 2 3 (reaches onlyB) onlyA = some true := by
  decide +kernel

theorem either_eventually_open :
    askDeclared RelationEnv.empty eitherPool 2 3 (eventually onlyB) onlyA = none := by
  decide +kernel

/-- **The declared readings disagree as the readings do**: consume and either establish that some run reaches `{B}`,
keep refutes it. -/
theorem declared_verdicts :
    (nativeStructure RelationEnv.empty consumePool).sat Env.closed (reaches onlyB) (pointOf consumePool onlyA) ∧
      ¬ (nativeStructure RelationEnv.empty keepPool).sat Env.closed (reaches onlyB) (pointOf keepPool onlyA) ∧
      (nativeStructure RelationEnv.empty eitherPool).sat Env.closed (reaches onlyB) (pointOf eitherPool onlyA) :=
  ⟨(askDeclared_sound (by decide) (formsSuit_none _ _) consume_reaches).mp rfl,
    fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) keep_reaches).mpr holds),
    (askDeclared_sound (by decide) (formsSuit_none _ _) either_reaches).mp rfl⟩

/-! ## At an internal boundary -/

open SetReadings (memberSteps doubleRule memberStepRule setAtom hfRule ModuloSetLanguage moduloForms
  answersAlike_empty NestedElement)

def consumeMembers : DeclaredLanguage := { language := memberSteps, sets := .consume }
def keepMembers : DeclaredLanguage := { language := memberSteps, sets := .keep }
def eitherMembers : DeclaredLanguage := { language := memberSteps }

/-- **The member-step language read modulo the set laws**, its steps listed with two copies at one depth. -/
theorem memberSteps_modulo : ModuloSetLanguage RelationEnv.empty memberSteps hfRule [2] true where
  hereditary := ⟨rfl, by decide, ⟨by simp [memberSteps], ⟨"members", rfl⟩, rfl⟩⟩
  rules := by
    intro rule member
    simp only [show memberSteps.rewrites = [doubleRule, memberStepRule] from rfl, List.mem_cons, List.mem_nil_iff,
      or_false] at member
    rcases member with rfl | rfl
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide, by decide, fun _ inside => by
        simp [doubleRule] at inside⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at elementMember
      rcases elementMember with rfl | rfl
      · exact .closed _ (.atom ⟨setAtom "A", by simp [memberSteps], rfl, rfl, rfl⟩) rfl
      · exact .var _ _
    · refine ⟨.set (by decide) fun element elementMember => ?_, by decide, by decide, fun premise inside => ?_⟩
      · rw [List.mem_singleton] at elementMember
        subst elementMember
        exact .var _ _
      · rw [show memberStepRule.premises = [.congruence (.fvar "x") (.fvar "y")] from rfl, List.mem_singleton] at inside
        subst inside
        exact ⟨by decide, .var _ _, by decide⟩
  answers := answersAlike_empty

abbrev memberForms : CanonicalForms RelationEnv.empty memberSteps 2 := moduloForms memberSteps_modulo 2

theorem consume_member : askDeclared RelationEnv.empty consumeMembers 2 4 (reaches (set [token "B"]))
    (set [set [token "A"]]) = some false := by
  decide +kernel

theorem keep_member : askDeclared RelationEnv.empty keepMembers 2 4 (reaches (set [token "B"]))
    (set [set [token "A"]]) = some false := by
  decide +kernel

theorem either_member : askDeclared RelationEnv.empty eitherMembers 2 4 (reaches (set [token "B"]))
    (set [set [token "A"]]) (some memberForms) = some true := by
  decide +kernel

theorem memberForms_suit : FormsSuit RelationEnv.empty eitherMembers (some memberForms) := by
  intro found same
  cases same
  exact SetReadings.moduloReading_structure (relEnv := RelationEnv.empty) (language := memberSteps) [2]

/-- **The readings part at an internal boundary**: under consume and keep the member `{A}` is stepped as they present
it, where `{A, y} ⇒ B` does not fire, and no run from `{{A}}` reaches `{B}`; under either it is stepped at `{A, A}`,
and a run does. -/
theorem member_verdicts :
    ¬ (nativeStructure RelationEnv.empty consumeMembers).sat Env.closed (reaches (set [token "B"]))
        (pointOf consumeMembers (set [set [token "A"]])) ∧
      ¬ (nativeStructure RelationEnv.empty keepMembers).sat Env.closed (reaches (set [token "B"]))
        (pointOf keepMembers (set [set [token "A"]])) ∧
      (nativeStructure RelationEnv.empty eitherMembers).sat Env.closed (reaches (set [token "B"]))
        (pointOf eitherMembers (set [set [token "A"]])) :=
  ⟨fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) consume_member).mpr holds),
    fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) keep_member).mpr holds),
    (askDeclared_sound (by decide) memberForms_suit either_member).mp rfl⟩

/-! ## At a premise's child -/

open SetReadings.ModuloControls (twice drain twice_modulo drain_modulo twiceForms drainForms)
open SetReadings (tabledFormsAt_structure)

def consumeTwice : DeclaredLanguage := { language := twice, sets := .consume }
def keepTwice : DeclaredLanguage := { language := twice, sets := .keep }
def eitherTwice : DeclaredLanguage := { language := twice }

theorem consume_twice : askDeclared RelationEnv.empty consumeTwice 2 4 (reaches (token "B")) (set [token "A"]) =
    some true := by
  decide +kernel

theorem keep_twice : askDeclared RelationEnv.empty keepTwice 2 4 (reaches (token "B")) (set [token "A"]) =
    some false := by
  decide +kernel

theorem either_twice : askDeclared RelationEnv.empty eitherTwice 1 4 (reaches (token "B")) (set [token "A"])
    (some twiceForms) = some true := by
  decide +kernel

theorem twiceForms_suit : FormsSuit RelationEnv.empty eitherTwice (some twiceForms) := by
  intro found same
  cases same
  exact tabledFormsAt_structure twice_modulo 1 (set [token "A"]) 6

/-- **The readings part at a premise's child**: consume and either read the child `{A, A}` at `{A}`, where it steps, and
reach `B`; keep writes `{A}` saturated, where no rule fires. -/
theorem twice_verdicts :
    (nativeStructure RelationEnv.empty consumeTwice).sat Env.closed (reaches (token "B"))
        (pointOf consumeTwice (set [token "A"])) ∧
      ¬ (nativeStructure RelationEnv.empty keepTwice).sat Env.closed (reaches (token "B"))
        (pointOf keepTwice (set [token "A"])) ∧
      (nativeStructure RelationEnv.empty eitherTwice).sat Env.closed (reaches (token "B"))
        (pointOf eitherTwice (set [token "A"])) :=
  ⟨(askDeclared_sound (by decide) (formsSuit_none _ _) consume_twice).mp rfl,
    fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) keep_twice).mpr holds),
    (askDeclared_sound (by decide) twiceForms_suit either_twice).mp rfl⟩

/-! ## At a rest -/

def consumeDrain : DeclaredLanguage := { language := drain, sets := .consume }
def keepDrain : DeclaredLanguage := { language := drain, sets := .keep }
def eitherDrain : DeclaredLanguage := { language := drain }

theorem consume_drain : askDeclared RelationEnv.empty consumeDrain 2 4 (reaches (token "A")) (set [token "A"]) =
    some false := by
  decide +kernel

theorem keep_drain : askDeclared RelationEnv.empty keepDrain 2 4 (reaches (token "A")) (set [token "A"]) =
    some false := by
  decide +kernel

theorem either_drain : askDeclared RelationEnv.empty eitherDrain 1 4 (reaches (token "A")) (set [token "A"])
    (some drainForms) = some true := by
  decide +kernel

theorem drainForms_suit : FormsSuit RelationEnv.empty eitherDrain (some drainForms) := by
  intro found same
  cases same
  exact tabledFormsAt_structure drain_modulo 1 (set [token "A"]) 6

/-- **The readings part at a rest**: consume leaves the empty rest, which does not step; keep writes the rest
saturated again, and no derivation ends; either writes `{A}` as `{A, A}`, whose rest `{A}` steps, and reaches `A`. -/
theorem drain_verdicts :
    ¬ (nativeStructure RelationEnv.empty consumeDrain).sat Env.closed (reaches (token "A"))
        (pointOf consumeDrain (set [token "A"])) ∧
      ¬ (nativeStructure RelationEnv.empty keepDrain).sat Env.closed (reaches (token "A"))
        (pointOf keepDrain (set [token "A"])) ∧
      (nativeStructure RelationEnv.empty eitherDrain).sat Env.closed (reaches (token "A"))
        (pointOf eitherDrain (set [token "A"])) :=
  ⟨fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) consume_drain).mpr holds),
    fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) (formsSuit_none _ _) keep_drain).mpr holds),
    (askDeclared_sound (by decide) drainForms_suit either_drain).mp rfl⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.Controls
