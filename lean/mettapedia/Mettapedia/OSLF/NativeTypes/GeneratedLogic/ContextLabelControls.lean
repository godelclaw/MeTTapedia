import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNetDistinctions

/-!
# Controls: context labels

In `tiny`, `Out p ~> p` fires at the root, and the congruence for `Par` covers its left component only. The modal
decider evaluates at the listed successors, with the static decider as its base.

- **A term that needs its context**: `Nil` has no step of its own (`nil_has_no_step`), and placed in `Out _` it steps
  (`nil_steps_in_out`), to `Nil` again (`nil_in_out_returns`), so it does so twice in a row (`nil_steps_twice_in_out`).
- **A context that offers nothing**: placed in `Par Nil _`, `Out Nil` does not step, since the congruence covers only the
  left component (`out_stuck_on_the_right`); placed in `Par _ Nil` it does (`out_steps_on_the_left`), at the
  congruence's site (`out_steps_at_the_site`) and not at the root (`out_not_at_the_root`).
- **A binder context**: placed under the abstraction `Abs (λ. _)`, the term is in no reactive position
  (`under_binder_stuck`).

In the Petri net `{A, B, ...r} ⇒ {C, D, ...r}`, `{C, ...r} ⇒ {A, ...r}`, read modulo its bag laws through sorted bags, a
context `{c₁, …, cₙ, ...x}` places a marking beside tokens: the parallel context of the net.

- **What a marking lacks**: `{A}` is stuck (`a_stuck`); beside `B` it steps (`a_beside_b_steps`), and only to `{C, D}`
  (`a_beside_b_gives_cd`); beside `D` it is stuck (`a_beside_d_stuck`).
- **The order of a marking is immaterial**: beside `A`, `{B}` steps to `{C, D}` too (`b_beside_a_gives_cd`).
- **Contexts compose**: beside `B`, then beside `C`, `{A}` steps twice (`a_beside_b_then_c`).
- **The net is a token net** (`petriNet`), so its least labels are the theory's: the least label of `{A}` for
  `ConsumeAB` is `{B}`, with result `{C, D}` (`a_least_label`), and that transition is a context step at the front door
  (`a_least_label_steps`).
- **No environment tells `{D}` from the empty marking**, since no rule consumes `D` (`d_inert`), so they have the same
  context-labelled native types (`d_same_native_types`). `{A}` is told apart from it, beside `B` (`a_not_inert`).
- **Read as distinctions**: under the native-type observer `{D}` and the empty marking are indistinguishable
  (`d_indistinguishable`), and `{A}` and the empty marking are apart (`a_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabelControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
open Mettapedia.GSLT.BagRelativePushout (bag)
open Mettapedia.GSLT.RedexRelativeCongruence (ActIPO)

/-- The modal decider of `tiny`. -/
def decider : Decider RelationEnv.empty tiny :=
  modalDecider (equationFreeSuccessors 3 tiny_equationFree) (staticDecider tiny_equationFree)

theorem proved {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some true) :
    Tiny.sat Env.closed formula term :=
  (decider.exact decided).mpr rfl

theorem refuted {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some false) :
    ¬ Tiny.sat Env.closed formula term :=
  fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)

/-- Placed as the argument of `Out`. -/
def inOut (label : StepLabel) : StepLabel := .context "x" (out (.fvar "x")) label

/-- Placed as the right component of `Par Nil _`. -/
def onTheRight (label : StepLabel) : StepLabel := .context "x" (par nilTerm (.fvar "x")) label

/-- Placed as the left component of `Par _ Nil`. -/
def onTheLeft (label : StepLabel) : StepLabel := .context "x" (par (.fvar "x") nilTerm) label

/-- Placed as the body of `Abs (λ. _)`. -/
def underBinder (label : StepLabel) : StepLabel := .context "x" (.apply "Abs" [.lambda none (.fvar "x")]) label

/-- **`Nil` has no step of its own.** -/
theorem nil_has_no_step : ¬ Tiny.sat Env.closed (.possibly .any .top) nilTerm :=
  refuted (by decide +kernel)

/-- **Placed in `Out _`, `Nil` steps.** -/
theorem nil_steps_in_out : Tiny.sat Env.closed (.possibly (inOut .any) .top) nilTerm :=
  proved (by decide +kernel)

/-- **Every step of `Nil` placed in `Out _` returns `Nil`.** -/
theorem nil_in_out_returns : Tiny.sat Env.closed (.necessarily (inOut .any) (.is nilTerm)) nilTerm :=
  proved (by decide +kernel)

/-- **`Nil` steps in `Out _` twice in a row.** -/
theorem nil_steps_twice_in_out :
    Tiny.sat Env.closed (.possibly (inOut .any) (.possibly (inOut .any) .top)) nilTerm :=
  proved (by decide +kernel)

/-- **Placed as the right component of `Par Nil _`, `Out Nil` does not step.** -/
theorem out_stuck_on_the_right : ¬ Tiny.sat Env.closed (.possibly (onTheRight .any) .top) (out nilTerm) :=
  refuted (by decide +kernel)

/-- **Placed as the left component of `Par _ Nil`, `Out Nil` steps.** -/
theorem out_steps_on_the_left : Tiny.sat Env.closed (.possibly (onTheLeft .any) .top) (out nilTerm) :=
  proved (by decide +kernel)

/-- **It steps at the site of the congruence**, firing `Out` there. -/
theorem out_steps_at_the_site : Tiny.sat Env.closed (.possibly (onTheLeft (.under 1 (.rule 0))) .top) (out nilTerm) :=
  proved (by decide +kernel)

/-- **And not at the root.** -/
theorem out_not_at_the_root : ¬ Tiny.sat Env.closed (.possibly (onTheLeft (.rule 0)) .top) (out nilTerm) :=
  refuted (by decide +kernel)

/-- **Under the binder of `Abs`, `Out Nil` does not step.** -/
theorem under_binder_stuck : ¬ Tiny.sat Env.closed (.possibly (underBinder .any) .top) (out nilTerm) :=
  refuted (by decide +kernel)

/-! ## The Petri net beside tokens -/

section Petri

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls (petriCore Petri petri_no_equations petri_no_algebra
  petri_guarded marking token)

/-- The modal decider of the Petri net, with named markings by their sorted forms. -/
def petriDecider : Decider RelationEnv.empty petriCore :=
  modalDecider (bagSuccessors 2 petri_no_equations petri_no_algebra petri_guarded)
    (namedDecider _ _ (BagForms.canonical petri_no_equations petri_no_algebra))

theorem petri_proved {formula : Formula 0} {term : Pattern} (decided : petriDecider.decide formula term = some true) :
    Petri.sat Env.closed formula term :=
  (petriDecider.exact decided).mpr rfl

theorem petri_refuted {formula : Formula 0} {term : Pattern} (decided : petriDecider.decide formula term = some false) :
    ¬ Petri.sat Env.closed formula term :=
  fun holds => Bool.false_ne_true ((petriDecider.exact decided).mp holds)

/-- Placed beside tokens. -/
def beside (names : List String) (label : StepLabel) : StepLabel :=
  .context "x" (.collection .hashBag (names.map token) (some "x")) label

/-- **`{A}` is stuck.** -/
theorem a_stuck : ¬ Petri.sat Env.closed (.possibly .any .top) (marking [token "A"]) :=
  petri_refuted (by decide +kernel)

/-- **Beside `B`, `{A}` steps.** -/
theorem a_beside_b_steps : Petri.sat Env.closed (.possibly (beside ["B"] .any) .top) (marking [token "A"]) :=
  petri_proved (by decide +kernel)

/-- **And only to `{C, D}`.** -/
theorem a_beside_b_gives_cd :
    Petri.sat Env.closed (.necessarily (beside ["B"] .any) (.is (marking [token "C", token "D"]))) (marking [token "A"]) :=
  petri_proved (by decide +kernel)

/-- **Beside `D`, `{A}` is stuck.** -/
theorem a_beside_d_stuck : ¬ Petri.sat Env.closed (.possibly (beside ["D"] .any) .top) (marking [token "A"]) :=
  petri_refuted (by decide +kernel)

/-- **Beside `A`, `{B}` steps to `{C, D}` too**: the order of a marking is immaterial. -/
theorem b_beside_a_gives_cd :
    Petri.sat Env.closed (.possibly (beside ["A"] .any) (.is (marking [token "D", token "C"]))) (marking [token "B"]) :=
  petri_proved (by decide +kernel)

/-- **Beside `B`, then beside `C`, `{A}` steps twice.** -/
theorem a_beside_b_then_c :
    Petri.sat Env.closed (.possibly (beside ["B"] .any) (.possibly (beside ["C"] .any) .top)) (marking [token "A"]) :=
  petri_proved (by decide +kernel)

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls (consumeAB recycleC bagRule placeRule)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType ArgumentsHaveTypes FreeTypeContext)

theorem place_typed (name : String) (declared : placeRule name ∈ petriCore.terms) :
    HasType petriCore FreeTypeContext.empty [] (TokenNets.token name) (.base "Place") :=
  HasType.constructor (rule := placeRule name) declared
    (by rintro ⟨_, _, _, bare⟩; simp [placeRule, GrammarRule.bareParams] at bare) .nil

/-- **The Petri net is a token net.** -/
def petriNet : TokenNets.TokenNet petriCore where
  noEquations := petri_no_equations
  noAlgebra := petri_no_algebra
  former := bagRule "MarkingBag" "Marking" "tokens"
  formerDeclared := by simp [petriCore]
  sort := "Place"
  parameter := "tokens"
  formerParameter := by simp [bagRule]
  tokens := ["A", "B", "C", "D"]
  typed name member := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact place_typed _ (by simp [petriCore])
  rules rule member := by
    simp only [petriCore, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨["A", "B"], ["C", "D"], "rest"⟩, ⟨rfl, rfl, rfl⟩, by decide, by decide⟩
    · exact ⟨⟨["C"], ["A"], "rest"⟩, ⟨rfl, rfl, rfl⟩, by decide, by decide⟩

/-- **The least label of `{A}` for `ConsumeAB` is `{B}`**, with result `{C, D}`. -/
theorem a_least_label :
    ActIPO (TokenNets.reactions petriCore) (bag (["B"] : Multiset String)) (bag (["A"] : Multiset String))
      (bag (["C", "D"] : Multiset String)) :=
  TokenNets.actIPO_iff.mpr ⟨consumeAB, by simp [petriCore], ⟨["A", "B"], ["C", "D"], "rest"⟩, ⟨rfl, rfl, rfl⟩,
    by decide, by decide⟩

/-- **And that transition is a context step at the front door**: placed beside `B`, `{A}` steps to `{C, D}`. -/
theorem a_least_label_steps :
    Petri.step (TokenNets.marking ["A"]) (.context "x" (TokenNets.beside "x" ["B"]) .any) (TokenNets.marking ["C", "D"]) :=
  TokenNets.step_of_actIPO petriNet "x" (fun _ member => by simp at member; simp [member, petriNet])
    (fun _ member => by simp at member; simp [member, petriNet]) a_least_label

open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn)
open TokenNets (NetFormula nativeFormula TokenBag)

theorem empty_region : TokenNets.Region petriNet [] := fun _ member => nomatch member

theorem single_region {name : String} (member : name ∈ petriNet.tokens) : TokenNets.Region petriNet [name] :=
  fun _ found => by simp only [List.mem_cons, List.not_mem_nil, or_false] at found; exact found ▸ member

/-- **No environment tells `{D}` from the empty marking**: no rule consumes `D`. -/
theorem d_inert :
    SaturatedBisimilarIn (TokenNets.reactions petriCore) (TokenBag petriNet) (["D"] : Multiset String)
      (([] : List String) : Multiset String) := by
  refine TokenNets.inert_saturated ?_ _ 0
  intro rule member netRule presents
  simp only [petriCore, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [presents.unique (second := ⟨["A", "B"], ["C", "D"], "rest"⟩) ⟨rfl, rfl, rfl⟩]
    decide
  · rw [presents.unique (second := ⟨["C"], ["A"], "rest"⟩) ⟨rfl, rfl, rfl⟩]
    decide

/-- **So `{D}` and the empty marking have the same native types over the net's contexts.** -/
theorem d_same_native_types (formula : NetFormula) (within : formula.Within (TokenBag petriNet)) :
    Petri.sat Env.closed (nativeFormula formula) (TokenNets.marking ["D"]) ↔
      Petri.sat Env.closed (nativeFormula formula) (TokenNets.marking []) :=
  (TokenNets.saturated_iff_nativeTypes petriNet (single_region (by decide)) empty_region).mp d_inert formula within

/-- **`{A}` is told apart from the empty marking**: beside `B` it steps, and the empty marking does not. -/
theorem a_not_inert :
    ¬ SaturatedBisimilarIn (TokenNets.reactions petriCore) (TokenBag petriNet) (["A"] : Multiset String)
      (([] : List String) : Multiset String) := fun bisimilar => by
  have agree := (TokenNets.saturated_iff_nativeTypes (relEnv := RelationEnv.empty) petriNet
    (single_region (by decide)) empty_region).mp bisimilar (.possibly ["B"] .top)
    ⟨fun _ member => by simp at member; simp [member, petriNet], trivial⟩
  exact petri_refuted (by decide +kernel) (agree.mp (petri_proved (by decide +kernel)))

/-- **Under the native-type observer `{D}` and the empty marking are indistinguishable.** -/
theorem d_indistinguishable : (TokenNets.nativeObserver petriNet RelationEnv.empty).Indistinguishable ["D"] [] :=
  (TokenNets.indistinguishable_iff_saturated petriNet RelationEnv.empty (single_region (by decide)) empty_region).mpr
    d_inert

/-- **Under the native-type observer `{A}` and the empty marking are apart.** -/
theorem a_apart : (TokenNets.nativeObserver petriNet RelationEnv.empty).Apart ["A"] [] :=
  (TokenNets.apart_iff_not_saturated petriNet RelationEnv.empty (single_region (by decide)) empty_region).mpr
    a_not_inert

end Petri

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabelControls
