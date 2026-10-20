import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL
import Mettapedia.Languages.Megalodon.NaturalClosure
import Mettapedia.Languages.Megalodon.NaturalRecursion

/-!
# The native natural-closure predicate on the authored carrier

The constant-free Mathdata definition has an exact intrinsic HOL reading.
Here that same reading is instantiated in the existing interpretation of the
admitted natural declaration. Its membership and induction concern the actual
source carrier and successor. A collapsing successor supplies an explicit
negative comparison; closure alone does not provide Peano's other properties.

Native proof acceptance is qualified separately against the exact Mathdata
statements. Neither this model nor truth in it supplies native proof extraction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodon

open Mettapedia.Logic.HOL
open Mettapedia.Languages.Megalodon
open IndexedInductiveNatVec

open IndexedInductiveNaturalHOL Mettapedia.Logic.HOL.SevenVirtues

/-- The source constants are applied to the same typed closure definition. -/
def membership {context : Ctx Unit} (number : Term Peano.PeanoConst context Peano.ι) :
    Formula Peano.PeanoConst context :=
  Mettapedia.Logic.HOL.NaturalClosure.predicate (.const .zero) (.const .succ) number

theorem source_member (number : Natural.Carrier) :
    Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model Peano.ι
      peanoStructure.zero peanoStructure.succ (ULift.up number) := by
  intro property _ atZero atSuccessor
  exact IndexedInductiveNaturalHOL.induction (fun previous => (property (ULift.up previous)).down)
    atZero (fun previous holds => atSuccessor (ULift.up previous)
      (fullDomains _ _) holds) number

theorem source_membership_formula :
    model.models (.all (σ := Peano.ι) (membership (.var .vz))) := by
  intro number _
  exact source_member number.down

/-- The native generic statements are satisfied by the selected source
interpretation, independently of their native proof objects. -/
theorem source_native_formulas :
    model.models (Mettapedia.Logic.HOL.NaturalClosure.zeroStatement Peano.ι) ∧
    model.models (Mettapedia.Logic.HOL.NaturalClosure.successorStatement Peano.ι) ∧
    model.models (Mettapedia.Logic.HOL.NaturalClosure.inductionStatement Peano.ι) :=
  ⟨Mettapedia.Logic.HOL.NaturalClosure.models_zero _ _, Mettapedia.Logic.HOL.NaturalClosure.models_successor _ _,
    Mettapedia.Logic.HOL.NaturalClosure.models_induction _ fullDomains _⟩

/-- The closure hypothesis may be omitted on this carrier because every
source value satisfies it; no inhabitant is silently removed from induction. -/
theorem source_induction (property : model.Carrier () → Prop)
    (atZero : property peanoStructure.zero)
    (atSuccessor : ∀ number,
      Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model Peano.ι peanoStructure.zero
        peanoStructure.succ number →
      property number → property (peanoStructure.succ number)) :
    ∀ number, property number := by
  intro number
  exact IndexedInductiveNaturalHOL.induction (fun previous => property (ULift.up previous)) atZero
    (fun previous holds => atSuccessor (ULift.up previous) (source_member previous) holds)
    number.down

/-- A wrong realization of successor does not make a genuine source
successor satisfy the translated closure predicate. -/
theorem collapsing_successor_refused :
    ¬ Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model Peano.ι peanoStructure.zero
      (fun _ => peanoStructure.zero) (ULift.up (Natural.succ Natural.zero)) := by
  intro closed
  let property : model.Carrier () → ULift.{1} Prop :=
    fun number => .up (number = peanoStructure.zero)
  have collapsed := closed property (fullDomains _ _) rfl (by
    intro _ _ _
    rfl)
  exact Natural.succ_ne_zero Natural.zero (congrArg ULift.down collapsed)

/-- At zero the same collapsed operation does satisfy closure, so the
negative test is about the selected source operation, not empty evidence. -/
theorem collapsing_zero_accepted :
    Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model Peano.ι peanoStructure.zero
      (fun _ => peanoStructure.zero) peanoStructure.zero :=
  Mettapedia.Logic.HOL.NaturalClosure.closedUnder_zero _ _ _ _

universe v

/-- The native graph's independent mathematical reading contains the actual
authored eliminator, at every result type. -/
theorem source_recursion_graph {A : Type v} (start : A)
    (step : Natural.Carrier → A → A) (number : Natural.Carrier) :
    NaturalRecursion.Graph Natural.zero Natural.succ start step number (recurse start step number) := by
  apply IndexedInductiveNaturalHOL.induction
    (fun n => NaturalRecursion.Graph Natural.zero Natural.succ start step n (recurse start step n))
  · simpa only [recurse_zero] using
      (NaturalRecursion.Graph.zero (zero := Natural.zero) (successor := Natural.succ)
        (start := start) (step := step))
  · intro n prior
    simpa only [recurse_succ] using NaturalRecursion.Graph.successor prior

theorem source_graph_iff {A : Type v} (start : A) (step : Natural.Carrier → A → A)
    (number : Natural.Carrier) (value : A) :
    NaturalRecursion.Graph Natural.zero Natural.succ start step number value ↔
      value = recurse start step number := by
  constructor
  · intro graph
    exact graph.agrees (recurse start step) (recurse_zero start step)
      (fun n _ _ => recurse_succ start step n)
  · rintro rfl
    exact source_recursion_graph start step number

/-- Every authored value is generated; no proper subset is substituted for
the source carrier when applying native uniqueness. -/
theorem source_generated (number : Natural.Carrier) (predicate : Natural.Carrier → Prop)
    (initial : predicate Natural.zero)
    (closed : ∀ n, predicate n → predicate (Natural.succ n)) : predicate number :=
  IndexedInductiveNaturalHOL.induction predicate initial closed number

theorem source_selector_agrees {A : Type v} (start : A) (step : Natural.Carrier → A → A)
    (choose : (A → Prop) → A)
    (selects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate))
    (number : Natural.Carrier) :
    NaturalRecursion.selected choose Natural.zero Natural.succ start step number =
      recurse start step number := by
  apply (source_graph_iff start step number _).mp
  exact NaturalRecursion.selected_graph choose selects (source_generated number)

theorem source_selectors_agree {A : Type v} (start : A) (step : Natural.Carrier → A → A)
    (first second : (A → Prop) → A)
    (firstSelects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (first predicate))
    (secondSelects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (second predicate))
    (number : Natural.Carrier) :
    NaturalRecursion.selected first Natural.zero Natural.succ start step number =
      NaturalRecursion.selected second Natural.zero Natural.succ start step number :=
  (source_selector_agrees start step first firstSelects number).trans
    (source_selector_agrees start step second secondSelects number).symm

/-- This interpretation may supply a selector at an inhabited target. The
choice is a semantic witness, not an executable implementation or a global
choice rule for a dependent guest. -/
theorem source_recursion_with_choice {A : Type v} (start : A)
    (step : Natural.Carrier → A → A) :
    ∃ choose : (A → Prop) → A,
      (∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate)) ∧
      ∀ number, NaturalRecursion.selected choose Natural.zero Natural.succ start step number =
        recurse start step number := by
  classical
  let choose := fun predicate : A → Prop =>
    if inhabited : ∃ value, predicate value then Classical.choose inhabited else start
  have selects : ∀ predicate : A → Prop,
      (∃ value, predicate value) → predicate (choose predicate) := by
    intro predicate inhabited
    simpa only [choose, dif_pos inhabited] using Classical.choose_spec inhabited
  exact ⟨choose, selects, source_selector_agrees start step choose selects⟩

theorem source_recursion_statement (target : Ty Unit) :
    model.models (NaturalRecursion.recursionStatement Peano.ι target) :=
  NaturalRecursion.models_recursion model fullDomains Peano.ι target

theorem source_successor_formulas :
    model.models (NaturalRecursion.zeroExcluded (.const Peano.PeanoConst.zero)
      (.const Peano.PeanoConst.succ)) ∧
    model.models (NaturalRecursion.successorInjective (.const Peano.PeanoConst.succ)) := by
  constructor
  · apply (NaturalRecursion.denote_zeroExcluded model fullDomains _ _ _).mpr
    intro number same
    exact Natural.succ_ne_zero number.down (congrArg ULift.down same)
  · apply (NaturalRecursion.denote_successorInjective model fullDomains _ _).mpr
    intro left right same
    exact ULift.ext _ _ (Natural.succ_injective (congrArg ULift.down same))

/-- The chosen source carrier discharges the native successor interface. -/
theorem source_successor_interface :
    (∀ number, Natural.succ number ≠ Natural.zero) ∧ Function.Injective Natural.succ :=
  ⟨Natural.succ_ne_zero, Natural.succ_injective⟩

theorem source_recursion_nonempty :
    NaturalRecursion.Graph Natural.zero Natural.succ (1 : Nat) (fun _ value => value + 1)
      (Natural.succ (Natural.succ Natural.zero)) 3 :=
  .successor (.successor .zero)

/-- A well-formed function of the right selector type can still violate
its selection law and return the wrong recursive value. -/
theorem constant_selector_wrong_result :
    ¬ NaturalRecursion.Graph Natural.zero Natural.succ (0 : Nat) (fun _ value => value + 1)
      (Natural.succ Natural.zero)
      (NaturalRecursion.selected (fun _ => 0) Natural.zero Natural.succ 0
        (fun _ value => value + 1) (Natural.succ Natural.zero)) := by
  rw [source_graph_iff]
  simp only [NaturalRecursion.selected, recurse_succ, recurse_zero]
  exact Nat.zero_ne_one

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodon
