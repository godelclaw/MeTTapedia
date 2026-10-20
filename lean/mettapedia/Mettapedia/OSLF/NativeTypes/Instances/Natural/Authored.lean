import Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Representation
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native recurrence for the authored natural counter

The parsed module supplies the source relation. Exact root execution proves
that every outgoing transition of an encoded counter is its next counter.
This closes the finite parity query against the full authored relation,
including exclusion of additional target shapes. It makes no incoming-coverage
claim for arbitrary raw eliminator terms in that larger carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Reference.Core (Outcome)

open Mettapedia.GSLT.LanguageDef.Examples

theorem source_has_no_equations : Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.equations = [] := by rfl

/-- The declared fragment has no equations, so its source GSLT uses equality. -/
def theory (base : BasePremiseEvaluator) : Mettapedia.GSLT.GSLT :=
  equalityGSLT Pattern (Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language)

def observation (base : BasePremiseEvaluator) : SpanMap Counter.counter (gsltSpan (theory base)) where
  states := NativeNaturalCounter.counter
  events (number : Nat) := ⟨NativeNaturalCounter.counter number, NativeNaturalCounter.counter (number + 1),
    (NativeNaturalCounter.counter_step_target_iff base number _).mpr rfl⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- Coverage follows from the arbitrary-target source theorem, not merely
from constructing one chosen edge for each counter. -/
theorem outgoing_coverage (base : BasePremiseEvaluator) : (observation base).SourceLifts := by
  intro number event starts
  refine ⟨number, rfl, ?_⟩
  change NativeNaturalCounter.counter (number + 1) = event.target
  have executed : Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language (NativeNaturalCounter.counter number) event.target := by
    change event.source = NativeNaturalCounter.counter number at starts
    exact starts ▸ event.step
  exact ((NativeNaturalCounter.counter_step_target_iff base number event.target).mp executed).symm

/-- Finite source execution advances by exactly a natural number of successors.
This operational reachability fact is separate from algebraic initiality. -/
theorem finite_run_iff (base : BasePremiseEvaluator) (start : Nat) (target : Pattern) :
    (theory base).MultiStep (NativeNaturalCounter.counter start) target ↔
      ∃ steps : Nat, target = NativeNaturalCounter.counter (start + steps) := by
  constructor
  · intro run
    have forward : ∀ source target, (theory base).MultiStep source target →
        ∀ start, source = NativeNaturalCounter.counter start →
          ∃ steps : Nat, target = NativeNaturalCounter.counter (start + steps) := by
      intro source target path
      induction path with
      | refl term =>
        intro start same
        exact ⟨0, same⟩
      | step edge _ ih =>
        intro start same
        have next := (NativeNaturalCounter.counter_step_target_iff base start _).mp
          (same ▸ edge)
        obtain ⟨steps, ends⟩ := ih (start + 1) next
        refine ⟨steps + 1, ?_⟩
        simpa only [Nat.add_assoc, Nat.add_comm 1 steps] using ends
    exact forward _ _ run start rfl
  · rintro ⟨steps, rfl⟩
    induction steps generalizing start with
    | zero => exact .refl _
    | succ steps ih =>
      have next := (NativeNaturalCounter.counter_step_target_iff base start _).mpr
        (Eq.refl (NativeNaturalCounter.counter (start + 1)))
      have tail := ih (start + 1)
      exact .step next (by simpa only [Nat.add_assoc, Nat.add_comm 1 steps] using tail)

theorem reachable_from_zero_iff (base : BasePremiseEvaluator) (target : Pattern) :
    (theory base).MultiStep (NativeNaturalCounter.counter 0) target ↔
      ∃ number : Nat, target = NativeNaturalCounter.counter number := by
  simpa only [Nat.zero_add] using finite_run_iff base 0 target

def accepting (phases : Finset (Fin 2)) : Set Pattern :=
  {term | ∃ number : Nat, NativeNaturalCounter.counter number = term ∧ Counter.phase number ∈ phases}

theorem accepting_preimage (base : BasePremiseEvaluator) (phases : Finset (Fin 2)) :
    (observation base).states ⁻¹' accepting phases =
      Counter.observation.states ⁻¹' (↑phases : Set (Fin 2)) := by
  ext number
  change (∃ index, NativeNaturalCounter.counter index = NativeNaturalCounter.counter number ∧ Counter.phase index ∈ phases) ↔
    Counter.phase number ∈ phases
  simp only [NativeNaturalCounter.counter_injective.eq_iff, exists_eq_left]

/-- Exact source-level meaning of the finite public Büchi query. -/
theorem check_buchi_iff (base : BasePremiseEvaluator) (phases : Finset (Fin 2))
    (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (gsltSpan (theory base))) .future
      (accepting phases) (NativeNaturalCounter.counter number) := by
  have finiteMeaning := Finite.check_buchi_iff Counter.table phases budget (Counter.phase number) enough
  have parityMeaning := path_pullback Counter.observation Counter.outgoing_coverage
    (↑phases : Set (Fin 2)) number
  have authoredMeaning := path_pullback (observation base) (outgoing_coverage base)
    (accepting phases) number
  rw [accepting_preimage] at authoredMeaning
  exact finiteMeaning.trans (parityMeaning.trans authoredMeaning.symm)

/-- The same verdict checks the native formula on the authored GSLT, not
just a reachability proposition on the finite observation. -/
theorem check_formula_iff (base : BasePremiseEvaluator) (phases : Finset (Fin 2))
    (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some true) ↔
    satisfies (transitionSystem (gsltSpan (theory base))) (fun _ => accepting phases)
      (Formula.buchi .future) (NativeNaturalCounter.counter number) := by
  have finiteMeaning := Finite.check_positive_iff Counter.table (Formula.buchi .future)
    (Formula.buchi_positive _) (fun _ => phases) budget (Counter.phase number) enough
  have parityMeaning := satisfies_pullback Counter.observation (Formula.buchi .future)
    Counter.coverage (Formula.buchi_positive _) (fun _ => (↑phases : Set (Fin 2))) number
  have authoredMeaning := satisfies_pullback (observation base) (Formula.buchi .future)
    (Finite.buchi_coverage _ (outgoing_coverage base)) (Formula.buchi_positive _)
    (fun _ => accepting phases) number
  have environments : pullEnvironment (observation base).states (fun _ : Fin 1 => accepting phases) =
      pullEnvironment Counter.observation.states (fun _ : Fin 1 => (↑phases : Set (Fin 2))) :=
    funext fun _ => accepting_preimage base phases
  rw [environments] at authoredMeaning
  exact finiteMeaning.trans (parityMeaning.trans authoredMeaning.symm)

theorem check_negative_iff (base : BasePremiseEvaluator) (phases : Finset (Fin 2))
    (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some false) ↔
    ¬ BuchiPath (transitionSystem (gsltSpan (theory base))) .future
      (accepting phases) (NativeNaturalCounter.counter number) := by
  refine (Finite.check_negative_iff Counter.table _ (Formula.buchi_positive _)
    (fun _ => phases) budget (Counter.phase number) enough).trans ?_
  apply not_congr
  have finiteMeaning := satisfies_buchi_iff_path (transitionSystem Counter.parity) .future
    (↑phases : Set (Fin 2)) (Counter.phase number)
  have parityMeaning := path_pullback Counter.observation Counter.outgoing_coverage
    (↑phases : Set (Fin 2)) number
  have authoredMeaning := path_pullback (observation base) (outgoing_coverage base)
    (accepting phases) number
  rw [accepting_preimage] at authoredMeaning
  exact finiteMeaning.trans (parityMeaning.trans authoredMeaning.symm)

theorem every_authored_counter_recurrently_even (base : BasePremiseEvaluator) (number : Nat) :
    BuchiPath (transitionSystem (gsltSpan (theory base))) .future
      (accepting {0}) (NativeNaturalCounter.counter number) := by
  apply (check_buchi_iff base {0} 1000 number (by decide +kernel)).mp
  have both : ∀ phase : Fin 2,
      (Finite.check Counter.table (Formula.buchi .future) (fun _ => {0})
        1000 phase).map Outcome.answer = some (some true) := by decide +kernel
  exact both (Counter.phase number)

theorem no_authored_counter_recurrently_empty (base : BasePremiseEvaluator) (number : Nat) :
    ¬ BuchiPath (transitionSystem (gsltSpan (theory base))) .future
      (accepting ∅) (NativeNaturalCounter.counter number) := by
  apply (check_negative_iff base ∅ 1000 number (by decide +kernel)).mp
  have both : ∀ phase : Fin 2,
      (Finite.check Counter.table (Formula.buchi .future) (fun _ => ∅)
        1000 phase).map Outcome.answer = some (some false) := by decide +kernel
  exact both (Counter.phase number)

/-- The authored language and every faithful natural representation answer
the same recurrence query. The two meanings meet at the certified finite
observation; neither is defined by the other's verdict. -/
theorem representation_buchi_iff {Carrier : Type*}
    {algebra : Mettapedia.TypeTheory.NaturalAlgebra.Algebra Carrier}
    (representation : Mettapedia.TypeTheory.NaturalAlgebra.Representation algebra)
    (base : BasePremiseEvaluator) (phases : Finset (Fin 2)) (number : Nat) :
    BuchiPath (transitionSystem (gsltSpan (theory base))) .future
      (accepting phases) (NativeNaturalCounter.counter number) ↔
    BuchiPath (transitionSystem (Semantics.SuccessorObservation.span algebra.succ)) .future
      (Representation.accepted representation phases) (representation.encode number) := by
  let budget := FiniteMuCalculus.requiredBudget (State := Fin 2) (Formula.buchi Traversal.future)
  exact (check_buchi_iff base phases budget number (Nat.le_refl _)).symm.trans
    (Representation.check_encoded_buchi_iff representation phases budget number (Nat.le_refl _))

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored
