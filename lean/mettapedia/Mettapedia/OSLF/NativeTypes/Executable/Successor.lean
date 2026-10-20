import Mettapedia.OSLF.NativeTypes.Executable.Finite
import Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation

/-!
# Finite behavioural checking of successor observations

The public finite checker decides recurrence on a finite successor observation
of a possibly infinite source. Its positive and negative answers refer to
actual infinite source paths. The source needs a commuting successor map;
neither initiality nor a source enumeration is required by this strategy.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Successor

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open Reference.Core (Outcome)

universe u v
variable {A : Type u} {B : Type v} [Fintype B] [DecidableEq B]

def table (next : B → B) : FiniteGraph.Table (span next) where
  edge source target := decide (target = next source)
  exact := by
    intro source target
    change decide (target = next source) = true ↔
      ∃ event, event = source ∧ next event = target
    simp [eq_comm]

private theorem mapped_answer {first second : Prop} (equivalent : first ↔ second)
    (result : Outcome first) : (result.map equivalent).answer = result.answer := by
  cases result <;> rfl

/-- The source proof carried by the public checker does not change the
finite verdict or its Unknown state. -/
theorem source_answer (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    (accepting : Finset B) (budget : Nat) (value : A) :
    (Finite.checkSource (table second) (observation first second encode commutes)
      (Formula.buchi .future)
      (Finite.buchi_coverage _ (source_lifts first second encode commutes))
      (fun _ => accepting) budget value).map Outcome.answer =
    (Finite.check (table second) (Formula.buchi .future) (fun _ => accepting)
      budget (encode value)).map Outcome.answer := by
  simp only [Finite.checkSource, Finite.check, FiniteMuCalculus.check?,
    Formula.buchi_positive, ↓reduceDIte, Option.map_some, mapped_answer]
  rfl

theorem positive_iff_path (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    (accepting : Finset B) (budget : Nat) (value : A)
    (enough : FiniteMuCalculus.requiredBudget (State := B)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.checkSource (table second) (observation first second encode commutes)
      (Formula.buchi .future)
      (Finite.buchi_coverage _ (source_lifts first second encode commutes))
      (fun _ => accepting) budget value).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (span first)) .future
      (encode ⁻¹' (↑accepting : Set B)) value := by
  rw [source_answer]
  exact (Finite.check_buchi_iff (table second) accepting budget (encode value) enough).trans
    (buchi_iff first second encode commutes (↑accepting : Set B) value)

theorem negative_iff_no_path (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    (accepting : Finset B) (budget : Nat) (value : A)
    (enough : FiniteMuCalculus.requiredBudget (State := B)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.checkSource (table second) (observation first second encode commutes)
      (Formula.buchi .future)
      (Finite.buchi_coverage _ (source_lifts first second encode commutes))
      (fun _ => accepting) budget value).map Outcome.answer = some (some false) ↔
    ¬ BuchiPath (transitionSystem (span first)) .future
      (encode ⁻¹' (↑accepting : Set B)) value := by
  rw [source_answer]
  refine (Finite.check_negative_iff (table second) _ (Formula.buchi_positive _)
    (fun _ => accepting) budget (encode value) enough).trans ?_
  apply not_congr
  exact (satisfies_buchi_iff_path (transitionSystem (span second)) .future
    (↑accepting : Set B) (encode value)).trans
      (buchi_iff first second encode commutes (↑accepting : Set B) value)

theorem short_allowance_unknown (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    (accepting : Finset B) (budget : Nat) (value : A)
    (short : budget < FiniteMuCalculus.requiredBudget (State := B)
      (Formula.buchi Traversal.future)) :
    (Finite.checkSource (table second) (observation first second encode commutes)
      (Formula.buchi .future)
      (Finite.buchi_coverage _ (source_lifts first second encode commutes))
      (fun _ => accepting) budget value).map Outcome.answer = some none := by
  rw [source_answer]
  simp only [Finite.check, FiniteMuCalculus.check?, Formula.buchi_positive,
    ↓reduceDIte, Option.map_some]
  exact congrArg some (FiniteMuCalculus.check_unknown_of_budget (Finite.model (table second))
    _ (Formula.buchi_positive _) (fun _ => accepting) budget (encode value) short)

end Mettapedia.OSLF.NativeTypes.Executable.Successor
