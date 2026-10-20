import Mettapedia.TypeTheory.NaturalRepresentations
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Representation

/-!
# Executable observations of material and surreal naturals

The finite public checker decides recurrence on both phases. Its established
transport theorem then gives actual infinite-path properties for the material
and surreal successor algebras, without executing their selected inverses.

The incoming modality also detects the boundary between the natural surreal
image and the full surreal carrier: natural zero has no predecessor, while
full surreal zero has predecessor minus one under the same addition operation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.RepresentationControls

open Mettapedia.TypeTheory.NaturalAlgebra
open Mettapedia.TypeTheory.NaturalRepresentations
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.SetTheory.SignExpansion
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Reference.Core (Outcome)

universe u

def recurrenceBudget : Nat :=
  FiniteMuCalculus.requiredBudget (State := Fin 2) (Formula.buchi Traversal.future)

def recurrenceVerdict (accepting : Finset (Fin 2)) (budget : Nat) (state : Fin 2) :
    Option (Option Bool) :=
  (Finite.check Counter.table (Formula.buchi .future) (fun _ => accepting)
    budget state).map Outcome.answer

/-- The actual public checker is evaluated for every state of the finite model. -/
theorem recurrent_even_all_phases :
    ∀ state : Fin 2, recurrenceVerdict {0} recurrenceBudget state = some (some true) := by
  decide +kernel

theorem empty_acceptance_all_phases :
    ∀ state : Fin 2, recurrenceVerdict ∅ recurrenceBudget state = some (some false) := by
  decide +kernel

theorem exhausted_all_phases :
    ∀ state : Fin 2, recurrenceVerdict {0} 0 state = some none := by
  decide +kernel

theorem material_recurrent_even (number : Nat) :
    BuchiPath (transitionSystem (span materialAlgebra.{u}.succ)) .future
      (Representation.accepted materialRepresentation {0})
      (NaturalOrdinalModel.naturalMembers number) := by
  exact (Representation.check_encoded_buchi_iff materialRepresentation {0}
    recurrenceBudget number (Nat.le_refl _)).mp (recurrent_even_all_phases _)

theorem surreal_recurrent_even (number : Nat) :
    BuchiPath (transitionSystem (span surrealAlgebra.succ)) .future
      (Representation.accepted surrealRepresentation {0}) (surrealEncode number) := by
  exact (Representation.check_encoded_buchi_iff surrealRepresentation {0}
    recurrenceBudget number (Nat.le_refl _)).mp (recurrent_even_all_phases _)

theorem material_empty_acceptance (number : Nat) :
    ¬ BuchiPath (transitionSystem (span materialAlgebra.{u}.succ)) .future
      (Representation.accepted materialRepresentation ∅)
      (NaturalOrdinalModel.naturalMembers number) := by
  exact (Representation.check_encoded_negative_iff materialRepresentation ∅
    recurrenceBudget number (Nat.le_refl _)).mp (empty_acceptance_all_phases _)

theorem surreal_empty_acceptance (number : Nat) :
    ¬ BuchiPath (transitionSystem (span surrealAlgebra.succ)) .future
      (Representation.accepted surrealRepresentation ∅) (surrealEncode number) := by
  exact (Representation.check_encoded_negative_iff surrealRepresentation ∅
    recurrenceBudget number (Nat.le_refl _)).mp (empty_acceptance_all_phases _)

def noPredecessor : Formula Traversal 0 := .box .past .ff

theorem natural_zero_no_predecessor :
    satisfies (transitionSystem (span Nat.succ)) Fin.elim0 noPredecessor 0 := by
  rintro source ⟨event, ends, _⟩
  exact Nat.succ_ne_zero event ends

theorem material_zero_no_predecessor :
    satisfies (transitionSystem (span materialAlgebra.{u}.succ)) Fin.elim0
      noPredecessor materialAlgebra.zero := by
  rw [← materialRepresentation.map_zero]
  apply (Representation.formula_iff materialRepresentation noPredecessor (by rfl)
    Fin.elim0 0).mpr
  exact natural_zero_no_predecessor

theorem surreal_zero_no_predecessor :
    satisfies (transitionSystem (span surrealAlgebra.succ)) Fin.elim0
      noPredecessor surrealAlgebra.zero := by
  rw [← surrealRepresentation.map_zero]
  apply (Representation.formula_iff surrealRepresentation noPredecessor (by rfl)
    Fin.elim0 0).mpr
  exact natural_zero_no_predecessor

theorem full_surreal_minus_one_precedes_zero :
    Surreal.add (Surreal.ofInt (-1)) (Surreal.ofNat 1) = 0 := by
  rw [← Surreal.ofInt_ofNat 1, Surreal.ofInt_add]
  norm_num [Surreal.ofInt_zero]

/-- Extending the carrier to all surreals changes incoming observations even
though successor is still actual addition of one. -/
theorem full_surreal_zero_has_predecessor :
    ¬ satisfies (transitionSystem (span (fun value => Surreal.add value (Surreal.ofNat 1))))
      Fin.elim0 noPredecessor 0 := by
  intro holds
  exact holds (Surreal.ofInt (-1))
    ⟨Surreal.ofInt (-1), full_surreal_minus_one_precedes_zero, rfl⟩

/-- Closed executable controls retain source indices instead of trying to
evaluate the noncomputable inverse of either representation. -/
theorem source_index_controls :
    [0, 1, 2, 17, 42, 101].map
      (fun number => recurrenceVerdict {0} recurrenceBudget (Counter.phase number)) =
        List.replicate 6 (some (some true)) := by
  decide +kernel

theorem rejected_source_index_controls :
    [0, 1, 2, 17, 42, 101].map
      (fun number => recurrenceVerdict ∅ recurrenceBudget (Counter.phase number)) =
        List.replicate 6 (some (some false)) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.Instances.Natural.RepresentationControls
