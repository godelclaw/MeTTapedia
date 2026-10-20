import Mettapedia.OSLF.NativeTypes.Instances.Natural.Coherent
import Mettapedia.OSLF.NativeTypes.Instances.Natural.RepresentationControls

/-!
# Coherent dependent payloads and native verdicts

These controls use the actual material and surreal natural substructures.
The dependent payload is a finite index below the represented successor.
Equal lengths do not erase different payloads. A zero query budget remains
Unknown, even when the represented source has an accepting infinite path.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.CoherentControls

open Mettapedia.TypeTheory.NaturalAlgebra
open Mettapedia.TypeTheory.NaturalRepresentations
open Mettapedia.TypeTheory.NaturalRepresentationInterface
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open RepresentationControls

def Carrier : Bool → Type 1
  | false => MaterialNatural.{0}
  | true => SurrealNatural

noncomputable def algebras : ∀ index, Algebra (Carrier index)
  | false => materialAlgebra
  | true => surrealAlgebra

noncomputable def representations : ∀ index,
    Mettapedia.TypeTheory.NaturalAlgebra.Representation (algebras index)
  | false => materialRepresentation
  | true => surrealRepresentation

abbrev payload : Nat → Type := fun number => Fin (number + 1)

noncomputable def materialValue (offset : Fin 2) :
    Indexed algebras representations payload false :=
  indexedEquiv algebras representations payload false ⟨1, offset⟩

noncomputable def carried (offset : Fin 2) :
    Indexed algebras representations payload true :=
  (indexedFamily algebras representations payload).transport
    (source := false) (target := true) materialSurrealIso (materialValue offset)

theorem carried_index (offset : Fin 2) :
    (carried offset).1 = materialSurrealIso.toEquiv (materialValue offset).1 :=
  indexed_transport_index algebras representations payload
    (source := false) (target := true) materialSurrealIso _

theorem carried_payload (offset : Fin 2) :
    observe algebras representations payload (fun pair => pair.2.val) true
      (carried offset) = offset.val := by
  calc
    _ = observe algebras representations payload (fun pair => pair.2.val) false
        (materialValue offset) :=
      observe_transport algebras representations payload (fun pair => pair.2.val)
        (source := false) (target := true) materialSurrealIso _
    _ = offset.val := by
      unfold materialValue observe
      rw [Equiv.symm_apply_apply]

/-- Retaining the index alone would incorrectly identify these values. -/
theorem same_length_different_payload :
    (carried 0).1 = (carried 1).1 ∧ carried 0 ≠ carried 1 := by
  constructor
  · unfold carried materialValue indexedFamily
    simp only [Equiv.symm_apply_apply]
    rfl
  · intro same
    have offsets := congrArg
      (observe algebras representations payload (fun pair => pair.2.val) true) same
    rw [carried_payload, carried_payload] at offsets
    exact Nat.zero_ne_one offsets

theorem direct_and_via_naturals (value : MaterialNatural.{0}) :
    (values algebras).transport (source := false) (target := true)
      materialSurrealIso value =
    (values algebras).transport (source := false) (target := true)
      (natMaterialIso.symm.trans natSurrealIso) value :=
  transport_route_independent algebras representations (values algebras)
    (source := false) (target := true) _ _ value

theorem carried_recurrently_even (number : Nat) :
    BuchiPath (transitionSystem (span surrealAlgebra.succ)) .future
      (Representation.accepted surrealRepresentation {0})
      (materialSurrealIso.{0}.toEquiv (materialRepresentation.encode number)) := by
  exact (Coherent.check_at_route_iff algebras representations
    (source := false) (target := true) materialSurrealIso {0}
    recurrenceBudget number (Nat.le_refl _)).mp (recurrent_even_all_phases _)

theorem carried_empty_refuted (number : Nat) :
    ¬ BuchiPath (transitionSystem (span surrealAlgebra.succ)) .future
      (Representation.accepted surrealRepresentation ∅)
      (materialSurrealIso.{0}.toEquiv (materialRepresentation.encode number)) := by
  exact (Coherent.check_negative_at_route_iff algebras representations
    (source := false) (target := true) materialSurrealIso ∅
    recurrenceBudget number (Nat.le_refl _)).mp (empty_acceptance_all_phases _)

/-- The semantic existence proof does not promote an unfinished query to an
executable positive or negative answer. -/
theorem true_property_with_unknown_query (number : Nat) :
    recurrenceVerdict {0} 0 (Counter.phase number) = some none ∧
    BuchiPath (transitionSystem (span surrealAlgebra.succ)) .future
      (Representation.accepted surrealRepresentation {0})
      (materialSurrealIso.{0}.toEquiv (materialRepresentation.encode number)) :=
  ⟨exhausted_all_phases _, carried_recurrently_even number⟩

end Mettapedia.OSLF.NativeTypes.Instances.Natural.CoherentControls
