import Mettapedia.TypeTheory.NaturalAlgebra
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter

/-!
# Native behaviour across initial natural representations

The comparison used here is the isomorphism derived from algebraic initiality.
Its agreement with the supplied numeral encoding is proved separately.
Finite queries execute on retained natural indices; the material or surreal
inverse is used only in the semantic observation, not as a runtime decoder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Representation

open Mettapedia.TypeTheory.NaturalAlgebra
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Reference.Core (Outcome)

universe u
variable {A : Type u} {algebra : Algebra A}
  (representation : Mettapedia.TypeTheory.NaturalAlgebra.Representation algebra)

/-- All supported modalities are preserved by the initiality-derived
comparison, including incoming boxes and nested fixed points. -/
theorem formula_iff {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true) (environment : Env A n) (number : Nat) :
    satisfies (transitionSystem (span algebra.succ)) environment formula
      (representation.encode number) ↔
    satisfies (transitionSystem (span Nat.succ))
      (pullEnvironment representation.encode environment) formula number := by
  have comparison := Semantics.SuccessorObservation.formula_iff Nat.succ algebra.succ
    representation.canonicalIso.toEquiv representation.canonicalIso.map_succ
    formula positive environment number
  have same : (fun n => representation.canonicalIso.toEquiv n) = representation.encode :=
    funext representation.canonicalIso_encode
  simpa only [same] using comparison

noncomputable def phase (value : A) : Fin 2 :=
  Counter.phase (representation.canonicalIso.toEquiv.symm value)

theorem phase_encode (number : Nat) :
    phase representation (representation.encode number) = Counter.phase number := by
  rw [← representation.canonicalIso_encode number]
  exact congrArg Counter.phase (representation.canonicalIso.toEquiv.symm_apply_apply number)

theorem phase_successor (value : A) :
    phase representation (algebra.succ value) = Counter.toggle (phase representation value) := by
  unfold phase
  exact (congrArg Counter.phase (representation.canonicalIso.symm.map_succ value)).trans
    (Counter.phase_successor _).symm

/-- The observation predicate keeps its explicit original numeral witness.
It does not assert an executable inverse for arbitrary represented values. -/
def accepted (accepting : Finset (Fin 2)) : Set A :=
  {value | ∃ number : Nat, representation.encode number = value ∧ Counter.phase number ∈ accepting}

theorem accepted_iff_phase (accepting : Finset (Fin 2)) (value : A) :
    value ∈ accepted representation accepting ↔ phase representation value ∈ accepting := by
  constructor
  · rintro ⟨number, rfl, member⟩
    rwa [phase_encode]
  · intro member
    obtain ⟨number, rfl⟩ := representation.bijective.2 value
    exact ⟨number, rfl, (phase_encode representation number) ▸ member⟩

/-- A finite public verdict on an original numeral is exactly the Büchi
property of the represented value under its actual successor operation. -/
theorem check_encoded_buchi_iff (accepting : Finset (Fin 2)) (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => accepting)
      budget (Counter.phase number)).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (span algebra.succ)) .future
      (accepted representation accepting) (representation.encode number) := by
  have exactCheck := Finite.check_buchi_iff Counter.table accepting budget (Counter.phase number) enough
  have transfer := Semantics.SuccessorObservation.buchi_iff algebra.succ Counter.toggle
    (phase representation) (phase_successor representation) (↑accepting : Set (Fin 2))
    (representation.encode number)
  have predicates : phase representation ⁻¹' (↑accepting : Set (Fin 2)) = accepted representation accepting := by
    ext value
    exact (accepted_iff_phase representation accepting value).symm
  rw [phase_encode, predicates] at transfer
  exact exactCheck.trans transfer

/-- A completed refutation has the same source-level meaning. -/
theorem check_encoded_negative_iff (accepting : Finset (Fin 2)) (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => accepting)
      budget (Counter.phase number)).map Outcome.answer = some (some false) ↔
    ¬ BuchiPath (transitionSystem (span algebra.succ)) .future
      (accepted representation accepting) (representation.encode number) := by
  refine (Finite.check_negative_iff Counter.table _ (Formula.buchi_positive _)
    (fun _ => accepting) budget (Counter.phase number) enough).trans ?_
  apply not_congr
  have paths := (satisfies_buchi_iff_path (transitionSystem Counter.parity) .future
    (↑accepting : Set (Fin 2)) (Counter.phase number))
  have transfer := Semantics.SuccessorObservation.buchi_iff algebra.succ Counter.toggle
    (phase representation) (phase_successor representation) (↑accepting : Set (Fin 2))
    (representation.encode number)
  have predicates : phase representation ⁻¹' (↑accepting : Set (Fin 2)) = accepted representation accepting := by
    ext value
    exact (accepted_iff_phase representation accepting value).symm
  rw [phase_encode, predicates] at transfer
  exact paths.trans transfer

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Representation
