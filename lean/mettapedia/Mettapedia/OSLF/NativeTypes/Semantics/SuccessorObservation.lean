import Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
import Mathlib.Logic.Function.Iterate

/-!
# Behavioural observation of successor algebras

A map commuting with successor gives complete outgoing observation of the
deterministic successor system. An equivalence additionally covers incoming
steps, and therefore transports every supported modal fixed-point formula.
Neither conclusion asserts initiality of the underlying successor algebra.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open ModalFormula

universe u v
variable {A : Type u} {B : Type v}

def span (successor : A → A) : ReductionSpan A where
  Edge := A
  source := id
  target := successor

/-- The deterministic run is fixed by its initial state and successor law.
This is a uniqueness theorem for runs, separate from algebraic initiality. -/
theorem path_eq_iterate (next : A → A) (initial : A) (path : Nat → A)
    (starts : path 0 = initial) (steps : ∀ index, path (index + 1) = next (path index))
    (index : Nat) : path index = next^[index] initial := by
  induction index with
  | zero => exact starts
  | succ index ih =>
    exact (steps index).trans ((congrArg next ih).trans
      (Function.iterate_succ_apply' next index initial).symm)

/-- In a deterministic successor system Büchi acceptance is recurrence
along its unique iterate sequence, without a stream-finality assumption. -/
theorem buchi_iff_iterates (next : A → A) (accepting : Set A) (initial : A) :
    BuchiPath (transitionSystem (span next)) .future accepting initial ↔
      ∀ lower : Nat, ∃ visit : Nat, lower ≤ visit ∧ next^[visit] initial ∈ accepting := by
  constructor
  · rintro ⟨path, starts, steps, recurring⟩
    have equations (index : Nat) : path (index + 1) = next (path index) := by
      obtain ⟨event, source, target⟩ := steps index
      change event = path index at source
      change next event = path (index + 1) at target
      exact target.symm.trans (congrArg next source)
    intro lower
    obtain ⟨visit, after, accepted⟩ := recurring lower
    exact ⟨visit, after, (path_eq_iterate next initial path starts equations visit) ▸ accepted⟩
  · intro recurring
    refine ⟨fun index => next^[index] initial, rfl, ?_, recurring⟩
    intro index
    exact ⟨next^[index] initial, rfl, (Function.iterate_succ_apply' next index initial).symm⟩

def observation (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value)) :
    SpanMap (span first) (span second) where
  states := encode
  events := encode
  source_comm _ := rfl
  target_comm value := (commutes value).symm

theorem source_lifts (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value)) :
    (observation first second encode commutes).SourceLifts := by
  intro value event starts
  change event = encode value at starts
  exact ⟨value, rfl, (commutes value).trans (congrArg second starts.symm)⟩

theorem target_lifts (first : A → A) (second : B → B) (encode : A ≃ B)
    (commutes : ∀ value, encode (first value) = second (encode value)) :
    (observation first second encode commutes).TargetLifts := by
  intro value event ends
  change second event = encode value at ends
  refine ⟨encode.symm event, ?_, encode.apply_symm_apply event⟩
  apply encode.injective
  change encode (first (encode.symm event)) = encode value
  exact (commutes (encode.symm event)).trans
    ((congrArg second (encode.apply_symm_apply event)).trans ends)

theorem covers_formula (first : A → A) (second : B → B) (encode : A ≃ B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    {n : Nat} (formula : Formula Traversal n) :
    CoversFormula (observation first second encode commutes) formula := by
  induction formula with
  | tt | ff | var _ => trivial
  | neg _ ih | mu _ ih | nu _ ih => exact ih
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | diamond direction _ ih | box direction _ ih =>
    refine ⟨?_, ih⟩
    cases direction
    · exact source_lifts first second encode commutes
    · exact target_lifts first second encode commutes

/-- Both temporal directions and nested fixed points survive a successor
representation equivalence, with the observation predicates translated. -/
theorem formula_iff (first : A → A) (second : B → B) (encode : A ≃ B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true) (environment : Env B n) (value : A) :
    satisfies (transitionSystem (span second)) environment formula (encode value) ↔
      satisfies (transitionSystem (span first)) (pullEnvironment encode environment) formula value :=
  satisfies_pullback (observation first second encode commutes) formula
    (covers_formula first second encode commutes formula) positive environment value

/-- Future recurrence can also pass through a noninjective observation.
This theorem does not transfer predicates that distinguish its fibres. -/
theorem buchi_iff (first : A → A) (second : B → B) (encode : A → B)
    (commutes : ∀ value, encode (first value) = second (encode value))
    (accepting : Set B) (value : A) :
    BuchiPath (transitionSystem (span second)) .future accepting (encode value) ↔
      BuchiPath (transitionSystem (span first)) .future (encode ⁻¹' accepting) value :=
  BuchiTransport.path_pullback (observation first second encode commutes)
    (source_lifts first second encode commutes) accepting value

end Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
