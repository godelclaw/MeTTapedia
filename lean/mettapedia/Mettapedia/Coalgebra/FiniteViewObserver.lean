import Mettapedia.Coalgebra.StreamFinality
import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

/-!
# Observer-relative stream transformations and selection

Finite prefixes form coherent observers. Overwriting the first unseen position
preserves its finite observer but changes the complete tower. The same retained
pair of streams admits selection at that prefix and fails selection at identity:
selection is justified by the chosen observer fibre, not by erasing alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.FiniteViewObserver

open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uLabel

variable {Label : Type uLabel}

/-! ## The coherent observer tower -/

def finiteObserver (depth : Nat) :
    Observer (Stream Label) (Prefix Label depth) where
  observe := finiteView depth

def completeTowerObserver :
    Observer (Stream Label) ((depth : Nat) → Prefix Label depth) where
  observe := allPrefixes

theorem finiteObserver_not_injective
    (depth : Nat) {ordinary changed : Label}
    (different : ordinary ≠ changed) :
    ¬ Function.Injective
      (finiteObserver (Label := Label) depth).observe :=
  finiteView_not_injective depth different

theorem completeTowerObserver_injective :
    Function.Injective
      (completeTowerObserver (Label := Label)).observe :=
  allPrefixes_injective

/-- Earlier observation is exactly a postcomposition of every longer view. -/
theorem finiteObserver_postcompose
    {earlier later : Nat}
    (bounded : earlier ≤ later) :
    finiteObserver (Label := Label) earlier =
      (finiteObserver (Label := Label) later).postcompose
        (restrictPrefix bounded) := rfl

/-! ## A transformation lawful at one finite observer -/

/-- Replace the label at one selected position, retaining every other
position. -/
def overwriteAt
    (depth : Nat) (replacement : Label) (stream : Stream Label) :
    Stream Label :=
  fun index => if index = depth then replacement else stream index

/-- Replacing position `depth` cannot be seen by the prefix of length
`depth`. -/
def overwritePreservesFinite
    (depth : Nat) (replacement : Label) :
    ObserverPreservingMap (Stream Label) (Stream Label) (Prefix Label depth)
      (finiteObserver depth) (finiteObserver depth) where
  transform := overwriteAt depth replacement
  preserves := by
    intro stream
    funext index
    exact if_neg (Nat.ne_of_lt index.isLt)

/-- The same overwrite is visible to the complete tower whenever it changes
the selected label. -/
theorem overwrite_does_not_preserve_completeTower
    (depth : Nat) :
    ¬ ∀ stream : Stream Bool,
      (completeTowerObserver.observe
          (overwriteAt depth false stream)) =
        completeTowerObserver.observe stream := by
  intro alleged
  have towerEquality := alleged (constant true)
  have streamEquality :
      overwriteAt depth false (constant true) = constant true :=
    completeTowerObserver_injective towerEquality
  have atDepth := congrFun streamEquality depth
  simp [overwriteAt, constant] at atDepth

/-! ## Observer-indexed selection over retained worlds -/

/-- A complete two-world fibre: the worlds first differ exactly at `depth`. -/
def finitePairFamily (depth : Nat) :
    AlternativeFamily Unit (Stream Bool) where
  accepts := fun _ stream =>
    stream = constant false ∨
      stream = changedAt depth false true

theorem finitePairFamily_covered (depth : Nat) :
    (finitePairFamily depth).Covered := fun _ => ⟨constant false, Or.inl rfl⟩

theorem finitePairFamily_finite_invariant (depth : Nat) :
    (finitePairFamily depth).ObserverInvariant (finiteObserver depth) := by
  rintro _ _ _ (rfl | rfl) (rfl | rfl)
  · rfl
  · exact finiteView_constant_changedAt depth false true
  · exact (finiteView_constant_changedAt depth false true).symm
  · rfl

theorem finitePairFamily_not_identity_invariant (depth : Nat) :
    ¬ (finitePairFamily depth).ObserverInvariant
      (Observer.identity (Stream Bool)) := by
  intro invariant
  have equalStreams := invariant ()
    (first := constant false)
    (second := changedAt depth false true)
    (Or.inl rfl) (Or.inr rfl)
  exact constant_ne_changedAt depth Bool.false_ne_true equalStreams

/-- The retained pair admits representative selection for the finite observer.
The family itself is not deleted or identified. -/
theorem finitePairFamily_has_finite_resolution (depth : Nat) :
    Nonempty
      ((finitePairFamily depth).ObservationalResolution
        (finiteObserver depth)) :=
  ((AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
    (finitePairFamily depth) (finiteObserver depth))).2
      ⟨finitePairFamily_covered depth,
        finitePairFamily_finite_invariant depth⟩

/-- The same pair admits no exact representative at the identity observer. -/
theorem finitePairFamily_has_no_identity_resolution (depth : Nat) :
    ¬ Nonempty
      ((finitePairFamily depth).ObservationalResolution
        (Observer.identity (Stream Bool))) := by
  intro resolution
  have coveredAndInvariant :=
    (AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
      (finitePairFamily depth) (Observer.identity (Stream Bool))).1 resolution
  exact finitePairFamily_not_identity_invariant depth coveredAndInvariant.2

/-- Paired selection canary: one and the same retained alternative family is
selectable at its finite observation and unselectable at exact identity. -/
theorem finite_selection_is_observer_relative (depth : Nat) :
    Nonempty
        ((finitePairFamily depth).ObservationalResolution
          (finiteObserver depth)) ∧
      ¬ Nonempty
        ((finitePairFamily depth).ObservationalResolution
          (Observer.identity (Stream Bool))) :=
  ⟨finitePairFamily_has_finite_resolution depth,
    finitePairFamily_has_no_identity_resolution depth⟩

end Mettapedia.Coalgebra.FiniteViewObserver
