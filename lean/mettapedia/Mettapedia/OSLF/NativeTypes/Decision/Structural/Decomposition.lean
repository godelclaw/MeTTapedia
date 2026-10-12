import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Ordered constructor checking from primitive decompositions

The independently specified image quantifies over typed constructor values.
The executable checker inspects only values returned by the local backend and
tests their ordered arguments. Source and argument equations are separate;
coverage must preserve every argument class before a negative result is valid.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition

open Mettapedia.GSLT
open GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

universe u v

/-- A total executable primitive predicate with its own equation-invariant
meaning. This interface contains no constructor-output comparison. -/
structure BooleanPredicate {Term : Type u} (equations : Setoid Term) where
  meaning : Term → Prop
  invariant : ∀ {first second}, equations.r first second → (meaning first ↔ meaning second)
  accepts : Term → Bool
  exact : ∀ term, accepts term = true ↔ meaning term

structure Backend {Term : Type u} (Value : Type v) (arity : Nat)
    (image : Value → Term) (argument : Value → Fin arity → Term)
    (sourceEquations : Setoid Term) (inputEquations : Fin arity → Setoid Term)
    (admitted : Term → Prop) where
  values : Nat → Term → List Value
  closed : Nat → Term → Bool
  sound : ∀ budget source value, value ∈ values budget source →
    sourceEquations.r source (image value)
  ordered_coverage : ∀ budget source, closed budget source = true →
    ∀ value, sourceEquations.r source (image value) →
      ∃ candidate, candidate ∈ values budget source ∧
        ∀ position, (inputEquations position).r (argument value position) (argument candidate position)
  completionBudget : Term → Nat
  complete_at : ∀ source, admitted source → closed (completionBudget source) source = true
  values_stable : ∀ source budget, completionBudget source ≤ budget →
    values budget source = values (completionBudget source) source
  closed_stable : ∀ source budget, completionBudget source ≤ budget →
    closed budget source = closed (completionBudget source) source

def imagePredicate {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    (image : Value → system.Term) (argument : Value → Fin arity → system.Term)
    (inputEquations : Fin arity → Setoid system.Term)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position)) : EquationPredicate system where
  val source := output.meaning source ∧
    ∃ value, system.Equiv source (image value) ∧ ∀ position, (inputs position).meaning (argument value position)
  property := by
    intro first second related
    constructor
    · rintro ⟨sorted, value, represents, arguments⟩
      exact ⟨(output.invariant related).mp sorted, value,
        system.equations.iseqv.trans (system.equations.iseqv.symm related) represents, arguments⟩
    · rintro ⟨sorted, value, represents, arguments⟩
      exact ⟨(output.invariant related).mpr sorted, value,
        system.equations.iseqv.trans related represents, arguments⟩

def acceptsArguments {Term : Type u} {Value : Type v} {arity : Nat}
    (argument : Value → Fin arity → Term) (inputEquations : Fin arity → Setoid Term)
    (inputs : ∀ position, BooleanPredicate (inputEquations position)) (value : Value) : Bool :=
  (List.finRange arity).all (fun position => (inputs position).accepts (argument value position))

theorem acceptsArguments_exact {Term : Type u} {Value : Type v} {arity : Nat}
    (argument : Value → Fin arity → Term) (inputEquations : Fin arity → Setoid Term)
    (inputs : ∀ position, BooleanPredicate (inputEquations position)) (value : Value) :
    acceptsArguments argument inputEquations inputs value = true ↔
      ∀ position, (inputs position).meaning (argument value position) := by
  simp only [acceptsArguments, List.all_eq_true]
  constructor
  · intro all position
    exact (inputs position).exact _ |>.mp (all position (List.mem_finRange position))
  · intro all position _
    exact (inputs position).exact _ |>.mpr (all position)

def evaluate {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    {image : Value → system.Term} {argument : Value → Fin arity → system.Term}
    {inputEquations : Fin arity → Setoid system.Term} {admitted : system.Term → Prop}
    (backend : Backend Value arity image argument system.equations inputEquations admitted)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position))
    (budget : Nat) (source : system.Term) : Option Bool :=
  if output.accepts source = false then some false
  else if (backend.values budget source).any (acceptsArguments argument inputEquations inputs) then some true
  else if backend.closed budget source then some false else none

theorem evaluate_positive {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    {image : Value → system.Term} {argument : Value → Fin arity → system.Term}
    {inputEquations : Fin arity → Setoid system.Term} {admitted : system.Term → Prop}
    (backend : Backend Value arity image argument system.equations inputEquations admitted)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position))
    (budget : Nat) (source : system.Term)
    (read : evaluate backend output inputs budget source = some true) :
    imagePredicate image argument inputEquations output inputs source := by
  unfold evaluate at read
  split at read
  · contradiction
  · rename_i sorted
    have outputHolds : output.meaning source := (output.exact source).mp (by cases h : output.accepts source <;> simp_all)
    split at read
    · rename_i accepted
      obtain ⟨value, listed, arguments⟩ := List.any_eq_true.mp accepted
      exact ⟨outputHolds, value, backend.sound budget source value listed,
        (acceptsArguments_exact argument inputEquations inputs value).mp arguments⟩
    · split at read <;> contradiction

theorem evaluate_negative {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    {image : Value → system.Term} {argument : Value → Fin arity → system.Term}
    {inputEquations : Fin arity → Setoid system.Term} {admitted : system.Term → Prop}
    (backend : Backend Value arity image argument system.equations inputEquations admitted)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position))
    (budget : Nat) (source : system.Term)
    (read : evaluate backend output inputs budget source = some false) :
    ¬ imagePredicate image argument inputEquations output inputs source := by
  intro holds
  obtain ⟨outputHolds, value, represents, arguments⟩ := holds
  have outputAccepted := (output.exact source).mpr outputHolds
  unfold evaluate at read
  simp only [outputAccepted, Bool.true_eq_false, ↓reduceIte] at read
  split at read
  · contradiction
  · rename_i noneAccepted
    split at read
    · rename_i closed
      obtain ⟨candidate, listed, related⟩ := backend.ordered_coverage budget source closed value represents
      have candidateAccepted : acceptsArguments argument inputEquations inputs candidate = true := by
        apply (acceptsArguments_exact argument inputEquations inputs candidate).mpr
        intro position
        exact ((inputs position).invariant (related position)).mp (arguments position)
      exact noneAccepted (List.any_eq_true.mpr ⟨candidate, listed, candidateAccepted⟩)
    · contradiction

theorem evaluate_complete {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    {image : Value → system.Term} {argument : Value → Fin arity → system.Term}
    {inputEquations : Fin arity → Setoid system.Term} {admitted : system.Term → Prop}
    (backend : Backend Value arity image argument system.equations inputEquations admitted)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position))
    (source : system.Term) (sourceAdmitted : admitted source) :
    ∃ answer, evaluate backend output inputs (backend.completionBudget source) source = some answer := by
  have closed := backend.complete_at source sourceAdmitted
  unfold evaluate
  split
  · exact ⟨false, rfl⟩
  · split
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩

def test {system : GSLT.{u}} {Value : Type v} {arity : Nat}
    {image : Value → system.Term} {argument : Value → Fin arity → system.Term}
    {inputEquations : Fin arity → Setoid system.Term} {admitted : system.Term → Prop}
    (backend : Backend Value arity image argument system.equations inputEquations admitted)
    (output : BooleanPredicate system.equations)
    (inputs : ∀ position, BooleanPredicate (inputEquations position)) : Test system admitted where
  predicate := imagePredicate image argument inputEquations output inputs
  evaluate := evaluate backend output inputs
  positive := evaluate_positive backend output inputs
  negative := evaluate_negative backend output inputs
  completionBudget := backend.completionBudget
  complete_at := evaluate_complete backend output inputs
  complete_above source sourceAdmitted budget enough := by
    rw [evaluate, backend.values_stable source budget enough, backend.closed_stable source budget enough]
    exact evaluate_complete backend output inputs source sourceAdmitted

end Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition
