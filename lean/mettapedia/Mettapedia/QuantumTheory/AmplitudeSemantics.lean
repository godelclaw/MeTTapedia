import Mettapedia.Algebra.RationalComplexAmplitude
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.ModularLattice

/-!
# Coherent amplitudes, ordered actions, and intensity observations

Complex addition and multiplication are the chosen amplitude operations.
Squared norm is an observation of their results. Unit phases preserve this
observation, but coherent addition can distinguish equal-intensity states.
The ordered action language also applies to exact rational complex amplitudes;
its interpretation commutes with execution through the existing algebra map.
-/

namespace Mettapedia.QuantumTheory

/-- An authored occurrence of scaling or coherent addition. -/
inductive AmplitudeAction (A : Type*) where
  | scale (coefficient : A)
  | combine (amplitude : A)

namespace AmplitudeAction

def eval {A : Type*} [Mul A] [Add A] : AmplitudeAction A → A → A
  | .scale a, z => z * a
  | .combine a, z => z + a

def map {A B : Type*} (f : A → B) : AmplitudeAction A → AmplitudeAction B
  | .scale a => .scale (f a)
  | .combine a => .combine (f a)

end AmplitudeAction

def execute {A : Type*} [Mul A] [Add A] (events : List (AmplitudeAction A)) (initial : A) : A :=
  events.foldl (fun z event => event.eval z) initial

/-- Repeated states are retained as separate execution positions. -/
def trajectory {A : Type*} [Mul A] [Add A] (events : List (AmplitudeAction A)) (initial : A) :
    List A := events.scanl (fun z event => event.eval z) initial

theorem execute_append {A : Type*} [Mul A] [Add A]
    (xs ys : List (AmplitudeAction A)) (z : A) :
    execute (xs ++ ys) z = execute ys (execute xs z) := List.foldl_append

theorem trajectory_length {A : Type*} [Mul A] [Add A]
    (events : List (AmplitudeAction A)) (z : A) :
    (trajectory events z).length = events.length + 1 := by simp [trajectory]

theorem trajectory_endpoint {A : Type*} [Mul A] [Add A]
    (events : List (AmplitudeAction A)) (z : A) :
    (trajectory events z).getLast? = some (execute events z) := List.getLast?_scanl

/-- Representation change preserves the supplied actions and their exact endpoint. -/
theorem execute_hom {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (events : List (AmplitudeAction A)) (z : A) :
    f (execute events z) = execute (events.map (AmplitudeAction.map f)) (f z) := by
  induction events generalizing z with
  | nil => rfl
  | cons event events ih =>
      cases event with
      | scale a => simpa [execute, AmplitudeAction.eval, AmplitudeAction.map] using ih (z * a)
      | combine a => simpa [execute, AmplitudeAction.eval, AmplitudeAction.map] using ih (z + a)

/-- The same interpretation preserves all intermediate states, not only the endpoint. -/
theorem trajectory_hom {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (events : List (AmplitudeAction A)) (z : A) :
    (trajectory events z).map f = trajectory (events.map (AmplitudeAction.map f)) (f z) := by
  induction events generalizing z with
  | nil => rfl
  | cons event events ih =>
      cases event with
      | scale a =>
          simpa [trajectory, AmplitudeAction.eval, AmplitudeAction.map] using
            congrArg (List.cons (f z)) (ih (z * a))
      | combine a =>
          simpa [trajectory, AmplitudeAction.eval, AmplitudeAction.map] using
            congrArg (List.cons (f z)) (ih (z + a))

/-- Label each transition by its supplied action occurrence and resulting state. -/
def history {A : Type*} [Mul A] [Add A] (events : List (AmplitudeAction A)) (z : A) :
    List (AmplitudeAction A × A) := events.zip (trajectory events z).tail

theorem history_reproduces_actions {A : Type*} [Mul A] [Add A]
    (events : List (AmplitudeAction A)) (z : A) : (history events z).map Prod.fst = events := by
  unfold history
  apply List.map_fst_zip
  simp [trajectory]

theorem normSq_unit_phase (z : ℂ) (u : Circle) :
    Complex.normSq (z * u) = Complex.normSq z := by
  have hu : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  simp only [Complex.normSq_eq_norm_sq, norm_mul, hu, mul_one]

theorem phase_execution_preserves_intensity (phases : List Circle) (z : ℂ) :
    Complex.normSq (execute (phases.map (fun u => AmplitudeAction.scale (u : ℂ))) z) =
      Complex.normSq z := by
  induction phases generalizing z with
  | nil => rfl
  | cons phase phases ih =>
      simpa [execute, AmplitudeAction.eval] using (ih (z * phase)).trans (normSq_unit_phase z phase)

open Mettapedia.Algebra.RationalComplexAmplitude

/-- Exact rational execution has the same squared-norm readout after complex interpretation. -/
theorem rational_execution_readout (events : List (AmplitudeAction Amplitude)) (z : Amplitude) :
    (born (execute events z) : ℝ) =
      Complex.normSq (execute (events.map (AmplitudeAction.map intoComplex)) (intoComplex z)) := by
  rw [born_agrees_complex]
  exact congrArg Complex.normSq (execute_hom intoComplex.toRingHom events z)

/-- Equal intensity is not a congruence for coherent addition. -/
theorem equal_intensity_distinguished_by_addition :
    Complex.normSq (1 : ℂ) = Complex.normSq (-1) ∧
      Complex.normSq ((1 : ℂ) + 1) ≠ Complex.normSq ((-1 : ℂ) + 1) := by
  norm_num [Complex.normSq_apply]

theorem ordered_phase_addition_distinct :
    execute [.combine 1, .scale (-1)] (1 : ℂ) = -2 ∧
      execute [.scale (-1), .combine 1] (1 : ℂ) = 0 := by
  norm_num [execute, AmplitudeAction.eval]

/-- Two identity phase occurrences still contribute two execution positions. -/
theorem identity_phase_occurrences_retained :
    trajectory [.scale 1, .scale 1] (1 : ℂ) = [1, 1, 1] := by
  simp [trajectory, AmplitudeAction.eval]

/-- Disjoint nonempty events occur in an ordinary distributive Boolean algebra. -/
theorem classical_disjoint_nonempty_events :
    ∃ a b : Set Bool, a ≠ ⊥ ∧ b ≠ ⊥ ∧ Disjoint a b := by
  refine ⟨{true}, {false}, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

end Mettapedia.QuantumTheory
