import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fin.VecNotation
import Mettapedia.UniversalAlgebra.EquationalLogic

/-!
# The monoid equation system and its Mathlib models
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.Logic
open Mettapedia.UniversalAlgebra

inductive Operation : Type where
  | mul
  | one
deriving DecidableEq, Repr

def signature : Signature.{0} where
  Operation := Operation
  arity
    | .mul => 2
    | .one => 0

instance signatureOperationDecidableEq : DecidableEq signature.Operation :=
  inferInstanceAs (DecidableEq Operation)

/-- Binary multiplication in the monoid term language. -/
def mul (left right : Term signature) : Term signature :=
  .op .mul (fun i => if i.val = 0 then left else right)

/-- The unit in the monoid term language. -/
def one : Term signature :=
  .op .one (fun i => absurd i.isLt (by simp [signature]))

def x : Term signature := .var 0
def y : Term signature := .var 1
def z : Term signature := .var 2

/-- Associativity, left unit, and right unit. -/
def equationSystem : EquationSystem signature where
  equations :=
    [ (mul (mul x y) z, mul x (mul y z))
    , (mul one x, x)
    , (mul x one, x) ]

/-- The monoid system extended by commutativity. -/
def commutativeEquationSystem : EquationSystem signature where
  equations := equationSystem.equations ++ [(mul x y, mul y x)]

/-- Every Mathlib monoid interprets the monoid signature. -/
def mathlibModel (Carrier : Type) [Monoid Carrier] : Model signature Carrier where
  interpret
    | .mul => fun arguments =>
        arguments ⟨0, by decide⟩ * arguments ⟨1, by decide⟩
    | .one => fun _ => 1

@[simp] theorem evaluate_mul {Carrier : Type} [Monoid Carrier]
    (valuation : Nat → Carrier) (left right : Term signature) :
    (mul left right).evaluate (mathlibModel Carrier) valuation =
      left.evaluate (mathlibModel Carrier) valuation *
        right.evaluate (mathlibModel Carrier) valuation := rfl

@[simp] theorem evaluate_one {Carrier : Type} [Monoid Carrier]
    (valuation : Nat → Carrier) :
    one.evaluate (mathlibModel Carrier) valuation = 1 := rfl

@[simp] theorem evaluate_var {Carrier : Type} [Monoid Carrier]
    (valuation : Nat → Carrier) (index : Nat) :
    (Term.var index : Term signature).evaluate
      (mathlibModel Carrier) valuation = valuation index := rfl

theorem subst_mul (substitution : Nat → Term signature)
    (left right : Term signature) :
    (mul left right).subst substitution =
      mul (left.subst substitution) (right.subst substitution) := by
  unfold mul
  show Term.op _ _ = Term.op _ _
  congr 1
  funext i
  by_cases h : i.val = 0 <;> simp [h]

theorem subst_one (substitution : Nat → Term signature) :
    one.subst substitution = one := by
  unfold one
  show Term.op _ _ = Term.op _ _
  congr 1
  funext i
  exact absurd i.isLt (by simp [signature])

theorem mathlibModel_satisfies (Carrier : Type) [Monoid Carrier] :
    (mathlibModel Carrier).Satisfies equationSystem := by
  intro equation member
  change equation ∈ equationSystem.equations at member
  simp only [equationSystem, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro valuation
    simp only [evaluate_mul]
    exact mul_assoc _ _ _
  · intro valuation
    simp only [evaluate_mul, evaluate_one]
    exact one_mul _
  · intro valuation
    simp only [evaluate_mul, evaluate_one]
    exact mul_one _

/-- One generated consequence holds in every Mathlib monoid. -/
theorem consequence_holds_in_monoid {left right : Term signature}
    (derivation : EquationalConsequence equationSystem (left, right))
    (Carrier : Type) [Monoid Carrier] (valuation : Nat → Carrier) :
    left.evaluate (mathlibModel Carrier) valuation =
      right.evaluate (mathlibModel Carrier) valuation :=
  equationalConsequence_sound derivation Carrier (mathlibModel Carrier)
    (mathlibModel_satisfies Carrier) valuation

/-- An equation-system occurrence instantiated at a simultaneous
substitution is an equational consequence. -/
private theorem systemInstance
    {equation : Equation signature}
    (member : equation ∈ equationSystem)
    (substitution : Nat → Term signature) :
    EquationalConsequence equationSystem
      (equation.1.subst substitution, equation.2.subst substitution) :=
  (EquationalConsequence.of_mem member).subst substitution

theorem leftUnit (term : Term signature) :
    EquationalConsequence equationSystem (mul one term, term) := by
  simpa [subst_mul, subst_one, x] using systemInstance
    (show (mul one x, x) ∈ equationSystem from by
      change _ ∈ equationSystem.equations; simp [equationSystem]) (fun _ => term)

theorem rightUnit (term : Term signature) :
    EquationalConsequence equationSystem (mul term one, term) := by
  simpa [subst_mul, subst_one, x] using systemInstance
    (show (mul x one, x) ∈ equationSystem from by
      change _ ∈ equationSystem.equations; simp [equationSystem]) (fun _ => term)

theorem associativity (first second third : Term signature) :
    EquationalConsequence equationSystem
      (mul (mul first second) third, mul first (mul second third)) := by
  have instantiated := systemInstance
    (equation := (mul (mul x y) z, mul x (mul y z)))
    (by
      change (mul (mul x y) z, mul x (mul y z)) ∈ equationSystem.equations
      simp [equationSystem])
    (fun index =>
      if index = 0 then first else if index = 1 then second else third)
  simpa [subst_mul, x, y, z] using instantiated

/-- Multiplication is congruent in both arguments. -/
theorem mulCongr {left left' right right' : Term signature}
    (leftConversion :
      EquationalConsequence equationSystem (left, left'))
    (rightConversion :
      EquationalConsequence equationSystem (right, right')) :
    EquationalConsequence equationSystem
      (mul left right, mul left' right') := by
  apply EquationalConsequence.operation (system := equationSystem) Operation.mul
  intro position
  split_ifs <;> assumption

/-- Positive control: `(1 * x) * 1 = x` is generated by the monoid equations. -/
theorem one_mul_mul_one :
    EquationalConsequence equationSystem (mul (mul one x) one, x) :=
  (rightUnit (mul one x)).trans (leftUnit x)

example (Carrier : Type) [Monoid Carrier] (element : Carrier) :
    (1 * element) * 1 = element := by
  have result := consequence_holds_in_monoid one_mul_mul_one Carrier (fun _ => element)
  change (1 * element) * 1 = element at result
  exact result

/-- Negative control: two distinct variables are not a monoid consequence. -/
theorem distinct_variables_not_consequence :
    ¬ EquationalConsequence equationSystem
      ((Term.var 0 : Term signature), Term.var 1) := by
  intro derivation
  have result := consequence_holds_in_monoid derivation (FreeMonoid Unit)
    (fun index => if index = 0 then FreeMonoid.ofList []
      else FreeMonoid.ofList [()])
  simp at result

/-- Every monoid consequence remains a consequence after adding commutativity. -/
theorem consequence_lifts_to_commutative {equation : Equation signature}
    (derivation : EquationalConsequence equationSystem equation) :
    EquationalConsequence commutativeEquationSystem equation :=
  EquationalConsequence.mono
    (fun _ member => List.mem_append_left _ member) derivation


end Mettapedia.UniversalAlgebra.Monoid
