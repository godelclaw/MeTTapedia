import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Checking a finite family of proposed computation equations

Every equation carries syntax for its telescope, endpoints and displayed type.
The existing executable equality checker checks every row. In particular, a
compiler's proposed recursor and its source equations need separate checks:
typing the recursor alone does not establish the equations.

Acceptance derives typed equality for every row, every typed simultaneous
instance, and context extensions. Failure is absence of a certificate within
this search budget, not a proof that the equation is false. The budget here is
the existing recursive checker's fuel per row; a native shared work allowance
is an independent implementation contract.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.EquationAdmission

variable {Head : Type}

structure Equation (Head : Type) where
  arity : Nat
  context : Ctx Head arity
  left : Tm Head arity
  right : Tm Head arity
  type : Tm Head arity

variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
  (heads : ExecutableChecking.HeadChoices R) (reducer : ExecutableReduction.Reducer R)

def check (fuel : Nat) (equations : List (Equation Head)) : Bool :=
  equations.all fun equation =>
    (ExecutableChecking.equality R heads reducer fuel equation.context
      equation.left equation.right equation.type).isSome

theorem check_append (fuel : Nat) (first second : List (Equation Head)) :
    check R heads reducer fuel (first ++ second) =
      (check R heads reducer fuel first && check R heads reducer fuel second) := by
  simp [check]

/-- A successful batch contains actual checker-produced certificates for its
original rows, preserving their contexts and endpoints. -/
theorem certificate {fuel : Nat} {equations : List (Equation Head)}
    (accepted : check R heads reducer fuel equations = true)
    {equation : Equation Head} (member : equation ∈ equations) :
    ∃ result, ExecutableChecking.equality R heads reducer fuel equation.context
      equation.left equation.right equation.type = some result := by
  exact Option.isSome_iff_exists.mp (List.all_eq_true.mp accepted equation member)

section Soundness

open UniverseLevel (LevelOrder)

variable {L : Type} [LevelOrder L] {S : Setting Head L}
  [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R)
  (evaluator : ExecutableReduction.Reducer S.R)

include facts roots headSteps algebra declared

theorem sound {fuel : Nat} {equations : List (Equation Head)}
    (accepted : check S.R choices evaluator fuel equations = true)
    {equation : Equation Head} (member : equation ∈ equations) :
    Typed S.R equation.context equation.left equation.type ∧
      Typed S.R equation.context equation.right equation.type ∧
      Equal S.R equation.context equation.left equation.right equation.type := by
  obtain ⟨result, _⟩ := certificate S.R choices evaluator accepted member
  exact ⟨result.firstChecked.sound facts roots headSteps algebra declared,
    result.secondChecked.sound facts roots headSteps algebra declared,
    result.sound facts roots headSteps algebra declared⟩

theorem instance_sound {fuel m : Nat} {equations : List (Equation Head)}
    (accepted : check S.R choices evaluator fuel equations = true)
    {equation : Equation Head} (member : equation ∈ equations)
    {target : Ctx Head m} {substitution : Sub Head equation.arity m}
    (arguments : SubstMor S.R equation.context target substitution) :
    Typed S.R target (subst substitution equation.left) (subst substitution equation.type) ∧
      Typed S.R target (subst substitution equation.right) (subst substitution equation.type) ∧
      Equal S.R target (subst substitution equation.left) (subst substitution equation.right)
        (subst substitution equation.type) := by
  obtain ⟨left, right, equal⟩ := sound facts roots headSteps algebra declared choices evaluator
    accepted member
  exact ⟨left.substitute arguments, right.substitute arguments, equal.substitute arguments⟩

theorem context_extension {fuel : Nat} {equations : List (Equation Head)}
    (accepted : check S.R choices evaluator fuel equations = true)
    {equation : Equation Head} (member : equation ∈ equations)
    (extension : Tm Head equation.arity) :
    Equal S.R (.snoc equation.context extension)
      (rename wk equation.left) (rename wk equation.right) (rename wk equation.type) :=
  (sound facts roots headSteps algebra declared choices evaluator accepted member).2.2.weaken

theorem refuses_unequal_member {fuel : Nat} {equations : List (Equation Head)}
    {equation : Equation Head} (member : equation ∈ equations)
    (unequal : ¬ Equal S.R equation.context equation.left equation.right equation.type) :
    check S.R choices evaluator fuel equations ≠ true := by
  intro accepted
  exact unequal (sound facts roots headSteps algebra declared choices evaluator accepted member).2.2

end Soundness
end TypedEquality.Normalization.EquationAdmission
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
