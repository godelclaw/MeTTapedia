import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mathlib.Data.Finset.Basic

/-!
# The MM0 witness interface and its binding guards

This observer records operations requested at a node of the original proof or
conversion witness. Child nodes are observed separately. It includes the
actual simultaneous substitution and dependency checks: MM0 is not a checker
which only compares strings. Definition admission and whole-file authority
remain separate interfaces.

The least inventory below is relative to this observer. It is not semantic
irredundancy, an implementation lower bound, or a linear-time theorem. The
controls establish a stronger concrete fact about one guard: typing does not
imply independence, and omitting independence admits a forbidden binding
substitution in the original checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.CheckingDiscipline

open Kernel

inductive Operation where
  | lookup | syntaxComparison | sortChecking | substitution
  | dependencyChecking | dummyFreshness | explicitConversion
  | implicitNormalization
deriving DecidableEq, Repr

abbrev Request := Sum ProofWitness ConvWitness
abbrev Basis := Finset Operation

def operations : Request → Basis
  | .inl (.hyp _) => {.lookup}
  | .inl (.theoremApp _ _ _) =>
      {.lookup, .syntaxComparison, .sortChecking, .substitution, .dependencyChecking}
  | .inl (.conversion _ _) => {.syntaxComparison, .explicitConversion}
  | .inr (.refl _) => {.sortChecking}
  | .inr (.symm _) => {.explicitConversion}
  | .inr (.trans _ _) => {.syntaxComparison, .sortChecking, .explicitConversion}
  | .inr (.congruence _ _) => {.lookup, .sortChecking, .explicitConversion}
  | .inr (.unfold _ _ _) =>
      {.lookup, .sortChecking, .substitution, .dependencyChecking, .dummyFreshness}

def Covers (basis : Basis) : Prop := ∀ request, operations request ⊆ basis

def requiredBasis : Basis :=
  {.lookup, .syntaxComparison, .sortChecking, .substitution,
    .dependencyChecking, .dummyFreshness, .explicitConversion}

theorem required_basis_covers : Covers requiredBasis := by
  intro request
  rcases request with proof | conversion
  · cases proof <;> simp only [operations] <;> decide
  · cases conversion <;> simp only [operations] <;> decide

theorem covers_iff_contains_required (basis : Basis) :
    Covers basis ↔ requiredBasis ⊆ basis := by
  constructor
  · intro covers operation member
    have app := covers (.inl (.theoremApp 0 [] []))
    have conversion := covers (.inl (.conversion (.refl (.var 0)) (.hyp 0)))
    have unfold := covers (.inr (.unfold 0 [] []))
    cases operation <;> simp_all [requiredBasis, operations, Finset.subset_iff]
  · intro included request
    exact (required_basis_covers request).trans included

theorem no_implicit_normalization (request : Request) :
    Operation.implicitNormalization ∉ operations request := by
  rcases request with proof | conversion
  · cases proof <;> simp [operations]
  · cases conversion <;> simp [operations]

theorem substitution_required (basis : Basis) (covered : Covers basis) :
    Operation.substitution ∈ basis :=
  covered (.inl (.theoremApp 0 [] [])) (by simp [operations])

/-- The observer restricts admission, but leaves the original checker and its
independently defined witness semantics intact. -/
theorem admitted_check_exact (basis : Basis) (signature : TermSignature)
    (definitions : Definition.Signature) (theorems : TheoremSignature)
    (context : Context) (hypotheses : List Preterm) (proof : ProofWitness)
    (claim : Preterm) :
    (operations (.inl proof) ⊆ basis ∧
      ProofWitness.check signature definitions theorems context hypotheses proof claim = true) ↔
    (operations (.inl proof) ⊆ basis ∧
      ProofWitness.Checks signature definitions theorems context hypotheses proof claim) := by
  rw [ProofWitness.check_iff]

namespace Controls

def signature : TermSignature := fun _ => none
def twoBound : Context := [.bound 0, .bound 0]
def separated : List Preterm := [.var 0, .var 1]
def coincident : List Preterm := [.var 0, .var 0]

theorem independent_images_accept :
    Substitution.checkAdmissible signature twoBound twoBound separated = true := by decide +kernel

theorem typing_does_not_imply_independence :
    Substitution.checkArguments signature twoBound coincident twoBound = true ∧
    Substitution.checkAdmissible signature twoBound twoBound coincident = false := by decide +kernel

theorem dependency_guard_not_redundant :
    ¬ (∀ expressions,
      Substitution.checkArguments signature twoBound expressions twoBound = true →
      Substitution.Admissible signature twoBound twoBound expressions) := by
  intro redundant
  have admitted := redundant coincident typing_does_not_imply_independence.1
  have checked := (Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
  rw [typing_does_not_imply_independence.2] at checked
  cases checked

theorem exact_arity_required :
    Substitution.checkAdmissible signature twoBound twoBound [.var 0] = false := by decide +kernel

theorem bound_slot_requires_a_variable :
    Substitution.checkAdmissible signature twoBound twoBound [.term 0, .var 1] = false := by decide +kernel

/-- Even an unused result does not authorize a forbidden substitution. -/
theorem unused_argument_still_checked :
    Substitution.instantiate signature twoBound twoBound coincident (.var 0) = none ∧
    Preterm.substitute (Substitution.ofList coincident) (.var 0) = some (.var 0) := by decide +kernel

end Controls

end Mettapedia.Languages.MM0.CheckingDiscipline
