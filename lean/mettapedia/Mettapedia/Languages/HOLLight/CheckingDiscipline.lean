import Mettapedia.Languages.HOLLight.Rules
import Mathlib.Data.Finset.Basic

/-!
# A basis-relative view of the original HOL Light inference interface

The observation here is the rule-level computation requested by the original
ten-way dispatcher. It is not a machine instruction trace or an optimal
implementation footprint. In particular, `betaAdmission` names the explicit
source BETA rule, not an implicit normalization or conversion search.

A primitive basis is supplied explicitly. Thus a strict basis may exclude
HOL's substitution or beta-admission operations without implying a separation
in polynomial certificate size or checking time. Resource classification
requires separate executed-machine results.

Axioms and declaration-history extensions are not among these ten inference
operations and are not classified by this module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CheckingDiscipline

open Mettapedia.Languages.OpenTheory

inductive Operation where
  | syntaxComparison
  | hypothesisOperations
  | scopeAdmission
  | termSubstitution
  | typeSubstitution
  | betaAdmission
  | implicitNormalization
deriving DecidableEq, Repr

/-- Rule-level operations exposed by the existing source dispatcher. This
view does not prescribe the internal implementation of these operations. -/
def operations : InferenceKind → Finset Operation
  | .refl | .assume => { .syntaxComparison }
  | .trans | .mkComb | .eqMp | .deductAntisym =>
      { .syntaxComparison, .hypothesisOperations }
  | .abs => { .syntaxComparison, .hypothesisOperations, .scopeAdmission }
  | .beta => { .syntaxComparison, .betaAdmission }
  | .instType => { .syntaxComparison, .typeSubstitution }
  | .inst => { .syntaxComparison, .scopeAdmission, .termSubstitution, .typeSubstitution }

/-- All ten source inference operations, with no axiom or definition rule. -/
def inferenceKinds : List InferenceKind :=
  [.refl, .trans, .mkComb, .abs, .beta, .assume, .eqMp, .deductAntisym, .instType, .inst]

theorem kinds_complete (kind : InferenceKind) : kind ∈ inferenceKinds := by
  cases kind <;> simp [inferenceKinds]

abbrev Basis := Finset Operation

def Admitted (basis : Basis) (kind : InferenceKind) : Prop :=
  operations kind ⊆ basis

def Covers (basis : Basis) : Prop := ∀ kind, Admitted basis kind

theorem admitted_mono {small large : Basis} (included : small ⊆ large)
    {kind : InferenceKind} (admitted : Admitted small kind) : Admitted large kind :=
  fun _ used => included (admitted used)

theorem covers_mono {small large : Basis} (included : small ⊆ large)
    (covered : Covers small) : Covers large :=
  fun kind => admitted_mono included (covered kind)

/-- The explicit BETA rule is present in the actual source inference family. -/
theorem beta_uses_beta_admission : Operation.betaAdmission ∈ operations .beta := by
  simp [operations]

theorem inst_uses_term_substitution : Operation.termSubstitution ∈ operations .inst := by
  simp [operations]

theorem inst_type_uses_type_substitution :
    Operation.typeSubstitution ∈ operations .instType := by simp [operations]

/-- This dispatcher exposes no implicit normalization request. This says
nothing about an arbitrary HOL tactic or a different HOL kernel. -/
theorem no_implicit_normalization (kind : InferenceKind) :
    Operation.implicitNormalization ∉ operations kind := by
  cases kind <;> simp [operations]

/-- A strict replay basis excluding beta admission does not cover this
interface. The supplied basis is part of the theorem's statement. -/
theorem not_covers_without_beta {basis : Basis}
    (excluded : Operation.betaAdmission ∉ basis) : ¬ Covers basis := by
  intro covered
  exact excluded (covered .beta beta_uses_beta_admission)

theorem not_covers_without_substitution {basis : Basis}
    (excluded : Operation.termSubstitution ∉ basis) : ¬ Covers basis := by
  intro covered
  exact excluded (covered .inst inst_uses_term_substitution)

/-- The profile preserves the original requests and checker. It does not
replace its admission guards or its independent rule semantics. -/
theorem admitted_request_exact (basis : Basis) (request : InferenceRequest)
    (out : Theorem) :
    (Admitted basis request.kind ∧ request.check = some out) ↔
      (Admitted basis request.kind ∧ request.Semantics out) := by
  rw [InferenceRequest.check_eq_some_iff]

/-- The least operation basis for this fixed rule-level observation. This is
not a universal least proof system or an ISA-independent lower bound. -/
def requiredBasis : Basis :=
  { .syntaxComparison, .hypothesisOperations, .scopeAdmission,
    .termSubstitution, .typeSubstitution, .betaAdmission }

theorem required_basis_covers : Covers requiredBasis := by
  intro kind
  unfold Admitted
  cases kind <;> decide

theorem covers_iff_contains_required (basis : Basis) :
    Covers basis ↔ requiredBasis ⊆ basis := by
  constructor
  · intro covered operation member
    simp only [requiredBasis, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact covered .refl (by simp [operations])
    · exact covered .trans (by simp [operations])
    · exact covered .abs (by simp [operations])
    · exact covered .inst inst_uses_term_substitution
    · exact covered .instType inst_type_uses_type_substitution
    · exact covered .beta beta_uses_beta_admission
  · intro included
    exact covers_mono included required_basis_covers

namespace Controls

/-- A basis admitting the nonbinding comparison rules. -/
def comparisonBasis : Basis := { .syntaxComparison, .hypothesisOperations }

theorem reflexivity_admitted : Admitted comparisonBasis .refl := by
  simp [Admitted, comparisonBasis, operations]

theorem transitivity_admitted : Admitted comparisonBasis .trans := by
  simp [Admitted, comparisonBasis, operations]

theorem beta_not_admitted : ¬ Admitted comparisonBasis .beta := by
  simp [Admitted, comparisonBasis, operations]

theorem inst_not_admitted : ¬ Admitted comparisonBasis .inst := by
  intro admitted
  have used := admitted inst_uses_term_substitution
  simp [comparisonBasis] at used

theorem strict_basis_not_full_hol : ¬ Covers comparisonBasis :=
  not_covers_without_beta (by simp [comparisonBasis])

end Controls

end Mettapedia.Languages.HOLLight.CheckingDiscipline
