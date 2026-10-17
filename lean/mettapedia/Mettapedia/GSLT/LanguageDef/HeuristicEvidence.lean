import Mettapedia.GSLT.LanguageDef.NonEffectiveKernelBoundary

/-!
# Suggestions, checked evidence and truth beyond a fixed checker

An arbitrary producer may suggest certificates. Checking those suggestions
needs no correctness, fairness or completeness assumption on the producer.
Even a noncomputable producer cannot turn a claim outside the fixed checker's
accepted language into a checked theorem. Changing the checker or its axioms
is a different operation.

The concrete nonhalting result is relative to each sound effective checker:
there is a true nonhalting claim with no accepted certificate for that checker.
It does not assert that one particular claim lacks proofs in every possible
sound theory. The finite list is the submission policy, not an order promised
by an object language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HeuristicEvidence

open KernelAuthority
open Nat.Partrec (Code)

universe u v
variable {Claim : Type u} {Certificate : Type v}

/-- Retain exactly the submitted certificates accepted by the original checker. -/
def screen (checker : Checker Claim Certificate) (claim : Claim)
    (proposals : List Certificate) : List Certificate :=
  proposals.filter (checker.check claim)

theorem mem_screen (checker : Checker Claim Certificate) (claim : Claim)
    (proposals : List Certificate) (certificate : Certificate) :
    certificate ∈ screen checker claim proposals ↔
      certificate ∈ proposals ∧ checker.check claim certificate = true := by
  simp [screen]

theorem screen_sound (checker : Checker Claim Certificate) (meaning : Claim → Prop)
    (sound : checker.Sound meaning) (claim : Claim) (proposals : List Certificate)
    (certificate : Certificate) (found : certificate ∈ screen checker claim proposals) :
    meaning claim := sound claim certificate ((mem_screen _ _ _ _).mp found).2

theorem screen_complete_for_submissions (checker : Checker Claim Certificate)
    (claim : Claim) (proposals : List Certificate) :
    (∃ certificate, certificate ∈ screen checker claim proposals) ↔
      ∃ certificate ∈ proposals, checker.check claim certificate = true := by
  simp only [mem_screen]

/-- Resubmitting two batches preserves each accepted occurrence. -/
theorem screen_append (checker : Checker Claim Certificate) (claim : Claim)
    (first second : List Certificate) :
    screen checker claim (first ++ second) =
      screen checker claim first ++ screen checker claim second := by
  simp [screen]

theorem screen_empty_iff (checker : Checker Claim Certificate) (claim : Claim)
    (proposals : List Certificate) :
    screen checker claim proposals = [] ↔
      ∀ certificate ∈ proposals, checker.check claim certificate = false := by
  simp [screen, List.filter_eq_nil_iff]

/-- The producer has no semantic obligations. Its suggestions earn authority
only from acceptance by the separately supplied sound checker. -/
theorem arbitrary_producer_sound (checker : Checker Claim Certificate)
    (meaning : Claim → Prop) (sound : checker.Sound meaning)
    (producer : Claim → List Certificate) (claim : Claim)
    (certificate : Certificate)
    (found : certificate ∈ screen checker claim (producer claim)) : meaning claim :=
  screen_sound checker meaning sound claim _ certificate found

/-- An empty submission can miss a theorem even for an exact checker. -/
theorem empty_submission_can_miss_truth (checker : Checker Claim Certificate)
    (meaning : Claim → Prop) (authority : checker.Authority meaning)
    (claim : Claim) (trueClaim : meaning claim) :
    screen checker claim [] = [] ∧
      ∃ certificate, screen checker claim [certificate] = [certificate] := by
  obtain ⟨certificate, checked⟩ := authority.complete claim trueClaim
  exact ⟨rfl, certificate, by simp [screen, checked]⟩

open EffectiveKernelSearch

/-- Every fixed sound effective checker misses a true nonhalting claim.
Soundness alone is assumed; the impossibility of complete recognition proves
the existence of the missing truth. -/
theorem sound_effective_checker_misses_truth (checkerCode : Code)
    (sound : ∀ (program : Code) (certificate : Nat),
      Accepted checkerCode (Encodable.encode program) certificate →
        ¬ (program.eval 0).Dom) :
    ∃ program : Code, ¬ (program.eval 0).Dom ∧
      ∀ certificate, ¬ Accepted checkerCode (Encodable.encode program) certificate := by
  classical
  by_contra noGap
  apply NonEffectiveKernelBoundary.no_effective_complete_nonhalting checkerCode
  intro program
  constructor
  · rintro ⟨certificate, accepted⟩
    exact sound program certificate accepted
  · intro trueClaim
    by_contra noProof
    exact noGap ⟨program, trueClaim, fun certificate accepted => noProof ⟨certificate, accepted⟩⟩

/-- Arbitrary suggestion streams, including abstract external oracles, cannot
close this gap while keeping the same effective evidence checker. -/
theorem producer_cannot_add_authority (checkerCode : Code)
    (sound : ∀ (program : Code) (certificate : Nat),
      Accepted checkerCode (Encodable.encode program) certificate →
        ¬ (program.eval 0).Dom)
    (producer : Code → Nat → Nat) :
    ∃ program : Code, ¬ (program.eval 0).Dom ∧
      ∀ attempt, ¬ Accepted checkerCode (Encodable.encode program) (producer program attempt) := by
  obtain ⟨program, trueClaim, noProof⟩ := sound_effective_checker_misses_truth checkerCode sound
  exact ⟨program, trueClaim, fun attempt => noProof (producer program attempt)⟩

end Mettapedia.GSLT.LanguageDef.HeuristicEvidence
