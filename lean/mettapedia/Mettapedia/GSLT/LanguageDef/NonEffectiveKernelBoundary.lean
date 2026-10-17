import Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch

/-!
# A concrete boundary beyond effective complete checking

Halting computations have finite effectively checked evidence. Their
complement has no sound and complete effective finite-certificate checker,
even if that checker may diverge on rejected certificates and search is fair.

This is an obstruction to completeness for the whole nonhalting predicate,
not to sound proofs of particular nonhalting claims. A regular infinitary
proof language with a decidable global condition remains effective and must
retain its explicitly stated semantic scope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NonEffectiveKernelBoundary

open Nat.Partrec (Code)
open Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

/-- Arbitrary divergence inside the proposed checker does not evade the
obstruction: finite accepted runs still form a recursively enumerable set. -/
theorem no_effective_complete_nonhalting (checkerCode : Code) :
    ¬ (∀ program : Code,
      (∃ certificate, Accepted checkerCode (Encodable.encode program) certificate) ↔
        ¬ (program.eval 0).Dom) := by
  intro authority
  have recognized : REPred (fun program : Code =>
      (search checkerCode (Encodable.encode program)).Dom) :=
    ((search_partrec checkerCode).comp Computable.encode).dom_re
  exact ComputablePred.halting_problem_not_re 0
    (recognized.of_eq fun program =>
      (search_dom_iff checkerCode (Encodable.encode program)).trans (authority program))

/-- A positive, computably checked finite witness language exists for
halting, while no supplied finite checking code has full negative authority. -/
theorem positive_evidence_negative_boundary :
    (haltingTrustBoundaryChecker.Authority HaltingMeaning) ∧
    Computable (fun input : Code × Nat =>
      haltingTrustBoundaryChecker.check input.1 input.2) ∧
    ¬ (∃ checkerCode : Code, ∀ program : Code,
      (∃ certificate, Accepted checkerCode (Encodable.encode program) certificate) ↔
        ¬ (program.eval 0).Dom) := by
  refine ⟨haltingTrustBoundaryAuthority, haltingTrustBoundaryChecker_computable, ?_⟩
  rintro ⟨checkerCode, authority⟩
  exact no_effective_complete_nonhalting checkerCode authority

end Mettapedia.GSLT.LanguageDef.NonEffectiveKernelBoundary
