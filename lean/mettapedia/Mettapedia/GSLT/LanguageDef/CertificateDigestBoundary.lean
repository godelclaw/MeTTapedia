import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# When a digest can preserve exact proof replay

A digest is an identifier, not evidence that a computation or proof succeeded.
Exact replay based only on a digest requires the original acceptance predicate
to be constant on each digest fibre, separately for every claim and authority.

The existence theorem below is set-theoretic. Its classical representative
selection does not produce an efficient digest checker. Cryptographic
certificates and authenticated caches need their own explicit trust and
correctness contracts; none is inferred from a hash equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateDigestBoundary

open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Claim Certificate Key : Type*}

def FibreConstant (checker : Checker Claim Certificate) (digest : Certificate → Key) : Prop :=
  ∀ claim first second, digest first = digest second →
    checker.check claim first = checker.check claim second

def ExactDigestReplay (checker : Checker Claim Certificate) (digest : Certificate → Key)
    (digestChecker : Checker Claim Key) : Prop :=
  ∀ claim certificate, digestChecker.check claim (digest certificate) =
    checker.check claim certificate

theorem exact_replay_fibre_constant
    {checker : Checker Claim Certificate} {digest : Certificate → Key}
    {digestChecker : Checker Claim Key}
    (exactReplay : ExactDigestReplay checker digest digestChecker) :
    FibreConstant checker digest := by
  intro claim first second collision
  rw [← exactReplay claim first, ← exactReplay claim second, collision]

/-- A collision joining an accepted and rejected proof prevents exact replay
from the digest alone, even if the digest checker is otherwise trusted. -/
theorem collision_prevents_exact_replay
    (checker : Checker Claim Certificate) (digest : Certificate → Key)
    (claim : Claim) (first second : Certificate)
    (collision : digest first = digest second)
    (accepted : checker.check claim first = true)
    (refused : checker.check claim second = false) :
    ¬ ∃ digestChecker, ExactDigestReplay checker digest digestChecker := by
  rintro ⟨digestChecker, exactReplay⟩
  have same := exact_replay_fibre_constant exactReplay claim first second collision
  rw [accepted, refused] at same
  cases same

/-- This characterization does not assert that representative choice or the
original checker is computable, or that hashing saves any checking work. -/
theorem exists_exact_replay_iff (checker : Checker Claim Certificate)
    (digest : Certificate → Key) :
    (∃ digestChecker, ExactDigestReplay checker digest digestChecker) ↔
      FibreConstant checker digest := by
  constructor
  · rintro ⟨_, exactReplay⟩
    exact exact_replay_fibre_constant exactReplay
  · intro constant
    classical
    let digestChecker : Checker Claim Key := ⟨fun claim key =>
      if represented : ∃ certificate, digest certificate = key then
        checker.check claim (Classical.choose represented)
      else false⟩
    refine ⟨digestChecker, fun claim certificate => ?_⟩
    dsimp only [digestChecker]
    have represented : ∃ original, digest original = digest certificate := ⟨certificate, rfl⟩
    rw [dif_pos represented]
    exact constant claim _ certificate (Classical.choose_spec represented)

theorem injective_digest_fibre_constant (checker : Checker Claim Certificate)
    {digest : Certificate → Key} (injective : Function.Injective digest) :
    FibreConstant checker digest := by
  intro claim first second same
  rw [injective same]

namespace Controls

def zeroChecker : Checker Nat Nat where
  check claim certificate := decide (claim = 0 ∧ certificate = 0)

def parityDigest (certificate : Nat) : Nat := certificate % 2

theorem accepted_original : zeroChecker.check 0 0 = true := by decide

theorem changed_certificate_refused : zeroChecker.check 0 2 = false := by decide

theorem same_digest_different_authority :
    ¬ ∃ digestChecker, ExactDigestReplay zeroChecker parityDigest digestChecker :=
  collision_prevents_exact_replay zeroChecker parityDigest 0 0 2
    (by decide) accepted_original changed_certificate_refused

theorem complete_identifier_preserves_replay :
    ∃ digestChecker, ExactDigestReplay zeroChecker id digestChecker :=
  (exists_exact_replay_iff zeroChecker id).mpr
    (injective_digest_fibre_constant zeroChecker Function.injective_id)

end Controls

end Mettapedia.GSLT.LanguageDef.CertificateDigestBoundary
