import Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanaries

/-!
# Regression checks for PNP v13 locked-core lab canaries

Regression anchors for the finite locked-core ambiguity search and the
public-message invariant repair surface.
-/

namespace Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanariesRegression

open Mettapedia.Computability.PNP

universe u v w z

theorem public_message_invariant_implies_locked_message_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    {publicMessage : PublicLock → Message}
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    C.LockedMessageRigidity := by
  exact
    AppendixDLockedCore.lockedMessageRigidity_of_publicMessageInvariant
      C hinvariant

theorem locked_core_public_message_invariant_bool_positive_regression :
    lockedCoreRigidPublicMessageInvariantAudit.clearsPublicMessageInvariantGate =
        true ∧
      lockedCoreRigidPublicMessageInvariantAudit.publicMessageInvariant =
        true ∧
      lockedCoreRigidPublicMessageInvariantAudit.crossCompletionAmbiguity =
        false := by
  exact lockedCorePublicMessageInvariant_bool_positive_canary

theorem locked_core_deterministic_readout_only_bool_negative_regression :
    lockedCoreAmbiguousDeterministicReadoutAudit.deterministicReadoutOnlyCounterexample =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.clearsPublicMessageInvariantGate =
        false := by
  exact lockedCoreDeterministicReadoutOnly_bool_negative_canary

theorem locked_core_ambiguous_no_public_message_invariant_bool_negative_regression :
    lockedCoreAmbiguousDeterministicReadoutAudit.blocksPublicMessageInvariant =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.publicMessageInvariant =
        false := by
  exact lockedCoreAmbiguousNoPublicMessageInvariant_bool_negative_canary

theorem locked_core_public_message_invariant_bool_guardrails_regression :
    lockedCoreRigidPublicMessageInvariantAudit.clearsPublicMessageInvariantGate =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.deterministicReadoutOnlyCounterexample =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.clearsPublicMessageInvariantGate =
        false ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.blocksPublicMessageInvariant =
        true := by
  exact lockedCorePublicMessageInvariant_bool_guardrails

theorem rigid_locked_core_public_message_invariant_regression :
    rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity := by
  exact rigidAppendixDLockedCore_publicMessageInvariant_canary

theorem ambiguous_locked_core_has_no_public_message_invariant_regression :
    (∀ publicMessage : Unit → Bool,
      ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact ambiguousAppendixDLockedCore_noPublicMessageInvariant_canary

theorem locked_core_public_message_invariant_guardrails_regression :
    (rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity) ∧
      (∀ publicMessage : Unit → Bool,
        ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact lockedCorePublicMessageInvariant_lab_guardrails

theorem locked_core_identity_readout_family_refutation_regression (n : Nat) :
    (identityReadoutAppendixDLockedCoreFinSucc n).LockSatisfiable ∧
      (identityReadoutAppendixDLockedCoreFinSucc n).ReadDeterministic ∧
      (∀ publicMessage : Unit → Fin (n + 1) → Bool,
        ¬ (identityReadoutAppendixDLockedCoreFinSucc n).PublicMessageInvariant
          publicMessage) ∧
      ¬ (identityReadoutAppendixDLockedCoreFinSucc n).LockedMessageRigidity := by
  exact lockedCoreIdentityReadoutFamily_lab_refutation n

end Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanariesRegression
