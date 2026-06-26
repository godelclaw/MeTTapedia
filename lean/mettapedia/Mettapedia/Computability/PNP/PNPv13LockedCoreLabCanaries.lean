import Mettapedia.Computability.PNP.PNPv13AppendixDLockedCore

/-!
# PNP v13 locked-core lab canaries

This module records the finite canaries mirrored by the private validation lab.
The negative canary shows that deterministic readout at each completion state
does not imply Appendix D locked-message rigidity.  The positive canary records
a tiny rigid core where every accepted completion reads one public message.
-/

namespace Mettapedia.Computability.PNP

/-- Finite Boolean audit state for the locked-core public-message invariant. -/
structure LockedCorePublicMessageInvariantCanaryAudit where
  lockSatisfiable : Bool
  readDeterministic : Bool
  publicMessageInvariant : Bool
  crossCompletionAmbiguity : Bool
deriving DecidableEq, Repr

namespace LockedCorePublicMessageInvariantCanaryAudit

/-- Whether the public-message invariant gate clears in the finite audit. -/
def clearsPublicMessageInvariantGate
    (audit : LockedCorePublicMessageInvariantCanaryAudit) : Bool :=
  audit.lockSatisfiable &&
    audit.publicMessageInvariant &&
    !audit.crossCompletionAmbiguity

/-- Whether deterministic readout alone is exposed as an ambiguity canary. -/
def deterministicReadoutOnlyCounterexample
    (audit : LockedCorePublicMessageInvariantCanaryAudit) : Bool :=
  audit.lockSatisfiable &&
    audit.readDeterministic &&
    audit.crossCompletionAmbiguity &&
    !audit.publicMessageInvariant

/-- Whether the finite audit refutes public-message invariance. -/
def blocksPublicMessageInvariant
    (audit : LockedCorePublicMessageInvariantCanaryAudit) : Bool :=
  audit.crossCompletionAmbiguity &&
    !audit.publicMessageInvariant

end LockedCorePublicMessageInvariantCanaryAudit

/-- Positive finite audit: a satisfiable core with a public-message invariant
and no cross-completion ambiguity clears the gate. -/
def lockedCoreRigidPublicMessageInvariantAudit :
    LockedCorePublicMessageInvariantCanaryAudit where
  lockSatisfiable := true
  readDeterministic := true
  publicMessageInvariant := true
  crossCompletionAmbiguity := false

/-- Negative finite audit: deterministic readout with a cross-completion
ambiguity lacks the public-message invariant. -/
def lockedCoreAmbiguousDeterministicReadoutAudit :
    LockedCorePublicMessageInvariantCanaryAudit where
  lockSatisfiable := true
  readDeterministic := true
  publicMessageInvariant := false
  crossCompletionAmbiguity := true

theorem lockedCorePublicMessageInvariant_bool_positive_canary :
    lockedCoreRigidPublicMessageInvariantAudit.clearsPublicMessageInvariantGate =
        true ∧
      lockedCoreRigidPublicMessageInvariantAudit.publicMessageInvariant =
        true ∧
      lockedCoreRigidPublicMessageInvariantAudit.crossCompletionAmbiguity =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem lockedCoreDeterministicReadoutOnly_bool_negative_canary :
    lockedCoreAmbiguousDeterministicReadoutAudit.deterministicReadoutOnlyCounterexample =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.clearsPublicMessageInvariantGate =
        false := by
  exact ⟨rfl, rfl⟩

theorem lockedCoreAmbiguousNoPublicMessageInvariant_bool_negative_canary :
    lockedCoreAmbiguousDeterministicReadoutAudit.blocksPublicMessageInvariant =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.publicMessageInvariant =
        false := by
  exact ⟨rfl, rfl⟩

theorem lockedCorePublicMessageInvariant_bool_guardrails :
    lockedCoreRigidPublicMessageInvariantAudit.clearsPublicMessageInvariantGate =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.deterministicReadoutOnlyCounterexample =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.clearsPublicMessageInvariantGate =
        false ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.blocksPublicMessageInvariant =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A bounded rigid locked core: every accepted completion reads the public
message `false`, independent of the quotient and lock auxiliary coordinates. -/
def rigidAppendixDLockedCore :
    AppendixDLockedCore Unit Unit Unit Bool where
  publicLockFinite := inferInstance
  quotientFinite := inferInstance
  lockAuxFinite := inferInstance
  messageFinite := inferInstance
  support := fun _ => () = ()
  lockPredicate := fun _ _ _ M => M = false
  readPredicate := fun _ _ _ M => M = false

/-- The canonical accepted completion for the rigid locked-core canary. -/
def rigidAppendixDCompletionFalse :
    rigidAppendixDLockedCore.LockedCompletion () where
  quotient := ()
  lockAux := ()
  message := false
  lock_ok := rfl
  read_ok := rfl

/-- The rigid canary is satisfiable on every supported public lock. -/
theorem rigidAppendixDLockedCore_lockSatisfiable :
    rigidAppendixDLockedCore.LockSatisfiable := by
  intro Y _hY
  cases Y
  exact ⟨rigidAppendixDCompletionFalse⟩

/-- The rigid canary has deterministic readout at each completion state. -/
theorem rigidAppendixDLockedCore_readDeterministic :
    rigidAppendixDLockedCore.ReadDeterministic := by
  intro _Y _z _ξ M M' hM hM'
  exact hM.trans hM'.symm

/-- The rigid canary satisfies cross-completion locked-message rigidity. -/
theorem rigidAppendixDLockedCore_lockedMessageRigidity :
    rigidAppendixDLockedCore.LockedMessageRigidity := by
  intro _Y _hY L L'
  have hL : L.message = false := by
    simpa [rigidAppendixDLockedCore] using L.read_ok
  have hL' : L'.message = false := by
    simpa [rigidAppendixDLockedCore] using L'.read_ok
  exact hL.trans hL'.symm

/-- Public message selected by the rigid finite canary. -/
def rigidAppendixDLockedCore_publicMessage : Unit → Bool :=
  fun _ => false

/-- The rigid finite canary carries the candidate public-message invariant. -/
theorem rigidAppendixDLockedCore_publicMessageInvariant :
    rigidAppendixDLockedCore.PublicMessageInvariant
      rigidAppendixDLockedCore_publicMessage := by
  intro Y _hY L
  cases Y
  have hL : L.message = false := by
    simpa [rigidAppendixDLockedCore] using L.read_ok
  simpa [rigidAppendixDLockedCore_publicMessage] using hL

/-- Positive invariant canary: the public-message invariant closes D.8 for the
rigid bounded locked core. -/
theorem rigidAppendixDLockedCore_publicMessageInvariant_canary :
    rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity := by
  exact
    ⟨rigidAppendixDLockedCore_publicMessageInvariant,
      AppendixDLockedCore.lockedMessageRigidity_of_publicMessageInvariant
        rigidAppendixDLockedCore
        rigidAppendixDLockedCore_publicMessageInvariant⟩

/-- Positive lab canary: a public-message invariant is enough for this bounded
locked core to satisfy the locked-message target. -/
theorem rigidAppendixDLockedCore_lab_positive_canary :
    rigidAppendixDLockedCore.LockSatisfiable ∧
      rigidAppendixDLockedCore.ReadDeterministic ∧
      rigidAppendixDLockedCore.LockedMessageRigidity := by
  exact
    ⟨rigidAppendixDLockedCore_lockSatisfiable,
      rigidAppendixDLockedCore_readDeterministic,
      rigidAppendixDLockedCore_lockedMessageRigidity⟩

/-- Negative lab canary: satisfiability and deterministic per-state readout do
not imply cross-completion locked-message rigidity. -/
theorem ambiguousAppendixDLockedCore_lab_negative_canary :
    ambiguousAppendixDLockedCore.LockSatisfiable ∧
      ambiguousAppendixDLockedCore.ReadDeterministic ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact
    ⟨ambiguousAppendixDLockedCore_lockSatisfiable,
      ambiguousAppendixDLockedCore_readDeterministic,
      ambiguousAppendixDLockedCore_not_lockedMessageRigidity⟩

/-- The ambiguous finite canary has no public-message invariant over its single
supported public lock. -/
theorem ambiguousAppendixDLockedCore_not_publicMessageInvariant
    (publicMessage : Unit → Bool) :
    ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage := by
  exact
    AppendixDLockedCore.not_publicMessageInvariant_of_distinct_completions
      ambiguousAppendixDLockedCore
      (Y := ())
      trivial
      ambiguousAppendixDCompletionFalse
      ambiguousAppendixDCompletionTrue
      (by
        intro h
        cases h)

/-- Negative invariant canary: deterministic readout does not merely omit a
proof of the candidate invariant; the ambiguous bounded core refutes it. -/
theorem ambiguousAppendixDLockedCore_noPublicMessageInvariant_canary :
    (∀ publicMessage : Unit → Bool,
      ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact
    ⟨ambiguousAppendixDLockedCore_not_publicMessageInvariant,
      ambiguousAppendixDLockedCore_not_lockedMessageRigidity⟩

/-- The finite lab canaries separate deterministic readout from the actual
Appendix D.8 locked-message rigidity obligation. -/
theorem lockedCoreLabCanaries_separate_readDeterministic_from_lockedMessageRigidity :
    (∃ C : AppendixDLockedCore Unit Unit Unit Bool,
      C.LockSatisfiable ∧ C.ReadDeterministic ∧ C.LockedMessageRigidity) ∧
      (∃ C : AppendixDLockedCore Unit Bool Unit Bool,
        C.LockSatisfiable ∧ C.ReadDeterministic ∧
          ¬ C.LockedMessageRigidity) := by
  exact
    ⟨⟨rigidAppendixDLockedCore,
        rigidAppendixDLockedCore_lab_positive_canary⟩,
      ⟨ambiguousAppendixDLockedCore,
        ambiguousAppendixDLockedCore_lab_negative_canary⟩⟩

/-- The lab-refined missing invariant surface: public-message invariance is a
sufficient repair, while the deterministic-readout countermodel refutes every
public-message invariant. -/
theorem lockedCorePublicMessageInvariant_lab_guardrails :
    (rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity) ∧
      (∀ publicMessage : Unit → Bool,
        ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact
    ⟨rigidAppendixDLockedCore_publicMessageInvariant_canary,
      ambiguousAppendixDLockedCore_noPublicMessageInvariant_canary⟩

end Mettapedia.Computability.PNP
