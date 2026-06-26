import Mathlib.Data.Fintype.Pi
import Mettapedia.Computability.PNP.PNPv13AppendixDLockedCore

/-!
# PNP v13: finite identity-readout locked-core family

This module scales the Appendix D deterministic-readout countermodel from one
Boolean quotient bit to every nonempty finite Boolean quotient block.  The
readout predicate is the concrete identity predicate `M = z`: every fixed
readout state has a unique message, but different accepted states over the same
public lock carry different messages.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- The finite identity-readout locked core over a Boolean coordinate block. -/
def identityReadoutAppendixDLockedCore
    (Coord : Type u) [Fintype Coord] [DecidableEq Coord] :
    AppendixDLockedCore Unit (Coord → Bool) Unit (Coord → Bool) where
  publicLockFinite := inferInstance
  quotientFinite := inferInstance
  lockAuxFinite := inferInstance
  messageFinite := inferInstance
  support := fun _ => () = ()
  lockPredicate := fun _ _ _ _ => () = ()
  readPredicate := fun _ z _ M => M = z

/-- The accepted completion determined by one Boolean quotient block. -/
def identityReadoutAppendixDCompletion
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord]
    (assignment : Coord → Bool) :
    (identityReadoutAppendixDLockedCore Coord).LockedCompletion () where
  quotient := assignment
  lockAux := ()
  message := assignment
  lock_ok := rfl
  read_ok := rfl

/-- The all-false accepted completion. -/
def identityReadoutAppendixDCompletionFalse
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] :
    (identityReadoutAppendixDLockedCore Coord).LockedCompletion () :=
  identityReadoutAppendixDCompletion (fun _ => false)

/-- The all-true accepted completion. -/
def identityReadoutAppendixDCompletionTrue
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] :
    (identityReadoutAppendixDLockedCore Coord).LockedCompletion () :=
  identityReadoutAppendixDCompletion (fun _ => true)

/-- The finite identity-readout family is satisfiable on its public lock. -/
theorem identityReadoutAppendixDLockedCore_lockSatisfiable
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] :
    (identityReadoutAppendixDLockedCore Coord).LockSatisfiable := by
  intro Y _hY
  cases Y
  exact ⟨identityReadoutAppendixDCompletionFalse⟩

/-- Identity readout is deterministic for each fixed readout state. -/
theorem identityReadoutAppendixDLockedCore_readDeterministic
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] :
    (identityReadoutAppendixDLockedCore Coord).ReadDeterministic := by
  intro _Y _z _ξ _M _M' hM hM'
  exact hM.trans hM'.symm

/-- Any visible coordinate separates the all-false and all-true completions. -/
theorem identityReadoutAppendixDLockedCore_not_lockedMessageRigidity_of_coord
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] (i : Coord) :
    ¬ (identityReadoutAppendixDLockedCore Coord).LockedMessageRigidity := by
  exact
    AppendixDLockedCore.not_lockedMessageRigidity_of_distinct_completions
      (identityReadoutAppendixDLockedCore Coord)
      (Y := ())
      rfl
      identityReadoutAppendixDCompletionFalse
      identityReadoutAppendixDCompletionTrue
      (by
        intro h
        have hpoint := congrFun h i
        cases hpoint)

/-- Every nonempty finite identity-readout block refutes D.8 rigidity. -/
theorem identityReadoutAppendixDLockedCore_not_lockedMessageRigidity
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] [Nonempty Coord] :
    ¬ (identityReadoutAppendixDLockedCore Coord).LockedMessageRigidity := by
  rcases (inferInstance : Nonempty Coord) with ⟨i⟩
  exact identityReadoutAppendixDLockedCore_not_lockedMessageRigidity_of_coord i

/-- A visible coordinate also refutes any public-message invariant candidate. -/
theorem identityReadoutAppendixDLockedCore_not_publicMessageInvariant_of_coord
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] (i : Coord)
    (publicMessage : Unit → Coord → Bool) :
    ¬ (identityReadoutAppendixDLockedCore Coord).PublicMessageInvariant
      publicMessage := by
  exact
    AppendixDLockedCore.not_publicMessageInvariant_of_distinct_completions
      (identityReadoutAppendixDLockedCore Coord)
      (Y := ())
      rfl
      identityReadoutAppendixDCompletionFalse
      identityReadoutAppendixDCompletionTrue
      (by
        intro h
        have hpoint := congrFun h i
        cases hpoint)

/-- No public-message invariant exists for a nonempty identity-readout block. -/
theorem identityReadoutAppendixDLockedCore_noPublicMessageInvariant
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] [Nonempty Coord] :
    ∀ publicMessage : Unit → Coord → Bool,
      ¬ (identityReadoutAppendixDLockedCore Coord).PublicMessageInvariant
        publicMessage := by
  intro publicMessage
  rcases (inferInstance : Nonempty Coord) with ⟨i⟩
  exact
    identityReadoutAppendixDLockedCore_not_publicMessageInvariant_of_coord
      i publicMessage

/-- The scaled refutation packet: satisfiable and read-deterministic, but no
public-message invariant and no D.8 locked-message rigidity. -/
theorem identityReadoutAppendixDLockedCore_refutation_packet
    {Coord : Type u} [Fintype Coord] [DecidableEq Coord] [Nonempty Coord] :
    (identityReadoutAppendixDLockedCore Coord).LockSatisfiable ∧
      (identityReadoutAppendixDLockedCore Coord).ReadDeterministic ∧
      (∀ publicMessage : Unit → Coord → Bool,
        ¬ (identityReadoutAppendixDLockedCore Coord).PublicMessageInvariant
          publicMessage) ∧
      ¬ (identityReadoutAppendixDLockedCore Coord).LockedMessageRigidity := by
  exact
    ⟨identityReadoutAppendixDLockedCore_lockSatisfiable,
      identityReadoutAppendixDLockedCore_readDeterministic,
      identityReadoutAppendixDLockedCore_noPublicMessageInvariant,
      identityReadoutAppendixDLockedCore_not_lockedMessageRigidity⟩

/-- The concrete positive-dimensional finite family used by the validation lab. -/
def identityReadoutAppendixDLockedCoreFinSucc (n : Nat) :
    AppendixDLockedCore Unit (Fin (n + 1) → Bool) Unit
      (Fin (n + 1) → Bool) :=
  identityReadoutAppendixDLockedCore (Fin (n + 1))

/-- Lab-facing scaled refutation over every positive finite dimension. -/
theorem identityReadoutAppendixDLockedCoreFinSucc_refutation_packet
    (n : Nat) :
    (identityReadoutAppendixDLockedCoreFinSucc n).LockSatisfiable ∧
      (identityReadoutAppendixDLockedCoreFinSucc n).ReadDeterministic ∧
      (∀ publicMessage : Unit → Fin (n + 1) → Bool,
        ¬ (identityReadoutAppendixDLockedCoreFinSucc n).PublicMessageInvariant
          publicMessage) ∧
      ¬ (identityReadoutAppendixDLockedCoreFinSucc n).LockedMessageRigidity := by
  exact
    identityReadoutAppendixDLockedCore_refutation_packet
      (Coord := Fin (n + 1))

end Mettapedia.Computability.PNP
