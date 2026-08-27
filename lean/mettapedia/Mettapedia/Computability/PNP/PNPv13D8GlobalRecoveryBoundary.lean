import Mettapedia.Computability.PNP.V13FaithfulQuantitativeFrontiers

/-!
# PNP v13: D.8 and full-syntax recovery

Appendix D.7 and D.8 imply that the common locked message is a mathematical
function of the complete public lock syntax.  This module connects that fact
to the full-syntax hiding predicate used by the faithful statement layer.

The result does not weaken D.30.  It separates two meanings that cannot be
conflated: D.30 may forbid raw primitives and computationally uncharged
decoding, but it cannot forbid every set-theoretic decoder while also requiring
D.7 and D.8.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

namespace AppendixDLockedCore

universe u v w

/-- The ordinary nondependent tuple presentation of an Appendix-D completion
when the locked message is Boolean. -/
abbrev FlatBoolWitness (Quotient : Type v) (LockAux : Type w) :=
  Quotient × LockAux × Bool

/-- Verification of a flat tuple against the full public lock syntax. -/
def flatBoolVerifier
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Bool)
    (Y : PublicLock) (W : FlatBoolWitness Quotient LockAux) : Prop :=
  C.support Y ∧
    C.lockPredicate Y W.1 W.2.1 W.2.2 ∧
      C.readPredicate Y W.1 W.2.1 W.2.2

/-- The message coordinate of a flat Appendix-D completion. -/
def flatBoolReadout {Quotient : Type v} {LockAux : Type w}
    (W : FlatBoolWitness Quotient LockAux) : Bool :=
  W.2.2

/-- D.7 and D.8 refute global set-theoretic readout hiding for the complete
public lock syntax.  The recovery map is the common message selected from the
nonempty rigid completion fiber; no efficient decoder is asserted. -/
theorem not_fullPublicSyntaxReadoutHiding_of_D7_D8
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Bool)
    (hsat : C.LockSatisfiable) (hrigid : C.LockedMessageRigidity) :
    ¬ V13FullPublicSyntaxReadoutHiding
      (C.flatBoolVerifier)
      (flatBoolReadout (Quotient := Quotient) (LockAux := LockAux))
      (fun Y => Y) := by
  intro hhiding
  apply hhiding
  let recover : PublicLock -> Bool :=
    C.publicMessageOfLockedRigidity false hsat hrigid
  refine ⟨recover, ?_⟩
  intro Y W hW
  rcases hW with ⟨hY, hlock, hread⟩
  let L : C.LockedCompletion Y :=
    { quotient := W.1
      lockAux := W.2.1
      message := W.2.2
      lock_ok := hlock
      read_ok := hread }
  exact
    C.publicMessageInvariant_of_lockSatisfiable_of_lockedMessageRigidity
      false hsat hrigid hY L

end AppendixDLockedCore

end Mettapedia.Computability.PNP
