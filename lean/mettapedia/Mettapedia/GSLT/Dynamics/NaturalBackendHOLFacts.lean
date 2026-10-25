import Mettapedia.GSLT.Dynamics.NaturalBackendAdmission
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall
import Mathlib.Data.FinEnum

/-!
# Guarded word execution at the selected HOL natural carrier

The guarded `UInt64` backend and its unbounded fallback are an operational
representation choice.  Decoding either branch gives the same host natural
observation, but the tagged sum is not itself a carrier representation:
different branches can denote the same number.  This module connects the exact
observation to the selected HOL natural carrier while retaining that boundary.

These theorems concern Lean's word backend contract.  They do not verify a C or
GMP implementation and make no performance claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.NaturalBackendHOLFacts

open Mettapedia.GSLT.LanguageDef.IndexedInductive
open Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts
open Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
open NaturalBackendAdmission

namespace IntegerProvider

open Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall
open Mettapedia.GSLT.LanguageDef.ArithmeticExternalCallPilot
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

/-- Read a nonnegative exact-integer result at the selected host-natural
carrier.  Negative integers and declines have no natural observation. -/
def observeNatural :
    Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger.Outcome →
      Option NaturalControl.hostInterpretation.Carrier
  | .declined => none
  | .val value => if value < 0 then none else some ⟨value.toNat⟩

/-- Every provider satisfying the existing roundtrip, soundness and fallback
contracts computes addition by one at the selected HOL natural carrier.  The
provider representation remains abstract. -/
theorem addOne_host_exact {Representation Fault : Type*}
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault)
    (sound : SuccessfulSound decode provider)
    (available : FallbackAvailable signedFastPath encode provider)
    (number : Nat) :
    run signedFastPath encode decode provider
        ⟨compileSyntax .add, Int.ofNat number, 1⟩ =
      .ok (.val (Int.ofNat (number + 1))) ∧
    observeNatural (.val (Int.ofNat (number + 1))) = some ⟨number + 1⟩ := by
  constructor
  · rw [run_compiled_eq_core signedFastPath encode decode roundtrip provider sound available]
    simp [coreSem, undefinedAt, CoreOp.isPartial, CoreOp.fn]
  · simp [observeNatural]
    omega

end IntegerProvider

/-- Observe either operational branch in the same lifted host-natural carrier
used by the selected HOL interpretation. -/
def observeBackend : UInt64 ⊕ Nat → NaturalControl.hostInterpretation.Carrier
  | .inl word => ⟨word.toNat⟩
  | .inr number => ⟨number⟩

@[simp] theorem observeBackend_down (artifact : UInt64 ⊕ Nat) :
    (observeBackend artifact).down =
      Sum.elim UInt64.toNat (fun result => result) artifact := by
  cases artifact <;> rfl

/-- Guarded word execution plus fallback preserves unbounded successor at the
selected HOL carrier. -/
theorem successorBackend_host_exact (number : Nat) :
    observeBackend (successorBackend.compile () number) = ⟨number + 1⟩ := by
  apply ULift.ext
  rw [observeBackend_down]
  exact successorBackend_exact number

/-- The same result is the selected image of the authored polynomial
successor, so the execution contract reaches the HOL representation edge. -/
theorem successorBackend_authored_exact (number : Nat) :
    observeBackend (successorBackend.compile () number) =
      NaturalControl.hostCarrierEquiv
        ⟨Natural.succ (Natural.fromNat number)⟩ := by
  apply ULift.ext
  rw [observeBackend_down]
  rw [show (NaturalControl.hostCarrierEquiv
      ⟨Natural.succ (Natural.fromNat number)⟩).down = number + 1 by
    change Natural.toNat (Natural.succ (Natural.fromNat number)) = number + 1
    simp]
  exact successorBackend_exact number

/-- On the admitted fast region the result is an actual word and its selected
HOL observation is still exact. -/
theorem fast_branch_host_exact (number : Nat)
    (fits : number + 1 < UInt64.size) :
    ∃ word, successorBackend.compile () number = .inl word ∧
      observeBackend (.inl word) = ⟨number + 1⟩ := by
  obtain ⟨word, compiled, decoded⟩ := successorBackend_uses_word number fits
  exact ⟨word, compiled, ULift.ext _ _ decoded⟩

/-- Outside the word range the retained unbounded fallback supplies the exact
same selected observation. -/
theorem fallback_branch_host_exact (number : Nat)
    (outside : UInt64.size ≤ number + 1) :
    successorBackend.compile () number = .inr (number + 1) ∧
      observeBackend (.inr (number + 1)) = ⟨number + 1⟩ :=
  ⟨successorBackend_uses_fallback number outside, rfl⟩

/-- A finite word alone cannot carry the selected Dedekind-infinity fact. -/
theorem finiteWord_has_no_infinityWitness :
    ¬ Nonempty (InfinityWitness (ULift.{1} UInt64)) :=
  no_infinityWitness_of_finite (ULift.{1} UInt64)

/-- Fast and fallback tags can denote the same natural, so observation is not
a carrier equivalence.  The tag remains operational evidence. -/
theorem observeBackend_not_injective : ¬ Function.Injective observeBackend := by
  intro injective
  have same : observeBackend (.inl 0) = observeBackend (.inr 0) := rfl
  have impossible := injective same
  exact Sum.inl_ne_inr impossible

/-- Unchecked word successor cannot replace the guarded backend at this edge. -/
theorem unchecked_word_successor_not_host_exact :
    (ULift.up (maxWord + 1).toNat : ULift.{1} Nat) ≠
      ⟨maxWord.toNat + 1⟩ := by
  intro same
  exact NaturalBackendAdmission.Controls.unchecked_successor_not_natural
    (congrArg ULift.down same)

#print axioms successorBackend_host_exact
#print axioms successorBackend_authored_exact
#print axioms fast_branch_host_exact
#print axioms fallback_branch_host_exact
#print axioms finiteWord_has_no_infinityWitness
#print axioms observeBackend_not_injective
#print axioms unchecked_word_successor_not_host_exact
#print axioms IntegerProvider.addOne_host_exact

end Mettapedia.GSLT.Dynamics.NaturalBackendHOLFacts
