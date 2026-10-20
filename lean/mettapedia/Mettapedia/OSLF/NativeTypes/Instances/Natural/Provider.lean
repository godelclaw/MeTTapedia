import Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCall

/-!
# Authored naturals through a represented integer provider

The join has three separate obligations: natural-domain admission, successful
integer computation, and availability of the fallback. Successful calls are
sound without availability. The two-sided contract needs availability; it
does not reinterpret a resource failure as a false arithmetic proposition.

The original `dispatch` receives mathematical integers and re-encodes fallback
inputs. The retained-counter join below instead uses stored operands directly;
its availability premise concerns those actual operands, not fresh encodings.
Clients use the same natural operations and initial-algebra interpretations.
GMP can supply the trusted integer provider. Its marshaling, ownership and
generated C interface require separate qualification.

The external-call reference machine's ordered-receipt theorem remains in
`ExactArithmetic`: the provider hosting theorem here does not claim that an
arbitrary provider returns those receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider

open Mettapedia.GSLT.LanguageDef
open ArithmeticExtension.ExactInteger
open ArithmeticExternalCallPilot
open Mettapedia.TypeTheory.NaturalAlgebra

variable {Storage Fault : Type*}
variable (fast : IntegerRepresentationExternalCall.FastPath)
variable (encode : Int → Storage) (decode : Storage → Int)
variable (roundtrip : Function.LeftInverse decode encode)
variable (provider : IntegerRepresentationExternalCall.Provider Storage Fault)
variable (sound : IntegerRepresentationExternalCall.SuccessfulSound decode provider)

include roundtrip sound

/-- A resource-limited provider need not satisfy completeness to justify a
returned natural value. Rejection of a request is not refutation of arithmetic. -/
theorem returned_natural_sound (operation : CoreOp)
    (supported : ExactArithmetic.Supported operation) (first second result : Nat)
    (returned : IntegerRepresentationExternalCall.run fast encode decode provider
      ⟨compileSyntax operation, Int.ofNat first, Int.ofNat second⟩ =
        .ok (.val (Int.ofNat result))) :
    ExactArithmetic.Evaluation operation first second result := by
  apply (ExactArithmetic.exact_iff operation supported first second result).mp
  exact IntegerRepresentationExternalCall.run_compiled_value_sound fast encode decode
    roundtrip provider sound operation first second result returned

/-- Availability is separate from value correctness. An admitted provider
execution agrees with the independently defined natural rules in both directions. -/
theorem run_natural_iff
    (available : IntegerRepresentationExternalCall.FallbackAvailable fast encode provider)
    (operation : CoreOp) (supported : ExactArithmetic.Supported operation)
    (first second result : Nat) :
    IntegerRepresentationExternalCall.run fast encode decode provider
        ⟨compileSyntax operation, Int.ofNat first, Int.ofNat second⟩ =
      .ok (.val (Int.ofNat result)) ↔ ExactArithmetic.Evaluation operation first second result := by
  rw [IntegerRepresentationExternalCall.run_compiled_eq_core fast encode decode roundtrip provider sound available]
  simpa only [Except.ok.injEq] using ExactArithmetic.exact_iff operation supported first second result

/-- An arbitrary target of the authored counter is covered exactly by adding
one through the represented backend. This does not expose storage to the source. -/
theorem authored_target_iff
    (available : IntegerRepresentationExternalCall.FallbackAvailable fast encode provider)
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (number : Nat) (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
        Examples.NativeNaturalCounter.language (Examples.NativeNaturalCounter.counter number) target ↔
      ∃ result : Nat,
        IntegerRepresentationExternalCall.run fast encode decode provider ⟨.add, Int.ofNat number, 1⟩ =
          .ok (.val (Int.ofNat result)) ∧
        target = Examples.NativeNaturalCounter.counter result := by
  rw [ExactArithmetic.authored_target_iff]
  simp only [show (CompiledOp.add) = compileSyntax .add from rfl,
    IntegerRepresentationExternalCall.run_compiled_eq_core fast encode decode roundtrip provider sound available,
    Except.ok.injEq]

/-- Any successful addition, regardless of selected storage, has the result
of the initial-algebra fold. No availability assumption is needed here. -/
theorem retained_add_interpretation
    {Carrier : Type*} {algebra : Algebra Carrier} (reading : Representation algebra)
    (first second : Nat) (result : Int64 ⊕ Storage)
    (returned : IntegerRepresentationExternalCall.dispatch fast encode provider
      ⟨.add, Int.ofNat first, Int.ofNat second⟩ = .ok result) :
    ExactArithmetic.representedAdd reading (reading.encode first) (reading.encode second) =
      reading.encode (IntegerRepresentationExternalCall.resultInteger decode result).toNat := by
  have exactValue := IntegerRepresentationExternalCall.dispatch_success fast encode decode roundtrip provider sound
    ⟨.add, Int.ofNat first, Int.ofNat second⟩
    (by simp [IntegerRepresentationExternalCall.Request.Defined, CompiledOp.undefinedAt, CompiledOp.guard]) result returned
  simp only [IntegerRepresentationExternalCall.Request.meaning, CompiledOp.fn,
    Int.ofNat_eq_natCast, ← Int.natCast_add] at exactValue
  rw [exactValue, Int.toNat_natCast, ExactArithmetic.representedAdd_encode]

/-- Adding one to an actual retained representation implements the authored
counter step. Availability concerns precisely the operands passed to fallback.
The theorem does not decode and re-encode the operand to execute the call. -/
theorem retained_counter_target_iff
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (number : Nat) (value : Int64 ⊕ Storage)
    (represents : IntegerRepresentationExternalCall.resultInteger decode value = Int.ofNat number)
    (available : IntegerRepresentationExternalCall.Retained.fast? value (.inl 1) = none →
      ∃ storedResult, provider .add
        (IntegerRepresentationExternalCall.Retained.stored encode value)
        (IntegerRepresentationExternalCall.Retained.stored encode (.inl 1)) = .ok storedResult)
    (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
        Examples.NativeNaturalCounter.language (Examples.NativeNaturalCounter.counter number) target ↔
      ∃ result, IntegerRepresentationExternalCall.Retained.add encode provider value (.inl 1) = .ok result ∧
        target = Examples.NativeNaturalCounter.counter
          (IntegerRepresentationExternalCall.resultInteger decode result).toNat := by
  have successor (result : Int64 ⊕ Storage)
      (returned : IntegerRepresentationExternalCall.Retained.add encode provider value (.inl 1) = .ok result) :
      (IntegerRepresentationExternalCall.resultInteger decode result).toNat = number + 1 := by
    have exactValue := IntegerRepresentationExternalCall.Retained.add_sound
      encode decode roundtrip provider sound value (.inl 1) result returned
    rw [represents] at exactValue
    have one : IntegerRepresentationExternalCall.resultInteger decode (.inl (1 : Int64)) = 1 := rfl
    rw [one] at exactValue
    rw [exactValue]
    simp
  rw [Examples.NativeNaturalCounter.counter_step_target_iff]
  constructor
  · intro targetEq
    obtain ⟨result, returned⟩ := IntegerRepresentationExternalCall.Retained.add_available
      encode provider value (.inl 1) available
    exact ⟨result, returned, by rw [successor result returned]; exact targetEq⟩
  · rintro ⟨result, returned, targetEq⟩
    simpa only [successor result returned] using targetEq

#print axioms retained_counter_target_iff

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider
