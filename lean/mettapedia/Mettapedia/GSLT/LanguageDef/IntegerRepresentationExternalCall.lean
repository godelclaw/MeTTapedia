import Mettapedia.GSLT.LanguageDef.ArithmeticExternalCallPilot
import Mettapedia.GSLT.Dynamics.RepresentationSwitching
import Init.Data.SInt.Lemmas

/-!
# Represented integer providers with a guarded signed fast path

Successful provider calls preserve decoded integers. This obligation alone
does not promise termination or resource availability. Availability on the
requests refused by the fast path is the separate hypothesis needed to derive
the existing external-call hosting contract.

Provider faults remain polymorphic: a realization can retain its existing
language, engine and resource fault vocabulary without another status enum.
The source's declined zero-divisor outcome is produced before dispatch and
is never identified with a provider fault. The concrete fast path uses Lean's
actual signed word addition. Neither it nor the abstract provider theorem
qualifies a C ABI, memory ownership discipline, or GMP implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall

open ArithmeticExternalCallPilot
open Mettapedia.GSLT.Dynamics.RepresentationSwitching

structure Request where
  operation : CompiledOp
  left : Int
  right : Int
  deriving DecidableEq, Repr

def Request.meaning (request : Request) : Int :=
  request.operation.fn request.left request.right

def Request.Defined (request : Request) : Prop :=
  ¬ request.operation.undefinedAt request.right

instance (request : Request) : Decidable request.Defined := by
  unfold Request.Defined
  infer_instance

abbrev FastPath := GuardedTransfer Request.meaning Int64.toInt

/-- Independent provider behavior, including failures. Encoding and decoding
are supplied separately and must satisfy the round-trip theorem below. -/
abbrev Provider (Representation Fault : Type*) :=
  CompiledOp → Representation → Representation → Except Fault Representation

def SuccessfulSound {Representation Fault : Type*} (decode : Representation → Int)
    (provider : Provider Representation Fault) : Prop :=
  ∀ operation left right result,
    ¬ operation.undefinedAt (decode right) →
    provider operation left right = .ok result →
    decode result = operation.fn (decode left) (decode right)

/-- Retaining the alternative in the result makes the selected representation
observable without changing the integer meaning. -/
def dispatch {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (provider : Provider Representation Fault)
    (request : Request) : Except Fault (Int64 ⊕ Representation) :=
  match fast.attempt request with
  | some word => .ok (.inl word)
  | none => (provider request.operation (encode request.left) (encode request.right)).map Sum.inr

def resultInteger {Representation : Type*} (decode : Representation → Int) :
    Int64 ⊕ Representation → Int := Sum.elim Int64.toInt decode

theorem dispatch_success {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (request : Request) (defined : request.Defined) (result : Int64 ⊕ Representation)
    (returned : dispatch fast encode provider request = .ok result) :
    resultInteger decode result = request.meaning := by
  cases attempted : fast.attempt request with
  | some word =>
      simp only [dispatch, attempted] at returned
      cases returned
      exact fast.correct request word attempted
  | none =>
      cases called : provider request.operation (encode request.left) (encode request.right) with
      | error fault => simp [dispatch, attempted, called, Except.map] at returned
      | ok value =>
          simp only [dispatch, attempted, called, Except.map] at returned
          cases returned
          have correct := sound request.operation (encode request.left) (encode request.right)
            value (by rw [roundtrip request.right]; exact defined) called
          rw [roundtrip request.left, roundtrip request.right] at correct
          exact correct

/-- Availability is needed only where the fast path refuses. It asserts a
successful result exists, not what that result means. -/
def FallbackAvailable {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (provider : Provider Representation Fault) : Prop :=
  ∀ request, request.Defined → fast.attempt request = none →
    ∃ result, provider request.operation (encode request.left) (encode request.right) = .ok result

theorem dispatch_available {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (provider : Provider Representation Fault)
    (available : FallbackAvailable fast encode provider)
    (request : Request) (defined : request.Defined) :
    ∃ result, dispatch fast encode provider request = .ok result := by
  cases attempted : fast.attempt request with
  | some word => exact ⟨.inl word, by simp [dispatch, attempted]⟩
  | none =>
      obtain ⟨value, returned⟩ := available request defined attempted
      exact ⟨.inr value, by simp [dispatch, attempted, returned, Except.map]⟩

/-- Only returned values enter the pilot's relation. Faults and source
declines remain distinct observations of `run` below. -/
def successfulExternal {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (provider : Provider Representation Fault) : ExternalCallSpec :=
  fun operation left right value =>
    let request : Request := ⟨operation, left, right⟩
    request.Defined ∧ ∃ result,
      dispatch fast encode provider request = .ok result ∧ resultInteger decode result = value

theorem externalCallAdequacy {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (available : FallbackAvailable fast encode provider) :
    ExternalCallAdequacy (successfulExternal fast encode decode provider) where
  complete := by
    intro operation left right defined
    obtain ⟨result, returned⟩ := dispatch_available fast encode provider available
      ⟨operation, left, right⟩ defined
    exact ⟨defined, result, returned,
      dispatch_success fast encode decode roundtrip provider sound
        ⟨operation, left, right⟩ defined result returned⟩
  sound := by
    rintro operation left right value ⟨defined, result, returned, decoded⟩
    exact decoded.symm.trans
      (dispatch_success fast encode decode roundtrip provider sound
        ⟨operation, left, right⟩ defined result returned)

/-- The unchanged pilot hosting theorem now applies to the assembled machine
path and represented fallback, rather than an assumed adequate value relation. -/
def hostsArithmetic {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (available : FallbackAvailable fast encode provider) :=
  arithHostedByExternalCall
    (externalCallAdequacy fast encode decode roundtrip provider sound available)

def run {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (provider : Provider Representation Fault) (request : Request) :
    Except Fault ArithmeticExtension.ExactInteger.Outcome :=
  if request.operation.undefinedAt request.right then .ok .declined
  else (dispatch fast encode provider request).map fun result => .val (resultInteger decode result)

theorem run_declined_iff {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (provider : Provider Representation Fault) (request : Request) :
    run fast encode decode provider request = .ok .declined ↔
      request.operation.undefinedAt request.right := by
  by_cases undefined : request.operation.undefinedAt request.right
  · simp [run, undefined]
  · cases h : dispatch fast encode provider request <;> simp [run, undefined, h, Except.map]

theorem run_defined {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (available : FallbackAvailable fast encode provider)
    (request : Request) (defined : request.Defined) :
    run fast encode decode provider request = .ok (.val request.meaning) := by
  obtain ⟨result, returned⟩ := dispatch_available fast encode provider available request defined
  have correct := dispatch_success fast encode decode roundtrip provider sound request defined result returned
  simp only [run, if_neg defined, returned, Except.map, correct]

/-- A successful result is justified even when other requests can fail for
resources. No provider availability hypothesis is used. -/
theorem run_compiled_value_sound {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (operation : ArithmeticExtension.ExactInteger.CoreOp) (left right value : Int)
    (returned : run fast encode decode provider ⟨compileSyntax operation, left, right⟩ =
      .ok (.val value)) :
    ArithmeticExtension.ExactInteger.coreSem operation left right = .val value := by
  by_cases undefined : (compileSyntax operation).undefinedAt right
  · simp [run, undefined] at returned
  · cases called : dispatch fast encode provider ⟨compileSyntax operation, left, right⟩ with
    | error fault => simp [run, undefined, called, Except.map] at returned
    | ok result =>
        have correct := dispatch_success fast encode decode roundtrip provider sound
          ⟨compileSyntax operation, left, right⟩ undefined result called
        simp only [run, if_neg undefined, called, Except.map,
          Except.ok.injEq, ArithmeticExtension.ExactInteger.Outcome.val.injEq] at returned
        have sourceDefined : ¬ ArithmeticExtension.ExactInteger.undefinedAt operation right :=
          by simpa only [compileSyntax_undefinedAt] using undefined
        rw [ArithmeticExtension.ExactInteger.coreSem_neg sourceDefined]
        congr 1
        have same : operation.fn left right = resultInteger decode result := by
          simpa only [Request.meaning, compileSyntax_fn] using correct.symm
        exact same.trans returned

theorem run_compiled_eq_core {Representation Fault : Type*} (fast : FastPath)
    (encode : Int → Representation) (decode : Representation → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Representation Fault) (sound : SuccessfulSound decode provider)
    (available : FallbackAvailable fast encode provider)
    (operation : ArithmeticExtension.ExactInteger.CoreOp) (left right : Int) :
    run fast encode decode provider ⟨compileSyntax operation, left, right⟩ =
      .ok (ArithmeticExtension.ExactInteger.coreSem operation left right) := by
  by_cases undefined : ArithmeticExtension.ExactInteger.undefinedAt operation right
  · simp [run, compileSyntax_undefinedAt, undefined, ArithmeticExtension.ExactInteger.coreSem]
  · simpa only [Request.meaning, compileSyntax_fn,
      ArithmeticExtension.ExactInteger.coreSem_neg undefined] using
      run_defined fast encode decode roundtrip provider sound available
        ⟨compileSyntax operation, left, right⟩ (by simpa [Request.Defined] using undefined)

/-! ## Actual signed-word addition on its admitted domain -/

def SignedFits (value : Int) : Prop := -2^63 ≤ value ∧ value < 2^63

instance (value : Int) : Decidable (SignedFits value) := by
  unfold SignedFits
  infer_instance

def signedEncode? (value : Int) : Option Int64 :=
  if SignedFits value then some (Int64.ofInt value) else none

theorem signedEncode?_correct (value : Int) (word : Int64)
    (encoded : signedEncode? value = some word) : word.toInt = value := by
  by_cases fits : SignedFits value
  · simp only [signedEncode?, if_pos fits, Option.some.injEq] at encoded
    subst word
    exact Int64.toInt_ofInt_of_le fits.1 fits.2
  · simp [signedEncode?, fits] at encoded

def signedAddition? (left right : Int64) : Option Int64 :=
  if SignedFits (left.toInt + right.toInt) then some (left + right) else none

theorem signedAddition?_correct (left right result : Int64)
    (added : signedAddition? left right = some result) :
    result.toInt = left.toInt + right.toInt := by
  by_cases fits : SignedFits (left.toInt + right.toInt)
  · simp only [signedAddition?, if_pos fits, Option.some.injEq] at added
    subst result
    rw [Int64.toInt_add]
    exact (Int64.toInt_ofInt (n := left.toInt + right.toInt)).symm.trans
      (Int64.toInt_ofInt_of_le fits.1 fits.2)
  · simp [signedAddition?, fits] at added

/-- Other operations deliberately fall back. The guard is a mathematical
signed-range specification; successful execution uses native word addition.
A C overflow check can refine this guard without changing the provider join. -/
def signedFastAttempt (request : Request) : Option Int64 :=
  match request.operation with
  | .add => do
      let left ← signedEncode? request.left
      let right ← signedEncode? request.right
      signedAddition? left right
  | _ => none

theorem signedFastAttempt_correct (request : Request) (result : Int64)
    (accepted : signedFastAttempt request = some result) : result.toInt = request.meaning := by
  rcases request with ⟨operation, left, right⟩
  cases operation <;> simp only [signedFastAttempt] at accepted
  all_goals try contradiction
  cases leftEncoded : signedEncode? left with
  | none => simp [leftEncoded] at accepted
  | some first =>
      cases rightEncoded : signedEncode? right with
      | none => simp [leftEncoded, rightEncoded] at accepted
      | some second =>
          have added : signedAddition? first second = some result := by
            simpa only [leftEncoded, rightEncoded, bind, Option.bind_some] using accepted
          simpa only [Request.meaning, CompiledOp.fn,
            signedEncode?_correct left first leftEncoded,
            signedEncode?_correct right second rightEncoded] using
            signedAddition?_correct first second result added

def signedFastPath : FastPath where
  attempt := signedFastAttempt
  correct := signedFastAttempt_correct

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall
