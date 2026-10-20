import Mettapedia.OSLF.NativeTypes.Instances.Natural.Backend
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationArithmetic
import Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall
import Mettapedia.GSLT.LanguageDef.PeanoExactArithmeticAddBridge

/-!
# Natural requests through the existing exact-integer boundary

Addition, multiplication and domain-checked subtraction reuse the existing
exact-integer operation family, representation declarations and external-call
machine. Natural admission is separate from integer definedness: subtraction
below zero is a valid integer computation but not an admitted natural request.

The external-call theorem retains the existing request-local reference
environment and exact ordered receipt. It does not verify a linked GMP library,
invent a second ABI, or change any MeTTa dialect's arithmetic policy. The actual
authored counter is connected through addition by one; the independently
specified Peano addition relation supplies the broader addition comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic

open Mettapedia.GSLT.LanguageDef
open ArithmeticExtension.ExactInteger
open IntegerRepresentationExtension
open ExactArithmeticToExternalCall
open Mettapedia.TypeTheory.NaturalAlgebra
open Mettapedia.TypeTheory.InductionRecursionBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

def Supported (operation : CoreOp) : Prop :=
  operation = .add ∨ operation = .sub ∨ operation = .mul

def NaturalDomain (operation : CoreOp) (first second : Nat) : Prop :=
  Supported operation ∧ (operation = .sub → second ≤ first)

instance (operation : CoreOp) (first second : Nat) :
    Decidable (NaturalDomain operation first second) := by
  unfold NaturalDomain Supported
  infer_instance

/-- Independent natural rules; subtraction has an explicit domain premise. -/
inductive Evaluation : CoreOp → Nat → Nat → Nat → Prop where
  | add (first second : Nat) : Evaluation .add first second (first + second)
  | mul (first second : Nat) : Evaluation .mul first second (first * second)
  | sub (first second : Nat) (domain : second ≤ first) :
      Evaluation .sub first second (first - second)

def evaluate? : CoreOp → Nat → Nat → Option Nat
  | .add, first, second => some (first + second)
  | .mul, first, second => some (first * second)
  | .sub, first, second => if second ≤ first then some (first - second) else none
  | _, _, _ => none

theorem evaluate?_of_evaluation {operation : CoreOp} {first second result : Nat}
    (evaluation : Evaluation operation first second result) :
    evaluate? operation first second = some result := by
  cases evaluation with
  | add => rfl
  | mul => rfl
  | sub first second domain => simp [evaluate?, domain]

theorem evaluate?_iff (operation : CoreOp) (first second result : Nat) :
    evaluate? operation first second = some result ↔ Evaluation operation first second result := by
  constructor
  · intro computed
    cases operation with
    | add =>
        simp only [evaluate?, Option.some.injEq] at computed
        subst result
        exact .add _ _
    | mul =>
        simp only [evaluate?, Option.some.injEq] at computed
        subst result
        exact .mul _ _
    | sub =>
        by_cases domain : second ≤ first
        · simp only [evaluate?, if_pos domain, Option.some.injEq] at computed
          subst result
          exact .sub _ _ domain
        · simp [evaluate?, domain] at computed
    | tquot | fquot | trem | frem => contradiction
  · exact evaluate?_of_evaluation

theorem evaluate?_admission (operation : CoreOp) (first second : Nat) :
    (evaluate? operation first second).isSome = true ↔ NaturalDomain operation first second := by
  cases operation <;> simp [evaluate?, NaturalDomain, Supported]

theorem Evaluation.exact {operation : CoreOp} {first second result : Nat}
    (evaluation : Evaluation operation first second result) :
    coreSem operation (Int.ofNat first) (Int.ofNat second) = .val (Int.ofNat result) := by
  cases evaluation with
  | add => simp [coreSem, undefinedAt, CoreOp.isPartial, CoreOp.fn]
  | mul => simp [coreSem, undefinedAt, CoreOp.isPartial, CoreOp.fn]
  | sub first second domain =>
      simp [coreSem, undefinedAt, CoreOp.isPartial, CoreOp.fn, Int.ofNat_sub domain]

/-- No integer result is rounded or truncated into a natural result. On the
selected operations, every exact nonnegative result reflects a natural rule. -/
theorem exact_iff (operation : CoreOp) (supported : Supported operation)
    (first second result : Nat) :
    coreSem operation (Int.ofNat first) (Int.ofNat second) = .val (Int.ofNat result) ↔
      Evaluation operation first second result := by
  constructor
  · intro computed
    rcases supported with rfl | rfl | rfl
    · have addition :=
        (PeanoExactArithmeticAddBridge.nativeNatAdd_iff first second result).mp computed
      subst result
      exact .add _ _
    · simp only [coreSem, undefinedAt, CoreOp.isPartial, Bool.false_eq_true,
        false_and, if_false, CoreOp.fn, Outcome.val.injEq, Int.ofNat_eq_natCast] at computed
      have domain : second ≤ first := by omega
      have resultEq : result = first - second := by omega
      subst result
      exact .sub _ _ domain
    · simp only [coreSem, undefinedAt, CoreOp.isPartial, Bool.false_eq_true,
        false_and, if_false, CoreOp.fn, Outcome.val.injEq, Int.ofNat_eq_natCast] at computed
      have equal : first * second = result := Int.ofNat_inj.mp
        (by simpa only [Int.ofNat_eq_natCast, Int.natCast_mul] using computed)
      subst result
      exact .mul _ _
  · exact Evaluation.exact

theorem peano_add_iff (first second result : Nat) :
    PeanoAddSpecialization.AddRel PeanoExactArithmeticAddBridge.Symbol.zero
      PeanoExactArithmeticAddBridge.Symbol.successor
      (PeanoExactArithmeticAddBridge.numeral first)
      (PeanoExactArithmeticAddBridge.numeral second)
      (PeanoExactArithmeticAddBridge.numeral result) ↔
    Evaluation .add first second result :=
  (PeanoExactArithmeticAddBridge.peanoAdd_iff_nativeNatAdd first second result).trans
    (exact_iff .add (Or.inl rfl) first second result)

/-- This is an existing structured coGSLT declaration, not new parser syntax. -/
def registry : Registry :=
  ⟨[{ name := "natural-exact", profile := .exact }], by decide⟩

theorem representation_admitted :
    representationLayer.elaborate standardTheory (quoteRegistry registry) = some registry :=
  elaborate?_quote registry

/-- Read the admitted exact profile first, then check the natural domain. -/
def readNatural? (wire : ModuleFormat.Value) : Option Nat := do
  let outcome ← readAuthored? (quoteRegistry registry) "natural-exact" wire
  match outcome with
  | .value integer false => if 0 ≤ integer then some integer.toNat else none
  | _ => none

private theorem readAuthored_registry (wire : ModuleFormat.Value) :
    readAuthored? (quoteRegistry registry) "natural-exact" wire = readValue? .exact wire := by
  simp only [readAuthored?, elaborate?_quote, bind, Option.bind_some]
  have lookup : lookup? registry "natural-exact" = some .exact := by decide +kernel
  rw [lookup]
  rfl

theorem readNatural?_integer (integer : Int) :
    readNatural? (.integer integer) = if 0 ≤ integer then some integer.toNat else none := by
  simp only [readNatural?, readAuthored_registry, readValue?, bind, Option.bind_some]

theorem readNatural?_encoded (number : Nat) :
    readNatural? (encodeValue .exact (Int.ofNat number)) = some number := by
  rw [show encodeValue .exact (Int.ofNat number) = .integer (Int.ofNat number) from rfl,
    readNatural?_integer]
  simp

theorem readNatural?_iff (wire : ModuleFormat.Value) (number : Nat) :
    readNatural? wire = some number ↔ wire = encodeValue .exact (Int.ofNat number) := by
  cases wire with
  | integer integer =>
      rw [readNatural?_integer]
      by_cases nonnegative : 0 ≤ integer
      · simp only [nonnegative, if_true, Option.some.injEq, encodeValue, ModuleFormat.Value.integer.injEq, Int.ofNat_eq_natCast]
        omega
      · simp only [if_neg nonnegative, reduceCtorEq, encodeValue, ModuleFormat.Value.integer.injEq]
        constructor
        · exact False.elim
        · intro equality
          apply nonnegative
          rw [equality]
          simpa only [Int.ofNat_eq_natCast] using (Int.natCast_nonneg number)
  | record | list | string | bytes | floatBits | boolean | nil =>
      simp [readNatural?, readAuthored_registry, readValue?, encodeValue]

/-- The existing target machine reaches exactly the natural result and its
ordered external-call receipt. No implementation-correctness field is added. -/
theorem external_completion_iff {operation : CoreOp} {first second result : Nat}
    (evaluation : Evaluation operation first second result) (outcome receipt : Pattern) :
    Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        ExternalCallMachine.externalCallLanguage)
      (compiledExternalCallStart operation first second)
      (ExternalCallMachine.halted outcome receipt) ↔
    outcome = a "external-call:outcome-value" [exactIntegerValue result] ∧
      receipt = compiledExternalCallReceipt operation first second := by
  have correctOutcome : compiledExternalCallOutcome operation first second =
      a "external-call:outcome-value" [exactIntegerValue result] := by
    rw [compiledExternalCallOutcome_commutes]
    have exactResult := evaluation.exact
    simp only [Int.ofNat_eq_natCast] at exactResult
    rw [exactResult]
  constructor
  · intro execution
    obtain ⟨outcomeEq, receiptEq⟩ :=
      compiledExternalCall_halted_no_invention operation first second outcome receipt execution
    exact ⟨outcomeEq.trans correctOutcome, receiptEq⟩
  · rintro ⟨rfl, rfl⟩
    have path := compiledExternalCall_reaches_declared_done operation first second
    change Relation.ReflTransGen _ _
      (ExternalCallMachine.halted (compiledExternalCallOutcome operation first second)
        (compiledExternalCallReceipt operation first second)) at path
    rw [correctOutcome] at path
    exact path

/-- The module's arbitrary target is its unique counter successor exactly
when the imported exact-integer request has that result. -/
theorem authored_successor_iff
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (number result : Nat) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
      Examples.NativeNaturalCounter.language (Examples.NativeNaturalCounter.counter number)
      (Examples.NativeNaturalCounter.counter result) ↔
    coreSem .add (Int.ofNat number) 1 = .val (Int.ofNat result) := by
  rw [Examples.NativeNaturalCounter.counter_step_iff]
  exact (PeanoExactArithmeticAddBridge.nativeNatAdd_iff number 1 result).symm

/-- Arbitrary authored targets cannot escape the natural-counter image. -/
theorem authored_target_iff
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (number : Nat) (target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
      Examples.NativeNaturalCounter.language (Examples.NativeNaturalCounter.counter number) target ↔
    ∃ result : Nat, coreSem .add (Int.ofNat number) 1 = .val (Int.ofNat result) ∧
      target = Examples.NativeNaturalCounter.counter result := by
  rw [Examples.NativeNaturalCounter.counter_step_target_iff]
  constructor
  · intro targetEq
    exact ⟨number + 1, (Evaluation.add number 1).exact, targetEq⟩
  · rintro ⟨result, computed, targetEq⟩
    have resultEq :=
      (PeanoExactArithmeticAddBridge.nativeNatAdd_iff number 1 result).mp computed
    simpa only [resultEq] using targetEq

theorem guarded_backend_exact (number : Nat) :
    coreSem .add (Int.ofNat number) 1 = .val (Int.ofNat (Backend.advance number)) := by
  rw [Backend.advance_exact]
  exact (Evaluation.add number 1).exact

universe u
variable {Carrier : Type u} {algebra : Algebra Carrier}

/-- Addition constructed by the initial algebra's fold, not by decoding the
carrier and calling integer arithmetic. This semantic inverse is not executable. -/
noncomputable def representedAdd (representation : Representation algebra)
    (first second : Carrier) : Carrier :=
  representation.foldHom ⟨second, algebra.succ⟩ first

theorem representedAdd_encode (representation : Representation algebra) (first second : Nat) :
    representedAdd representation (representation.encode first) (representation.encode second) =
      representation.encode (first + second) := by
  unfold representedAdd
  rw [Representation.foldHom_encode]
  induction first with
  | zero => simp [natFold]
  | succ first ih =>
      simp only [natFold, ih, Nat.succ_add, representation.map_succ]

theorem exact_add_representation_iff (representation : Representation algebra)
    (first second result : Nat) :
    coreSem .add (Int.ofNat first) (Int.ofNat second) = .val (Int.ofNat result) ↔
    representedAdd representation (representation.encode first) (representation.encode second) =
      representation.encode result := by
  rw [representedAdd_encode, representation.bijective.1.eq_iff]
  exact (PeanoExactArithmeticAddBridge.nativeNatAdd_iff first second result).trans eq_comm

end Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic
