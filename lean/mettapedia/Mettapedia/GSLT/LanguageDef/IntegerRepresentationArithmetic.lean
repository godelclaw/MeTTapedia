import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension

/-!
# Arithmetic correspondence on shared integer domains

Representation equality is not operation equality. This module relates the
existing exact operation family to C arithmetic only where the mathematical
result and the required quotient fit the already-promoted operand format.
The operation relation is independent of both executable evaluators. Finite
representations still have their own overflow and conversion rules outside
that domain; floor and truncating quotients remain different operations.

The constructed step realization compiles admitted requests into actual
`IntegerStep.ConfigurationData`. Its artifact observation executes the
independently qualified C step and retains undefined outcomes as faults.
This numeric reduction is neither an enclosing C expression step nor a native
compiler/ABI correspondence. The source-provider bridge concerns its selected
exact-integer addition fragment, not full MeTTa evaluation or an MM0 kernel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationArithmetic

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension
open Mettapedia.Languages.C11

/-- Independent mathematical rules for the shared exact operation family. -/
inductive ExactEvaluation (operation : CoreOp) (left right : Int) : Outcome → Prop where
  | value (defined : ¬ undefinedAt operation right) :
      ExactEvaluation operation left right (.val (operation.fn left right))
  | declined (undefined : undefinedAt operation right) :
      ExactEvaluation operation left right .declined

theorem coreSem_sound (operation : CoreOp) (left right : Int) :
    ExactEvaluation operation left right (coreSem operation left right) := by
  by_cases undefined : undefinedAt operation right
  · simpa only [coreSem, if_pos undefined] using ExactEvaluation.declined (left := left) undefined
  · simpa only [coreSem, if_neg undefined] using ExactEvaluation.value (left := left) undefined

theorem coreSem_complete (operation : CoreOp) (left right : Int) (outcome : Outcome)
    (evaluated : ExactEvaluation operation left right outcome) :
    coreSem operation left right = outcome := by
  cases evaluated with
  | value defined => exact coreSem_neg defined left
  | declined undefined => exact coreSem_pos undefined left

theorem coreSem_iff (operation : CoreOp) (left right : Int) (outcome : Outcome) :
    coreSem operation left right = outcome ↔ ExactEvaluation operation left right outcome := by
  constructor
  · intro same
    rw [← same]
    exact coreSem_sound operation left right
  · exact coreSem_complete operation left right outcome

def exactOperation : IntegerBinaryOperator → CoreOp
  | .add => .add
  | .subtract => .sub
  | .multiply => .mul
  | .divide => .tquot
  | .remainder => .trem

def mathematical (operation : IntegerBinaryOperator) (left right : Int) : Int :=
  (exactOperation operation).fn left right

/-- Besides result representability, both C division and remainder require a
nonzero divisor and a representable quotient. This excludes minimum / -1
even when the mathematical remainder itself is representable. -/
def CommonDomain (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) : Prop :=
  ((operation = .divide ∨ operation = .remainder) →
    right.value ≠ 0 ∧ format.Represents (left.value.tdiv right.value)) ∧
  format.Represents (mathematical operation left.value right.value)

instance (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) : Decidable (CommonDomain format operation left right) := by
  unfold CommonDomain
  infer_instance

theorem CommonDomain.defined (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (domain : CommonDomain format operation left right) :
    ¬ undefinedAt (exactOperation operation) right.value := by
  cases operation with
  | add | subtract | multiply => simp [exactOperation, undefinedAt, CoreOp.isPartial]
  | divide =>
      have nonzero := (domain.1 (Or.inl rfl)).1
      simp [exactOperation, undefinedAt, CoreOp.isPartial, nonzero]
  | remainder =>
      have nonzero := (domain.1 (Or.inr rfl)).1
      simp [exactOperation, undefinedAt, CoreOp.isPartial, nonzero]

theorem ArithmeticReduction.within (format : IntegerFormat) (value : Int)
    (fits : format.Represents value) : ArithmeticReduction format value (.value value) := by
  cases format with
  | unsigned precision positive =>
      exact .unsigned precision positive value value fits ⟨0, by simp⟩
  | signed precision positive representation =>
      exact .signedWithin precision positive representation value fits

theorem binary_within (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (domain : CommonDomain format operation left right) :
    IntegerBinaryEvaluation format left right operation
      (.value (mathematical operation left.value right.value)) := by
  cases operation with
  | add => exact .add _ (ArithmeticReduction.within format _ domain.2)
  | subtract => exact .subtract _ (ArithmeticReduction.within format _ domain.2)
  | multiply => exact .multiply _ (ArithmeticReduction.within format _ domain.2)
  | divide =>
      obtain ⟨nonzero, quotientFits⟩ := domain.1 (Or.inl rfl)
      have division := divideIntegers_sound left.value right.value
        (left.value.tdiv right.value) (left.value.tmod right.value)
        (by simp [divideIntegers, nonzero])
      exact .divide _ (.computed _ _ division quotientFits _
        (ArithmeticReduction.within format _ domain.2))
  | remainder =>
      obtain ⟨nonzero, quotientFits⟩ := domain.1 (Or.inr rfl)
      have division := divideIntegers_sound left.value right.value
        (left.value.tdiv right.value) (left.value.tmod right.value)
        (by simp [divideIntegers, nonzero])
      exact .remainder _ (.computed _ _ division quotientFits _
        (ArithmeticReduction.within format _ domain.2))

theorem evaluateIntegerBinary_within (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (domain : CommonDomain format operation left right) :
    evaluateIntegerBinary format operation left right =
      .value (mathematical operation left.value right.value) :=
  evaluateIntegerBinary_complete format operation left right _
    (binary_within format operation left right domain)

theorem coreSem_within (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (domain : CommonDomain format operation left right) :
    coreSem (exactOperation operation) left.value right.value =
      .val (mathematical operation left.value right.value) :=
  coreSem_neg (domain.defined format operation left right) left.value

/-- Two-sided arithmetic correspondence on the explicit common domain. -/
theorem exact_iff_binary (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) (domain : CommonDomain format operation left right)
    (value : Int) :
    ExactEvaluation (exactOperation operation) left.value right.value (.val value) ↔
      IntegerBinaryEvaluation format left right operation (.value value) := by
  rw [← coreSem_iff, ← evaluateIntegerBinary_iff,
    coreSem_within format operation left right domain,
    evaluateIntegerBinary_within format operation left right domain]
  simp

/-- The actual numeric configuration codec retains operands, format and op. -/
def compile (format : IntegerFormat) (operation : IntegerBinaryOperator)
    (left right : IntegerValue format) : IntegerStep.ConfigurationData :=
  IntegerStep.encode (.pending (.binary format operation left right))

def arithmeticObservation : IntegerArithmeticOutcome → Outcome ⊕ ArithmeticFault
  | .value value => .inl (.val value)
  | .undefined fault => .inr fault

def observeStep? (policy : SignedConversionPolicy)
    (wire : IntegerStep.ConfigurationData) : Option (Outcome ⊕ ArithmeticFault) := do
  let next ← IntegerStep.stepData policy wire
  let configuration ← IntegerStep.decode next
  match configuration with
  | .completed (.binary outcome) => some (arithmeticObservation outcome)
  | _ => none

theorem compiled_step (policy : SignedConversionPolicy) (format : IntegerFormat)
    (operation : IntegerBinaryOperator) (left right : IntegerValue format)
    (domain : CommonDomain format operation left right) :
    IntegerStep.stepData policy (compile format operation left right) =
      some (IntegerStep.encode (.completed (.binary
        (.value (mathematical operation left.value right.value))))) :=
  IntegerStep.stepData_complete policy _ _
    (.binary format operation left right _ (binary_within format operation left right domain))

theorem observeStep?_compiled (policy : SignedConversionPolicy) (format : IntegerFormat)
    (operation : IntegerBinaryOperator) (left right : IntegerValue format)
    (domain : CommonDomain format operation left right) :
    observeStep? policy (compile format operation left right) =
      some (.inl (.val (mathematical operation left.value right.value))) := by
  simp only [observeStep?, compiled_step policy format operation left right domain,
    bind, Option.bind_some, IntegerStep.decode_encode, arithmeticObservation]

abbrev AdmittedRequest (format : IntegerFormat) :=
  Σ operation : IntegerBinaryOperator,
    { operands : IntegerValue format × IntegerValue format //
      CommonDomain format operation operands.1 operands.2 }

/-- A constructed staged realization; target arithmetic is observed only
after the actual represented C transition has executed. -/
def boundedStepRealization (policy : SignedConversionPolicy) :
    Mettapedia.GSLT.Realization AdmittedRequest (fun _ => IntegerStep.ConfigurationData)
      (fun _ => Option (Outcome ⊕ ArithmeticFault)) where
  compile := fun format request => compile format request.1 request.2.1.1 request.2.1.2
  observeSource := fun _ request =>
    some (.inl (coreSem (exactOperation request.1) request.2.1.1.value request.2.1.2.value))
  observeArtifact := fun _ => observeStep? policy
  adequate := by
    intro format request
    rw [observeStep?_compiled policy format request.1 request.2.1.1 request.2.1.2 request.2.2,
      coreSem_within format request.1 request.2.1.1 request.2.1.2 request.2.2]

theorem represented_result_readback (format : IntegerFormat) (mode : IntegerBits.NegativeZero)
    (operation : IntegerBinaryOperator) (left right : IntegerValue format)
    (domain : CommonDomain format operation left right) :
    readValue? (.bounded format mode)
      (encodeValue (.bounded format mode)
        ⟨mathematical operation left.value right.value, domain.2⟩) =
      some (.value (mathematical operation left.value right.value) false) :=
  readValue?_encode (.bounded format mode) _

/-- The selected source provider consumes the shared exact addition meaning.
Both operand derivations may concern arbitrarily nested source expressions. -/
theorem source_provider_add (env : Mettapedia.GSLT.Parsing.SourceIntegerProvider.Env)
    (left right : Algorithms.MeTTa.Simple.Parser.SExpr) (first second : Int)
    (leftValue : Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval env left first)
    (rightValue : Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval env right second) :
    Mettapedia.GSLT.Parsing.SourceIntegerProvider.IntegerEval env
        (.list [.atom "+", left, right]) (first + second) ∧
      ExactEvaluation .add first second (.val (first + second)) := by
  exact ⟨.add leftValue rightValue,
    .value (by simp [undefinedAt, CoreOp.isPartial])⟩

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationArithmetic
