import Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic
import Mettapedia.TypeTheory.NaturalRepresentations

/-!
# Natural exact-arithmetic boundary controls

The controls distinguish rejected natural requests from valid negative integer
results, cross the word boundary without wrapping, and reject invented target
values and receipts. Representation comparisons are semantic and do not execute
the material or surreal inverse maps.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic.Controls

open Mettapedia.GSLT.LanguageDef
open ArithmeticExtension.ExactInteger
open ExactArithmeticToExternalCall
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.TypeTheory.NaturalRepresentations

def checks : List (String × Bool) := [
  ("natural addition", evaluate? .add 2 3 == some 5),
  ("natural multiplication", evaluate? .mul 7 8 == some 56),
  ("natural subtraction in domain", evaluate? .sub 8 3 == some 5),
  ("subtraction to zero", evaluate? .sub 8 8 == some 0),
  ("natural underflow is rejected", (evaluate? .sub 2 3).isNone),
  ("underflow remains valid negative integer arithmetic", coreSem .sub 2 3 == .val (-1)),
  ("quotient requires a separate natural policy", (evaluate? .tquot 7 2).isNone),
  ("exact natural wire", readNatural? (.integer 5) == some 5),
  ("negative wire is not natural zero", (readNatural? (.integer (-1))).isNone),
  ("string is not an exact integer wire", (readNatural? (.string "5")).isNone),
  ("successor crosses the word boundary",
    evaluate? .add (UInt64.size - 1) 1 == some UInt64.size),
  ("multiplication is unbounded", evaluate? .mul (2 ^ 80) (2 ^ 80) == some (2 ^ 160))]

theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

#eval checks

theorem natural_subtraction_is_not_monus :
    evaluate? .sub 2 3 = none ∧ (2 - 3 : Nat) = 0 ∧
      coreSem .sub 2 3 = .val (-1) := by
  decide +kernel

theorem wrong_external_result_refused :
    ¬ Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv .add 2 3)
        ExternalCallMachine.externalCallLanguage)
      (compiledExternalCallStart .add 2 3)
      (ExternalCallMachine.halted
        (a "external-call:outcome-value" [exactIntegerValue 6])
        (compiledExternalCallReceipt .add 2 3)) := by
  intro execution
  have reflected := (external_completion_iff (Evaluation.add 2 3) _ _).mp execution
  have different : a "external-call:outcome-value" [exactIntegerValue 6] ≠
      a "external-call:outcome-value" [exactIntegerValue (2 + 3)] := by decide +kernel
  exact different reflected.1

theorem invented_external_receipt_refused :
    ¬ Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv .add 2 3)
        ExternalCallMachine.externalCallLanguage)
      (compiledExternalCallStart .add 2 3)
      (ExternalCallMachine.halted
        (a "external-call:outcome-value" [exactIntegerValue 5])
        (a "invented-receipt")) := by
  intro execution
  have reflected := (external_completion_iff (Evaluation.add 2 3) _ _).mp execution
  have different : a "invented-receipt" ≠ compiledExternalCallReceipt .add 2 3 := by decide +kernel
  exact different reflected.2

theorem fallback_preserves_exact_successor :
    coreSem .add (Int.ofNat (UInt64.size - 1)) 1 =
      .val (Int.ofNat (Backend.advance (UInt64.size - 1))) ∧
      Backend.advance (UInt64.size - 1) = UInt64.size := by
  refine ⟨guarded_backend_exact _, ?_⟩
  rw [Backend.advance_exact]
  decide +kernel

/-- The same exact primitive result agrees with the independently constructed
initial-algebra fold on two materially different natural representations. -/
theorem material_addition :
    representedAdd materialRepresentation
      (materialRepresentation.encode 2) (materialRepresentation.encode 3) =
      materialRepresentation.encode 5 :=
  (exact_add_representation_iff materialRepresentation 2 3 5).mp (by decide +kernel)

theorem surreal_addition :
    representedAdd surrealRepresentation
      (surrealRepresentation.encode 2) (surrealRepresentation.encode 3) =
      surrealRepresentation.encode 5 :=
  (exact_add_representation_iff surrealRepresentation 2 3 5).mp (by decide +kernel)

theorem material_wrong_sum_refused :
    representedAdd materialRepresentation
      (materialRepresentation.encode 2) (materialRepresentation.encode 3) ≠
      materialRepresentation.encode 6 := by
  intro invented
  have exactResult := (exact_add_representation_iff materialRepresentation 2 3 6).mpr invented
  have different : coreSem .add (Int.ofNat 2) (Int.ofNat 3) ≠ .val (Int.ofNat 6) := by
    decide +kernel
  exact different exactResult

end Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmetic.Controls
