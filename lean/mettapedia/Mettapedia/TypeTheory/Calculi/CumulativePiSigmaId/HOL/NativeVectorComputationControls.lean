import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorComputationRows
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.AnnotatedCertificateProducer
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInterpreter
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# Original Vec row admission and a realizable projection profile

The source certificates cite the original nil/cons addresses and include
their complete typed argument premises. The shared interpreter receives
them using the new retained proofs. A full-domain model uses natural numbers,
Boolean elements and Boolean lists; all four background commitments hold.
A projection that always returns the empty list fails the tail commitment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open Programs.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive BaseSort where
  | number | element | vector
  deriving DecidableEq

abbrev number : HOL.Ty BaseSort := .base .number
abbrev element : HOL.Ty BaseSort := .base .element
abbrev vector : HOL.Ty BaseSort := .base .vector

inductive Const : HOL.Ty BaseSort → Type where
  | zero : Const number
  | successor : Const (number ⇒ number)
  | nil : Const vector
  | cons : Const (number ⇒ element ⇒ vector ⇒ vector)
  | head : Const (vector ⇒ element)
  | tail : Const (vector ⇒ vector)
  | selection : Const (HOL.SelectionProofs.Selection (number ⇒ vector ⇒ number))

def operations : Operations BaseSort Const where
  number := number
  element := element
  vector := vector
  result := number
  zero := .const .zero
  successor := .const .successor
  nil := .const .nil
  cons := .const .cons
  head := .const .head
  tail := .const .tail
  selection := .const .selection

def carrier : BaseSort → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .vector => ULift.{1} (List Bool)

def inhabitant : (sort : BaseSort) → carrier sort
  | .number => ULift.up 0
  | .element => ULift.up false
  | .vector => ULift.up []

noncomputable def meaning : {type : HOL.Ty BaseSort} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .zero => ULift.up 0
  | _, .successor => fun n => ULift.up (n.down + 1)
  | _, .nil => ULift.up []
  | _, .cons => fun _ h t => ULift.up (h.down :: t.down)
  | _, .head => fun values => ULift.up (values.down.headD false)
  | _, .tail => fun values => ULift.up values.down.tail
  | _, .selection => HOL.HOLLightStandardTheory.selectionOperation carrier inhabitant (number ⇒ vector ⇒ number)

noncomputable def model : HOL.HenkinModel.{0,0,0} BaseSort Const := .standard carrier meaning

theorem selection_holds : model.models (HOL.SelectionProofs.principle operations.selection) := by
  intro predicate _ witness _ holds
  exact HOL.HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (number ⇒ vector ⇒ number)
    predicate ⟨witness, holds⟩

theorem recursion_holds : model.models
    (HOL.NaturalRecursionProofs.statement operations.zero operations.successor (vector ⇒ number)) := by
  intro initial _ step _
  let values : ULift.{1} Nat → (ULift.{1} (List Bool) → ULift.{1} Nat) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨values, trivial, ?_, ?_⟩
  · intro values _
    rfl
  · intro n _ values _
    rfl

theorem head_holds : model.models operations.headLaw := by
  intro n _ h _ t _
  rfl

theorem tail_holds : model.models operations.tailLaw := by
  intro n _ h _ t _
  rfl

theorem background_realizable :
    ∀ formula ∈ operations.closedAssumptions, model.models formula := by
  intro formula member
  simp only [Operations.closedAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact selection_holds
  · exact recursion_holds
  · exact head_holds
  · exact tail_holds

noncomputable def wrongTailMeaning : {type : HOL.Ty BaseSort} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .tail => fun _ => ULift.up []
  | _, symbol => meaning symbol

noncomputable def wrongTailModel : HOL.HenkinModel.{0,0,0} BaseSort Const := .standard carrier wrongTailMeaning

theorem incorrect_tail_refused : ¬ wrongTailModel.models operations.tailLaw := by
  intro law
  have impossible := law (ULift.up 0) trivial (ULift.up true) trivial (ULift.up [false]) trivial
  cases impossible

def profile : Programs.ComputationProfiles.Selection := fun _ => true

def sourceContext : (row : Row) → CCtx Tower.Head (row.parameters operations).length
  | .nil => Programs.Annotated.context ⟨2, by decide⟩
  | .cons => Programs.Annotated.context ⟨3, by decide⟩

def sourceType : (row : Row) → CTm Tower.Head (row.parameters operations).length
  | .nil => Programs.Annotated.resultType ⟨2, by decide⟩
  | .cons => Programs.Annotated.resultType ⟨3, by decide⟩

def leftCertificate : Row → JudgmentReplay.Certificate profile
  | .nil => by annotated_certificate 5000 (Evidence.left_2 profile)
  | .cons => by annotated_certificate 5000 (Evidence.left_3 profile)

def rightCertificate : Row → JudgmentReplay.Certificate profile
  | .nil => by annotated_certificate 5000 (Evidence.right_2 profile)
  | .cons => by annotated_certificate 5000 (Evidence.right_3 profile)

def contextCertificate : (row : Row) → JudgmentReplay.ContextCertificate profile (row.parameters operations).length
  | .nil => by annotated_context_certificate 5000 (Evidence.context_2 profile)
  | .cons => by annotated_context_certificate 5000 (Evidence.context_3 profile)

def citedRow (row : Row) : SchemaJudgmentCode.Code Tower.Head (row.parameters operations).length :=
  ⟨row.address.val, List.ofFn CTm.var⟩

def certificate (row : Row) : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := sourceContext row) (left := liftTm (row.rawLeft operations))
      (right := liftTm (row.rawRight operations)) (A := sourceType row) (citedRow row))
    ([leftCertificate row, rightCertificate row] ++ List.ofFn fun index : Fin (row.parameters operations).length =>
      JudgmentReplay.Producer.assemble profile (.var (Γ := sourceContext row) index) [])

theorem source_checked (row : Row) : JudgmentReplay.check profile (certificate row)
    (.equality (sourceContext row) (liftTm (row.rawLeft operations)) (liftTm (row.rawRight operations)) (sourceType row)) = true := by
  cases row <;> decide +kernel

theorem context_checked (row : Row) : JudgmentReplay.checkContext profile (sourceContext row) (contextCertificate row) = true := by
  cases row <;> decide +kernel

def roots (Γ : HOL.Ctx BaseSort) (left right : CTm Tower.Head Γ.length) (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :=
  (AnnotatedPredicateReading.Roots.read? (entries operations profile) profile Γ left right code).map
    AnnotatedPredicateReading.Roots.Result.equality

def received (row : Row) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots (row.parameters operations) (sourceContext row)
    (liftTm (row.rawLeft operations)) (liftTm (row.rawRight operations)) (sourceType row)
    (contextCertificate row) (certificate row)

theorem received_nil : (received .nil).isSome = true := by decide +kernel
theorem received_cons : (received .cons).isSome = true := by decide +kernel

theorem nil_proof_free : (Row.nil.proof operations).FunctionExtensionalityFree := Row.proof_free operations .nil
theorem cons_proof_free : (Row.cons.proof operations).FunctionExtensionalityFree := Row.proof_free operations .cons

def countingMethod : HOL.ClosedTerm Const operations.method :=
  .lam (.lam (.lam (.lam (.app (HOL.weakenCtx _ operations.successor) (.var .vz)))))

def choiceProof : HOL.ProofSyntax Const (operations.assumptions [])
    (HOL.SelectionProofs.principle operations.selection) :=
  .hyp ⟨0, by decide⟩

def recursionProof : HOL.ProofSyntax Const (operations.assumptions [])
    (HOL.NaturalRecursionProofs.statement operations.zero operations.successor (vector ⇒ number)) :=
  .hyp ⟨1, by decide⟩

def sampleHead : HOL.ClosedTerm Const element := .app operations.head operations.nil

def headProof := operations.head_at (Δ := operations.assumptions []) operations.zero sampleHead operations.nil
  (HOL.ProofSyntax.hyp (Δ := operations.assumptions []) ⟨2, by decide⟩)

def tailProof := operations.tail_at (Δ := operations.assumptions []) operations.zero sampleHead operations.nil
  (HOL.ProofSyntax.hyp (Δ := operations.assumptions []) ⟨3, by decide⟩)

def zeroComputation := HOL.VectorRecursionProofs.atZero operations.selection operations.zero operations.successor
  operations.head operations.tail operations.zero countingMethod operations.nil choiceProof recursionProof

def consComputation := HOL.VectorRecursionProofs.atCons operations.selection operations.zero operations.successor
  operations.head operations.tail operations.cons operations.zero countingMethod operations.zero sampleHead operations.nil
  choiceProof recursionProof headProof tailProof

theorem zero_computation_free : zeroComputation.FunctionExtensionalityFree :=
  HOL.VectorRecursionProofs.atZero_free operations.selection operations.zero operations.successor
    operations.head operations.tail operations.zero countingMethod operations.nil choiceProof recursionProof
    True.intro True.intro

theorem cons_computation_free : consComputation.FunctionExtensionalityFree := by
  apply HOL.VectorRecursionProofs.atCons_free operations.selection operations.zero operations.successor
    operations.head operations.tail operations.cons operations.zero countingMethod operations.zero sampleHead operations.nil
    choiceProof recursionProof headProof tailProof True.intro True.intro
  · simp [headProof, Operations.head_at, HOL.ProofSyntax.FunctionExtensionalityFree]
  · simp [tailProof, Operations.tail_at, HOL.ProofSyntax.FunctionExtensionalityFree]

/-- Closing an unknown base value commutes with construction of the actual
function-valued recursor; the source method is a nonconstant successor fold. -/
theorem closing_preserves_program :
    HOL.subst (HOL.Subst.single operations.zero)
      (operations.recursion (.var .vz) (HOL.weaken countingMethod)) =
      operations.recursion operations.zero countingMethod := by
  rw [operations.subst_recursion]
  change operations.recursion operations.zero (HOL.instantiate operations.zero (HOL.weaken countingMethod)) = _
  rw [HOL.instantiate_weaken]

def receipt (row : Row) := AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile)
  profile (row.parameters operations) (citedRow row)

theorem original_addresses :
    (receipt .nil).map (fun value => value.parsed.index.val) = some 2 ∧
    (receipt .cons).map (fun value => value.parsed.index.val) = some 3 := by decide +kernel

def weakenedCitation (row : Row) : SchemaJudgmentCode.Code Tower.Head (row.parameters operations).length.succ :=
  ⟨row.address.val, List.ofFn fun index : Fin (row.parameters operations).length => CTm.var index.succ⟩

def weakenedReceipt (row : Row) := AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile)
  profile (operations.number :: row.parameters operations) (weakenedCitation row)

theorem weakened_rows_received (row : Row) : (weakenedReceipt row).isSome = true := by
  cases row <;> decide +kernel

theorem disabled_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile) (fun _ => false)
      (Row.cons.parameters operations) (citedRow .cons)).isNone = true := by decide +kernel

theorem wrong_arity_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile) profile
      (Row.cons.parameters operations) {citedRow .cons with arguments := []}).isNone = true := by decide +kernel

def exchangedFields : SchemaJudgmentCode.Code Tower.Head (Row.cons.parameters operations).length :=
  (⟨3, [.var 1, .var 0, .var 2, .var 3, .var 4, .var 5, .var 6]⟩ : SchemaJudgmentCode.Code Tower.Head 7)

theorem exchanged_carriers_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile) profile
      (Row.cons.parameters operations) exchangedFields).isNone = true := by decide +kernel

theorem changed_endpoint_refused :
    (roots (Row.cons.parameters operations) (liftTm (Row.cons.rawLeft operations)) (.var (0 : Fin 7)) (citedRow .cons)).isNone = true := by
  decide +kernel

def nilResult :=
  (AnnotatedPredicateReading.Roots.read? (entries operations profile) profile (Row.nil.parameters operations)
    (liftTm (Row.nil.rawLeft operations)) (liftTm (Row.nil.rawRight operations)) (citedRow .nil)).get
    (by decide +kernel)

theorem received_proof_free : nilResult.equality.2.proof.FunctionExtensionalityFree :=
  nilResult.equality_free (entries_free operations profile)

def naturalCitation : SchemaJudgmentCode.Code Tower.Head 3 := ⟨0, [.var 0, .var 1, .var 2]⟩

theorem natural_row_decodes : (SchemaJudgmentCode.decodeInstance Checking.table profile naturalCitation).isSome = true := by
  decide +kernel

theorem natural_row_not_supplied :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations profile) profile
      [number, number, number] naturalCitation).isNone = true := by decide +kernel

#print axioms background_realizable
#print axioms incorrect_tail_refused
#print axioms source_checked
#print axioms received_nil
#print axioms received_cons
#print axioms exchanged_carriers_refused
#print axioms closing_preserves_program
#print axioms cons_proof_free
#print axioms received_proof_free
#print axioms zero_computation_free
#print axioms cons_computation_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.Controls
