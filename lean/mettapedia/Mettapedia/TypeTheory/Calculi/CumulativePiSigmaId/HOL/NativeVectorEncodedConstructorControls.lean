import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorEncodedConstructor
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorComputationControls
import Mettapedia.TypeTheory.RecursiveSpace

/-!
# Encoded Vec rows in a recursive-tree interpretation

The model interprets the raw constructor by the existing recursive-space
tree constructor and its payload by the actual typed function encoding.
Choice and natural recursion realize the background at all required types.
The original source certificates are reused for the encoded row instance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.EncodedConstructor.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive BaseSort where
  | number | element | space
  deriving DecidableEq

abbrev number : HOL.Ty BaseSort := .base .number
abbrev element : HOL.Ty BaseSort := .base .element
abbrev space : HOL.Ty BaseSort := .base .space
abbrev payload := HOL.FiniteConstructorEncoding.payloadType (HOL.RawVectorConstructors.fields number element)

inductive Const : HOL.Ty BaseSort → Type where
  | zero : Const number
  | successor : Const (number ⇒ number)
  | bottom : Const space
  | construct : Const (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  | select (type : HOL.Ty BaseSort) : Const (HOL.SelectionProofs.Selection type)

def raw : HOL.RawVectorConstructors.Signature BaseSort Const where
  number := number
  element := element
  space := space
  zero := .const .zero
  successor := .const .successor
  bottom := .const .bottom
  construct := .const .construct
  selection := .const (.select (number ⇒ space))

def interface : Interface raw where
  result := number
  recursionSelection := .const (.select (number ⇒ space ⇒ number))
  headSelection := .const (.select element)
  tailSelection := .const (.select space)

def generated := operations raw interface

abbrev Payload := ULift.{1} Prop → (ULift.{1} Nat → ULift.{1} Bool → ULift.{1} Prop) → ULift.{1} Prop

def carrier : BaseSort → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .space => Mettapedia.TypeTheory.RecursiveSpace.Tree Payload

def inhabitant : (sort : BaseSort) → carrier sort
  | .number => ULift.up 0
  | .element => ULift.up false
  | .space => Mettapedia.TypeTheory.RecursiveSpace.bottom

noncomputable def meaning : {type : HOL.Ty BaseSort} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .zero => ULift.up 0
  | _, .successor => fun n => ULift.up (n.down + 1)
  | _, .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
  | _, .construct => fun tag data children =>
      Mettapedia.TypeTheory.RecursiveSpace.construct tag.down data (fun n => children (ULift.up n))
  | _, .select type => HOL.HOLLightStandardTheory.selectionOperation carrier inhabitant type

noncomputable def model : HOL.HenkinModel.{0,0,0} BaseSort Const := .standard carrier meaning

theorem choice_holds (type : HOL.Ty BaseSort) : model.models
    (HOL.SelectionProofs.principle (HOL.Term.const (.select type))) := by
  intro predicate _ witness _ holds
  exact HOL.HOLLightStandardTheory.selectionOperation_specified carrier inhabitant type predicate ⟨witness, holds⟩

theorem recursion_holds (type : HOL.Ty BaseSort) : model.models
    (HOL.NaturalRecursionProofs.statement raw.zero raw.successor type) := by
  intro initial _ step _
  let values : ULift.{1} Nat → HOL.Ty.denote carrier type :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨values, trivial, ?_, ?_⟩
  · apply (model.eqv_iff_eq_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _) _ _).mpr
    rfl
  · intro index _
    apply (model.eqv_iff_eq_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _) _ _).mpr
    rfl

theorem raw_injective : model.models (HOL.ConstructorProjections.fieldInjective raw.construct) := by
  intro tag _ data _ children _ tag' _ data' _ children' _ same
  change Mettapedia.TypeTheory.RecursiveSpace.construct tag'.down data' (fun n => children' (ULift.up n)) =
    Mettapedia.TypeTheory.RecursiveSpace.construct tag.down data (fun n => children (ULift.up n)) at same
  obtain ⟨_, payloads, recursive⟩ := (Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
  have childFunctions : children' = children := by
    funext index
    exact congrFun recursive index.down
  constructor
  · exact (model.eqv_iff_eq_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _) _ _).mpr payloads
  · exact (model.eqv_iff_eq_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _) _ _).mpr childFunctions

theorem background_realizable :
    ∀ formula ∈ closedAssumptions raw interface, model.models formula := by
  intro formula member
  change formula ∈ [HOL.SelectionProofs.principle interface.recursionSelection,
    HOL.NaturalRecursionProofs.statement raw.zero raw.successor (space ⇒ number),
    HOL.SelectionProofs.principle interface.headSelection, HOL.SelectionProofs.principle interface.tailSelection,
    HOL.SelectionProofs.principle raw.selection, HOL.NaturalRecursionProofs.statement raw.zero raw.successor space,
    HOL.ConstructorProjections.fieldInjective raw.construct] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact choice_holds _
  · exact recursion_holds _
  · exact choice_holds _
  · exact choice_holds _
  · exact choice_holds _
  · exact recursion_holds _
  · exact raw_injective

def profile := NativeVectorComputationRows.Controls.profile

def sourceContext : (row : Row) → CCtx Tower.Head (row.parameters generated).length
  | .nil => NativeVectorComputationRows.Controls.sourceContext .nil
  | .cons => NativeVectorComputationRows.Controls.sourceContext .cons

def sourceType : (row : Row) → CTm Tower.Head (row.parameters generated).length
  | .nil => NativeVectorComputationRows.Controls.sourceType .nil
  | .cons => NativeVectorComputationRows.Controls.sourceType .cons

def contextCertificate : (row : Row) → JudgmentReplay.ContextCertificate profile (row.parameters generated).length
  | .nil => NativeVectorComputationRows.Controls.contextCertificate .nil
  | .cons => NativeVectorComputationRows.Controls.contextCertificate .cons

def citedRow (row : Row) : SchemaJudgmentCode.Code Tower.Head (row.parameters generated).length :=
  ⟨row.address.val, List.ofFn CTm.var⟩

def roots (Γ : HOL.Ctx BaseSort) (left right : CTm Tower.Head Γ.length) (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :=
  (AnnotatedPredicateReading.Roots.read? (entries raw interface profile) profile Γ left right code).map
    AnnotatedPredicateReading.Roots.Result.equality

def received (row : Row) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots (row.parameters generated)
    (sourceContext row)
    (liftTm (row.rawLeft generated)) (liftTm (row.rawRight generated))
    (sourceType row)
    (contextCertificate row) (NativeVectorComputationRows.Controls.certificate row)

theorem nil_received : (received .nil).isSome = true := by decide +kernel
theorem cons_received : (received .cons).isSome = true := by decide +kernel

def receipt (row : Row) :=
  AnnotatedPredicateReading.Roots.readReceipt? (entries raw interface profile) profile (row.parameters generated)
    (citedRow row)

theorem original_addresses : (receipt .nil).map (fun result => result.parsed.index.val) = some 2 ∧
    (receipt .cons).map (fun result => result.parsed.index.val) = some 3 := by decide +kernel

theorem constructor_injective_free : (injectivity raw interface []).FunctionExtensionalityFree := injectivity_free raw interface []
theorem row_free : (rowProof raw interface .cons).FunctionExtensionalityFree := rowProof_free raw interface .cons

def nilResult :=
  (AnnotatedPredicateReading.Roots.read? (entries raw interface profile) profile (Row.nil.parameters generated)
    (liftTm (Row.nil.rawLeft generated)) (liftTm (Row.nil.rawRight generated))
    (NativeVectorComputationRows.Controls.citedRow .nil)).get (by decide +kernel)

theorem received_free : nilResult.equality.2.proof.FunctionExtensionalityFree := nilResult.equality_free (entries_free raw interface profile)

theorem disabled_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries raw interface profile) (fun _ => false)
      (Row.cons.parameters generated) (NativeVectorComputationRows.Controls.citedRow .cons)).isNone = true := by decide +kernel

theorem exchanged_fields_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries raw interface profile) profile
      (Row.cons.parameters generated) NativeVectorComputationRows.Controls.exchangedFields).isNone = true := by decide +kernel

def zeroChildImplication : HOL.ProofSyntax Const []
    (.imp (HOL.SelectionProofs.principle raw.selection)
      (.imp (HOL.NaturalRecursionProofs.statement raw.zero raw.successor space)
        (.eq (.app (raw.children raw.nil) raw.zero) raw.nil))) :=
  .impI (.impI (raw.children_zero raw.nil (.hyp 1) (.hyp 0)))

def successorChildImplication : HOL.ProofSyntax Const []
    (.imp (HOL.SelectionProofs.principle raw.selection)
      (.imp (HOL.NaturalRecursionProofs.statement raw.zero raw.successor space)
        (.eq (.app (raw.children raw.nil) (.app raw.successor raw.zero)) raw.bottom))) :=
  .impI (.impI (raw.children_successor raw.nil raw.zero (.hyp 1) (.hyp 0)))

theorem zero_child_proof_free : zeroChildImplication.FunctionExtensionalityFree :=
  raw.children_zero_free raw.nil _ _ True.intro True.intro

theorem successor_child_proof_free : successorChildImplication.FunctionExtensionalityFree :=
  raw.children_successor_free raw.nil raw.zero _ _ True.intro True.intro

theorem zero_child_retains_tail : model.models (.eq (.app (raw.children raw.nil) raw.zero) raw.nil) := by
  have valid := HOL.Soundness.extTheorem_sound zeroChildImplication.erase model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid (choice_holds _) (recursion_holds _)

theorem successor_child_is_bottom : model.models
    (.eq (.app (raw.children raw.nil) (.app raw.successor raw.zero)) raw.bottom) := by
  have valid := HOL.Soundness.extTheorem_sound successorChildImplication.erase model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid (choice_holds _) (recursion_holds _)

def wrongPadding : HOL.ClosedTerm Const (number ⇒ space) := .lam (HOL.weaken raw.nil)

theorem constant_child_padding_refused :
    ¬ model.models (.eq (.app wrongPadding (.app raw.successor raw.zero)) raw.bottom) := by
  change ¬ Mettapedia.TypeTheory.RecursiveSpace.construct 0 _ _ = Mettapedia.TypeTheory.RecursiveSpace.bottom
  exact Mettapedia.TypeTheory.RecursiveSpace.construct_ne_bottom _ _ _

namespace PayloadReadout
open HOL.FiniteConstructorEncoding

def signature : List (List (HOL.Ty BaseSort)) := [[], [.prop, .prop]]
def first : Arguments Const [] [HOL.Ty.prop, .prop] := (.top, .bot, PUnit.unit)
def changed : Arguments Const [] [HOL.Ty.prop, .prop] := (.bot, .top, PUnit.unit)

def observed := observe_field (Const := Const) (Γ := []) (Δ := []) signature ⟨1, by decide⟩ .vz .top first
theorem observed_free : observed.FunctionExtensionalityFree := observe_field_free _ _ _ _ _

def distinct : HOL.ProofSyntax Const [] (.not
    (.eq (encode signature ⟨1, by decide⟩ first) (encode signature ⟨1, by decide⟩ changed))) :=
  .notI (.impE (.eqPropEL (recover_field signature ⟨1, by decide⟩ .vz first changed (.hyp 0))) .topI)

theorem distinct_free : distinct.FunctionExtensionalityFree := by
  exact ⟨recover_field_free _ _ _ _ _ _ True.intro, True.intro⟩

def betaTop : HOL.ClosedFormula Const := .app (.lam (.var .vz)) .top
def betaFields : Arguments Const [] [HOL.Ty.prop, .prop] := (betaTop, .bot, PUnit.unit)

def payloadEqual : HOL.ProofSyntax Const []
    (.eq (encode signature ⟨1, by decide⟩ betaFields) (encode signature ⟨1, by decide⟩ first)) :=
  .eqLam (.eqLam (.eqApp .bot (.eqAppArg (.var .vz) (.beta .top (.var .vz)))))

def recovered : HOL.ProofSyntax Const [] (.eq betaTop .top) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (recover_field signature ⟨1, by decide⟩ .vz betaFields first payloadEqual)
  simp only [argumentAt, betaFields, first]

theorem recovered_free : recovered.FunctionExtensionalityFree := by
  unfold recovered
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply recover_field_free
  simp [payloadEqual, HOL.ProofSyntax.FunctionExtensionalityFree]

end PayloadReadout

#print axioms background_realizable
#print axioms raw_injective
#print axioms nil_received
#print axioms cons_received
#print axioms constructor_injective_free
#print axioms received_free
#print axioms PayloadReadout.distinct
#print axioms PayloadReadout.recovered_free
#print axioms zero_child_retains_tail
#print axioms successor_child_is_bottom
#print axioms constant_child_padding_refused
#print axioms zero_child_proof_free
#print axioms successor_child_proof_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.EncodedConstructor.Controls
