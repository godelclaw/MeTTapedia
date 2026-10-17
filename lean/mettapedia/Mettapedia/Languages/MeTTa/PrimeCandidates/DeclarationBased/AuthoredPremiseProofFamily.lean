import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireDataConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeDiscovery
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseServices
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-!
# Native dependent proof programs for authored source receipts

The source judgments are the original general-rule receipt judgments. The
native target extends the existing wire-data declarations by one opaque
checker constant and a source-authorized computation rule. Its executable
root decoder runs the independently proved total receipt validator.

Each accepted original receipt constructs an actual lambda program typed in
the dependent family `Σ receipt : Data, Id Data (check claim receipt) claim`.
The original request, receipt, declaration positions, premise history and
scope remain in the literal packets. Renaming, substitution, formed types,
program typing, finite beta evidence and exact program-image readback are
proved separately. The native proof service and retained proof-discovery
operation reuse their existing source authority and search.

The executable program-image judgment is exact for original source receipts;
every accepted image also has an actual formed native typing derivation.
This does not assert that unrestricted native typing alone reflects source
receipt validity, or that every ambient inhabitant lies in the compiler image.
The checker admits an explicit computation profile; semantic universe-head
operations are outside its selected finite conversion-code policy. Refusal
of that policy is not a proof of nonconvertibility. The two beta occurrences
measured below exclude receipt validation, copying and machine execution cost.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration

abbrev Claim := GeneralPremiseNativeEvidence.Claim
abbrev Proof := GeneralRuleJobs.Receipt

/-- The same original request packet at any native variable scope. -/
def requestAt (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) : Tower.Tm n :=
  AuthoredPremiseServices.nativeObject GeneralPremiseReceiptWire.requestCodec
    (GeneralPremiseReceiptWire.header scope handler plan bound type, claim)

/-- The same original receipt packet at any native variable scope. -/
def receiptAt (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (proof : Proof) : Tower.Tm n :=
  AuthoredPremiseServices.nativeObject GeneralPremiseReceiptWire.proofCodec
    (GeneralPremiseReceiptWire.header scope handler plan bound type, proof)

@[simp] theorem requestAt_rename (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (rho : Ren n m) (claim : Claim) :
    rename rho (requestAt scope handler plan bound type claim) =
      requestAt scope handler plan bound type claim := by
  simp only [requestAt, AuthoredPremiseServices.nativeObject, NativeWireData.rename_encode]

@[simp] theorem receiptAt_rename (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (rho : Ren n m) (proof : Proof) :
    rename rho (receiptAt scope handler plan bound type proof) =
      receiptAt scope handler plan bound type proof := by
  simp only [receiptAt, AuthoredPremiseServices.nativeObject, NativeWireData.rename_encode]

@[simp] theorem requestAt_subst (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (sigma : Sub Tower.Head n m) (claim : Claim) :
    subst sigma (requestAt scope handler plan bound type claim) =
      requestAt scope handler plan bound type claim := by
  simp only [requestAt, AuthoredPremiseServices.nativeObject, NativeWireData.subst_encode]

@[simp] theorem receiptAt_subst (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (sigma : Sub Tower.Head n m) (proof : Proof) :
    subst sigma (receiptAt scope handler plan bound type proof) =
      receiptAt scope handler plan bound type proof := by
  simp only [receiptAt, AuthoredPremiseServices.nativeObject, NativeWireData.subst_encode]

def checkerName : Lean.Name := .str .anonymous "Prime.AuthoredReceipt.check.v1"

def checking {n : Nat} (request receipt : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const checkerName) request) receipt

/-- The new root's authority is the original receipt relation and literal
source target. It is independent of the executable receipt validator. -/
inductive ReceiptRoot (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | checked {n : Nat} (claim : Claim) (proof : Proof)
      (valid : proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2) :
      ReceiptRoot scope handler dynamic plan bound type
        (checking (requestAt scope handler plan bound type claim)
          (receiptAt scope handler plan bound type proof))
        (requestAt (n := n) scope handler plan bound type claim)

def receiptComputation (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) : RootComputation Tower.Head where
  step := ReceiptRoot scope handler dynamic plan bound type
  rename := by
    intro n m rho left right step
    cases step with
    | checked claim proof valid =>
        simpa only [checking, rename, requestAt_rename, receiptAt_rename] using
          (ReceiptRoot.checked (n := m) (scope := scope) (handler := handler) claim proof valid)
  substitute := by
    intro n m sigma left right step
    cases step with
    | checked claim proof valid =>
        simpa only [checking, subst, requestAt_subst, receiptAt_subst] using
          (ReceiptRoot.checked (n := m) (scope := scope) (handler := handler) claim proof valid)

/-- A finite selected root code retains the exact original claim and receipt;
its decoder runs the original total source checker. -/
def receiptRootDecoder (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    StructuralConversionCode.RootDecoder (receiptComputation scope handler dynamic plan bound type) where
  Code := fun _ => Claim × Proof
  decode := fun {n} (claim, proof) =>
    if GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof then
      some (checking (requestAt scope handler plan bound type claim)
          (receiptAt scope handler plan bound type proof),
        requestAt (n := n) scope handler plan bound type claim)
    else none
  sound := by
    intro n code left right decoded
    rcases code with ⟨claim, proof⟩
    dsimp only at decoded
    split at decoded
    · rename_i accepted
      cases Option.some.inj decoded
      exact .checked claim proof
        ((GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp accepted)
    · cases decoded
  complete := by
    intro n left right step
    cases step with
    | checked claim proof valid =>
        refine ⟨(claim, proof), ?_⟩
        simp only [(GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid,
          ite_true]


/-- The actual one-entry checker declaration extends the existing data rules. -/
def signature (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) : Signature Tower.Head :=
  { Signature.ofList [(checkerName, ⟨NativeWireData.binaryType, none⟩)] with
    computation := receiptComputation scope handler dynamic plan bound type }

def rules (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) : Rules Tower.Head :=
  extendRules NativeWireData.rules (signature scope handler dynamic plan bound type)

private theorem signature_entries (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (name : Lean.Name) :
    (signature scope handler dynamic plan bound type).entries name =
      if name = checkerName then some ⟨NativeWireData.binaryType, none⟩ else none := rfl

theorem signature_no_value (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (name : Lean.Name) :
    (signature scope handler dynamic plan bound type).valueOf? name = none := by
  unfold Signature.valueOf?
  rw [signature_entries]
  split <;> rfl

private theorem data_no_value (name : Lean.Name) : NativeWireData.signature.valueOf? name = none := by
  dsimp only [Signature.valueOf?, NativeWireData.signature]
  by_cases data : name = NativeWireData.dataName
  · simp only [data, ite_true, Option.bind]
  simp only [data, ite_false]
  by_cases binary : name = NativeWireData.applicationName ∨ name = NativeWireData.consName
  · simp only [binary, ite_true, Option.bind]
  simp only [binary, ite_false]
  by_cases nil : name = NativeWireData.nilName
  · simp only [nil, ite_true, Option.bind]
  simp only [nil, ite_false]
  cases name with
  | anonymous => rfl
  | str tag value =>
      by_cases literal : tag = NativeWireData.symbolPrefix ∨ tag = NativeWireData.stringPrefix
      · simp only [literal, ite_true, Option.bind]
      · simp only [literal, ite_false, Option.bind]
  | num tag value =>
      by_cases literal : tag = NativeWireData.naturalPrefix
      · simp only [literal, ite_true, Option.bind]
      · simp only [literal, ite_false, Option.bind]

theorem data_no_root {n : Nat} {left right : Tower.Tm n}
    (step : NativeWireData.rules.computation.step left right) : False := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta value =>
      simp only [data_no_value] at value
      cases value
  | declared impossible => exact impossible.elim

theorem checker_fresh : NativeWireData.rules.constantType checkerName = none := by
  decide

private theorem checker_lookup (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    (rules scope handler dynamic plan bound type).constantType checkerName =
      some NativeWireData.binaryType := by
  change combinedType NativeWireData.rules (signature scope handler dynamic plan bound type) checkerName = _
  apply combinedType_of_signature _ _ checker_fresh
  simp only [Signature.typeOf?, signature_entries, ite_true, Option.map_some]

theorem data_formed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      NativeWireData.dataType (sortTm Tower.zero) :=
  (NativeWireData.dataType_formed context).includeSignature (signature scope handler dynamic plan bound type)

private theorem checkerType_formed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) .nil
      NativeWireData.binaryType (sortTm (.max Tower.zero (.max Tower.zero Tower.zero))) :=
  .piForm (data_formed scope handler dynamic plan bound type _) (.sort _)
    (.piForm (data_formed scope handler dynamic plan bound type _) (.sort _)
      (data_formed scope handler dynamic plan bound type _) (.sort _) (.sorts _ _))
    (.sort _) (.sorts _ _)

/-- Actual declaration formation is earned independently of receipt acceptance. -/
theorem signature_formed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    (signature scope handler dynamic plan bound type).Formed NativeWireData.rules where
  fresh := by
    intro name entry found
    rw [signature_entries] at found
    split at found
    · rename_i same
      rw [same]
      exact checker_fresh
    · cases found
  types := by
    intro name declared found
    unfold Signature.typeOf? at found
    rw [signature_entries] at found
    split at found
    · cases Option.some.inj found
      exact ⟨_, .sort _, (checkerType_formed scope handler dynamic plan bound type).toRaw⟩
    · cases found
  values := by
    intro name declared value _ unfolded
    simp only [signature_no_value] at unfolded
    cases unfolded
  noSelfDelta := by
    intro name value unfolded
    simp only [signature_no_value] at unfolded
    cases unfolded

theorem checker_typed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (.const checkerName) NativeWireData.binaryType := by
  have typed := FormationSensitive.Typing.const (Γ := context)
    (checker_lookup scope handler dynamic plan bound type)
    (checkerType_formed scope handler dynamic plan bound type) (.sort _)
  simpa only [NativeWireData.binaryType, NativeWireData.dataType, liftClosed, rename] using typed

theorem request_typed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (context : Tower.Ctx n) (claim : Claim) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (requestAt scope handler plan bound type claim) NativeWireData.dataType :=
  (NativeWireData.encode_typing context _).includeSignature (signature scope handler dynamic plan bound type)

theorem receipt_typed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (context : Tower.Ctx n) (proof : Proof) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (receiptAt scope handler plan bound type proof) NativeWireData.dataType :=
  (NativeWireData.encode_typing context _).includeSignature (signature scope handler dynamic plan bound type)

/-- The full native root decoder additionally rejects impossible inherited and
transparent-definition roots; only the checker declaration supplies new roots. -/
def nativeRootDecoder (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    StructuralConversionCode.RootDecoder (rules scope handler dynamic plan bound type).computation where
  Code := fun _ => Claim × Proof
  decode := (receiptRootDecoder scope handler dynamic plan bound type).decode
  sound := by
    intro n code left right decoded
    exact .declared ((receiptRootDecoder scope handler dynamic plan bound type).sound code decoded)
  complete := by
    intro n left right step
    cases step with
    | inherited impossible => exact (data_no_root impossible).elim
    | delta value =>
        simp only [signature_no_value] at value
        cases value
    | declared step => exact (receiptRootDecoder scope handler dynamic plan bound type).complete step


/-- Executable receipt evidence never requests a semantic universe-head step. -/
def codeHeadPolicy (_ _ : Tower.Head) : Prop := False
instance decidableCodeHeadPolicy : DecidableRel codeHeadPolicy := fun _ _ => isFalse id

abbrev ConversionCode (n : Nat) := StructuralConversionCode.Code Tower.Head (fun _ => Claim × Proof) n

def rootCode {n : Nat} (claim : Claim) (proof : Proof) : ConversionCode n :=
  .single (.root (claim, proof))

/-- The finite code checks the actual native request/receipt endpoints. -/
theorem rootCode_check (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (claim : Claim) (proof : Proof) :
    StructuralConversionCode.Code.check codeHeadPolicy
      (nativeRootDecoder scope handler dynamic plan bound type).decode
      (rootCode claim proof)
      (checking (requestAt scope handler plan bound type claim)
        (receiptAt scope handler plan bound type proof))
      (requestAt (n := n) scope handler plan bound type claim) =
    GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof := by
  simp only [rootCode, StructuralConversionCode.Code.check,
    StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode,
    nativeRootDecoder, receiptRootDecoder]
  split <;> simp_all

theorem source_root_step (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2) :
    Step (rules scope handler dynamic plan bound type).headEq
      (checking (requestAt scope handler plan bound type claim)
        (receiptAt scope handler plan bound type proof))
      (requestAt (n := n) scope handler plan bound type claim)
      (rules scope handler dynamic plan bound type).computation :=
  .root (.declared (.checked claim proof valid))

/-- An accepted selected executable code earns conversion in the actual native
rules, while rejected head requests make no nonconvertibility assertion. -/
theorem rootCode_sound (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (claim : Claim) (proof : Proof)
    (accepted : StructuralConversionCode.Code.check codeHeadPolicy
      (nativeRootDecoder scope handler dynamic plan bound type).decode
      (rootCode claim proof)
      (checking (requestAt scope handler plan bound type claim)
        (receiptAt scope handler plan bound type proof))
      (requestAt (n := n) scope handler plan bound type claim) = true) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (checking (requestAt scope handler plan bound type claim)
        (receiptAt scope handler plan bound type proof))
      (requestAt (n := n) scope handler plan bound type claim)
      (rules scope handler dynamic plan bound type).computation := by
  rw [rootCode_check] at accepted
  exact .rel _ _ (source_root_step scope handler dynamic plan bound type claim proof
    ((GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp accepted))


open FormationSensitive.DependentComputation

def family (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) : Tower.Tm n :=
  ReceiptPacking.family NativeWireData.dataName (.const checkerName)
    (requestAt scope handler plan bound type claim)

/-- The public native proof program applies one fixed dependent pair program
to the exact source receipt and its checked-computation equality witness. -/
def program (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) (proof : Proof) : Tower.Tm n :=
  .app (.app ReceiptPacking.pack (receiptAt scope handler plan bound type proof))
    (.refl (requestAt scope handler plan bound type claim))

theorem family_formed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (context : Tower.Ctx n) (claim : Claim) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (family scope handler plan bound type claim) (sortTm (.max Tower.zero Tower.zero)) :=
  ReceiptPacking.family_formed NativeWireData.dataName
    (data_formed scope handler dynamic plan bound type .nil) (.sort _) (.sorts _ _)
    (checker_typed scope handler dynamic plan bound type context)
    (request_typed scope handler dynamic plan bound type context claim)

/-- Reflexivity at the returned request inhabits the required checker equality
only after the original valid receipt earns the licensed computation root. -/
theorem equality_witness_typed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (context : Tower.Ctx n) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (.refl (requestAt scope handler plan bound type claim))
      (ReceiptPacking.equalityType NativeWireData.dataName (.const checkerName)
        (requestAt scope handler plan bound type claim) (receiptAt scope handler plan bound type proof)) := by
  have formed := ReceiptPacking.equality_formed NativeWireData.dataName
    (data_formed scope handler dynamic plan bound type .nil) (.sort _)
    (checker_typed scope handler dynamic plan bound type context)
    (request_typed scope handler dynamic plan bound type context claim)
    (receipt_typed scope handler dynamic plan bound type context proof)
  apply FormationSensitive.Typing.conv
    (.reflIntro (request_typed scope handler dynamic plan bound type context claim)) formed (.sort _)
  exact .symm _ _ (.rel _ _ (.congIdLeft
    (source_root_step scope handler dynamic plan bound type claim proof valid)))

/-- Every original valid finite receipt constructs an actually typed native
program in the formed dependent family; no source body surjectivity is used. -/
theorem program_typed (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (context : Tower.Ctx n) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2) :
    FormationSensitive.Typing (rules scope handler dynamic plan bound type) context
      (program scope handler plan bound type claim proof) (family scope handler plan bound type claim) :=
  ReceiptPacking.pack_application_typed NativeWireData.dataName
    (data_formed scope handler dynamic plan bound type .nil)
    (.sort _) (.sort _) (.sort _) (.sort _) (.sorts _ _) (.sorts _ _) (.sorts _ _)
    (checker_typed scope handler dynamic plan bound type context)
    (request_typed scope handler dynamic plan bound type context claim)
    (receipt_typed scope handler dynamic plan bound type context proof)
    (equality_witness_typed scope handler dynamic plan bound type context claim proof valid)

theorem program_judgment (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2) :
    FormationSensitive.Judgment (rules scope handler dynamic plan bound type) context
      (program scope handler plan bound type claim proof) (family scope handler plan bound type claim) :=
  ⟨formed, program_typed scope handler dynamic plan bound type context claim proof valid⟩

theorem program_two_steps (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (claim : Claim) (proof : Proof) :
    ∃ middle, Step (rules scope handler dynamic plan bound type).headEq
      (program scope handler plan bound type claim proof) middle
      (rules scope handler dynamic plan bound type).computation ∧
      Step (rules scope handler dynamic plan bound type).headEq middle
        (.pair (receiptAt (n := n) scope handler plan bound type proof)
          (.refl (requestAt scope handler plan bound type claim)))
        (rules scope handler dynamic plan bound type).computation :=
  ReceiptPacking.pack_two_steps _ _


private def evaluationContext (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : Tower.Ctx 2 :=
  .snoc (.snoc .nil NativeWireData.dataType)
    (ReceiptPacking.receiptBody NativeWireData.dataName (.const checkerName)
      (requestAt (n := 0) scope handler plan bound type claim))

private def evaluationValues {n : Nat} (request receipt : Tower.Tm n) : Sub Tower.Head 2 n :=
  consSub (.refl request) (consSub receipt Fin.elim0)

/-- Reuse the original finite telescope certificate generator for the native
proof program's two beta steps. No source checking occurs in these steps. -/
def evaluationCode (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) (proof : Proof) :
    StructuralConversionCode.Code Tower.Head (fun _ => Empty) n :=
  FormationCheckedTelescopePrograms.applicationCode (evaluationContext scope handler plan bound type claim)
    (evaluationValues (requestAt scope handler plan bound type claim) (receiptAt scope handler plan bound type proof))
    (.pair (.var 1) (.var 0))

theorem evaluationCode_checked (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) (proof : Proof) :
    (evaluationCode scope handler plan bound type claim proof).check codeHeadPolicy
      FormationCheckedTelescopePrograms.noRoot
      (program scope handler plan bound type claim proof)
      (.pair (receiptAt (n := n) scope handler plan bound type proof) (.refl (requestAt scope handler plan bound type claim))) = true := by
  have checked := FormationCheckedTelescopePrograms.applicationCode_checked
    (evaluationContext scope handler plan bound type claim)
    (evaluationValues (requestAt (n := n) scope handler plan bound type claim) (receiptAt scope handler plan bound type proof))
    (.pair (.var 1) (.var 0))
  simp only [evaluationContext, evaluationValues, TelescopeAbstraction.closeTerm,
    TelescopeAbstraction.applyClosed, liftClosed, rename, subst, consSub] at checked
  simp only [← Fin.succ_zero_eq_one] at checked
  simp only [liftRen, Fin.cases_zero, Fin.cases_succ] at checked
  simp only [consSub, Fin.cases_zero] at checked
  simp only [Fin.succ_zero_eq_one] at checked
  convert checked using 1
  rfl

/-- This is a selected beta-occurrence count. Packet decoding, receipt
validation, copying, comparison and host execution time are separate costs. -/
theorem evaluationCode_beta_count (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) (proof : Proof) :
    (evaluationCode (n := n) scope handler plan bound type claim proof).stepCount = 2 :=
  FormationCheckedTelescopePrograms.applicationCode_stepCount _ _ _

/-- This recognizer reads the actual two-application native program and
retains its literal request and receipt arguments. It does not check validity. -/
def readPacked? {n : Nat} : Tower.Tm n → Option (Tower.Tm n × Tower.Tm n)
  | .app (.app head receipt) (.refl request) =>
      if head = ReceiptPacking.pack then some (request, receipt) else none
  | _ => none

def packProgram {n : Nat} (request receipt : Tower.Tm n) : Tower.Tm n :=
  .app (.app ReceiptPacking.pack receipt) (.refl request)

theorem readPacked?_packProgram {n : Nat} (request receipt : Tower.Tm n) :
    readPacked? (packProgram request receipt) = some (request, receipt) := by
  simp only [readPacked?, packProgram, ite_true]

theorem readPacked?_exact {n : Nat} (native request receipt : Tower.Tm n) :
    readPacked? native = some (request, receipt) ↔ native = packProgram request receipt := by
  constructor
  · intro read
    cases native with
    | app function equality =>
        cases function with
        | app head proof =>
            cases equality with
            | refl claim =>
                dsimp only [readPacked?] at read
                split at read
                · rename_i same
                  rcases Prod.mk.inj (Option.some.inj read) with ⟨rfl, rfl⟩
                  simp only [packProgram, same]
                · cases read
            | _ => simp only [readPacked?, reduceCtorEq] at read
        | _ => simp only [readPacked?, reduceCtorEq] at read
    | _ => simp only [readPacked?, reduceCtorEq] at read
  · intro same
    rw [same]
    exact readPacked?_packProgram request receipt

/-- The image checker reuses the original packet readers and original total
receipt checker. A typed data packet does not bypass receipt authority. -/
def readProgram? (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) : Option Proof := do
  let (inside, packet) ← readPacked? native
  if inside = request then
    if AuthoredPremiseServices.check scope handler dynamic plan bound type request packet then
      AuthoredPremiseServices.readProof? scope handler plan bound type packet
    else none
  else none

theorem readProgram?_source (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof) :
    readProgram? scope handler dynamic plan bound type
      (requestAt scope handler plan bound type claim)
      (program scope handler plan bound type claim proof) =
    if GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof then some proof else none := by
  have proofRead := (AuthoredPremiseServices.readProof?_exact scope handler plan bound type
    (AuthoredPremiseServices.proofTerm scope handler plan bound type proof) proof).mpr rfl
  change readProgram? scope handler dynamic plan bound type
    (AuthoredPremiseServices.requestTerm scope handler plan bound type claim)
    (packProgram (AuthoredPremiseServices.requestTerm scope handler plan bound type claim)
      (AuthoredPremiseServices.proofTerm scope handler plan bound type proof)) = _
  simp only [readProgram?, readPacked?_packProgram, Bind.bind, Option.bind, ite_true,
    AuthoredPremiseServices.check_source, proofRead]

theorem readProgram?_exact (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) (proof : Proof) :
    readProgram? scope handler dynamic plan bound type request native = some proof ↔
      ∃ claim : Claim, request = requestAt scope handler plan bound type claim ∧
        native = program scope handler plan bound type claim proof ∧
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  constructor
  · intro accepted
    cases packed : readPacked? native with
    | none => simp only [readProgram?, packed, Bind.bind, Option.bind] at accepted; cases accepted
    | some pair =>
        rcases pair with ⟨inside, packet⟩
        simp only [readProgram?, packed, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i same
          split at accepted
          · rename_i checked
            rcases (AuthoredPremiseServices.check_exact scope handler dynamic plan bound type request packet).mp checked with
              ⟨claim, actual, requestAt, receiptAt, valid⟩
            have actualRead := (AuthoredPremiseServices.readProof?_exact scope handler plan bound type packet actual).mpr receiptAt
            have equal : actual = proof := Option.some.inj (actualRead.symm.trans accepted)
            subst actual
            refine ⟨claim, requestAt, ?_, valid⟩
            have image := (readPacked?_exact native inside packet).mp packed
            rw [same, requestAt, receiptAt] at image
            exact image
          · cases accepted
        · cases accepted
  · rintro ⟨claim, rfl, rfl, valid⟩
    rw [readProgram?_source, (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid]
    rfl


@[simp] theorem family_renaming (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (rho : Ren n m) (claim : Claim) :
    rename rho (family scope handler plan bound type claim) =
      family scope handler plan bound type claim := by
  rw [family, ReceiptPacking.family_rename]
  simp only [rename, requestAt_rename]
  rfl

@[simp] theorem family_substitution (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n m : Nat} (sigma : Sub Tower.Head n m) (claim : Claim) :
    subst sigma (family scope handler plan bound type claim) =
      family scope handler plan bound type claim := by
  rw [family, ReceiptPacking.family_substitute]
  simp only [subst, requestAt_subst]
  rfl

/-- Source receipt occurrence data is not identified by compiling its native
program, even when two receipts happen to prove the same statement. -/
theorem program_injective (scope handler : Lean.Name) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) {n : Nat} (claim : Claim) :
    Function.Injective (program (n := n) scope handler plan bound type claim) := by
  intro first second same
  have packets := congrArg readPacked? same
  change readPacked? (packProgram (requestAt scope handler plan bound type claim)
      (receiptAt scope handler plan bound type first)) =
    readPacked? (packProgram (requestAt scope handler plan bound type claim)
      (receiptAt scope handler plan bound type second)) at packets
  rw [readPacked?_packProgram, readPacked?_packProgram] at packets
  have encoded := congrArg Prod.snd (Option.some.inj packets)
  have decoded := congrArg (AuthoredPremiseServices.readObject? GeneralPremiseReceiptWire.proofCodec) encoded
  simp only [receiptAt, AuthoredPremiseServices.readObject?_nativeObject] at decoded
  exact congrArg Prod.snd (Option.some.inj decoded)

open KernelAuthority SemanticEvidence

/-- The proof object is an actual native program. Its authority retains the
original independently defined receipt judgment through the existing guest. -/
def guest (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    NativeProofSystem (Tower.Tm bound.length) where
  ProofObject := Tower.Tm bound.length
  Judges native request := ∃ packet,
    native = packProgram request packet ∧
    (AuthoredPremiseServices.guest scope handler dynamic plan bound type).Judges packet request

/-- The actual image checker returns only programs whose retained receipt
passes the original total source validator. -/
def checkProgram (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) : Bool :=
  (readProgram? scope handler dynamic plan bound type request native).isSome

theorem checkProgram_exact (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) :
    checkProgram scope handler dynamic plan bound type request native = true ↔
      (guest scope handler dynamic plan bound type).Judges native request := by
  constructor
  · intro accepted
    rcases Option.isSome_iff_exists.mp accepted with ⟨proof, read⟩
    rcases (readProgram?_exact scope handler dynamic plan bound type request native proof).mp read with
      ⟨claim, requestAt, programAt, valid⟩
    refine ⟨receiptAt scope handler plan bound type proof, ?_, claim, proof, requestAt, rfl, valid⟩
    rw [requestAt]
    exact programAt
  · rintro ⟨packet, programAt, claim, proof, requestAt, receiptAt, valid⟩
    apply Option.isSome_iff_exists.mpr
    refine ⟨proof, (readProgram?_exact scope handler dynamic plan bound type request native proof).mpr ?_⟩
    refine ⟨claim, requestAt, ?_, valid⟩
    rw [programAt, requestAt, receiptAt]
    rfl

def kernel (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    NativeProofKernel (guest scope handler dynamic plan bound type) where
  decide := checkProgram scope handler dynamic plan bound type
  correct := checkProgram_exact scope handler dynamic plan bound type

/-- Every accepted image has the declared dependent native type. This theorem
does not assert that all ambient inhabitants belong to the compiler image. -/
theorem accepted_program_judgment (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context)
    (request native : Tower.Tm bound.length)
    (accepted : checkProgram scope handler dynamic plan bound type request native = true) :
    ∃ claim : Claim, request = requestAt scope handler plan bound type claim ∧
      FormationSensitive.Judgment (rules scope handler dynamic plan bound type) context native
        (family scope handler plan bound type claim) := by
  rcases Option.isSome_iff_exists.mp accepted with ⟨proof, read⟩
  rcases (readProgram?_exact scope handler dynamic plan bound type request native proof).mp read with
    ⟨claim, requestAt, programAt, valid⟩
  refine ⟨claim, requestAt, ?_⟩
  rw [programAt]
  exact program_judgment scope handler dynamic plan bound type formed claim proof valid

/-- Existence of a source-valid receipt is equivalent to existence of an
accepted native proof program, with literal original request authority. -/
theorem source_iff_program (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔
      ∃ native : Tower.Tm bound.length,
        checkProgram scope handler dynamic plan bound type
          (requestAt scope handler plan bound type claim) native = true := by
  constructor
  · rintro ⟨proof, valid⟩
    refine ⟨program scope handler plan bound type claim proof, ?_⟩
    change (readProgram? _ _ _ _ _ _ _ _).isSome = true
    rw [readProgram?_source, (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid]
    rfl
  · rintro ⟨native, accepted⟩
    rcases Option.isSome_iff_exists.mp accepted with ⟨proof, read⟩
    rcases (readProgram?_exact scope handler dynamic plan bound type _ native proof).mp read with
      ⟨actual, requestAt, _programAt, valid⟩
    have decoded := congrArg (AuthoredPremiseServices.readObject? GeneralPremiseReceiptWire.requestCodec) requestAt
    simp only [AuthoredPremiseProofFamily.requestAt, AuthoredPremiseServices.readObject?_nativeObject] at decoded
    have same := congrArg Prod.snd (Option.some.inj decoded)
    change claim = actual at same
    rw [same]
    exact ⟨proof, valid⟩


/-- Accepted proof-program fibres retain the original packet service meaning. -/
theorem meaning_exact (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request : Tower.Tm bound.length) :
    (AuthoredPremiseServices.target scope handler dynamic plan bound type).Meaning request ↔
      Nonempty ((guest scope handler dynamic plan bound type).ProofFibre request) := by
  constructor
  · rintro ⟨claim, requestAt, proof, valid⟩
    refine ⟨⟨program scope handler plan bound type claim proof,
      receiptAt scope handler plan bound type proof, ?_, claim, proof, requestAt, rfl, valid⟩⟩
    rw [requestAt]
    rfl
  · rintro ⟨⟨native, packet, _programAt, claim, proof, requestAt, _receiptAt, valid⟩⟩
    exact ⟨claim, requestAt, proof, valid⟩

/-- This service checks actual native proof programs, whose separate typing
theorem places accepted images in the dependent checker-indexed family. -/
def service (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    SemanticService.Service (AuthoredPremiseServices.target scope handler dynamic plan bound type) :=
  .nativeProof (guest scope handler dynamic plan bound type)
    (kernel scope handler dynamic plan bound type) (meaning_exact scope handler dynamic plan bound type)

def invocation (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) :
    SemanticServiceInvocation.Request (service scope handler dynamic plan bound type) :=
  .nativeProof request native

theorem invocation_exact (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (request native : Tower.Tm bound.length) :
    (SemanticServiceInvocation.invoke
      (invocation scope handler dynamic plan bound type request native)).acceptedValue = some request ↔
      (guest scope handler dynamic plan bound type).Judges native request := by
  change (if checkProgram scope handler dynamic plan bound type request native then some request else none) =
    some request ↔ _
  rw [← checkProgram_exact]
  cases checkProgram scope handler dynamic plan bound type request native <;> simp

/-- A receipt-root certificate can also explicitly check the conversion used
by the equality witness, with both dependent type endpoints retained. -/
def equalityCode (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) {n : Nat} (claim : Claim) (proof : Proof) : ConversionCode n :=
  .symm (.single (.congIdLeft NativeWireData.dataType (.root (claim, proof))
    (requestAt scope handler plan bound type claim)))

theorem equalityCode_check (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    (claim : Claim) (proof : Proof) :
    StructuralConversionCode.Code.check codeHeadPolicy
      (nativeRootDecoder scope handler dynamic plan bound type).decode
      (equalityCode scope handler plan bound type claim proof)
      (.id NativeWireData.dataType (requestAt scope handler plan bound type claim)
        (requestAt scope handler plan bound type claim))
      (ReceiptPacking.equalityType NativeWireData.dataName (.const checkerName)
        (requestAt (n := n) scope handler plan bound type claim) (receiptAt scope handler plan bound type proof)) =
    GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof := by
  simp only [equalityCode, StructuralConversionCode.Code.check,
    StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode,
    nativeRootDecoder, receiptRootDecoder]
  split <;> simp_all [StructuralConversionCode.mapEndpoints, StructuralConversionCode.reverseEndpoints,
    ReceiptPacking.equalityType, ReceiptPacking.dataType, NativeWireData.dataType, checking]


/-- This total compiler obtains its source evidence by running the original
validator. Its result carries an actual native judgment, not a validity flag. -/
def compileProgram? (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof) :
    Option {native : Tower.Tm n // FormationSensitive.Judgment
      (rules scope handler dynamic plan bound type) context native (family scope handler plan bound type claim)} :=
  if accepted : GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof then
    some ⟨program scope handler plan bound type claim proof,
      program_judgment scope handler dynamic plan bound type formed claim proof
        ((GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp accepted)⟩
  else none

theorem compileProgram?_value (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof) :
    (compileProgram? scope handler dynamic plan bound type formed claim proof).map Subtype.val =
      if GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof then
        some (program (n := n) scope handler plan bound type claim proof) else none := by
  unfold compileProgram?
  split <;> rfl

/-- The executable compiler accepts exactly original valid receipts and
retains the literal program construction. -/
theorem compileProgram?_exact (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat}
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof) (native : Tower.Tm n) :
    (compileProgram? scope handler dynamic plan bound type formed claim proof).map Subtype.val = some native ↔
      native = program scope handler plan bound type claim proof ∧
      proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  rw [compileProgram?_value]
  by_cases accepted : GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof = true
  · rw [if_pos accepted]
    have valid := (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp accepted
    simp only [Option.some.injEq]
    exact ⟨fun same => ⟨same.symm, valid⟩, fun pair => pair.1.symm⟩
  · rw [if_neg accepted]
    constructor
    · intro impossible; cases impossible
    · intro valid
      exact (accepted ((GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid.2)).elim

/-- Compilation returns a typed native term without accepting a source
correctness proof from its caller. -/
theorem compileProgram?_accepts (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {context : Tower.Ctx bound.length} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof) (native : Tower.Tm bound.length)
    (returned : (compileProgram? scope handler dynamic plan bound type formed claim proof).map Subtype.val = some native) :
    checkProgram scope handler dynamic plan bound type (requestAt scope handler plan bound type claim) native = true := by
  rcases (compileProgram?_exact scope handler dynamic plan bound type formed claim proof native).mp returned with
    ⟨rfl, valid⟩
  apply Option.isSome_iff_exists.mpr
  exact ⟨proof, (readProgram?_exact scope handler dynamic plan bound type _ _ proof).mpr ⟨claim, rfl, rfl, valid⟩⟩

namespace Discovery

/-- The original retained search remains the only search implementation.
Its actual source receipt readout is compiled occurrence by occurrence. -/
def programs (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (budget : Nat) :
    List (Tower.Tm bound.length) :=
  (GeneralPremiseNativeDiscovery.readout (GeneralPremiseNativeDiscovery.search dynamic plan bound type claim budget)).map
    (program scope handler plan bound type claim)

theorem programs_sound (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (budget : Nat)
    {context : Tower.Ctx bound.length} (formed : FormationSensitive.ContextFormation
      (rules scope handler dynamic plan bound type) context)
    (native : Tower.Tm bound.length)
    (found : native ∈ programs scope handler dynamic plan bound type claim budget) :
    checkProgram scope handler dynamic plan bound type (requestAt scope handler plan bound type claim) native = true ∧
      FormationSensitive.Judgment (rules scope handler dynamic plan bound type) context native
        (family scope handler plan bound type claim) := by
  obtain ⟨proof, present, rfl⟩ := List.mem_map.mp found
  have valid := GeneralPremiseNativeDiscovery.search_sound dynamic plan bound type claim budget proof present
  constructor
  · apply Option.isSome_iff_exists.mpr
    exact ⟨proof, (readProgram?_exact scope handler dynamic plan bound type _ _ proof).mpr ⟨claim, rfl, rfl, valid⟩⟩
  · exact program_judgment scope handler dynamic plan bound type formed claim proof valid

/-- Every exact source receipt eventually appears as its own injectively
compiled native program. The input to search contains no proof. -/
theorem receipt_program_discovered (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (target : proof.target = claim.2) :
    program scope handler plan bound type claim proof ∈
      programs scope handler dynamic plan bound type claim (GeneralPremiseNativeDiscovery.discoveryBound proof) :=
  List.mem_map.mpr ⟨proof, GeneralPremiseNativeDiscovery.receipt_discovered dynamic plan bound type claim proof valid target, rfl⟩

theorem programs_nodup (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (budget : Nat) :
    (programs scope handler dynamic plan bound type claim budget).Nodup :=
  (GeneralPremiseNativeDiscovery.search_nodup dynamic plan bound type claim budget).map
    (program_injective scope handler plan bound type claim)

/-- The observation is discovered proof articles, with no assertion that an
empty finite search proves unprovability. -/
theorem source_iff_programs (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔
      ∃ budget, programs scope handler dynamic plan bound type claim budget ≠ [] := by
  rw [GeneralPremiseNativeDiscovery.source_iff_discovery]
  simp only [programs, ne_eq, List.map_eq_nil_iff]

/-- Native operation replies retain their original full journal. This map
adds actual proof programs without rerunning source proof search. -/
def nativePrograms (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (output : GeneralPremiseNativeDiscovery.Output) : List (Tower.Tm bound.length) :=
  (GeneralPremiseNativeDiscovery.discovered output).map (program scope handler plan bound type output.1)

theorem receipt_native_program (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (target : proof.target = claim.2) :
    ∃ output,
      (SemanticServiceInvocation.invoke (GeneralPremiseNativeDiscovery.request dynamic plan bound type
        (claim, GeneralPremiseNativeDiscovery.discoveryBound proof))).acceptedValue = some output ∧
      output.1 = claim ∧ program scope handler plan bound type claim proof ∈ nativePrograms scope handler plan bound type output := by
  refine ⟨(claim, GeneralPremiseNativeDiscovery.discoveryBound proof,
    GeneralPremiseNativeDiscovery.search dynamic plan bound type claim (GeneralPremiseNativeDiscovery.discoveryBound proof)), rfl, rfl, ?_⟩
  simpa only [nativePrograms, GeneralPremiseNativeDiscovery.discovered, programs] using
    receipt_program_discovered scope handler dynamic plan bound type claim proof valid target

abbrev CompiledOutput (bound : List TypeExpr) := GeneralPremiseNativeDiscovery.Output × List (Tower.Tm bound.length)

/-- The retained original journal and the compiled native program list agree
occurrence by occurrence, and every program has the required native judgment. -/
def compiledTarget (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (context : Tower.Ctx bound.length) : AdmissionObject where
  Carrier := CompiledOutput bound
  Meaning output :=
    (GeneralPremiseNativeDiscovery.target dynamic plan bound type).Meaning output.1 ∧
    output.2 = nativePrograms scope handler plan bound type output.1 ∧
    ∀ native ∈ output.2,
      (guest scope handler dynamic plan bound type).Judges native
        (requestAt scope handler plan bound type output.1.1) ∧
      FormationSensitive.Judgment (rules scope handler dynamic plan bound type) context native
        (family scope handler plan bound type output.1.1)

/-- This deterministic postprocessing has no search, rule selection or source
correctness callback. Source authority comes from the original retained output. -/
def compileOutput (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context) :
    AdmissionHom (GeneralPremiseNativeDiscovery.target dynamic plan bound type)
      (compiledTarget scope handler dynamic plan bound type context) where
  run output := (output, nativePrograms scope handler plan bound type output)
  preserves := by
    intro output admitted
    refine ⟨admitted, rfl, ?_⟩
    intro native found
    obtain ⟨proof, present, rfl⟩ := List.mem_map.mp found
    have valid := admitted.2.2.2 proof present
    constructor
    · exact ⟨receiptAt scope handler plan bound type proof, rfl, output.1, proof, rfl, rfl, valid⟩
    · exact program_judgment scope handler dynamic plan bound type formed output.1 proof valid

/-- Actual proof search receives only the original goal and budget. The
existing admitted operation composes with native typed compilation. -/
def operation (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context) :
    AdmissionHom (GeneralPremiseNativeDiscovery.source plan bound type)
      (compiledTarget scope handler dynamic plan bound type context) :=
  (GeneralPremiseNativeDiscovery.operation dynamic plan bound type).comp
    (compileOutput scope handler dynamic plan bound type formed)

def service (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context) :
    SemanticService.Service (compiledTarget scope handler dynamic plan bound type context) :=
  .nativeOperation (GeneralPremiseNativeDiscovery.source plan bound type)
    (operation scope handler dynamic plan bound type formed)

def request (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context)
    (input : GeneralPremiseNativeDiscovery.Query) :
    SemanticServiceInvocation.Request (service scope handler dynamic plan bound type formed) :=
  .nativeOperation input

/-- Original input sorting suffices for sound operation. No proof is an
argument to execution, and finite exhaustion is not unprovability. -/
theorem invocation_sound (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context)
    (input : GeneralPremiseNativeDiscovery.Query)
    (admitted : GeneralPremiseNativeDiscovery.QueryAdmitted plan bound type input.1) :
    (compiledTarget scope handler dynamic plan bound type context).Meaning
      ((operation scope handler dynamic plan bound type formed).run input) :=
  (operation scope handler dynamic plan bound type formed).preserves input admitted

/-- Every independently source-valid finite receipt eventually appears in an
actual native operation's typed program output, without a proof input. -/
theorem receipt_operation_discovered (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation (rules scope handler dynamic plan bound type) context)
    (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (target : proof.target = claim.2) :
    ∃ output : CompiledOutput bound,
      (SemanticServiceInvocation.invoke (request scope handler dynamic plan bound type formed
        (claim, GeneralPremiseNativeDiscovery.discoveryBound proof))).acceptedValue = some output ∧
      program scope handler plan bound type claim proof ∈ output.2 := by
  let sourceOutput : GeneralPremiseNativeDiscovery.Output :=
    (claim, GeneralPremiseNativeDiscovery.discoveryBound proof,
      GeneralPremiseNativeDiscovery.search dynamic plan bound type claim (GeneralPremiseNativeDiscovery.discoveryBound proof))
  refine ⟨(sourceOutput, nativePrograms scope handler plan bound type sourceOutput), rfl, ?_⟩
  simpa only [sourceOutput, nativePrograms, GeneralPremiseNativeDiscovery.discovered, programs] using
    receipt_program_discovered scope handler dynamic plan bound type claim proof valid target

end Discovery

#print axioms evaluationCode_checked
#print axioms program_typed
#print axioms readProgram?_exact
#print axioms program_injective
#print axioms checkProgram_exact
#print axioms accepted_program_judgment
#print axioms source_iff_program
#print axioms invocation_exact
#print axioms equalityCode_check
#print axioms compileProgram?_exact
#print axioms Discovery.programs_sound
#print axioms Discovery.receipt_program_discovered
#print axioms Discovery.receipt_native_program
#print axioms Discovery.compileOutput
#print axioms Discovery.receipt_operation_discovered

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration

/-- The independent semantic root is interpreted by two pure beta steps. The
receipt's validity restricts the source root; erasure need not recheck it. -/
theorem root_projection (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {n : Nat} {first last : Tower.Tm n}
    (step : (rules scope handler dynamic plan bound type).computation.step first last) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (ConstantExpansion.expand (ConstantExpansion.projectConstant checkerName) first)
      (ConstantExpansion.expand (ConstantExpansion.projectConstant checkerName) last) := by
  cases step with
  | inherited impossible => exact (data_no_root impossible).elim
  | delta value =>
      simp only [signature_no_value] at value
      cases value
  | declared declared =>
      cases declared with
      | checked claim proof valid =>
          change Conv Tower.rules.headEq
            (ConstantExpansion.expand (ConstantExpansion.projectConstant checkerName)
              (checking (requestAt scope handler plan bound type claim)
                (receiptAt scope handler plan bound type proof)))
            (ConstantExpansion.expand (ConstantExpansion.projectConstant checkerName)
              (requestAt scope handler plan bound type claim))
          simp only [checking, ConstantExpansion.expand, ConstantExpansion.projectConstant]
          exact ConstantExpansion.firstProjection_application _ _ _

/-- Full ambient native conversion reflects literal equality of original wire
values, including paths through non-image functions and receipt-checking terms. -/
theorem wire_conversion_iff_eq (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {n : Nat} (first last : NativeWireData.Wire) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (NativeWireData.encode (n := n) first) (NativeWireData.encode last)
      (rules scope handler dynamic plan bound type).computation ↔ first = last :=
  NativeWireDataConversion.encode_conversion_iff_eq_of_projection
    (rules scope handler dynamic plan bound type) checkerName checker_fresh
    (root_projection scope handler dynamic plan bound type)
    LevelTower.headEq_symmetric first last

/-- Literal codec payloads remain distinguishable under all ambient native
conversion, not only by the selected executable image reader. -/
theorem object_conversion_iff_eq (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {Value : Type} (codec : Mettapedia.OSLF.Binding.WireCodec.Codec Value)
    {n : Nat} (first last : Value) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (AuthoredPremiseServices.nativeObject (n := n) codec first)
      (AuthoredPremiseServices.nativeObject codec last)
      (rules scope handler dynamic plan bound type).computation ↔ first = last := by
  constructor
  · intro converted
    have payload := (wire_conversion_iff_eq scope handler dynamic plan bound type
      (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.objectWire codec first)
      (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.objectWire codec last)).mp converted
    have literal : AuthoredPremiseServices.nativeObject (n := n) codec first =
        AuthoredPremiseServices.nativeObject codec last := congrArg NativeWireData.encode payload
    have decoded := congrArg (AuthoredPremiseServices.readObject? codec) literal
    simpa only [AuthoredPremiseServices.readObject?_nativeObject, Option.some.injEq] using decoded
  · intro same
    cases same
    exact .refl _

theorem request_conversion_iff_eq (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat} (first last : Claim) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (requestAt (n := n) scope handler plan bound type first)
      (requestAt scope handler plan bound type last)
      (rules scope handler dynamic plan bound type).computation ↔ first = last := by
  simpa only [requestAt, Prod.mk.injEq, true_and] using
    object_conversion_iff_eq scope handler dynamic plan bound type
      GeneralPremiseReceiptWire.requestCodec
      (GeneralPremiseReceiptWire.header scope handler plan bound type, first)
      (GeneralPremiseReceiptWire.header scope handler plan bound type, last) (n := n)

/-- Conversion cannot erase a repeated event, provenance field or other
receipt payload. It reflects the entire original receipt's equality. -/
theorem receipt_conversion_iff_eq (scope handler : Lean.Name) (dynamic : DynamicProvider)
    (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {n : Nat} (first last : Proof) :
    Conv (rules scope handler dynamic plan bound type).headEq
      (receiptAt (n := n) scope handler plan bound type first)
      (receiptAt scope handler plan bound type last)
      (rules scope handler dynamic plan bound type).computation ↔ first = last := by
  simpa only [receiptAt, Prod.mk.injEq, true_and] using
    object_conversion_iff_eq scope handler dynamic plan bound type
      GeneralPremiseReceiptWire.proofCodec
      (GeneralPremiseReceiptWire.header scope handler plan bound type, first)
      (GeneralPremiseReceiptWire.header scope handler plan bound type, last) (n := n)

#print axioms root_projection
#print axioms wire_conversion_iff_eq
#print axioms object_conversion_iff_eq
#print axioms request_conversion_iff_eq
#print axioms receipt_conversion_iff_eq

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily
