import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalVectorProfile
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityInterpreterControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextConcatenation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# Original Nat and Vec computations in one checked context

The two independent parameter telescopes embed into one formed context with
an open combining function. Its two arguments contain a natural and a vector
computation respectively; application congruence retains both dependencies.
Source certificates and guarded context reading are checked independently.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorProfile.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr

abbrev BaseSort := NativeVectorComputationRows.EncodedConstructor.Controls.BaseSort
abbrev Const := NativeVectorComputationRows.EncodedConstructor.Controls.Const
def raw := NativeVectorComputationRows.EncodedConstructor.Controls.raw
def vectorInterface := NativeVectorComputationRows.EncodedConstructor.Controls.interface
def naturalSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (raw.number ⇒ vectorInterface.result)) :=
  .const (.select (raw.number ⇒ vectorInterface.result))
def naturalOps := natural raw vectorInterface naturalSelection
def vectorOps := vector raw vectorInterface
def profile : Programs.ComputationProfiles.Selection := fun _ => true
def lex := lexical raw vectorInterface naturalSelection
def roots (Γ : HOL.Ctx BaseSort) (left right : CTm Tower.Head Γ.length)
    (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :=
  (AnnotatedPredicateReading.Roots.read? (entries raw vectorInterface naturalSelection profile) profile Γ left right code).map
    AnnotatedPredicateReading.Roots.Result.equality

def naturalContext : CCtx Tower.Head 3 := Programs.Annotated.context ⟨0, by decide⟩
def vectorContext : CCtx Tower.Head 4 := Programs.Annotated.context ⟨2, by decide⟩
def bothContext : CCtx Tower.Head 7 := CCtx.appendOlder naturalContext vectorContext

def naturalType : CTm Tower.Head 7 := (Programs.Annotated.resultType ⟨0, by decide⟩).rename (CCtx.older 3 4)
def vectorType : CTm Tower.Head 7 := (Programs.Annotated.resultType ⟨2, by decide⟩).rename (CCtx.younger 3 4)
def functionType : CTm Tower.Head 7 := .pi naturalType ((CTm.pi vectorType (.const natName)).rename wk)
def sourceContext : CCtx Tower.Head 8 := .snoc bothContext functionType

def natPlacement : Ren 3 8 := fun index => wk (CCtx.older 3 4 index)
def vecPlacement : Ren 4 8 := fun index => wk (CCtx.younger 3 4 index)

theorem natural_placement : CCtxRen naturalContext sourceContext natPlacement :=
  placement_succ (CCtx.older_compatible naturalContext vectorContext) functionType

theorem vector_placement : CCtxRen vectorContext sourceContext vecPlacement :=
  placement_succ (CCtx.younger_compatible naturalContext vectorContext) functionType

theorem both_formed : CCtxFormed (Programs.Annotated.church profile) bothContext :=
  (Programs.Annotated.Evidence.context_0 profile).appendOlder
    (Programs.Annotated.Evidence.context_2 profile)

theorem natural_type_formed : CIsType (Programs.Annotated.church profile) bothContext naturalType :=
  ((Programs.Annotated.Evidence.left_0 profile).isType
    (Programs.Annotated.levelModel profile) (Programs.Annotated.Evidence.context_0 profile)).rename
    (CCtx.older_compatible naturalContext vectorContext)

theorem vector_type_formed : CIsType (Programs.Annotated.church profile) bothContext vectorType :=
  ((Programs.Annotated.Evidence.left_2 profile).isType
    (Programs.Annotated.levelModel profile) (Programs.Annotated.Evidence.context_2 profile)).rename
    (CCtx.younger_compatible naturalContext vectorContext)

theorem natural_formed {n : Nat} (context : CCtx Tower.Head n) :
    CIsType (Programs.Annotated.church profile) context (.const natName) := by
  exact ⟨.sort Tower.zero, by decide +kernel, .const (name := natName)
    (type := CTm.head (.sort Tower.zero : Tower.Head)) (u := (.sort (.succ Tower.zero) : Tower.Head))
    (by rw [Programs.Annotated.constantType_eq profile]; decide +kernel)
    (.headType (by decide +kernel)) (by decide +kernel)⟩

theorem source_formed : CCtxFormed (Programs.Annotated.church profile) sourceContext := by
  apply CCtxFormed.snoc both_formed
  exact CIsType.pi (Programs.Annotated.levelModel profile) natural_type_formed
    ((CIsType.pi (Programs.Annotated.levelModel profile) vector_type_formed
      (natural_formed (.snoc bothContext vectorType))).rename (CCtxRen.wk bothContext naturalType))

def natLeft : CTm Tower.Head 8 := (liftTm (Programs.Annotated.left ⟨0, by decide⟩)).rename natPlacement
def natRight : CTm Tower.Head 8 := (liftTm (Programs.Annotated.right ⟨0, by decide⟩)).rename natPlacement
def vecLeft : CTm Tower.Head 8 := (liftTm (Programs.Annotated.left ⟨2, by decide⟩)).rename vecPlacement
def vecRight : CTm Tower.Head 8 := (liftTm (Programs.Annotated.right ⟨2, by decide⟩)).rename vecPlacement

def natResult : CTm Tower.Head 8 := (Programs.Annotated.resultType ⟨0, by decide⟩).rename natPlacement
def vecResult : CTm Tower.Head 8 := (Programs.Annotated.resultType ⟨2, by decide⟩).rename vecPlacement

def mixedLeft : CTm Tower.Head 8 := .app (.app (.var 0) natLeft) vecLeft
def mixedRight : CTm Tower.Head 8 := .app (.app (.var 0) natRight) vecRight

theorem combining_function_typed : CTyped (Programs.Annotated.church profile) sourceContext (.var 0)
    (.pi natResult ((CTm.pi vecResult (.const natName)).rename wk)) := by
  have actual : sourceContext.lookup 0 = .pi natResult ((CTm.pi vecResult (.const natName)).rename wk) := by decide +kernel
  rw [← actual]
  exact .var 0

theorem mixed_source_equal : CEqual (Programs.Annotated.church profile) sourceContext mixedLeft mixedRight (.const natName) := by
  have first := (Programs.Annotated.canonical_equal ⟨0, by decide⟩).rename natural_placement
  have second := (Programs.Annotated.canonical_equal ⟨2, by decide⟩).rename vector_placement
  have application : CEqual (Programs.Annotated.church profile) sourceContext
      (.app (.var 0) natLeft) (.app (.var 0) natRight) (.pi vecResult (.const natName)) := by
    simpa only [CTm.inst0_rename_wk, natLeft, natRight] using CDerivable.appCong (.refl combining_function_typed) first
  exact CDerivable.appCong application second

open Programs.Annotated

def natLeftCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 ((Evidence.left_0 profile).rename natural_placement)
def natRightCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 ((Evidence.right_0 profile).rename natural_placement)
def vecLeftCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 ((Evidence.left_2 profile).rename vector_placement)
def vecRightCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 ((Evidence.right_2 profile).rename vector_placement)
def sourceContextCertificate : JudgmentReplay.ContextCertificate profile 8 := by
  annotated_context_certificate 8000 source_formed

def natRowCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := sourceContext) (left := natLeft) (right := natRight) (A := natResult)
      ⟨0, List.ofFn (fun index => CTm.var (natPlacement index))⟩)
    ([natLeftCertificate, natRightCertificate] ++ List.ofFn fun index : Fin 3 =>
      JudgmentReplay.Producer.assemble profile (.var (Γ := sourceContext) (natPlacement index)) [])

def vecRowCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := sourceContext) (left := vecLeft) (right := vecRight) (A := vecResult)
      ⟨2, List.ofFn (fun index => CTm.var (vecPlacement index))⟩)
    ([vecLeftCertificate, vecRightCertificate] ++ List.ofFn fun index : Fin 4 =>
      JudgmentReplay.Producer.assemble profile (.var (Γ := sourceContext) (vecPlacement index)) [])

def firstApplication : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.appCong (Γ := sourceContext) (f := .var 0) (g := .var 0) (a := natLeft) (b := natRight)
      (A := natResult) (B := (CTm.pi vecResult (.const natName)).rename wk))
    [JudgmentReplay.Producer.assemble profile
      (.refl (Γ := sourceContext) (a := .var 0) (A := .pi natResult ((CTm.pi vecResult (.const natName)).rename wk)))
      [JudgmentReplay.Producer.assemble profile (.var (Γ := sourceContext) 0) []], natRowCertificate]

def mixedCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.appCong (Γ := sourceContext) (f := .app (.var 0) natLeft) (g := .app (.var 0) natRight)
      (a := vecLeft) (b := vecRight) (A := vecResult) (B := .const natName))
    [firstApplication, vecRowCertificate]

abbrev parameters : HOL.Ctx BaseSort :=
  (vectorInterface.result ⇒ vectorInterface.result ⇒ raw.number) ::
    NativeVectorComputationRows.Row.nil.parameters vectorOps ++ naturalOps.parameters

def received := AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
  AnnotatedPredicateReading.Interpreter.standard roots parameters sourceContext mixedLeft mixedRight (.const natName)
  sourceContextCertificate mixedCertificate

def receivedContext := AnnotatedPredicateReading.Reader.admitContext? (church profile) lex
  (JudgmentReplay.decoder profile) parameters sourceContext sourceContextCertificate

theorem mixed_source_checked : JudgmentReplay.check profile mixedCertificate
    (.equality sourceContext mixedLeft mixedRight (.const natName)) = true := by decide +kernel

theorem mixed_context_checked : JudgmentReplay.checkContext profile sourceContext sourceContextCertificate = true := by decide +kernel

theorem mixed_context_read : receivedContext.isSome = true := by decide +kernel

theorem mixed_received : received.isSome = true := by decide +kernel

def naturalCertificate : NativeNaturalPredicateReading.AnnotatedConversion.Row → JudgmentReplay.Certificate profile
  | .zero => NativeNaturalPredicateReading.AnnotatedConversion.CertificateInterpretation.Controls.zeroCertificate
  | .successor => NativeNaturalPredicateReading.AnnotatedConversion.CertificateInterpretation.Controls.successorCertificate

def naturalContextCertificate : (row : NativeNaturalPredicateReading.AnnotatedConversion.Row) →
    JudgmentReplay.ContextCertificate profile (row.parameters naturalOps).length
  | .zero => NativeNaturalPredicateReading.AnnotatedConversion.CertificateInterpretation.Controls.zeroContext
  | .successor => NativeNaturalPredicateReading.AnnotatedConversion.CertificateInterpretation.Controls.successorContext

def receiveNatural (row : NativeNaturalPredicateReading.AnnotatedConversion.Row) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots (row.parameters naturalOps) (row.context naturalOps)
    (row.left naturalOps) (row.right naturalOps) (row.type naturalOps) (naturalContextCertificate row) (naturalCertificate row)

def receiveVector (row : NativeVectorComputationRows.Row) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots (row.parameters vectorOps)
    (NativeVectorComputationRows.EncodedConstructor.Controls.sourceContext row)
    (liftTm (row.rawLeft vectorOps)) (liftTm (row.rawRight vectorOps))
    (NativeVectorComputationRows.EncodedConstructor.Controls.sourceType row)
    (NativeVectorComputationRows.EncodedConstructor.Controls.contextCertificate row)
    (NativeVectorComputationRows.Controls.certificate row)

theorem all_original_rows_received :
    (receiveNatural .zero).isSome = true ∧ (receiveNatural .successor).isSome = true ∧
    (receiveVector .nil).isSome = true ∧ (receiveVector .cons).isSome = true := by decide +kernel

def rootsRestricted (enabled : Programs.ComputationProfiles.Selection) (Γ : HOL.Ctx BaseSort)
    (left right : CTm Tower.Head Γ.length) (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :=
  (AnnotatedPredicateReading.Roots.read? (entries raw vectorInterface naturalSelection profile) enabled Γ left right code).map
    AnnotatedPredicateReading.Roots.Result.equality

def receivedWith (enabled : Programs.ComputationProfiles.Selection) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard (rootsRestricted enabled)
    parameters sourceContext mixedLeft mixedRight (.const natName) sourceContextCertificate mixedCertificate

theorem disabled_natural_refused : (receivedWith (fun index => index.val != 0)).isNone = true := by decide +kernel

theorem disabled_vector_refused : (receivedWith (fun index => index.val != 2)).isNone = true := by decide +kernel

def wrongParameters : HOL.Ctx BaseSort :=
  (vectorInterface.result ⇒ raw.number) ::
    NativeVectorComputationRows.Row.nil.parameters vectorOps ++ naturalOps.parameters

def receivedWrongCarrier := AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
  AnnotatedPredicateReading.Interpreter.standard roots wrongParameters sourceContext mixedLeft mixedRight (.const natName)
  sourceContextCertificate mixedCertificate

theorem wrong_function_carrier_refused : receivedWrongCarrier.isNone = true := by decide +kernel

def changedEndpoint := AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
  AnnotatedPredicateReading.Interpreter.standard roots parameters sourceContext mixedLeft (.const zeroName) (.const natName)
  sourceContextCertificate mixedCertificate

theorem changed_endpoint_refused : changedEndpoint.isNone = true := by decide +kernel

def result := received.get mixed_received

def expectedRight : HOL.Term Const parameters raw.number :=
  .app (.app (.var .vz) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs .vz)))

theorem expected_right_reads : AnnotatedPredicateReading.Reads lex (Γ := parameters) mixedRight expectedRight :=
  AnnotatedPredicateReading.Reader.infer?_sound lex parameters mixedRight raw.number expectedRight (by decide +kernel)

theorem result_right_exact :
    (⟨result.carrier, result.evidence.right⟩ : (type : HOL.Ty BaseSort) × HOL.Term Const parameters type) =
      ⟨raw.number, expectedRight⟩ :=
  AnnotatedPredicateReading.Reader.coherent result.evidence.rightRead expected_right_reads

noncomputable def model := NativeVectorComputationRows.EncodedConstructor.Controls.model

theorem root_background_realizable :
    ∀ formula ∈ closedAssumptions raw vectorInterface naturalSelection, model.models formula := by
  intro formula present
  rcases List.mem_append.mp present with nat | vec
  · change formula ∈ [HOL.SelectionProofs.principle naturalSelection,
      HOL.NaturalRecursionProofs.statement raw.zero raw.successor vectorInterface.result] at nat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at nat
    rcases nat with rfl | rfl
    · exact NativeVectorComputationRows.EncodedConstructor.Controls.choice_holds _
    · exact NativeVectorComputationRows.EncodedConstructor.Controls.recursion_holds _
  · exact NativeVectorComputationRows.EncodedConstructor.Controls.background_realizable formula vec

def originalNaturalReceipt :=
  NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.receipt naturalOps profile
    .zero rfl naturalOps.parameters CTm.ids HOL.Subst.id (fun index => .var index)

def extendedNaturalReceipt := (naturalExtension raw vectorInterface naturalSelection).receipt originalNaturalReceipt

theorem extended_receipt_address : extendedNaturalReceipt.parsed.index.val = 0 :=
  (naturalExtension raw vectorInterface naturalSelection).receipt_address originalNaturalReceipt

theorem natural_template_cost :
    (naturalTemplate raw vectorInterface naturalSelection profile .zero).proof.nodeCount =
      (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.template naturalOps profile .zero).proof.nodeCount :=
  (naturalExtension raw vectorInterface naturalSelection).template_nodeCount _

def zeroEntry := (entries raw vectorInterface naturalSelection profile ⟨0, by decide⟩).get
  (entries_present raw vectorInterface naturalSelection profile ⟨0, by decide⟩)

theorem zero_entry_free : zeroEntry.template.proof.FunctionExtensionalityFree :=
  entries_free raw vectorInterface naturalSelection profile ⟨0, by decide⟩ zeroEntry (by
    exact (Option.some_get (entries_present raw vectorInterface naturalSelection profile ⟨0, by decide⟩)).symm)

theorem parameter_blocks_distinct (naturalIndex : Fin 3) (vectorIndex : Fin 4) :
    natPlacement naturalIndex ≠ vecPlacement vectorIndex := by
  intro same
  exact CCtx.blocks_disjoint naturalIndex vectorIndex (Fin.succ_inj.mp same)

#print axioms source_formed
#print axioms mixed_source_equal
#print axioms mixed_source_checked
#print axioms mixed_context_read
#print axioms mixed_received
#print axioms all_original_rows_received
#print axioms disabled_natural_refused
#print axioms disabled_vector_refused
#print axioms result_right_exact
#print axioms root_background_realizable
#print axioms extended_receipt_address
#print axioms natural_template_cost
#print axioms zero_entry_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorProfile.Controls
