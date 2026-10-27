import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityInterpreterCoverage
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.AnnotatedCertificateProducer
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversionControls

/-!
# Incoming natural and beta equality certificates

The surrounding source typing/context certificates are produced from existing
canonical proofs and replayed independently. The natural rule itself cites
the original table address and supplies every actual argument guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.CertificateInterpretation.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated
open AnnotatedConversion.Controls (operations profile)

def zeroLeft : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 (Evidence.left_0 profile)

def zeroRight : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 (Evidence.right_0 profile)

def zeroContext : JudgmentReplay.ContextCertificate profile 3 := by
  annotated_context_certificate 5000 (Evidence.context_0 profile)

def successorLeft : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 (Evidence.left_1 profile)

def successorRight : JudgmentReplay.Certificate profile := by
  annotated_certificate 5000 (Evidence.right_1 profile)

def successorContext : JudgmentReplay.ContextCertificate profile 4 := by
  annotated_context_certificate 5000 (Evidence.context_1 profile)

def zeroCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := Row.zero.context operations) (left := Row.zero.left operations)
      (right := Row.zero.right operations) (A := Row.zero.type operations)
      (JudgmentReplay.Controls.citedRow ⟨0, by decide⟩))
    ([zeroLeft, zeroRight] ++ List.ofFn fun index : Fin 3 =>
      JudgmentReplay.Producer.assemble profile (.var (Γ := Row.zero.context operations) index) [])

def successorCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := Row.successor.context operations) (left := Row.successor.left operations)
      (right := Row.successor.right operations) (A := Row.successor.type operations)
      (JudgmentReplay.Controls.citedRow ⟨1, by decide⟩))
    ([successorLeft, successorRight] ++ List.ofFn fun index : Fin 4 =>
      JudgmentReplay.Producer.assemble profile (.var (Γ := Row.successor.context operations) index) [])

theorem zero_source_checked : JudgmentReplay.check profile zeroCertificate
    (.equality (Row.zero.context operations) (Row.zero.left operations) (Row.zero.right operations)
      (Row.zero.type operations)) = true := by decide

theorem successor_source_checked : JudgmentReplay.check profile successorCertificate
    (.equality (Row.successor.context operations) (Row.successor.left operations) (Row.successor.right operations)
      (Row.successor.type operations)) = true := by decide

theorem zero_context_checked : JudgmentReplay.checkContext profile (Row.zero.context operations) zeroContext = true := by decide

theorem successor_context_checked : JudgmentReplay.checkContext profile
    (Row.successor.context operations) successorContext = true := by decide

def zeroRead := check? operations profile operations.parameters (Row.zero.context operations)
  (Row.zero.left operations) (Row.zero.right operations) (Row.zero.type operations) zeroContext zeroCertificate

def successorRead := check? operations profile operations.successorParameters (Row.successor.context operations)
  (Row.successor.left operations) (Row.successor.right operations) (Row.successor.type operations)
  successorContext successorCertificate

def betaRead := check? operations profile [] .nil
  (.app (.lam (.const natName) (.var 0)) (.const zeroName)) (.const zeroName) (.const natName)
  .nil JudgmentReplay.Controls.beta

def betaLeft : CTm Tower.Head 0 := .app (.lam (.const natName) (.var 0)) (.const zeroName)
def identityTerm : CTm Tower.Head 0 := .lam (.const natName) (.var 0)

def reversedBeta : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.symm (Γ := .nil) (a := betaLeft) (b := .const zeroName) (A := .const natName)) [JudgmentReplay.Controls.beta]

def composedBeta : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.trans (Γ := .nil) (a := betaLeft) (b := .const zeroName) (c := betaLeft) (A := .const natName))
    [JudgmentReplay.Controls.beta, reversedBeta]

def badMiddle : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.trans (Γ := .nil) (a := betaLeft) (b := .const zeroName) (c := betaLeft) (A := .const natName))
    [JudgmentReplay.Controls.beta, JudgmentReplay.Controls.beta]

def application : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.appCong (Γ := .nil) (f := identityTerm) (g := identityTerm) (a := betaLeft) (b := .const zeroName)
      (A := .const natName) (B := .const natName))
    [JudgmentReplay.Producer.assemble profile
      (.refl (Γ := .nil) (a := identityTerm) (A := .pi (.const natName) (.const natName))) [JudgmentReplay.Controls.identity],
     JudgmentReplay.Controls.beta]

def naturalArrow {n : Nat} (context : CCtx Tower.Head n) : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.piForm (Γ := context) (A := .const natName) (B := .const natName)
      (u := JudgmentReplay.Controls.u0) (v := JudgmentReplay.Controls.u0) (w := JudgmentReplay.Controls.u00))
    [JudgmentReplay.Controls.natural context, JudgmentReplay.Controls.natural (.snoc context (.const natName))]

def betaUnderBinder : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.betaPi (Γ := .snoc .nil (.const natName)) (A := .const natName) (a := .var 0) (body := .var 0)
      (B := .const natName) (u := JudgmentReplay.Controls.u00))
    [naturalArrow (.snoc .nil (.const natName)),
     JudgmentReplay.Producer.assemble profile (.var (Γ := .snoc (.snoc .nil (.const natName)) (.const natName)) 0) [],
     JudgmentReplay.Controls.identityBody]

def binder : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.lamCong (Γ := .nil) (A := .const natName) (A' := .const natName)
      (body := .app (.lam (.const natName) (.var 0)) (.var 0)) (body' := .var 0) (B := .const natName)
      (u := JudgmentReplay.Controls.u00) (w := JudgmentReplay.Controls.u0))
    [JudgmentReplay.Producer.assemble profile
      (.refl (Γ := .nil) (a := .const natName) (A := .head JudgmentReplay.Controls.u0)) [JudgmentReplay.Controls.natural .nil],
     naturalArrow .nil, betaUnderBinder]

def typeBetaLeft : CTm Tower.Head 0 := .app (.lam (.const natName) (.const natName)) (.const zeroName)
abbrev typeFunctionLevel : Tower.Head := .sort (.max Tower.zero (.succ Tower.zero))

def typeFunction : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.piForm (Γ := .nil) (A := .const natName) (B := .head JudgmentReplay.Controls.u0)
      (u := JudgmentReplay.Controls.u0) (v := JudgmentReplay.Controls.u1) (w := typeFunctionLevel))
    [JudgmentReplay.Controls.natural .nil,
     JudgmentReplay.Producer.assemble profile
       (.headType (Γ := .snoc .nil (.const natName)) (h := JudgmentReplay.Controls.u0) (u := JudgmentReplay.Controls.u1)) []]

def typeBeta : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.betaPi (Γ := .nil) (A := .const natName) (a := .const zeroName) (body := .const natName)
      (B := .head JudgmentReplay.Controls.u0) (u := typeFunctionLevel))
    [typeFunction, JudgmentReplay.Controls.natural (.snoc .nil (.const natName)), JudgmentReplay.Controls.zero .nil]

def product : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.piCong (Γ := .nil) (A := typeBetaLeft) (A' := .const natName) (B := .const natName) (B' := .const natName)
      (u := JudgmentReplay.Controls.u0) (v := JudgmentReplay.Controls.u0) (w := JudgmentReplay.Controls.u00))
    [typeBeta, JudgmentReplay.Producer.assemble profile
      (.refl (Γ := .snoc .nil typeBetaLeft) (a := .const natName) (A := .head JudgmentReplay.Controls.u0))
      [JudgmentReplay.Controls.natural (.snoc .nil typeBetaLeft)]]

theorem composed_source_checked : JudgmentReplay.check profile composedBeta
    (.equality .nil betaLeft betaLeft (.const natName)) = true := by decide

theorem application_source_checked : JudgmentReplay.check profile application
    (.equality .nil (.app identityTerm betaLeft) (.app identityTerm (.const zeroName)) (.const natName)) = true := by decide

theorem binder_source_checked : JudgmentReplay.check profile binder
    (.equality .nil (.lam (.const natName) (.app (.lam (.const natName) (.var 0)) (.var 0))) identityTerm
      (.pi (.const natName) (.const natName))) = true := by decide

theorem product_source_checked : JudgmentReplay.check profile product
    (.equality .nil (.pi typeBetaLeft (.const natName)) (.pi (.const natName) (.const natName))
      (.head JudgmentReplay.Controls.u00)) = true := by decide

def convertedType : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.convEq (Γ := .nil) (a := betaLeft) (b := .const zeroName) (A := .const natName) (B := typeBetaLeft)
      (u := JudgmentReplay.Controls.u0))
    [JudgmentReplay.Controls.beta, JudgmentReplay.Producer.assemble profile
      (.symm (Γ := .nil) (a := typeBetaLeft) (b := .const natName) (A := .head JudgmentReplay.Controls.u0)) [typeBeta]]

def subtypedBack : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.subEq (Γ := .nil) (a := betaLeft) (b := .const zeroName) (A := typeBetaLeft) (B := .const natName))
    [convertedType, JudgmentReplay.Producer.assemble profile
      (.subEqual (Γ := .nil) (A := typeBetaLeft) (B := .const natName) (u := JudgmentReplay.Controls.u0)) [typeBeta]]

theorem converted_type_source_checked : JudgmentReplay.check profile convertedType
    (.equality .nil betaLeft (.const zeroName) typeBetaLeft) = true := by decide

theorem subtyped_back_source_checked : JudgmentReplay.check profile subtypedBack
    (.equality .nil betaLeft (.const zeroName) (.const natName)) = true := by decide

theorem bad_middle_refused : JudgmentReplay.check profile badMiddle
    (.equality .nil betaLeft betaLeft (.const natName)) = false := by decide

def betaEvidence : EqualityAt operations [] betaLeft (.const zeroName) operations.number :=
  EqualityAt.beta (domainCode := HOL.PredicateProducts.full operations.number)
    (bodyCode := .var .vz) (argumentCode := operations.zero) .natural
    (AnnotatedReads.var (Γ := [operations.number]) .vz) .zero

theorem beta_interpreted : readEquality? operations profile JudgmentReplay.Controls.beta [] .nil
    betaLeft (.const zeroName) (.const natName) = some ⟨operations.number, betaEvidence⟩ := by
  have parsed := (read_beta (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    (.const natName) (.const zeroName) (.var 0) (.const natName) JudgmentReplay.Controls.u00
    [JudgmentReplay.Controls.functionType, JudgmentReplay.Controls.identityBody, JudgmentReplay.Controls.zero .nil]).trans
      (EqualityCode.beta?_complete (operations := operations)
        (domainCode := HOL.PredicateProducts.full operations.number)
        (bodyCode := .var .vz) (argumentCode := operations.zero) .natural (.var .vz) .zero)
  exact parsed

def betaReceived : CheckedEquality operations profile [] .nil betaLeft (.const zeroName) (.const natName) :=
  ⟨.nil, JudgmentReplay.Controls.independent_beta, ⟨operations.number, betaEvidence⟩⟩

theorem beta_received_exact : betaRead = some betaReceived :=
  admit_reading (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    betaLeft (.const zeroName) (.const natName) .nil JudgmentReplay.Controls.beta
    ⟨operations.number, betaEvidence⟩ rfl JudgmentReplay.Controls.beta_checked beta_interpreted

theorem beta_root_free : betaReceived.rootProof.FunctionExtensionalityFree := betaReceived.rootProof_free

def zeroEvidence : EqualityAt operations operations.parameters (Row.zero.left operations)
    (Row.zero.right operations) operations.result :=
  EqualityAt.row .zero CTm.ids HOL.Subst.id (fun index => .var index)

theorem zero_interpreted : readEquality? operations profile zeroCertificate operations.parameters (Row.zero.context operations)
    (Row.zero.left operations) (Row.zero.right operations) (Row.zero.type operations) =
      some ⟨operations.result, zeroEvidence⟩ := by
  rw [show zeroCertificate = equationNode profile
    (.root (Γ := Row.zero.context operations) (left := Row.zero.left operations) (right := Row.zero.right operations)
      (A := Row.zero.type operations) (JudgmentReplay.Controls.citedRow ⟨0, by decide⟩))
      ([zeroLeft, zeroRight] ++ List.ofFn fun index : Fin 3 =>
        JudgmentReplay.Producer.assemble profile (.var (Γ := Row.zero.context operations) index) []) from rfl]
  rw [read_root (operations := operations) (profile := profile) (Γ := operations.parameters)
    (context := Row.zero.context operations)]
  exact EqualityCode.natural?_complete profile .zero rfl CTm.ids HOL.Subst.id (fun index => .var index)

def zeroReceived : CheckedEquality operations profile operations.parameters (Row.zero.context operations)
    (Row.zero.left operations) (Row.zero.right operations) (Row.zero.type operations) :=
  ⟨JudgmentReplay.context_sound profile zero_context_checked,
    JudgmentReplay.check_sound profile zero_source_checked, ⟨operations.result, zeroEvidence⟩⟩

theorem zero_received_exact : zeroRead = some zeroReceived :=
  admit_reading (operations := operations) (profile := profile) (Γ := operations.parameters)
    (context := Row.zero.context operations) _ _ _ zeroContext zeroCertificate ⟨operations.result, zeroEvidence⟩
    zero_context_checked zero_source_checked zero_interpreted

theorem zero_root_free : zeroReceived.rootProof.FunctionExtensionalityFree := zeroReceived.rootProof_free

def successorEvidence : EqualityAt operations operations.successorParameters (Row.successor.left operations)
    (Row.successor.right operations) operations.result :=
  EqualityAt.row .successor CTm.ids HOL.Subst.id (fun index => .var index)

theorem successor_interpreted : readEquality? operations profile successorCertificate operations.successorParameters
    (Row.successor.context operations) (Row.successor.left operations) (Row.successor.right operations)
    (Row.successor.type operations) = some ⟨operations.result, successorEvidence⟩ :=
  (read_root (operations := operations) (profile := profile) (Γ := operations.successorParameters)
    (context := Row.successor.context operations) (Row.successor.left operations) (Row.successor.right operations)
    (Row.successor.type operations) (JudgmentReplay.Controls.citedRow ⟨1, by decide⟩) _).trans
    (EqualityCode.natural?_complete profile .successor rfl CTm.ids HOL.Subst.id (fun index => .var index))

def successorReceived : CheckedEquality operations profile operations.successorParameters (Row.successor.context operations)
    (Row.successor.left operations) (Row.successor.right operations) (Row.successor.type operations) :=
  ⟨JudgmentReplay.context_sound profile successor_context_checked,
    JudgmentReplay.check_sound profile successor_source_checked, ⟨operations.result, successorEvidence⟩⟩

theorem successor_received_exact : successorRead = some successorReceived :=
  admit_reading (operations := operations) (profile := profile) (Γ := operations.successorParameters)
    (context := Row.successor.context operations) _ _ _ successorContext successorCertificate ⟨operations.result, successorEvidence⟩
    successor_context_checked successor_source_checked successor_interpreted

theorem reversed_interpreted : readEquality? operations profile reversedBeta [] .nil
    (.const zeroName) betaLeft (.const natName) = some ⟨operations.number, betaEvidence.symm⟩ :=
  read_symm (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    betaLeft (.const zeroName) (.const natName) JudgmentReplay.Controls.beta
    ⟨operations.number, betaEvidence⟩ beta_interpreted

def composedEvidence := EqualityReading.trans ⟨operations.number, betaEvidence⟩ ⟨operations.number, betaEvidence.symm⟩

theorem composed_interpreted : readEquality? operations profile composedBeta [] .nil
    betaLeft betaLeft (.const natName) = some composedEvidence :=
  read_trans (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    betaLeft (.const zeroName) betaLeft (.const natName) JudgmentReplay.Controls.beta reversedBeta
    ⟨operations.number, betaEvidence⟩ ⟨operations.number, betaEvidence.symm⟩ beta_interpreted reversed_interpreted

def identityEvidence : EqualityAt operations [] identityTerm identityTerm (.arr operations.number operations.number) :=
  EqualityAt.refl (AnnotatedReads.abstraction AnnotatedReads.natural
    (AnnotatedReads.var (Γ := [operations.number]) .vz))

theorem identity_refl_interpreted : readEquality? operations profile
    (JudgmentReplay.Producer.assemble profile
      (.refl (Γ := .nil) (a := identityTerm) (A := .pi (.const natName) (.const natName))) [JudgmentReplay.Controls.identity])
    [] .nil identityTerm identityTerm (.pi (.const natName) (.const natName)) = some ⟨_, identityEvidence⟩ :=
  read_refl (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    identityTerm (.pi (.const natName) (.const natName)) JudgmentReplay.Controls.identity
    (AnnotatedReads.abstraction AnnotatedReads.natural (AnnotatedReads.var (Γ := [operations.number]) .vz))

theorem application_interpreted : readEquality? operations profile application [] .nil
    (.app identityTerm betaLeft) (.app identityTerm (.const zeroName)) (.const natName) =
    some ⟨operations.number, EqualityAt.app identityEvidence betaEvidence⟩ :=
  read_app (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    identityTerm identityTerm betaLeft (.const zeroName) (.const natName) (.const natName)
    _ JudgmentReplay.Controls.beta identityEvidence betaEvidence identity_refl_interpreted beta_interpreted

def underBinderEvidence : EqualityAt operations [operations.number]
    (.app (.lam (.const natName) (.var 0)) (.var 0)) (.var 0) operations.number :=
  EqualityAt.beta (domainCode := HOL.PredicateProducts.full operations.number)
    (bodyCode := .var .vz) (argumentCode := .var .vz) .natural
    (AnnotatedReads.var (Γ := [operations.number, operations.number]) .vz)
    (AnnotatedReads.var (Γ := [operations.number]) .vz)

theorem under_binder_interpreted : readEquality? operations profile betaUnderBinder [operations.number]
    (.snoc .nil (.const natName)) (.app (.lam (.const natName) (.var 0)) (.var 0)) (.var 0) (.const natName) =
    some ⟨operations.number, underBinderEvidence⟩ :=
  (read_beta (operations := operations) (profile := profile) (Γ := [operations.number])
    (context := .snoc .nil (.const natName)) (.const natName) (.var 0) (.var 0) (.const natName)
    JudgmentReplay.Controls.u00 _).trans
    (EqualityCode.beta?_complete (domainCode := HOL.PredicateProducts.full operations.number)
      (bodyCode := .var .vz) (argumentCode := .var .vz) .natural
      (AnnotatedReads.var (Γ := [operations.number, operations.number]) .vz)
      (AnnotatedReads.var (Γ := [operations.number]) .vz))

def naturalEvidence {Γ : HOL.Ctx Unit} : EqualityAt operations Γ (.const natName) (.const natName)
    (.arr operations.number .prop) := EqualityAt.refl AnnotatedReads.natural

theorem natural_refl_interpreted {Γ : HOL.Ctx Unit} (context : CCtx Tower.Head Γ.length) :
    readEquality? operations profile
      (JudgmentReplay.Producer.assemble profile
        (.refl (Γ := context) (a := .const natName) (A := .head JudgmentReplay.Controls.u0)) [JudgmentReplay.Controls.natural context])
      Γ context (.const natName) (.const natName) (.head JudgmentReplay.Controls.u0) = some ⟨_, naturalEvidence⟩ :=
  read_refl (operations := operations) (profile := profile) (Γ := Γ) (context := context)
    (.const natName) (.head JudgmentReplay.Controls.u0) (JudgmentReplay.Controls.natural context) AnnotatedReads.natural

theorem binder_interpreted : readEquality? operations profile binder [] .nil
    (.lam (.const natName) (.app (.lam (.const natName) (.var 0)) (.var 0))) identityTerm
    (.pi (.const natName) (.const natName)) =
    some ⟨.arr operations.number operations.number, EqualityAt.lam naturalEvidence underBinderEvidence⟩ :=
  read_lam (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    (.const natName) (.const natName) (.app (.lam (.const natName) (.var 0)) (.var 0)) (.var 0) (.const natName)
    JudgmentReplay.Controls.u00 JudgmentReplay.Controls.u0 _ (naturalArrow .nil) betaUnderBinder
    naturalEvidence underBinderEvidence (natural_refl_interpreted (Γ := []) .nil) under_binder_interpreted

def typeBetaEvidence : EqualityAt operations [] typeBetaLeft (.const natName) (.arr operations.number .prop) :=
  EqualityAt.beta (domainCode := HOL.PredicateProducts.full operations.number)
    (bodyCode := HOL.PredicateProducts.full operations.number) (argumentCode := operations.zero) .natural .natural .zero

theorem type_beta_interpreted : readEquality? operations profile typeBeta [] .nil
    typeBetaLeft (.const natName) (.head JudgmentReplay.Controls.u0) = some ⟨_, typeBetaEvidence⟩ :=
  (read_beta (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    (.const natName) (.const zeroName) (.const natName) (.head JudgmentReplay.Controls.u0) typeFunctionLevel _).trans
    (EqualityCode.beta?_complete (domainCode := HOL.PredicateProducts.full operations.number)
      (bodyCode := HOL.PredicateProducts.full operations.number) (argumentCode := operations.zero) .natural .natural .zero)

theorem product_interpreted : readEquality? operations profile product [] .nil
    (.pi typeBetaLeft (.const natName)) (.pi (.const natName) (.const natName)) (.head JudgmentReplay.Controls.u00) =
    some ⟨_, EqualityAt.pi typeBetaEvidence naturalEvidence⟩ :=
  read_pi (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    typeBetaLeft (.const natName) (.const natName) (.const natName)
    JudgmentReplay.Controls.u0 JudgmentReplay.Controls.u0 JudgmentReplay.Controls.u00 typeBeta _
    typeBetaEvidence naturalEvidence type_beta_interpreted
    (natural_refl_interpreted (Γ := [operations.number]) (.snoc .nil typeBetaLeft))

theorem bad_middle_not_received : check? operations profile [] .nil betaLeft betaLeft (.const natName)
    .nil badMiddle = none :=
  check?_refuses_source (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    (source := betaLeft) (target := betaLeft) (type := .const natName) .nil badMiddle bad_middle_refused

theorem converted_type_interpreted : readEquality? operations profile convertedType [] .nil
    betaLeft (.const zeroName) typeBetaLeft = some ⟨operations.number, betaEvidence⟩ :=
  (read_convEq (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    betaLeft (.const zeroName) (.const natName) typeBetaLeft JudgmentReplay.Controls.u0 JudgmentReplay.Controls.beta _).trans
    beta_interpreted

theorem subtyped_back_interpreted : readEquality? operations profile subtypedBack [] .nil
    betaLeft (.const zeroName) (.const natName) = some ⟨operations.number, betaEvidence⟩ :=
  (read_subEq (operations := operations) (profile := profile) (Γ := []) (context := .nil)
    betaLeft (.const zeroName) typeBetaLeft (.const natName) convertedType _).trans converted_type_interpreted

namespace RootDispatch

def identityCode : SchemaJudgmentCode.Code Tower.Head operations.parameters.length :=
  ⟨0, List.ofFn (fun index => CTm.var index)⟩

def receipt := AnnotatedPredicateReading.Roots.readReceipt? (EqualityCode.RootTable.entries operations profile)
  profile operations.parameters identityCode

theorem accepted : receipt.isSome = true := by decide +kernel

def received := receipt.get accepted

theorem received_address_exact : received.parsed.index.val = identityCode.row := received.address_exact

theorem original_address : (receipt.map (fun received => received.parsed.index.val)) = some 0 := by decide +kernel

theorem disabled_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (EqualityCode.RootTable.entries operations profile)
      (fun _ => false) operations.parameters identityCode).isNone = true := by decide +kernel

theorem wrong_arity_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (EqualityCode.RootTable.entries operations profile)
      profile operations.parameters {identityCode with arguments := []}).isNone = true := by decide +kernel

theorem wrong_carrier_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (EqualityCode.RootTable.entries operations profile)
      profile operations.parameters {identityCode with arguments := List.replicate 3 (.const zeroName)}).isNone = true := by
  decide +kernel

def unsupported : SchemaJudgmentCode.Code Tower.Head 4 := ⟨2, List.ofFn (fun index => CTm.var index)⟩

theorem unsupported_decodes : (SchemaJudgmentCode.decodeInstance Checking.table profile unsupported).isSome = true := by
  decide +kernel

theorem unsupported_has_no_interpretation :
    (AnnotatedPredicateReading.Roots.readReceipt? (EqualityCode.RootTable.entries operations profile)
      profile [operations.number, operations.number, operations.number, operations.number] unsupported).isNone = true := by
  decide +kernel

theorem changed_endpoint_refused :
    (AnnotatedPredicateReading.Roots.read? (EqualityCode.RootTable.entries operations profile) profile
      operations.parameters (Row.zero.left operations) (.var 0) identityCode).isNone = true := by decide +kernel

/-- Duplicate source rows carry independent addresses despite equal endpoints
and the same retained HOL justification. -/
def duplicateTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [(EqualityCode.RootTable.template operations profile .zero).sourceRow,
   (EqualityCode.RootTable.template operations profile .zero).sourceRow]

def duplicateEntries : AnnotatedPredicateReading.Roots.Table (lexicalReading operations)
    (closedAssumptions operations) (Programs.Annotated.church profile).constantType duplicateTable
  | ⟨0, _⟩ => some ⟨EqualityCode.RootTable.template operations profile .zero, rfl⟩
  | ⟨1, _⟩ => some ⟨EqualityCode.RootTable.template operations profile .zero, rfl⟩
  | ⟨n + 2, impossible⟩ => False.elim (by change n + 2 < 2 at impossible; omega)

def duplicateReceipt (address : Nat) := AnnotatedPredicateReading.Roots.readReceipt? duplicateEntries
  (fun _ => true) operations.parameters {identityCode with row := address}

theorem duplicate_addresses_retained :
    ((duplicateReceipt 0).map (fun received => received.parsed.index.val) = some 0) ∧
    ((duplicateReceipt 1).map (fun received => received.parsed.index.val) = some 1) := by decide +kernel

theorem duplicate_conclusions_agree :
    ((duplicateReceipt 0).map (fun received => received.parsed.result (Programs.Annotated.church profile).constantType)) =
    ((duplicateReceipt 1).map (fun received => received.parsed.result (Programs.Annotated.church profile).constantType)) := by
  decide +kernel

/-- The shared proof carrier can retain explicit extensionality. This is a
proof-layer control, not an extension of the current source interpreter. -/
def etaReading : AnnotatedPredicateReading.EqualityAt (lexicalReading operations) [] []
    (.lam (.const natName) (.app (.const succName) (.var 0))) (.const succName)
    (.arr operations.number operations.number) where
  left := .lam (.app (HOL.weaken operations.successor) (.var .vz))
  right := operations.successor
  leftRead := (AnnotatedReads.abstraction (operations := operations) (Γ := [])
    AnnotatedReads.natural (AnnotatedReads.application AnnotatedReads.successor (AnnotatedReads.var .vz))).toGeneric
  rightRead := (AnnotatedReads.successor (operations := operations) (Γ := [])).toGeneric
  proof := .eta operations.successor

theorem eta_dependency_retained : ¬ etaReading.proof.FunctionExtensionalityFree := by
  intro free
  cases free

#print axioms eta_dependency_retained

#print axioms accepted
#print axioms changed_endpoint_refused
#print axioms duplicate_addresses_retained
#print axioms duplicate_conclusions_agree
end RootDispatch

namespace Shared

/-- The standard evidence implementation consumes the original row entries
directly; it does not use Nat's extensionality-free evidence wrapper. -/
def roots (Γ : HOL.Ctx Unit) (source target : CTm Tower.Head Γ.length)
    (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :
    Option (AnnotatedPredicateReading.EqualityReading (lexicalReading operations)
      (closedAssumptions operations) Γ source target) :=
  (AnnotatedPredicateReading.Roots.read? (EqualityCode.RootTable.entries operations profile)
    profile Γ source target code).map AnnotatedPredicateReading.Roots.Result.equality

def read (Γ : HOL.Ctx Unit) (context : CCtx Tower.Head Γ.length)
    (source target type : CTm Tower.Head Γ.length) (certificate : JudgmentReplay.Certificate profile) :=
  AnnotatedPredicateReading.Interpreter.readEquality? AnnotatedPredicateReading.Interpreter.standard
    roots certificate Γ context source target type

def receive (Γ : HOL.Ctx Unit) (context : CCtx Tower.Head Γ.length)
    (source target type : CTm Tower.Head Γ.length)
    (contextCertificate : JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : JudgmentReplay.Certificate profile) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots Γ context source target type contextCertificate certificate

def positive : List (String × Bool) :=
  [("zero", (receive operations.parameters (Row.zero.context operations) (Row.zero.left operations)
      (Row.zero.right operations) (Row.zero.type operations) zeroContext zeroCertificate).isSome),
   ("successor", (receive operations.successorParameters (Row.successor.context operations) (Row.successor.left operations)
      (Row.successor.right operations) (Row.successor.type operations) successorContext successorCertificate).isSome),
   ("beta", (receive [] .nil betaLeft (.const zeroName) (.const natName) .nil JudgmentReplay.Controls.beta).isSome),
   ("transitive", (receive [] .nil betaLeft betaLeft (.const natName) .nil composedBeta).isSome),
   ("application", (receive [] .nil (.app identityTerm betaLeft) (.app identityTerm (.const zeroName))
      (.const natName) .nil application).isSome),
   ("binder", (receive [] .nil (.lam (.const natName) (.app (.lam (.const natName) (.var 0)) (.var 0)))
      identityTerm (.pi (.const natName) (.const natName)) .nil binder).isSome),
   ("product", (receive [] .nil (.pi typeBetaLeft (.const natName)) (.pi (.const natName) (.const natName))
      (.head JudgmentReplay.Controls.u00) .nil product).isSome),
   ("converted type", (receive [] .nil betaLeft (.const zeroName) typeBetaLeft .nil convertedType).isSome),
   ("subtyped", (receive [] .nil betaLeft (.const zeroName) (.const natName) .nil subtypedBack).isSome)]

theorem positive_checked : positive.all Prod.snd = true := by decide +kernel

theorem bad_middle_refused :
    (receive [] .nil betaLeft betaLeft (.const natName) .nil badMiddle).isNone = true := by decide +kernel

/-- The variable rule alone permits this derivation in an unformed context.
The separate formation check must reject the complete request. -/
def unformedContext : CCtx Tower.Head 1 := .snoc .nil (.const zeroName)

def unformedCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.refl (Γ := unformedContext) (a := .var 0) (A := .const zeroName))
    [JudgmentReplay.Producer.assemble profile (.var (Γ := unformedContext) 0) []]

def incorrectFormation : JudgmentReplay.ContextCertificate profile 1 :=
  .snoc .nil JudgmentReplay.Controls.u0 (JudgmentReplay.Controls.natural .nil)

theorem unformed_judgment_checks : JudgmentReplay.check profile unformedCertificate
    (.equality unformedContext (.var 0) (.var 0) (.const zeroName)) = true := by decide +kernel

theorem unformed_endpoints_read :
    (read [operations.number] unformedContext (.var 0) (.var 0) (.const zeroName) unformedCertificate).isSome = true := by
  decide +kernel

theorem unformed_context_refused :
    JudgmentReplay.checkContext profile unformedContext incorrectFormation = false := by decide +kernel

theorem unformed_request_refused :
    receive [operations.number] unformedContext (.var 0) (.var 0) (.const zeroName)
      incorrectFormation unformedCertificate = none :=
  AnnotatedPredicateReading.Interpreter.check?_refuses_context (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots [operations.number] unformedContext
    (.var 0) (.var 0) (.const zeroName) incorrectFormation unformedCertificate unformed_context_refused

#print axioms positive_checked
#print axioms bad_middle_refused
#print axioms unformed_request_refused
end Shared

#print axioms zero_source_checked
#print axioms successor_source_checked

end AnnotatedConversion.CertificateInterpretation.Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
