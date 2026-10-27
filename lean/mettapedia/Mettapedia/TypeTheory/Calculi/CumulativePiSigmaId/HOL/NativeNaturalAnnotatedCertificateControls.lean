import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedCertificates
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedReindexingControls

/-!
# Original-checker controls for annotated conversion certificates

The mixed dependent path has a prescribed declaration wrapper, original row
address and argument order, followed by the reversed structural beta step.
The maintained decoder checks this data directly. Disabled rows, changed
endpoints and malformed arities are refused.

Specialization preserves accepted codes, but it can repair a raw code whose
two middle terms originally disagreed. Such an accepted specialization is
not evidence that the original code was accepted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.CertificateControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedConversion.Controls AnnotatedConversion.ReindexingControls

def check {n : Nat} (selected : Programs.ComputationProfiles.Selection)
    (code : SourceCertificates.Code n) (source target : Tower.Tm n) : Bool :=
  code.check Tower.rules.headEq (Programs.ComputationProfiles.decoder selected).decode source target

def mixedCode : SourceCertificates.Code 3 := (SourceCertificates.emit mixedPath).code

theorem mixed_shape : mixedCode =
    .trans (.single (.root (.declared ⟨0, [.var 0, .var 1, .var 2]⟩)))
      (.symm (.single (.betaPi (.var 0) (.var 1)))) := by
  simp only [mixedCode, mixedPath, SourceCertificates.emit,
    StructuralConversionCode.Elaboration.code_trans, StructuralConversionCode.Elaboration.code_symm,
    StructuralConversionCode.Elaboration.code_step, SourceCertificates.certificate,
    StructuralConversionCode.Certificate.single]
  rfl

theorem mixed_accepted :
    check profile mixedCode zeroInstance.source.term.erase identityBeta.source.term.erase = true :=
  SourceCertificates.emit_selected mixedPath

theorem zero_root_accepted : (Programs.ComputationProfiles.decoder profile).decode
    (SourceCertificates.rootCode zeroInstance) = some (zeroInstance.source.term.erase, zeroInstance.target.term.erase) :=
  SourceCertificates.rootCode_accepted zeroInstance profile rfl

theorem restricted_accepted :
    check Programs.ComputationProfiles.zeroOnly mixedCode
      zeroInstance.source.term.erase identityBeta.source.term.erase = true := by
  rw [mixed_shape]
  decide +kernel

theorem disabled_refused :
    check (fun _ => false) mixedCode zeroInstance.source.term.erase identityBeta.source.term.erase = false := by
  rw [mixed_shape]
  decide +kernel

/-- The changed target is convertible to the original target, but this
unchanged submitted code does not certify that different endpoint. -/
theorem changed_endpoint_refused :
    check profile mixedCode zeroInstance.source.term.erase (.var 1) = false := by
  rw [mixed_shape]
  decide +kernel

theorem mixed_source_conversion : Conv (Programs.ComputationProfiles.rules profile).headEq
    zeroInstance.source.term.erase identityBeta.source.term.erase
    (Programs.ComputationProfiles.rules profile).computation :=
  SourceCertificates.emit_original mixedPath

theorem mixed_work : mixedCode.stepCount = 2 := by
  rw [mixedCode, SourceCertificates.emit_work, Controls.mixed_work]

theorem weakened_code : (SourceCertificates.emit weakenedPath).code =
    mixedCode.substitute SourceCertificates.substituteRoot (CTm.eraseSub weaken.source) :=
  SourceCertificates.emit_substitute weaken mixedPath

theorem widened_code :
    SourceCertificates.emit ((bubbles operations profile).widen
      (Step.widen (large := profile) (fun _ _ => rfl)) limitedPath) = SourceCertificates.emit limitedPath :=
  SourceCertificates.emit_widen (large := profile) (fun _ _ => rfl) limitedPath

/-- A direct closed consumer of the shared selected-decoder fold. -/
theorem shared_selected : check profile mixedCode
    zeroInstance.source.term.erase identityBeta.source.term.erase = true :=
  StructuralConversionCode.Elaboration.checkWith (B := bubbles operations profile)
    (RootCode := SourceCertificates.RootCode)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    (SourceCertificates.certificate (operations := operations) (profile := profile) (enabled := profile))
    Tower.rules.headEq (Programs.ComputationProfiles.decoder profile).decode
    (fun step => SourceCertificates.step_selected step) mixedPath

theorem shared_work : mixedCode.stepCount = BubbleElaboration.stepCount mixedPath :=
  StructuralConversionCode.Elaboration.stepCount (B := bubbles operations profile)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    (SourceCertificates.certificate (operations := operations) (profile := profile) (enabled := profile))
    (fun _ => rfl) mixedPath

/-- The original successor row, with its four open arguments in table order. -/
def successorRoot : SourceCertificates.RootCode 4 :=
  .declared ⟨1, [.var 0, .var 1, .var 2, .var 3]⟩

/-- Direct application of the shared declaration decoder law to a nonidentity
substitution of the actual successor citation. -/
theorem declared_decoder_substitution :
    DeclarationConversionCode.decode (Programs.ComputationProfiles.signature profile)
      (StructuralConversionCode.RootDecoder.ofEmpty Tower.rules.computation rfl).decode
      (SchemaTableConversionCode.decode Checking.table profile)
      (DeclarationConversionCode.RootCode.substitute (fun _ code => Empty.elim code)
        SchemaTableConversionCode.Code.substitute (subst0 (.const zeroName)) successorRoot) =
    (DeclarationConversionCode.decode (Programs.ComputationProfiles.signature profile)
      (StructuralConversionCode.RootDecoder.ofEmpty Tower.rules.computation rfl).decode
      (SchemaTableConversionCode.decode Checking.table profile) successorRoot).map
        (fun endpoints => (subst (subst0 (.const zeroName)) endpoints.1,
          subst (subst0 (.const zeroName)) endpoints.2)) :=
  DeclarationConversionCode.decode_substitute (fun _ code => Empty.elim code)
    SchemaTableConversionCode.Code.substitute (Programs.ComputationProfiles.signature profile)
    (StructuralConversionCode.RootDecoder.ofEmpty Tower.rules.computation rfl).decode
    (SchemaTableConversionCode.decode Checking.table profile)
    (fun _ code => nomatch code) (SchemaTableConversionCode.decode_substitute Checking.table profile)
    (subst0 (.const zeroName)) successorRoot

def malformedRoot : SourceCertificates.RootCode 4 := .declared ⟨0, []⟩

theorem malformed_refused : (Programs.ComputationProfiles.decoder profile).decode malformedRoot = none := by
  decide +kernel

theorem malformed_still_refused : (Programs.ComputationProfiles.decoder profile).decode
    (SourceCertificates.substituteRoot (CTm.eraseSub closeZero.source) malformedRoot) = none := by
  rw [SourceCertificates.decode_substitute, malformed_refused]
  rfl

def brokenMiddle : SourceCertificates.Code 4 :=
  .trans (.refl (.var 0)) (.refl (.const zeroName))

theorem broken_middle_refused : check profile brokenMiddle (.var 0) (.const zeroName) = false := by
  decide +kernel

theorem specialized_middle_accepted :
    check profile
      (brokenMiddle.substitute SourceCertificates.substituteRoot (CTm.eraseSub closeZero.source))
      (.const zeroName) (.const zeroName) = true := by
  decide +kernel

theorem opaque_delta_refused :
    (Programs.ComputationProfiles.decoder profile).decode
      (.delta natEliminateName : SourceCertificates.RootCode 3) = none := by
  decide +kernel

#print axioms mixed_shape
#print axioms mixed_accepted
#print axioms restricted_accepted
#print axioms disabled_refused
#print axioms changed_endpoint_refused
#print axioms mixed_source_conversion
#print axioms weakened_code
#print axioms widened_code
#print axioms malformed_still_refused
#print axioms specialized_middle_accepted

end AnnotatedConversion.CertificateControls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
