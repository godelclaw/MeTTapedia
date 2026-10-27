import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyConversionSubstitution

/-!
# Open Nat/Vec computation trees and retained certificate controls

The original Nat-zero and Vec-nil schema telescopes supply typed bubble
steps. Controls exercise the maintained decoder on the emitted syntax,
including a disabled row and a forged endpoint. Weakening changes the open
arguments while retaining the row. A round trip keeps two step occurrences,
and two equal schema rows keep different citations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.BubbleControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration
open Declaration.ComputationAuthority
open Declaration.IndexedFamily.ConversionBubbles

def zeroOnly : Fin Checking.table.length → Bool := fun row => row.val == 0
def vectorOnly : Fin Checking.table.length → Bool := fun row => row.val == 2

def zeroSource : State Tower.rules rawSignature ⟨3, natContextPZS, natZeroIotaType⟩ :=
  ⟨natZeroIotaLeft, ⟨natZeroIotaReceipt.sourceTyping⟩⟩
def zeroTarget : State Tower.rules rawSignature ⟨3, natContextPZS, natZeroIotaType⟩ :=
  ⟨natZeroIotaRight, ⟨natZeroIotaReceipt.targetTyping⟩⟩

def zeroStep : Step Checking.schemas zeroOnly zeroSource zeroTarget where
  row := ⟨0, by decide⟩
  permitted := by decide
  occurrence := by
    simpa [Checking.schemas, IndexedFamily.Checking.receiptAt, natZeroIotaSchema,
      zeroSource, zeroTarget] using natZeroIotaReceipt.identityInstance

def zeroPath : (bubbles Checking.schemas).Conv zeroOnly zeroSource zeroTarget := .step zeroStep
def zeroCertificate := elaborate Checking.schemas zeroPath

theorem zero_code_exact : zeroCertificate.code =
    .single (.root ⟨0, [.var 0, .var 1, .var 2]⟩) := by
  rw [zeroCertificate, zeroPath, elaborate_step]
  rfl

theorem zero_selected_accepted : zeroCertificate.code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table zeroOnly) natZeroIotaLeft natZeroIotaRight = true :=
  elaborate_selected Checking.schemas zeroPath

theorem zero_original_conversion : Conv rules.headEq natZeroIotaLeft natZeroIotaRight rules.computation :=
  elaborate_original Checking.schemas rfl zeroPath

theorem disabled_row_refused : zeroCertificate.code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table (fun _ => false))
    natZeroIotaLeft natZeroIotaRight = false := by
  rw [zero_code_exact]
  decide +kernel

theorem forged_endpoint_refused : zeroCertificate.code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table zeroOnly)
    natZeroIotaLeft (.var 0) = false := by
  rw [zero_code_exact]
  decide +kernel

def roundTrip : (bubbles Checking.schemas).Conv zeroOnly zeroSource zeroSource :=
  .trans zeroPath (.symm zeroPath)

theorem roundTrip_accepted : (elaborate Checking.schemas roundTrip).code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table zeroOnly) natZeroIotaLeft natZeroIotaLeft = true :=
  elaborate_selected Checking.schemas roundTrip

theorem roundTrip_work : (elaborate Checking.schemas roundTrip).code.stepCount = 2 := by
  rw [elaborate_work]
  simp only [roundTrip, zeroPath, BubbleElaboration.stepCount_trans,
    BubbleElaboration.stepCount_symm, BubbleElaboration.stepCount_step]

theorem roundTrip_not_reflexivity :
    (elaborate Checking.schemas roundTrip).code ≠ .refl natZeroIotaLeft := by
  intro same
  have count := congrArg StructuralConversionCode.Code.stepCount same
  rw [roundTrip_work] at count
  contradiction

def extendedContext : Tower.Ctx 4 := .snoc natContextPZS natTm
theorem weakenTyping : CtxMor rules natContextPZS extendedContext projection :=
  CtxMor.projectionTyped rules natContextPZS natTm

def weakenedPath := substitute extendedContext projection weakenTyping zeroPath

theorem weakened_code_exact : (elaborate Checking.schemas weakenedPath).code =
    .single (.root ⟨0, [.var (1 : Fin 4), .var (2 : Fin 4), .var (3 : Fin 4)]⟩) := by
  rw [weakenedPath, elaborate_substitute, ← zeroCertificate, zero_code_exact]
  rfl

theorem weakened_accepted : (elaborate Checking.schemas weakenedPath).code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table zeroOnly)
    (rename wk natZeroIotaLeft) (.var (2 : Fin 4)) = true := by
  have checked := substituted_code_accepted Checking.schemas extendedContext projection weakenTyping zeroPath
  rw [← elaborate_substitute Checking.schemas extendedContext projection weakenTyping zeroPath] at checked
  have shifted : Fin.succ (1 : Fin 3) = (2 : Fin 4) := rfl
  simpa only [zeroSource, zeroTarget, subst_projection, natZeroIotaRight, rename, wk,
    shifted, weakenedPath, Checking.table] using checked

theorem widening_keeps_code :
    elaborate Checking.schemas
      ((bubbles Checking.schemas).widen (Step.widen (large := fun _ => true) (fun _ _ => rfl)) zeroPath) =
      zeroCertificate :=
  elaborate_widen Checking.schemas (fun _ _ => rfl) zeroPath

def vectorSource : State Tower.rules rawSignature ⟨4, vecContextAPZS, vecNilIotaType⟩ :=
  ⟨vecNilIotaLeft, ⟨vecNilIotaReceipt.sourceTyping⟩⟩
def vectorTarget : State Tower.rules rawSignature ⟨4, vecContextAPZS, vecNilIotaType⟩ :=
  ⟨vecNilIotaRight, ⟨vecNilIotaReceipt.targetTyping⟩⟩
def vectorStep : Step Checking.schemas vectorOnly vectorSource vectorTarget where
  row := ⟨2, by decide⟩
  permitted := by decide
  occurrence := by
    simpa [Checking.schemas, IndexedFamily.Checking.receiptAt, IndexedFamily.Checking.table,
      vecNilIotaSchema, vectorSource, vectorTarget, Fin.cases, Fin.induction,
      Fin.induction.go] using vecNilIotaReceipt.identityInstance
def vectorPath : (bubbles Checking.schemas).Conv vectorOnly vectorSource vectorTarget := .step vectorStep
def vectorCertificate := elaborate Checking.schemas vectorPath

theorem vector_code_exact : vectorCertificate.code =
    .single (.root ⟨2, [.var 0, .var 1, .var 2, .var 3]⟩) := by
  rw [vectorCertificate, vectorPath, elaborate_step]
  rfl

theorem vector_accepted : vectorCertificate.code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table vectorOnly) vecNilIotaLeft vecNilIotaRight = true :=
  elaborate_selected Checking.schemas vectorPath

theorem vector_refused_by_zero_policy : vectorCertificate.code.check Tower.rules.headEq
    (SchemaTableConversionCode.decode Checking.table zeroOnly) vecNilIotaLeft vecNilIotaRight = false := by
  rw [vector_code_exact]
  decide +kernel

namespace RepeatedRows

def schemas : IndexedFamily.Checking.Schemas Tower.rules rawSignature proofRelevantIotaComputation :=
  [⟨3, natZeroIotaSchema⟩, ⟨3, natZeroIotaSchema⟩]
def first : Step schemas (fun _ => true) zeroSource zeroTarget where
  row := ⟨0, by decide⟩
  permitted := rfl
  occurrence := by
    simpa [schemas, IndexedFamily.Checking.receiptAt, natZeroIotaSchema,
      zeroSource, zeroTarget] using natZeroIotaReceipt.identityInstance
def second : Step schemas (fun _ => true) zeroSource zeroTarget where
  row := (0 : Fin 1).succ
  permitted := rfl
  occurrence := by
    simpa only [schemas, IndexedFamily.Checking.receiptAt, Fin.cases_succ, Fin.cases_zero,
      natZeroIotaSchema, zeroSource, zeroTarget] using natZeroIotaReceipt.identityInstance

theorem same_endpoints :
    SchemaTableConversionCode.decode (IndexedFamily.Checking.table schemas) (fun _ => true) first.rootCode =
      SchemaTableConversionCode.decode (IndexedFamily.Checking.table schemas) (fun _ => true) second.rootCode := by
  rw [Step.rootCode_accepted, Step.rootCode_accepted]

theorem distinct_citations : first.rootCode ≠ second.rootCode := by
  intro same
  have different := congrArg SchemaTableConversionCode.Code.row same
  contradiction

end RepeatedRows

#print axioms zero_selected_accepted
#print axioms zero_original_conversion
#print axioms weakened_accepted
#print axioms disabled_row_refused
#print axioms forged_endpoint_refused
#print axioms roundTrip_not_reflexivity
#print axioms vector_accepted
#print axioms RepeatedRows.distinct_citations

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.BubbleControls
