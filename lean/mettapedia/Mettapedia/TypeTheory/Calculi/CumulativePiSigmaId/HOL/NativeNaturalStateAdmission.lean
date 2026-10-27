import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay

/-!
# Certificate-based admission to the interpreted annotated state fibres

Incoming context and typing certificates are replayed by the actual annotated
source checker. The independent certifying reader then supplies the unique
simple HOL carrier and term. Every state in the interpreted fragment admits
finite certificates; unsupported readings are still refused. This does not
interpret every equality rule of the larger source judgment in HOL.
The simple HOL context remains explicit input; admission alone does not prove
a semantic correspondence between arbitrary source and HOL contexts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.StateAdmission

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open Programs.Annotated

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} [DecidableEq Base]

def readState? (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx Base) (context : CCtx Tower.Head Γ.length) (term type : CTm Tower.Head Γ.length)
    (contextCertificate : JudgmentReplay.ContextCertificate profile Γ.length)
    (typingCertificate : JudgmentReplay.Certificate profile) :
    Option ((carrier : HOL.Ty Base) × State operations profile ⟨Γ, context, type, carrier⟩) :=
  if formed : JudgmentReplay.checkContext profile context contextCertificate = true then
    if typed : JudgmentReplay.check profile typingCertificate (.typing context term type) = true then
      match AnnotatedReading.read? operations Γ term with
      | none => none
      | some read => some ⟨read.val.1, {
          contextFormed := JudgmentReplay.context_sound profile formed
          term := term
          typed := JudgmentReplay.check_sound profile typed
          code := read.val.2
          reading := read.property }⟩
    else none
  else none

theorem readState?_of_checked {operations : Operations Base Const}
    {profile : Programs.ComputationProfiles.Selection} {index : Index Base}
    (state : State operations profile index)
    (contextCertificate : JudgmentReplay.ContextCertificate profile index.targetContext.length)
    (typingCertificate : JudgmentReplay.Certificate profile)
    (formed : JudgmentReplay.checkContext profile index.sourceContext contextCertificate = true)
    (typed : JudgmentReplay.check profile typingCertificate
      (.typing index.sourceContext state.term index.sourceType) = true) :
    readState? operations profile index.targetContext index.sourceContext state.term index.sourceType
      contextCertificate typingCertificate = some ⟨index.targetType, state⟩ := by
  simp only [readState?, formed, typed, dite_true, AnnotatedReading.read?_complete state.reading]

/-- All existing interpreted states have finite, independently replayed
source evidence, with exact recovery of their annotated term and HOL code. -/
theorem complete {operations : Operations Base Const}
    {profile : Programs.ComputationProfiles.Selection} {index : Index Base}
    (state : State operations profile index) :
    ∃ (contextCertificate : JudgmentReplay.ContextCertificate profile index.targetContext.length)
      (typingCertificate : JudgmentReplay.Certificate profile),
      readState? operations profile index.targetContext index.sourceContext state.term index.sourceType
        contextCertificate typingCertificate = some ⟨index.targetType, state⟩ := by
  obtain ⟨contextCertificate, formed⟩ := JudgmentReplay.context_complete profile state.contextFormed
  obtain ⟨typingCertificate, typed⟩ := JudgmentReplay.check_complete profile state.typed
  exact ⟨contextCertificate, typingCertificate, readState?_of_checked state _ _ formed typed⟩

#print axioms readState?
#print axioms readState?_of_checked
#print axioms complete

end AnnotatedConversion.StateAdmission
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
