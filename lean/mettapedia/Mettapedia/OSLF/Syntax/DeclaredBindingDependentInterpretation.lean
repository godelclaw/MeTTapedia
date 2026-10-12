import Mettapedia.OSLF.Syntax.DeclaredBindingContextTransport
import Mettapedia.OSLF.Syntax.DeclaredBindingProvenance
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclaredBindingDependent

/-!
# The existing declared binding fold in dependent syntax

This adapter connects the previously constructed binding-clone interpretation
to the dependent translation. It does not create another authored lowering.
All finite sorted contexts and recursively nested wrapper bodies are retained.
Private binder identities are constructed from the ambient frame, independently
of the payload's positions. Typing is the independent dependent source judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
namespace Dependent

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open PrivateIdentityContexts

variable {Head : Type}

def index : {Γ : Binding.Ctx Target.sig} → {s : Target.sig.Srt} →
    Binding.Var Γ s → Fin Γ.length
  | _, _, .zero => 0
  | _, _, .succ prior => (index prior).succ

def payload : {Γ : Binding.Ctx Target.sig} → {s : Target.sig.Srt} → Binding.Term Target.sig Γ s →
    Presentation.Tm Head Γ.length
  | _, _, .var occurrence => .var (index occurrence)
  | _, _, .op .app (.cons function (.cons argument .nil)) => .app (payload function) (payload argument)
  | _, _, .op .lam (.cons body .nil) => .lam (payload body)

def source : {Γ : Binding.Ctx sig} → Frame Γ.length → Program Γ →
    DeclaredBindingDependent.Source Head Γ.length
  | _, frame, .lambda body =>
      let name := frame.freshName "parameter"
      .lambda name (source (frame.extend name) body)
  | _, frame, .whereBinding value body =>
      let name := frame.freshName "pattern"
      .whereBinding name (.core (payload value)) (source (frame.extend name) body)
  | _, _, .result value => .result (.core (payload value))

theorem translation_meaning : ∀ {Γ : Binding.Ctx sig} (frame : Frame Γ.length)
    (program : Program Γ), DeclaredBindingDependent.translate (source (Head := Head) frame program) =
      payload program.meaning
  | _, frame, .lambda body => by
      simp only [source, DeclaredBindingDependent.translate, Program.meaning,
        LambdaContextualRung.lamT, payload, translation_meaning]
  | _, frame, .whereBinding value body => by
      simp only [source, DeclaredBindingDependent.translate, Program.meaning,
        LambdaContextualRung.appT, LambdaContextualRung.lamT, payload, translation_meaning]
  | _, _, .result value => rfl

/-- The established initial fold and the new dependent interpretation meet
at the same term, rather than two independently chosen implementations. -/
theorem interpretation_square {Γ : Binding.Ctx sig} (frame : Frame Γ.length)
    (program : Program Γ) :
    payload (Head := Head) (lower program.source) =
      DeclaredBindingDependent.translate (source frame program) := by
  rw [program.lower_source, translation_meaning]

theorem typed_authored_lowering {R : Presentation.Rules Head} {Γ : Binding.Ctx sig}
    {context : PrivateIdentityContexts.Context Head Γ.length} (program : Program Γ)
    {type : Presentation.Tm Head Γ.length}
    (typed : DeclaredBindingDependent.Typing R context (source context.frame program) type) :
    Presentation.FormationSensitive.Typing R context.erase (payload (lower program.source)) type := by
  rw [interpretation_square]
  exact DeclaredBindingDependent.typing_preservation typed

/-- The dependent bridge preserves the established occurrence addresses,
including those in recursively nested authored bodies. -/
theorem occurrences_agree : ∀ {Γ : Binding.Ctx sig} (frame : Frame Γ.length)
    (program : Program Γ),
    DeclaredBindingDependent.bindingOccurrences (source (Head := Head) frame program) =
      Provenance.bindingOccurrences program
  | _, frame, .lambda body => by
      simp only [source, DeclaredBindingDependent.bindingOccurrences,
        Provenance.bindingOccurrences, occurrences_agree]
  | _, frame, .whereBinding value body => by
      simp only [source, DeclaredBindingDependent.bindingOccurrences,
        Provenance.bindingOccurrences, List.map_nil, List.nil_append, occurrences_agree]
  | _, _, .result value => rfl

theorem retained_receipts_agree {Origin : Type} {Γ : Binding.Ctx sig}
    (frame : Frame Γ.length) (retained : Provenance.Retained Origin Γ) :
    (DeclaredBindingDependent.bindingOccurrences
      (source (Head := Head) frame retained.1.body)).map (fun path => (retained.2, path)) =
      Provenance.receipts retained := by
  rw [occurrences_agree]
  rfl

end Dependent
end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
