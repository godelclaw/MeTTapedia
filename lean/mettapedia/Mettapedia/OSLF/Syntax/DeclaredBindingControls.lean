import Mettapedia.OSLF.Syntax.DeclaredBindingSource
import Mettapedia.OSLF.Syntax.DeclaredBindingProvenance
import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Scope and transport controls for the authored binding interpretation

The named grammar is an explicit mathematical source fragment, not a claim
about the runtime reader. Its resolution constructs the previously admitted
intrinsic program. The capturing raw fold intentionally fails the transport
law and therefore is not supplied as a substitution-compatible model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Controls

open FreeBindingTerms

/-- The derived interpretation is essential: neither target constructor has
the unbound unary arity of the transparent `result` operation. -/
theorem no_strict_signature_morphism : ¬ Nonempty (SigMor sig Target.sig) := by
  rintro ⟨strict⟩
  have arity := strict.carriesArity Op.result
  cases actual : strict.opMap Op.result with
  | app =>
      rw [actual] at arity
      simp [sig, Target.sig, LambdaContextualRung.sig, mapArities, mapArity] at arity
  | lam =>
      rw [actual] at arity
      simp [sig, Target.sig, LambdaContextualRung.sig, mapArities, mapArity] at arity


def nested : Program [.term] :=
  .lambda (.lambda (.result (LambdaContextualRung.appT (.var (.succ .zero))
    (LambdaContextualRung.appT (.var .zero) (.var (.succ (.succ .zero)))))))

def identity {Γ : Ctx Target.sig} : Term Target.sig Γ .term :=
  LambdaContextualRung.lamT (.var .zero)

def supplyIdentity : Sub Target.sig [.term] []
  | _, .zero => identity

def closedIntoOpen : Ren Target.sig [] [.term] := fun _ impossible => nomatch impossible

theorem nested_binders_and_live_dependency :
    lower nested.source = LambdaContextualRung.lamT (LambdaContextualRung.lamT
      (LambdaContextualRung.appT (.var (.succ .zero))
        (LambdaContextualRung.appT (.var .zero) (.var (.succ (.succ .zero)))))) := rfl

theorem substitution_keeps_nested_locals :
    lower (nested.substitute supplyIdentity).source =
      LambdaContextualRung.lamT (LambdaContextualRung.lamT
        (LambdaContextualRung.appT (.var (.succ .zero))
          (LambdaContextualRung.appT (.var .zero) identity))) := rfl

theorem free_dependency_is_observable :
    lower nested.source ≠ lower ((nested.substitute supplyIdentity).renamed closedIntoOpen).source := by
  intro equal
  have sizes := congrArg termSize equal
  change 7 = 8 at sizes
  omega

/-- Deliberately wrong: an extra scope captures the value's ambient names.
The independently scoped body keeps its own parameter through the lift. -/
def capturingOperation {Γ : Ctx sig} {s : sig.Srt} (op : sig.Op s)
    (args : FamilyArgs sig (Term Target.sig) (sig.arity op) Γ) : Term Target.sig Γ s :=
  match op with
  | .baseApp => operation (BindingCloneAlgebra.terms Target.sig) .baseApp args
  | .baseLam => operation (BindingCloneAlgebra.terms Target.sig) .baseLam args
  | .lambda => operation (BindingCloneAlgebra.terms Target.sig) .lambda args
  | .result => operation (BindingCloneAlgebra.terms Target.sig) .result args
  | .whereBinding => LambdaContextualRung.lamT
      (LambdaContextualRung.appT
        (LambdaContextualRung.lamT (rename
          (liftRen (Srt := LambdaContextualRung.Srt)
            (fun _ x => Var.succ x) [LambdaContextualRung.Srt.term])
          (argumentHead (argumentTail args))))
        (bind (fun sort _ => match sort with | .term => .var .zero) (argumentHead args)))

def capturingRawModel : FreeBindingTerms.Algebra sig where
  Carrier := Term Target.sig
  injectVar := fun x => Term.var (S := Target.sig) x
  operation := capturingOperation

def capturingLower {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) : Term Target.sig Γ s :=
  fold capturingRawModel term

def whereOpen : Term sig [.term] .term := whereBinding (.var .zero) (.var .zero)

def sourceSupplyIdentity : Sub sig [.term] []
  | _, .zero => embed identity

/-- This actual alternative fold fails the general substitution square;
the negative is not merely failure to construct an interface instance. -/
theorem capturing_interpretation_breaks_substitution :
    capturingLower (bind sourceSupplyIdentity whereOpen) ≠
      bind (fun s x => capturingLower (sourceSupplyIdentity s x)) (capturingLower whereOpen) := by
  intro equal
  have sizes := congrArg termSize equal
  change 6 = 5 at sizes
  omega

theorem result_erasure_changes_source :
    result (Term.var (S := sig)
      (.zero : Var [LambdaContextualRung.Srt.term] LambdaContextualRung.Srt.term)) ≠ .var .zero := by
  intro equal
  cases equal

theorem result_erasure_keeps_target :
    lower (result (Term.var (S := sig)
      (.zero : Var [LambdaContextualRung.Srt.term] LambdaContextualRung.Srt.term))) = lower (.var .zero) :=
  lower_result _

theorem where_advances_and_preserves_denotation :
    Step whereOpen (.var .zero) ∧
      LambdaContextualRung.Step [.term] (lower whereOpen) (.var .zero) ∧
      lower whereOpen ≠ (.var .zero : Term Target.sig [.term] .term) ∧
      BetaModel.denote whereOpen = BetaModel.denote (.var .zero) := by
  refine ⟨Step.whereBeta _ _, where_lower_step _ _, ?_, BetaModel.denote_where_beta _ _⟩
  intro equal
  cases equal

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Controls
