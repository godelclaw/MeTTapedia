import Mettapedia.OSLF.Syntax.RhoPayloadParameterizedRuntime
import Mettapedia.OSLF.Syntax.RhoQuoteSafeCommComparison

/-!
# Intrinsic COMM receipts at the admitted payload-runtime boundary

The original name-binding rule generator has an actual authored firing and
an actual firing in the independently interpreted payload presentation.
Its intrinsic and authored immediate reducts retain the established residual
comparison; they are not identified as structural equation classes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoPayloadIntrinsicCommComparison

open Mettapedia.OSLF.Binding
open RhoSchema RhoSchema.IntrinsicEncoding RhoSemanticRulePolynomial
open RhoAuthoredCommRuleCover RhoQuoteSafeCommComparison
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (FreeSortContext)
open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

private abbrev raw := BindingCloneAlgebra.terms sig

theorem empty_names_only (name : String) :
    FreeSortContext.empty name ≠ some rhoReflectivePresentation.processSort := by
  change none ≠ some "Proc"
  decide

/-- The receipt retains both independently formed reducts, the supplied
intrinsic generator, and the actual strict payload firing. -/
structure CommReceipt (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) where
  source : ParameterizedRewriteSystem.Process FreeSortContext.empty
  authoredTarget : ParameterizedRewriteSystem.Process FreeSortContext.empty
  intrinsicTarget : ParameterizedRewriteSystem.Process FreeSortContext.empty
  sourceReadout : source.1 = authoredInputFirst channel payload body
  authoredReadout : authoredTarget.1 = authoredResult payload body
  intrinsicReadout : intrinsicTarget.1 = encodeTerm (commTarget raw payload body)
  authoredFiring : RhoStep source.1 authoredTarget.1
  payloadFiring : RhoPayloadParameterizedRuntime.targetTheory.Step
    (RhoPayloadParameterizedRuntime.mapClass empty_names_only source)
    (RhoPayloadParameterizedRuntime.mapClass empty_names_only authoredTarget)
  sourceComparison : StructuralCongruence
    (encodeTerm (intrinsicSource channel payload body)) source.1
  residualComparison : ProcResidualEquiv authoredTarget.1 intrinsicTarget.1
  intrinsicTree :
    (rules (FreeBindingEquationModel.presented rhoSourceE).algebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom
        (FreeBindingEquationModel.presented rhoSourceE).algebra)
        (judgment raw (intrinsicSource channel payload body) (commTarget raw payload body)))

def interpret_comm (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) : CommReceipt channel payload body := by
  obtain ⟨sourceAdmitted, firing, sourceComparison, residual⟩ :=
    authored_comm_residual_simulation channel payload body channelSafe payloadSafe bodySafe
  obtain ⟨authoredAdmitted, intrinsicAdmitted, _, _⟩ :=
    authored_comm_both_targets_admitted channel payload body channelSafe payloadSafe bodySafe
  let source : ParameterizedRewriteSystem.Process FreeSortContext.empty :=
    ⟨authoredInputFirst channel payload body, sourceAdmitted⟩
  let authoredTarget : ParameterizedRewriteSystem.Process FreeSortContext.empty :=
    ⟨authoredResult payload body, authoredAdmitted⟩
  let intrinsicTarget : ParameterizedRewriteSystem.Process FreeSortContext.empty :=
    ⟨encodeTerm (commTarget raw payload body), intrinsicAdmitted⟩
  exact ⟨source, authoredTarget, intrinsicTarget, rfl, rfl, rfl, firing,
    RhoPayloadParameterizedRuntime.raw_step empty_names_only firing,
    sourceComparison, residual, sourceEquationCommTree channel payload body⟩

variable {channel : Term sig [] Srt.nm} {payload : Term sig [] Srt.pr}
variable {body : Term sig [Srt.nm] Srt.pr}

theorem CommReceipt.residual_observation (receipt : CommReceipt channel payload body)
    (predicate : ProcPred) (respects : ProcPredRespectsResidualEquiv predicate) :
    predicate receipt.authoredTarget.1 ↔ predicate receipt.intrinsicTarget.1 :=
  ⟨respects receipt.residualComparison,
    respects (ProcResidualEquiv.symm receipt.residualComparison)⟩

end Mettapedia.OSLF.Binding.RhoPayloadIntrinsicCommComparison
