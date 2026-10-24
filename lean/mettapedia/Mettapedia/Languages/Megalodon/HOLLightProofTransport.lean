import Mettapedia.Languages.Megalodon.CheckedProofReconstruction
import Mettapedia.Languages.Megalodon.HOLLightNormalization

/-!
# Checked Megalodon proofs transported to primitive HOL Light certificates

The admitted monomorphic proof representation is reconstructed with its exact
authored conclusion. Known facts and defining equations stay explicit source
assumptions. The typed name translation and complete HOL compiler then emit
an actual primitive certificate, including equality evidence for beta/eta/delta
conversion. HOL Light hypotheses are finite sets, so this last step forgets
ordered assumption occurrences. Prefix-polymorphic proofs and a forward
compiler from arbitrary HOL proofs to Megalodon remain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.HOLLightProofTransport
open MathdataKernel HenkinTermInterpretation HenkinTermInterpretation.NativeProof
open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open CheckedProofReconstruction

variable {environment : Environment} {Γ : HOL.Ctx HenkinTermInterpretation.Base}
    {rawHypotheses : List Tm} {rawGoal : Tm}

/-- Transport a supplied accepted proof, not a chosen witness of derivability. -/
def compile (checked : CheckedPlainDefinitions environment)
    (theory : List (HOL.ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) (hypotheses : List (HOL.Formula (Constant environment) Γ))
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : HOL.Formula (Constant environment) Γ)
    (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true)
    (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute HOLLightNormalization.base)))
    (origin : HOLLight.ProofExecution.Origin) :=
  let retained := checkedSourceDefined checked theory equations known fuel depth
    hypotheses erased proof fragment goal goalErased accepted
  HOLLight.RetainedCompilation.compile policy eta
    (HOL.ProofSyntax.mapTypes HOLLightNormalization.base HOLLightNormalization.constant retained) names origin

theorem compile_accepted (checked : CheckedPlainDefinitions environment)
    (theory : List (HOL.ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) (hypotheses : List (HOL.Formula (Constant environment) Γ))
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : HOL.Formula (Constant environment) Γ)
    (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true)
    (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute HOLLightNormalization.base)))
    (origin : HOLLight.ProofExecution.Origin) :
    (HOLLight.ProofSystem.checker policy).check
      (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
        accepted policy eta names origin).proof.result
      (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
        accepted policy eta names origin).proof.certificate = true :=
  (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
    accepted policy eta names origin).proof.accepted

/-- Exact conclusion and hypotheses: each defining premise remains in the
translated sequent. There is no extra axiom that declares the whole claim. -/
theorem compile_sequent (checked : CheckedPlainDefinitions environment)
    (theory : List (HOL.ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) (hypotheses : List (HOL.Formula (Constant environment) Γ))
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : HOL.Formula (Constant environment) Γ)
    (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true)
    (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute HOLLightNormalization.base)))
    (origin : HOLLight.ProofExecution.Origin) :
    (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
      accepted policy eta names origin).proof.result.sequent =
    ⟨ReverseTranslation.reverseHypotheses names
      ((hypotheses ++ facts theory Γ).map (fun formula => HOL.ImpredicativeConnectives.expand
        (HOL.mapTypes HOLLightNormalization.base HOLLightNormalization.constant formula))),
     ReverseTranslation.reverseCanonical names (HOL.ImpredicativeConnectives.expand
       (HOL.mapTypes HOLLightNormalization.base HOLLightNormalization.constant goal))⟩ := by
  apply Sequent.ext
  · refine (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
        accepted policy eta names origin).hypotheses_exact.trans ?_
    apply congrArg (ReverseTranslation.reverseHypotheses names)
    exact List.map_map
  · exact (compile checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased
        accepted policy eta names origin).conclusion_exact

end Mettapedia.Languages.Megalodon.HOLLightProofTransport
