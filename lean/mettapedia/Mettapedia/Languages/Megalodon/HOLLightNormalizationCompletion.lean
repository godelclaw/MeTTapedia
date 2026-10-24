import Mettapedia.Languages.Megalodon.HOLLightNormalization
import Mettapedia.Languages.Megalodon.NormalizationTermination

/-!
# Complete monomorphic normalization with HOL Light receipts

For every intrinsic monomorphic term in the native grammar, the actual
beta/eta normalizer computes a sufficient budget and its retained equality
compiles into an accepted primitive HOL Light certificate. The checked
sequent has no logical assumptions and states the exact translated equality.

The eta axiom policy remains explicit. Definition unfolding and prefix type
computation are outside this completion theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLLightNormalizationCompletion

open Mettapedia.Logic
open Mettapedia.Languages
open OpenTheory ReverseTranslation
open HenkinTermInterpretation HOLLightNormalization

variable {environment : MathdataKernel.Environment} {gamma : HOL.Ctx Base}
  {type : HOL.Ty Base}

/-- Compute the native normalization budget and compile its retained equality.
No successful-run premise or externally supplied fuel is required. -/
def certificate (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (source : HOL.Term (Constant environment) gamma type) {raw : MathdataKernel.Tm}
    (erased : erase source = some raw)
    (names : Naming (gamma.map (HOL.Ty.substitute base)))
    (origin : HOLLight.ProofExecution.Origin) :=
  let completed := NormalizationTermination.complete source erased
  HOLLightNormalization.certificate policy eta completed.val.1 source erased completed.property
    names origin

theorem certificate_accepted (policy : AxiomPolicy) [DecidablePred policy]
    (eta : policy EtaAxiom.sequent)
    (source : HOL.Term (Constant environment) gamma type) {raw : MathdataKernel.Tm}
    (erased : erase source = some raw)
    (names : Naming (gamma.map (HOL.Ty.substitute base)))
    (origin : HOLLight.ProofExecution.Origin) :
    (HOLLight.ProofSystem.checker policy).check
      (certificate policy eta source erased names origin).proof.result
      (certificate policy eta source erased names origin).proof.certificate = true :=
  HOLLightNormalization.certificate_accepted policy eta _ source erased
    (NormalizationTermination.complete source erased).property names origin

/-- The independently checked receipt states the precise computed equality,
with the source context retained and no added logical assumptions. -/
theorem certificate_sequent (policy : AxiomPolicy) [DecidablePred policy]
    (eta : policy EtaAxiom.sequent)
    (source : HOL.Term (Constant environment) gamma type) {raw : MathdataKernel.Tm}
    (erased : erase source = some raw)
    (names : Naming (gamma.map (HOL.Ty.substitute base)))
    (origin : HOLLight.ProofExecution.Origin) :
    (certificate policy eta source erased names origin).proof.result.sequent =
      let completed := NormalizationTermination.complete source erased
      ⟨∅, reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (HOL.mapTypes base constant (.eq source
          (RetainedNormalization.readback completed.val.1 source erased completed.property).val.target)))⟩ :=
  HOLLightNormalization.certificate_sequent policy eta _ source erased
    (NormalizationTermination.complete source erased).property names origin

#print axioms certificate
#print axioms certificate_accepted
#print axioms certificate_sequent

end Mettapedia.Languages.Megalodon.HOLLightNormalizationCompletion
