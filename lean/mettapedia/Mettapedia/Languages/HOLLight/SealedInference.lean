import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.MeTTa.Seal.NativeContract

/-!
# HOL Light inference through the shared seal contract

The brand is indexed by the actual HOL rule policy. A theorem capsule issued
under that policy has a source derivation, an independently replayable graph,
and a finite source GSLT execution. Under the empty axiom policy its claim
also has the existing extensional Henkin interpretation.

The hypotheses describe the implementation boundary: private minting must
follow the checked native rule operation and its fixed policy. This does not
verify the C adapter, its owner counts, or its allocator. Exposing the same
display name or constructing an ordinary expression does not meet the held
capsule hypothesis in a well-formed reached configuration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.SealedInference

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open Mettapedia.Languages.MeTTa

theorem capsule_has_source_derivation (policy : AxiomPolicy)
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Theorem} {claim : Theorem}
    (start : Seal.KernelStart (Rule policy) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rule policy) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data claim) ∈
      final.holds principal) : Derives (Rule policy) claim :=
  Seal.NativeContract.lcf_original (Rule policy) start reached held

/-- Retained authority reconstructs both an executable graph and a finite
run of the original rule presentation; the checked graph is not a new axiom. -/
theorem capsule_has_graph_and_execution (policy : AxiomPolicy) [DecidablePred policy]
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Theorem} {claim : Theorem}
    (start : Seal.KernelStart (Rule policy) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rule policy) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data claim) ∈
      final.holds principal) :
    (∃ certificate, (ProofSystem.checker policy).check claim certificate = true) ∧
      ∃ after, (ProofExecution.gslt policy).MultiStep ProofExecution.empty after ∧
        claim ∈ after.cache := by
  have derived := capsule_has_source_derivation policy start reached held
  exact ⟨(ProofSystem.checker_authority policy).complete claim derived,
    (ProofExecution.derives_iff_reachable policy claim).mp derived⟩

theorem capsule_has_extensional_meaning
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Theorem} {claim : Theorem}
    (start : Seal.KernelStart (Rule emptyAxiomPolicy) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rule emptyAxiomPolicy) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data claim) ∈
      final.holds principal)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv) :
    ∃ formula, Translates [] claim.sequent.concl.term .prop formula ∧
      ((∀ hypothesis ∈ translatedHypotheses claim.sequent.hyp, model.models hypothesis) →
        model.models formula) := by
  obtain ⟨certificate, checked⟩ :=
    (capsule_has_graph_and_execution emptyAxiomPolicy start reached held).1
  exact ProofSystem.checker_models checked model extensional

/-- A refutation of source derivability excludes the corresponding native
capsule throughout every client trace licensed by the fixed kernel policy. -/
theorem source_impossible_excludes_capsule (policy : AxiomPolicy)
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Theorem} {claim : Theorem}
    (start : Seal.KernelStart (Rule policy) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rule policy) kernel brand) initial final)
    (impossible : ¬ Derives (Rule policy) claim) :
    Seal.NativeContract.Value.box identity brand (.data claim) ∉ final.holds principal :=
  fun held => impossible (capsule_has_source_derivation policy start reached held)

#print axioms capsule_has_graph_and_execution
#print axioms capsule_has_extensional_meaning
#print axioms source_impossible_excludes_capsule

end Mettapedia.Languages.HOLLight.SealedInference
