import Mettapedia.Languages.Megalodon.BudgetIndependent
import Mettapedia.Languages.MeTTa.Seal.NativeContract

/-!
# Megalodon inference through the shared seal service

The selected environment fixes the rule relation behind a brand. Public data,
equal printed names and client-generated boxes do not establish membership in
that brand. Every native capsule issued under the private kernel policy has
an original Mathdata proof and an independently replayable row certificate.

The policy requires the implementation's checked constructor to use retained
kernel code and declarations. A mutable client equation named like a helper
does not implement that policy. The native module must enforce this boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SealedInference
open MathdataKernel BorrowedProofCursor
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Languages.MeTTa

theorem native_capsule_has_original {environment : Environment}
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Judgment} {judgment : Judgment}
    (start : Seal.KernelStart (BudgetIndependent.UnboundedRules environment) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (BudgetIndependent.UnboundedRules environment) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data judgment) ∈ final.holds principal) :
    ∃ fuel proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition :=
  (BudgetIndependent.original_iff environment judgment).mp
    (Seal.NativeContract.lcf_original (BudgetIndependent.UnboundedRules environment) start reached held)

theorem native_capsule_has_certificate {environment : Environment}
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Judgment} {judgment : Judgment}
    (start : Seal.KernelStart (BudgetIndependent.UnboundedRules environment) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (BudgetIndependent.UnboundedRules environment) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data judgment) ∈ final.holds principal) :
    ∃ (nodes : List (Node Judgment (Nat × Witness) Nat)) (root : Nat),
      (CheckedJudgment.mint (BudgetIndependent.interface environment) nodes root).map
        CheckedJudgment.judgment = some judgment :=
  (CheckedJudgment.exists_mint_iff (BudgetIndependent.interface environment) (0 : Nat) judgment).mpr
    (Seal.NativeContract.lcf_original (BudgetIndependent.UnboundedRules environment) start reached held)

/-- The public inference service can construct every original finite proof;
the private sealer is sufficient and need never be given to its clients. -/
theorem original_has_sealed_run {environment : Environment} {fuel : Nat} {proof : Pf}
    {judgment : Judgment} {kernel brand index : Nat} (initial : Seal.Config Judgment)
    (sealer : initial.held kernel index = some (.cap brand Seal.Rights.both))
    (accepted : inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition) :
    ∃ final, Seal.Reach (Seal.kernelPolicy (BudgetIndependent.UnboundedRules environment) kernel brand)
      initial final ∧ Seal.Val.box brand (.data judgment) ∈ final.holds kernel :=
  Seal.lcf_complete (BudgetIndependent.UnboundedRules environment)
    ((BudgetIndependent.original_iff environment judgment).mpr ⟨fuel, proof, accepted⟩) initial sealer

/-- No quantity of client-side activity creates a theorem outside the selected
kernel's derivation relation, provided its private sealing policy is upheld. -/
theorem native_forgery_excluded {environment : Environment}
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Judgment} {judgment : Judgment}
    (start : Seal.KernelStart (BudgetIndependent.UnboundedRules environment) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (BudgetIndependent.UnboundedRules environment) kernel brand) initial final)
    (impossible : ∀ fuel proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof ≠ some judgment.proposition) :
    Seal.NativeContract.Value.box identity brand (.data judgment) ∉ final.holds principal := by
  intro held
  obtain ⟨fuel, proof, checked⟩ := native_capsule_has_original start reached held
  exact impossible fuel proof checked

end Mettapedia.Languages.Megalodon.SealedInference
