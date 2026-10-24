import Mettapedia.Languages.Megalodon.SourceRuleProof
import Mettapedia.Languages.Megalodon.NormalizationNormalForm

/-!
# Sufficient native budgets for typed proof applications

Proof application joins already checked programs at one common budget. Term
application additionally computes a sufficient normalization budget for its
typed substituted body. The environment, ordered hypotheses and actual proof
programs are retained throughout. Context support and native annotation
formation remain explicit premises, rather than assumed checking outcomes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.TypedProofApplication

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation ProofJudgment

theorem proof_application {environment : Environment} {first second : Nat}
    {context : Context} {function argument : Pf} {domain codomain : Tm}
    (functionDerived : Proves environment first context function (.imp domain codomain))
    (argumentDerived : Proves environment second context argument domain) :
    Proves environment (max first second) context (.proofApp function argument) codomain :=
  .proofApp (SourceCursor.proof_mono (Nat.le_max_left _ _) functionDerived)
    (SourceCursor.proof_mono (Nat.le_max_right _ _) argumentDerived)

/-- The typed argument and body supply a terminating contractum. The normal
support of the body follows from the existing checked function judgment. -/
theorem term_application {environment : Environment} {gamma : Ctx Base} {domain : Ty Base}
    {functionFuel depth : Nat} {hypotheses : List Tm} {function : Pf}
    (body : Formula (Constant environment) (domain :: gamma)) {bodyRaw : Tm}
    (bodyErased : erase body = some bodyRaw)
    (argument : Term (Constant environment) gamma domain) {argumentRaw : Tm}
    (argumentErased : erase argument = some argumentRaw)
    (argumentFormed : plainAnnotations depth argumentRaw = true)
    (argumentNormal : DeltaNormalInvariant.Normal environment argumentRaw)
    (contextNormal : DeltaNormalInvariant.ContextNormal environment
      ⟨depth, gamma.map reifyType, hypotheses⟩)
    (functionDerived : Proves environment functionFuel
      ⟨depth, gamma.map reifyType, hypotheses⟩ function (.all (reifyType domain) bodyRaw)) :
    ∃ fuel output,
      MathdataKernel.normalize environment fuel (Tm.instantiate argumentRaw bodyRaw) = some output ∧
      Proves environment fuel ⟨depth, gamma.map reifyType, hypotheses⟩
        (.termApp function argumentRaw) output := by
  have bodyNormal : DeltaNormalInvariant.Normal environment bodyRaw := by
    simpa only [DeltaNormalInvariant.Normal, NativeSupport.termSupport] using
      (DeltaNormalInvariant.inferred_normal functionDerived contextNormal)
  have substitutedErased : erase (instantiate argument body) =
      some (Tm.instantiate argumentRaw bodyRaw) := by
    rw [erase_instantiate argument body argumentErased, bodyErased]
    rfl
  let completed := NormalizationTermination.completeNative (instantiate argument body)
    substitutedErased (DeltaNormalInvariant.instantiate bodyNormal argumentNormal)
  let fuel := max functionFuel completed.val.1
  have normalized := FuelledConversionProfile.normalize_mono environment _ _
    (Nat.le_max_right functionFuel completed.val.1) completed.property
  refine ⟨fuel, completed.val.2, normalized, ?_⟩
  exact .termApp (SourceCursor.proof_mono (Nat.le_max_left _ _) functionDerived)
    (infer_of_erase argument argumentErased argumentFormed)
    (DeltaNormalInvariant.fixed argumentNormal fuel) normalized

#print axioms proof_application
#print axioms term_application

end Mettapedia.Languages.Megalodon.TypedProofApplication
