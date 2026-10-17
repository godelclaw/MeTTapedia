import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

/-!
# Native proof services for original authored occurrence receipts

The fixed service parameters retain the actual plan, dynamic provider,
bound context and result type. Its proof language is the original receipt
language; its judgment is original receipt validity with the literal result.
The total validator checks each finite receipt without restricting recursive
child declaration indices. No search-completeness or physical-time claim is
inferred from total certificate validation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeEvidence

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open KernelAuthority SemanticEvidence

/-- The request fixes both original source and original replacement result. -/
abbrev Claim := Pattern × Pattern
abbrev Proof := GeneralRuleJobs.Receipt

/-- Original source authority, before choosing a checker implementation. -/
def Meaning (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : Prop :=
  ∃ proof : Proof, proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2

def target (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionObject where
  Carrier := Claim
  Meaning := Meaning dynamic plan bound type

/-- Native proof objects retain declaration/occurrence identity, both
matching traces, captured/completed bindings and the entire finite history. -/
def guest (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : NativeProofSystem Claim where
  ProofObject := Proof
  Judges proof claim := proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2

def check (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : Bool :=
  GeneralRewriteRecipe.checkFiringWith dynamic plan bound type claim.1 proof && decide (proof.target = claim.2)

theorem check_exact (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) :
    check dynamic plan bound type claim proof = true ↔
      proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  simp only [check, Bool.and_eq_true, GeneralRewriteRecipe.checkFiringWith_exact, decide_eq_true_eq]

def kernel (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : NativeProofKernel (guest dynamic plan bound type) where
  decide := check dynamic plan bound type
  correct := check_exact dynamic plan bound type

theorem meaning_exact (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) :
    Meaning dynamic plan bound type claim ↔ Nonempty ((guest dynamic plan bound type).ProofFibre claim) := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨⟨proof, valid⟩⟩
  · rintro ⟨⟨proof, valid⟩⟩
    exact ⟨proof, valid⟩

def service (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : SemanticService.Service (target dynamic plan bound type) :=
  .nativeProof (guest dynamic plan bound type) (kernel dynamic plan bound type)
    (meaning_exact dynamic plan bound type)

def request (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) :
    SemanticServiceInvocation.Request (service dynamic plan bound type) := .nativeProof claim proof

theorem invocation_exact (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) :
    (SemanticServiceInvocation.invoke (request dynamic plan bound type claim proof)).acceptedValue =
      some claim ↔ proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  change (if check dynamic plan bound type claim proof then some claim else none) = some claim ↔ _
  rw [← check_exact]
  cases check dynamic plan bound type claim proof <;> simp

/-- Every original valid receipt is accepted as itself. No proof search,
certificate expansion or change of evidence language is needed. -/
theorem original_receipt_accepted (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type source) :
    (SemanticServiceInvocation.invoke
      (request dynamic plan bound type (source, proof.target) proof)).acceptedValue =
        some (source, proof.target) :=
  (invocation_exact dynamic plan bound type _ proof).mpr ⟨valid, rfl⟩

theorem source_iff_service (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    Meaning dynamic plan bound type claim ↔ ∃ proof : Proof,
      (SemanticServiceInvocation.invoke (request dynamic plan bound type claim proof)).acceptedValue = some claim := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨proof, (invocation_exact dynamic plan bound type claim proof).mpr valid⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨proof, (invocation_exact dynamic plan bound type claim proof).mp accepted⟩

/-- A forged result is refused even if the retained local source evidence
happens to be valid. The literal submitted result is part of the judgment. -/
theorem wrong_result_refused (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof)
    (wrong : proof.target ≠ claim.2) : check dynamic plan bound type claim proof = false := by
  simp only [check, decide_eq_false wrong, Bool.and_false]

end Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeEvidence
