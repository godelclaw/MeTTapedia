import Mettapedia.Languages.Megalodon.SetOperationProofReconstruction
import Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation

/-!
# Checked common-profile Megalodon proofs in maintained MM0 HOL

An accepted Megalodon program is reconstructed as an ordinary source proof
with its exact common-signature assumptions and conclusion. The independent
MM0 compiler constructs its checked witness over the material parameter
context. The components share the same closed source judgment; no global
extensionality assumptions are appended during reconstruction.

The native MM0 format and its parameter bound remain a separate qualification
boundary. The returned mathematical witness uses the existing unbounded
finite-context reference kernel and constructs its complete allocation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.MM0ProofTransport
open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation
open HenkinTermInterpretation.NativeProof
open Embedding.ZFSetHenkinInterpretation (Symbol)
open Mettapedia.Languages.MM0

variable {sorts : Kernel.SortSignature} {terms : Kernel.TermSignature} {definitions : Kernel.Definition.Signature}
variable {theorems : Kernel.TheoremSignature}

/-- Exact closed source readback followed by actual maintained-MM0 proof
construction. Its target assumptions stay in the encoded logical antecedent. -/
def compile (instances : List (Ty Base × Ty Base)) (fuel depth : Nat)
    (assumptions : List (ClosedFormula Symbol)) (goal : ClosedFormula Symbol) (program : Pf)
    (fragment : Fragment (SetOperationExtensionality.environment instances) depth program)
    (accepted : checkProof (SetOperationExtensionality.environment instances) fuel depth []
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
      program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true)
    (signature : HOLKernelSyntax.Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference) :
    let source := SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted
    HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := (HOLKernelProofAllocation.forProof source).target
        (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object) (hypotheses := [])
      (HOLKernelSetOperationInterpretation.statement signature.symbol assumptions goal) :=
  HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
    (SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted)

theorem compile_accepted (instances : List (Ty Base × Ty Base)) (fuel depth : Nat)
    (assumptions : List (ClosedFormula Symbol)) (goal : ClosedFormula Symbol) (program : Pf)
    (fragment : Fragment (SetOperationExtensionality.environment instances) depth program)
    (accepted : checkProof (SetOperationExtensionality.environment instances) fuel depth []
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
      program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true)
    (signature : HOLKernelSyntax.Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference) :
    let source := SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted
    (compile instances fuel depth assumptions goal program fragment accepted signature abbreviation profile structural typing rules binding).val.check
      terms definitions theorems
      ((HOLKernelProofAllocation.forProof source).target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object) []
      (HOLKernelSetOperationInterpretation.statement signature.symbol assumptions goal) = true :=
  (Kernel.ProofWitness.check_iff _ _ _ _ _ _ _).mpr
    (compile instances fuel depth assumptions goal program fragment accepted signature abbreviation profile structural typing rules binding).property

#print axioms compile
#print axioms compile_accepted
end Mettapedia.Languages.Megalodon.MM0ProofTransport
