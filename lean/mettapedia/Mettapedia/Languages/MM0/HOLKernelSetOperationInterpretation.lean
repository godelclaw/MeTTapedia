import Mettapedia.Languages.MM0.HOLKernelProofCompilation
import Mettapedia.Languages.MM0.HOLKernelSetOperationSyntax

/-!
# The common six-operation HOL signature in maintained MM0 HOL

A regular type parameter and six distinct regular term parameters represent
material sets and their operations. Their object-level typings form an explicit
formation antecedent; source formulas remain separate ordered assumptions.
The complete retained proof compiler uses this context without adding any
set-theoretic axioms to the maintained MM0 theory.

The six operations retain distinct native names even when their types agree.
The interpretation permits equal values and keeps native bound-name freshness
separate from material equality. Source reflection and the native byte boundary
are separate obligations from this constructive forward interpretation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation
open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation (Symbol set predicate mapping)
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed)
open HOLKernelStructuralRules (CheckedProof)
open HOLKernelProofAllocation
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature}


theorem binderName_eq (ids : SortIds) : binderName = Layout.names (initialContext ids) := rfl

def compile (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {assumptions : List Formula} {conclusion : Formula} (proof : ProofSyntax Symbol assumptions conclusion) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := (forProof proof).target (initialContext signature.ids) signature.ids.object) (hypotheses := [])
      (statement signature.symbol assumptions conclusion) := by
  exact HOLKernelProofCompilation.compileFromInitial signature abbreviation profile structural typing rules binding
    (initialContext_formed signature) typeCode (fun {_} symbol => symbolCode symbol)
    (typeCode_sorted signature) (symbolCode_sorted signature) noAssignment
    (by intro type index; nomatch index) (formation signature.symbol) (formation_sorted signature)
    (by intro type index; nomatch index) (constantTyping signature structural) proof

theorem compile_accepted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {assumptions : List Formula} {conclusion : Formula} (proof : ProofSyntax Symbol assumptions conclusion) :
    (compile signature abbreviation profile structural typing rules binding proof).val.check terms definitions theorems
      ((forProof proof).target (initialContext signature.ids) signature.ids.object) []
      (statement signature.symbol assumptions conclusion) = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr (compile signature abbreviation profile structural typing rules binding proof).property

#print axioms initialContext_formed
#print axioms symbolIndex_injective
#print axioms constantTyping
#print axioms compile
#print axioms compile_accepted
end Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation
