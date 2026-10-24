import Mettapedia.Languages.Megalodon.SetOperationCompilerAcceptance
import Mathlib.Data.Nat.Find

/-!
# Executable checking budgets for complete material HOL compilation

The all-constructor acceptance theorem licenses a computable search for the
least successful reference-checker normalization budget. The supplied source
proof determines the actual program, declaration instances, ordered canonical
hypotheses and authored conclusion before the budget is selected.

This parameter bounds the checker's normalization passes. Certificate size,
receipt grades and native runtime costs are separate quantities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SetOperationCheckedCompilation

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms
open SetOperationExtensionality SetOperationCompilerAcceptance

variable {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
variable {conclusion : Formula Symbol gamma}

def checkingBudget (source : ProofSyntax Symbol assumptions conclusion) : Nat :=
  Nat.find (accepted_required source)

theorem checkingBudget_accepted (source : ProofSyntax Symbol assumptions conclusion) :
    checkProof (environment (requiredInstances source)) (checkingBudget source) 0
      ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => normalFormCode (term (requiredInstances source) formula)))
      (compile (requiredInstances source) source)
      (native (term (requiredInstances source) conclusion)) = true :=
  Nat.find_spec (accepted_required source)

theorem checkingBudget_failure_below (source : ProofSyntax Symbol assumptions conclusion)
    {budget : Nat} (below : budget < checkingBudget source) :
    checkProof (environment (requiredInstances source)) budget 0
      ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => normalFormCode (term (requiredInstances source) formula)))
      (compile (requiredInstances source) source)
      (native (term (requiredInstances source) conclusion)) = false :=
  Bool.eq_false_iff.mpr (Nat.find_min (accepted_required source) below)

theorem checkingBudget_le (source : ProofSyntax Symbol assumptions conclusion) {budget : Nat}
    (accepted : checkProof (environment (requiredInstances source)) budget 0
      ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => normalFormCode (term (requiredInstances source) formula)))
      (compile (requiredInstances source) source)
      (native (term (requiredInstances source) conclusion)) = true) :
    checkingBudget source ≤ budget :=
  Nat.find_min' (accepted_required source) accepted

#print axioms checkingBudget
#print axioms checkingBudget_accepted
#print axioms checkingBudget_failure_below
#print axioms checkingBudget_le

end Mettapedia.Languages.Megalodon.SetOperationCheckedCompilation
