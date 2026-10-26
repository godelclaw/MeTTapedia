import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Certified assembly preserves the replaying builder's exact graph

The control shares one reflexivity node between two transitivity premises.
Structural assembly retains both parent occurrences, origins and node order.
Its result is checked independently; a changed conclusion is refused.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RetainedAssemblyControls
open Mettapedia.Languages.OpenTheory
open RetainedCompilation GraphExpansion ProofExecution
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def first : Origin := ("certified-assembly",17)
def second : Origin := ("certified-assembly",23)
def requests := GraphExpansion.Controls.sharedPlan first second

theorem localChecks : LocallyChecked emptyAxiomPolicy #[] requests :=
  GraphExpansion.Controls.sharedPlan_checked first second

def assembled : CheckedProof emptyAxiomPolicy :=
  CheckedProof.assemble requests 1 ProofExecution.Controls.reflexivityTheorem localChecks rfl

theorem exact_graph : assembled.certificate =
    ([ProofExecution.Controls.reflexivity first,ProofExecution.Controls.sharedTransitivity second],1) := rfl

theorem replayed_plan_same : finishPlan emptyAxiomPolicy (start []) #[] requests 1 = some assembled.certificate :=
  CheckedProof.assemble_matches_replayed_plan requests 1 ProofExecution.Controls.reflexivityTheorem localChecks rfl

theorem duplicate_parent_occurrences : (assembled.certificate.1[1]?).map (·.parents) = some [0,0] := rfl

theorem checked : (ProofSystem.checker emptyAxiomPolicy).check assembled.result assembled.certificate = true :=
  assembled.accepted

def forged : Theorem := {assembled.result with sequent :=
  ⟨∅,CanonicalTerm.free ⟨Name.global "forged_assembled_conclusion",Ty.bool⟩⟩}

theorem forged_refused : (ProofSystem.checker emptyAxiomPolicy).check forged assembled.certificate = false := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("certified-assembly/replayed-plan-available",(finishPlan emptyAxiomPolicy (start []) #[] requests 1).isSome),
   ("certified-assembly/duplicate-parent-occurrences",decide ((assembled.certificate.1[1]?).map (·.parents) = some [0,0])),
   ("certified-assembly/accepted",(ProofSystem.checker emptyAxiomPolicy).check assembled.result assembled.certificate),
   ("certified-assembly/forged-refused",!(ProofSystem.checker emptyAxiomPolicy).check forged assembled.certificate)]

#print axioms replayed_plan_same
#print axioms checked
#print axioms forged_refused
end Mettapedia.Languages.HOLLight.RetainedAssemblyControls
