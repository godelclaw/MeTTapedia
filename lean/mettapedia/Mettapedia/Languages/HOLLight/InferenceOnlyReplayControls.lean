import Mettapedia.Languages.HOLLight.InferenceOnlyReplay
import Mettapedia.Languages.HOLLight.ExtensionalityExpansion

/-!
# A root with empty dependencies can retain an earlier axiom node

The first physical node uses the existing eta policy. The selected second
node is an independent reflexivity theorem with empty axiom dependencies.
The complete graph is accepted with the eta license and refused by the empty
policy. Thus root metadata alone does not imply policy-independent replay.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.InferenceOnlyReplay.Controls
open Mettapedia.Languages.OpenTheory
open GraphExpansion EqualityExpansion

local instance : DecidablePred etaAxiomPolicy :=
  fun claim => inferInstanceAs (Decidable (claim = EtaAxiom.sequent))
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def independentRoot : Theorem := reflexivity EtaAxiom.sequent.concl

def retainedAxiom : ProofExecution.Receipt :=
  ⟨ExtensionalityExpansion.etaAxiomTheorem, .axiom EtaAxiom.sequent, [], ("retained-eta", 0)⟩

def rootReceipt : ProofExecution.Receipt :=
  ⟨independentRoot, .inference (.refl EtaAxiom.sequent.concl), [], ("independent-refl", 1)⟩

def certificate : ProofSystem.Certificate := ([retainedAxiom, rootReceipt], 1)

theorem root_axioms_empty : independentRoot.axioms = ∅ := rfl

theorem retained_axiom_visible : inferenceOnly certificate.1 = false := rfl

theorem licensed_replay : (ProofSystem.checker etaAxiomPolicy).check independentRoot certificate = true := by
  decide +kernel

theorem empty_replay_refused : (ProofSystem.checker emptyAxiomPolicy).check independentRoot certificate = false := by
  decide +kernel

theorem policy_difference : (ProofSystem.checker etaAxiomPolicy).check independentRoot certificate ≠
    (ProofSystem.checker emptyAxiomPolicy).check independentRoot certificate := by
  rw [licensed_replay, empty_replay_refused]
  decide

theorem inference_node_policies : rootReceipt.replay (ruleWitness etaAxiomPolicy) #[] =
    rootReceipt.replay (ruleWitness emptyAxiomPolicy) #[] :=
  node_replay etaAxiomPolicy emptyAxiomPolicy rootReceipt #[] rfl

theorem inference_graph_policies :
    Mettapedia.Logic.DerivationGraph.replayFrom (ruleWitness etaAxiomPolicy) #[] [rootReceipt] =
      Mettapedia.Logic.DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) #[] [rootReceipt] :=
  replay_from etaAxiomPolicy emptyAxiomPolicy [rootReceipt] rfl #[]

def verdicts : List (String × Bool) :=
  [("independent root has empty axiom dependencies", decide (independentRoot.axioms = ∅)),
   ("earlier retained axiom remains visible", !(inferenceOnly certificate.1)),
   ("licensed whole graph replays", (ProofSystem.checker etaAxiomPolicy).check independentRoot certificate),
   ("empty policy refuses the earlier retained axiom", !((ProofSystem.checker emptyAxiomPolicy).check independentRoot certificate))]

#print axioms licensed_replay
#print axioms empty_replay_refused
#print axioms policy_difference
end Mettapedia.Languages.HOLLight.InferenceOnlyReplay.Controls
