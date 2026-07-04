import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TwoLayerEscape

namespace Mettapedia.GraphTheory.FourColor

/-!
# Section 9.2 two-sided avoidance probe

The finite probe strengthens the collar certification by rejecting Kempe
components that touch either external side of the tested open chain.  The
length-2 tau/tau fiber below shows that this strengthened relation is too
strong for per-input connectivity: the witness pair is connected by the
ordinary input-avoiding certificate, and that certificate necessarily uses
the output side.
-/

namespace GoertzelLemma818TwoSidedAvoidance

open GoertzelLemma814
open GoertzelLemma818TwoLayerEscape

def chainOuterOutputEdges (orients : List TauOrient) : List ChainEdge :=
  (chainOutputOrder orients (orients.length - 1)).map fun e =>
    ({ occ := orients.length - 1, edge := e } : ChainEdge)

def chainOutputKey (orients : List TauOrient) (states : List TauState) : List LColor :=
  (chainOuterOutputEdges orients).map (chainEdgeColor states)

def chainComponentAvoidsOutputs
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  !component.any fun e => (chainOuterOutputEdges orients).contains e

def chainComponentAvoidsFullInterface
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  chainComponentAvoidsInputs orients component &&
    chainComponentAvoidsOutputs orients component

def chainSpecifiedKempeStepAvoidsFullInterface
    (orients : List TauOrient) (s t : List TauState) (move : ChainMove) : Bool :=
  let component := chainComponent orients s move.a move.c move.seed
  !component.isEmpty &&
    chainComponentAvoidsFullInterface orients component &&
      chainAgreesWithSwitch orients s t component move.a move.c

def chainSingleKempeStepAvoidsFullInterface
    (orients : List TauOrient) (s t : List TauState) : Bool :=
  colorPairs.any fun pair =>
    let a := pair.1
    let c := pair.2
    (chainEdges orients).any fun seed =>
      let component := chainComponent orients s a c seed
      !component.isEmpty &&
        chainComponentAvoidsFullInterface orients component &&
          chainAgreesWithSwitch orients s t component a c

def chainFullInterfaceClosureStep
    (orients : List TauOrient) (fiber seen : List (List TauState)) :
    List (List TauState) :=
  fiber.foldl
    (fun acc candidate =>
      if acc.any fun current =>
          chainSingleKempeStepAvoidsFullInterface orients current candidate then
        addIfFresh acc candidate
      else
        acc)
    seen

def closeChainFullInterfaceFiber
    (orients : List TauOrient) (fiber : List (List TauState)) :
    Nat → List (List TauState) → List (List TauState)
  | 0, seen => seen
  | n + 1, seen =>
      let seen' := chainFullInterfaceClosureStep orients fiber seen
      if seen'.length == seen.length then seen'
      else closeChainFullInterfaceFiber orients fiber n seen'

def chainFullInterfaceFiberConnected
    (orients : List TauOrient) (fiber : List (List TauState)) : Bool :=
  match fiber with
  | [] => true
  | root :: _ =>
      let closure := closeChainFullInterfaceFiber orients fiber fiber.length [root]
      fiber.all fun state => closure.contains state

def twoSidedStubAvoidanceCounterexampleKey : List LColor :=
  chainInputKey twoLayerEscapeOuterWord twoLayerEscapeCollarSource

def twoSidedStubAvoidanceOutputKeySource : List LColor :=
  chainOutputKey twoLayerEscapeOuterWord twoLayerEscapeCollarSource

def twoSidedStubAvoidanceOutputKeyTarget : List LColor :=
  chainOutputKey twoLayerEscapeOuterWord twoLayerEscapeCollarTarget

theorem twoSidedStubAvoidance_counterexampleWord_mem_length2 :
    twoLayerEscapeOuterWord ∈ tauOrientWords2 := by
  decide

theorem twoSidedStubAvoidance_counterexampleKey_mem :
    twoSidedStubAvoidanceCounterexampleKey ∈ colorAssignments4 := by
  decide

theorem twoSidedStubAvoidance_source_target_same_input_key :
    chainInputKey twoLayerEscapeOuterWord twoLayerEscapeCollarSource =
      chainInputKey twoLayerEscapeOuterWord twoLayerEscapeCollarTarget := by
  decide

theorem twoSidedStubAvoidance_source_target_connected_by_input_avoiding_step :
    chainSpecifiedKempeStep twoLayerEscapeOuterWord
      twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
      twoLayerEscapeMove = true :=
  twoLayerEscape_certifiedCollarStep

theorem twoSidedStubAvoidance_witness_component_touches_output :
    chainComponentAvoidsOutputs twoLayerEscapeOuterWord
      twoLayerEscapeCollarComponent = false := by
  decide

theorem twoSidedStubAvoidance_witness_not_full_interface_step :
    chainSpecifiedKempeStepAvoidsFullInterface twoLayerEscapeOuterWord
      twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
      twoLayerEscapeMove = false := by
  decide

theorem twoSidedStubAvoidance_output_keys_differ :
    twoSidedStubAvoidanceOutputKeySource ≠
      twoSidedStubAvoidanceOutputKeyTarget := by
  decide

/--
The tested two-sided repair target for the length-2 open tau/mirror class:
each fixed first-input fiber would be connected by switches whose components
avoid both the first input stubs and the last output stubs.
-/
def section92Step4TwoSidedAvoidanceLength2Target : Prop :=
  ∀ orients, orients ∈ tauOrientWords2 →
    ∀ key, key ∈ colorAssignments4 →
      chainFullInterfaceFiberConnected orients
        (chainFiberFrom orients (allChainStates orients) key) = true

/--
The finite counterexample class for the attempted two-sided strengthening:
there is a length-2 per-input pair connected by an ordinary input-avoiding
certificate, but the certificate touches the output side and is therefore not
a full-interface-avoiding certificate.  The archived lab verdict records the
whole tested fiber as disconnected under the full-interface relation.
-/
def Section92Step4TwoSidedAvoidanceCounterexampleClass : Prop :=
  twoLayerEscapeOuterWord ∈ tauOrientWords2 ∧
  twoSidedStubAvoidanceCounterexampleKey ∈ colorAssignments4 ∧
  chainInputKey twoLayerEscapeOuterWord twoLayerEscapeCollarSource =
    chainInputKey twoLayerEscapeOuterWord twoLayerEscapeCollarTarget ∧
  chainSpecifiedKempeStep twoLayerEscapeOuterWord
    twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
    twoLayerEscapeMove = true ∧
  chainComponentAvoidsOutputs twoLayerEscapeOuterWord
    twoLayerEscapeCollarComponent = false ∧
  chainSpecifiedKempeStepAvoidsFullInterface twoLayerEscapeOuterWord
    twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
    twoLayerEscapeMove = false ∧
  twoSidedStubAvoidanceOutputKeySource ≠
    twoSidedStubAvoidanceOutputKeyTarget

theorem section92Step4TwoSidedAvoidanceCounterexampleClass :
    Section92Step4TwoSidedAvoidanceCounterexampleClass := by
  exact
    ⟨twoSidedStubAvoidance_counterexampleWord_mem_length2,
      twoSidedStubAvoidance_counterexampleKey_mem,
      twoSidedStubAvoidance_source_target_same_input_key,
      twoSidedStubAvoidance_source_target_connected_by_input_avoiding_step,
      twoSidedStubAvoidance_witness_component_touches_output,
      twoSidedStubAvoidance_witness_not_full_interface_step,
      twoSidedStubAvoidance_output_keys_differ⟩

end GoertzelLemma818TwoSidedAvoidance

end Mettapedia.GraphTheory.FourColor
