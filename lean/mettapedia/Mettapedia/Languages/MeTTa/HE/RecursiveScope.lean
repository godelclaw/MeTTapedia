import Mettapedia.Languages.MeTTa.HE.RecursiveEncoding
import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-!
# Live scope of retained recursive configurations

All atom-bearing fields of every request and continuation contribute to the
live scope. Binding keys and equality endpoints are represented as variable
atoms alongside their stored values. Pending alternatives and already emitted
answers retain both their atoms and bindings. Rule templates in the read-only
space are separate from these live equation instances.

The scoped freshener is executable on represented configurations and realizes
the independent hygiene judgment. This module does not replace the recursive
controller's legacy query policy or identify it with native runtime states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveEncoding LeaTTaBridge
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Eval.Steps

def bindingAtoms (bindings : Bindings) : List Atom :=
  bindings.assignments.flatMap (fun entry => [.var entry.1, entry.2]) ++
    bindings.equalities.flatMap (fun edge => [.var edge.1, .var edge.2])

def resultAtoms (results : ResultSet) : List Atom :=
  results.flatMap fun entry => entry.1 :: bindingAtoms entry.2

/-- Every atom and binding field retained by a request. -/
def taskAtoms : Task → List Atom
  | .atom value expected bindings _
  | .expression value expected bindings _
  | .func value expected bindings _
  | .call value expected bindings _
  | .tupleCalls value expected bindings _ => [value, expected] ++ bindingAtoms bindings
  | .args values types bindings _ => values ++ types ++ bindingAtoms bindings
  | .tuple value bindings _ => value :: bindingAtoms bindings
  | .functions value expected bindings _ types =>
      [value, expected] ++ types ++ bindingAtoms bindings
  | .bindingAlternatives value operatorType resultType _ alternatives =>
      [value, operatorType, resultType] ++ alternatives.flatMap bindingAtoms
  | .heads operatorType arguments _ alternatives =>
      operatorType :: (arguments ++ resultAtoms alternatives)
  | .argumentHeads original remaining types _ alternatives =>
      original :: (remaining ++ types ++ resultAtoms alternatives)
  | .tupleHeads tail _ alternatives => tail :: resultAtoms alternatives
  | .calls expected _ alternatives
  | .atoms expected _ alternatives => expected :: resultAtoms alternatives
  | .equations expected incoming _ alternatives
  | .grounded expected incoming _ alternatives =>
      expected :: (bindingAtoms incoming ++ resultAtoms alternatives)

/-- Every atom and binding field retained by a continuation. -/
def frameAtoms : Frame → List Atom
  | .filter | .tupleSingleton => []
  | .heads operatorType arguments _ => operatorType :: arguments
  | .argumentHeads original remaining types _ => original :: (remaining ++ types)
  | .tupleHeads tail _ => [tail]
  | .calls expected _ => [expected]
  | .functionTail head
  | .argumentTail head
  | .tupleTail head => [head]
  | .append remaining => taskAtoms remaining
  | .prepend selected => resultAtoms selected
  | .fallback value expected bindings _ types =>
      [value, expected] ++ types ++ bindingAtoms bindings

def controlAtoms : Control → List Atom
  | .work task => taskAtoms task
  | .returning results => resultAtoms results

/-- The current control, entire continuation stack, and ordered answer prefix. -/
def liveAtoms (configuration : Configuration) : List Atom :=
  controlAtoms configuration.control ++
    configuration.stack.flatMap frameAtoms ++ resultAtoms configuration.emitted

def configurationNames (configuration : Configuration) : List String :=
  (liveAtoms configuration).flatMap fun atom => (toLeaTTaAtom atom).vars

theorem bindingAtoms_names (bindings : Bindings) :
    (bindingAtoms bindings).flatMap (fun atom => (toLeaTTaAtom atom).vars) =
      EquationScope.bindingNames bindings := by
  simp [bindingAtoms, EquationScope.bindingNames, List.flatMap_append,
    List.flatMap_assoc, toLeaTTaAtom, Metta.Atom.vars]

theorem retained_atom_name_mem {configuration : Configuration} {atom : Atom} {name : String}
    (member : atom ∈ liveAtoms configuration) (occurrence : AtomOccurs atom name) :
    name ∈ configurationNames configuration := by
  exact List.mem_flatMap.mpr ⟨atom, member, atomOccurs_iff_mem_translated_vars.mp occurrence⟩

theorem control_atom_mem {configuration : Configuration} {atom : Atom}
    (member : atom ∈ controlAtoms configuration.control) : atom ∈ liveAtoms configuration := by
  simp only [liveAtoms, List.mem_append]
  exact Or.inl (Or.inl member)

theorem continuation_atom_mem {configuration : Configuration} {frame : Frame} {atom : Atom}
    (frameMember : frame ∈ configuration.stack) (atomMember : atom ∈ frameAtoms frame) :
    atom ∈ liveAtoms configuration := by
  simp only [liveAtoms, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨frame, frameMember, atomMember⟩))

theorem emitted_atom_mem {configuration : Configuration} {atom : Atom}
    (member : atom ∈ resultAtoms configuration.emitted) : atom ∈ liveAtoms configuration := by
  simp only [liveAtoms, List.mem_append]
  exact Or.inr member

theorem continuation_name_mem {configuration : Configuration} {frame : Frame}
    {atom : Atom} {name : String} (frameMember : frame ∈ configuration.stack)
    (atomMember : atom ∈ frameAtoms frame) (occurrence : AtomOccurs atom name) :
    name ∈ configurationNames configuration :=
  retained_atom_name_mem (continuation_atom_mem frameMember atomMember) occurrence

/-- Freshen an equation against the entire retained state and current query. -/
def freshRule (configuration : Configuration) (query : Atom) (incoming : Bindings)
    (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  EquationFreshening.freshRule
    (EquationScope.visibleNames (liveAtoms configuration) query incoming) counter lhs rhs

theorem freshRule_alphaVariant (configuration : Configuration) (query : Atom)
    (incoming : Bindings) (counter : Nat) (lhs rhs : Atom) :
    AlphaVariantRel (liveAtoms configuration) query incoming lhs rhs
      (freshRule configuration query incoming counter lhs rhs).1
      (freshRule configuration query incoming counter lhs rhs).2 :=
  EquationFreshening.freshRule_alphaVariant (liveAtoms configuration) query lhs rhs incoming counter

/-- Decode the complete state before performing scoped equation freshening. -/
def freshRuleData (data query : Atom) (incoming : Bindings) (counter : Nat)
    (lhs rhs : Atom) : Option (Atom × Atom) :=
  (readConfiguration data).map fun configuration => freshRule configuration query incoming counter lhs rhs

theorem freshRuleData_representation (configuration : Configuration) (query : Atom)
    (incoming : Bindings) (counter : Nat) (lhs rhs : Atom) :
    freshRuleData (configurationData configuration) query incoming counter lhs rhs =
      some (freshRule configuration query incoming counter lhs rhs) := by
  simp [freshRuleData, readConfiguration_configurationData]

end Mettapedia.Languages.MeTTa.HE.RecursiveScope
