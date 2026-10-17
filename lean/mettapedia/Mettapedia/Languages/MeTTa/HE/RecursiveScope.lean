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
the independent hygiene judgment. The recursive controller itself renames each
equation apart from a narrower scope: the call, its type, its bindings and the
atoms its continuation still holds (`equationScope`). This module does not
identify either scope with native runtime states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveEncoding LeaTTaBridge
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Eval.Steps

open private atomVariables_eq_typeVars
  from Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-- The low structural inventory agrees with the existing translated reading. -/
theorem configurationNames_translated (configuration : Configuration) :
    configurationNames configuration =
      (liveAtoms configuration).flatMap (fun atom => (toLeaTTaAtom atom).vars) := by
  unfold configurationNames
  rw [atomListVariables_eq_flatMap]
  apply congrArg (fun read => (liveAtoms configuration).flatMap read)
  funext atom
  exact (atomVariables_eq_typeVars atom).trans
    (LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars atom).symm

theorem bindingAtoms_names (bindings : Bindings) :
    (bindingAtoms bindings).flatMap (fun atom => (toLeaTTaAtom atom).vars) =
      EquationScope.bindingNames bindings := by
  simp [bindingAtoms, EquationScope.bindingNames, List.flatMap_append,
    List.flatMap_assoc, toLeaTTaAtom, Metta.Atom.vars]

theorem retained_atom_name_mem {configuration : Configuration} {atom : Atom} {name : String}
    (member : atom ∈ liveAtoms configuration) (occurrence : AtomOccurs atom name) :
    name ∈ configurationNames configuration := by
  rw [configurationNames_translated]
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
