import Mettapedia.Algorithms.Compression.StrictProgramComposition

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.StrictProgramCompositionControls

open Mettapedia.Algorithms.Compression
open StrictProgramComposition

private def read (bytes : KolmogorovComplexity.BinString) : Leaf Nat String :=
  if bytes = [] then .input else .constant 1

private def apply (tag : KolmogorovComplexity.BinString) (values : List Nat) : Except String Nat :=
  if tag = [] then .error "operation" else .ok values.sum

private def shifted : FramedTree.Tree := .node [true] [.leaf [true], .leaf []]
private def doubled : FramedTree.Tree := .node [true] [.leaf [], .leaf []]
private def ignored : FramedTree.Tree := .leaf [true]
private def competing : FramedTree.Tree := .node [true] [.node [] [.leaf [true]], .leaf []]

theorem preceding_constant_does_not_hide_input_failure :
    demand read shifted = .inputDominant ∧ run read apply (.error "earlier") shifted = .error "earlier" := by
  simp [demand, run, shifted, CompactDag.fold, leafDemand, leafValue, dominance, nodeValue, collect, read,
    Except.map, Except.bind]

theorem competing_failure_is_not_certified_strict :
    demand read competing = .other ∧ run read apply (.error "earlier") competing = .error "operation" := by
  simp [demand, run, competing, CompactDag.fold, leafDemand, leafValue, dominance, nodeValue, collect, read, apply,
    Except.map, Except.bind]

theorem input_ignoring_term_needs_a_sequencing_guard :
    demand read ignored = .total ∧
      run read apply (.error "earlier") (substitute read (.leaf []) ignored) = .ok 1 ∧
      ((run read apply (.error "earlier") (.leaf [])).bind
        (fun middle => run read apply (.ok middle) ignored)) = .error "earlier" := by
  simp [demand, run, substitute, ignored, CompactDag.fold, leafDemand, leafValue, read, Except.bind]

theorem admitted_composition_computes_the_new_program :
    run read apply (.ok 3) (substitute read shifted doubled) = .ok 8 := by
  simp [run, substitute, shifted, doubled, CompactDag.fold, leafValue, nodeValue, collect, read, apply,
    Except.map, Except.bind]

theorem admitted_composition_retains_earlier_failure :
    run read apply (.error "earlier") (substitute read shifted doubled) = .error "earlier" := by
  simp [run, substitute, shifted, doubled, CompactDag.fold, leafValue, nodeValue, collect, read,
    Except.map, Except.bind]

theorem constant_only_operation_is_not_assumed_total :
    demand read (.node [true] [.leaf [true]]) = .other := by
  simp [demand, CompactDag.fold, leafDemand, dominance, read]

#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.run_node
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.dominance_ne_total
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.collect_dominant
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.demand_sound
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.substitute_node
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.run_substitute
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.strict_composition
#print axioms Mettapedia.Algorithms.Compression.StrictProgramComposition.compact_execution_agrees
#print axioms preceding_constant_does_not_hide_input_failure
#print axioms competing_failure_is_not_certified_strict
#print axioms input_ignoring_term_needs_a_sequencing_guard
#print axioms admitted_composition_computes_the_new_program
#print axioms admitted_composition_retains_earlier_failure
#print axioms constant_only_operation_is_not_assumed_total

end Mettapedia.Examples.Compression.StrictProgramCompositionControls
