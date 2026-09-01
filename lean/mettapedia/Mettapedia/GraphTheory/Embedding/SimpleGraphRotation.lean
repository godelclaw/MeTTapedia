import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Cyclic vertex rotations for graph-backed rotation systems

The graph-backed presentation says that the stored permutation is a cycle on
each outgoing-dart fiber.  The abstract rotation-system presentation says
that any two darts at one vertex lie in the same cycle of `rho`.  This file
identifies the two formulations.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph-backed and abstract formulations of a cyclic vertex rotation
are equivalent. -/
theorem vertexRotationCyclic_iff_isVertexwiseCyclic (data : Data G) :
    VertexRotationCyclic data.toRotationSystem ↔ data.IsVertexwiseCyclic := by
  constructor
  · intro hcyclic vertex
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro dart hdart
        change (data.vertexRotation dart).fst = vertex
        rw [data.vertexRotation_fst]
        exact hdart
      · intro first _ second _ heq
        exact data.vertexRotation.injective heq
      · intro dart hdart
        refine ⟨data.vertexRotation.symm dart, ?_, ?_⟩
        · change (data.vertexRotation.symm dart).fst = vertex
          have hfst := data.vertexRotation_fst (data.vertexRotation.symm dart)
          rw [data.vertexRotation.apply_symm_apply] at hfst
          exact hfst.symm.trans hdart
        · exact data.vertexRotation.apply_symm_apply dart
    · intro first hfirst second hsecond
      apply hcyclic first second
      exact hfirst.trans hsecond.symm
  · intro hcyclic first second hbase
    have hsame := (hcyclic (data.toRotationSystem.vertOf first)).2
      (x := first) (y := second) (by rfl) (by exact hbase.symm)
    change Equiv.Perm.SameCycle data.vertexRotation first second
    exact hsame

end Mettapedia.GraphTheory.Embedding
