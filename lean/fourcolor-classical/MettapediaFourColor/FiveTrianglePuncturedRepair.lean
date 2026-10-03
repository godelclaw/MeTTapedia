import MettapediaFourColor.FiveTriangleKempeTrap
import Mettapedia.GraphTheory.FourColor.OrderedFanKempe
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Repair after exposing the actual fan exterior

Remove the old interior before recolouring. The retained ten vertices induce
an ordered fan, so the uniform fan theorem connects every exterior colouring
to the shared source/target witness. Both original interiors can then be
reconstructed with exactly the same retained colours.

Keeping the old interior throughout would forbid this repair, as proved by
the preceding palette invariant. The distinction is between histories on the
whole source and histories on its actual punctured exterior. No claim about
arbitrary exteriors or geometric coverage is made here.
-/

namespace FourColor.FiveTrianglePuncturedRepair

open Color FiveTriangleCollapseObstruction
open Mettapedia.GraphTheory.FourColor
open KempeChainCertificate

abbrev exterior := OrderedFanKempe.graph 9

/-- The smaller graph is the exact induced graph on the retained source
vertices. No edge between retained vertices has been discarded. -/
theorem exterior_exact : Function.Injective (FiveTriangleKempeTrap.ports false) ∧
    ∀ i j : Fin 10, exterior.Adj i j ↔
      FiveTriangleKempeTrap.graph.Adj
        (FiveTriangleKempeTrap.ports false i) (FiveTriangleKempeTrap.ports false j) := by
  decide +kernel

def restrictSource (C : FiveTriangleKempeTrap.graph.Coloring Color) : exterior.Coloring Color :=
  .mk (fun i => C (FiveTriangleKempeTrap.ports false i))
    (fun h => C.valid ((exterior_exact.2 _ _).mp h))

def terminal : exterior.Coloring Color := restrictSource FiveTriangleKempeTrap.goodColouring

def target : FiveTriangleJointChoice.targetGraph.Coloring Color :=
  .mk FiveTriangleKempeTrap.goodTarget (fun h => FiveTriangleKempeTrap.good_proper.2.1 _ _ h)

/-- Every initial exterior state reaches the same jointly compatible
terminal witness. The old interior need not remain colourable en route. -/
theorem every_exterior_reconstructs (C : exterior.Coloring Color) :
    Nonempty (History C terminal) ∧
      (∀ i, terminal i = FiveTriangleKempeTrap.goodColouring
        (FiveTriangleKempeTrap.ports false i)) ∧
      (∀ i : Fin 10, terminal i = target (i.castAdd 7)) := by
  exact ⟨OrderedFanKempe.history C terminal, fun _ => rfl,
    FiveTriangleKempeTrap.good_proper.2.2⟩

/-- This repair applies in particular to the state whose entire-source
Kempe orbit was proved trapped. -/
theorem trapped_exterior_repairs :
    Nonempty (History (restrictSource FiveTriangleKempeTrap.base) terminal) :=
  (every_exterior_reconstructs _).1

/-- No history retaining the complete old source can have this boundary
endpoint. Repair genuinely needs the punctured graph. -/
theorem no_whole_source_lift :
    ¬ ∃ C : FiveTriangleKempeTrap.graph.Coloring Color,
      Nonempty (History FiveTriangleKempeTrap.base C) ∧
        ∀ i, C (FiveTriangleKempeTrap.ports false i) = terminal i := by
  rintro ⟨C, ⟨p⟩, agree⟩
  apply FiveTriangleKempeTrap.no_history_repairs p
  refine ⟨false, .mk FiveTriangleKempeTrap.goodTarget
    (fun {u v} h => FiveTriangleKempeTrap.good_proper.2.1 u v (Or.inl h)), ?_⟩
  intro i
  exact (agree i).trans ((every_exterior_reconstructs terminal).2.2 i)

/-- All vertices of the retained fan are counted; the omitted patch has
eight vertices, including the bypassed boundary vertex. -/
theorem strict_vertex_count : Fintype.card (Fin 10) < Fintype.card (Fin 18) := by decide

/-- The small obstruction does not satisfy even the minimum-degree-five
consequence used in stronger minimal-counterexample settings. -/
theorem omitted_vertex_degree : FiveTriangleKempeTrap.graph.degree 6 = 3 := by decide +kernel

theorem not_minimum_degree_five :
    ¬ ∀ v, 5 ≤ FiveTriangleKempeTrap.graph.degree v := by
  intro h
  have := h 6
  rw [omitted_vertex_degree] at this
  omega

end FourColor.FiveTrianglePuncturedRepair
