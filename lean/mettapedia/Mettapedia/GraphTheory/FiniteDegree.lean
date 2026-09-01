import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Finite-degree presentation independence

Mathlib represents local finiteness by a family of `Fintype` instances on
neighbor sets.  The resulting neighbor finset and degree do not depend on
which finite presentation is chosen.  These lemmas make that extensional fact
available when two independently constructed graph packages contribute
definitionally different local-finiteness instances.
-/

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The neighbor finset is independent of the finite presentation of the
neighbor set. -/
theorem neighborFinset_instance_independent (vertex : V)
    (first second : Fintype (G.neighborSet vertex)) :
    @neighborFinset V G vertex first =
      @neighborFinset V G vertex second := by
  ext neighbor
  simp

/-- Graph degree is independent of the finite presentation of the neighbor
set. -/
theorem degree_instance_independent (vertex : V)
    (first second : Fintype (G.neighborSet vertex)) :
    @degree V G vertex first = @degree V G vertex second :=
  congrArg Finset.card
    (neighborFinset_instance_independent vertex first second)

/-- Regularity is independent of the chosen family of finite neighbor-set
presentations. -/
theorem isRegularOfDegree_instance_independent (degreeValue : Nat)
    (first second : LocallyFinite G)
    (hregular : @IsRegularOfDegree V G first degreeValue) :
    @IsRegularOfDegree V G second degreeValue := by
  intro vertex
  exact (degree_instance_independent vertex (first vertex) (second vertex)).symm.trans
    (hregular vertex)

end SimpleGraph
