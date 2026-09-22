import Mettapedia.GraphTheory.FourColor.SphericalOrderedMeshReduction

/-!
# What the raw width supply actually supplies

`RawBranchDecompositionSupply w` says every graph-backed vertex-minimal Tait
counterexample admits a rooted branch decomposition of width at most `w`.  Read
as an interface statement, that is the promise the compositional route needs: a
decomposition whose every cut has a small complete ambient middle set, so that
a finite profile machine can run along it.

It is not what the available instantiation delivers.  Every middle set is a set
of ambient vertices, so `WidthAtMost w` is automatic once `w` is a bound on the
vertex count -- that is `widthAtMost_of_card_le`, and it is the final step of
the proved conventional half `rawDecompositionOfNoOrderedInjectiveMesh`, whose
width parameter is literally the mesh-free *vertex* bound.

This file states that scope exactly.  `rawBranchDecompositionSupply_of_vertexBound`
shows the supply follows from a vertex bound and nothing else, so at such a `w`
it carries no interface information: the decomposition it produces may have
every middle set equal to the whole vertex set.  `widthAtMost_card` records the
degenerate case directly.

Consequence for the route, stated plainly and not proved here: the profile
fold, the interface state and the pumping argument all consume a bound on the
middle sets that is independent of the vertex count.  A supply whose width is
the vertex bound does not feed them.  Nothing in this file refutes the
exclusion statement itself, which remains a genuine and open proposition about
a fixed mesh; what it locates is that the chain from that statement to a
*bounded interface* is missing, not merely unproved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RawWidthSupplyScope

open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphTaitBridge
open SphericalMeshFreeRawDecomposition
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- Every rooted decomposition has width at most the vertex count: a middle set
is a set of vertices.  The width parameter only says something about interfaces
below this value. -/
theorem widthAtMost_card (d : RootedBranchDecomposition (G := G)) :
    d.WidthAtMost (Fintype.card V) :=
  widthAtMost_of_card_le d _ le_rfl

end

/-- **The supply is a vertex bound.**  If every graph-backed vertex-minimal
Tait counterexample has at most `w` vertices, then the raw width supply at `w`
holds -- with no geometric input, and with every middle set permitted to be the
entire vertex set.

This is the shape of the only currently proved instantiation, whose `w` is the
mesh-free vertex bound. -/
theorem rawBranchDecompositionSupply_of_vertexBound (w : Nat)
    (hbound : ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj] (data : Data G),
      GraphBackedVertexMinimalTaitCounterexample data → Fintype.card V ≤ w) :
    RawBranchDecompositionSupply.{u} w := by
  intro V _ _ G _ data minimal
  classical
  letI : G.LocallyFinite := fun _ => Subtype.fintype _
  have hthree : 3 ≤ Fintype.card G.edgeSet := by
    let v := data.toRotationSystem.vertOf data.toRotationSystem.outer
    have hc := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data minimal.spherical.cubic v
    exact hc ▸ Finset.card_le_univ (incidentEdgeFinset G v)
  obtain ⟨d⟩ := exists_rooted_decomposition hthree
  exact ⟨d, widthAtMost_of_card_le d _ (hbound data minimal)⟩

end GoertzelV24RawWidthSupplyScope

end Mettapedia.GraphTheory.FourColor
