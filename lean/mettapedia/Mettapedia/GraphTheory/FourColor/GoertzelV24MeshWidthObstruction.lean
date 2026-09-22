import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24InjectiveMeshWidthExclusion

/-!
# The mesh is the obstruction to the tool that would exclude it

Every mechanism available for excluding a large ordered mesh from a minimal
counterexample runs a finite profile along a decomposition whose cuts have
*bounded ambient interfaces*: the fold, the phased state, the nested-chain
length bound and the shore-tree vertex bound all take a width parameter and
are useless without a small one.

This file records why that is circular, as a theorem rather than as a remark.
A vertex-injective mesh with more branch positions than the checked bound is
incompatible with a bounded-width connected decomposition of the same graph
-- so in exactly the situation the exclusion is needed, no bounded-width
decomposition exists to run a profile along.

`no_rootedConnectedBranchDecomposition_of_orderedMesh` is the contrapositive
of the existing width-to-wall theorem, stated pointwise on one graph.  It is
not a new mathematical fact; it makes an existing one usable as a statement
about method.

The companion `no_orderedMesh_of_card_lt` marks the opposite, trivial regime:
a mesh injects its branch positions into the vertices, so a mesh larger than
the graph is absent for counting reasons alone.  Any exclusion proved only in
that regime says nothing about the route.

Nothing here refutes `FixedOrderedInjectiveMeshExclusion`, which remains open.
What it locates is that the exclusion cannot be obtained from a bounded-width
profile argument on the same object, because the hypothesis of every such
argument fails exactly when the mesh is present.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MeshWidthObstruction

open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24InjectiveMeshWidthExclusion
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

/-- **A large ordered mesh forbids a bounded-width connected decomposition.**

If the graph carries an ordered injective mesh whose branch positions
outnumber the checked raw vertex bound at `(k, w)`, then it has no rooted
connected branch decomposition at `(k, w)` at all.

Every profile-pumping mechanism in this development consumes such a
decomposition.  So none of them applies to a counterexample containing the
mesh they are meant to exclude. -/
theorem no_rootedConnectedBranchDecomposition_of_orderedMesh
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w : Nat) {a b : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
    (hlarge : rawVertexBound k w < a * b) :
    IsEmpty (RootedConnectedBranchDecomposition (G := G) (k := k) (w := w)) := by
  constructor
  intro decomposition
  exact
    (not_isVertexInjective_of_connectedDecomposition rotation minimal k w
      decomposition (toMultigraph rotation.toRotationSystem) ordered.toMesh hlarge)
      ordered.toMesh_isVertexInjective

/-- The trivial regime.  A mesh injects its branch positions into the vertex
set, so a mesh with more positions than the graph has vertices cannot exist,
for counting reasons and with no route content whatsoever. -/
theorem no_orderedMesh_of_card_lt {Edg : Type v} [DecidableEq Edg] [Fintype Edg]
    {g : Multigraph V Edg} {a b : Nat}
    (hsmall : Fintype.card V < a * b) :
    IsEmpty (OrderedInjectiveMesh g a b) := by
  constructor
  intro ordered
  exact
    (not_isVertexInjective_of_card_lt_mul ordered.toMesh hsmall)
      ordered.toMesh_isVertexInjective

end

end GoertzelV24MeshWidthObstruction

end Mettapedia.GraphTheory.FourColor
