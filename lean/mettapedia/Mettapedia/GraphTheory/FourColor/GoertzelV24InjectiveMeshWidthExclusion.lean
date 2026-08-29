import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalReductiveAssembly

/-!
# Bounded width excludes an injective large mesh

`GoertzelV24MeshIsoperimetry.Mesh` deliberately permits two row--column
positions to designate the same ambient vertex.  That generality is harmless
for its cut-isoperimetry theorem, which counts positions.  A subdivided wall,
however, has a distinct branch vertex at every position.  This file records
that extra property explicitly and connects it to the checked bounded-width
descent.

The result is one direction of the wall/width reduction used by the
compositional route.  A raw width bound gives a connected decomposition and
hence a vertex bound; an injective `a`-by-`b` mesh supplies at least `a*b`
vertices.  Therefore a minimal counterexample satisfying the raw width bound
cannot contain a mesh larger than the checked vertex threshold.  No wall
theorem, colouring theorem, or reducibility certificate is used here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InjectiveMeshWidthExclusion

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24MeshIsoperimetry
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u v

variable {Vtx : Type u} {Edg : Type v}

/-- A mesh whose row--column branch positions are represented by distinct
ambient vertices.  This is the additional property supplied by a genuine
subdivided wall and intentionally omitted from the more general
isoperimetric `Mesh` carrier. -/
def IsVertexInjective {g : Multigraph Vtx Edg} {a b : Nat}
    (mesh : Mesh g a b) : Prop :=
  Function.Injective fun position : Fin a × Fin b =>
    mesh.branch position.1 position.2

/-- An injective `a`-by-`b` mesh occupies at least `a*b` ambient vertices. -/
theorem mul_le_card_vertices_of_isVertexInjective
    [Fintype Vtx]
    {g : Multigraph Vtx Edg} {a b : Nat} (mesh : Mesh g a b)
    (hinjective : IsVertexInjective mesh) :
    a * b ≤ Fintype.card Vtx := by
  have hcard := Fintype.card_le_of_injective
    (fun position : Fin a × Fin b =>
      mesh.branch position.1 position.2) hinjective
  simpa only [Fintype.card_prod, Fintype.card_fin] using hcard

/-- A carrier smaller than `a*b` admits no injective `a`-by-`b` mesh. -/
theorem not_isVertexInjective_of_card_lt_mul
    [Fintype Vtx]
    {g : Multigraph Vtx Edg} {a b : Nat} (mesh : Mesh g a b)
    (hsmall : Fintype.card Vtx < a * b) :
    ¬ IsVertexInjective mesh := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (mul_le_card_vertices_of_isVertexInjective mesh hinjective)) hsmall

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

/-- The checked connected-decomposition bound excludes every injective mesh
whose number of branch positions exceeds that bound. -/
theorem not_isVertexInjective_of_connectedDecomposition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w : Nat)
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    {Edg : Type v}
    (g : Multigraph V Edg) {a b : Nat} (mesh : Mesh g a b)
    (hlarge : rawVertexBound k w < a * b) :
    ¬ IsVertexInjective mesh := by
  intro hinjective
  have hmesh : a * b ≤ Fintype.card V :=
    mul_le_card_vertices_of_isVertexInjective mesh hinjective
  have hbound : Fintype.card V ≤ rawVertexBound k w := by
    simpa [rawVertexBound] using
      vertexCount_le_of_rootedConnectedBranchDecomposition
        rotation minimal k w decomposition
  omega

/-- **Width-to-wall direction of M1.**  If every least counterexample has a
raw branch decomposition of width at most `w`, then no such counterexample
contains an injective mesh with more branch positions than the checked raw
vertex bound.  Width-preserving connectedization and the literal Count
descent are invoked internally. -/
theorem not_isVertexInjective_of_rawBranchDecompositionSupply
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {Edg : Type v}
    (g : Multigraph V Edg) {a b : Nat} (mesh : Mesh g a b)
    (hlarge : rawVertexBound w w < a * b) :
    ¬ IsVertexInjective mesh := by
  exact not_isVertexInjective_of_connectedDecomposition
    rotation minimal w w
      (connectedDecompositionSupply_of_raw w raw rotation minimal)
    g mesh hlarge

end

end GoertzelV24InjectiveMeshWidthExclusion

end Mettapedia.GraphTheory.FourColor
