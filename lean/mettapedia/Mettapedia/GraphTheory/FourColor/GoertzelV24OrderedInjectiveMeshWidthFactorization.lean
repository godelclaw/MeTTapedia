import Mettapedia.GraphTheory.FourColor.GoertzelV24FixedMeshWidthFactorization

/-!
# Ordered injective meshes: the wall-like high-width carrier

The `Mesh` used by the isoperimetric argument is deliberately permissive: it
does not require its paths to be simple or its designated row--column branch
vertices to occur in grid order.  Those omissions are harmless for cut
counting, but they are too weak for a two-dimensional transport or holonomy
argument.

An `OrderedInjectiveMesh` retains the same checked `Mesh` while recording the
wall-like geometry needed by such an argument: simple row and column paths,
distinct branch vertices, and strictly ordered branch positions along every
path.  Its projection therefore reuses all existing mesh isoperimetry.

The second half of this file repeats the high-width factorization on this
more faithful carrier.  No wall theorem or colouring claim is hidden in the
definitions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedInjectiveMeshWidthFactorization

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24FixedMeshWidthFactorization
open GoertzelV24InjectiveMeshWidthExclusion
open GoertzelV24MeshIsoperimetry
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u v

variable {Vtx : Type u} {Edg : Type v}

/-- A wall-like mesh whose designated branch positions occur in a coherent
rectangular order.  Intersections between a row and a column away from the
designated branch position are not forbidden: the standard cubic-wall mesh
representation may let the two families share path segments. -/
structure OrderedInjectiveMesh
    [DecidableEq Vtx] [DecidableEq Edg] [Fintype Edg]
    (g : Multigraph Vtx Edg) (a b : Nat) where
  toMesh : Mesh g a b
  rowVertexInjective : ∀ i, Function.Injective (toMesh.row i).vert
  colVertexInjective : ∀ j, Function.Injective (toMesh.col j).vert
  branchInjective : Function.Injective fun position : Fin a × Fin b =>
    toMesh.branch position.1 position.2
  rowBranchPosition : ∀ i j,
    Fin ((toMesh.row i).len + 1)
  colBranchPosition : ∀ i j,
    Fin ((toMesh.col j).len + 1)
  rowBranchPosition_spec : ∀ i j,
    (toMesh.row i).vert (rowBranchPosition i j) = toMesh.branch i j
  colBranchPosition_spec : ∀ i j,
    (toMesh.col j).vert (colBranchPosition i j) = toMesh.branch i j
  rowBranchPosition_strictMono : ∀ i,
    StrictMono fun j => rowBranchPosition i j
  colBranchPosition_strictMono : ∀ j,
    StrictMono fun i => colBranchPosition i j

namespace OrderedInjectiveMesh

variable [DecidableEq Vtx] [DecidableEq Edg] [Fintype Edg]
  {g : Multigraph Vtx Edg} {a b : Nat}

/-- Forgetting the ordering data leaves the vertex-injective mesh consumed by
the existing isoperimetric and size arguments. -/
theorem toMesh_isVertexInjective (ordered : OrderedInjectiveMesh g a b) :
    IsVertexInjective ordered.toMesh :=
  ordered.branchInjective

end OrderedInjectiveMesh

/-- The route-specific high-width statement on the wall-like carrier: one
fixed ordered injective mesh is absent from every graph-backed vertex-minimal
Tait counterexample. -/
def FixedOrderedInjectiveMeshExclusion (a b : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      ¬ Nonempty (OrderedInjectiveMesh
        (toMultigraph rotation.toRotationSystem) a b)

/-- The conventional wall/grid side, now stated on the carrier that actually
records rectangular order. -/
def RawDecompositionOfNoOrderedInjectiveMesh (a b w : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      (¬ Nonempty (OrderedInjectiveMesh
        (toMultigraph rotation.toRotationSystem) a b)) →
        ∃ decomposition : RootedBranchDecomposition (G := G),
          decomposition.WidthAtMost w

/-- The stronger exclusion of every injective permissive mesh implies the
wall-like ordered exclusion. -/
theorem fixedOrderedInjectiveMeshExclusion_of_fixedInjectiveMeshExclusion
    (a b : Nat) (exclude : FixedInjectiveMeshExclusion.{u} a b) :
    FixedOrderedInjectiveMeshExclusion.{u} a b := by
  intro V _ _ G _ rotation minimal
  rintro ⟨ordered⟩
  exact exclude rotation minimal
    ⟨ordered.toMesh, ordered.toMesh_isVertexInjective⟩

/-- Ordered fixed-mesh exclusion and its conventional width theorem compose
to the exact raw-width supplier consumed by the reductive assembly. -/
theorem rawBranchDecompositionSupply_of_fixedOrderedInjectiveMeshExclusion
    (a b w : Nat)
    (exclude : FixedOrderedInjectiveMeshExclusion.{u} a b)
    (decompose : RawDecompositionOfNoOrderedInjectiveMesh.{u} a b w) :
    RawBranchDecompositionSupply.{u} w := by
  intro V _ _ G _ rotation minimal
  exact decompose rotation minimal (exclude rotation minimal)

/-- A supplied raw width bound excludes an ordered injective mesh whenever
its branch-position count exceeds the checked vertex threshold. -/
theorem fixedOrderedInjectiveMeshExclusion_of_rawBranchDecompositionSupply
    (a b w : Nat)
    (hlarge : rawVertexBound w w < a * b)
    (raw : RawBranchDecompositionSupply.{u} w) :
    FixedOrderedInjectiveMeshExclusion.{u} a b := by
  intro V _ _ G _ rotation minimal
  rintro ⟨ordered⟩
  exact
    (not_isVertexInjective_of_rawBranchDecompositionSupply
      w raw rotation minimal
      (toMultigraph rotation.toRotationSystem) ordered.toMesh hlarge)
      ordered.toMesh_isVertexInjective

/-- Consumer-facing conditional headline with the route-specific receipt
stated on a wall-like ordered mesh rather than the permissive cut-counting
carrier. -/
theorem combinatorialFourColorStatement_of_fixedOrderedMeshExclusion_and_base
    (a b w : Nat)
    (exclude : FixedOrderedInjectiveMeshExclusion.{u} a b)
    (decompose : RawDecompositionOfNoOrderedInjectiveMesh.{u} a b w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound w w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_base w
    (rawBranchDecompositionSupply_of_fixedOrderedInjectiveMeshExclusion
      a b w exclude decompose)
    base

end

end GoertzelV24OrderedInjectiveMeshWidthFactorization

/-! Publication-facing aliases. -/

alias GoertzelV24OrderedInjectiveMeshWidthFactorization.toMesh_isVertexInjective :=
  GoertzelV24OrderedInjectiveMeshWidthFactorization.OrderedInjectiveMesh.toMesh_isVertexInjective

end Mettapedia.GraphTheory.FourColor
