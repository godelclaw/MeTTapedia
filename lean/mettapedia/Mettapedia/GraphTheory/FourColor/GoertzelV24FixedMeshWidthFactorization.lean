import Mettapedia.GraphTheory.FourColor.GoertzelV24InjectiveMeshWidthExclusion

/-!
# Exact fixed-mesh boundary of the compositional width input

The route-specific high-width obligation and the conventional planar
wall-to-width theorem are different mathematical inputs.  This file keeps
them different:

* `FixedInjectiveMeshExclusion a b` says that one fixed injective mesh is
  absent from every graph-backed vertex-minimal Tait counterexample;
* `RawDecompositionOfNoInjectiveMesh a b w` says that absence of that mesh
  supplies a raw branch decomposition of width at most `w`.

Their composition is exactly `RawBranchDecompositionSupply w`, the remaining
M1 premise consumed by the checked reductive assembly.  Conversely, the
checked raw width bound excludes every injective mesh with more branch
positions than the resulting vertex threshold.

No wall theorem, colouring theorem, reducibility certificate, or finite base
is hidden in either definition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FixedMeshWidthFactorization

open GoertzelV24InjectiveMeshWidthExclusion
open GoertzelV24MeshIsoperimetry
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-- The route-specific D1 statement on an exact finite carrier: one fixed
injective `a`-by-`b` mesh is absent from every graph-backed vertex-minimal
Tait counterexample.  A genuine subdivided wall supplies such a mesh, but
that geometric conversion is intentionally not part of this definition. -/
def FixedInjectiveMeshExclusion (a b : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      ¬ ∃ mesh : Mesh (toMultigraph rotation.toRotationSystem) a b,
        IsVertexInjective mesh

/-- The conventional wall/grid side of M1 in the exact form needed here:
for a graph-backed vertex-minimal counterexample, absence of the fixed
injective mesh supplies a raw rooted branch decomposition of width at most
`w`.  This implication is kept separate from fixed-mesh exclusion. -/
def RawDecompositionOfNoInjectiveMesh (a b w : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      (¬ ∃ mesh : Mesh (toMultigraph rotation.toRotationSystem) a b,
          IsVertexInjective mesh) →
        ∃ decomposition : RootedBranchDecomposition (G := G),
          decomposition.WidthAtMost w

/-- Fixed-mesh exclusion and the wall-free decomposition theorem compose to
the exact raw-width premise consumed by the reductive assembly. -/
theorem rawBranchDecompositionSupply_of_fixedInjectiveMeshExclusion
    (a b w : Nat)
    (exclude : FixedInjectiveMeshExclusion.{u} a b)
    (decompose : RawDecompositionOfNoInjectiveMesh.{u} a b w) :
    RawBranchDecompositionSupply.{u} w := by
  intro V _ _ G _ rotation minimal
  exact decompose rotation minimal (exclude rotation minimal)

/-- The converse quantitative check: a supplied raw width bound excludes
every fixed injective mesh whose number of branch positions exceeds the
checked vertex threshold. -/
theorem fixedInjectiveMeshExclusion_of_rawBranchDecompositionSupply
    (a b w : Nat)
    (hlarge : rawVertexBound w w < a * b)
    (raw : RawBranchDecompositionSupply.{u} w) :
    FixedInjectiveMeshExclusion.{u} a b := by
  intro V _ _ G _ rotation minimal
  rintro ⟨mesh, hinjective⟩
  exact
    (not_isVertexInjective_of_rawBranchDecompositionSupply
      w raw rotation minimal
      (toMultigraph rotation.toRotationSystem) mesh hlarge) hinjective

/-- Consumer-facing conditional headline with the high-width receipt split
at its honest boundary: route-specific fixed-mesh exclusion, conventional
wall-free bounded width, and the route-native finite base. -/
theorem combinatorialFourColorStatement_of_fixedMeshExclusion_and_base
    (a b w : Nat)
    (exclude : FixedInjectiveMeshExclusion.{u} a b)
    (decompose : RawDecompositionOfNoInjectiveMesh.{u} a b w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound w w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_base w
    (rawBranchDecompositionSupply_of_fixedInjectiveMeshExclusion
      a b w exclude decompose)
    base

end

end GoertzelV24FixedMeshWidthFactorization

end Mettapedia.GraphTheory.FourColor
