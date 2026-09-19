import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalReductiveAssembly

/-!
# The finite base only ever meets maps the width supply delivers

The checked headline consumed `TaitBaseVerifiedAt (rawVertexBound k w)`: every
graph-backed bridgeless spherical cubic map below a tower-height vertex bound
is Tait colourable.  That premise carries no width hypothesis, so discharging
it means colouring maps of arbitrarily large interface width — up to roughly
the square root of the bound.  The route's own instrument is an interface
closure at width `w`, whose domain is maps of bounded width.  As stated, the
base obligation therefore asked for strictly more than the route can supply,
and strictly more than the headline uses.

At the point of use the minimal counterexample already carries the supply's
rooted connected decomposition.  Handing that decomposition to the base costs
nothing and restricts the obligation to exactly the maps the interface closure
can see.  The resulting premise has all the hypotheses of the old one and one
more, so it is weaker; the old headline is recovered as a corollary.

At a genuinely small fixed `w` this restriction can exclude maps.  It does
not currently give a small-width advantage at the load-bearing use site: the
available mesh-free suppliers set `w` to a vertex-count bound and obtain a
decomposition from the trivial inequality
`middleSet.card ≤ Fintype.card V ≤ w`.  The restriction still excludes some
other maps below `rawVertexBound k w`; it is not logically vacuous.  But the
direct mesh-free assembly already asks for colourability only through that
smaller vertex-count bound.  A useful fixed-width interface audit needs an
independently small width supplier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DecomposableFiniteBase

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24SphericalMinimalCounterexampleSelection
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u v

/-- The finite-base obligation restricted to the class the width supply
actually delivers: bounded vertex count **and** a rooted connected branch
decomposition of the fixed interface bounds.  Every hypothesis of the
unrestricted premise is retained, so this is the weaker obligation. -/
def TaitBaseVerifiedOnDecomposable (k w : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    BridgelessSphericalCubicMapData rotation.toRotationSystem →
    Fintype.card V ≤ rawVertexBound k w →
    RootedConnectedBranchDecomposition (G := G) k w →
    RotationSystemTaitColorable rotation.toRotationSystem

/-- The restricted obligation is weaker: it is the unrestricted one with an
extra hypothesis. -/
theorem taitBaseVerifiedOnDecomposable_of_taitBaseVerifiedAt (k w : Nat)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    TaitBaseVerifiedOnDecomposable.{u} k w :=
  fun rotation mapData hbound _ => base rotation mapData hbound

/-- The headline never needed colourability of high-width maps.  The supply's
own decomposition is available at the point where the base is applied. -/
theorem noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_decomposableBase
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedOnDecomposable.{u} k w) :
    NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro V _ _ G _ rotation minimal
  have hdecomposition := supply rotation minimal
  have hbound : Fintype.card V ≤ rawVertexBound k w := by
    simpa [rawVertexBound] using
      vertexCount_le_of_rootedConnectedBranchDecomposition
        rotation minimal k w hdecomposition
  exact minimal.notColorable
    (base rotation minimal.toBridgelessSphericalCubicMapData hbound
      hdecomposition)

/-- Connected spherical headline from the restricted base. -/
theorem connectedSphericalFourColorStatement_of_supply_and_decomposableBase
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedOnDecomposable.{u} k w) :
    GoertzelV24SphericalGraphPresentation.ConnectedSphericalFourColorStatement.{u} :=
  connectedSphericalFourColorStatement_of_no_minimal
    (noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_decomposableBase
      k w supply base)

/-- Componentwise spherical headline from the restricted base. -/
theorem sphericalFourColorStatement_of_supply_and_decomposableBase
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedOnDecomposable.{u} k w) :
    GoertzelV24SphericalGraphPresentation.SphericalFourColorStatement.{u} :=
  sphericalFourColorStatement_of_no_minimal
    (noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_decomposableBase
      k w supply base)

/-- **Combinatorial Four-Colour headline from the restricted base.** -/
theorem combinatorialFourColorStatement_of_supply_and_decomposableBase
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedOnDecomposable.{u} k w) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  (GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.{u}).2
    (sphericalFourColorStatement_of_supply_and_decomposableBase k w supply base)

/-- **Combinatorial headline from the raw width bound and the restricted
base.**  This is the consumer-facing form: the open inputs are the raw
bounded-width decomposition and a finite base that is only ever asked about
maps of interface width at most `w`. -/
theorem combinatorialFourColorStatement_of_raw_and_decomposableBase
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (base : TaitBaseVerifiedOnDecomposable.{u} w w) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_supply_and_decomposableBase w w
    (connectedDecompositionSupply_of_raw w raw) base

/-! ## The reflection joint, with the decomposition in scope

The earlier route-native reflection extracted its finite state from the bare
map.  Nothing in that signature carried a width bound, so an instantiation had
to manufacture an interface from an arbitrary map below the vertex bound —
precisely the step a fixed-width interface machine cannot take.

Here the decomposition is an input to `trace`.  A width-`w` sweep along the
supplied decomposition is then a legal way to produce the state, which is what
makes the finite closure the intended instrument rather than an enumeration. -/

structure DecomposableBaseReflection
    (k w : Nat) (State : Type v) [DecidableEq State] where
  /-- The state-level condition forced by a noncolourable decomposable map. -/
  Necessary : State → Prop
  /-- The explicitly computed finite reachable closure. -/
  reachable : Finset State
  /-- Extract a finite state, **using the supplied decomposition**. -/
  trace :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G),
      BridgelessSphericalCubicMapData rotation.toRotationSystem →
      Fintype.card V ≤ rawVertexBound k w →
      RootedConnectedBranchDecomposition (G := G) k w →
      State
  trace_mem_reachable :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G)
      (mapData : BridgelessSphericalCubicMapData rotation.toRotationSystem)
      (hbound : Fintype.card V ≤ rawVertexBound k w)
      (decomposition : RootedConnectedBranchDecomposition (G := G) k w),
      trace rotation mapData hbound decomposition ∈ reachable
  necessary_of_not_colorable :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G)
      (mapData : BridgelessSphericalCubicMapData rotation.toRotationSystem)
      (hbound : Fintype.card V ≤ rawVertexBound k w)
      (decomposition : RootedConnectedBranchDecomposition (G := G) k w),
      ¬ RotationSystemTaitColorable rotation.toRotationSystem →
      Necessary (trace rotation mapData hbound decomposition)

namespace DecomposableBaseReflection

variable {k w : Nat} {State : Type v} [DecidableEq State]

/-- An empty filtered closure discharges the restricted base obligation. -/
theorem taitBaseVerifiedOnDecomposable_of_filter_eq_empty
    (reflection : DecomposableBaseReflection.{u, v} k w State)
    [DecidablePred reflection.Necessary]
    (haudit : reflection.reachable.filter reflection.Necessary = ∅) :
    TaitBaseVerifiedOnDecomposable.{u} k w := by
  intro V _ _ G _ rotation mapData hbound decomposition
  by_contra hnot
  have hmem :
      reflection.trace rotation mapData hbound decomposition ∈
        reflection.reachable.filter reflection.Necessary :=
    Finset.mem_filter.mpr
      ⟨reflection.trace_mem_reachable rotation mapData hbound decomposition,
        reflection.necessary_of_not_colorable rotation mapData hbound
          decomposition hnot⟩
  rw [haudit] at hmem
  simp at hmem

/-- Consumer-facing assembly: a raw width bound plus an audited finite closure
whose trace sees the decomposition imply the combinatorial Four-Colour
statement. -/
theorem combinatorialFourColorStatement_of_raw_and_filter_audit
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (reflection : DecomposableBaseReflection.{u, v} w w State)
    [DecidablePred reflection.Necessary]
    (haudit : reflection.reachable.filter reflection.Necessary = ∅) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_decomposableBase w raw
    (reflection.taitBaseVerifiedOnDecomposable_of_filter_eq_empty haudit)

end DecomposableBaseReflection

/-! ## Nothing is lost

The previously checked headlines are corollaries: the unrestricted base
implies the restricted one, so every earlier consumer still applies. -/

theorem noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_base'
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    NoGraphBackedVertexMinimalTaitCounterexample.{u} :=
  noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_decomposableBase
    k w supply (taitBaseVerifiedOnDecomposable_of_taitBaseVerifiedAt k w base)

theorem combinatorialFourColorStatement_of_supply_and_base'
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_supply_and_decomposableBase k w supply
    (taitBaseVerifiedOnDecomposable_of_taitBaseVerifiedAt k w base)

theorem combinatorialFourColorStatement_of_raw_and_base'
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound w w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_decomposableBase w raw
    (taitBaseVerifiedOnDecomposable_of_taitBaseVerifiedAt w w base)

end

end GoertzelV24DecomposableFiniteBase

end Mettapedia.GraphTheory.FourColor
