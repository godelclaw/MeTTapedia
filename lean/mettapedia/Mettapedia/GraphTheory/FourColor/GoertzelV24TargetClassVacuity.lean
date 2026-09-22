import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedInterfaceObligation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization

/-!
# Obligations over the target class cannot be refuted by example

Both remaining high-width obligations quantify over graph-backed
vertex-minimal Tait counterexamples: fixed ordered-mesh exclusion, and the
bounded-interface chain supply that replaces it.  A search for a countermodel
to either is not merely unpromising; it is a search for an object whose
existence would refute the theorem the whole route is proving.

This file records that as a theorem rather than as advice.  If every
bridgeless spherical cubic rotation system is Tait colourable -- the statement
the route exists to establish -- then the target class is empty, and every
obligation quantified over it holds vacuously.

Two consequences worth keeping in view.

First, the only admissible outcomes for these obligations are a proof or
honest wreckage.  A colourable graph may refute a *generic geometry lemma*
stated over all maps, and such refutations have been valuable here; but it can
never refute a statement restricted to the target class, and reporting one as
if it did would be a scope error.

Second, vacuity is not a shortcut.  Deriving either obligation this way
assumes the conclusion, so the implications below are of no use inside the
route.  Their only content is about method.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TargetClassVacuity

open GoertzelV24BoundedInterfaceObligation
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-- The statement the route is proving, in the rotation-system form the
target class is stated against. -/
def AllBridgelessSphericalCubicTaitColorable : Prop :=
  ∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E),
    BridgelessSphericalCubicMapData RS → RotationSystemTaitColorable RS

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The target class is empty if the route's conclusion holds.**  A
counterexample carries both its own bridgeless spherical cubic data and the
failure of colourability of that very rotation system. -/
theorem isEmpty_counterexample_of_taitColorable
    (h : AllBridgelessSphericalCubicTaitColorable.{u}) (rotation : Data G) :
    IsEmpty (GraphBackedVertexMinimalTaitCounterexample rotation) := by
  constructor
  intro minimal
  exact minimal.notColorable
    (h rotation.toRotationSystem minimal.toBridgelessSphericalCubicMapData)

/-- Fixed ordered-mesh exclusion is unrefutable: it follows from the
conclusion.  So no countermodel to it exists to be found. -/
theorem fixedOrderedInjectiveMeshExclusion_of_taitColorable
    (h : AllBridgelessSphericalCubicTaitColorable.{u}) (a b : Nat) :
    FixedOrderedInjectiveMeshExclusion.{u} a b := by
  intro V _ _ G _ rotation minimal
  exact ((isEmpty_counterexample_of_taitColorable h rotation).false minimal).elim

/-- The replacement obligation is unrefutable for the same reason. -/
theorem longNestedShoreSupply_of_taitColorable
    (h : AllBridgelessSphericalCubicTaitColorable.{u}) (k w N : Nat) :
    LongNestedShoreSupply.{u} k w N := by
  intro V _ _ G _ rotation minimal _
  exact ((isEmpty_counterexample_of_taitColorable h rotation).false minimal).elim

end

end GoertzelV24TargetClassVacuity

end Mettapedia.GraphTheory.FourColor
