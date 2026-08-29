import Mathlib.Data.Finset.Filter
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalReductiveAssembly

/-!
# Route-native reflection for the spherical finite base

The checked spherical headline consumes TaitBaseVerifiedAt: every bounded
bridgeless spherical cubic map is Tait colourable.  The compositional route
does not intend to establish that proposition by importing a classical
configuration catalogue.  It intends to compute a finite reachable closure
of its own interface-state machine and replay a small audit.

This module exposes the exact reflection joint between those two levels.  A
bounded map has a finite trace, every such trace lies in the computed
reachable set, and a counterexample forces a decidable necessary condition
on its trace.  If the reachable states satisfying that condition form the
empty finset, the precise TaitBaseVerifiedAt premise follows.

Nothing here asserts adequacy, coverage, or emptiness.  Those three fields
are deliberately visible because they are the remaining route-native base
work.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphericalRouteNativeBaseReflection

open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u v

/-- A route-native finite-state reflection of the spherical Tait base below
one explicit vertex bound.

The reachable set may overapproximate the traces of realizable bounded maps.
Only coverage of actual traces is required. -/
structure TaitBaseReflection
    (bound : Nat) (State : Type v) [DecidableEq State] where
  /-- The state-level condition forced by a bounded counterexample. -/
  Necessary : State → Prop
  /-- The explicitly computed finite reachable closure. -/
  reachable : Finset State
  /-- Extract a finite state from an actual bounded map in the headline
  class. -/
  trace :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
      (rotation : Data G) →
      BridgelessSphericalCubicMapData rotation.toRotationSystem →
      Fintype.card V ≤ bound →
      State
  /-- Completeness of the computed closure for traces of actual bounded
  maps. -/
  trace_mem_reachable :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G)
      (mapData :
        BridgelessSphericalCubicMapData rotation.toRotationSystem)
      (hbound : Fintype.card V ≤ bound),
      trace rotation mapData hbound ∈ reachable
  /-- Adequacy: a bounded noncolourable map forces the state-level
  obstruction on its own trace. -/
  necessary_of_not_colorable :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G)
      (mapData :
        BridgelessSphericalCubicMapData rotation.toRotationSystem)
      (hbound : Fintype.card V ≤ bound),
      ¬ RotationSystemTaitColorable rotation.toRotationSystem →
      Necessary (trace rotation mapData hbound)

namespace TaitBaseReflection

variable {bound : Nat} {State : Type v} [DecidableEq State]

/-- The logical reflection step: if no reachable state satisfies the
necessary counterexample condition, then every bounded map in the spherical
headline class is Tait colourable. -/
theorem taitBaseVerifiedAt_of_audit
    (reflection : TaitBaseReflection.{u, v} bound State)
    (haudit :
      ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state) :
    TaitBaseVerifiedAt.{u} bound := by
  intro V _ _ G _ rotation mapData hbound
  by_contra hnot
  exact haudit
    (reflection.trace rotation mapData hbound)
    (reflection.trace_mem_reachable rotation mapData hbound)
    (reflection.necessary_of_not_colorable rotation mapData hbound hnot)

/-- The replayable finite form of the audit.  Once Necessary is decidable,
the route-native base is discharged by checking that the filtered reachable
set is empty. -/
theorem taitBaseVerifiedAt_of_filter_eq_empty
    (reflection : TaitBaseReflection.{u, v} bound State)
    [DecidablePred reflection.Necessary]
    (haudit :
      reflection.reachable.filter reflection.Necessary = ∅) :
    TaitBaseVerifiedAt.{u} bound := by
  apply reflection.taitBaseVerifiedAt_of_audit
  intro state hreachable hnecessary
  have hmem :
      state ∈ reflection.reachable.filter reflection.Necessary :=
    Finset.mem_filter.mpr ⟨hreachable, hnecessary⟩
  rw [haudit] at hmem
  simp at hmem

/-- Consumer-facing assembly: a raw uniform width bound and an audited
route-native finite reflection imply the combinatorial Four-Colour
statement.  The only unproved inputs are the raw width supplier and the
three explicit fields plus finite audit carried by reflection. -/
theorem combinatorialFourColorStatement_of_raw_and_filter_audit
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (reflection :
      TaitBaseReflection.{u, v} (rawVertexBound w w) State)
    [DecidablePred reflection.Necessary]
    (haudit :
      reflection.reachable.filter reflection.Necessary = ∅) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_base w raw
    (reflection.taitBaseVerifiedAt_of_filter_eq_empty haudit)

end TaitBaseReflection

end

end GoertzelV24SphericalRouteNativeBaseReflection

end Mettapedia.GraphTheory.FourColor
