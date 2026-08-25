import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# Forgetting coordinates of a deletion-stable interface

Successor interfaces generally retain only some coordinates of a larger
transition interface.  Restricting the old code along the retained-coordinate
map is not sound: a forgotten coordinate becomes an exterior graph vertex and
may connect two retained coordinates.

This file gives the exact graph operation underlying that reindexing.  The
finite mask selects precisely the retained coordinates in the larger
interface.  Applying that mask therefore produces the graph strictly outside
the retained interface.  Aliases and noninjective coordinate maps are handled
by ambient vertex equality, so no freshness premise is needed.

The next finite-code theorem can use this identity to compute the new
`exteriorConnected` row by a closure through the forgotten coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorForget

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorTotal
open SimpleGraph

/-- Select the image of the retained-coordinate map inside the larger
interface. -/
noncomputable def retainedCoordinateMask
    {Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (retain : Retained → Larger) (slot : Larger) : Bool := by
  classical
  exact decide (∃ retained, retain retained = slot)

@[simp]
theorem retainedCoordinateMask_eq_true_iff
    {Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (retain : Retained → Larger) (slot : Larger) :
    retainedCoordinateMask retain slot = true ↔
      ∃ retained, retain retained = slot := by
  classical
  simp [retainedCoordinateMask]

/-- The retained-coordinate mask selects exactly the ambient vertices named
by the smaller interface.  Injectivity of either presentation is unnecessary:
masking one alias masks every alias of the same ambient vertex. -/
theorem removedBy_retainedCoordinateMask_iff
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Larger)
    (hretain : ∀ retained,
      largerVertex (retain retained) = retainedVertex retained)
    (vertex : N) :
    RemovedByInterfaceMask largerVertex (retainedCoordinateMask retain)
        vertex ↔
      ∃ retained, vertex = retainedVertex retained := by
  constructor
  · rintro ⟨slot, hslot, hvertex⟩
    rw [retainedCoordinateMask_eq_true_iff] at hslot
    rcases hslot with ⟨retained, rfl⟩
    exact ⟨retained, hvertex.trans (hretain retained)⟩
  · rintro ⟨retained, hvertex⟩
    refine ⟨retain retained, ?_, ?_⟩
    · rw [retainedCoordinateMask_eq_true_iff]
      exact ⟨retained, rfl⟩
    · exact hvertex.trans (hretain retained).symm

/-- Surviving the retained-coordinate mask is exactly being strictly outside
the retained ambient interface. -/
theorem survives_retainedCoordinateMask_iff_outsideInterface
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Larger)
    (hretain : ∀ retained,
      largerVertex (retain retained) = retainedVertex retained)
    (vertex : N) :
    survivesMask largerVertex (retainedCoordinateMask retain) vertex ↔
      OutsideInterface retainedVertex vertex := by
  rw [survivesMask_iff_not_removedByInterfaceMask,
    removedBy_retainedCoordinateMask_iff largerVertex retainedVertex retain
      hretain]
  simp only [OutsideInterface]
  constructor
  · intro hnot retained heq
    exact hnot ⟨retained, heq⟩
  · intro houtside hnamed
    rcases hnamed with ⟨retained, heq⟩
    exact houtside retained heq

/-- Crown graph identity for interface forgetting.  Deleting the coordinates
which the successor retains from the larger interface leaves exactly the
ambient graph exterior to the successor interface.  Hence forgotten
coordinates are available as exterior vertices rather than silently lost. -/
theorem restrictedBy_retainedCoordinateMask_eq_exteriorGraph
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Larger)
    (hretain : ∀ retained,
      largerVertex (retain retained) = retainedVertex retained) :
    restrictedByMask graph largerVertex (retainedCoordinateMask retain) =
      exteriorGraph graph retainedVertex := by
  ext left right
  simp only [restrictedByMask, exteriorGraph, supportRestriction_adj]
  rw [survives_retainedCoordinateMask_iff_outsideInterface largerVertex
      retainedVertex retain hretain left,
    survives_retainedCoordinateMask_iff_outsideInterface largerVertex
      retainedVertex retain hretain right]

/-- The exterior connectivity needed by the smaller interface is therefore an
ordinary finite closure in the larger deletion-stable code, restricted to
coordinates which survive the retained-coordinate mask.  This is the exact
operation that a successor reindexing must execute; merely pulling back the
old `exteriorConnected` table would omit paths through forgotten slots. -/
theorem exteriorGraph_reachable_iff_exactInterfaceExteriorFactoredClosure
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Larger)
    (hretain : ∀ retained,
      largerVertex (retain retained) = retainedVertex retained)
    (left right : SurvivingInterfaceSlot largerVertex
      (retainedCoordinateMask retain)) :
    (exteriorGraph graph retainedVertex).Reachable
        (largerVertex left.1) (largerVertex right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot largerVertex
            (retainedCoordinateMask retain) =>
          InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            first.1 second.1)
        left right := by
  rw [← restrictedBy_retainedCoordinateMask_eq_exteriorGraph graph
    largerVertex retainedVertex retain hretain]
  exact
    restrictedByMask_reachable_iff_exactInterfaceExteriorFactoredClosure
      graph largerVertex (retainedCoordinateMask retain) left right

/-- Select the larger coordinates named by a partial successor map.  A target
coordinate mapped to `none` is intended to be inactive in the graph currently
being reindexed. -/
noncomputable def partialRetainedCoordinateMask
    {Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (retain : Retained → Option Larger) (slot : Larger) : Bool := by
  classical
  exact decide (∃ retained, retain retained = some slot)

@[simp]
theorem partialRetainedCoordinateMask_eq_true_iff
    {Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (retain : Retained → Option Larger) (slot : Larger) :
    partialRetainedCoordinateMask retain slot = true ↔
      ∃ retained, retain retained = some slot := by
  classical
  simp [partialRetainedCoordinateMask]

private theorem restrictedByMask_all_true_eq_exteriorGraph
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) :
    restrictedByMask graph interfaceVertex (fun _ => true) =
      exteriorGraph graph interfaceVertex := by
  ext left right
  simp only [restrictedByMask, exteriorGraph, supportRestriction_adj,
    survivesMask, forall_const]
  rfl

/-- Partial successor reindexing has the same exterior graph as the literal
target interface when every unmapped target coordinate is inactive.  This is
the graph-level soundness condition for padded bounded carriers: `none` may
stand only for an isolated coordinate, never for hidden live support. -/
theorem restrictedBy_partialRetainedCoordinateMask_eq_exteriorGraph
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support) :
    restrictedByMask graph largerVertex
        (partialRetainedCoordinateMask retain) =
      exteriorGraph graph retainedVertex := by
  rw [← restrictedByMask_all_true_eq_exteriorGraph graph retainedVertex]
  apply restrictedByMask_eq_of_removedByInterfaceMask_iff_on_support
  intro vertex hvertex
  constructor
  · rintro ⟨slot, hslot, hvertexSlot⟩
    rw [partialRetainedCoordinateMask_eq_true_iff] at hslot
    rcases hslot with ⟨retained, hretained⟩
    refine ⟨retained, rfl, ?_⟩
    exact hvertexSlot.trans (hsome retained slot hretained)
  · rintro ⟨retained, _hremoved, hvertexRetained⟩
    cases hretained : retain retained with
    | none =>
        have hnotSupport := hnone retained hretained
        exact (hnotSupport (hvertexRetained ▸ hvertex)).elim
    | some slot =>
        refine ⟨slot, ?_, ?_⟩
        · rw [partialRetainedCoordinateMask_eq_true_iff]
          exact ⟨retained, hretained⟩
        · exact hvertexRetained.trans (hsome retained slot hretained).symm

end GoertzelV24InterfaceDeletionComponentFactorForget

end Mettapedia.GraphTheory.FourColor
