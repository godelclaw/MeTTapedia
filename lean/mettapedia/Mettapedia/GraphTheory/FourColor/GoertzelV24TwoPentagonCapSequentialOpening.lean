import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapFrontierFactorization

/-!
# L1: sequential and simultaneous two-cap openings agree

The separated two-cap laboratory may be opened in the source's order: first
open the outer cap to construct a frontier, then open the transported inner
cap.  This module proves that the resulting graph is exactly the graph obtained
by deleting both cap cycles simultaneously.

This is a graph-level comparison for a supplied cap pair.  It does not claim
that an arbitrary Addendum-V frontier has such a closed antecedent.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapSequentialOpening

open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapFrontierFactorization
open GoertzelV24TwoPentagonCapFrontierFactorization.PentagonCapPair
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCapPair

local instance outerOpenGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.outer.openGraph.Adj :=
  Classical.decRel _

/-- Restricting the inner cap to the outer-open frontier does not change the
value-level set of its five cycle edges. -/
theorem innerInOuterOpenGraph_cycleValueSet_eq
    (caps : PentagonCapPair G) :
    edgeFinsetValueSet (innerInOuterOpenGraph caps).cycleSupport =
      edgeFinsetValueSet caps.inner.cycleSupport := by
  ext edge
  constructor
  · intro hrestricted
    rcases (mem_edgeFinsetValueSet_iff
      (innerInOuterOpenGraph caps).cycleSupport edge).mp hrestricted with
      ⟨restrictedEdge, hrestrictedEdge, hvalue⟩
    rcases Finset.mem_map.mp hrestrictedEdge with
      ⟨step, -, hstep⟩
    apply (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport edge).mpr
    refine ⟨caps.inner.cycleEdge step, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨step, Finset.mem_univ step, rfl⟩
    · calc
        (caps.inner.cycleEdge step).1 =
            ((innerInOuterOpenGraph caps).cycleEdge step).1 := rfl
        _ = restrictedEdge.1 := congrArg Subtype.val hstep
        _ = edge := hvalue
  · intro hambient
    rcases (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport edge).mp hambient with
      ⟨ambientEdge, hambientEdge, hvalue⟩
    rcases Finset.mem_map.mp hambientEdge with ⟨step, -, hstep⟩
    apply (mem_edgeFinsetValueSet_iff
      (innerInOuterOpenGraph caps).cycleSupport edge).mpr
    refine ⟨(innerInOuterOpenGraph caps).cycleEdge step, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨step, Finset.mem_univ step, rfl⟩
    · calc
        ((innerInOuterOpenGraph caps).cycleEdge step).1 =
            (caps.inner.cycleEdge step).1 := rfl
        _ = ambientEdge.1 := congrArg Subtype.val hstep
        _ = edge := hvalue

omit [DecidableRel G.Adj] in
/-- The value-level deletion set of a simultaneous pair is the union of the
two individual cap deletion sets. -/
theorem cycleValueSet_eq_union (caps : PentagonCapPair G) :
    edgeFinsetValueSet caps.cycleSupport =
      edgeFinsetValueSet caps.inner.cycleSupport ∪
        edgeFinsetValueSet caps.outer.cycleSupport := by
  ext edge
  simp only [mem_edgeFinsetValueSet_iff, PentagonCapPair.cycleSupport,
    Finset.mem_union]
  constructor
  · rintro ⟨graphEdge, hinner | houter, hvalue⟩
    · exact Or.inl ⟨graphEdge, hinner, hvalue⟩
    · exact Or.inr ⟨graphEdge, houter, hvalue⟩
  · rintro (⟨graphEdge, hinner, hvalue⟩ | ⟨graphEdge, houter, hvalue⟩)
    · exact ⟨graphEdge, Or.inl hinner, hvalue⟩
    · exact ⟨graphEdge, Or.inr houter, hvalue⟩

/-- Opening the transported inner cap of the outer-open frontier gives
exactly the simultaneous two-cap opening graph. -/
theorem sequentialOpenGraph_eq_openGraph (caps : PentagonCapPair G) :
    (innerInOuterOpenGraph caps).openGraph = caps.openGraph := by
  change
    (G.deleteEdges (edgeFinsetValueSet caps.outer.cycleSupport)).deleteEdges
        (edgeFinsetValueSet (innerInOuterOpenGraph caps).cycleSupport) =
      G.deleteEdges (edgeFinsetValueSet caps.cycleSupport)
  rw [SimpleGraph.deleteEdges_deleteEdges,
    innerInOuterOpenGraph_cycleValueSet_eq,
    cycleValueSet_eq_union, Set.union_comm]

end PentagonCapPair

end


end GoertzelV24TwoPentagonCapSequentialOpening

end Mettapedia.GraphTheory.FourColor
