import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# Presenting a rotation-system edge carrier as a simple graph

The concrete corridor splice changes both the vertex and edge carriers.  The
next closed-web descent step, however, is stated over a graph-backed rotation.
This file closes the edge-carrier part of that junction.

Every edge of a bare rotation system determines an edge of its computed primal
simple graph, and this map is always onto.  It is one-to-one exactly at the
load-bearing side of the no-parallel-edge condition: injectivity of the
rotation system's endpoint map.  Thus an output satisfying the already-defined
finite `OrderedCutEndpointSimple` test has a canonical edge equivalence with
its primal graph.  The theorem does not assume that a general splice is simple,
and it does not yet transport the dart rotation or the two named hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemPrimalEdgePresentation

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A fixed representative dart over one rotation-system edge. -/
def chosenDart (RS : RotationSystem V E) (edge : E) : RS.D :=
  Classical.choose (RS.dartsOn_nonempty edge)

theorem chosenDart_mem (RS : RotationSystem V E) (edge : E) :
    chosenDart RS edge ∈ RS.dartsOn edge :=
  Classical.choose_spec (RS.dartsOn_nonempty edge)

theorem chosenDart_edgeOf (RS : RotationSystem V E) (edge : E) :
    RS.edgeOf (chosenDart RS edge) = edge :=
  RS.mem_dartsOn.mp (chosenDart_mem RS edge)

/-- The undirected primal edge represented by one rotation-system edge. -/
def primalEdge (RS : RotationSystem V E) (edge : E) :
    (rotationPrimalGraph RS).edgeSet :=
  ⟨s(RS.vertOf (chosenDart RS edge),
      RS.vertOf (RS.alpha (chosenDart RS edge))),
    (SimpleGraph.mem_edgeSet (rotationPrimalGraph RS)).2
      ⟨chosenDart RS edge, rfl, rfl⟩⟩

/-- Forgetting the unordered-pair presentation recovers the intrinsic
rotation-system endpoint set. -/
theorem primalEdge_toFinset (RS : RotationSystem V E) (edge : E) :
    ((primalEdge RS edge).1 : Sym2 V).toFinset = RS.endpoints edge := by
  rw [RS.endpoints_eq_pair_of_mem (chosenDart_mem RS edge)]
  ext vertex
  simp [primalEdge, Sym2.mem_toFinset]

/-- Every edge of the computed primal graph comes from a rotation-system
edge.  No simplicity premise is needed in this direction. -/
theorem primalEdge_surjective (RS : RotationSystem V E) :
    Function.Surjective (primalEdge RS) := by
  rintro ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hadj : (rotationPrimalGraph RS).Adj left right :=
        (SimpleGraph.mem_edgeSet (rotationPrimalGraph RS)).1 hedge
      rcases hadj with ⟨dart, hleft, hright⟩
      refine ⟨RS.edgeOf dart, ?_⟩
      apply Subtype.ext
      have hvalue :
          (primalEdge RS (RS.edgeOf dart)).1 = s(left, right) := by
        change s(RS.vertOf (chosenDart RS (RS.edgeOf dart)),
          RS.vertOf (RS.alpha (chosenDart RS (RS.edgeOf dart)))) = s(left, right)
        rcases RS.edge_fiber_two_cases
            (chosenDart_edgeOf RS (RS.edgeOf dart)) rfl with hsame | hreverse
        · rw [← hsame, hleft, hright]
        · have hchosen : chosenDart RS (RS.edgeOf dart) = RS.alpha dart := by
            have halpha := congrArg RS.alpha hreverse
            simpa [RS.alpha_involutive] using halpha.symm
          rw [hchosen, RS.alpha_involutive, hright, hleft]
          exact Sym2.eq_swap
      exact hvalue

/-- Distinct endpoint sets make the primal-edge presentation injective. -/
theorem primalEdge_injective (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    Function.Injective (primalEdge RS) := by
  intro first second heq
  apply hinjective
  rw [← primalEdge_toFinset RS first, ← primalEdge_toFinset RS second, heq]

/-- A no-parallel rotation system has exactly the edge carrier of its
computed primal simple graph. -/
def edgeEquiv (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    E ≃ (rotationPrimalGraph RS).edgeSet :=
  Equiv.ofBijective (primalEdge RS)
    ⟨primalEdge_injective RS hinjective, primalEdge_surjective RS⟩

@[simp] theorem edgeEquiv_apply (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (edge : E) :
    edgeEquiv RS hinjective edge = primalEdge RS edge :=
  rfl

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The explicit edge carrier hidden in the result type of `data.output`. -/
abbrev OutputEdge
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :=
  (orderedCutRetainedVertexRewiredDartSystem RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective data.rightInjective
    data.cover data.disjoint data.outer_kept data.seamEndpoints).Edge

/-- The finite seam-endpoint test upgrades the literal splice output to an
endpoint-injective rotation system.  This is the exact prerequisite for a
simple-graph presentation, not an extra planarity hypothesis. -/
theorem output_endpoints_injective
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    Function.Injective data.output.endpoints := by
  unfold GoertzelV24SpliceUnification.OrderedCutSpliceData.output
  exact orderedCutRetainedVertexRotationSystem_endpoints_injective RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective data.rightInjective
    data.cover data.disjoint data.outer_kept data.seamEndpoints hambient hsimple

/-- Under that exact finite test, the splice output's abstract edge type is
canonically equivalent to the edge subtype of its computed primal graph. -/
def outputEdgeEquiv
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    OutputEdge data ≃ (rotationPrimalGraph data.output).edgeSet :=
  edgeEquiv data.output (output_endpoints_injective data hambient hsimple)

end OrderedCutSpliceData

end

end GoertzelV24RotationSystemPrimalEdgePresentation

end Mettapedia.GraphTheory.FourColor
