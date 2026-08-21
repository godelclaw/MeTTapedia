import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalGraphBacking
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

/-!
# Transporting a rotation-system Tait coloring to its primal graph

The ordered-cut splice already constructs a proper nonzero edge coloring on
its literal rotation-system edge carrier.  The packed reductive endpoint is
instead graph-backed.  This file closes the coloring part of that
representation junction.

For an endpoint-injective rotation system, the canonical edge equivalence is
an isomorphism from the rotation system's edge-adjacency graph to the line
graph of its computed primal simple graph.  Proper colorings and the nonzero
Tait condition therefore transport without recomputing local incidence.

The ordered-cut specialization consumes `OrderedCutEndpointSimple`, exactly
as the edge- and dart-carrier bridges do.  It does not derive that receipt
from the physical L1/C-5 crosscuts, transport the two named hole faces, or
construct the shortened packed closed-web witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemPrimalColorTransport

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The canonical primal-edge equivalence preserves and reflects edge
adjacency. -/
def edgeAdjacencyIso (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    RS.edgeAdjacencyGraph ≃g (rotationPrimalGraph RS).lineGraph where
  toEquiv := edgeEquiv RS hinjective
  map_rel_iff' := by
    intro first second
    rw [RotationSystem.edgeAdjacencyGraph_adj_iff,
      SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne, vertex, hfirst, hsecond⟩
      refine ⟨?_, vertex, ?_, ?_⟩
      · intro heq
        exact hne (congrArg (edgeEquiv RS hinjective) heq)
      · have hmem : vertex ∈ ((primalEdge RS first).1 : Sym2 V).toFinset := by
          simpa [edgeEquiv_apply, Sym2.mem_toFinset] using hfirst
        rw [primalEdge_toFinset RS first] at hmem
        exact hmem
      · have hmem : vertex ∈ ((primalEdge RS second).1 : Sym2 V).toFinset := by
          simpa [edgeEquiv_apply, Sym2.mem_toFinset] using hsecond
        rw [primalEdge_toFinset RS second] at hmem
        exact hmem
    · rintro ⟨hne, vertex, hfirst, hsecond⟩
      refine ⟨?_, vertex, ?_, ?_⟩
      · intro heq
        exact hne ((edgeEquiv RS hinjective).injective heq)
      · have hmem : vertex ∈ ((primalEdge RS first).1 : Sym2 V).toFinset := by
          rw [primalEdge_toFinset RS first]
          exact hfirst
        simpa [edgeEquiv_apply, Sym2.mem_toFinset] using hmem
      · have hmem : vertex ∈ ((primalEdge RS second).1 : Sym2 V).toFinset := by
          rw [primalEdge_toFinset RS second]
          exact hsecond
        simpa [edgeEquiv_apply, Sym2.mem_toFinset] using hmem

/-- Present a proper rotation-system edge coloring as a proper edge coloring
of the computed primal simple graph. -/
def graphEdgeColoring (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : RS.EdgeColoring Color) :
    (rotationPrimalGraph RS).EdgeColoring Color :=
  coloring.comp (edgeAdjacencyIso RS hinjective).symm.toHom

@[simp] theorem graphEdgeColoring_apply (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : RS.EdgeColoring Color)
    (edge : E) :
    graphEdgeColoring RS hinjective coloring (edgeEquiv RS hinjective edge) =
      coloring edge := by
  change coloring ((edgeAdjacencyIso RS hinjective).symm
    (edgeEquiv RS hinjective edge)) = coloring edge
  change coloring ((edgeEquiv RS hinjective).symm
    (edgeEquiv RS hinjective edge)) = coloring edge
  rw [Equiv.symm_apply_apply]

/-- The graph presentation preserves the nonzero Tait condition. -/
theorem graphEdgeColoring_isTait (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (coloring : RS.EdgeColoring Color)
    (hTait : RS.IsTaitEdgeColoring coloring) :
    IsTaitEdgeColoring (rotationPrimalGraph RS)
      (graphEdgeColoring RS hinjective coloring) := by
  intro edge
  change coloring ((edgeAdjacencyIso RS hinjective).symm edge) ≠ 0
  exact hTait ((edgeAdjacencyIso RS hinjective).symm edge)

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The literal splice coloring, presented on the computed primal graph. -/
def outputGraphColoring
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    (rotationPrimalGraph data.output).EdgeColoring Color :=
  graphEdgeColoring data.output
    (output_endpoints_injective data hambient hsimple)
    (data.splicedColoring profile)

/-- Equal source profiles give a literal Tait coloring of the computed output
graph once the exact endpoint-simplicity receipt is supplied. -/
theorem outputGraphColoring_isTait
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    IsTaitEdgeColoring (rotationPrimalGraph data.output)
      (outputGraphColoring data profile hambient hsimple) := by
  exact graphEdgeColoring_isTait data.output
    (output_endpoints_injective data hambient hsimple)
    (data.splicedColoring profile) (data.splicedColoring_isTait profile)

end OrderedCutSpliceData

end


end GoertzelV24RotationSystemPrimalColorTransport

end Mettapedia.GraphTheory.FourColor
