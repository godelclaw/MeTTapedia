import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutPair

/-!
# Open interfaces of paired annular crosscuts

The compositional source works with open tangles: a transversal opens each
crossed edge to two boundary ends.  This file exposes that construction for a
pair of source transversals.  In particular, the two interfaces have distinct
fresh boundary stubs even when their old primal endpoints happen to coincide.
That is why the source splice is first an operation on open instances, rather
than an unqualified retained-vertex graph surgery.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance openInterfaceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace AlignedSimpleDualCrosscuts

/-- One actual oriented boundary end exposed by the left source
transversal.  The index retains the source order and the dart retains which
end of the crossed primal edge was opened. -/
abbrev LeftInterfaceEnd
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :=
  Σ step : Fin pair.left.walk.length,
    {dart : RS.D // RS.edgeOf dart = pair.left.crossingEdge hunique step}

/-- One actual oriented boundary end exposed by the right source
transversal. -/
abbrev RightInterfaceEnd
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :=
  Σ step : Fin pair.right.walk.length,
    {dart : RS.D // RS.edgeOf dart = pair.right.crossingEdge hunique step}

/-- Embed a left interface end in the simultaneous slit's literal cut-dart
carrier. -/
def leftInterfaceCutDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (endpoint : pair.LeftInterfaceEnd) : CutDart RS pair.crossingSupport :=
  ⟨endpoint.2.1,
    pair.left_crossingEdges_subset_support
      ((pair.left.mem_crossingEdges_iff hunique _).2
        ⟨endpoint.1, endpoint.2.2.symm⟩)⟩

/-- Embed a right interface end in the simultaneous slit's literal cut-dart
carrier. -/
def rightInterfaceCutDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (endpoint : pair.RightInterfaceEnd) : CutDart RS pair.crossingSupport :=
  ⟨endpoint.2.1,
    pair.right_crossingEdges_subset_support
      ((pair.right.mem_crossingEdges_iff hunique _).2
        ⟨endpoint.1, endpoint.2.2.symm⟩)⟩

/-- The fresh slit dart at a left interface end. -/
def leftInterfaceStub
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (endpoint : pair.LeftInterfaceEnd) : SlitDart RS pair.crossingSupport :=
  Sum.inr (pair.leftInterfaceCutDart endpoint)

/-- The fresh slit dart at a right interface end. -/
def rightInterfaceStub
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (endpoint : pair.RightInterfaceEnd) : SlitDart RS pair.crossingSupport :=
  Sum.inr (pair.rightInterfaceCutDart endpoint)

/-- The two source interfaces are disjoint in the simultaneous slit's
boundary carrier.  This follows from edge-disjointness of the original
crosscuts; it does not require their old endpoint vertices to be different. -/
theorem leftInterfaceCutDart_ne_rightInterfaceCutDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd) (right : pair.RightInterfaceEnd) :
    pair.leftInterfaceCutDart left ≠ pair.rightInterfaceCutDart right := by
  intro hcutDarts
  have hdarts : left.2.1 = right.2.1 :=
    congrArg Subtype.val hcutDarts
  have hedges : pair.left.crossingEdge hunique left.1 =
      pair.right.crossingEdge hunique right.1 := by
    calc
      pair.left.crossingEdge hunique left.1 = RS.edgeOf left.2.1 :=
        left.2.2.symm
      _ = RS.edgeOf right.2.1 := congrArg RS.edgeOf hdarts
      _ = pair.right.crossingEdge hunique right.1 := right.2.2
  have hleft : pair.left.crossingEdge hunique left.1 ∈
      pair.left.crossingEdges hunique :=
    (pair.left.mem_crossingEdges_iff hunique _).2 ⟨left.1, rfl⟩
  have hright : pair.left.crossingEdge hunique left.1 ∈
      pair.right.crossingEdges hunique := by
    rw [hedges]
    exact (pair.right.mem_crossingEdges_iff hunique _).2 ⟨right.1, rfl⟩
  exact (Finset.disjoint_left.1 pair.crossing_disjoint hleft hright).elim

/-- The two exposed interfaces remain distinct as fresh slit darts. -/
theorem leftInterfaceStub_ne_rightInterfaceStub
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd) (right : pair.RightInterfaceEnd) :
    pair.leftInterfaceStub left ≠ pair.rightInterfaceStub right := by
  intro hstubs
  apply pair.leftInterfaceCutDart_ne_rightInterfaceCutDart left right
  exact Sum.inr.inj hstubs

/-- In the actual cut-open rotation system, opposite source interfaces have
different boundary vertices.  This is the source-faithful noncollision fact:
opening the edges creates the boundary ends before any gluing is attempted. -/
theorem leftInterfaceStub_vertex_ne_rightInterfaceStub_vertex
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd) (right : pair.RightInterfaceEnd) :
    (pair.slitRotationSystem).vertOf (pair.leftInterfaceStub left) ≠
      (pair.slitRotationSystem).vertOf (pair.rightInterfaceStub right) := by
  intro hvertices
  apply pair.leftInterfaceCutDart_ne_rightInterfaceCutDart left right
  change
    (Sum.inr (pair.leftInterfaceCutDart left) :
        SlitVertex RS pair.crossingSupport) =
      Sum.inr (pair.rightInterfaceCutDart right) at hvertices
  exact Sum.inr.inj hvertices

/-- Gluing any left source port to a right source port in the cut-open
rotation system cannot create a self-loop: the two endpoints are literal,
distinct fresh boundary vertices.  This is the basic well-formedness fact for
the source's open-tangle composition, and does not ask the old closed graph
to have disjoint endpoint vertices. -/
theorem openInterface_matching_no_selfLoop
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (matching : pair.LeftInterfaceEnd → pair.RightInterfaceEnd) :
    ∀ left,
      (pair.slitRotationSystem).vertOf (pair.leftInterfaceStub left) ≠
        (pair.slitRotationSystem).vertOf
          (pair.rightInterfaceStub (matching left)) := by
  intro left
  exact pair.leftInterfaceStub_vertex_ne_rightInterfaceStub_vertex left
    (matching left)

end AlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
