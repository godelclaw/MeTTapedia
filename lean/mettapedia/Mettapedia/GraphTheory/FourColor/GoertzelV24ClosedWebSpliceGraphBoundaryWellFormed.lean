import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphBoundaryData

/-!
# Well-formed boundary data on the graph-backed splice output

The source-facing L1 splice keeps both named hole faces outside the pumped
region.  The preceding boundary-data module uses that fact to retain the ten
ordered stubs and their incident edges.  This module proves that the resulting
graph-backed boundary datum is genuinely `WellFormed`.

The proof transports edge incidence through the literal retained-edge
decomposition and transports local degree through the dart equivalence between
an endpoint-simple rotation system and its computed primal graph.  It does not
postulate global cubicity: the ten retained boundary vertices remain degree
one, while source cubicity is reused only at every other retained vertex.

This closes the graph-level boundary interface of the shortened carrier.  It
does not yet construct the output annular cellulation or prove the
counterexample-preservation field of the final reductive system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemPrimalGraphBacking

open GoertzelV24FaceDualConnectedness

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance boundaryRotationPrimalGraphAdjDecidable
    (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

/-- Restrict the canonical literal-dart equivalence to the darts based at one
vertex. -/
def primalDartsAtEquiv (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (vertex : V) :
    { dart : RS.D // RS.vertOf dart = vertex } ≃
      { dart : (rotationPrimalGraph RS).Dart // dart.fst = vertex } :=
  (primalDartEquiv RS hinjective).subtypeEquiv (fun dart => by
    simp only [primalDartEquiv_fst])

/-- The computed primal graph has exactly the same local degree as its
endpoint-simple rotation-system presentation. -/
theorem incidentEdgeFinset_card_rotationPrimalGraph_eq_dartsAt_card
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (vertex : V) :
    (incidentEdgeFinset (rotationPrimalGraph RS) vertex).card =
      (RS.dartsAt vertex).card := by
  rw [GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := rotationPrimalGraph RS)]
  rw [← (rotationPrimalGraph RS).dart_fst_fiber_card_eq_degree vertex]
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (primalDartsAtEquiv RS hinjective vertex)).symm

end


end GoertzelV24RotationSystemPrimalGraphBacking

namespace GoertzelV24ClosedWebAtGoodWord.Instance

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24SpliceUnification

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : Instance data coloring}

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

local instance boundarySourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance boundaryOutputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

/-- A retained source edge remains incident to the corresponding retained
vertex in the computed shortened graph. -/
theorem outputBoundaryEdge_incident
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (edge : G.edgeSet)
    (hkept : ∀ dart ∈ web.annular.RS.dartsOn edge,
      splice.keep (web.annular.RS.vertOf dart))
    (vertex : W) (hvertexKept : splice.keep vertex)
    (hincident : edge ∈ incidentEdgeFinset G vertex) :
    outputBoundaryEdge splice hsimple edge hkept ∈
      incidentEdgeFinset (rotationPrimalGraph splice.output)
        (⟨vertex, hvertexKept⟩ : RetainedVertex splice.keep) := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hsource : vertex ∈ web.annular.RS.endpoints edge :=
    (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      web.annular.cellulation.rotation edge vertex).2
      (by
        simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
          true_and] using hincident)
  let dart := internalDartOfEdgeKept web.annular.RS splice.keep edge hkept
  have himage : vertex ∈
      (retainedInternalEndpointPair web.annular.RS splice.keep dart).image
        Subtype.val := by
    rw [image_val_retainedInternalEndpointPair,
      internalDartOfEdgeKept_edgeOf]
    exact hsource
  rcases Finset.mem_image.1 himage with ⟨retained, hretained, hvalue⟩
  have heq : retained =
      (⟨vertex, hvertexKept⟩ : RetainedVertex splice.keep) := by
    apply Subtype.ext
    exact hvalue
  have houtEndpoint :
      (⟨vertex, hvertexKept⟩ : RetainedVertex splice.keep) ∈
        splice.output.endpoints
          (retainedInternalSpliceEdge web.annular.RS splice.keep
            splice.left.crossingEdge splice.right.crossingEdge
            splice.leftCrosses splice.rightCrosses splice.leftInjective
            splice.rightInjective splice.cover splice.disjoint splice.outer_kept
            splice.seamEndpoints dart) := by
    unfold GoertzelV24SpliceUnification.OrderedCutSpliceData.output
    rw [endpoints_retainedInternalSpliceEdge]
    simpa [heq] using hretained
  have hfinset :
      (⟨vertex, hvertexKept⟩ : RetainedVertex splice.keep) ∈
        ((outputBoundaryEdge splice hsimple edge hkept).1 :
          Sym2 (RetainedVertex splice.keep)).toFinset := by
    change (⟨vertex, hvertexKept⟩ : RetainedVertex splice.keep) ∈
      ((primalEdge splice.output
        (retainedInternalSpliceEdge web.annular.RS splice.keep
          splice.left.crossingEdge splice.right.crossingEdge
          splice.leftCrosses splice.rightCrosses splice.leftInjective
          splice.rightInjective splice.cover splice.disjoint splice.outer_kept
          splice.seamEndpoints dart)).1 :
        Sym2 (RetainedVertex splice.keep)).toFinset
    rw [primalEdge_toFinset]
    exact houtEndpoint
  simpa [Sym2.mem_toFinset] using hfinset

/-- Both ordered hole interfaces remain graph-level well-formed after the
endpoint-simple L1 splice. -/
theorem outputBoundaryData_wellFormed
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    (outputBoundaryData splice hinner houter hsimple).WellFormed := by
  let hinnerKept : ProtectedInnerInterface.InnerBoundaryKept splice :=
    innerBoundaryKept_of_innerHoleFaceKept splice hinner
  let houterKept : ProtectedInnerInterface.OuterBoundaryKept splice :=
    outerBoundaryKept_of_outerHoleFaceKept splice houter
  have hambient : Function.Injective web.annular.RS.endpoints :=
    endpoints_injective web.annular.cellulation.rotation
  have hout : Function.Injective splice.output.endpoints :=
    output_endpoints_injective splice hambient hsimple
  refine {
    inner_outer_stub_disjoint := ?_
    inner_outer_edge_disjoint := ?_
    innerBoundaryEdge_incident := ?_
    outerBoundaryEdge_incident := ?_
    inner_stub_degree_one := ?_
    outer_stub_degree_one := ?_
    cubic_elsewhere := ?_ }
  · intro inner outer heq
    apply web.boundary_wellFormed.inner_outer_stub_disjoint inner outer
    exact congrArg Subtype.val heq
  · intro inner outer heq
    apply web.boundary_wellFormed.inner_outer_edge_disjoint inner outer
    exact outputBoundaryEdge_injective splice hsimple
      (hinnerKept inner) (houterKept outer) heq
  · intro inner
    exact outputBoundaryEdge_incident splice hsimple
      (data.innerBoundaryEdge inner) (hinnerKept inner)
      (data.innerStub inner) (outputInnerStub splice hinner inner).2
      (web.boundary_wellFormed.innerBoundaryEdge_incident inner)
  · intro outer
    exact outputBoundaryEdge_incident splice hsimple
      (data.outerBoundaryEdge outer) (houterKept outer)
      (data.outerStub outer) (outputOuterStub splice houter outer).2
      (web.boundary_wellFormed.outerBoundaryEdge_incident outer)
  · intro inner
    rw [incidentEdgeFinset_card_rotationPrimalGraph_eq_dartsAt_card
      splice.output hout]
    exact ProtectedInnerInterface.output_dartsAt_card_eq_one_of_innerBoundaryKept
      splice hinnerKept inner
  · intro outer
    rw [incidentEdgeFinset_card_rotationPrimalGraph_eq_dartsAt_card
      splice.output hout]
    exact ProtectedInnerInterface.output_dartsAt_card_eq_one_of_outerBoundaryKept
      splice houterKept outer
  · intro vertex hnotInner hnotOuter
    rw [incidentEdgeFinset_card_rotationPrimalGraph_eq_dartsAt_card
      splice.output hout]
    unfold GoertzelV24SpliceUnification.OrderedCutSpliceData.output
    rw [orderedCutRetainedVertexRotationSystem_dartsAt_card web.annular.RS
      splice.keep splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses splice.leftInjective
      splice.rightInjective splice.cover splice.disjoint splice.outer_kept
      splice.seamEndpoints vertex]
    change ({dart : G.Dart | dart.fst = vertex.1} : Finset G.Dart).card = 3
    rw [G.dart_fst_fiber_card_eq_degree vertex.1]
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
      (G := G)]
    apply web.boundary_wellFormed.cubic_elsewhere
    · intro inner heq
      apply hnotInner inner
      apply Subtype.ext
      exact heq
    · intro outer heq
      apply hnotOuter outer
      apply Subtype.ext
      exact heq

end

end GoertzelV24ClosedWebAtGoodWord.Instance

end Mettapedia.GraphTheory.FourColor
