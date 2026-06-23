import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjectionCore
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Canonical source witness choice gives the positive same-embedding endpoint.  The canonical
choice first builds the one-collar annulus geometry, whose repaired previous-boundary witness
surface yields the finite collar-layer witness-cover package used by the projection layer. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hchoice with ⟨choice⟩
  let collar : PlanarBoundaryAnnulusCollarGeometry emb :=
    choice.toPlanarBoundaryAnnulusCollarGeometry
  let previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
    collar.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
      choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) previous.toPlanarBoundaryCollarLayerFacePeelWitnessData C0 hC0 hCarrier

/-- Graph-level positive endpoint from an honest closed-walk source with canonical witness choice
and a nonempty selected-boundary-purified carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, hchoice, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        source hchoice hCarrier C0 hC0⟩

/-- Same-boundary one-collar source geometry gives the positive same-embedding endpoint.  The
source-boundary equality keeps this theorem aligned with the geometric construction surface. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1)
    (hboundary :
      data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let _ := hboundary
  let previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
    data.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one hnum
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) previous.toPlanarBoundaryCollarLayerFacePeelWitnessData C0 hC0 hCarrier

/-- Graph-level positive endpoint from an honest closed-walk source with same-boundary one-collar
geometry and a nonempty selected-boundary-purified carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, data, hnum, hboundary, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        source data hnum hboundary hCarrier C0 hC0⟩

end Mettapedia.GraphTheory.FourColor
