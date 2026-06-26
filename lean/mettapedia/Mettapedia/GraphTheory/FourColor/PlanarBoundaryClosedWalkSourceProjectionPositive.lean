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

/-- Projected non-vacuous theorem-4.9 endpoint from canonical witness choice plus the finite
no-chord carrier condition. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hChordFree : InteriorEdgesNotSelectedBoundaryChords emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    source hchoice
    (selectedBoundaryInteriorEdgeEndpointVertices_nonempty_of_interiorEdgesNotSelectedBoundaryChords_and_nonempty
      hChordFree hInterior)
    C0 hC0

/-- Projected non-vacuous theorem-4.9 endpoint from canonical witness choice plus the finite
selected-boundary inducedness condition mined by the validation lab. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_selectedBoundaryInducedSubgraph_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hInduced : SelectedBoundaryInducedSubgraph emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
    source hchoice
    (interiorEdgesNotSelectedBoundaryChords_of_selectedBoundaryInducedSubgraph hInduced)
    hInterior C0 hC0

/-- Projected non-vacuous theorem-4.9 endpoint from canonical witness choice plus the exact
finite boundary-split repair: component-wise inducedness and cross-component chord freedom. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_boundarySplitInducedCrossComponentChordFree_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {outer inner : Finset G.edgeSet}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hSelected :
      selectedBoundarySupport emb.faceBoundary emb.faces emb.faces = outer ∪ inner)
    (hOuter : BoundaryEdgeSetInducedSubgraph outer)
    (hInner : BoundaryEdgeSetInducedSubgraph inner)
    (hCross : BoundaryEdgeSetCrossComponentChordFree outer inner)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
    source hchoice
    (interiorEdgesNotSelectedBoundaryChords_of_selectedBoundarySupport_eq_union_of_induced_of_crossComponentChordFree
      hSelected hOuter hInner hCross)
    hInterior C0 hC0

/-- Projected same-embedding theorem-4.9 endpoint from the repaired finite boundary split carried
directly by the source's annulus boundary data. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_sourceBoundaryDataInducedCrossComponentChordFree_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hOuter :
      BoundaryEdgeSetInducedSubgraph
        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (hInner :
      BoundaryEdgeSetInducedSubgraph
        source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary
        source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
    source hchoice
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.interiorEdgesNotSelectedBoundaryChords_of_inducedBoundaryComponents_of_crossComponentChordFree
        hOuter hInner hCross)
    hInterior C0 hC0

/-- Graph-level projected non-vacuous theorem-4.9 endpoint from an honest closed-walk source,
canonical witness choice, and the finite no-chord carrier condition. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          InteriorEdgesNotSelectedBoundaryChords emb ∧
          (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, hchoice, hChordFree, hInterior⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_interiorEdgesNotSelectedBoundaryChords_direct
        source hchoice hChordFree hInterior C0 hC0⟩

/-- Graph-level projected non-vacuous theorem-4.9 endpoint from an honest closed-walk source,
canonical witness choice, and selected-boundary inducedness. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_selectedBoundaryInducedSubgraph_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          SelectedBoundaryInducedSubgraph emb ∧
          (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, hchoice, hInduced, hInterior⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_selectedBoundaryInducedSubgraph_direct
        source hchoice hInduced hInterior C0 hC0⟩

/-- Graph-level projected non-vacuous theorem-4.9 endpoint from an honest closed-walk source,
canonical witness choice, and the exact induced-split plus cross-free boundary repair. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_boundarySplitInducedCrossComponentChordFree_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ outer inner : Finset G.edgeSet,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          selectedBoundarySupport emb.faceBoundary emb.faces emb.faces = outer ∪ inner ∧
          BoundaryEdgeSetInducedSubgraph outer ∧
          BoundaryEdgeSetInducedSubgraph inner ∧
          BoundaryEdgeSetCrossComponentChordFree outer inner ∧
          (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, outer, inner, hchoice, hSelected, hOuter, hInner, hCross, hInterior⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_boundarySplitInducedCrossComponentChordFree_direct
        source hchoice hSelected hOuter hInner hCross hInterior C0 hC0⟩

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
