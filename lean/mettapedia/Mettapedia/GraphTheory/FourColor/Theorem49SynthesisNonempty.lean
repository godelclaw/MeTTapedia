import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisRoutes

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]


/-- Non-vacuous version of the common Theorem 4.9 synthesis endpoint. This deliberately does not
change the algebraic package: it records the additional route obligation that the selected-
boundary purified interior-edge endpoint carrier actually contains a vertex. -/
structure Theorem49BoundaryRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ : G.EdgeColoring Color) : Prop where
  synthesis : Theorem49BoundaryRootSynthesis emb C₀
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- Outer-boundary-root presentation of the non-vacuous synthesis package. -/
abbrev Theorem49OuterBoundaryRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootNonemptySynthesis emb C₀

/-- Two-sided annulus-root presentation of the non-vacuous synthesis package. -/
abbrev Theorem49AnnulusRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootNonemptySynthesis emb C₀

/-- Construct the non-vacuous synthesis package from generic boundary-root interior-dual data
when the selected-boundary purified carrier is known to be nonempty. -/
theorem theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ where
  synthesis :=
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀
  carrier_nonempty := hCarrier

/-- Construct the non-vacuous outer-boundary-root synthesis package when the selected-boundary
purified carrier is known to be nonempty. -/
theorem theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀ hCarrier

/-- Endpoint-separated outer-boundary-rooted annulus data yields the non-vacuous synthesis
package as soon as the raw interior-edge endpoint carrier is nonempty. The endpoint-separation
field makes selected-boundary purification lossless, so no extra carrier hypothesis is needed
beyond nonemptiness of the raw carrier itself. -/
theorem
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data.routeData C₀ := by
  have hEq :=
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport
      data
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
    rcases hRawCarrier with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [hEq] using hv
  exact theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    (G := G) data.routeData C₀ hC₀ hCarrier

/-- Construction-level peeled-face endpoint no-touch is enough to reach the non-vacuous
outer-boundary-root synthesis endpoint once the raw interior-edge endpoint carrier is nonempty.
This packages the new endpoint-separation repair without forcing downstream route theorems to
manually rebuild `WithEndpointSeparation`. -/
theorem
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ := by
  exact
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
      (G := G)
      (data.withEndpointSeparationOfPeelFacesEndpointDisjoint hPeelNoTouch)
      C₀ hC₀ hRawCarrier

/-- Construct the non-vacuous two-sided annulus-root synthesis package when the selected-boundary
purified carrier is known to be nonempty. -/
theorem theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀ hCarrier

/-- Construct the non-vacuous synthesis package directly from the two-sided annulus-root parent
package when the selected-boundary purified carrier is known to be nonempty. -/
theorem theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ where
  synthesis :=
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀
  carrier_nonempty := hCarrier

/-- Two-sided annulus-root data yields the non-vacuous synthesis endpoint as soon as the raw
interior-edge endpoint carrier is nonempty and endpoint-disjoint from the selected boundary.
Unlike the outer-root repair line, this formulation stays on the honest two-sided root surface
and therefore avoids any all-roots-on-one-boundary hypothesis. -/
theorem theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  have hEq :
      selectedBoundaryInteriorEdgeEndpointVertices emb =
        interiorEdgeEndpointSupport emb :=
    (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
      emb).2 hEndpointDisjoint
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
    rcases hRawCarrier with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [hEq] using hv
  exact
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier

/-- Construction-level peeled-face endpoint no-touch is enough to reach the non-vacuous
two-sided annulus-root synthesis endpoint once the raw interior-edge endpoint carrier is
nonempty.  This is the generic annulus-root version of the source-facing repair: it avoids the
all-outer-root localization while still making the global endpoint-separation burden explicit as
a local construction condition. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  have hEndpointDisjoint :
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
    data.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch
  exact
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ hEndpointDisjoint hRawCarrier

/-- Same-embedding non-vacuous synthesis constructor from an explicit annulus boundary split and
generic boundary-root interior-dual data, provided the selected-boundary purified carrier is
nonempty. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData interiorData)
        C₀ :=
  theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    (G := G)
    (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData)
    C₀ hC₀ hCarrier

/-- Same-embedding non-vacuous synthesis constructor from an explicit annulus boundary split and
generic boundary-root interior-dual parent data, provided the selected-boundary purified carrier
is nonempty. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData)
    C₀ hC₀ hCarrier

/-- Same-embedding non-vacuous synthesis constructor from an honest closed-walk source and
generic boundary-root interior-dual parent data. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData)
    C₀ hC₀ hCarrier

/-- Graph-level non-vacuous synthesis from explicit outer-boundary-rooted annulus data whose
selected-boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49OuterBoundaryRootNonemptySynthesis_of_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from endpoint-separated outer-boundary-rooted annulus data
whose raw interior-edge endpoint carrier is nonempty. This is the current positive repair line
that the endpoint-touch obstruction fails exactly because it cannot satisfy the endpoint-separation
field. -/
theorem
    exists_theorem49OuterBoundaryRootNonemptySynthesis_of_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation_with_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data :
        PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb,
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data :
        PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb,
        Theorem49OuterBoundaryRootNonemptySynthesis emb data.routeData C₀ := by
  rcases hG with ⟨emb, data, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
      (G := G) data C₀ hC₀ hRawCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose selected-
boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose raw
interior-edge endpoint carrier is nonempty and endpoint-disjoint from the selected boundary. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ hEndpointDisjoint hRawCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose raw
interior-edge endpoint carrier is nonempty and whose canonical construction satisfies peeled-face
endpoint no-touch. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hPeelNoTouch, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (G := G) data C₀ hC₀ hPeelNoTouch hRawCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an explicit annulus boundary split plus
generic boundary-root interior-dual data on the same embedding. This is the primitive two-sided
annulus entry point when a nonempty selected-boundary purified carrier is available. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, hCarrier⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root parent data whose
selected-boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an explicit annulus boundary split plus
generic boundary-root interior-dual parent data on the same embedding. This is the primitive
two-sided annulus entry point for the parent-oriented branch when a nonempty selected-boundary
purified carrier is available. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      (G := G) boundaryData interiorData C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an honest closed-walk source plus generic
boundary-root interior-dual parent data on the same embedding. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, source, interiorData, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      (G := G) source interiorData C₀ hC₀ hCarrier⟩

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of a target construction-side package refutes a
universal derivation from that endpoint back to that package. -/
theorem
    not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    {P : PlaneEmbeddingWithBoundary G → Type*}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (P emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (P emb) := by
  intro h
  rcases hWitness with ⟨emb, hSynth, hNoPackage⟩
  rcases hSynth with ⟨C, hC, hBoundary⟩
  exact hNoPackage (h (emb := emb) C hC hBoundary)

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of boundary-support face data refutes a universal
derivation from that endpoint back to that construction shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without
      (P := fun emb => PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) hWitness

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of face-partition data refutes a universal
derivation from that endpoint back to that construction shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  exact
    not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without
      (P := fun emb => PlanarBoundaryAnnulusConstructionFacePartitionData emb) hWitness

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of face-layer data refutes a universal derivation
from that endpoint back to that construction shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without
      (P := fun emb => PlanarBoundaryAnnulusConstructionFaceLayerData emb) hWitness

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of positive-frontier construction data refutes a
universal derivation from that endpoint back to the positive-frontier shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without
      (P := fun emb => PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) hWitness

/-- Any explicit same-embedding witness carrying a real Tait coloring, the final theorem-4.9
boundary-root synthesis endpoint, and failure of every currently formalized positive-stage
construction shell refutes a universal derivation from that endpoint to the disjunctive
positive-stage construction surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
        NoPositiveStageConstructionShells emb) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            SomePositiveStageConstructionShell emb := by
  intro h
  rcases hWitness with ⟨emb, hSynth, hNo⟩
  rcases hSynth with ⟨C, hC, hBoundary⟩
  exact
    not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo
      (h (emb := emb) C hC hBoundary)

end Mettapedia.GraphTheory.FourColor
