import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesEndpointObstructionPeeledModel
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisNonempty

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49InteriorVerticesEndpointObstruction

/-- The current outer-boundary-rooted adjacency-distance peel package is still only an
edge-disjoint package. It does not imply the raw endpoint-support separation needed to use
`interiorEdgeEndpointSupport` without the separate peeled-face endpoint no-touch hypothesis. -/
theorem outerBoundaryRootAdjDistancePeelData_does_not_imply_endpointSupport_disjoint_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    not_endpointSupport_disjoint_peeledEndpointTouch⟩

/-- On the endpoint-touch embedding, no theorem can derive raw endpoint-support separation from
arbitrary outer-boundary-rooted peeled route data alone. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact not_endpointSupport_disjoint_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

/-- On the endpoint-touch embedding, no theorem can derive the peeled-face endpoint no-touch
bridge premise from arbitrary outer-boundary-rooted peeled route data alone. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_peelFaces_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      ∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          data).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

theorem not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch :
    ¬ Nonempty
      (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
        peeledEndpointTouchEmbedding) := by
  rintro ⟨data⟩
  exact not_endpointSupport_disjoint_peeledEndpointTouch data.hEndpointDisjoint

/-- The endpoint-touch embedding carries the current outer-boundary-rooted peeled route package,
but it cannot carry the stronger route package with raw endpoint separation. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_withEndpointSeparation_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
          peeledEndpointTouchEmbedding) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch⟩

/-- Summary certificate for the endpoint-touch obstruction at the strongest current route layer.
The same fixed embedding carries the present outer-boundary-rooted peeled annulus data and its
annulus-construction edge-disjointness, but the raw endpoint carrier is not endpoint-disjoint from
the selected boundary, the per-peeled-face and aggregate no-touch repairs fail, the stronger
endpoint-separation package is unavailable, and selected-boundary purification deletes the raw
carrier completely. -/
theorem peeledEndpointTouch_rawCarrierRepairObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
        (∀ f ∈ data.peelFaces,
          Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
          ¬ (∀ f ∈ data.peelFaces,
            Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) ∧
          ¬ data.peelFacesEndpointDisjointSelectedBoundarySupport) ∧
        ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
          ¬ Nonempty
            (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
              peeledEndpointTouchEmbedding) ∧
            selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  refine ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch, ?_, ?_, ?_, ?_⟩
  · exact ⟨peeledEndpointTouchAnnulusConstruction,
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
      peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch,
      not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction⟩
  · exact not_endpointSupport_disjoint_peeledEndpointTouch
  · exact not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch
  · exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- In the endpoint-touch obstruction model, the selected-boundary synthesis theorem still applies
to the current peeled annulus data, but it applies over the empty purified carrier.  This separates
the positive formal synthesis endpoint from any non-vacuous raw-carrier interpretation. -/
theorem peeledEndpointTouch_emptyCarrier_synthesis
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring peeledEndpointTouchGraph C₀) :
    Theorem49OuterBoundaryRootSynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
        C₀ ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ :=
  ⟨theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := peeledEndpointTouchGraph)
      peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData C₀ hC₀,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch⟩

/-- The same endpoint-touch model also carries the newer two-sided annulus-root package, obtained
by forgetting that all roots happen to lie on the outer boundary component. -/
noncomputable def peeledEndpointTouchAnnulusRootAdjDistancePeelData :
    PlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchEmbedding :=
  peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
    |>.toPlanarBoundaryAnnulusRootAdjDistancePeelData

theorem nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty
      (PlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchAnnulusRootAdjDistancePeelData⟩

/-- The newer two-sided annulus-rooted peeled data still does not force the raw endpoint-support
separation needed by the annulus-root non-vacuous repair theorem. -/
theorem annulusRootAdjDistancePeelData_does_not_imply_endpointSupport_disjoint_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    not_endpointSupport_disjoint_peeledEndpointTouch⟩

/-- On the endpoint-touch embedding, no theorem can derive raw endpoint-support separation from
arbitrary two-sided annulus-rooted peeled route data alone. -/
theorem not_forall_annulusRootAdjDistancePeelData_implies_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact not_endpointSupport_disjoint_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusRootAdjDistancePeelData)

/-- So the newer two-sided annulus-root synthesis theorem is subject to the same vacuity issue on
the endpoint-touch model: it holds positively, but only over the empty purified carrier. -/
theorem peeledEndpointTouch_emptyCarrier_annulusSynthesis
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring peeledEndpointTouchGraph C₀) :
    Theorem49AnnulusRootSynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchAnnulusRootAdjDistancePeelData
        C₀ ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ :=
  ⟨theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := peeledEndpointTouchGraph)
      peeledEndpointTouchAnnulusRootAdjDistancePeelData C₀ hC₀,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch⟩

/-- The raw interior-edge endpoint carrier is nonempty in the endpoint-touch model: vertex `1`
is an endpoint of the raw interior edge `pet12`. -/
theorem interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch :
    (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty :=
  ⟨1, vertex_one_mem_interiorEdgeEndpointSupport_peeledEndpointTouch⟩

/-- The purified selected-boundary interior-edge endpoint carrier is not nonempty in the
endpoint-touch model. -/
theorem not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch] at hv

/-- The endpoint-touch model refutes the non-vacuous selected-boundary synthesis surface: the
raw carrier is nonempty, but the purified carrier required by the synthesis endpoint is empty. -/
theorem not_theorem49OuterBoundaryRootNonemptySynthesis_peeledEndpointTouch
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color) :
    ¬ Theorem49OuterBoundaryRootNonemptySynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
        C₀ := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    h.carrier_nonempty

/-- The same purified-carrier obstruction also blocks the non-vacuous two-sided annulus-root
synthesis package. -/
theorem not_theorem49AnnulusRootNonemptySynthesis_peeledEndpointTouch
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color) :
    ¬ Theorem49AnnulusRootNonemptySynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchAnnulusRootAdjDistancePeelData
        C₀ := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    h.carrier_nonempty

/-- The current outer-boundary-rooted peeled data does not force a nonempty purified endpoint
carrier, even in a model where the raw interior-edge endpoint carrier is nonempty. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch⟩

/-- The same non-vacuity failure already appears on the newer two-sided annulus-root route
surface. -/
theorem
    annulusRootAdjDistancePeelData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch⟩

/-- Fixed-embedding universal obstruction: no theorem can derive nonemptiness of the purified
interior-edge endpoint carrier from arbitrary current peeled route data on this embedding. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty) := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

/-- The same fixed-embedding universal obstruction for the newer two-sided annulus-root route
surface. -/
theorem
    not_forall_annulusRootAdjDistancePeelData_implies_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty) := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusRootAdjDistancePeelData)

/-- Crux certificate for the non-vacuity failure of the purified Theorem 4.9 route surface.
The fixed endpoint-touch model admits the current peeled annulus data and has a nonempty raw
interior-edge endpoint carrier.  Nevertheless the purified carrier is empty, so every attempted
non-vacuous selected-boundary synthesis package is impossible, while the ordinary purified
synthesis still holds for any Tait coloring. -/
theorem peeledEndpointTouch_nonvacuousPurifiedSynthesisCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
          (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
            ¬ Theorem49OuterBoundaryRootNonemptySynthesis
                peeledEndpointTouchEmbedding
                peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
                C₀) ∧
            (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
              IsTaitEdgeColoring peeledEndpointTouchGraph C₀ →
                Theorem49OuterBoundaryRootSynthesis
                  peeledEndpointTouchEmbedding
                  peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
                  C₀) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    not_theorem49OuterBoundaryRootNonemptySynthesis_peeledEndpointTouch,
    fun C₀ hC₀ =>
      theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        (G := peeledEndpointTouchGraph)
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData C₀ hC₀⟩

/-- The same non-vacuity crux now blocks the newer two-sided annulus-root synthesis surface as
well. The route may have abandoned the all-outer-root requirement, but unless it also rules out
endpoint-touch purification collapse, the purified endpoint remains vacuous on this model. -/
theorem peeledEndpointTouch_annulusNonvacuousPurifiedSynthesisCruxObstructionSummary :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
          (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
            ¬ Theorem49AnnulusRootNonemptySynthesis
                peeledEndpointTouchEmbedding
                peeledEndpointTouchAnnulusRootAdjDistancePeelData
                C₀) ∧
            (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
              IsTaitEdgeColoring peeledEndpointTouchGraph C₀ →
                Theorem49AnnulusRootSynthesis
                  peeledEndpointTouchEmbedding
                  peeledEndpointTouchAnnulusRootAdjDistancePeelData
                  C₀) :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    not_theorem49AnnulusRootNonemptySynthesis_peeledEndpointTouch,
    fun C₀ hC₀ =>
      theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
        (G := peeledEndpointTouchGraph)
        peeledEndpointTouchAnnulusRootAdjDistancePeelData C₀ hC₀⟩

/-- Broader carrier crux certificate: in the endpoint-touch model, selected-boundary
purification empties not only the face-incidence interior-edge endpoint carrier, but every finite
candidate carrier contained in the graph-edge endpoint support.  Thus the route cannot repair the
non-vacuity problem by switching to the canonical all-graph-endpoint carrier or to any of its
subcarriers. -/
theorem peeledEndpointTouch_graphEndpointSubcarrierCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        (graphEdgeEndpointSupport peeledEndpointTouchGraph).Nonempty ∧
          selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
            selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding = ∅ ∧
              ∀ vertices : Finset (Fin 4),
                vertices ⊆ graphEdgeEndpointSupport peeledEndpointTouchGraph →
                  selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    graphEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch,
    selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch⟩

/-- Strongest carrier-level crux certificate for the endpoint-touch model.  The selected-boundary
endpoint support already covers every vertex of the graph, while the graph-edge endpoint support
is also all vertices.  Hence every finite candidate carrier on this vertex type purifies to the
empty set.  A non-vacuous repair cannot be obtained by changing the finite carrier inside this
model; it must add a genuinely stronger geometric hypothesis excluding this model or change the
strategy. -/
theorem peeledEndpointTouch_arbitraryCarrierCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        graphEdgeEndpointSupport peeledEndpointTouchGraph = Finset.univ ∧
          edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) =
            Finset.univ ∧
            ∀ vertices : Finset (Fin 4),
              selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch,
    selectedBoundaryEndpointSupport_eq_univ_peeledEndpointTouch,
    selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch⟩

/-- The peeled endpoint-touch graph is acyclic, so no embedding of it can carry honest
facial closed-walk geometry. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph
    {emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph} :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData peeledEndpointTouchEmbedding) := by
  exact not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph

theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData peeledEndpointTouchGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

/-- The endpoint-touch graph cannot satisfy the honest closed-walk annulus-boundary source:
that source already contains a facial closed-walk witness. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

theorem admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_interiorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouch⟩

theorem admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch⟩

theorem admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch⟩

/-- The endpoint-touch embedding already reaches the direct boundary height-ordered witness-cover
surface through the same annulus-root interior-dual data. So the endpoint-touch collapse is not
merely a well-founded-parent or certificate-endpoint artifact. -/
noncomputable def peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData :
    PlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchEmbedding :=
  planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

/-- The purified selected-boundary carrier is still empty on the endpoint-touch height-ordered
witness-cover model, because the witness data lives on the same embedding. -/
theorem peeledEndpointTouch_heightOrderedWitnessData_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- Even the direct boundary height-ordered witness-cover surface does not force a nonempty
purified selected-boundary carrier on the endpoint-touch model. -/
theorem
    planarBoundaryHeightOrderedFacePeelWitnessData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        (interiorEdgeEndpointSupport emb).Nonempty ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  refine ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData⟩, ?_, ?_⟩
  · exact interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct boundary height-ordered witness-cover lane: the endpoint-touch
graph already admits this earlier witness-cover endpoint, the raw interior-edge endpoint carrier is
nonempty, but the purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_heightOrderedWitnessCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact ⟨admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    peeledEndpointTouch_heightOrderedWitnessData_emptyCarrier⟩

/-- The endpoint-touch embedding already reaches the earlier well-founded witness-cover surface
through the same annulus-root interior-dual data. So the endpoint-touch collapse is not merely a
certificate-endpoint artifact. -/
noncomputable def peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData :
    PlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchEmbedding :=
  planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData.toInteriorDualWellFoundedParentPeelData

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData⟩⟩

/-- The purified selected-boundary carrier is still empty on the endpoint-touch witness-cover
model, because the witness data lives on the same embedding. -/
theorem peeledEndpointTouch_wellFoundedWitnessData_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- Even the earlier well-founded witness-cover surface does not force a nonempty purified
selected-boundary carrier on the endpoint-touch model. -/
theorem
    planarBoundaryWellFoundedFacePeelWitnessData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph,
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
        (interiorEdgeEndpointSupport emb).Nonempty ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  refine ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData⟩, ?_, ?_⟩
  · exact interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct well-founded witness-cover lane: the endpoint-touch graph already
admits the witness-cover endpoint, the raw interior-edge endpoint carrier is nonempty, but the
purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_wellFoundedWitnessCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact ⟨admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    peeledEndpointTouch_wellFoundedWitnessData_emptyCarrier⟩

/-- The same endpoint-touch embedding already reaches the graph-level attached-certificate
surface through its annulus-root interior-dual data. This shows the certificate endpoint itself
does not rule out the endpoint-touch collapse. -/
noncomputable def peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate :
    PlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph :=
  planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
    peeledEndpointTouchEmbedding peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData

theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate⟩

/-- The attached-certificate endpoint is still vacuous on the endpoint-touch model: its ambient
embedding is exactly the same one whose purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_attachedCertificate_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices
        peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding = ∅ := by
  simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- So the graph-level attached-certificate surface also fails to force a nonempty purified
selected-boundary carrier, even when the raw interior-edge endpoint carrier is nonempty. -/
theorem
    planarBoundaryAttachedRootedFacePeelCertificate_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph,
      (interiorEdgeEndpointSupport data.embedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices data.embedding).Nonempty := by
  refine ⟨peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate, ?_, ?_⟩
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct attached-certificate lane: the endpoint-touch graph already admits
the graph-level certificate endpoint, the raw interior-edge endpoint carrier is nonempty, but the
certificate's own purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_attachedCertificateCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport
          peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices
            peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding = ∅ := by
  refine ⟨admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph, ?_, ?_⟩
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact peeledEndpointTouch_attachedCertificate_emptyCarrier

/-- Calibration theorem for the current route layers: the endpoint-touch graph still carries the
current outer-boundary-rooted peeled annulus data, but it cannot carry the stronger honest
closed-walk annulus-boundary source. So the former does not imply the latter. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- Calibration theorem for the current route layers: the endpoint-touch graph still carries the
current outer-boundary-rooted peeled annulus data, but it cannot carry the stronger honest
closed-walk annulus-boundary source. So the former does not imply the latter. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration for the newer two-sided annulus-root route surface. The endpoint-touch
graph already carries annulus-root adjacency-distance data, but still cannot carry the honest
closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the direct boundary height-ordered witness-cover surface. The
endpoint-touch graph already reaches this earlier planarity-side witness endpoint, but still cannot
carry the honest closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the earlier well-founded witness-cover surface. The endpoint-touch
graph already reaches this planarity-side witness endpoint, but still cannot carry the honest
closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the direct graph-level attached-certificate surface. The endpoint-
touch graph already reaches the certificate endpoint, but still cannot carry the honest closed-
walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

end Theorem49InteriorVerticesEndpointObstruction

end Mettapedia.GraphTheory.FourColor
