import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisPeelBridge

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Outer-boundary-root presentation of the common synthesis package. The outer-root data is an
input theorem surface, but the synthesized consequences depend only on the embedding and the Tait
coloring. -/
abbrev Theorem49OuterBoundaryRootSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootSynthesis emb C₀

/-- Two-sided annulus-root presentation of the same synthesis package. This is the direct
ground-up synthesis surface for the annulus-root replacement route. -/
abbrev Theorem49AnnulusRootSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootSynthesis emb C₀


/-- The weakest current boundary-aware well-founded peel witness surface already reaches the full
Theorem 4.9 synthesis package, via the attached rooted certificate it canonically induces. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    (G := G) data.toPlanarBoundaryAttachedRootedFacePeelCertificate C₀ hC₀

/-- The weakest explicit-remainder annulus peel surface already induces the boundary-aware
attached rooted certificate on the same embedding. This keeps the synthesis boundary at the
earliest current annulus layer that still carries explicit later-witness remainder geometry. -/
noncomputable def
    PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  let cert :
      BoundaryRootedFacePeelCertificate emb.faces.attach
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
      (data := data)
  exact
    { embedding := emb
      certificate := cert }

/-- The split annulus decomposition plus witness-assignment surface already induces the
boundary-aware attached rooted certificate, via the canonical local explicit-remainder collar
package it determines. -/
noncomputable def PlanarBoundaryAnnulusWitnessAssignment.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G :=
  Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    (data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData)

/-- The weakest explicit-remainder annulus peel surface already reaches the full current
Theorem 4.9 synthesis package. Once this local remainder geometry exists, no further theorem-4.9
algebra remains. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate] using
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G)
      (Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
        data)
      C₀ hC₀

/-- The split annulus decomposition plus witness-assignment surface already reaches the full
current Theorem 4.9 synthesis package. This is the earliest current point where the remaining
burden is purely geometric ownership of witness edges on a fixed annulus decomposition. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (G := G) data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData C₀ hC₀

/-- Even the weaker annulus collar geometry surface already reaches the full current Theorem 4.9
synthesis package. The remaining burden is purely geometric: once the collar-layer witness data
exists, the attached boundary-rooted certificate and all downstream algebra are automatic. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    (G := G) data.toPlanarBoundaryAttachedRootedFacePeelCertificate C₀ hC₀

/-- The repaired previous-boundary witness geometry surface also reaches the full synthesis
package, but this is now just a specialization of the weaker collar-geometry route. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
    (G := G) data.toPlanarBoundaryAnnulusCollarGeometry C₀ hC₀

/-- Construct the route-level synthesis package from generic boundary-root interior-dual data.
This is the ground-up core behind both the outer-boundary-rooted and the new two-sided annulus-
rooted Theorem 4.9 synthesis surfaces. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := emb) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀)

/-- Construct the route-level synthesis package from the canonical parent form of generic
boundary-root interior-dual data. This exposes the acyclic-parent sufficiency branch at the same
Theorem 4.9 synthesis layer as the older adjacency-distance package. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData]
    using
      theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
        (G := G)
        (planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData
          emb data)
        C₀ hC₀

/-- Construct the outer-boundary-root synthesis package from concrete outer-boundary-rooted
annulus data. -/
theorem theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49OuterBoundaryRootSynthesis emb data C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀

/-- Construct the two-sided annulus-root synthesis package directly from annulus-root data. -/
theorem theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49AnnulusRootSynthesis emb data C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀

/-- Construct the route-level synthesis package directly from the two-sided annulus-root parent
package.  The annulus boundary split is additional route structure, but the proved algebraic
endpoint still depends only on the embedded parent payload. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    (G := G) data.interiorData C₀ hC₀

/-- Same-embedding synthesis constructor from an explicit annulus boundary split and the generic
boundary-root interior-dual adjacency-distance data. This is the primitive two-sided annulus
entry point before packaging the full annulus-root route object. -/
theorem
    theorem49AnnulusRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49AnnulusRootSynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData interiorData)
        C₀ :=
  theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    (G := G)
    (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData)
    C₀ hC₀

/-- Same-embedding synthesis constructor from an explicit annulus boundary split and the generic
boundary-root interior-dual parent data. This is the primitive two-sided annulus entry point for
the acyclic-parent sufficiency branch. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData)
    C₀ hC₀

/-- Closed-walk source constructor for the acyclic-parent sufficiency branch at the proved
Theorem 4.9 synthesis endpoint. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData)
    C₀ hC₀

/-- Direct synthesis constructor from annulus-construction data plus the explicit parent-witness
orientation hypothesis. This bypasses the older interior-dual boundary-root packaging and uses the
construction-side annihilator route directly on the selected-boundary purified endpoint carrier. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := emb) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀)

/-- Graph-level synthesis theorem for the attached rooted face-peel certificate route. Once any
graph reaches this certificate surface, the remaining Theorem 4.9 algebra is automatic. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨data⟩
  exact ⟨data.embedding,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the boundary-aware height-ordered witness-cover surface.
This shows the current theorem-4.9 endpoint already starts at the height-sorted annulus peeling
interface. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the finite collar-layer witness-cover surface. This moves
the theorem-4.9 boundary earlier than any explicit annulus-remainder package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the weakest current boundary-aware well-founded peel
witness surface. This packages the canonical certificate conversion before invoking the generic
synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryWellFoundedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the weakest local explicit-remainder annulus peel surface.
Once a graph reaches this annulus-side remainder geometry, theorem-4.9 synthesis is automatic. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the split annulus decomposition plus witness-assignment
surface. This isolates the remaining theorem-4.9 burden at the current pure annulus geometry plus
witness-ownership layer. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusWitnessAssignment G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _decomp, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the collar-geometry route. This packages the fact that the
weaker annulus collar witness data already contains enough structure to induce the boundary-aware
certificate surface. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusCollarGeometry
      hG)
    C₀ hC₀

/-- Graph-level synthesis theorem for the corrected previous-boundary witness geometry surface.
This now factors through the weaker collar-geometry route because the synthesis burden itself no
longer depends on the previous-boundary witness placement refinement. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusCollarGeometry
    (admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
      hG)
    C₀ hC₀

/-- Synthesis theorem for the repaired collar-geometry surface stated directly with the explicit
current-boundary witness placement witness. This isolates the live geometric content without
restating certificate or well-founded-peeling intermediates. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
      hG)
    C₀ hC₀

/-- The annulus-construction parent-witness orientation surface already reaches the boundary-aware
attached certificate endpoint via the canonical well-founded peel witness. -/
theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
      (admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
        hG)

/-- Graph-level synthesis theorem for the construction-side parent-witness annulus route. This is
the current ground-up entry point from explicit annulus-construction geometry into the full
Theorem 4.9 synthesis package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      hG)
    C₀ hC₀

/-- Graph-level ground-up synthesis theorem for the generic boundary-root interior-dual route. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level ground-up synthesis theorem for the canonical-parent boundary-root interior-dual
route. This is the end-to-end synthesis endpoint for source arguments that construct an acyclic
parent witness instead of an adjacency-distance package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the current outer-boundary-rooted Theorem 4.9 route. -/
theorem exists_theorem49OuterBoundaryRootSynthesis_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Theorem49OuterBoundaryRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the two-sided annulus-root Theorem 4.9 route. -/
theorem exists_theorem49AnnulusRootSynthesis_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the two-sided annulus-root parent route.  This packages the
annulus-side boundary split together with the acyclic-parent payload before invoking the generic
Theorem 4.9 endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusRootParentPeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem from an explicit annulus boundary split plus generic
boundary-root interior-dual data on the same embedding. This exposes the theorem-4.9 endpoint
at the primitive two-sided annulus-split layer, before any stronger closed-walk source fields are
introduced. -/
theorem
    exists_theorem49AnnulusRootSynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  exact ⟨emb, data,
    theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem from an explicit annulus boundary split plus generic
boundary-root parent data on the same embedding. This is the primitive two-sided annulus-split
entry point for the parent-oriented theorem-4.9 route. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      (G := G) boundaryData interiorData C₀ hC₀⟩


end Mettapedia.GraphTheory.FourColor
