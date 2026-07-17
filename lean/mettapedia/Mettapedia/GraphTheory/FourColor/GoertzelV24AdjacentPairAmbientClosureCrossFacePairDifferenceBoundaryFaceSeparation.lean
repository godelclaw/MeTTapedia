import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairRotationPortFaceCut

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

local instance ambientClosureBoundaryFaceSeparationGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The exterior first-vertex wedge is represented by the retained-side
dart at rotation port `0`. -/
def rotationFirstExteriorOrbitFace
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    OrbitFace graphData.toRotationSystem :=
  dartOrbitFace graphData.toRotationSystem
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 0)

/-- The exterior second-vertex wedge is represented by the retained-side
dart at rotation port `2`. -/
def rotationSecondExteriorOrbitFace
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    OrbitFace graphData.toRotationSystem :=
  dartOrbitFace graphData.toRotationSystem
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 2)

/-- A face agrees with exactly one of the two rotation exterior faces. -/
def FaceMatchesExactlyOneRotationExterior
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem) : Prop :=
  Xor (face = data.rotationFirstExteriorOrbitFace graphData hcubic hrotation)
    (face = data.rotationSecondExteriorOrbitFace graphData hcubic hrotation)

/-- The complementary aligned signature: a face agrees with both rotation
exterior faces or with neither. -/
def FaceMatchesBothOrNeitherRotationExterior
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem) : Prop :=
  (face = data.rotationFirstExteriorOrbitFace graphData hcubic hrotation ∧
      face = data.rotationSecondExteriorOrbitFace graphData hcubic hrotation) ∨
    (face ≠ data.rotationFirstExteriorOrbitFace graphData hcubic hrotation ∧
      face ≠ data.rotationSecondExteriorOrbitFace graphData hcubic hrotation)

/-- One face step from retained rotation port `0` reaches the opposite dart
of retained rotation port `1`, traversing the exterior first-vertex wedge. -/
theorem rotationOrdered_boundaryPortDart_zero_phi_eq_alpha_one
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    graphData.toRotationSystem.phi
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 0) =
      graphData.toRotationSystem.alpha
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 1) := by
  rw [data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
      graphData hcubic hrotation,
    data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
      graphData hcubic hrotation]
  simp only [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  rfl

/-- The analogous exterior face step at the second restored vertex runs
from retained rotation port `2` to the opposite dart at port `3`. -/
theorem rotationOrdered_boundaryPortDart_two_phi_eq_alpha_three
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    graphData.toRotationSystem.phi
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 2) =
      graphData.toRotationSystem.alpha
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 3) := by
  rw [data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
      graphData hcubic hrotation,
    data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
      graphData hcubic hrotation]
  simp only [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  rfl

/-- The first exterior face can equivalently be represented by the dart
opposite retained rotation port `1`. -/
theorem rotationFirstExteriorOrbitFace_eq_alpha_boundaryPortDart_one
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    data.rotationFirstExteriorOrbitFace graphData hcubic hrotation =
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
            (data.rotationOrderedData graphData hcubic hrotation) 1)) := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 0
  change dartOrbitFace graphData.toRotationSystem boundary = _
  calc
    dartOrbitFace graphData.toRotationSystem boundary =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.phi boundary) :=
      (dartOrbitFace_phi_eq graphData.toRotationSystem boundary).symm
    _ = dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 1)) :=
      congrArg (dartOrbitFace graphData.toRotationSystem)
        (data.rotationOrdered_boundaryPortDart_zero_phi_eq_alpha_one
          graphData hcubic hrotation)

/-- The second exterior face is likewise the face of the dart opposite
retained rotation port `3`. -/
theorem rotationSecondExteriorOrbitFace_eq_alpha_boundaryPortDart_three
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    data.rotationSecondExteriorOrbitFace graphData hcubic hrotation =
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
            (data.rotationOrderedData graphData hcubic hrotation) 3)) := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 2
  change dartOrbitFace graphData.toRotationSystem boundary = _
  calc
    dartOrbitFace graphData.toRotationSystem boundary =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.phi boundary) :=
      (dartOrbitFace_phi_eq graphData.toRotationSystem boundary).symm
    _ = dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 3)) :=
      congrArg (dartOrbitFace graphData.toRotationSystem)
        (data.rotationOrdered_boundaryPortDart_two_phi_eq_alpha_three
          graphData hcubic hrotation)

/-- The rotation central dart represents the restored central edge. -/
theorem rotationCentralDart_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    graphData.toRotationSystem.edgeOf data.rotationCentralDart =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdge
        (data.rotationOrderedData graphData hcubic hrotation) := by
  apply Subtype.ext
  rfl

/-- A retained-side boundary dart represents its indexed restored edge. -/
theorem rotationOrdered_boundaryPortDart_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    graphData.toRotationSystem.edgeOf
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) port) =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
        (data.rotationOrderedData graphData hcubic hrotation) port := by
  apply Subtype.ext
  exact GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart_edge
    (data.rotationOrderedData graphData hcubic hrotation) port

/-- Rotation boundary edge `1` lies on the first exterior face. -/
theorem boundary_one_mem_rotationFirstExteriorOrbitFace
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
        (data.rotationOrderedData graphData hcubic hrotation) 1 ∈
      orbitFaceBoundary graphData.toRotationSystem
        (data.rotationFirstExteriorOrbitFace graphData hcubic hrotation) := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 1
  rw [data.rotationFirstExteriorOrbitFace_eq_alpha_boundaryPortDart_one
    graphData hcubic hrotation]
  rw [← data.rotationOrdered_boundaryPortDart_edgeOf graphData
      hcubic hrotation 1,
    ← graphData.toRotationSystem.edge_alpha boundary]
  exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
    graphData.toRotationSystem (graphData.toRotationSystem.alpha boundary)

/-- Rotation boundary edge `3` lies on the second exterior face. -/
theorem boundary_three_mem_rotationSecondExteriorOrbitFace
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
        (data.rotationOrderedData graphData hcubic hrotation) 3 ∈
      orbitFaceBoundary graphData.toRotationSystem
        (data.rotationSecondExteriorOrbitFace graphData hcubic hrotation) := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 3
  rw [data.rotationSecondExteriorOrbitFace_eq_alpha_boundaryPortDart_three
    graphData hcubic hrotation]
  rw [← data.rotationOrdered_boundaryPortDart_edgeOf graphData
      hcubic hrotation 3,
    ← graphData.toRotationSystem.edge_alpha boundary]
  exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
    graphData.toRotationSystem (graphData.toRotationSystem.alpha boundary)

/-- A face incident to rotation boundary edge `1` but not to the central
edge is necessarily the first exterior face. -/
theorem face_eq_rotationFirstExteriorOrbitFace_of_boundary_one_of_not_central
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
          (data.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) 1 ∈
        orbitFaceBoundary graphData.toRotationSystem face)
    (hcentral :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdge
          (data.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) ∉
        orbitFaceBoundary graphData.toRotationSystem face) :
    face = data.rotationFirstExteriorOrbitFace graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      ordered 1
  have hedge : graphData.toRotationSystem.edgeOf boundary =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
        ordered 1 := by
    exact data.rotationOrdered_boundaryPortDart_edgeOf graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 1
  have hfaces : face ∈
      ({dartOrbitFace graphData.toRotationSystem boundary,
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha boundary)} :
        Finset (OrbitFace graphData.toRotationSystem)) := by
    rw [← orbitFace_incidentFaces_eq_dartSide_pair
      graphData.toRotationSystem minimal.facesTwoSided boundary]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hedge]
    exact hboundary
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfaces
  rcases hfaces with hcentralFace | hexteriorFace
  · exfalso
    apply hcentral
    rw [hcentralFace,
      data.rotationOrdered_boundaryPortDart_one_face_eq_rotationCentralDart
        graphData minimal.spherical.cubic minimal.vertexRotationCyclic,
      ← data.rotationCentralDart_edgeOf graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      graphData.toRotationSystem data.rotationCentralDart
  · rw [data.rotationFirstExteriorOrbitFace_eq_alpha_boundaryPortDart_one
      graphData minimal.spherical.cubic minimal.vertexRotationCyclic]
    exact hexteriorFace

/-- The symmetric classification at rotation boundary edge `3` identifies
the second exterior face. -/
theorem face_eq_rotationSecondExteriorOrbitFace_of_boundary_three_of_not_central
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
          (data.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) 3 ∈
        orbitFaceBoundary graphData.toRotationSystem face)
    (hcentral :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdge
          (data.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) ∉
        orbitFaceBoundary graphData.toRotationSystem face) :
    face = data.rotationSecondExteriorOrbitFace graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      ordered 3
  have hedge : graphData.toRotationSystem.edgeOf boundary =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge
        ordered 3 := by
    exact data.rotationOrdered_boundaryPortDart_edgeOf graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic 3
  have hfaces : face ∈
      ({dartOrbitFace graphData.toRotationSystem boundary,
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha boundary)} :
        Finset (OrbitFace graphData.toRotationSystem)) := by
    rw [← orbitFace_incidentFaces_eq_dartSide_pair
      graphData.toRotationSystem minimal.facesTwoSided boundary]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hedge]
    exact hboundary
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfaces
  rcases hfaces with hcentralFace | hexteriorFace
  · exfalso
    apply hcentral
    rw [hcentralFace,
      data.rotationOrdered_boundaryPortDart_three_face_eq_alpha_rotationCentralDart
        graphData minimal.spherical.cubic minimal.vertexRotationCyclic,
      ← data.rotationCentralDart_edgeOf graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic,
      ← graphData.toRotationSystem.edge_alpha data.rotationCentralDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      graphData.toRotationSystem
        (graphData.toRotationSystem.alpha data.rotationCentralDart)
  · rw [data.rotationSecondExteriorOrbitFace_eq_alpha_boundaryPortDart_three
      graphData minimal.spherical.cubic minimal.vertexRotationCyclic]
    exact hexteriorFace

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- For rotation-ordered ports, the selected singleton face is the first
exterior face exactly when it takes the first exterior turn. -/
theorem CrossCentralExactFaceCutPair.selectedFace_eq_rotationFirstExteriorOrbitFace_iff
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (firstIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex) :
    edgeCrossFaceCoordinateOrbitFace graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cross) coordinate =
      baseData.rotationFirstExteriorOrbitFace graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic ↔
      pair.CrossFaceUsesFirstExteriorTurn coordinate := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let face := edgeCrossFaceCoordinateOrbitFace graphData
    (retainedEdgeToAmbientEdge ordered cross) coordinate
  have hnotCentralPair : face ∉ edgeOrbitFacePair graphData
      (centralEdge ordered) :=
    pair.selectedFace_not_mem_centralFacePair minimal coordinate hcentral
  have hnotCentral : centralEdge ordered ∉
      orbitFaceBoundary graphData.toRotationSystem face := by
    intro hmem
    exact hnotCentralPair
      ((mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
        graphData minimal face (centralEdge ordered)).2 hmem)
  constructor
  · intro hface
    have hface' : face =
        baseData.rotationFirstExteriorOrbitFace graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic := hface
    apply (pair.boundaryEdge_mem_selectedFaceBoundary_iff_firstExteriorTurn
      minimal coordinate firstIndex hfirstExact 1).1
    change boundaryEdge ordered (firstSidePort 1) ∈
      orbitFaceBoundary graphData.toRotationSystem face
    rw [firstSidePort_one, hface']
    exact baseData.boundary_one_mem_rotationFirstExteriorOrbitFace
      graphData minimal.spherical.cubic minimal.vertexRotationCyclic
  · intro hturn
    apply baseData.face_eq_rotationFirstExteriorOrbitFace_of_boundary_one_of_not_central
      graphData minimal face
    · change boundaryEdge ordered 1 ∈
        orbitFaceBoundary graphData.toRotationSystem face
      simpa only [firstSidePort_one] using
        (pair.boundaryEdge_mem_selectedFaceBoundary_iff_firstExteriorTurn
          minimal coordinate firstIndex hfirstExact 1).2 hturn
    · exact hnotCentral

/-- The second exterior-turn proposition analogously identifies the second
rotation exterior face. -/
theorem CrossCentralExactFaceCutPair.selectedFace_eq_rotationSecondExteriorOrbitFace_iff
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (secondIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    edgeCrossFaceCoordinateOrbitFace graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cross) coordinate =
      baseData.rotationSecondExteriorOrbitFace graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic ↔
      pair.CrossFaceUsesSecondExteriorTurn coordinate := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let face := edgeCrossFaceCoordinateOrbitFace graphData
    (retainedEdgeToAmbientEdge ordered cross) coordinate
  have hnotCentralPair : face ∉ edgeOrbitFacePair graphData
      (centralEdge ordered) :=
    pair.selectedFace_not_mem_centralFacePair minimal coordinate hcentral
  have hnotCentral : centralEdge ordered ∉
      orbitFaceBoundary graphData.toRotationSystem face := by
    intro hmem
    exact hnotCentralPair
      ((mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
        graphData minimal face (centralEdge ordered)).2 hmem)
  constructor
  · intro hface
    have hface' : face =
        baseData.rotationSecondExteriorOrbitFace graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic := hface
    apply (pair.boundaryEdge_mem_selectedFaceBoundary_iff_secondExteriorTurn
      minimal coordinate secondIndex hsecondExact 1).1
    change boundaryEdge ordered (secondSidePort 1) ∈
      orbitFaceBoundary graphData.toRotationSystem face
    rw [secondSidePort_one, hface']
    exact baseData.boundary_three_mem_rotationSecondExteriorOrbitFace
      graphData minimal.spherical.cubic minimal.vertexRotationCyclic
  · intro hturn
    apply baseData.face_eq_rotationSecondExteriorOrbitFace_of_boundary_three_of_not_central
      graphData minimal face
    · change boundaryEdge ordered 3 ∈
        orbitFaceBoundary graphData.toRotationSystem face
      simpa only [secondSidePort_one] using
        (pair.boundaryEdge_mem_selectedFaceBoundary_iff_secondExteriorTurn
          minimal coordinate secondIndex hsecondExact 1).2 hturn
    · exact hnotCentral

/-- In rotation order, trivial compensated transfer means that the selected
cross face is exactly one of the two exterior faces. -/
theorem CrossCentralExactFaceCutPair.closedTransfer_eq_refl_iff_selectedFace_eq_exactlyOneRotationExterior
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
          Equiv.refl (Bool × Bool) ↔
      Xor
        (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) cross) coordinate =
          baseData.rotationFirstExteriorOrbitFace graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic)
        (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) cross) coordinate =
          baseData.rotationSecondExteriorOrbitFace graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic) := by
  calc
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
          Equiv.refl (Bool × Bool) ↔
        firstIndex ≠ secondIndex :=
      rejectedCrossCentralReturnClosedTransfer_eq_refl_iff
        firstIndex secondIndex
    _ ↔ Xor (pair.CrossFaceUsesFirstExteriorTurn coordinate)
          (pair.CrossFaceUsesSecondExteriorTurn coordinate) :=
      pair.mixedChannel_iff_crossFaceUsesExactlyOneExteriorTurn minimal
        coordinate firstIndex secondIndex hfirstExact hsecondExact
    _ ↔ Xor
          (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate =
            baseData.rotationFirstExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
          (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate =
            baseData.rotationSecondExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) := by
      rw [pair.selectedFace_eq_rotationFirstExteriorOrbitFace_iff
          minimal baseData coordinate firstIndex hcentral hfirstExact,
        pair.selectedFace_eq_rotationSecondExteriorOrbitFace_iff
          minimal baseData coordinate secondIndex hcentral hsecondExact]

/-- Nontrivial compensated transfer has the complementary geometric normal
form: the selected face is both exterior faces or neither exterior face. -/
theorem CrossCentralExactFaceCutPair.closedTransfer_ne_refl_iff_selectedFace_eq_both_or_neitherRotationExterior
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (centralEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic))) ≠ 0)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)
                (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
          Equiv.refl (Bool × Bool) ↔
      ((edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate =
            baseData.rotationFirstExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) ∧
        (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate =
            baseData.rotationSecondExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)) ∨
      ((edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate ≠
            baseData.rotationFirstExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) ∧
        (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate ≠
            baseData.rotationSecondExteriorOrbitFace graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic)) := by
  let face := edgeCrossFaceCoordinateOrbitFace graphData
    (retainedEdgeToAmbientEdge
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) coordinate
  let firstFace := baseData.rotationFirstExteriorOrbitFace graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let secondFace := baseData.rotationSecondExteriorOrbitFace graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hcriterion :=
    pair.closedTransfer_eq_refl_iff_selectedFace_eq_exactlyOneRotationExterior
      minimal baseData coordinate firstIndex secondIndex hcentral
        hfirstExact hsecondExact
  constructor
  · intro hnontrivial
    by_cases hfirst : face = firstFace
    · by_cases hsecond : face = secondFace
      · exact Or.inl ⟨hfirst, hsecond⟩
      · exact False.elim (hnontrivial
          (hcriterion.2 (Or.inl ⟨hfirst, hsecond⟩)))
    · by_cases hsecond : face = secondFace
      · exact False.elim (hnontrivial
          (hcriterion.2 (Or.inr ⟨hsecond, hfirst⟩)))
      · exact Or.inr ⟨hfirst, hsecond⟩
  · intro haligned htrivial
    have hexactlyOne := hcriterion.1 htrivial
    rcases haligned with hboth | hneither
    · rcases hexactlyOne with hfirstOnly | hsecondOnly
      · exact hfirstOnly.2 hboth.2
      · exact hsecondOnly.2 hboth.1
    · rcases hexactlyOne with hfirstOnly | hsecondOnly
      · exact hneither.1 hfirstOnly.1
      · exact hneither.2 hsecondOnly.1

/-- Every exact cross-central pair in rotation order supplies a selected
cross face with a complete exterior-face monodromy normal form. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_rotationExteriorNormalForm
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G baseData.firstVertex
          baseData.secondVertex).Walk
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (firstSidePort firstIndex))
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet baseData.firstVertex
          baseData.secondVertex)) ∉ path.edges ∧
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).crossSidePortClosure
            firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic) cross ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        centralEdge (baseData.rotationOrderedData graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
              Equiv.refl (Bool × Bool) ↔
          baseData.FaceMatchesExactlyOneRotationExterior graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic
              (edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge
                  (baseData.rotationOrderedData graphData
                    minimal.spherical.cubic minimal.vertexRotationCyclic)
                      cross) coordinate)) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
              Equiv.refl (Bool × Bool) ↔
          baseData.FaceMatchesBothOrNeitherRotationExterior graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic
              (edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge
                  (baseData.rotationOrderedData graphData
                    minimal.spherical.cubic minimal.vertexRotationCyclic)
                      cross) coordinate)) := by
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceBoundarySupport
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, hcycle, hparity,
      hsource, hnotCentral, _hboundaryCriterion⟩
  have hidentity :=
    pair.closedTransfer_eq_refl_iff_selectedFace_eq_exactlyOneRotationExterior
      minimal baseData coordinate firstIndex secondIndex hcentral
        hfirstExact hsecondExact
  have hnonidentity :=
    pair.closedTransfer_ne_refl_iff_selectedFace_eq_both_or_neitherRotationExterior
      minimal baseData coordinate firstIndex secondIndex hcentral
        hfirstExact hsecondExact
  exact ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral,
    by simpa only [FaceMatchesExactlyOneRotationExterior] using hidentity,
    by simpa only [FaceMatchesBothOrNeitherRotationExterior] using
      hnonidentity⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
