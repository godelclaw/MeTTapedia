import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureTerminalCoefficientDegeneracy

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem f2_eq_zero_of_ne_one (value : F2) (hne : value ≠ 1) :
    value = 0 := by
  fin_cases value
  · rfl
  · exact False.elim (hne rfl)

namespace GoertzelV24MinimalFaceIntersections

local instance independentFaceGeneratorGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The binary label supported on one quotient face. -/
def singletonOrbitFaceLabels
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (face : OrbitFace RS) :
    OrbitFace RS → F2 :=
  fun other => if other = face then 1 else 0

@[simp]
theorem singletonOrbitFaceLabels_self
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (face : OrbitFace RS) :
    singletonOrbitFaceLabels face face = 1 := by
  simp [singletonOrbitFaceLabels]

@[simp]
theorem singletonOrbitFaceLabels_eq_zero
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} {face other : OrbitFace RS}
    (hne : other ≠ face) :
    singletonOrbitFaceLabels face other = 0 := by
  simp [singletonOrbitFaceLabels, hne]

/-- A singleton facial boundary crosses exactly the edges incident to its
chosen quotient face. -/
theorem orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem) (edge : G.edgeSet) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (singletonOrbitFaceLabels face) edge = 1 ↔
      face ∈ edgeOrbitFacePair graphData edge := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  have hboundary :
      orbitFaceBoundaryLinearMap RS (singletonOrbitFaceLabels face) edge =
        singletonOrbitFaceLabels face (dartOrbitFace RS dart) +
          singletonOrbitFaceLabels face
            (dartOrbitFace RS (RS.alpha dart)) := by
    rw [← hedge,
      orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided]
  rw [hboundary]
  simp only [singletonOrbitFaceLabels, edgeOrbitFacePair, RS, dart,
    Finset.mem_insert, Finset.mem_singleton]
  have hfaces : dartOrbitFace RS dart ≠
      dartOrbitFace RS (RS.alpha dart) := htwoSided dart
  change
    ((if dartOrbitFace RS dart = face then 1 else 0) +
          (if dartOrbitFace RS (RS.alpha dart) = face then 1 else 0) = 1) ↔
      face = dartOrbitFace RS dart ∨
        face = dartOrbitFace RS (RS.alpha dart)
  by_cases hleft : dartOrbitFace RS dart = face
  · have hright : dartOrbitFace RS (RS.alpha dart) ≠ face := by
      intro hright
      exact hfaces (hleft.trans hright.symm)
    simp [hleft, hright]
  · by_cases hright : dartOrbitFace RS (RS.alpha dart) = face
    · simp [hleft, hright]
    · simp [hleft, hright, Ne.symm hleft, Ne.symm hright]

/-- Every actual edge has exactly two incident quotient faces in a
two-sided rotation map. -/
theorem card_edgeOrbitFacePair_eq_two
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (edge : G.edgeSet) :
    (edgeOrbitFacePair graphData edge).card = 2 := by
  apply Finset.card_eq_two.mpr
  exact ⟨dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.dartRepresentative edge),
    dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.alpha
        (graphData.toRotationSystem.dartRepresentative edge)),
    htwoSided (graphData.toRotationSystem.dartRepresentative edge), rfl⟩

/-- Distinct edges of a graph-backed minimal map have a quotient face
incident to the first edge and not to the second. Its singleton boundary is
therefore `1` on the first edge and `0` on the second. -/
theorem exists_singletonOrbitFaceLabels_separating_distinct_edges
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : G.edgeSet} (hne : first ≠ second) :
    ∃ face : OrbitFace graphData.toRotationSystem,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels face) first = 1 ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels face) second = 0 := by
  have hpairs : edgeOrbitFacePair graphData first ≠
      edgeOrbitFacePair graphData second := by
    intro heq
    exact hne (edgeOrbitFacePair_injective_of_minimal
      graphData minimal heq)
  have hfirstCard : (edgeOrbitFacePair graphData first).card = 2 :=
    card_edgeOrbitFacePair_eq_two graphData minimal.facesTwoSided first
  have hsecondCard : (edgeOrbitFacePair graphData second).card = 2 :=
    card_edgeOrbitFacePair_eq_two graphData minimal.facesTwoSided second
  have hnotSubset : ¬ edgeOrbitFacePair graphData first ⊆
      edgeOrbitFacePair graphData second := by
    intro hsubset
    apply hpairs
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hfirstCard, hsecondCard]
  rcases Finset.not_subset.mp hnotSubset with ⟨face, hfirst, hsecond⟩
  refine ⟨face,
    (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
      graphData minimal.facesTwoSided face first).2 hfirst, ?_⟩
  have hneOne : orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels face) second ≠ 1 := by
    intro hone
    exact hsecond
      ((orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided face second).1 hone)
  exact f2_eq_zero_of_ne_one _ hneOne

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A canonical third facial generator: one quotient face is incident to
the retained cross edge but not to the restored central edge. -/
structure CrossCentralIndependentFaceGenerator
    (graphData : Data G) (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) where
  face : OrbitFace graphData.toRotationSystem
  face_mem_cross : face ∈
    edgeOrbitFacePair graphData (retainedEdgeToAmbientEdge data cross)
  face_not_mem_central : face ∉
    edgeOrbitFacePair graphData (centralEdge data)

namespace CrossCentralIndependentFaceGenerator

/-- Binary face labels of the selected singleton face. -/
def labels
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross) :
    OrbitFace graphData.toRotationSystem → F2 :=
  singletonOrbitFaceLabels generator.face

/-- Scalar edge transfer of the singleton facial boundary. -/
def edgeTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (edge : G.edgeSet) : F2 :=
  orbitFaceBoundaryLinearMap graphData.toRotationSystem
    generator.labels edge

/-- Recolor the singleton facial boundary by an arbitrary `F2²` value. -/
def colorTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (coefficient : Color) (edge : G.edgeSet) : Color :=
  generator.edgeTransfer edge • coefficient

@[simp]
theorem edgeTransfer_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross) :
    generator.edgeTransfer (retainedEdgeToAmbientEdge data cross) = 1 := by
  exact
    (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
      graphData minimal.facesTwoSided generator.face
        (retainedEdgeToAmbientEdge data cross)).2 generator.face_mem_cross

@[simp]
theorem edgeTransfer_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross) :
    generator.edgeTransfer (centralEdge data) = 0 := by
  have hneOne : generator.edgeTransfer (centralEdge data) ≠ 1 := by
    intro hone
    exact generator.face_not_mem_central
      ((orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided generator.face
          (centralEdge data)).1 hone)
  exact f2_eq_zero_of_ne_one _ hneOne

@[simp]
theorem colorTransfer_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (coefficient : Color) :
    generator.colorTransfer coefficient
        (retainedEdgeToAmbientEdge data cross) = coefficient := by
  simp [colorTransfer, generator.edgeTransfer_retainedCross minimal]

@[simp]
theorem colorTransfer_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (coefficient : Color) :
    generator.colorTransfer coefficient (centralEdge data) = 0 := by
  simp [colorTransfer, generator.edgeTransfer_centralEdge minimal]

/-- A recolored singleton facial boundary is a graph flow. -/
theorem colorTransfer_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (coefficient : Color) :
    IsGraphFlow G (generator.colorTransfer coefficient) := by
  have hcycle : generator.edgeTransfer ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace graphData
      minimal.facesTwoSided ⟨generator.labels, rfl⟩
  intro vertex
  unfold vertexKirchhoffSum
  calc
    ∑ edge ∈ incidentEdgeFinset G vertex,
        generator.colorTransfer coefficient edge =
        (∑ edge ∈ incidentEdgeFinset G vertex,
          generator.edgeTransfer edge) • coefficient := by
      simp only [colorTransfer]
      rw [Finset.sum_smul]
    _ = 0 := by
      have hzero := scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
        hcycle vertex
      unfold scalarVertexKirchhoffSum at hzero
      rw [hzero]
      simp

/-- Operational independence from the two exact closure generators: every
two-generator transfer has equal values on the retained cross and central
edges, while this nonzero singleton transfer separates them. -/
theorem colorTransfer_ne_edgeTransferInBasis
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (coefficient : Color) (hcoefficient : coefficient ≠ 0)
    (first second : Color) :
    generator.colorTransfer coefficient ≠
      pair.edgeTransferInBasis first second := by
  intro heq
  have hcross := congrFun heq (retainedEdgeToAmbientEdge data cross)
  have hcentral := congrFun heq (centralEdge data)
  rw [generator.colorTransfer_retainedCross minimal,
    pair.edgeTransferInBasis_retainedCross minimal] at hcross
  rw [generator.colorTransfer_centralEdge minimal,
    pair.edgeTransferInBasis_centralEdge minimal] at hcentral
  exact hcoefficient (hcross.trans hcentral.symm)

end CrossCentralIndependentFaceGenerator

/-- The distinct cross and central face pairs canonically supply an
independent singleton facial generator. -/
theorem exists_crossCentralIndependentFaceGenerator
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    Nonempty (CrossCentralIndependentFaceGenerator graphData data cross) := by
  rcases exists_singletonOrbitFaceLabels_separating_distinct_edges
      graphData minimal (retainedEdgeToAmbientEdge_ne_centralEdge data cross)
    with ⟨face, hcross, hcentral⟩
  refine ⟨⟨face, ?_, ?_⟩⟩
  · exact
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided face
          (retainedEdgeToAmbientEdge data cross)).1 hcross
  · intro hmem
    have hone :=
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided face (centralEdge data)).2 hmem
    exact zero_ne_one (hcentral.symm.trans hone)

/-- Add the independent singleton facial transfer to the reconstructed
two-closure flow. -/
def CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second third : Color) (edge : G.edgeSet) : Color :=
  pair.oneZeroClosureBasisPerturbation C first second edge +
    generator.colorTransfer third edge

/-- The three-generator perturbation remains a graph flow. -/
theorem CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second third : Color) :
    IsGraphFlow G
      (pair.oneZeroThreeGeneratorPerturbation generator C
        first second third) := by
  exact
    (pair.oneZeroClosureBasisPerturbation_isGraphFlow
      minimal C hC hsame first second).add
        (generator.colorTransfer_isGraphFlow minimal third)

/-- The independent generator leaves the restored central value unchanged. -/
theorem CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation_centralEdge
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second third : Color) :
    pair.oneZeroThreeGeneratorPerturbation generator C first second third
        (centralEdge data) = first + second := by
  rw [CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation,
    pair.oneZeroClosureBasisPerturbation_centralEdge minimal,
    generator.colorTransfer_centralEdge minimal, add_zero]

/-- On the retained cross, the third coefficient is added independently
of the common two-closure value. -/
theorem CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second third : Color) :
    pair.oneZeroThreeGeneratorPerturbation generator C first second third
        (retainedEdgeToAmbientEdge data cross) =
      C cross + (first + second) + third := by
  rw [CrossCentralExactFaceCutPair.oneZeroThreeGeneratorPerturbation,
    CrossCentralExactFaceCutPair.oneZeroClosureBasisPerturbation,
    oneZeroAmbientChain_retainedEdgeToAmbientEdge,
    pair.edgeTransferInBasis_retainedCross minimal,
    generator.colorTransfer_retainedCross minimal]

/-- If the two closure coefficients sum to the cross color, a nonzero third
coefficient repairs that cross zero while the nonzero sum keeps the central
edge repaired. Noncolorability therefore forces every remaining zero away
from both distinguished edges. -/
theorem CrossCentralExactFaceCutPair.exists_zero_off_cross_central_of_threeGenerator
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (generator : CrossCentralIndependentFaceGenerator graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second third : Color)
    (hcross : C cross = first + second)
    (hsum : first + second ≠ 0) (hthird : third ≠ 0) :
    ∃ edge : G.edgeSet,
      pair.oneZeroThreeGeneratorPerturbation generator C
          first second third edge = 0 ∧
        edge ≠ retainedEdgeToAmbientEdge data cross ∧
        edge ≠ centralEdge data := by
  let chain := pair.oneZeroThreeGeneratorPerturbation generator C
    first second third
  have hflow : IsGraphFlow G chain :=
    pair.oneZeroThreeGeneratorPerturbation_isGraphFlow
      minimal generator C hC hsame first second third
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hexistsZero : ∃ edge : G.edgeSet, chain edge = 0 := by
    by_contra hnone
    push Not at hnone
    have hnowhere : IsNowhereZeroFlow G chain := ⟨hflow, hnone⟩
    exact
      (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
        graphData minimal)
        (exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
          (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
            hcubic)
          chain hnowhere)
  rcases hexistsZero with ⟨edge, hedge⟩
  refine ⟨edge, hedge, ?_, ?_⟩
  · intro hedgeCross
    subst edge
    have hvalue := pair.oneZeroThreeGeneratorPerturbation_retainedCross
      minimal generator C first second third
    rw [hcross, color_add_self, zero_add] at hvalue
    exact hthird (hvalue.symm.trans hedge)
  · intro hedgeCentral
    subst edge
    have hvalue := pair.oneZeroThreeGeneratorPerturbation_centralEdge
      minimal generator C first second third
    exact hsum (hvalue.symm.trans hedge)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
