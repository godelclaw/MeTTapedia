import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFacePairSeparation

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24MinimalFaceIntersections

/-- The five possible oriented incidence profiles of two edge-face pairs
when the pairs share at most one quotient face. -/
inductive EdgeOrbitFacePairProfile where
  | disjoint
  | leftLeft
  | leftRight
  | rightLeft
  | rightRight
  deriving DecidableEq, Fintype

theorem card_edgeOrbitFacePairProfile :
    Fintype.card EdgeOrbitFacePairProfile = 5 := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientClosureFacePairProfileGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Canonical oriented face-pair profile for two ambient edges. The side
orientation comes from the canonical representative dart of each edge. -/
def edgeOrbitFacePairProfile (graphData : Data G)
    (first second : G.edgeSet) : EdgeOrbitFacePairProfile :=
  let RS := graphData.toRotationSystem
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  if dartOrbitFace RS firstDart = dartOrbitFace RS secondDart then
    .leftLeft
  else if dartOrbitFace RS firstDart =
      dartOrbitFace RS (RS.alpha secondDart) then
    .leftRight
  else if dartOrbitFace RS (RS.alpha firstDart) =
      dartOrbitFace RS secondDart then
    .rightLeft
  else if dartOrbitFace RS (RS.alpha firstDart) =
      dartOrbitFace RS (RS.alpha secondDart) then
    .rightRight
  else
    .disjoint

/-- The finite profile reports one actual face equality, or reports that all
four possible side equalities fail. -/
theorem edgeOrbitFacePairProfile_spec
    (graphData : Data G) (first second : G.edgeSet) :
    let RS := graphData.toRotationSystem
    let firstDart := RS.dartRepresentative first
    let secondDart := RS.dartRepresentative second
    match edgeOrbitFacePairProfile graphData first second with
    | .disjoint =>
        dartOrbitFace RS firstDart ≠ dartOrbitFace RS secondDart ∧
          dartOrbitFace RS firstDart ≠
            dartOrbitFace RS (RS.alpha secondDart) ∧
          dartOrbitFace RS (RS.alpha firstDart) ≠
            dartOrbitFace RS secondDart ∧
          dartOrbitFace RS (RS.alpha firstDart) ≠
            dartOrbitFace RS (RS.alpha secondDart)
    | .leftLeft =>
        dartOrbitFace RS firstDart = dartOrbitFace RS secondDart
    | .leftRight =>
        dartOrbitFace RS firstDart =
          dartOrbitFace RS (RS.alpha secondDart)
    | .rightLeft =>
        dartOrbitFace RS (RS.alpha firstDart) =
          dartOrbitFace RS secondDart
    | .rightRight =>
        dartOrbitFace RS (RS.alpha firstDart) =
          dartOrbitFace RS (RS.alpha secondDart) := by
  simp only [edgeOrbitFacePairProfile]
  split_ifs <;> simp_all

/-- Distinct edges of a graph-backed vertex-minimal counterexample share at
most one quotient face. -/
theorem card_edgeOrbitFacePair_inter_le_one_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : G.edgeSet} (hne : first ≠ second) :
    ((edgeOrbitFacePair graphData first) ∩
      (edgeOrbitFacePair graphData second)).card ≤ 1 := by
  by_contra hcard
  have hinterCard : 2 ≤ ((edgeOrbitFacePair graphData first) ∩
      (edgeOrbitFacePair graphData second)).card := by
    omega
  have hfirstCard : (edgeOrbitFacePair graphData first).card = 2 := by
    apply Finset.card_eq_two.mpr
    exact ⟨dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative first),
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative first)),
      minimal.facesTwoSided
        (graphData.toRotationSystem.dartRepresentative first), rfl⟩
  have hsecondCard : (edgeOrbitFacePair graphData second).card = 2 := by
    apply Finset.card_eq_two.mpr
    exact ⟨dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative second),
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative second)),
      minimal.facesTwoSided
        (graphData.toRotationSystem.dartRepresentative second), rfl⟩
  have hinterFirst :
      (edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second) =
        edgeOrbitFacePair graphData first := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    simpa only [hfirstCard] using hinterCard
  have hinterSecond :
      (edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second) =
        edgeOrbitFacePair graphData second := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    simpa only [hsecondCard] using hinterCard
  apply hne
  apply edgeOrbitFacePair_injective_of_minimal graphData minimal
  exact hinterFirst.symm.trans hinterSecond

end

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- In particular, the selected singleton-cross edge and the restored
central edge occupy one of the five exact face-incidence states, with no
second common face hidden by the binary cut labels. -/
theorem retainedCross_central_facePair_inter_card_le_one
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    ((edgeOrbitFacePair graphData (retainedEdgeToAmbientEdge data cross)) ∩
      (edgeOrbitFacePair graphData (centralEdge data))).card ≤ 1 := by
  apply card_edgeOrbitFacePair_inter_le_one_of_minimal graphData minimal
  exact retainedEdgeToAmbientEdge_ne_centralEdge data cross

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
