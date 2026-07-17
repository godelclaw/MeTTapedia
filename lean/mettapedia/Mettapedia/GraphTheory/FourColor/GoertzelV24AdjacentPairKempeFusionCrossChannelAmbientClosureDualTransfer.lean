import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFacePairCompatibility
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24DualPathTransversal

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A face coefficient changes across a dual-walk step by exactly the
boundary-map coordinate of the primal edge crossed at that step. -/
theorem orbitFaceBoundaryLinearMap_apply_dualWalkCrossingEdge
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (labels : OrbitFace RS → F2) (step : Fin walk.length) :
    orbitFaceBoundaryLinearMap RS labels
        (dualWalkCrossingEdge (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step) =
      labels (walk.getVert step.val).1 +
        labels (walk.getVert (step.val + 1)).1 := by
  let left := (walk.getVert step.val).1
  let right := (walk.getVert (step.val + 1)).1
  let edge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hadj := walk.adj_getVert_succ step.isLt
  have hfaces : left ≠ right := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary RS left :=
    dualWalkCrossingEdge_mem_leftFace (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hright : edge ∈ orbitFaceBoundary RS right :=
    dualWalkCrossingEdge_mem_rightFace (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  rw [orbitFaceBoundaryLinearMap_apply]
  calc
    (∑ face : OrbitFace RS,
        if edge ∈ orbitFaceBoundary RS face then labels face else 0) =
        ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
          edge ∈ orbitFaceBoundary RS face), labels face := by
      rw [Finset.sum_filter]
    _ = ∑ face ∈ ({left, right} : Finset (OrbitFace RS)),
        labels face := by
      rw [orbitFace_incidentFaces_eq_pair_of_mem RS htwoSided
        hfaces edge hleft hright]
    _ = labels left + labels right := by
      simp [hfaces]

end

end GoertzelV24DualPathTransversal

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The paired binary boundary coordinate carried by one ambient edge. -/
def CrossCentralExactFaceCutPair.edgeTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet) : Color :=
  (orbitFaceBoundaryLinearMap graphData.toRotationSystem
      pair.prefixLabels edge,
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
      pair.suffixLabels edge)

/-- The first transfer bit is the exact support of the first ambient
closure. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_fst_eq_one_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    (pair.edgeTransfer edge).1 = 1 ↔
      edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  change orbitFaceBoundaryLinearMap RS pair.prefixLabels edge = 1 ↔ _
  rw [← hedge,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS minimal.facesTwoSided,
    f2_add_eq_one_iff_ne]
  simpa only [RS, hedge] using pair.prefixExact dart

/-- The second transfer bit is the exact support of the second ambient
closure. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_snd_eq_one_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    (pair.edgeTransfer edge).2 = 1 ↔
      edge.1 ∈
        (data.alternateOppositePortClosure pair.suffixTrail).edges := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  change orbitFaceBoundaryLinearMap RS pair.suffixLabels edge = 1 ↔ _
  rw [← hedge,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS minimal.facesTwoSided,
    f2_add_eq_one_iff_ne]
  simpa only [RS, hedge] using pair.suffixExact dart

private theorem f2_eq_zero_iff_ne_one (value : F2) :
    value = 0 ↔ value ≠ 1 := by
  constructor
  · rintro rfl h
    exact zero_ne_one h
  · intro h
    fin_cases value
    · rfl
    · exact (h rfl).elim

/-- The zero transfer letter records avoidance of both ambient closures. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_eq_zero_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    pair.edgeTransfer edge = 0 ↔
      edge.1 ∉ (data.oppositePortClosure pair.prefixTrail).edges ∧
        edge.1 ∉
          (data.alternateOppositePortClosure pair.suffixTrail).edges := by
  rw [Prod.ext_iff]
  change
    ((pair.edgeTransfer edge).1 = 0 ∧
      (pair.edgeTransfer edge).2 = 0) ↔ _
  rw [f2_eq_zero_iff_ne_one, f2_eq_zero_iff_ne_one]
  exact and_congr
    (not_congr (pair.edgeTransfer_fst_eq_one_iff minimal edge))
    (not_congr (pair.edgeTransfer_snd_eq_one_iff minimal edge))

/-- The red transfer letter records membership only in the first ambient
closure. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_eq_red_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    pair.edgeTransfer edge = red ↔
      edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∧
        edge.1 ∉
          (data.alternateOppositePortClosure pair.suffixTrail).edges := by
  rw [Prod.ext_iff]
  change
    ((pair.edgeTransfer edge).1 = 1 ∧
      (pair.edgeTransfer edge).2 = 0) ↔ _
  rw [f2_eq_zero_iff_ne_one]
  exact and_congr
    (pair.edgeTransfer_fst_eq_one_iff minimal edge)
    (not_congr (pair.edgeTransfer_snd_eq_one_iff minimal edge))

/-- The blue transfer letter records membership only in the second ambient
closure. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_eq_blue_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    pair.edgeTransfer edge = blue ↔
      edge.1 ∉ (data.oppositePortClosure pair.prefixTrail).edges ∧
        edge.1 ∈
          (data.alternateOppositePortClosure pair.suffixTrail).edges := by
  rw [Prod.ext_iff]
  change
    ((pair.edgeTransfer edge).1 = 0 ∧
      (pair.edgeTransfer edge).2 = 1) ↔ _
  rw [f2_eq_zero_iff_ne_one]
  exact and_congr
    (not_congr (pair.edgeTransfer_fst_eq_one_iff minimal edge))
    (pair.edgeTransfer_snd_eq_one_iff minimal edge)

/-- The paired face-label transfer across one step of an ambient facial-dual
walk. -/
def CrossCentralExactFaceCutPair.dualStepTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish)
    (step : Fin walk.length) : Color :=
  pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
      (walk.getVert step.val).1 +
    pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
      (walk.getVert (step.val + 1)).1

private theorem sum_adjacent_color_eq_endpoints
    (values : Nat → Color) (length : Nat) :
    (∑ step ∈ Finset.range length,
        (values step + values (step + 1))) =
      values 0 + values length := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.sum_range_succ, ih]
      calc
        (values 0 + values length) +
            (values length + values (length + 1)) =
          values 0 + (values length + values length) +
            values (length + 1) := by abel
        _ = values 0 + values (length + 1) := by simp

/-- The paired transfer word telescopes: its total is the paired-label
difference between the two endpoint faces. -/
theorem CrossCentralExactFaceCutPair.sum_dualStepTransfer_eq_endpoints
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish) :
    (∑ step : Fin walk.length, pair.dualStepTransfer walk step) =
      pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels start.1 +
        pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels finish.1 := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ step ∈ Finset.range walk.length,
        if h : step < walk.length then
          pair.dualStepTransfer walk ⟨step, h⟩ else 0) =
        ∑ step ∈ Finset.range walk.length,
          (pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
              (walk.getVert step).1 +
            pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
              (walk.getVert (step + 1)).1) := by
      apply Finset.sum_congr rfl
      intro step hstep
      have hlt : step < walk.length := Finset.mem_range.1 hstep
      simp only [dif_pos hlt,
        CrossCentralExactFaceCutPair.dualStepTransfer]
    _ = pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
          (walk.getVert 0).1 +
        pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
          (walk.getVert walk.length).1 :=
      sum_adjacent_color_eq_endpoints
        (fun step => pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels
          (walk.getVert step).1) walk.length
    _ = pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels start.1 +
        pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels finish.1 := by
      rw [walk.getVert_zero, walk.getVert_length]

/-- In particular, the paired transfer around any closed dual walk is zero. -/
theorem CrossCentralExactFaceCutPair.sum_dualStepTransfer_eq_zero_of_closed
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        face face) :
    (∑ step : Fin walk.length, pair.dualStepTransfer walk step) = 0 := by
  rw [pair.sum_dualStepTransfer_eq_endpoints walk]
  exact color_add_self _

/-- Along a graph-backed minimal map, the face-to-face transfer at a dual
step is the paired boundary coordinate of its canonical crossed edge. -/
theorem CrossCentralExactFaceCutPair.dualStepTransfer_eq_edgeTransfer
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish)
    (step : Fin walk.length) :
    pair.dualStepTransfer walk step =
      pair.edgeTransfer
        (dualWalkCrossingEdge
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step) := by
  apply Prod.ext
  · exact (orbitFaceBoundaryLinearMap_apply_dualWalkCrossingEdge
      graphData.toRotationSystem minimal.facesTwoSided
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
      pair.prefixLabels step).symm
  · exact (orbitFaceBoundaryLinearMap_apply_dualWalkCrossingEdge
      graphData.toRotationSystem minimal.facesTwoSided
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
      pair.suffixLabels step).symm

/-- The canonical crossing-edge word has total transfer equal to the paired
label difference of its endpoint faces. -/
theorem CrossCentralExactFaceCutPair.sum_edgeTransfer_crossings_eq_endpoints
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish) :
    (∑ step : Fin walk.length,
      pair.edgeTransfer
        (dualWalkCrossingEdge
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step)) =
      pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels start.1 +
        pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels finish.1 := by
  calc
    (∑ step : Fin walk.length,
        pair.edgeTransfer
          (dualWalkCrossingEdge
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step)) =
        ∑ step : Fin walk.length, pair.dualStepTransfer walk step := by
      apply Finset.sum_congr rfl
      intro step _hstep
      exact (pair.dualStepTransfer_eq_edgeTransfer minimal walk step).symm
    _ = pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels start.1 +
        pairedOrbitFaceLabels pair.prefixLabels pair.suffixLabels finish.1 :=
      pair.sum_dualStepTransfer_eq_endpoints walk

/-- Consequently, the canonical crossing-edge transfer word of a closed
dual walk has zero total. -/
theorem CrossCentralExactFaceCutPair.sum_edgeTransfer_crossings_eq_zero_of_closed
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        face face) :
    (∑ step : Fin walk.length,
      pair.edgeTransfer
        (dualWalkCrossingEdge
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step)) =
      0 := by
  rw [pair.sum_edgeTransfer_crossings_eq_endpoints minimal walk]
  exact color_add_self _

/-- The simultaneous nonzero boundary state occurs exactly on the retained
cross edge and the restored central edge. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_eq_purple_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (edge : G.edgeSet) :
    pair.edgeTransfer edge = purple ↔
      edge.1 = (retainedEdgeToAmbientEdge data cross).1 ∨
        edge.1 = centralEdgeValue data := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  simp only [CrossCentralExactFaceCutPair.edgeTransfer, purple,
    Prod.mk.injEq]
  change
    (orbitFaceBoundaryLinearMap RS pair.prefixLabels edge = 1 ∧
      orbitFaceBoundaryLinearMap RS pair.suffixLabels edge = 1) ↔
        edge.1 = (retainedEdgeToAmbientEdge data cross).1 ∨
          edge.1 = centralEdgeValue data
  rw [← hedge,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS minimal.facesTwoSided,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS minimal.facesTwoSided,
    f2_add_eq_one_iff_ne, f2_add_eq_one_iff_ne]
  simpa only [RS, hedge] using pair.jointExact dart

/-- Hence a dual step has the diagonal transfer precisely when it crosses
one of the two common edges of the exact cut pair. -/
theorem CrossCentralExactFaceCutPair.dualStepTransfer_eq_purple_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish)
    (step : Fin walk.length) :
    pair.dualStepTransfer walk step = purple ↔
      (dualWalkCrossingEdge
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step).1 =
          (retainedEdgeToAmbientEdge data cross).1 ∨
      (dualWalkCrossingEdge
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step).1 =
          centralEdgeValue data := by
  rw [pair.dualStepTransfer_eq_edgeTransfer minimal walk step,
    pair.edgeTransfer_eq_purple_iff minimal]

/-- Positions at which a paired face-label word makes a diagonal jump. -/
def CrossCentralExactFaceCutPair.dualPurpleSteps
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish) : Finset (Fin walk.length) :=
  Finset.univ.filter fun step => pair.dualStepTransfer walk step = purple

@[simp]
theorem CrossCentralExactFaceCutPair.mem_dualPurpleSteps_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish)
    (step : Fin walk.length) :
    step ∈ pair.dualPurpleSteps walk ↔
      (dualWalkCrossingEdge
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step).1 =
          (retainedEdgeToAmbientEdge data cross).1 ∨
      (dualWalkCrossingEdge
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk step).1 =
          centralEdgeValue data := by
  rw [CrossCentralExactFaceCutPair.dualPurpleSteps, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact pair.dualStepTransfer_eq_purple_iff minimal walk step

/-- A simple dual path encounters at most two diagonal jumps: its crossing
edges are injective, and the exact paired support contains only the retained
cross edge and the central edge. -/
theorem CrossCentralExactFaceCutPair.card_dualPurpleSteps_le_two_of_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Walk
        start finish)
    (hpath : walk.IsPath) :
    (pair.dualPurpleSteps walk).card ≤ 2 := by
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
  have hinjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isPath
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hpath
  have hsubset : (pair.dualPurpleSteps walk).image crossing ⊆
      {retainedEdgeToAmbientEdge data cross, centralEdge data} := by
    intro edge hedge
    rcases Finset.mem_image.1 hedge with ⟨step, hstep, rfl⟩
    have hcases := (pair.mem_dualPurpleSteps_iff minimal walk step).1 hstep
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with hcross | hcentral
    · exact Or.inl (Subtype.ext hcross)
    · exact Or.inr (Subtype.ext hcentral)
  calc
    (pair.dualPurpleSteps walk).card =
        ((pair.dualPurpleSteps walk).image crossing).card := by
      symm
      exact Finset.card_image_of_injective _ hinjective
    _ ≤ ({retainedEdgeToAmbientEdge data cross,
          centralEdge data} : Finset G.edgeSet).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
