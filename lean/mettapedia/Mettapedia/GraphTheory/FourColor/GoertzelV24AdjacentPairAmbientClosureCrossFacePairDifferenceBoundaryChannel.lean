import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferencePortClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedTransferMonoid

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

/-- The other port index on the same side of the deleted adjacent pair. -/
def otherSideIndex (index : Fin 2) : Fin 2 :=
  ⟨1 - index.val, by omega⟩

@[simp] theorem otherSideIndex_zero : otherSideIndex 0 = 1 := by
  apply Fin.ext
  rfl

@[simp] theorem otherSideIndex_one : otherSideIndex 1 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem otherSideIndex_involutive (index : Fin 2) :
    otherSideIndex (otherSideIndex index) = index := by
  fin_cases index <;> simp

theorem otherSideIndex_ne (index : Fin 2) :
    otherSideIndex index ≠ index := by
  fin_cases index <;> decide

/-- Select one of the two scalar coordinates of an edge color. -/
def crossFaceCoordinate (coordinate : Bool) (value : Color) : F2 :=
  if coordinate then value.2 else value.1

@[simp] theorem crossFaceCoordinate_false (value : Color) :
    crossFaceCoordinate false value = value.1 := by
  rfl

@[simp] theorem crossFaceCoordinate_true (value : Color) :
    crossFaceCoordinate true value = value.2 := by
  rfl

/-- A scalar coordinate of a color-valued graph flow satisfies scalar
Kirchhoff at every vertex. -/
theorem crossFaceCoordinate_isScalarFlow
    (chain : G.edgeSet → Color)
    (hchain : IsGraphFlow G chain) (coordinate : Bool) :
    ∀ vertex : V,
      scalarVertexKirchhoffSum G
        (fun edge => crossFaceCoordinate coordinate (chain edge)) vertex = 0 := by
  intro vertex
  cases coordinate
  · change scalarVertexKirchhoffSum G (fun edge => (chain edge).1) vertex = 0
    rw [scalarVertexKirchhoffSum_fst]
    exact congrArg Prod.fst (hchain vertex)
  · change scalarVertexKirchhoffSum G (fun edge => (chain edge).2) vertex = 0
    rw [scalarVertexKirchhoffSum_snd]
    exact congrArg Prod.snd (hchain vertex)

private theorem f2_eq_one_of_ne_zero (value : F2) (hvalue : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

private theorem f2_eq_zero_of_one_add_one_add_eq_zero
    (value : F2) (hsum : 1 + (1 + value) = 0) : value = 0 := by
  calc
    value = 0 + value := by simp
    _ = (1 + 1) + value := by rw [zmod2_add_self]
    _ = 1 + (1 + value) := by rw [add_assoc]
    _ = 0 := hsum

/-- At the first restored cubic vertex, a nonzero central value and one
nonzero boundary value force the other boundary value to vanish. -/
theorem scalarFlow_otherFirstSidePort_eq_zero
    (data : AdjacentPairData G) (flow : G.edgeSet → F2)
    (hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G flow vertex = 0)
    (index : Fin 2)
    (hcentral : flow (centralEdge data) ≠ 0)
    (hselected : flow (boundaryEdge data (firstSidePort index)) ≠ 0) :
    flow (boundaryEdge data (firstSidePort (otherSideIndex index))) = 0 := by
  have hsum := hflow data.firstVertex
  unfold scalarVertexKirchhoffSum at hsum
  rw [incidentEdgeFinset_firstVertex data] at hsum
  have hcentralZero : centralEdge data ≠ boundaryEdge data 0 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue data 0
      (congrArg Subtype.val hedge)
  have hcentralOne : centralEdge data ≠ boundaryEdge data 1 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue data 1
      (congrArg Subtype.val hedge)
  have hzeroOne : boundaryEdge data 0 ≠ boundaryEdge data 1 := by
    intro hedge
    apply boundaryEdgeValue_ne data (show (0 : Fin 4) ≠ 1 by decide)
    simpa using congrArg Subtype.val hedge
  simp [hcentralZero, hcentralOne, hzeroOne] at hsum
  have hcentralValue := f2_eq_one_of_ne_zero _ hcentral
  have hindex : index = 0 ∨ index = 1 := by
    fin_cases index <;> simp
  rcases hindex with rfl | rfl
  · have hselectedValue : flow (boundaryEdge data 0) = 1 := by
      simpa using f2_eq_one_of_ne_zero _ hselected
    rw [hcentralValue, hselectedValue] at hsum
    simpa using f2_eq_zero_of_one_add_one_add_eq_zero _ hsum
  · have hselectedValue : flow (boundaryEdge data 1) = 1 := by
      simpa using f2_eq_one_of_ne_zero _ hselected
    rw [hcentralValue, hselectedValue] at hsum
    have hsum' : 1 + (1 + flow (boundaryEdge data 0)) = 0 := by
      simpa [add_comm] using hsum
    simpa using f2_eq_zero_of_one_add_one_add_eq_zero _ hsum'

/-- At the second restored cubic vertex, a nonzero central value and one
nonzero boundary value force the other boundary value to vanish. -/
theorem scalarFlow_otherSecondSidePort_eq_zero
    (data : AdjacentPairData G) (flow : G.edgeSet → F2)
    (hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G flow vertex = 0)
    (index : Fin 2)
    (hcentral : flow (centralEdge data) ≠ 0)
    (hselected : flow (boundaryEdge data (secondSidePort index)) ≠ 0) :
    flow (boundaryEdge data (secondSidePort (otherSideIndex index))) = 0 := by
  have hsum := hflow data.secondVertex
  unfold scalarVertexKirchhoffSum at hsum
  rw [incidentEdgeFinset_secondVertex data] at hsum
  have hcentralTwo : centralEdge data ≠ boundaryEdge data 2 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue data 2
      (congrArg Subtype.val hedge)
  have hcentralThree : centralEdge data ≠ boundaryEdge data 3 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue data 3
      (congrArg Subtype.val hedge)
  have htwoThree : boundaryEdge data 2 ≠ boundaryEdge data 3 := by
    intro hedge
    apply boundaryEdgeValue_ne data (show (2 : Fin 4) ≠ 3 by decide)
    simpa using congrArg Subtype.val hedge
  simp [hcentralTwo, hcentralThree, htwoThree] at hsum
  have hcentralValue := f2_eq_one_of_ne_zero _ hcentral
  have hindex : index = 0 ∨ index = 1 := by
    fin_cases index <;> simp
  rcases hindex with rfl | rfl
  · have hselectedValue : flow (boundaryEdge data 2) = 1 := by
      simpa using f2_eq_one_of_ne_zero _ hselected
    rw [hcentralValue, hselectedValue] at hsum
    simpa using f2_eq_zero_of_one_add_one_add_eq_zero _ hsum
  · have hselectedValue : flow (boundaryEdge data 3) = 1 := by
      simpa using f2_eq_one_of_ne_zero _ hselected
    rw [hcentralValue, hselectedValue] at hsum
    have hsum' : 1 + (1 + flow (boundaryEdge data 2)) = 0 := by
      simpa [add_comm] using hsum
    simpa using f2_eq_zero_of_one_add_one_add_eq_zero _ hsum'

/-- The nonzero first-side boundary value is indexed exactly by the selected
port. -/
theorem scalarFlow_firstSidePort_ne_zero_iff_eq
    (data : AdjacentPairData G) (flow : G.edgeSet → F2)
    (hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G flow vertex = 0)
    (index : Fin 2)
    (hcentral : flow (centralEdge data) ≠ 0)
    (hselected : flow (boundaryEdge data (firstSidePort index)) ≠ 0) :
    ∀ candidate : Fin 2,
      flow (boundaryEdge data (firstSidePort candidate)) ≠ 0 ↔
        candidate = index := by
  have hother := scalarFlow_otherFirstSidePort_eq_zero data flow hflow
    index hcentral hselected
  intro candidate
  fin_cases index <;> fin_cases candidate <;> simp_all

/-- The nonzero second-side boundary value is indexed exactly by the selected
port. -/
theorem scalarFlow_secondSidePort_ne_zero_iff_eq
    (data : AdjacentPairData G) (flow : G.edgeSet → F2)
    (hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G flow vertex = 0)
    (index : Fin 2)
    (hcentral : flow (centralEdge data) ≠ 0)
    (hselected : flow (boundaryEdge data (secondSidePort index)) ≠ 0) :
    ∀ candidate : Fin 2,
      flow (boundaryEdge data (secondSidePort candidate)) ≠ 0 ↔
        candidate = index := by
  have hother := scalarFlow_otherSecondSidePort_eq_zero data flow hflow
    index hcentral hselected
  intro candidate
  fin_cases index <;> fin_cases candidate <;> simp_all

/-- Endpoint parity of an indexed cross-side channel. -/
def crossSideChannelEndpointFlip (first second : Fin 2) : Bool :=
  Bool.xor (finTwoEquiv first) (finTwoEquiv second)

/-- The channel parity transports the first endpoint bit to the second. -/
@[simp] theorem boolRoutePermutation_crossSideChannelEndpointFlip
    (first second : Fin 2) :
    boolRoutePermutation (crossSideChannelEndpointFlip first second)
        (finTwoEquiv first) = finTwoEquiv second := by
  fin_cases first <;> fin_cases second <;> rfl

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The selected scalar component has an exact boundary channel: on each
side of the deleted adjacent pair precisely one port is nonzero.  The same
component supports a retained simple path between those ports, and its
endpoint parity is the corresponding Boolean transfer. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideCoordinateChannelClosure
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        crossFaceCoordinate coordinate
            (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0 ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
            candidate = firstIndex) ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
            candidate = secondIndex) ∧
        (∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (retainedEdgeToAmbientEdge data edge)) ≠ 0) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        boolRoutePermutation
            (crossSideChannelEndpointFlip firstIndex secondIndex)
            (finTwoEquiv firstIndex) = finTwoEquiv secondIndex := by
  rcases pair.exists_indexedCrossSide_coordinateSupportPortClosure minimal with
    ⟨firstIndex, secondIndex, path, hpath, hcross,
      hcoordinate, hcycle⟩
  have hcolorFlow : IsGraphFlow G pair.crossFaceDifferenceProfile :=
    pair.crossFaceDifferenceProfile_isGraphFlow minimal
  rcases hcoordinate with hfirstCoordinate | hsecondCoordinate
  · have hflow := crossFaceCoordinate_isScalarFlow
      pair.crossFaceDifferenceProfile hcolorFlow false
    have hfirstExact := scalarFlow_firstSidePort_ne_zero_iff_eq data
      (fun edge => crossFaceCoordinate false
        (pair.crossFaceDifferenceProfile edge)) hflow firstIndex
      hfirstCoordinate.1 hfirstCoordinate.2.2.1
    have hsecondExact := scalarFlow_secondSidePort_ne_zero_iff_eq data
      (fun edge => crossFaceCoordinate false
        (pair.crossFaceDifferenceProfile edge)) hflow secondIndex
      hfirstCoordinate.1 hfirstCoordinate.2.1
    exact ⟨false, firstIndex, secondIndex, path, hpath, hcross,
      hfirstCoordinate.1, hfirstExact, hsecondExact,
      hfirstCoordinate.2.2.2, hcycle,
      boolRoutePermutation_crossSideChannelEndpointFlip firstIndex secondIndex⟩
  · have hflow := crossFaceCoordinate_isScalarFlow
      pair.crossFaceDifferenceProfile hcolorFlow true
    have hfirstExact := scalarFlow_firstSidePort_ne_zero_iff_eq data
      (fun edge => crossFaceCoordinate true
        (pair.crossFaceDifferenceProfile edge)) hflow firstIndex
      hsecondCoordinate.1 hsecondCoordinate.2.2.1
    have hsecondExact := scalarFlow_secondSidePort_ne_zero_iff_eq data
      (fun edge => crossFaceCoordinate true
        (pair.crossFaceDifferenceProfile edge)) hflow secondIndex
      hsecondCoordinate.1 hsecondCoordinate.2.1
    exact ⟨true, firstIndex, secondIndex, path, hpath, hcross,
      hsecondCoordinate.1, hfirstExact, hsecondExact,
      hsecondCoordinate.2.2.2, hcycle,
      boolRoutePermutation_crossSideChannelEndpointFlip firstIndex secondIndex⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
