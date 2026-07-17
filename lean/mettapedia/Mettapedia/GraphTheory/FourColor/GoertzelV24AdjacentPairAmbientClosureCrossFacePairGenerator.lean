import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureIndependentFaceGenerator

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossFacePairGeneratorGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24MinimalFaceIntersections

/-- The quotient face on the representative-dart side of an edge. -/
def edgeLeftOrbitFace (graphData : Data G) (edge : G.edgeSet) :
    OrbitFace graphData.toRotationSystem :=
  dartOrbitFace graphData.toRotationSystem
    (graphData.toRotationSystem.dartRepresentative edge)

/-- The quotient face on the opposite-dart side of an edge. -/
def edgeRightOrbitFace (graphData : Data G) (edge : G.edgeSet) :
    OrbitFace graphData.toRotationSystem :=
  dartOrbitFace graphData.toRotationSystem
    (graphData.toRotationSystem.alpha
      (graphData.toRotationSystem.dartRepresentative edge))

/-- Recolor the boundary of one singleton quotient face. -/
def singletonOrbitFaceColorTransfer
    (graphData : Data G) (face : OrbitFace graphData.toRotationSystem)
    (coefficient : Color) (edge : G.edgeSet) : Color :=
  orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels face) edge • coefficient

/-- A recolored singleton facial boundary satisfies Kirchhoff's law. -/
theorem singletonOrbitFaceColorTransfer_isGraphFlow
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (face : OrbitFace graphData.toRotationSystem)
    (coefficient : Color) :
    IsGraphFlow G
      (singletonOrbitFaceColorTransfer graphData face coefficient) := by
  have hcycle :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels face) ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace graphData
      minimal.facesTwoSided ⟨singletonOrbitFaceLabels face, rfl⟩
  intro vertex
  unfold vertexKirchhoffSum
  calc
    ∑ edge ∈ incidentEdgeFinset G vertex,
        singletonOrbitFaceColorTransfer graphData face coefficient edge =
        (∑ edge ∈ incidentEdgeFinset G vertex,
          orbitFaceBoundaryLinearMap graphData.toRotationSystem
            (singletonOrbitFaceLabels face) edge) • coefficient := by
      simp only [singletonOrbitFaceColorTransfer]
      rw [Finset.sum_smul]
    _ = 0 := by
      have hzero := scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
        hcycle vertex
      unfold scalarVertexKirchhoffSum at hzero
      rw [hzero]
      simp

/-- The two singleton facial boundaries incident to a selected edge,
recolored independently. -/
def edgeTwoFaceColorTransfer
    (graphData : Data G) (source : G.edgeSet)
    (leftCoefficient rightCoefficient : Color) (edge : G.edgeSet) : Color :=
  singletonOrbitFaceColorTransfer graphData
      (edgeLeftOrbitFace graphData source) leftCoefficient edge +
    singletonOrbitFaceColorTransfer graphData
      (edgeRightOrbitFace graphData source) rightCoefficient edge

/-- Both side-face boundaries cross their selected source edge. -/
theorem edgeTwoFaceColorTransfer_source
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) (leftCoefficient rightCoefficient : Color) :
    edgeTwoFaceColorTransfer graphData source
        leftCoefficient rightCoefficient source =
      leftCoefficient + rightCoefficient := by
  have hleft : orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels (edgeLeftOrbitFace graphData source))
        source = 1 := by
    apply
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided
          (edgeLeftOrbitFace graphData source) source).2
    simp [edgeOrbitFacePair, edgeLeftOrbitFace]
  have hright : orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels (edgeRightOrbitFace graphData source))
        source = 1 := by
    apply
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided
          (edgeRightOrbitFace graphData source) source).2
    simp [edgeOrbitFacePair, edgeRightOrbitFace]
  simp [edgeTwoFaceColorTransfer, singletonOrbitFaceColorTransfer,
    hleft, hright]

/-- The sum of the two recolored singleton boundaries remains a graph flow. -/
theorem edgeTwoFaceColorTransfer_isGraphFlow
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) (leftCoefficient rightCoefficient : Color) :
    IsGraphFlow G
      (edgeTwoFaceColorTransfer graphData source
        leftCoefficient rightCoefficient) := by
  exact
    (singletonOrbitFaceColorTransfer_isGraphFlow graphData minimal
      (edgeLeftOrbitFace graphData source) leftCoefficient).add
    (singletonOrbitFaceColorTransfer_isGraphFlow graphData minimal
      (edgeRightOrbitFace graphData source) rightCoefficient)

/-- An edge is crossed by both singleton side-face boundaries exactly when
it is the selected source edge. Distinct primal edges cannot have the same
two quotient-face sides in a graph-backed minimal map. -/
theorem edgeLeft_right_singletonBoundary_eq_one_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source edge : G.edgeSet) :
    (orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeLeftOrbitFace graphData source))
          edge = 1 ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeRightOrbitFace graphData source))
          edge = 1) ↔
      edge = source := by
  constructor
  · rintro ⟨hleftValue, hrightValue⟩
    have hleft : edgeLeftOrbitFace graphData source ∈
        edgeOrbitFacePair graphData edge :=
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided
          (edgeLeftOrbitFace graphData source) edge).1 hleftValue
    have hright : edgeRightOrbitFace graphData source ∈
        edgeOrbitFacePair graphData edge :=
      (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
        graphData minimal.facesTwoSided
          (edgeRightOrbitFace graphData source) edge).1 hrightValue
    have hsubset : edgeOrbitFacePair graphData source ⊆
        edgeOrbitFacePair graphData edge := by
      intro face hface
      simp only [edgeOrbitFacePair, Finset.mem_insert,
        Finset.mem_singleton] at hface
      rcases hface with hface | hface
      · exact hface ▸ hleft
      · exact hface ▸ hright
    have hpairs : edgeOrbitFacePair graphData source =
        edgeOrbitFacePair graphData edge := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [card_edgeOrbitFacePair_eq_two graphData
          minimal.facesTwoSided source,
        card_edgeOrbitFacePair_eq_two graphData
          minimal.facesTwoSided edge]
    exact (edgeOrbitFacePair_injective_of_minimal
      graphData minimal hpairs).symm
  · intro hedge
    subst edge
    constructor
    · apply
        (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
          graphData minimal.facesTwoSided
            (edgeLeftOrbitFace graphData source) source).2
      simp [edgeOrbitFacePair, edgeLeftOrbitFace]
    · apply
        (orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
          graphData minimal.facesTwoSided
            (edgeRightOrbitFace graphData source) source).2
      simp [edgeOrbitFacePair, edgeRightOrbitFace]

private theorem f2_smul_pair_eq_add_iff
    (leftBit rightBit : F2) {leftCoefficient rightCoefficient : Color}
    (hleft : leftCoefficient ≠ 0) (hright : rightCoefficient ≠ 0)
    (hdistinct : leftCoefficient ≠ rightCoefficient) :
    leftBit • leftCoefficient + rightBit • rightCoefficient =
        leftCoefficient + rightCoefficient ↔
      leftBit = 1 ∧ rightBit = 1 := by
  constructor
  · intro heq
    have hmapped :
        colorBasisAddHom leftCoefficient rightCoefficient
            (leftBit, rightBit) =
          colorBasisAddHom leftCoefficient rightCoefficient purple := by
      rw [colorBasisAddHom_purple]
      exact heq
    have hcoefficients : (leftBit, rightBit) = purple :=
      colorBasisAddHom_injective hleft hright hdistinct hmapped
    exact ⟨congrArg Prod.fst hcoefficients,
      congrArg Prod.snd hcoefficients⟩
  · rintro ⟨rfl, rfl⟩
    exact colorBasisAddHom_purple leftCoefficient rightCoefficient

/-- With distinct nonzero coefficients, their sum occurs on the two-face
transfer exactly at the selected source edge. -/
theorem edgeTwoFaceColorTransfer_eq_add_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source edge : G.edgeSet) {leftCoefficient rightCoefficient : Color}
    (hleft : leftCoefficient ≠ 0) (hright : rightCoefficient ≠ 0)
    (hdistinct : leftCoefficient ≠ rightCoefficient) :
    edgeTwoFaceColorTransfer graphData source
        leftCoefficient rightCoefficient edge =
          leftCoefficient + rightCoefficient ↔
      edge = source := by
  change
    (orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeLeftOrbitFace graphData source))
          edge • leftCoefficient +
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeRightOrbitFace graphData source))
          edge • rightCoefficient =
        leftCoefficient + rightCoefficient) ↔ edge = source
  rw [f2_smul_pair_eq_add_iff _ _ hleft hright hdistinct]
  exact edgeLeft_right_singletonBoundary_eq_one_iff
    graphData minimal source edge

end GoertzelV24MinimalFaceIntersections

/-- At a cubic vertex, a graph flow with a unique incident occurrence of a
nonzero value is nonzero on all three incident edges. A zero on either other
edge would force the third edge to repeat the distinguished value. -/
theorem IsGraphFlow.incident_ne_zero_of_card_three_of_unique_value
    {chain : G.edgeSet → Color} (hflow : IsGraphFlow G chain)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    (source : G.edgeSet) (hsourceIncident :
      source ∈ incidentEdgeFinset G vertex)
    (value : Color) (hvalue : value ≠ 0)
    (hsourceValue : chain source = value)
    (hunique : ∀ edge ∈ incidentEdgeFinset G vertex,
      chain edge = value → edge = source) :
    ∀ edge ∈ incidentEdgeFinset G vertex, chain edge ≠ 0 := by
  rcases Finset.card_eq_three.mp hcubic with
    ⟨first, second, third, hfirstSecond, hfirstThird,
      hsecondThird, hset⟩
  have hfirstIncident : first ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hsecondIncident : second ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hthirdIncident : third ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hlocal : chain first + chain second + chain third = 0 := by
    have hvertex := hflow vertex
    unfold vertexKirchhoffSum at hvertex
    rw [hset] at hvertex
    simpa [hfirstSecond, hfirstThird, hsecondThird, add_assoc] using hvertex
  have hsourceCases : source = first ∨ source = second ∨ source = third := by
    rw [hset] at hsourceIncident
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsourceIncident
  rcases hsourceCases with hsource | hsource | hsource
  · subst source
    have hfirstNonzero : chain first ≠ 0 := by
      rw [hsourceValue]
      exact hvalue
    have hsecondNonzero : chain second ≠ 0 := by
      intro hsecondZero
      have hfirstThirdValue : chain first = chain third :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hsecondZero, add_assoc] using hlocal)
      have hthirdSource : third = first :=
        hunique third hthirdIncident
          (hfirstThirdValue.symm.trans hsourceValue)
      exact hfirstThird hthirdSource.symm
    have hthirdNonzero : chain third ≠ 0 := by
      intro hthirdZero
      have hfirstSecondValue : chain first = chain second :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hthirdZero, add_assoc] using hlocal)
      have hsecondSource : second = first :=
        hunique second hsecondIncident
          (hfirstSecondValue.symm.trans hsourceValue)
      exact hfirstSecond hsecondSource.symm
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero
  · subst source
    have hsecondNonzero : chain second ≠ 0 := by
      rw [hsourceValue]
      exact hvalue
    have hfirstNonzero : chain first ≠ 0 := by
      intro hfirstZero
      have hsecondThirdValue : chain second = chain third :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hfirstZero, add_assoc] using hlocal)
      have hthirdSource : third = second :=
        hunique third hthirdIncident
          (hsecondThirdValue.symm.trans hsourceValue)
      exact hsecondThird hthirdSource.symm
    have hthirdNonzero : chain third ≠ 0 := by
      intro hthirdZero
      have hfirstSecondValue : chain first = chain second :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hthirdZero, add_assoc] using hlocal)
      have hfirstSource : first = second :=
        hunique first hfirstIncident
          (hfirstSecondValue.trans hsourceValue)
      exact hfirstSecond hfirstSource
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero
  · subst source
    have hthirdNonzero : chain third ≠ 0 := by
      rw [hsourceValue]
      exact hvalue
    have hfirstNonzero : chain first ≠ 0 := by
      intro hfirstZero
      have hsecondThirdValue : chain second = chain third :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hfirstZero, add_assoc] using hlocal)
      have hsecondSource : second = third :=
        hunique second hsecondIncident
          (hsecondThirdValue.trans hsourceValue)
      exact hsecondThird hsecondSource
    have hsecondNonzero : chain second ≠ 0 := by
      intro hsecondZero
      have hfirstThirdValue : chain first = chain third :=
        (add_eq_zero_iff_eq _ _).1 (by
          simpa [hsecondZero, add_assoc] using hlocal)
      have hfirstSource : first = third :=
        hunique first hfirstIncident
          (hfirstThirdValue.trans hsourceValue)
      exact hfirstThird hfirstSource
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero

namespace GoertzelV24MinimalFaceIntersections

/-- At either endpoint of the selected source edge, its two side-face
generators carry a nowhere-zero local triple. The sum coefficient occurs
only on the source, so Kirchhoff's law excludes a zero on either arm. -/
theorem edgeTwoFaceColorTransfer_incident_ne_zero
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) {leftCoefficient rightCoefficient : Color}
    (hleft : leftCoefficient ≠ 0) (hright : rightCoefficient ≠ 0)
    (hdistinct : leftCoefficient ≠ rightCoefficient)
    (vertex : V) (hvertex : vertex ∈ (source.1 : Sym2 V)) :
    ∀ edge ∈ incidentEdgeFinset G vertex,
      edgeTwoFaceColorTransfer graphData source
        leftCoefficient rightCoefficient edge ≠ 0 := by
  have hsourceIncident : source ∈ incidentEdgeFinset G vertex := by
    simpa [incidentEdgeFinset] using hvertex
  apply
    (edgeTwoFaceColorTransfer_isGraphFlow graphData minimal source
      leftCoefficient rightCoefficient)
      |>.incident_ne_zero_of_card_three_of_unique_value
        vertex
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic vertex)
        source hsourceIncident (leftCoefficient + rightCoefficient)
        (add_ne_zero_of_ne hdistinct)
  · exact edgeTwoFaceColorTransfer_source graphData minimal source
      leftCoefficient rightCoefficient
  · intro edge _hedge hvalue
    exact (edgeTwoFaceColorTransfer_eq_add_iff graphData minimal
      source edge hleft hright hdistinct).1 hvalue

end GoertzelV24MinimalFaceIntersections

end

end Mettapedia.GraphTheory.FourColor
