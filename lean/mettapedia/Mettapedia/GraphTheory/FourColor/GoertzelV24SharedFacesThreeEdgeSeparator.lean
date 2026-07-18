import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SharedFacesThreeEdgeSeparator

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Three edges shared cyclically by three distinct quotient faces have
zero total coordinate in every facial-boundary linear combination. -/
theorem orbitFaceBoundaryLinearMap_apply_sum_eq_zero_of_face_triangle
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    {firstFace secondFace thirdFace : OrbitFace RS}
    (hfirstSecond : firstFace ≠ secondFace)
    (hsecondThird : secondFace ≠ thirdFace)
    (hthirdFirst : thirdFace ≠ firstFace)
    {firstEdge secondEdge thirdEdge : E}
    (hfirstEdgeFirst : firstEdge ∈ orbitFaceBoundary RS firstFace)
    (hfirstEdgeSecond : firstEdge ∈ orbitFaceBoundary RS secondFace)
    (hsecondEdgeSecond : secondEdge ∈ orbitFaceBoundary RS secondFace)
    (hsecondEdgeThird : secondEdge ∈ orbitFaceBoundary RS thirdFace)
    (hthirdEdgeThird : thirdEdge ∈ orbitFaceBoundary RS thirdFace)
    (hthirdEdgeFirst : thirdEdge ∈ orbitFaceBoundary RS firstFace)
    (coefficients : OrbitFace RS → F2) :
    orbitFaceBoundaryLinearMap RS coefficients firstEdge +
        orbitFaceBoundaryLinearMap RS coefficients secondEdge +
        orbitFaceBoundaryLinearMap RS coefficients thirdEdge = 0 := by
  have hfirstIncident := orbitFace_incidentFaces_eq_pair_of_mem
    RS htwoSided hfirstSecond firstEdge hfirstEdgeFirst hfirstEdgeSecond
  have hsecondIncident := orbitFace_incidentFaces_eq_pair_of_mem
    RS htwoSided hsecondThird secondEdge hsecondEdgeSecond hsecondEdgeThird
  have hthirdIncident := orbitFace_incidentFaces_eq_pair_of_mem
    RS htwoSided hthirdFirst thirdEdge hthirdEdgeThird hthirdEdgeFirst
  have hfirstValue :
      orbitFaceBoundaryLinearMap RS coefficients firstEdge =
        coefficients firstFace + coefficients secondFace := by
    rw [orbitFaceBoundaryLinearMap_apply]
    calc
      (∑ face : OrbitFace RS,
          if firstEdge ∈ orbitFaceBoundary RS face then
            coefficients face else 0) =
          ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
            firstEdge ∈ orbitFaceBoundary RS face), coefficients face := by
          rw [Finset.sum_filter]
      _ = ∑ face ∈ ({firstFace, secondFace} : Finset (OrbitFace RS)),
          coefficients face := by rw [hfirstIncident]
      _ = coefficients firstFace + coefficients secondFace := by
          simp [hfirstSecond]
  have hsecondValue :
      orbitFaceBoundaryLinearMap RS coefficients secondEdge =
        coefficients secondFace + coefficients thirdFace := by
    rw [orbitFaceBoundaryLinearMap_apply]
    calc
      (∑ face : OrbitFace RS,
          if secondEdge ∈ orbitFaceBoundary RS face then
            coefficients face else 0) =
          ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
            secondEdge ∈ orbitFaceBoundary RS face), coefficients face := by
          rw [Finset.sum_filter]
      _ = ∑ face ∈ ({secondFace, thirdFace} : Finset (OrbitFace RS)),
          coefficients face := by rw [hsecondIncident]
      _ = coefficients secondFace + coefficients thirdFace := by
          simp [hsecondThird]
  have hthirdValue :
      orbitFaceBoundaryLinearMap RS coefficients thirdEdge =
        coefficients thirdFace + coefficients firstFace := by
    rw [orbitFaceBoundaryLinearMap_apply]
    calc
      (∑ face : OrbitFace RS,
          if thirdEdge ∈ orbitFaceBoundary RS face then
            coefficients face else 0) =
          ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
            thirdEdge ∈ orbitFaceBoundary RS face), coefficients face := by
          rw [Finset.sum_filter]
      _ = ∑ face ∈ ({thirdFace, firstFace} : Finset (OrbitFace RS)),
          coefficients face := by rw [hthirdIncident]
      _ = coefficients thirdFace + coefficients firstFace := by
          simp [hthirdFirst]
  rw [hfirstValue, hsecondValue, hthirdValue]
  simp [add_left_comm, add_comm]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every graph cycle meets a three-edge dual triangle with even parity. -/
theorem f2CycleSpace_apply_sum_eq_zero_of_face_triangle
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {firstFace secondFace thirdFace :
      OrbitFace data.toRotationSystem}
    (hfirstSecond : firstFace ≠ secondFace)
    (hsecondThird : secondFace ≠ thirdFace)
    (hthirdFirst : thirdFace ≠ firstFace)
    {firstEdge secondEdge thirdEdge : G.edgeSet}
    (hfirstEdgeFirst : firstEdge ∈
      orbitFaceBoundary data.toRotationSystem firstFace)
    (hfirstEdgeSecond : firstEdge ∈
      orbitFaceBoundary data.toRotationSystem secondFace)
    (hsecondEdgeSecond : secondEdge ∈
      orbitFaceBoundary data.toRotationSystem secondFace)
    (hsecondEdgeThird : secondEdge ∈
      orbitFaceBoundary data.toRotationSystem thirdFace)
    (hthirdEdgeThird : thirdEdge ∈
      orbitFaceBoundary data.toRotationSystem thirdFace)
    (hthirdEdgeFirst : thirdEdge ∈
      orbitFaceBoundary data.toRotationSystem firstFace)
    {cycle : G.edgeSet → F2} (hcycle : cycle ∈ f2CycleSpace G) :
    cycle firstEdge + cycle secondEdge + cycle thirdEdge = 0 := by
  have hspan : cycle ∈ LinearMap.range
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact hcycle
  rcases hspan with ⟨coefficients, rfl⟩
  exact orbitFaceBoundaryLinearMap_apply_sum_eq_zero_of_face_triangle
    data.toRotationSystem htwoSided hfirstSecond hsecondThird hthirdFirst
    hfirstEdgeFirst hfirstEdgeSecond hsecondEdgeSecond hsecondEdgeThird
    hthirdEdgeThird hthirdEdgeFirst coefficients

/-- A three-edge dual triangle is a primal edge separator. -/
theorem not_connected_deleteEdges_triple_of_face_triangle
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {firstFace secondFace thirdFace :
      OrbitFace data.toRotationSystem}
    (hfirstSecond : firstFace ≠ secondFace)
    (hsecondThird : secondFace ≠ thirdFace)
    (hthirdFirst : thirdFace ≠ firstFace)
    {firstEdge secondEdge thirdEdge : G.edgeSet}
    (hfirstSecondEdge : firstEdge ≠ secondEdge)
    (hfirstThirdEdge : firstEdge ≠ thirdEdge)
    (hfirstEdgeFirst : firstEdge ∈
      orbitFaceBoundary data.toRotationSystem firstFace)
    (hfirstEdgeSecond : firstEdge ∈
      orbitFaceBoundary data.toRotationSystem secondFace)
    (hsecondEdgeSecond : secondEdge ∈
      orbitFaceBoundary data.toRotationSystem secondFace)
    (hsecondEdgeThird : secondEdge ∈
      orbitFaceBoundary data.toRotationSystem thirdFace)
    (hthirdEdgeThird : thirdEdge ∈
      orbitFaceBoundary data.toRotationSystem thirdFace)
    (hthirdEdgeFirst : thirdEdge ∈
      orbitFaceBoundary data.toRotationSystem firstFace) :
    ¬ (G.deleteEdges
      ({firstEdge.1, secondEdge.1, thirdEdge.1} : Set (Sym2 V))).Connected := by
  intro hdeleteConnected
  rcases data.toRotationSystem.dartsOn_nonempty firstEdge with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = firstEdge :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hdartEdgeValue : dart.edge = firstEdge.1 :=
    congrArg Subtype.val hdartEdge
  rcases hdeleteConnected dart.snd dart.fst with ⟨returnWalkDeleted⟩
  let returnWalk : G.Walk dart.snd dart.fst :=
    returnWalkDeleted.mapLe
      (G.deleteEdges_le
        ({firstEdge.1, secondEdge.1, thirdEdge.1} : Set (Sym2 V)))
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le
        ({firstEdge.1, secondEdge.1, thirdEdge.1} : Set (Sym2 V)))
  have hreturnAvoidFirst : firstEdge.1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    simp at hdeleted
  have hreturnAvoidSecond : secondEdge.1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    simp at hdeleted
  have hreturnAvoidThird : thirdEdge.1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    simp at hdeleted
  let closedWalk : G.Walk dart.fst dart.fst :=
    Walk.cons dart.adj returnWalk
  have hcycle : walkEdgeParity closedWalk ∈ f2CycleSpace G :=
    walkEdgeParity_mem_f2CycleSpace_of_closed closedWalk
  have hcoordinates := f2CycleSpace_apply_sum_eq_zero_of_face_triangle
    data htwoSided hdual hconnected hsphere hfirstSecond hsecondThird
    hthirdFirst hfirstEdgeFirst hfirstEdgeSecond hsecondEdgeSecond
    hsecondEdgeThird hthirdEdgeThird hthirdEdgeFirst hcycle
  have hfirstCoordinate : walkEdgeParity closedWalk firstEdge = 1 := by
    have hreturnCount : returnWalk.edges.count firstEdge.1 = 0 :=
      List.count_eq_zero.2 hreturnAvoidFirst
    have hdartPairValue : s(dart.fst, dart.snd) = firstEdge.1 :=
      hdartEdgeValue
    change ((List.count firstEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 1
    simp [hdartPairValue, hreturnCount]
  have hdartPairNeSecond : s(dart.fst, dart.snd) ≠ secondEdge.1 := by
    intro heq
    apply hfirstSecondEdge
    apply Subtype.ext
    exact hdartEdgeValue.symm.trans heq
  have hsecondCoordinate : walkEdgeParity closedWalk secondEdge = 0 := by
    have hreturnCount : returnWalk.edges.count secondEdge.1 = 0 :=
      List.count_eq_zero.2 hreturnAvoidSecond
    change ((List.count secondEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [hdartPairNeSecond, hreturnCount]
  have hdartPairNeThird : s(dart.fst, dart.snd) ≠ thirdEdge.1 := by
    intro heq
    apply hfirstThirdEdge
    apply Subtype.ext
    exact hdartEdgeValue.symm.trans heq
  have hthirdCoordinate : walkEdgeParity closedWalk thirdEdge = 0 := by
    have hreturnCount : returnWalk.edges.count thirdEdge.1 = 0 :=
      List.count_eq_zero.2 hreturnAvoidThird
    change ((List.count thirdEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [hdartPairNeThird, hreturnCount]
  rw [hfirstCoordinate, hsecondCoordinate, hthirdCoordinate] at hcoordinates
  exact one_ne_zero hcoordinates

end

end GoertzelV24SharedFacesThreeEdgeSeparator

end Mettapedia.GraphTheory.FourColor
