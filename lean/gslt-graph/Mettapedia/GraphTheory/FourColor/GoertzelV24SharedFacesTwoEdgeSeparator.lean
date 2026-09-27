import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SharedFacesTwoEdgeSeparator

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- If two distinct quotient faces are both incident to an edge, they are the
complete pair of quotient faces incident to that edge. -/
theorem orbitFace_incidentFaces_eq_pair_of_mem
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    {left right : OrbitFace RS} (hfaces : left ≠ right) (edge : E)
    (hleft : edge ∈ orbitFaceBoundary RS left)
    (hright : edge ∈ orbitFaceBoundary RS right) :
    (Finset.univ.filter fun face : OrbitFace RS =>
      edge ∈ orbitFaceBoundary RS face) = {left, right} := by
  let incidentFaces := Finset.univ.filter fun face : OrbitFace RS =>
    edge ∈ orbitFaceBoundary RS face
  have hsubset : ({left, right} : Finset (OrbitFace RS)) ⊆ incidentFaces := by
    intro face hface
    simp only [Finset.mem_insert, Finset.mem_singleton] at hface
    rcases hface with rfl | rfl <;> simp [incidentFaces, hleft, hright]
  have hincidentCard : incidentFaces.card = 2 :=
    orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided edge
  have hpairCard : ({left, right} : Finset (OrbitFace RS)).card = 2 := by
    simp [hfaces]
  change incidentFaces = {left, right}
  apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
  rw [hincidentCard, hpairCard]

/-- Any facial-boundary linear combination has equal coefficients on two
edges shared by the same two distinct quotient faces. -/
theorem orbitFaceBoundaryLinearMap_apply_eq_of_shared_face_pair
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    {left right : OrbitFace RS} (hfaces : left ≠ right)
    {first second : E}
    (hfirstLeft : first ∈ orbitFaceBoundary RS left)
    (hfirstRight : first ∈ orbitFaceBoundary RS right)
    (hsecondLeft : second ∈ orbitFaceBoundary RS left)
    (hsecondRight : second ∈ orbitFaceBoundary RS right)
    (coefficients : OrbitFace RS → F2) :
    orbitFaceBoundaryLinearMap RS coefficients first =
      orbitFaceBoundaryLinearMap RS coefficients second := by
  rw [orbitFaceBoundaryLinearMap_apply,
    orbitFaceBoundaryLinearMap_apply]
  calc
    (∑ face : OrbitFace RS,
        if first ∈ orbitFaceBoundary RS face then coefficients face else 0) =
        ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
          first ∈ orbitFaceBoundary RS face), coefficients face := by
      rw [Finset.sum_filter]
    _ = ∑ face ∈ ({left, right} : Finset (OrbitFace RS)),
        coefficients face := by
      rw [orbitFace_incidentFaces_eq_pair_of_mem RS htwoSided
        hfaces first hfirstLeft hfirstRight]
    _ = ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
          second ∈ orbitFaceBoundary RS face), coefficients face := by
      rw [orbitFace_incidentFaces_eq_pair_of_mem RS htwoSided
        hfaces second hsecondLeft hsecondRight]
    _ = ∑ face : OrbitFace RS,
        if second ∈ orbitFaceBoundary RS face then coefficients face else 0 := by
      rw [Finset.sum_filter]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every graph cycle has equal coefficients on two edges shared by the same
two distinct quotient faces of a cellular sphere rotation. -/
theorem f2CycleSpace_apply_eq_of_shared_face_pair
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {left right : OrbitFace data.toRotationSystem} (hfaces : left ≠ right)
    {first second : G.edgeSet}
    (hfirstLeft : first ∈ orbitFaceBoundary data.toRotationSystem left)
    (hfirstRight : first ∈ orbitFaceBoundary data.toRotationSystem right)
    (hsecondLeft : second ∈ orbitFaceBoundary data.toRotationSystem left)
    (hsecondRight : second ∈ orbitFaceBoundary data.toRotationSystem right)
    {cycle : G.edgeSet → F2} (hcycle : cycle ∈ f2CycleSpace G) :
    cycle first = cycle second := by
  have hspan : cycle ∈ LinearMap.range
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact hcycle
  rcases hspan with ⟨coefficients, rfl⟩
  exact orbitFaceBoundaryLinearMap_apply_eq_of_shared_face_pair
    data.toRotationSystem htwoSided hfaces
    hfirstLeft hfirstRight hsecondLeft hsecondRight coefficients

/-- Two distinct edges shared by the same two distinct quotient faces form an
edge separator: deleting both edges disconnects the underlying graph. -/
theorem not_connected_deleteEdges_pair_of_shared_face_pair
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {left right : OrbitFace data.toRotationSystem} (hfaces : left ≠ right)
    {first second : G.edgeSet} (hedges : first ≠ second)
    (hfirstLeft : first ∈ orbitFaceBoundary data.toRotationSystem left)
    (hfirstRight : first ∈ orbitFaceBoundary data.toRotationSystem right)
    (hsecondLeft : second ∈ orbitFaceBoundary data.toRotationSystem left)
    (hsecondRight : second ∈ orbitFaceBoundary data.toRotationSystem right) :
    ¬ (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Connected := by
  intro hdeleteConnected
  rcases data.toRotationSystem.dartsOn_nonempty first with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = first :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hdartEdgeValue : dart.edge = first.1 :=
    congrArg Subtype.val hdartEdge
  rcases hdeleteConnected dart.snd dart.fst with ⟨returnWalkDeleted⟩
  let returnWalk : G.Walk dart.snd dart.fst :=
    returnWalkDeleted.mapLe
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  have hreturnAvoidFirst : first.1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    simp at hdeleted
  have hreturnAvoidSecond : second.1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    simp at hdeleted
  let closedWalk : G.Walk dart.fst dart.fst :=
    Walk.cons dart.adj returnWalk
  have hcycle : walkEdgeParity closedWalk ∈ f2CycleSpace G :=
    walkEdgeParity_mem_f2CycleSpace_of_closed closedWalk
  have hcoordinates := f2CycleSpace_apply_eq_of_shared_face_pair
    data htwoSided hdual hconnected hsphere hfaces
    hfirstLeft hfirstRight hsecondLeft hsecondRight hcycle
  have hfirstCoordinate : walkEdgeParity closedWalk first = 1 := by
    have hreturnCount : returnWalk.edges.count first.1 = 0 :=
      List.count_eq_zero.2 hreturnAvoidFirst
    have hdartPairValue : s(dart.fst, dart.snd) = first.1 :=
      hdartEdgeValue
    change ((List.count first.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 1
    simp [List.count_cons, hdartPairValue, hreturnCount]
  have hdartPairNeSecond : s(dart.fst, dart.snd) ≠ second.1 := by
    intro heq
    apply hedges
    apply Subtype.ext
    exact hdartEdgeValue.symm.trans heq
  have hsecondCoordinate : walkEdgeParity closedWalk second = 0 := by
    have hreturnCount : returnWalk.edges.count second.1 = 0 :=
      List.count_eq_zero.2 hreturnAvoidSecond
    change ((List.count second.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [List.count_cons, hdartPairNeSecond, hreturnCount]
  rw [hfirstCoordinate, hsecondCoordinate] at hcoordinates
  exact one_ne_zero hcoordinates

end

end GoertzelV24SharedFacesTwoEdgeSeparator

end Mettapedia.GraphTheory.FourColor
