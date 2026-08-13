import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

/-!
# Untouched faces after deleting one graph edge

The missing-edge framed source is formed from a closed graph by deleting one
edge.  The vertex rotation on the deleted graph was constructed in
`GoertzelV24DeletedEdgeRotation`.  Here that one-step construction is lifted to
complete face cycles: any ambient face orbit avoiding both darts of the removed
edge is carried bijectively to one face orbit of the deleted graph.

This is generic face transport.  It does not choose the source edge, construct
the annular containers, or prove that the source Cell-3 faces avoid the missing
edge.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedEdgeFaceTransport

open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24DeletedEdgeRotation
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24FaceOrbitIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- An ambient face is untouched by deletion when its complete dart orbit
avoids both orientations of the deleted edge. -/
def FaceAvoidsDeletedEdge (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) : Prop :=
  ∀ point, data.toRotationSystem.phi.SameCycle root point →
    point ≠ forwardDart huv ∧ point ≠ reverseDart huv

/-- The ambient face permutation restricted to the chosen complete face
cycle. -/
def ambientFacePerm (data : Data G) (root : G.Dart) :
    Equiv.Perm {point // data.toRotationSystem.phi.SameCycle root point} :=
  data.toRotationSystem.phi.subtypePerm
    (fun _ => Equiv.Perm.sameCycle_apply_right)

@[simp]
theorem ambientFacePerm_val (data : Data G) (root : G.Dart)
    (point : {point // data.toRotationSystem.phi.SameCycle root point}) :
    (ambientFacePerm data root point).1 = data.toRotationSystem.phi point.1 :=
  rfl

/-- A dart on an untouched ambient face, transported to the edge-deleted
graph. -/
def deletedFaceDart (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root)
    (point : {point // data.toRotationSystem.phi.SameCycle root point}) :
    (DeletedEdgeGraph G u v).Dart :=
  (deletedGraphDartEquiv huv).symm
    ⟨point.1, hface point.1 point.2⟩

/-- The root of an untouched ambient face on the deleted graph carrier. -/
def deletedFaceRoot (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    (DeletedEdgeGraph G u v).Dart :=
  deletedFaceDart data huv root hface
    ⟨root, Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩

@[simp]
theorem deletedGraphDartEquiv_deletedFaceDart
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root)
    (point : {point // data.toRotationSystem.phi.SameCycle root point}) :
    (deletedGraphDartEquiv huv
      (deletedFaceDart data huv root hface point)).1 = point.1 :=
  rfl

theorem deletedFaceDart_injective
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    Function.Injective (deletedFaceDart data huv root hface) := by
  intro left right heq
  apply Subtype.ext
  change (left.1 : G.Dart) = right.1
  have hremaining :
      (⟨(left.1 : G.Dart), hface left.1 left.2⟩ : RemainingDart huv) =
        ⟨(right.1 : G.Dart), hface right.1 right.2⟩ := by
    apply (deletedGraphDartEquiv huv).symm.injective
    simpa only [deletedFaceDart] using heq
  exact congrArg (fun dart : RemainingDart huv => dart.1) hremaining

/-- One face step on an untouched face commutes with transporting its dart to
the deleted graph. -/
theorem deletedFaceDart_phi
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root)
    (point : {point // data.toRotationSystem.phi.SameCycle root point}) :
    (deletedEdgeData data huv outer).toRotationSystem.phi
        (deletedFaceDart data huv root hface point) =
      deletedFaceDart data huv root hface (ambientFacePerm data root point) := by
  have hnext : data.toRotationSystem.phi.SameCycle root
      (data.toRotationSystem.phi point.1) :=
    point.2.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        data.toRotationSystem.phi point.1)
  have havoids := hface (data.toRotationSystem.phi point.1) hnext
  apply (deletedGraphDartEquiv huv).injective
  apply Subtype.ext
  simpa only [deletedGraphDartEquiv_deletedFaceDart,
    ambientFacePerm_val] using
    deletedEdgeData_phi_ambient_eq_of_ne data huv outer
      (deletedFaceDart data huv root hface point) havoids.1 havoids.2

/-- Map the complete untouched ambient face cycle into the corresponding
deleted-graph face cycle. -/
def deletedFaceCycleMap
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    {point // data.toRotationSystem.phi.SameCycle root point} →
      {point //
        (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
          (deletedFaceRoot data huv root hface) point} := by
  intro point
  refine ⟨deletedFaceDart data huv root hface point, ?_⟩
  have hsource : (ambientFacePerm data root).SameCycle
      ⟨root, Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩ point :=
    Equiv.Perm.SameCycle.subtypePerm point.2
  rcases hsource.exists_nat_pow_eq with ⟨power, hpower⟩
  have htransport := map_pow_of_map_apply_on_cycle
    (ambientFacePerm data root)
    (deletedEdgeData data huv outer).toRotationSystem.phi
    (deletedFaceDart data huv root hface)
    ⟨root, Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩
    (fun candidate _ =>
      (deletedFaceDart_phi data huv outer root hface candidate).symm)
    power
  rw [hpower] at htransport
  rw [htransport]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl _ (deletedFaceRoot data huv root hface))

theorem deletedFaceCycleMap_injective
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    Function.Injective (deletedFaceCycleMap data huv outer root hface) := by
  intro left right heq
  apply deletedFaceDart_injective data huv root hface
  exact congrArg Subtype.val heq

/-- An untouched ambient face and its face in the edge-deleted graph have
exactly the same complete dart cycle. -/
def deletedFaceCycleEquiv
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    {point // data.toRotationSystem.phi.SameCycle root point} ≃
      {point //
        (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
          (deletedFaceRoot data huv root hface) point} := by
  let map := deletedFaceCycleMap data huv outer root hface
  have hinjective : Function.Injective map :=
    deletedFaceCycleMap_injective data huv outer root hface
  have hcard := card_sameCycle_eq_of_injective_map_apply
    (ambientFacePerm data root)
    (deletedEdgeData data huv outer).toRotationSystem.phi
    (deletedFaceDart data huv root hface)
    (deletedFaceDart_injective data huv root hface)
    ⟨root, Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩
    (fun candidate _ =>
      (deletedFaceDart_phi data huv outer root hface candidate).symm)
  have hsourceAll :
      (Finset.univ.filter fun point =>
        (ambientFacePerm data root).SameCycle
          ⟨root, Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩ point) =
        Finset.univ := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Equiv.Perm.SameCycle.subtypePerm point.2)
  have hcardTypes :
      Fintype.card {point // data.toRotationSystem.phi.SameCycle root point} =
        Fintype.card {point //
          (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
            (deletedFaceRoot data huv root hface) point} := by
    calc
      Fintype.card {point // data.toRotationSystem.phi.SameCycle root point} =
          (Finset.univ.filter fun point =>
            (ambientFacePerm data root).SameCycle
              ⟨root,
                Equiv.Perm.SameCycle.refl data.toRotationSystem.phi root⟩
              point).card := by
        rw [hsourceAll]
        simp
      _ = (Finset.univ.filter fun point =>
          (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
            (deletedFaceRoot data huv root hface) point).card := hcard
      _ = Fintype.card {point //
          (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
            (deletedFaceRoot data huv root hface) point} := by
        rw [Fintype.card_subtype]
  exact Equiv.ofBijective map
    ((Fintype.bijective_iff_injective_and_card map).2
      ⟨hinjective, hcardTypes⟩)

/-- The face class occupied by one untouched ambient face after edge
deletion. -/
def deletedFaceOrbit
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    OrbitFace (deletedEdgeData data huv outer).toRotationSystem :=
  dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem
    (deletedFaceRoot data huv root hface)

@[simp]
theorem deletedGraphDartEquiv_deletedFaceRoot
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root) :
    (deletedGraphDartEquiv huv
      (deletedFaceRoot data huv root hface)).1 = root :=
  rfl

/-- Distinct untouched ambient faces remain distinct after deleting the edge.
The result is derived from the complete cycle equivalence, not from a count of
face classes. -/
theorem deletedFaceOrbit_ne_of_ambient_ne
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (hne : dartOrbitFace data.toRotationSystem leftRoot ≠
      dartOrbitFace data.toRotationSystem rightRoot) :
    deletedFaceOrbit data huv outer leftRoot hleft ≠
      deletedFaceOrbit data huv outer rightRoot hright := by
  intro hdeletedFaces
  have hdeletedCycle :
      (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
        (deletedFaceRoot data huv leftRoot hleft)
        (deletedFaceRoot data huv rightRoot hright) :=
    Quotient.exact hdeletedFaces
  let target : {point //
      (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
        (deletedFaceRoot data huv leftRoot hleft) point} :=
    ⟨deletedFaceRoot data huv rightRoot hright, hdeletedCycle⟩
  rcases (deletedFaceCycleEquiv data huv outer leftRoot hleft).surjective target with
    ⟨source, hsource⟩
  have hambientRoot : (source.1 : G.Dart) = rightRoot := by
    have hdeletedDart :
        deletedFaceDart data huv leftRoot hleft source =
          deletedFaceRoot data huv rightRoot hright :=
      congrArg Subtype.val hsource
    have hambient := congrArg
      (fun dart => (deletedGraphDartEquiv huv dart).1)
      hdeletedDart
    calc
      (source.1 : G.Dart) =
          (deletedGraphDartEquiv huv
            (deletedFaceDart data huv leftRoot hleft source)).1 := by rfl
      _ = (deletedGraphDartEquiv huv
          (deletedFaceRoot data huv rightRoot hright)).1 := hambient
      _ = rightRoot := by rfl
  apply hne
  apply Quotient.sound
  change data.toRotationSystem.phi.SameCycle leftRoot rightRoot
  simpa only [hambientRoot] using source.2

/-- The deleted-graph edge met by one dart of an untouched ambient face. -/
def deletedFaceEdge
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (root : G.Dart) (hface : FaceAvoidsDeletedEdge data huv root)
    (point : {point // data.toRotationSystem.phi.SameCycle root point}) :
    (DeletedEdgeGraph G u v).edgeSet :=
  (deletedEdgeData data huv outer).toRotationSystem.edgeOf
    (deletedFaceDart data huv root hface point)

/-- A shared ambient edge occurrence on two untouched faces remains one shared
edge occurrence in the deleted graph. -/
theorem deletedFaceEdge_eq_of_ambient_edge_eq_two_faces
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (left : {point // data.toRotationSystem.phi.SameCycle leftRoot point})
    (right : {point // data.toRotationSystem.phi.SameCycle rightRoot point})
    (hedge : data.toRotationSystem.edgeOf left.1 =
      data.toRotationSystem.edgeOf right.1) :
    deletedFaceEdge data huv outer leftRoot hleft left =
      deletedFaceEdge data huv outer rightRoot hright right := by
  apply Subtype.ext
  change left.1.edge = right.1.edge
  exact congrArg (fun edge : G.edgeSet => edge.1) hedge

/-- Conversely, deleting an edge does not identify two distinct surviving
ambient edge occurrences. -/
theorem ambient_edge_eq_of_deletedFaceEdge_eq_two_faces
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (left : {point // data.toRotationSystem.phi.SameCycle leftRoot point})
    (right : {point // data.toRotationSystem.phi.SameCycle rightRoot point})
    (hedge : deletedFaceEdge data huv outer leftRoot hleft left =
      deletedFaceEdge data huv outer rightRoot hright right) :
    data.toRotationSystem.edgeOf left.1 =
      data.toRotationSystem.edgeOf right.1 := by
  apply Subtype.ext
  change left.1.edge = right.1.edge
  exact congrArg
    (fun edge : (DeletedEdgeGraph G u v).edgeSet => edge.1) hedge

/-- A shared surviving ambient edge makes the two transported untouched faces
adjacent in the facial dual of the deleted graph. -/
theorem deletedFaceOrbit_adj_of_shared_ambient_edge
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (hne : dartOrbitFace data.toRotationSystem leftRoot ≠
      dartOrbitFace data.toRotationSystem rightRoot)
    (left : {point // data.toRotationSystem.phi.SameCycle leftRoot point})
    (right : {point // data.toRotationSystem.phi.SameCycle rightRoot point})
    (hedge : data.toRotationSystem.edgeOf left.1 =
      data.toRotationSystem.edgeOf right.1) :
    (interiorDualGraph
      (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))).Adj
        ⟨deletedFaceOrbit data huv outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨deletedFaceOrbit data huv outer rightRoot hright, Finset.mem_univ _⟩ := by
  apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))
    (orbitFace_incidence_le_two
      (deletedEdgeData data huv outer).toRotationSystem)
    (deletedFaceOrbit_ne_of_ambient_ne data huv outer
      leftRoot rightRoot hleft hright hne)
  · change deletedFaceEdge data huv outer leftRoot hleft left ∈
      orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem
        (deletedFaceOrbit data huv outer leftRoot hleft)
    rw [mem_orbitFaceBoundary_iff]
    refine ⟨deletedFaceDart data huv leftRoot hleft left, ?_, rfl⟩
    rw [mem_orbitFaceDarts_iff]
    apply Quotient.sound
    exact (deletedFaceCycleMap data huv outer leftRoot hleft left).2.symm
  · change deletedFaceEdge data huv outer leftRoot hleft left ∈
      orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem
        (deletedFaceOrbit data huv outer rightRoot hright)
    rw [deletedFaceEdge_eq_of_ambient_edge_eq_two_faces data huv outer
      leftRoot rightRoot hleft hright left right hedge]
    rw [mem_orbitFaceBoundary_iff]
    refine ⟨deletedFaceDart data huv rightRoot hright right, ?_, rfl⟩
    rw [mem_orbitFaceDarts_iff]
    apply Quotient.sound
    exact (deletedFaceCycleMap data huv outer rightRoot hright right).2.symm

/-- Conversely, every facial-dual adjacency between two transported untouched
faces comes from a shared ambient edge occurrence. -/
theorem exists_shared_ambient_edge_of_deletedFaceOrbit_adj
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (hadj :
      (interiorDualGraph
        (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))).Adj
          ⟨deletedFaceOrbit data huv outer leftRoot hleft, Finset.mem_univ _⟩
          ⟨deletedFaceOrbit data huv outer rightRoot hright, Finset.mem_univ _⟩) :
    ∃ left : {point // data.toRotationSystem.phi.SameCycle leftRoot point},
      ∃ right : {point // data.toRotationSystem.phi.SameCycle rightRoot point},
        data.toRotationSystem.edgeOf left.1 =
          data.toRotationSystem.edgeOf right.1 := by
  rcases (interiorDualGraph_adj_iff
      (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))).1 hadj with
    ⟨_, edge, _, hedgeLeft, hedgeRight⟩
  rw [mem_orbitFaceBoundary_iff] at hedgeLeft hedgeRight
  rcases hedgeLeft with ⟨leftDart, hleftDartFace, hleftEdge⟩
  rcases hedgeRight with ⟨rightDart, hrightDartFace, hrightEdge⟩
  have hleftCycle :
      (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
        (deletedFaceRoot data huv leftRoot hleft) leftDart := by
    rw [mem_orbitFaceDarts_iff] at hleftDartFace
    exact (Quotient.exact hleftDartFace).symm
  have hrightCycle :
      (deletedEdgeData data huv outer).toRotationSystem.phi.SameCycle
        (deletedFaceRoot data huv rightRoot hright) rightDart := by
    rw [mem_orbitFaceDarts_iff] at hrightDartFace
    exact (Quotient.exact hrightDartFace).symm
  rcases (deletedFaceCycleEquiv data huv outer leftRoot hleft).surjective
      ⟨leftDart, hleftCycle⟩ with ⟨left, hleftImage⟩
  rcases (deletedFaceCycleEquiv data huv outer rightRoot hright).surjective
      ⟨rightDart, hrightCycle⟩ with ⟨right, hrightImage⟩
  have hleftImageDart :
      deletedFaceDart data huv leftRoot hleft left = leftDart :=
    congrArg Subtype.val hleftImage
  have hrightImageDart :
      deletedFaceDart data huv rightRoot hright right = rightDart :=
    congrArg Subtype.val hrightImage
  refine ⟨left, right, ?_⟩
  apply ambient_edge_eq_of_deletedFaceEdge_eq_two_faces data huv outer
    leftRoot rightRoot hleft hright left right
  calc
    deletedFaceEdge data huv outer leftRoot hleft left = edge := by
      unfold deletedFaceEdge
      rw [hleftImageDart]
      exact hleftEdge
    _ = deletedFaceEdge data huv outer rightRoot hright right := by
      unfold deletedFaceEdge
      rw [hrightImageDart]
      exact hrightEdge.symm

/-- Exact facial-dual adjacency transport for two distinct untouched faces. -/
theorem deletedFaceOrbit_adj_iff_exists_shared_ambient_edge
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (hne : dartOrbitFace data.toRotationSystem leftRoot ≠
      dartOrbitFace data.toRotationSystem rightRoot) :
    (interiorDualGraph
      (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))).Adj
        ⟨deletedFaceOrbit data huv outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨deletedFaceOrbit data huv outer rightRoot hright, Finset.mem_univ _⟩ ↔
      ∃ left : {point // data.toRotationSystem.phi.SameCycle leftRoot point},
        ∃ right : {point // data.toRotationSystem.phi.SameCycle rightRoot point},
          data.toRotationSystem.edgeOf left.1 =
            data.toRotationSystem.edgeOf right.1 := by
  constructor
  · exact exists_shared_ambient_edge_of_deletedFaceOrbit_adj data huv outer
      leftRoot rightRoot hleft hright
  · rintro ⟨left, right, hedge⟩
    exact deletedFaceOrbit_adj_of_shared_ambient_edge data huv outer
      leftRoot rightRoot hleft hright hne left right hedge

/-- On the family of untouched faces, deleting one edge preserves the
facial-dual adjacency graph exactly. -/
theorem deletedFaceOrbit_adj_iff_ambientFaceOrbit_adj
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (leftRoot rightRoot : G.Dart)
    (hleft : FaceAvoidsDeletedEdge data huv leftRoot)
    (hright : FaceAvoidsDeletedEdge data huv rightRoot)
    (hne : dartOrbitFace data.toRotationSystem leftRoot ≠
      dartOrbitFace data.toRotationSystem rightRoot) :
    (interiorDualGraph
      (orbitFaceBoundary (deletedEdgeData data huv outer).toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace (deletedEdgeData data huv outer).toRotationSystem))).Adj
        ⟨deletedFaceOrbit data huv outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨deletedFaceOrbit data huv outer rightRoot hright, Finset.mem_univ _⟩ ↔
      (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
          ⟨dartOrbitFace data.toRotationSystem leftRoot, Finset.mem_univ _⟩
          ⟨dartOrbitFace data.toRotationSystem rightRoot, Finset.mem_univ _⟩ := by
  rw [deletedFaceOrbit_adj_iff_exists_shared_ambient_edge data huv outer
    leftRoot rightRoot hleft hright hne]
  constructor
  · rintro ⟨left, right, hedge⟩
    apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hne
    · rw [mem_orbitFaceBoundary_iff]
      exact ⟨left.1, by
        rw [mem_orbitFaceDarts_iff]
        exact Quotient.sound left.2.symm, rfl⟩
    · rw [mem_orbitFaceBoundary_iff]
      exact ⟨right.1, by
        rw [mem_orbitFaceDarts_iff]
        exact Quotient.sound right.2.symm, hedge.symm⟩
  · intro hadj
    rcases (interiorDualGraph_adj_iff
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))).1 hadj with
      ⟨_, edge, _, hedgeLeft, hedgeRight⟩
    rw [mem_orbitFaceBoundary_iff] at hedgeLeft hedgeRight
    rcases hedgeLeft with ⟨leftDart, hleftDart, hleftEdge⟩
    rcases hedgeRight with ⟨rightDart, hrightDart, hrightEdge⟩
    have hleftCycle : data.toRotationSystem.phi.SameCycle
        leftRoot leftDart := by
      rw [mem_orbitFaceDarts_iff] at hleftDart
      exact Quotient.exact hleftDart.symm
    have hrightCycle : data.toRotationSystem.phi.SameCycle
        rightRoot rightDart := by
      rw [mem_orbitFaceDarts_iff] at hrightDart
      exact Quotient.exact hrightDart.symm
    exact ⟨⟨leftDart, hleftCycle⟩, ⟨rightDart, hrightCycle⟩,
      hleftEdge.trans hrightEdge.symm⟩

end

end GoertzelV24DeletedEdgeFaceTransport

end Mettapedia.GraphTheory.FourColor
