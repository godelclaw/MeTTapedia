import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit

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

end

end GoertzelV24DeletedEdgeFaceTransport

end Mettapedia.GraphTheory.FourColor
