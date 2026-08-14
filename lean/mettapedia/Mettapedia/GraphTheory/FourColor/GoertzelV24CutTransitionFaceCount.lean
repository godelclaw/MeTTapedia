import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder

/-!
# Exact touched-face count from unique boundary occurrence

For a finite vertex cut, send each retained boundary dart to its ambient
facial orbit.  If every touched face contains a unique retained boundary dart,
this map is an equivalence onto the touched-face carrier.  Consequently the
number of touched ambient faces is exactly the number of crossing edges.

This is generic rotation-system counting.  It neither supplies the uniqueness
hypothesis nor asserts an Euler formula for an opened region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CutTransitionFaceCount

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The ambient touched face containing one retained boundary dart. -/
def boundaryDartTransitionFace
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundary : BoundaryDart RS (deletedRegionKeep deleted)) :
    {face : OrbitFace RS // face ∈ cutSideTransitionFaces RS deleted} := by
  refine ⟨dartOrbitFace RS boundary.1.1, ?_⟩
  rw [mem_cutSideTransitionFaces_iff]
  refine ⟨boundary.1.1, ?_⟩
  rw [mem_orbitFaceSideTransitionDarts_iff]
  refine ⟨rfl, ?_⟩
  intro heq
  apply boundary.2
  rw [← RS.vert_phi_eq_vert_alpha]
  exact heq.mp boundary.1.2

/-- Unique retained boundary occurrence identifies the boundary carrier with
the touched quotient-face carrier. -/
def boundaryDartEquivTransitionFace
    (RS : RotationSystem V E) (deleted : Finset V)
    (hunique : CutFacesHaveUniqueRetainedBoundaryDart RS deleted) :
    BoundaryDart RS (deletedRegionKeep deleted) ≃
      {face : OrbitFace RS // face ∈ cutSideTransitionFaces RS deleted} :=
  Equiv.ofBijective (boundaryDartTransitionFace RS deleted) <| by
    constructor
    · intro left right heq
      apply hunique left right
      have hfaces := congrArg Subtype.val heq
      change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) left.1.1 =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) right.1.1 at hfaces
      exact Quotient.exact hfaces
    · rintro ⟨face, hface⟩
      rcases exists_dartOrbitFace_eq RS face with ⟨root, rfl⟩
      have htransitionNonempty :
          (faceSideTransitionDarts RS (deletedRegionKeep deleted) root).Nonempty := by
        rw [← orbitFaceSideTransitionDarts_dartOrbitFace]
        exact (mem_cutSideTransitionFaces_iff RS deleted
          (dartOrbitFace RS root)).mp hface
      have htransitionPositive :
          0 < (faceSideTransitionDarts RS
            (deletedRegionKeep deleted) root).card :=
        Finset.card_pos.mpr htransitionNonempty
      have hexitPositive :
          0 < (faceSideExitDarts RS
            (deletedRegionKeep deleted) root).card := by
        rw [card_faceSideTransitionDarts_eq_twice_exitDarts] at htransitionPositive
        omega
      rcases Finset.card_pos.mp hexitPositive with ⟨dart, hdartExit⟩
      have hdartData := Finset.mem_sdiff.mp hdartExit
      have hcurrent := (mem_faceSideCurrentDarts_iff RS
        (deletedRegionKeep deleted) root dart).mp hdartData.1
      have halphaNot :
          ¬ deletedRegionKeep deleted (RS.vertOf (RS.alpha dart)) := by
        intro halpha
        apply hdartData.2
        rw [mem_faceSideNextDarts_iff]
        exact ⟨hcurrent.1, by
          rw [RS.vert_phi_eq_vert_alpha]
          exact halpha⟩
      let boundary : BoundaryDart RS (deletedRegionKeep deleted) :=
        ⟨⟨dart, hcurrent.2⟩, halphaNot⟩
      refine ⟨boundary, ?_⟩
      apply Subtype.ext
      apply Quotient.sound
      exact ((RS.mem_faceOrbit).mp hcurrent.1).symm

/-- Under unique retained occurrence, touched ambient faces are counted
exactly by the endpoint-computed crossing edges. -/
theorem card_cutSideTransitionFaces_eq_crossingEdges_of_unique
    (RS : RotationSystem V E) (deleted : Finset V)
    (hunique : CutFacesHaveUniqueRetainedBoundaryDart RS deleted) :
    (cutSideTransitionFaces RS deleted).card =
      (vertexSetCrossingEdges RS deleted).card := by
  calc
    (cutSideTransitionFaces RS deleted).card =
        Fintype.card
          {face : OrbitFace RS // face ∈ cutSideTransitionFaces RS deleted} := by
      exact (Fintype.card_coe (cutSideTransitionFaces RS deleted)).symm
    _ = Fintype.card (BoundaryDart RS (deletedRegionKeep deleted)) :=
      Fintype.card_congr (boundaryDartEquivTransitionFace
        RS deleted hunique).symm
    _ = (vertexSetCrossingEdges RS deleted).card :=
      card_boundaryDart_deletedRegionKeep RS deleted

end

end GoertzelV24CutTransitionFaceCount

end Mettapedia.GraphTheory.FourColor
