import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceTwoSided

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- No facial cycle repeats an underlying edge. This identifies facial-walk
length with boundary-support size. -/
def OrbitFaceBoundarySimple (RS : RotationSystem V E) : Prop :=
  ∀ face : OrbitFace RS,
    (orbitFaceBoundary RS face).card = (orbitFaceDarts RS face).card

/-- Every edge has distinct quotient faces on its two dart sides. This is a
local predicate computed directly from the rotation and face permutation. -/
def OrbitFacesTwoSided (RS : RotationSystem V E) : Prop :=
  ∀ dart : RS.D,
    dartOrbitFace RS dart ≠ dartOrbitFace RS (RS.alpha dart)

/-- Local two-sidedness makes `edgeOf` injective on every quotient facial
cycle, so facial-walk length equals boundary-support size. -/
theorem orbitFaceBoundarySimple_of_twoSided
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS) :
    OrbitFaceBoundarySimple RS := by
  intro face
  unfold orbitFaceBoundary
  apply Finset.card_image_iff.mpr
  intro left hleft right hright hedge
  rcases RS.edge_fiber_two_cases rfl hedge.symm with heq | heq
  · exact heq.symm
  · exfalso
    apply htwoSided left
    have hleftFace : dartOrbitFace RS left = face :=
      (mem_orbitFaceDarts_iff RS face left).1 hleft
    have hrightFace : dartOrbitFace RS right = face :=
      (mem_orbitFaceDarts_iff RS face right).1 hright
    rw [← heq, hleftFace, hrightFace]

/-- Conversely, a simple quotient facial boundary cannot contain both darts
of one edge. Thus boundary simplicity is exactly local edge two-sidedness. -/
theorem twoSided_of_orbitFaceBoundarySimple
    (RS : RotationSystem V E) (hsimple : OrbitFaceBoundarySimple RS) :
    OrbitFacesTwoSided RS := by
  intro dart hsame
  let face := dartOrbitFace RS dart
  have hinjective : Set.InjOn RS.edgeOf (orbitFaceDarts RS face) := by
    apply Finset.card_image_iff.mp
    exact hsimple face
  have hdart : dart ∈ orbitFaceDarts RS face :=
    (mem_orbitFaceDarts_iff RS face dart).2 rfl
  have halpha : RS.alpha dart ∈ orbitFaceDarts RS face :=
    (mem_orbitFaceDarts_iff RS face (RS.alpha dart)).2 hsame.symm
  have heq := hinjective hdart halpha (RS.edge_alpha dart).symm
  exact RS.alpha_fixfree dart heq.symm

theorem orbitFacesTwoSided_iff_boundarySimple
    (RS : RotationSystem V E) :
    OrbitFacesTwoSided RS ↔ OrbitFaceBoundarySimple RS :=
  ⟨orbitFaceBoundarySimple_of_twoSided RS,
    twoSided_of_orbitFaceBoundarySimple RS⟩

/-- Under local two-sidedness, every edge is incident to exactly two quotient
faces in the full facial incidence model. -/
theorem orbitFace_totalIncidenceCount_eq_two_of_twoSided
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (edge : E) :
    totalIncidenceCount (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge = 2 := by
  rcases RS.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hedge : RS.edgeOf dart = edge := (RS.mem_dartsOn).1 hdart
  have hleft : edge ∈ orbitFaceBoundary RS (dartOrbitFace RS dart) := by
    rw [← hedge]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
  have hright : edge ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart)) := by
    rw [← hedge, ← RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)
  have hgt : 1 < totalIncidenceCount (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge := by
    unfold totalIncidenceCount
    rw [Finset.one_lt_card]
    exact ⟨dartOrbitFace RS dart, by simp [hleft],
      dartOrbitFace RS (RS.alpha dart), by simp [hright], htwoSided dart⟩
  have hle := orbitFace_totalIncidenceCount_le_two RS edge
  omega

end GoertzelV24OrbitFaceTwoSided

end Mettapedia.GraphTheory.FourColor
