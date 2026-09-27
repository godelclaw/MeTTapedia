import Mettapedia.GraphTheory.FourColor.FaceIncidence
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceOrbitIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A facial cycle as an equivalence class of darts under the face
permutation. Unlike an edge-set encoding, this retains repeated boundaries
and every facial-cycle occurrence. -/
abbrev OrbitFace (RS : RotationSystem V E) :=
  Quotient (Equiv.Perm.SameCycle.setoid RS.phi)

noncomputable instance orbitFaceFintype (RS : RotationSystem V E) :
    Fintype (OrbitFace RS) :=
  Fintype.ofFinite (OrbitFace RS)

noncomputable instance orbitFaceDecidableEq (RS : RotationSystem V E) :
    DecidableEq (OrbitFace RS) :=
  Classical.decEq (OrbitFace RS)

/-- The facial-cycle class containing a dart. -/
def dartOrbitFace (RS : RotationSystem V E) (dart : RS.D) : OrbitFace RS :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) dart

/-- Advancing by the face permutation does not change the quotient face. -/
theorem dartOrbitFace_phi_eq (RS : RotationSystem V E) (dart : RS.D) :
    dartOrbitFace RS (RS.phi dart) = dartOrbitFace RS dart := by
  apply Quotient.sound
  exact (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
    RS.phi dart).symm

/-- Any finite number of face-permutation steps preserves the quotient
face. -/
theorem dartOrbitFace_phi_iterate_eq
    (RS : RotationSystem V E) (steps : Nat) (dart : RS.D) :
    dartOrbitFace RS ((RS.phi : RS.D → RS.D)^[steps] dart) =
      dartOrbitFace RS dart := by
  induction steps generalizing dart with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (RS.phi dart)).trans (dartOrbitFace_phi_eq RS dart)

/-- Darts belonging to one facial-cycle class. -/
noncomputable def orbitFaceDarts (RS : RotationSystem V E) (face : OrbitFace RS) :
    Finset RS.D :=
  Finset.univ.filter fun dart => dartOrbitFace RS dart = face

@[simp]
theorem mem_orbitFaceDarts_iff (RS : RotationSystem V E)
    (face : OrbitFace RS) (dart : RS.D) :
    dart ∈ orbitFaceDarts RS face ↔ dartOrbitFace RS dart = face := by
  simp [orbitFaceDarts]

theorem exists_dartOrbitFace_eq (RS : RotationSystem V E)
    (face : OrbitFace RS) :
    ∃ dart : RS.D, dartOrbitFace RS dart = face := by
  exact Quotient.mk_surjective face

/-- The quotient fiber at a representative is exactly the existing
`RotationSystem.faceOrbit` finset. -/
theorem orbitFaceDarts_dartOrbitFace_eq_faceOrbit
    (RS : RotationSystem V E) (dart : RS.D) :
    orbitFaceDarts RS (dartOrbitFace RS dart) = RS.faceOrbit dart := by
  ext other
  rw [mem_orbitFaceDarts_iff, RS.mem_faceOrbit]
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) other =
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) dart ↔
    RS.phi.SameCycle dart other
  rw [Quotient.eq]
  exact Equiv.Perm.sameCycle_comm

/-- Edge support of one facial cycle. Repeated visits are deliberately
forgotten here because `FaceIncidence` records boundary support; their
multiplicity remains available in `orbitFaceDarts`. -/
noncomputable def orbitFaceBoundary (RS : RotationSystem V E) (face : OrbitFace RS) :
    Finset E :=
  (orbitFaceDarts RS face).image RS.edgeOf

theorem mem_orbitFaceBoundary_iff (RS : RotationSystem V E)
    (face : OrbitFace RS) (edge : E) :
    edge ∈ orbitFaceBoundary RS face ↔
      ∃ dart ∈ orbitFaceDarts RS face, RS.edgeOf dart = edge := by
  simp [orbitFaceBoundary]

/-- At a representative dart, the orbit-face boundary is the existing
rotation-system face edge set. -/
theorem orbitFaceBoundary_dartOrbitFace_eq_faceEdges
    (RS : RotationSystem V E) (dart : RS.D) :
    orbitFaceBoundary RS (dartOrbitFace RS dart) = RS.faceEdges dart := by
  unfold orbitFaceBoundary RotationSystem.faceEdges
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]

/-- The quotient fibers partition all darts, so their cardinalities sum to
the total dart count. -/
theorem sum_card_orbitFaceDarts_eq_card_darts
    (RS : RotationSystem V E) :
    ∑ face : OrbitFace RS, (orbitFaceDarts RS face).card =
      Fintype.card RS.D := by
  classical
  symm
  change (Finset.univ : Finset RS.D).card =
    ∑ face ∈ (Finset.univ : Finset (OrbitFace RS)),
      (orbitFaceDarts RS face).card
  rw [Finset.card_eq_sum_card_fiberwise
    (f := dartOrbitFace RS) (t := Finset.univ) (by simp)]
  simp [orbitFaceDarts]

/-- Forgetting repeated edge visits cannot increase a facial-cycle length. -/
theorem orbitFaceBoundary_card_le_orbitFaceDarts_card
    (RS : RotationSystem V E) (face : OrbitFace RS) :
    (orbitFaceBoundary RS face).card ≤ (orbitFaceDarts RS face).card := by
  exact Finset.card_image_le

/-- Every edge is incident to at most two facial-cycle classes. This is
derived from the rotation system's two-darts-per-edge law rather than stored
as a face-incidence assumption. -/
theorem orbitFace_totalIncidenceCount_le_two
    (RS : RotationSystem V E) (edge : E) :
    totalIncidenceCount (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2 := by
  classical
  let incidentFaces : Finset (OrbitFace RS) :=
    Finset.univ.filter fun face => edge ∈ orbitFaceBoundary RS face
  let witnessExists : ∀ face : incidentFaces,
      ∃ dart ∈ orbitFaceDarts RS face.1, RS.edgeOf dart = edge :=
    fun face => (mem_orbitFaceBoundary_iff RS face.1 edge).1
      (Finset.mem_filter.1 face.2).2
  let witnessDartValue (face : incidentFaces) : RS.D :=
    Classical.choose (witnessExists face)
  have witnessDartValue_mem_face (face : incidentFaces) :
      witnessDartValue face ∈ orbitFaceDarts RS face.1 :=
    (Classical.choose_spec (witnessExists face)).1
  have witnessDartValue_edge (face : incidentFaces) :
      RS.edgeOf (witnessDartValue face) = edge :=
    (Classical.choose_spec (witnessExists face)).2
  let witnessDart : incidentFaces → {dart // dart ∈ RS.dartsOn edge} :=
    fun face => ⟨witnessDartValue face,
      (RS.mem_dartsOn).2 (witnessDartValue_edge face)⟩
  have hinjective : Function.Injective witnessDart := by
    intro left right hdarts
    have hdartValue : witnessDartValue left = witnessDartValue right :=
      congrArg Subtype.val hdarts
    have hleftFace : dartOrbitFace RS (witnessDartValue left) = left.1 :=
      (mem_orbitFaceDarts_iff RS left.1 _).1
        (witnessDartValue_mem_face left)
    have hrightFace : dartOrbitFace RS (witnessDartValue right) = right.1 :=
      (mem_orbitFaceDarts_iff RS right.1 _).1
        (witnessDartValue_mem_face right)
    apply Subtype.ext
    exact hleftFace.symm.trans ((congrArg (dartOrbitFace RS) hdartValue).trans
      hrightFace)
  have hcard := Fintype.card_le_of_injective witnessDart hinjective
  change incidentFaces.card ≤ 2
  calc
    incidentFaces.card = Fintype.card incidentFaces := by simp
    _ ≤ Fintype.card {dart // dart ∈ RS.dartsOn edge} := hcard
    _ = (RS.dartsOn edge).card := Fintype.card_coe _
    _ = 2 := RS.dartsOn_card_two edge

/-- The orbit-face incidence model satisfies the global at-most-two incidence
hypothesis required by the explicit facial dual. -/
theorem orbitFace_incidence_le_two (RS : RotationSystem V E) :
    ∀ edge,
      totalIncidenceCount (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2 :=
  orbitFace_totalIncidenceCount_le_two RS

end GoertzelV24FaceOrbitIncidence

end Mettapedia.GraphTheory.FourColor
