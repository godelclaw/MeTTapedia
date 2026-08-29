import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitParity

/-!
# Face-ribbon Euler parity

Select finitely many face cycles of a rotation system and restrict the face
permutation to their darts.  It has exactly one orbit for every selected
face.  Gluing selected face sectors across an internal edge is multiplication
by one dart transposition.  Consequently the boundary-orbit count after a
finite list of such gluings is congruent modulo two to

`number of selected faces + number of gluings`.

This is the finite-permutation core of the subsurface Euler identity used in
the Tutte--Kauffman parity proof.  The later colouring-specific adapter only
has to identify the gluing pairs and the resulting boundary walks.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanFaceRibbonParity

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence
open GoertzelV24PermutationOrbitParity
open GoertzelV24PermutationOrbitSurgery

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Darts whose face cycle belongs to a chosen finite face set. -/
abbrev SelectedFaceDart (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :=
  {dart : RS.D // dartOrbitFace RS dart ∈ faces}

/-- The face permutation restricted to the selected face cycles. -/
def selectedFacePerm (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    Perm (SelectedFaceDart RS faces) :=
  RS.phi.subtypePerm (by
    intro dart
    rw [dartOrbitFace_phi_eq])

@[simp]
theorem selectedFacePerm_apply_val (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) (dart : SelectedFaceDart RS faces) :
    ((selectedFacePerm RS faces dart : SelectedFaceDart RS faces) : RS.D) =
      RS.phi dart :=
  rfl

/-- A selected-face-permutation orbit remembers its unique ambient face. -/
def selectedFaceOrbitToFace (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    Quotient (SameCycle.setoid (selectedFacePerm RS faces)) →
      {face : OrbitFace RS // face ∈ faces} :=
  Quotient.lift
    (fun dart : SelectedFaceDart RS faces =>
      ⟨dartOrbitFace RS dart.1, dart.2⟩)
    (by
      intro left right hsame
      apply Subtype.ext
      apply Quotient.sound
      exact (sameCycle_subtypePerm.mp hsame))

theorem selectedFaceOrbitToFace_injective (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    Function.Injective (selectedFaceOrbitToFace RS faces) := by
  intro left right heq
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      apply Quotient.sound
      apply SameCycle.subtypePerm
      exact Quotient.exact (congrArg Subtype.val heq)

theorem selectedFaceOrbitToFace_surjective (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    Function.Surjective (selectedFaceOrbitToFace RS faces) := by
  intro face
  rcases exists_dartOrbitFace_eq RS face.1 with ⟨dart, hdart⟩
  let selectedDart : SelectedFaceDart RS faces :=
    ⟨dart, by simpa [hdart] using face.2⟩
  refine ⟨Quotient.mk _ selectedDart, ?_⟩
  apply Subtype.ext
  exact hdart

/-- The cycles of the restricted face permutation are canonically the
selected quotient faces. -/
def selectedFaceOrbitEquivFace (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    Quotient (SameCycle.setoid (selectedFacePerm RS faces)) ≃
      {face : OrbitFace RS // face ∈ faces} :=
  Equiv.ofBijective (selectedFaceOrbitToFace RS faces)
    ⟨selectedFaceOrbitToFace_injective RS faces,
      selectedFaceOrbitToFace_surjective RS faces⟩

/-- The restricted face permutation has exactly one orbit for each selected
face, including a face that will remain an isolated ribbon component. -/
theorem orbitCount_selectedFacePerm (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    orbitCount (selectedFacePerm RS faces) = faces.card := by
  calc
    orbitCount (selectedFacePerm RS faces) =
        Fintype.card {face : OrbitFace RS // face ∈ faces} := by
      exact Fintype.card_congr (selectedFaceOrbitEquivFace RS faces)
    _ = faces.card := Fintype.card_coe faces

/-- A finite ribbon surgery is a list of nontrivial pairs of selected darts.
Each pair records one internal edge across which two selected face sectors
are glued. -/
structure FaceRibbonSurgery (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) where
  pairs : List (SelectedFaceDart RS faces × SelectedFaceDart RS faces)
  pair_ne : ∀ pair ∈ pairs, pair.1 ≠ pair.2

/-- Boundary successor obtained by performing every recorded face-sector
gluing on the restricted face permutation. -/
def FaceRibbonSurgery.boundaryPerm
    {RS : RotationSystem V E} {faces : Finset (OrbitFace RS)}
    (surgery : FaceRibbonSurgery RS faces) :
    Perm (SelectedFaceDart RS faces) :=
  leftSwapFold surgery.pairs (selectedFacePerm RS faces)

/-- **Face-ribbon Euler parity.**  The number of boundary orbits after the
gluings is congruent to selected faces plus internal gluings modulo two. -/
theorem FaceRibbonSurgery.orbitCount_boundaryPerm_mod_two
    {RS : RotationSystem V E} {faces : Finset (OrbitFace RS)}
    (surgery : FaceRibbonSurgery RS faces) :
    orbitCount surgery.boundaryPerm % 2 =
      (faces.card + surgery.pairs.length) % 2 := by
  rw [FaceRibbonSurgery.boundaryPerm,
    orbitCount_leftSwapFold_mod_two surgery.pairs
      (selectedFacePerm RS faces) surgery.pair_ne,
    orbitCount_selectedFacePerm]

/-- Module-level interface for face-ribbon Euler parity. -/
theorem faceRibbonSurgery_orbitCount_boundaryPerm_mod_two
    {RS : RotationSystem V E} {faces : Finset (OrbitFace RS)}
    (surgery : FaceRibbonSurgery RS faces) :
    orbitCount surgery.boundaryPerm % 2 =
      (faces.card + surgery.pairs.length) % 2 :=
  surgery.orbitCount_boundaryPerm_mod_two

end

end GoertzelV24KauffmanFaceRibbonParity

end Mettapedia.GraphTheory.FourColor
