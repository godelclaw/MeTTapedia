import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSkeleton
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Fully retained hex corridors survive a literal opening

Lean flag L1 is first classified on the closed minimal map.  The source
corridor is later read in a literal vertex-region opening.  This file proves
the generic formation step between those carriers: a fully retained facial
orbit keeps its boundary size, and a fully retained closed hex corridor
therefore constructs an open hex corridor with the same index set.

Nothing here asserts that a particular source corridor is fully retained.
That remains the source-specific cap/collar separation theorem.  Once that
fact is supplied, however, the open corridor below is computed rather than
postulated.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionHexCorridorTransport

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- **L1 (retained face length).** A fully retained face of a two-sided
ambient rotation system has exactly the same boundary-support cardinality
after a literal vertex-region opening.

The proof does not compare cardinalities heuristically.  It uses the exact
cycle equivalence of the retained face and proves that the open edge map is
injective on that cycle by reflecting edge equality back to the ambient
two-sided face. -/
theorem openFaceOrbit_boundary_card_eq_ambient
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (keep : V → Prop) (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    (orbitFaceBoundary (rotationSystem RS keep outer)
      (openFaceOrbit RS keep outer root hface)).card =
        (orbitFaceBoundary RS (dartOrbitFace RS root)).card := by
  let openRS := rotationSystem RS keep outer
  let openRoot := openFaceRoot RS keep root hface
  have hopenInjective : Set.InjOn openRS.edgeOf
      (orbitFaceDarts openRS (dartOrbitFace openRS openRoot)) := by
    intro left hleft right hright hedge
    have hleftOrbit : left ∈ openRS.faceOrbit openRoot := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit openRS openRoot]
      exact hleft
    have hrightOrbit : right ∈ openRS.faceOrbit openRoot := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit openRS openRoot]
      exact hright
    let leftTarget : {point // openRS.phi.SameCycle openRoot point} :=
      ⟨left, (openRS.mem_faceOrbit).1 hleftOrbit⟩
    let rightTarget : {point // openRS.phi.SameCycle openRoot point} :=
      ⟨right, (openRS.mem_faceOrbit).1 hrightOrbit⟩
    rcases (openFaceCycleEquiv RS keep outer root hface).surjective
        leftTarget with ⟨leftSource, hleftSource⟩
    rcases (openFaceCycleEquiv RS keep outer root hface).surjective
        rightTarget with ⟨rightSource, hrightSource⟩
    have hleftVal : openFaceDart RS keep root hface leftSource = left :=
      congrArg Subtype.val hleftSource
    have hrightVal : openFaceDart RS keep root hface rightSource = right :=
      congrArg Subtype.val hrightSource
    have hopenEdge : openFaceEdge RS keep outer root hface leftSource =
        openFaceEdge RS keep outer root hface rightSource := by
      change (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep root hface leftSource) =
        (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep root hface rightSource)
      rw [hleftVal, hrightVal]
      exact hedge
    have hambientEdge : RS.edgeOf leftSource.1 = RS.edgeOf rightSource.1 :=
      ambient_edge_eq_of_openFaceEdge_eq RS keep outer root hface
        leftSource rightSource hopenEdge
    have hambientSimple := orbitFaceBoundarySimple_of_twoSided RS htwoSided
    have hsourceInjective : Set.InjOn RS.edgeOf
        (orbitFaceDarts RS (dartOrbitFace RS root)) := by
      apply Finset.card_image_iff.mp
      exact hambientSimple (dartOrbitFace RS root)
    have hleftAmbient : leftSource.1 ∈
        orbitFaceDarts RS (dartOrbitFace RS root) := by
      apply (mem_orbitFaceDarts_iff RS _ _).2
      exact (Quotient.sound leftSource.2).symm
    have hrightAmbient : rightSource.1 ∈
        orbitFaceDarts RS (dartOrbitFace RS root) := by
      apply (mem_orbitFaceDarts_iff RS _ _).2
      exact (Quotient.sound rightSource.2).symm
    have hsources : leftSource.1 = rightSource.1 :=
      hsourceInjective hleftAmbient hrightAmbient hambientEdge
    have hsourceEq : leftSource = rightSource := Subtype.ext hsources
    rw [← hleftVal, ← hrightVal, hsourceEq]
  have hopenSimple :
      (orbitFaceBoundary openRS (dartOrbitFace openRS openRoot)).card =
        (orbitFaceDarts openRS (dartOrbitFace openRS openRoot)).card := by
    unfold orbitFaceBoundary
    exact Finset.card_image_iff.mpr hopenInjective
  have hdartCards :
      (orbitFaceDarts openRS (dartOrbitFace openRS openRoot)).card =
        (orbitFaceDarts RS (dartOrbitFace RS root)).card := by
    rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
      orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
    simpa only [RotationSystem.faceOrbit, Fintype.card_subtype] using
      Fintype.card_congr (openFaceCycleEquiv RS keep outer root hface).symm
  change (orbitFaceBoundary openRS
    (dartOrbitFace openRS openRoot)).card = _
  rw [hopenSimple, hdartCards,
    (orbitFaceBoundarySimple_of_twoSided RS htwoSided)
      (dartOrbitFace RS root)]

/-- Choose one ambient dart representative of a quotient face. -/
def orbitFaceRoot (RS : RotationSystem V E) (face : OrbitFace RS) : RS.D :=
  Quotient.out face

@[simp] theorem dartOrbitFace_orbitFaceRoot
    (RS : RotationSystem V E) (face : OrbitFace RS) :
    dartOrbitFace RS (orbitFaceRoot RS face) = face := by
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
    (Quotient.out face) = face
  exact Quotient.out_eq face

/-- **L1 (closed-to-open corridor formation).** A closed hex corridor whose
selected facial orbits all lie completely on the retained side constructs a
literal-open hex corridor of the same length.

The face carrier is not copied by cardinality.  Each face is the exact
`openFaceOrbit` image of its ambient quotient orbit; injectivity and both
adjacency directions follow from the retained-face graph equivalence above.
-/
noncomputable def openOrbitHexCorridorSkeleton
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (keep : V → Prop) (outer : Dart RS keep)
    (hretained : ∀ offset,
      FaceFullyRetained RS keep
        (orbitFaceRoot RS (corridor.faceAt offset).1)) :
    OrbitHexCorridorSkeleton (rotationSystem RS keep outer) corridorLength := {
  faceAt := fun offset =>
    ⟨openFaceOrbit RS keep outer
      (orbitFaceRoot RS (corridor.faceAt offset).1) (hretained offset),
      Finset.mem_univ _⟩
  faceAt_injective := by
    intro left right hfaces
    by_contra hindices
    have hambientNe :
        dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt left).1) ≠
          dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt right).1) := by
      simpa using corridor.faceAt_ne hindices
    exact (openFaceOrbit_ne_of_ambient_ne RS keep outer
      (orbitFaceRoot RS (corridor.faceAt left).1)
      (orbitFaceRoot RS (corridor.faceAt right).1)
      (hretained left) (hretained right) hambientNe)
        (congrArg Subtype.val hfaces)
  hexagonal := by
    intro offset
    rw [openFaceOrbit_boundary_card_eq_ambient RS htwoSided keep outer
      (orbitFaceRoot RS (corridor.faceAt offset).1) (hretained offset)]
    simpa using corridor.hexagonal offset
  consecutive_adjacent := by
    intro left right hsuccessor
    have hambient := corridor.consecutive_adjacent left right hsuccessor
    have hambientNe :
        dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt left).1) ≠
          dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt right).1) := by
      simpa using hambient.ne
    apply (openFaceOrbit_adj_iff_ambientFaceOrbit_adj RS keep outer
      (orbitFaceRoot RS (corridor.faceAt left).1)
      (orbitFaceRoot RS (corridor.faceAt right).1)
      (hretained left) (hretained right) hambientNe).2
    simpa using hambient
  separated_not_adjacent := by
    intro left right hseparated hopen
    have hambientNot := corridor.separated_not_adjacent left right hseparated
    have hindices : left ≠ right := by
      intro heq
      have hvalues := congrArg Fin.val heq
      omega
    have hambientNe :
        dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt left).1) ≠
          dartOrbitFace RS (orbitFaceRoot RS (corridor.faceAt right).1) := by
      simpa using corridor.faceAt_ne hindices
    apply hambientNot
    simpa using (openFaceOrbit_adj_iff_ambientFaceOrbit_adj RS keep outer
      (orbitFaceRoot RS (corridor.faceAt left).1)
      (orbitFaceRoot RS (corridor.faceAt right).1)
      (hretained left) (hretained right) hambientNe).1 hopen
}

end

end GoertzelV24OpenRegionHexCorridorTransport

end Mettapedia.GraphTheory.FourColor
