import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargingScore
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationHubcapCover
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

/-!
# The exact join between discharging scores and hubcap covers

The darts of a facial orbit have a canonical cyclic enumeration from any
chosen root.  In this enumeration the global discharging score is exactly the
hub constant plus the sum of the local sector transfers used by a hubcap.
Thus an accepted linear cover whose local terms are valid makes that hub
nonpositive.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateDischargingHubcapJoin

open scoped BigOperators

open ClassicalCertificateDischargingScore
open ClassicalCertificatePresentationCertificate
open ClassicalCertificatePresentationHubcapCover
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- On the possible hub arities, the presentation constant is precisely ten
times the ordinary facial curvature. -/
theorem hubConstant_eq_ten_mul_six_sub
    {hubSize : Nat} (hminimum : 5 ≤ hubSize) :
    hubConstant hubSize = 10 * ((6 : Int) - (hubSize : Int)) := by
  by_cases hfive : hubSize = 5
  · subst hubSize
    norm_num [hubConstant]
  · have hsix : 6 ≤ hubSize := by omega
    obtain ⟨amount, rfl⟩ := Nat.exists_eq_add_of_le hsix
    rw [hubConstant, show 6 + amount - 5 = amount + 1 by omega]
    simp
    ring

/-- Bounded powers of the face permutation identify the standard finite
index type with the actual dart fiber of the facial orbit. -/
def faceCycleDartEquiv (RS : RotationSystem V E) (root : RS.D) :
    Fin (RS.faceOrbit root).card ≃
      {dart : RS.D // dart ∈ RS.faceOrbit root} :=
  Equiv.ofBijective
    (fun position =>
      ⟨faceCycleDart RS root position,
        faceCycleDart_mem RS root position⟩)
    ⟨by
      intro left right heq
      apply faceCycleDart_injective RS root
      exact congrArg Subtype.val heq,
    by
      intro dart
      obtain ⟨position, hposition, _hunique⟩ :=
        existsUnique_faceCycleDart_eq RS root dart.1 dart.2
      exact ⟨position, Subtype.ext hposition⟩⟩

/-- Reindexing a sum by the canonical facial cycle visits every dart in the
orbit exactly once. -/
theorem sum_faceCycleDart_eq_sum_faceOrbit
    (RS : RotationSystem V E) (root : RS.D) (value : RS.D → Int) :
    (∑ position : Fin (RS.faceOrbit root).card,
        value (faceCycleDart RS root position)) =
      ∑ dart ∈ RS.faceOrbit root, value dart := by
  calc
    (∑ position : Fin (RS.faceOrbit root).card,
        value (faceCycleDart RS root position)) =
        ∑ dart : {dart : RS.D // dart ∈ RS.faceOrbit root},
          value dart.1 := by
      simpa [faceCycleDartEquiv] using
        (Equiv.sum_comp (faceCycleDartEquiv RS root)
          (fun dart : {dart : RS.D // dart ∈ RS.faceOrbit root} =>
            value dart.1))
    _ = ∑ dart ∈ RS.faceOrbit root, value dart := by
      symm
      exact Finset.sum_subtype (RS.faceOrbit root)
        (fun _ => Iff.rfl) value

/-- The local score at a numerical sector, extended by zero outside the
facial cycle. -/
def faceSectorScore (RS : RotationSystem V E)
    (potential : RS.D → Int) (root : RS.D) (sector : Nat) : Int :=
  if hsector : sector < (RS.faceOrbit root).card then
    dartTransfer RS potential
      (faceCycleDart RS root ⟨sector, hsector⟩)
  else 0

/-- The presentation sector sum is the accumulated transfer around the
actual facial orbit. -/
theorem sum_faceSectorScore_eq_orbitFaceTransfer
    (RS : RotationSystem V E) (potential : RS.D → Int) (root : RS.D) :
    (∑ sector ∈ Finset.range (RS.faceOrbit root).card,
        faceSectorScore RS potential root sector) =
      orbitFaceTransfer RS potential (dartOrbitFace RS root) := by
  calc
    (∑ sector ∈ Finset.range (RS.faceOrbit root).card,
        faceSectorScore RS potential root sector) =
        ∑ position : Fin (RS.faceOrbit root).card,
          dartTransfer RS potential (faceCycleDart RS root position) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro sector hsector
      simp [faceSectorScore, Finset.mem_range.mp hsector]
    _ = ∑ dart ∈ RS.faceOrbit root,
        dartTransfer RS potential dart :=
      sum_faceCycleDart_eq_sum_faceOrbit RS root
        (dartTransfer RS potential)
    _ = orbitFaceTransfer RS potential (dartOrbitFace RS root) := by
      unfold orbitFaceTransfer
      rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]

/-- The hubcap expression in cyclic sector coordinates is definitionally the
global score of the rooted facial orbit. -/
theorem hubConstant_add_sum_faceSectorScore_eq_hubScore
    (RS : RotationSystem V E) (potential : RS.D → Int) (root : RS.D)
    (hminimum : 5 ≤ (RS.faceOrbit root).card) :
    hubConstant (RS.faceOrbit root).card +
        ∑ sector ∈ Finset.range (RS.faceOrbit root).card,
          faceSectorScore RS potential root sector =
      hubScore RS potential root := by
  rw [hubConstant_eq_ten_mul_six_sub hminimum,
    sum_faceSectorScore_eq_orbitFaceTransfer]
  unfold hubScore orbitFaceScore
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]

/-- A potential bounded between zero and five transfers at most five units
across any dart. -/
theorem dartTransfer_le_five_of_potential_bounds
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (dart : RS.D) : dartTransfer RS potential dart ≤ 5 := by
  unfold dartTransfer
  have hopposite := hupper (RS.alpha dart)
  have hcurrent := hnonnegative dart
  omega

/-- A facial cycle of length `n` can receive at most `5n` units when the
potential lies between zero and five. -/
theorem orbitFaceTransfer_le_five_mul_card
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (face : OrbitFace RS) :
    orbitFaceTransfer RS potential face ≤
      5 * ((orbitFaceDarts RS face).card : Int) := by
  unfold orbitFaceTransfer
  calc
    (∑ dart ∈ orbitFaceDarts RS face, dartTransfer RS potential dart) ≤
        ∑ _dart ∈ orbitFaceDarts RS face, (5 : Int) := by
      apply Finset.sum_le_sum
      intro dart _hdart
      exact dartTransfer_le_five_of_potential_bounds RS potential
        hnonnegative hupper dart
    _ = 5 * ((orbitFaceDarts RS face).card : Int) := by
      simp [mul_comm]

/-- The classical five-rule potential bound gives the sharp coarse estimate
`score ≤ 60 - 5n` for a hub of length `n`. -/
theorem hubScore_le_sixty_sub_five_mul_faceOrbitCard
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (root : RS.D) :
    hubScore RS potential root ≤
      60 - 5 * ((RS.faceOrbit root).card : Int) := by
  have htransfer := orbitFaceTransfer_le_five_mul_card RS potential
    hnonnegative hupper (dartOrbitFace RS root)
  unfold hubScore orbitFaceScore
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit] at htransfer ⊢
  omega

/-- Every positive hub has one of the presentation arities `5,…,11` once
the nonnegative potential is bounded above by five. -/
theorem faceOrbit_card_lt_twelve_of_hubScore_pos
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (root : RS.D) (hpositive : 0 < hubScore RS potential root) :
    (RS.faceOrbit root).card < 12 := by
  have hscore := hubScore_le_sixty_sub_five_mul_faceOrbitCard RS potential
    hnonnegative hupper root
  have hcardInt : ((RS.faceOrbit root).card : Int) < 12 := by omega
  exact_mod_cast hcardInt

/-- A checked cover together with its genuine local term bounds makes the
corresponding real hub score nonpositive. -/
theorem hubScore_nonpositive_of_coverCheck
    (RS : RotationSystem V E) (potential : RS.D → Int) (root : RS.D)
    (terms : List HubcapTerm)
    (hminimum : 5 ≤ (RS.faceOrbit root).card)
    (hcheck : coverCheck (RS.faceOrbit root).card terms = true)
    (hterms : ∀ term ∈ terms,
      TermBound (faceSectorScore RS potential root) term) :
    hubScore RS potential root ≤ 0 := by
  rw [← hubConstant_add_sum_faceSectorScore_eq_hubScore
    RS potential root hminimum]
  exact hubConstant_add_sum_nonpositive_of_coverCheck hcheck hterms

/-- If every rooted face receives a checked hubcap with valid local bounds,
global score conservation yields an immediate contradiction. -/
theorem false_of_hubcap_cover_at_every_dart
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int)
    (terms : RS.D → List HubcapTerm)
    (hminimum : ∀ root : RS.D, 5 ≤ (RS.faceOrbit root).card)
    (hchecks : ∀ root : RS.D,
      coverCheck (RS.faceOrbit root).card (terms root) = true)
    (hterms : ∀ root : RS.D, ∀ term ∈ terms root,
      TermBound (faceSectorScore RS potential root) term) : False := by
  obtain ⟨root, hpositive⟩ := exists_hubScore_pos RS hsphere potential
  have hnonpositive := hubScore_nonpositive_of_coverCheck RS potential root
    (terms root) (hminimum root) (hchecks root) (hterms root)
  omega

/-- It suffices to certify hubcap bounds for arities below twelve.  The
bounded-potential estimate forces the globally positive hub into that finite
range. -/
theorem false_of_bounded_potential_hubcap_covers
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (terms : RS.D → List HubcapTerm)
    (hminimum : ∀ root : RS.D, 5 ≤ (RS.faceOrbit root).card)
    (hchecks : ∀ root : RS.D, (RS.faceOrbit root).card < 12 →
      coverCheck (RS.faceOrbit root).card (terms root) = true)
    (hterms : ∀ root : RS.D, (RS.faceOrbit root).card < 12 →
      ∀ term ∈ terms root,
        TermBound (faceSectorScore RS potential root) term) : False := by
  obtain ⟨root, hpositive⟩ := exists_hubScore_pos RS hsphere potential
  have hsmall := faceOrbit_card_lt_twelve_of_hubScore_pos RS potential
    hnonnegative hupper root hpositive
  have hnonpositive := hubScore_nonpositive_of_coverCheck RS potential root
    (terms root) (hminimum root) (hchecks root hsmall) (hterms root hsmall)
  omega

end

end ClassicalCertificateDischargingHubcapJoin

end Mettapedia.GraphTheory.FourColor
