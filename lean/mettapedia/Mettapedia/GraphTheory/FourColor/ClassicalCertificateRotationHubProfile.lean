import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationPattern
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargingHubcapJoin
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

/-!
# Rotation-system realization of presentation hub profiles

The five arities in a presentation sector are the face sizes at the spoke,
hat, and three possible fans in the second neighborhood of a rooted face.
This file reads those darts directly from the edge and face permutations and
assembles their cyclic profile around the actual facial orbit.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRotationHubProfile

open ClassicalCertificatePresentationPattern
open ClassicalCertificateDischargingScore
open ClassicalCertificateDischargingHubcapJoin
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Facial arity counted with the multiplicity of actual dart visits. -/
def faceArity (RS : RotationSystem V E) (dart : RS.D) : Nat :=
  (RS.faceOrbit dart).card

/-- The dart naming one of the five standard locations in the sector based
at a hub dart. -/
def sectorLocationDart (RS : RotationSystem V E)
    (location : Location) (hubDart : RS.D) : RS.D :=
  match location with
  | .spoke => RS.alpha hubDart
  | .hat =>
      RS.alpha ((RS.phi : RS.D → RS.D)^[2] (RS.alpha hubDart))
  | .fan1 =>
      RS.alpha ((RS.phi : RS.D → RS.D)^[3] (RS.alpha hubDart))
  | .fan2 =>
      RS.alpha ((RS.phi : RS.D → RS.D)^[4] (RS.alpha hubDart))
  | .fan3 =>
      RS.alpha ((RS.phi : RS.D → RS.D)^[5] (RS.alpha hubDart))

@[simp] theorem sectorLocationDart_spoke
    (RS : RotationSystem V E) (hubDart : RS.D) :
    sectorLocationDart RS .spoke hubDart = RS.alpha hubDart :=
  rfl

@[simp] theorem sectorLocationDart_hat
    (RS : RotationSystem V E) (hubDart : RS.D) :
    sectorLocationDart RS .hat hubDart =
      RS.alpha ((RS.phi : RS.D → RS.D)^[2] (RS.alpha hubDart)) :=
  rfl

@[simp] theorem sectorLocationDart_fan1
    (RS : RotationSystem V E) (hubDart : RS.D) :
    sectorLocationDart RS .fan1 hubDart =
      RS.alpha ((RS.phi : RS.D → RS.D)^[3] (RS.alpha hubDart)) :=
  rfl

@[simp] theorem sectorLocationDart_fan2
    (RS : RotationSystem V E) (hubDart : RS.D) :
    sectorLocationDart RS .fan2 hubDart =
      RS.alpha ((RS.phi : RS.D → RS.D)^[4] (RS.alpha hubDart)) :=
  rfl

@[simp] theorem sectorLocationDart_fan3
    (RS : RotationSystem V E) (hubDart : RS.D) :
    sectorLocationDart RS .fan3 hubDart =
      RS.alpha ((RS.phi : RS.D → RS.D)^[5] (RS.alpha hubDart)) :=
  rfl

/-- The five actual second-neighborhood face sizes in one hub sector. -/
def sectorProfileAt (RS : RotationSystem V E)
    (hubDart : RS.D) : SectorProfile where
  spoke := faceArity RS (sectorLocationDart RS .spoke hubDart)
  hat := faceArity RS (sectorLocationDart RS .hat hubDart)
  fan1 := faceArity RS (sectorLocationDart RS .fan1 hubDart)
  fan2 := faceArity RS (sectorLocationDart RS .fan2 hubDart)
  fan3 := faceArity RS (sectorLocationDart RS .fan3 hubDart)

@[simp] theorem sectorProfileAt_valueAt
    (RS : RotationSystem V E) (hubDart : RS.D) (location : Location) :
    (sectorProfileAt RS hubDart).valueAt location =
      faceArity RS (sectorLocationDart RS location hubDart) := by
  cases location <;> rfl

/-- Rotation-ordered second-neighborhood sectors around a rooted face. -/
def hubProfile (RS : RotationSystem V E) (root : RS.D) : HubProfile :=
  List.ofFn fun position : Fin (RS.faceOrbit root).card =>
    sectorProfileAt RS (faceCycleDart RS root position)

@[simp] theorem hubProfile_length
    (RS : RotationSystem V E) (root : RS.D) :
    (hubProfile RS root).length = (RS.faceOrbit root).card := by
  simp [hubProfile]

/-- The standard free sector accepts exactly the five lower face-size
bounds carried by a valid observed sector. -/
theorem sectorProfile_fits_freeSector
    (profile : SectorProfile) (hvalid : profile.Valid) :
    profile.Fits (Sector.plain FaceRange.free FaceRange.free) := by
  rcases hvalid with ⟨hspoke, hhat, hfan1, hfan2, hfan3⟩
  exact ⟨⟨hspoke, Or.inl rfl⟩, ⟨hhat, Or.inl rfl⟩,
    ⟨hfan1, Or.inl rfl⟩, ⟨hfan2, Or.inl rfl⟩,
    ⟨hfan3, Or.inl rfl⟩⟩

/-- A list of valid observed sectors fits the free pattern of the same
length. -/
theorem fits_free_of_forall_valid
    (profile : HubProfile)
    (hvalid : ∀ sector ∈ profile, sector.Valid) :
    Pattern.Fits profile (Pattern.free profile.length) := by
  induction profile with
  | nil => exact .nil
  | cons sector rest ih =>
      have hhead : sector.Valid := hvalid sector (by simp)
      have htail : ∀ other ∈ rest, other.Valid := by
        intro other hother
        exact hvalid other (by simp [hother])
      change List.Forall₂ SectorProfile.Fits (sector :: rest)
        (List.replicate (rest.length + 1)
          (Sector.plain FaceRange.free FaceRange.free))
      rw [List.replicate_succ]
      exact List.Forall₂.cons
        (sectorProfile_fits_freeSector sector hhead) (ih htail)

/-- A global minimum face size of five makes every observed sector valid. -/
theorem sectorProfileAt_valid_of_minimum
    (RS : RotationSystem V E)
    (hminimum : ∀ dart : RS.D, 5 ≤ faceArity RS dart)
    (hubDart : RS.D) : (sectorProfileAt RS hubDart).Valid := by
  exact ⟨hminimum _, hminimum _, hminimum _, hminimum _, hminimum _⟩

/-- The actual cyclic hub profile is pointwise valid in a pentagonal map. -/
theorem hubProfile_forall_valid_of_minimum
    (RS : RotationSystem V E)
    (hminimum : ∀ dart : RS.D, 5 ≤ faceArity RS dart)
    (root : RS.D) :
    ∀ sector ∈ hubProfile RS root, sector.Valid := by
  intro sector hsector
  rcases List.mem_ofFn.mp hsector with ⟨position, rfl⟩
  exact sectorProfileAt_valid_of_minimum RS hminimum
    (faceCycleDart RS root position)

/-- Every rooted face in a pentagonal rotation system fits the free root
pattern of its actual arity. -/
theorem hubProfile_fits_free_of_minimum
    (RS : RotationSystem V E)
    (hminimum : ∀ dart : RS.D, 5 ≤ faceArity RS dart)
    (root : RS.D) :
    Pattern.Fits (hubProfile RS root)
      (Pattern.free (RS.faceOrbit root).card) := by
  have hfits := fits_free_of_forall_valid (hubProfile RS root)
    (hubProfile_forall_valid_of_minimum RS hminimum root)
  simpa using hfits

/-- Score conservation selects a genuinely observed presentation root of one
of the seven finite hub arities.  This is the exact entry point from a
spherical map into the finite presentation tree. -/
theorem exists_positive_small_hubProfile_fits_free
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int)
    (hnonnegative : ∀ dart : RS.D, 0 ≤ potential dart)
    (hupper : ∀ dart : RS.D, potential dart ≤ 5)
    (hminimum : ∀ dart : RS.D, 5 ≤ faceArity RS dart) :
    ∃ root : RS.D,
      0 < hubScore RS potential root ∧
        5 ≤ (RS.faceOrbit root).card ∧
          (RS.faceOrbit root).card < 12 ∧
            Pattern.Fits (hubProfile RS root)
              (Pattern.free (RS.faceOrbit root).card) := by
  obtain ⟨root, hpositive⟩ := exists_hubScore_pos RS hsphere potential
  refine ⟨root, hpositive, ?_,
    faceOrbit_card_lt_twelve_of_hubScore_pos RS potential
      hnonnegative hupper root hpositive, ?_⟩
  · simpa [faceArity] using hminimum root
  exact hubProfile_fits_free_of_minimum RS hminimum root

end

end ClassicalCertificateRotationHubProfile

end Mettapedia.GraphTheory.FourColor
