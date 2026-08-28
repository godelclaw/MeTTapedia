import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceDualDiameterDichotomy
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeparatedGeodesicLocality

/-!
# A bounded local carrier around a deleted-dual geodesic

The locality lemma says that an unmarked face meeting both sides of a cut in
an `S`-avoiding geodesic can touch the axis only within two steps of that cut.
This file packages the resulting four-face window and counts the boundary
data retained from the window, its unmarked neighbours, and the marked faces.

This is a radius-one carrier only.  It does not bound connectivity information
that may return through material outside the carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeparatedGeodesicLocalCarrier

open GoertzelV24SeparatedGeodesicLocality
open GoertzelV24BoundedDegreePath
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceDualDiameterDichotomy

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

/-- The at-most-four axis indices that can interact across the cut after
position `i`, clipped to an axis whose last index is `L`. -/
def localIndexWindow (i L : ℕ) : Finset ℕ :=
  ({i - 1, i, i + 1, i + 2} : Finset ℕ).filter fun j => j ≤ L

theorem card_localIndexWindow_le_four (i L : ℕ) :
    (localIndexWindow i L).card ≤ 4 := by
  have h₁ := Finset.card_insert_le (i - 1)
    ({i, i + 1, i + 2} : Finset ℕ)
  have h₂ := Finset.card_insert_le i ({i + 1, i + 2} : Finset ℕ)
  have h₃ := Finset.card_insert_le (i + 1) ({i + 2} : Finset ℕ)
  calc
    (localIndexWindow i L).card ≤
        ({i - 1, i, i + 1, i + 2} : Finset ℕ).card :=
      Finset.card_filter_le _ _
    _ ≤ 4 := by
      simp only [Finset.card_singleton] at h₃
      omega

/-- The faces at the four local axis positions. -/
def localAxisFaces (p : ℕ → F) (i L : ℕ) : Finset F :=
  (localIndexWindow i L).image p

theorem card_localAxisFaces_le_four (p : ℕ → F) (i L : ℕ) :
    (localAxisFaces p i L).card ≤ 4 :=
  (Finset.card_image_le.trans (card_localIndexWindow_le_four i L))

/-- An unmarked face retained in the radius-one local carrier. -/
def unmarkedLocalSideFaces (D : SimpleGraph F) [DecidableRel D.Adj]
    (S : Finset F) (p : ℕ → F) (i L : ℕ) : Finset F :=
  ((localAxisFaces p i L).biUnion fun face => D.neighborFinset face) \ S

/-- A side face crosses the cut after `i` when it touches an axis face at or
before `i` and another axis face at or after `i+1`. -/
def CrossesCut (D : SimpleGraph F) (p : ℕ → F) (i L : ℕ) (H : F) : Prop :=
  ∃ a b : ℕ,
    a ≤ i ∧ i + 1 ≤ b ∧ b ≤ L ∧ D.Adj (p a) H ∧ D.Adj H (p b)

/-- Every unmarked face crossing a cut of an `S`-avoiding geodesic belongs to
the four-face local side carrier. -/
theorem crossingSideFace_mem_unmarkedLocalSideFaces
    {D : SimpleGraph F} [DecidableRel D.Adj]
    {S : Finset F} {p : ℕ → F} {i L : ℕ}
    (hp : ∀ k, k ≤ L → p k ∉ (↑S : Set F))
    (hgeo : ∀ a b, a ≤ L → b ≤ L →
      (deleteFaces D (↑S : Set F)).dist (p a) (p b) =
        max a b - min a b)
    {H : F} (hH : H ∉ S) (hcross : CrossesCut D p i L H) :
    H ∈ unmarkedLocalSideFaces D S p i L := by
  rcases hcross with ⟨a, b, hai, hib, hbL, haH, hHb⟩
  have haL : a ≤ L := by omega
  have hab : a ≤ b := by omega
  have hdist := index_dist_le_two hp hgeo
    (H := H) (i := a) (j := b) (by simpa using hH) haL hbL haH hHb
  have hba : b - a ≤ 2 := by
    simpa [Nat.max_eq_right hab, Nat.min_eq_left hab] using hdist
  have hawindow : a ∈ localIndexWindow i L := by
    simp only [localIndexWindow, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · omega
    · exact haL
  have hpamem : p a ∈ localAxisFaces p i L :=
    Finset.mem_image.2 ⟨a, hawindow, rfl⟩
  refine Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨p a, hpamem, ?_⟩, hH⟩
  simpa using haH

/-- Total boundary data retained for a finite set of faces. -/
def boundaryCost (faceBoundary : F → Finset E) (faces : Finset F) : ℕ :=
  ∑ face ∈ faces, (faceBoundary face).card

theorem boundaryCost_le_card_mul (faceBoundary : F → Finset E)
    (faces : Finset F) {B : ℕ}
    (hface : ∀ face ∈ faces, (faceBoundary face).card ≤ B) :
    boundaryCost faceBoundary faces ≤ faces.card * B := by
  calc
    boundaryCost faceBoundary faces
        ≤ ∑ _face ∈ faces, B :=
      Finset.sum_le_sum fun face hmem => hface face hmem
    _ = faces.card * B := by simp [Finset.sum_const]

theorem card_unmarkedLocalSideFaces_le
    (D : SimpleGraph F) [DecidableRel D.Adj]
    (S : Finset F) (p : ℕ → F) (i L B : ℕ)
    (hdegree : ∀ face : F, D.degree face ≤ B) :
    (unmarkedLocalSideFaces D S p i L).card ≤ 4 * B := by
  classical
  have hside : (unmarkedLocalSideFaces D S p i L).card ≤
      ((localAxisFaces p i L).biUnion fun face => D.neighborFinset face).card :=
    Finset.card_le_card Finset.sdiff_subset
  refine hside.trans ?_
  calc
    ((localAxisFaces p i L).biUnion fun face => D.neighborFinset face).card
        ≤ ∑ face ∈ localAxisFaces p i L, (D.neighborFinset face).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _face ∈ localAxisFaces p i L, B :=
      Finset.sum_le_sum fun face _ => by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact hdegree face
    _ = (localAxisFaces p i L).card * B := by
      simp [Finset.sum_const]
    _ ≤ 4 * B := Nat.mul_le_mul_right B (card_localAxisFaces_le_four p i L)

/-- The explicit radius-one carrier cost: complete boundaries of unmarked
local side faces, of the local axis window, and of all marked faces. -/
def localCarrierCost (D : SimpleGraph F) [DecidableRel D.Adj]
    (faceBoundary : F → Finset E) (S : Finset F)
    (p : ℕ → F) (i L : ℕ) : ℕ :=
  boundaryCost faceBoundary (unmarkedLocalSideFaces D S p i L) +
    boundaryCost faceBoundary (localAxisFaces p i L) +
    boundaryCost faceBoundary S

/-- **The local carrier is bounded independently of the axis length.** -/
theorem localCarrierCost_le
    (D : SimpleGraph F) [DecidableRel D.Adj]
    (faceBoundary : F → Finset E) (S : Finset F)
    (p : ℕ → F) (i L B h : ℕ)
    (hdegree : ∀ face : F, D.degree face ≤ B)
    (hface : ∀ face : F, (faceBoundary face).card ≤ B)
    (hmarked : S.card ≤ h) :
    localCarrierCost D faceBoundary S p i L ≤
      4 * B * B + 4 * B + h * B := by
  apply carrier_le
  · exact (boundaryCost_le_card_mul faceBoundary
      (unmarkedLocalSideFaces D S p i L)
      (fun face _ => hface face)).trans
        (Nat.mul_le_mul_right B
          (card_unmarkedLocalSideFaces_le D S p i L B hdegree))
  · exact (boundaryCost_le_card_mul faceBoundary (localAxisFaces p i L)
      (fun face _ => hface face)).trans
        (Nat.mul_le_mul_right B (card_localAxisFaces_le_four p i L))
  · exact (boundaryCost_le_card_mul faceBoundary S
      (fun face _ => hface face)).trans
        (Nat.mul_le_mul_right B hmarked)

/-! ## Quotient-face specialization -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The locality and carrier bound specialized to the full quotient facial
dual of a rotation system.  The first conjunct says that every unmarked face
meeting both sides of the cut is retained; the second gives the explicit
length-independent boundary-data bound. -/
theorem orbitFace_locality_and_carrier_le
    (RS : RotationSystem V E)
    [DecidableRel (fullOrbitFaceDual RS).Adj]
    (B h i L : ℕ)
    (hface : ∀ face : OrbitFace RS,
      (orbitFaceBoundary RS face).card ≤ B)
    (S : Finset (AmbientFace (Finset.univ : Finset (OrbitFace RS))))
    (hmarked : S.card ≤ h)
    (p : ℕ → AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (hp : ∀ k, k ≤ L → p k ∉ (↑S : Set _))
    (hgeo : ∀ a b, a ≤ L → b ≤ L →
      (deleteFaces (fullOrbitFaceDual RS) (↑S : Set _)).dist (p a) (p b) =
        max a b - min a b) :
    (∀ H, H ∉ S → CrossesCut (fullOrbitFaceDual RS) p i L H →
      H ∈ unmarkedLocalSideFaces (fullOrbitFaceDual RS) S p i L) ∧
      localCarrierCost (fullOrbitFaceDual RS)
        (fun face => orbitFaceBoundary RS face.1) S p i L ≤
          4 * B * B + 4 * B + h * B := by
  classical
  constructor
  · intro H hH hcross
    exact crossingSideFace_mem_unmarkedLocalSideFaces hp hgeo hH hcross
  · apply localCarrierCost_le
    · intro face
      exact (interiorDualGraph_degree_le_faceBoundary_card
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_totalIncidenceCount_le_two RS) face).trans
          (hface face.1)
    · intro face
      exact hface face.1
    · exact hmarked

end GoertzelV24SeparatedGeodesicLocalCarrier

end Mettapedia.GraphTheory.FourColor
