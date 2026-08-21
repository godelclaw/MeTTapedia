import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFragmentReindexFinite

/-!
# Fragment-reindexing compression of width-two profiles

The occurrence-sensitive boundary fragments of a corridor cut are finite,
but their `Fin` coordinates come from an enumeration rather than geometric
order.  This file maps the existing complete five-field semantic codec into
the finite quotient and computes the bounded carrier used by L7.

Only the presentation choice is forgotten.  No different geometric states
are identified, and no quotient state is asserted reachable by a literal
source Cell.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoFragmentReindexCompression

open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open GoertzelV24WidthTwoPortIncidenceCodec

/-- The complete width-two state with its strand coordinate retained and only
the fragment enumeration forgotten. -/
abbrev WidthTwoFragmentReindexProfile (fragmentCount : Nat) :=
  WidthTwoStrandCode × WidthTwoUnlabelledFragmentPayload fragmentCount

/-- Expand the upper-triangular face code to its complete equivalence
relation. -/
def faceRelationPayload {fragmentCount : Nat}
    (face : FaceEquivalenceCode fragmentCount) :
    WidthTwoFaceRelation fragmentCount :=
  ⟨faceRelation face.1,
    ⟨fun fragment => by simp [faceRelation],
      faceRelation_symmetric face,
      face.2⟩⟩

/-- Forget only the strand coordinate and expose all fragment-indexed data. -/
def fragmentPayloadOfCode {fragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile fragmentCount) :
    WidthTwoFragmentPayload fragmentCount where
  face := faceRelationPayload code.face
  incidence := code.fragmentContainsPort
  cap := code.faceLengthCap

/-- Map a labelled semantic code to the same complete state modulo fragment
enumeration. -/
def compressFragmentReindex {fragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile fragmentCount) :
    WidthTwoFragmentReindexProfile fragmentCount :=
  ⟨code.strand,
    Quotient.mk (fragmentReindexSetoid fragmentCount)
      (fragmentPayloadOfCode code)⟩

/-- Fragment-reindex profiles with a dependent fragment count below a fixed
bound. -/
structure BoundedWidthTwoFragmentReindexProfile
    (faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : WidthTwoFragmentReindexProfile faceFragmentCount.val

deriving instance Fintype for BoundedWidthTwoFragmentReindexProfile

private def boundedWidthTwoFragmentReindexProfileEquiv
    (faceFragmentBound : Nat) :
    BoundedWidthTwoFragmentReindexProfile faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        WidthTwoFragmentReindexProfile faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def boundedWidthTwoFragmentReindexProfileCount
    (faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    24 * Fintype.card
      (WidthTwoUnlabelledFragmentPayload faceFragmentCount.val)

theorem card_boundedWidthTwoFragmentReindexProfile
    (faceFragmentBound : Nat) :
    Fintype.card
        (BoundedWidthTwoFragmentReindexProfile faceFragmentBound) =
      boundedWidthTwoFragmentReindexProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedWidthTwoFragmentReindexProfileEquiv faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_widthTwoStrandCode]
  rfl

theorem boundedWidthTwoFragmentReindexProfileCount_three :
    boundedWidthTwoFragmentReindexProfileCount 3 = 37944 := by
  norm_num [boundedWidthTwoFragmentReindexProfileCount, Fin.sum_univ_succ,
    card_widthTwoUnlabelledFragmentPayload_zero,
    card_widthTwoUnlabelledFragmentPayload_one,
    card_widthTwoUnlabelledFragmentPayload_two,
    card_widthTwoUnlabelledFragmentPayload_three]

/-- The exact quotient carrier through the four-fragment bound used by the
literal serial-prefix word. -/
theorem boundedWidthTwoFragmentReindexProfileCount_four :
    boundedWidthTwoFragmentReindexProfileCount 4 = 105744 := by
  norm_num [boundedWidthTwoFragmentReindexProfileCount, Fin.sum_univ_succ,
    card_widthTwoUnlabelledFragmentPayload_zero,
    card_widthTwoUnlabelledFragmentPayload_one,
    card_widthTwoUnlabelledFragmentPayload_two,
    card_widthTwoUnlabelledFragmentPayload_three,
    card_widthTwoUnlabelledFragmentPayload_four]

/-- Four residue classes force a distance-four repeat in the bounded quotient
carrier. -/
theorem exists_separated_boundedFragmentReindex_eq
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoFragmentReindexProfile faceFragmentBound) :
    ∃ first second : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoFragmentReindexProfile faceFragmentBound × Fin 4 :=
    fun index => (profiles index,
      ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hprofile : profiles first = profiles second := congrArg Prod.fst heq
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      simpa [encode] using hresidue
    apply Fin.ext
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · exact False.elim
          (hseparated first second (by omega) hprofile)
      · exact False.elim
          (hseparated second first (by omega) hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  rw [Fintype.card_fin, Fintype.card_prod,
    card_boundedWidthTwoFragmentReindexProfile, Fintype.card_fin] at hcard
  omega

theorem separated_boundedWidthTwoFragmentReindexProfileCount_three :
    4 * boundedWidthTwoFragmentReindexProfileCount 3 + 1 = 151777 := by
  rw [boundedWidthTwoFragmentReindexProfileCount_three]

theorem separated_boundedWidthTwoFragmentReindexProfileCount_four :
    4 * boundedWidthTwoFragmentReindexProfileCount 4 + 1 = 422977 := by
  rw [boundedWidthTwoFragmentReindexProfileCount_four]

end GoertzelV24WidthTwoFragmentReindexCompression

end Mettapedia.GraphTheory.FourColor
