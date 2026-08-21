import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFragmentReindexCompression

/-!
# Splice compatibility of fragment-reindex compression

The computable quotient is defined independently of the geometric splice
stack.  This module proves that equality in that quotient returns exactly the
fragment permutation accepted by the existing splice interface, while all
five decoded profile fields agree.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoFragmentReindexSplice

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24SpliceUnification
open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoFragmentReindexCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open GoertzelV24WidthTwoPortIncidenceCodec

/-- Fragment-only indexing for the existing splice correspondence. -/
def fragmentIndexing {fragmentCount : Nat}
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    CorridorProfileIndexing 2 0 fragmentCount where
  crossing := Equiv.refl _
  terminal := Equiv.refl _
  fragment := permutation

/-- Equality of the full fragment payload after relabelling reconstructs
equality of the complete decoded five-coordinate profiles after the same
splice indexing. -/
theorem reindex_decodePortIncidence_eq_of_payload
    {fragmentCount : Nat}
    (left right : WidthTwoPortIncidenceProfile fragmentCount)
    (permutation : Equiv.Perm (Fin fragmentCount))
    (hstrand : left.strand = right.strand)
    (hpayload : reindexFragmentPayload (fragmentPayloadOfCode left)
      permutation = fragmentPayloadOfCode right) :
    reindexCorridorCutProfile (decodePortIncidence left)
        (fragmentIndexing permutation) =
      decodePortIncidence right := by
  rw [GoertzelV24CorridorProfile.CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change left.strand.1.1 = right.strand.1.1
    exact congrArg (fun strand : WidthTwoStrandCode => strand.1.1) hstrand
  · funext pair first second
    rcases first with first | first
    · rcases second with second | second
      · change decodeStrandConnected left.strand pair (.inl first) (.inl second) =
          decodeStrandConnected right.strand pair (.inl first) (.inl second)
        rw [hstrand]
      · exact Fin.elim0 second
    · exact Fin.elim0 first
  · funext first second
    have hface := congrArg WidthTwoFragmentPayload.face hpayload
    change faceRelation left.face.1 (permutation first) (permutation second) =
      faceRelation right.face.1 first second
    simpa [reindexFragmentPayload, reindexFaceRelation,
      fragmentPayloadOfCode, faceRelationPayload] using
        congrFun (congrFun (congrArg Subtype.val hface) first) second
  · funext fragment port
    rcases port with port | port
    · have hincidence :=
        congrArg (fun payload => payload.incidence.1) hpayload
      have hrow := congrFun hincidence fragment
      have hrowValue := congrArg Subtype.val hrow
      change (left.fragmentContainsPort.1 (permutation fragment)).1 port =
        (right.fragmentContainsPort.1 fragment).1 port
      simpa [reindexFragmentPayload, reindexPortIncidence,
        fragmentPayloadOfCode] using
          congrFun hrowValue port
    · exact Fin.elim0 port
  · funext fragment
    have hcap := congrArg WidthTwoFragmentPayload.cap hpayload
    have hcapValue :=
      congrArg Subtype.val (congrFun hcap fragment)
    simpa [reindexCorridorCutProfile, decodePortIncidence, fragmentIndexing,
      reindexFragmentPayload, fragmentPayloadOfCode] using hcapValue

/-- The quotient is lossless at the semantic boundary relevant to the splice:
equal quotient states supply an explicit fragment permutation under which the
complete decoded profiles agree. -/
theorem exists_fragmentIndexing_decode_eq_of_compressFragmentReindex_eq
    {fragmentCount : Nat}
    (left right : WidthTwoPortIncidenceProfile fragmentCount)
    (heq : compressFragmentReindex left = compressFragmentReindex right) :
    ∃ permutation : Equiv.Perm (Fin fragmentCount),
      reindexCorridorCutProfile (decodePortIncidence left)
          (fragmentIndexing permutation) =
        decodePortIncidence right := by
  have hstrand : left.strand = right.strand := congrArg Prod.fst heq
  have hquotient :
      (Quotient.mk (fragmentReindexSetoid fragmentCount)
          (fragmentPayloadOfCode left) :
          WidthTwoUnlabelledFragmentPayload fragmentCount) =
        Quotient.mk (fragmentReindexSetoid fragmentCount)
          (fragmentPayloadOfCode right) :=
    congrArg Prod.snd heq
  have hreindex : FragmentReindexEquivalent
      (fragmentPayloadOfCode left) (fragmentPayloadOfCode right) :=
    (fragmentReindexEquivalent_iff_orbitRel _ _).2
      (Quotient.exact hquotient)
  rcases hreindex with ⟨permutation, hpayload⟩
  exact ⟨permutation,
    reindex_decodePortIncidence_eq_of_payload left right permutation
      hstrand hpayload⟩

/-- Forget only the fragment enumeration in an already encoded bounded
profile. -/
def compressFragmentReindexBoundedCode
    {faceFragmentBound : Nat}
    (profile : BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :
    BoundedWidthTwoFragmentReindexProfile faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compressFragmentReindex profile.profile

/-- A separated repeat in the bounded code returns an explicit splice
indexing on the decoded five-field profiles. -/
theorem exists_separated_reindexed_decode_of_boundedCode
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :
    ∃ first second : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1),
      ∃ fragmentCount : Fin (faceFragmentBound + 1),
      ∃ left right : WidthTwoPortIncidenceProfile fragmentCount.val,
        first.val + 3 < second.val ∧
        profiles first = ⟨fragmentCount, left⟩ ∧
        profiles second = ⟨fragmentCount, right⟩ ∧
        ∃ permutation : Equiv.Perm (Fin fragmentCount.val),
          reindexCorridorCutProfile (decodePortIncidence left)
              (fragmentIndexing permutation) =
            decodePortIncidence right := by
  let quotientProfiles : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoFragmentReindexProfile faceFragmentBound :=
    fun index => compressFragmentReindexBoundedCode (profiles index)
  obtain ⟨first, second, hfar, hquotient⟩ :=
    exists_separated_boundedFragmentReindex_eq quotientProfiles
  cases hfirst : profiles first with
  | mk firstCount firstProfile =>
      cases hsecond : profiles second with
      | mk secondCount secondProfile =>
          have hsigma := congrArg
            (fun profile : BoundedWidthTwoFragmentReindexProfile faceFragmentBound =>
              (⟨profile.faceFragmentCount, profile.profile⟩ :
                Σ fragmentCount : Fin (faceFragmentBound + 1),
                  WidthTwoFragmentReindexProfile fragmentCount.val)) hquotient
          simp only [quotientProfiles, compressFragmentReindexBoundedCode] at hsigma
          rw [hfirst, hsecond] at hsigma
          obtain ⟨hcount, hprofileHeq⟩ := Sigma.mk.inj_iff.mp hsigma
          change firstCount = secondCount at hcount
          subst secondCount
          have hcode :
              compressFragmentReindex firstProfile =
                compressFragmentReindex secondProfile :=
            eq_of_heq hprofileHeq
          obtain ⟨permutation, hreindex⟩ :=
            exists_fragmentIndexing_decode_eq_of_compressFragmentReindex_eq
              firstProfile secondProfile hcode
          exact ⟨first, second, firstCount, firstProfile, secondProfile,
            hfar, hfirst, hsecond, permutation, hreindex⟩

/-- Compress an actual bounded semantic profile while forgetting only its
arbitrary fragment enumeration. -/
noncomputable def compressFragmentReindexBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsPortIncidenceSemantic profile) :
    BoundedWidthTwoFragmentReindexProfile faceFragmentBound :=
  compressFragmentReindexBoundedCode
    (compressPortIncidenceBounded profile semantic)

/-- Source-facing `L7` repetition after quotienting only fragment labels.
The repeated profiles retain a common fragment count and return the explicit
fragment permutation accepted by the splice interface. -/
theorem exists_separated_reindexed_profile_of_portIncidenceSemantic
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index,
      BoundedIsPortIncidenceSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1),
      ∃ fragmentCount : Fin (faceFragmentBound + 1),
      ∃ left right : CorridorCutProfile 2 0 fragmentCount.val,
        first.val + 3 < second.val ∧
        profiles first = ⟨fragmentCount, left⟩ ∧
        profiles second = ⟨fragmentCount, right⟩ ∧
        ∃ permutation : Equiv.Perm (Fin fragmentCount.val),
          reindexCorridorCutProfile left (fragmentIndexing permutation) = right := by
  let codeProfiles : Fin
        (4 * boundedWidthTwoFragmentReindexProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoPortIncidenceProfile faceFragmentBound :=
    fun index => compressPortIncidenceBounded
      (profiles index) (semantic index)
  obtain ⟨first, second, fragmentCount, left, right,
      hfar, hleft, hright, permutation, hreindex⟩ :=
    exists_separated_reindexed_decode_of_boundedCode codeProfiles
  have hleftRaw :
      profiles first =
        ⟨fragmentCount, decodePortIncidence left⟩ := by
    calc
      profiles first = decodePortIncidenceBounded (codeProfiles first) :=
        (decodePortIncidenceBounded_compressPortIncidenceBounded
          (profiles first) (semantic first)).symm
      _ = ⟨fragmentCount, decodePortIncidence left⟩ := by
        rw [hleft]
        rfl
  have hrightRaw :
      profiles second =
        ⟨fragmentCount, decodePortIncidence right⟩ := by
    calc
      profiles second = decodePortIncidenceBounded (codeProfiles second) :=
        (decodePortIncidenceBounded_compressPortIncidenceBounded
          (profiles second) (semantic second)).symm
      _ = ⟨fragmentCount, decodePortIncidence right⟩ := by
        rw [hright]
        rfl
  exact ⟨first, second, fragmentCount, decodePortIncidence left,
    decodePortIncidence right, hfar, hleftRaw, hrightRaw,
    permutation, hreindex⟩

end GoertzelV24WidthTwoFragmentReindexSplice

end Mettapedia.GraphTheory.FourColor
