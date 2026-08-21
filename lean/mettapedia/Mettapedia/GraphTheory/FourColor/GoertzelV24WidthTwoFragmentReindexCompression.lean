import Mathlib.Data.Fintype.Quotient
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCodec

/-!
# Fragment-reindexing compression of width-two profiles

The occurrence-sensitive boundary fragments of a corridor cut are finite,
but their `Fin` coordinates come from an enumeration rather than geometric
order.  The splice interface already permits an explicit permutation of
those coordinates.  This file therefore quotients only that presentation
choice, retaining the strand state, face equivalence, port incidence, and
capped face length exactly.

This is an `L7` carrier compression.  It neither identifies different
geometric states nor asserts that every quotient state is reachable by a
literal source Cell.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoFragmentReindexCompression

open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open GoertzelV24WidthTwoPortIncidenceCodec
open GoertzelV24SpliceUnification

/-- A full Boolean equivalence relation on the fragment coordinates.  The
existing upper-triangular code is expanded to this form only so relabelling
is definitionally transparent. -/
def WidthTwoFaceRelation (fragmentCount : Nat) :=
  { relation : Fin fragmentCount → Fin fragmentCount → Bool //
    (∀ fragment, relation fragment fragment = true) ∧
      (∀ left right, relation left right = relation right left) ∧
      (∀ left middle right,
        relation left middle = true →
        relation middle right = true →
        relation left right = true) }

deriving noncomputable instance Fintype for WidthTwoFaceRelation
deriving noncomputable instance DecidableEq for WidthTwoFaceRelation

/-- The fragment-dependent part of a width-two semantic profile. -/
structure WidthTwoFragmentPayload (fragmentCount : Nat) where
  face : WidthTwoFaceRelation fragmentCount
  incidence : WidthTwoPortIncidenceCode fragmentCount
  cap : Fin fragmentCount → PositiveFaceLengthCap

deriving noncomputable instance Fintype for WidthTwoFragmentPayload
deriving noncomputable instance DecidableEq for WidthTwoFragmentPayload

/-- Relabel a full face relation by a permutation of fragment coordinates. -/
def reindexFaceRelation {fragmentCount : Nat}
    (face : WidthTwoFaceRelation fragmentCount)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    WidthTwoFaceRelation fragmentCount :=
  ⟨fun left right => face.1 (permutation left) (permutation right),
    ⟨fun fragment => face.2.1 (permutation fragment),
      fun left right => face.2.2.1 (permutation left) (permutation right),
      fun left middle right hleft hright =>
        face.2.2.2 (permutation left) (permutation middle)
          (permutation right) hleft hright⟩⟩

/-- Relabel the occurrence-sensitive port rows. -/
def reindexPortIncidence {fragmentCount : Nat}
    (incidence : WidthTwoPortIncidenceCode fragmentCount)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    WidthTwoPortIncidenceCode fragmentCount := by
  refine ⟨fun fragment => incidence.1 (permutation fragment), ?_⟩
  intro port
  have hcard :
      ((Finset.univ : Finset (Fin fragmentCount)).filter fun fragment =>
          (incidence.1 (permutation fragment)).1 port = true).card =
        ((Finset.univ : Finset (Fin fragmentCount)).filter fun fragment =>
          (incidence.1 fragment).1 port = true).card := by
    calc
      ((Finset.univ : Finset (Fin fragmentCount)).filter fun fragment =>
          (incidence.1 (permutation fragment)).1 port = true).card =
        (Finset.map permutation.symm.toEmbedding
          ((Finset.univ : Finset (Fin fragmentCount)).filter fun fragment =>
            (incidence.1 fragment).1 port = true)).card := by
        congr 1
        ext fragment
        simp
      _ = _ := Finset.card_map permutation.symm.toEmbedding
  rw [hcard]
  exact incidence.2 port

/-- Simultaneously relabel every fragment-dependent coordinate. -/
def reindexFragmentPayload {fragmentCount : Nat}
    (payload : WidthTwoFragmentPayload fragmentCount)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    WidthTwoFragmentPayload fragmentCount where
  face := reindexFaceRelation payload.face permutation
  incidence := reindexPortIncidence payload.incidence permutation
  cap := fun fragment => payload.cap (permutation fragment)

@[simp]
theorem reindexFragmentPayload_refl {fragmentCount : Nat}
    (payload : WidthTwoFragmentPayload fragmentCount) :
    reindexFragmentPayload payload (Equiv.refl _) = payload := by
  cases payload
  rfl

theorem reindexFragmentPayload_trans {fragmentCount : Nat}
    (payload : WidthTwoFragmentPayload fragmentCount)
    (first second : Equiv.Perm (Fin fragmentCount)) :
    reindexFragmentPayload (reindexFragmentPayload payload first) second =
      reindexFragmentPayload payload (second.trans first) := by
  cases payload
  rfl

/-- Two payloads present the same boundary semantics when they differ only by
an explicitly certified permutation of fragment coordinates. -/
def FragmentReindexEquivalent {fragmentCount : Nat}
    (left right : WidthTwoFragmentPayload fragmentCount) : Prop :=
  ∃ permutation : Equiv.Perm (Fin fragmentCount),
    reindexFragmentPayload left permutation = right

noncomputable instance fragmentReindexEquivalentDecidableRel (fragmentCount : Nat) :
    DecidableRel (@FragmentReindexEquivalent fragmentCount) := by
  classical
  intro left right
  unfold FragmentReindexEquivalent
  infer_instance

theorem fragmentReindexEquivalent_refl {fragmentCount : Nat}
    (payload : WidthTwoFragmentPayload fragmentCount) :
    FragmentReindexEquivalent payload payload :=
  ⟨Equiv.refl _, reindexFragmentPayload_refl payload⟩

theorem fragmentReindexEquivalent_symm {fragmentCount : Nat}
    {left right : WidthTwoFragmentPayload fragmentCount}
    (h : FragmentReindexEquivalent left right) :
    FragmentReindexEquivalent right left := by
  rcases h with ⟨permutation, rfl⟩
  refine ⟨permutation.symm, ?_⟩
  rw [reindexFragmentPayload_trans]
  simpa using reindexFragmentPayload_refl left

theorem fragmentReindexEquivalent_trans {fragmentCount : Nat}
    {first second third : WidthTwoFragmentPayload fragmentCount}
    (hfirst : FragmentReindexEquivalent first second)
    (hsecond : FragmentReindexEquivalent second third) :
    FragmentReindexEquivalent first third := by
  rcases hfirst with ⟨firstPermutation, rfl⟩
  rcases hsecond with ⟨secondPermutation, rfl⟩
  exact ⟨secondPermutation.trans firstPermutation,
    reindexFragmentPayload_trans first firstPermutation secondPermutation⟩

/-- The setoid generated by presentation-only fragment relabelling. -/
def fragmentReindexSetoid (fragmentCount : Nat) :
    Setoid (WidthTwoFragmentPayload fragmentCount) where
  r := FragmentReindexEquivalent
  iseqv := ⟨fragmentReindexEquivalent_refl,
    fragmentReindexEquivalent_symm, fragmentReindexEquivalent_trans⟩

/-- The exact fragment payload modulo arbitrary enumeration. -/
abbrev WidthTwoUnlabelledFragmentPayload (fragmentCount : Nat) :=
  Quotient (fragmentReindexSetoid fragmentCount)

noncomputable instance widthTwoUnlabelledFragmentPayloadFintype
    (fragmentCount : Nat) :
    Fintype (WidthTwoUnlabelledFragmentPayload fragmentCount) := by
  letI : DecidableRel (fragmentReindexSetoid fragmentCount).r :=
    fragmentReindexEquivalentDecidableRel fragmentCount
  exact Quotient.fintype (fragmentReindexSetoid fragmentCount)

/-- The complete width-two state with its strand coordinate retained and only
the fragment enumeration forgotten. -/
abbrev WidthTwoFragmentReindexProfile (fragmentCount : Nat) :=
  WidthTwoStrandCode × WidthTwoUnlabelledFragmentPayload fragmentCount

/-- Quotienting the arbitrary enumeration never enlarges the carrier. -/
theorem card_widthTwoUnlabelledFragmentPayload_le (fragmentCount : Nat) :
    Fintype.card (WidthTwoUnlabelledFragmentPayload fragmentCount) ≤
      Fintype.card (WidthTwoFragmentPayload fragmentCount) := by
  letI : DecidableRel (fragmentReindexSetoid fragmentCount).r :=
    fragmentReindexEquivalentDecidableRel fragmentCount
  exact Fintype.card_quotient_le (fragmentReindexSetoid fragmentCount)

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
  rcases Quotient.exact hquotient with ⟨permutation, hpayload⟩
  exact ⟨permutation,
    reindex_decodePortIncidence_eq_of_payload left right permutation
      hstrand hpayload⟩

end GoertzelV24WidthTwoFragmentReindexCompression

end Mettapedia.GraphTheory.FourColor
