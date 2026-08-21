import Mathlib.GroupTheory.GroupAction.Quotient
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCodec

/-!
# Finite fragment-reindex orbits of width-two profiles

This module contains only the executable finite action: simultaneous
permutation of the face relation, occurrence-sensitive port rows, and capped
face lengths.  Keeping it below the geometric splice import cone lets Lean
compute the small orbit counts directly in the kernel.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoFragmentReindexCompression

open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoPortIncidenceCompression

/-- A full Boolean equivalence relation on the fragment coordinates. -/
def WidthTwoFaceRelation (fragmentCount : Nat) :=
  { relation : Fin fragmentCount → Fin fragmentCount → Bool //
    (∀ fragment, relation fragment fragment = true) ∧
      (∀ left right, relation left right = relation right left) ∧
      (∀ left middle right,
        relation left middle = true →
        relation middle right = true →
        relation left right = true) }

deriving instance Fintype for WidthTwoFaceRelation
deriving instance DecidableEq for WidthTwoFaceRelation

/-- The fragment-dependent part of a width-two semantic profile. -/
structure WidthTwoFragmentPayload (fragmentCount : Nat) where
  face : WidthTwoFaceRelation fragmentCount
  incidence : WidthTwoPortIncidenceCode fragmentCount
  cap : Fin fragmentCount → PositiveFaceLengthCap
  deriving Fintype, DecidableEq

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
      _ = (Finset.map permutation.symm.toEmbedding
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

/-- Two payloads differ only by presentation when a fragment permutation
relates all three dependent coordinates. -/
def FragmentReindexEquivalent {fragmentCount : Nat}
    (left right : WidthTwoFragmentPayload fragmentCount) : Prop :=
  ∃ permutation : Equiv.Perm (Fin fragmentCount),
    reindexFragmentPayload left permutation = right

instance fragmentReindexEquivalentDecidableRel (fragmentCount : Nat) :
    DecidableRel (@FragmentReindexEquivalent fragmentCount) := by
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

instance widthTwoFragmentPayloadMulAction (fragmentCount : Nat) :
    MulAction (Equiv.Perm (Fin fragmentCount))
      (WidthTwoFragmentPayload fragmentCount) where
  smul permutation payload :=
    reindexFragmentPayload payload permutation.symm
  one_smul payload := by
    change reindexFragmentPayload payload (Equiv.refl _) = payload
    exact reindexFragmentPayload_refl payload
  mul_smul first second payload := by
    change reindexFragmentPayload payload (first * second).symm =
      reindexFragmentPayload
        (reindexFragmentPayload payload second.symm) first.symm
    rw [reindexFragmentPayload_trans]
    rfl

theorem fragmentReindexEquivalent_iff_orbitRel {fragmentCount : Nat}
    (left right : WidthTwoFragmentPayload fragmentCount) :
    FragmentReindexEquivalent left right ↔
      MulAction.orbitRel (Equiv.Perm (Fin fragmentCount))
        (WidthTwoFragmentPayload fragmentCount) left right := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨permutation, rfl⟩
    refine ⟨permutation, ?_⟩
    change reindexFragmentPayload
        (reindexFragmentPayload left permutation) permutation.symm = left
    rw [reindexFragmentPayload_trans]
    simpa using reindexFragmentPayload_refl left
  · rintro ⟨permutation, hpermutation⟩
    change reindexFragmentPayload right permutation.symm = left at hpermutation
    refine ⟨permutation, ?_⟩
    rw [← hpermutation, reindexFragmentPayload_trans]
    simpa using reindexFragmentPayload_refl right

/-- The setoid generated by presentation-only fragment relabelling. -/
abbrev fragmentReindexSetoid (fragmentCount : Nat) :=
  MulAction.orbitRel (Equiv.Perm (Fin fragmentCount))
    (WidthTwoFragmentPayload fragmentCount)

/-- The exact fragment payload modulo arbitrary enumeration. -/
abbrev WidthTwoUnlabelledFragmentPayload (fragmentCount : Nat) :=
  MulAction.orbitRel.Quotient (Equiv.Perm (Fin fragmentCount))
    (WidthTwoFragmentPayload fragmentCount)

instance widthTwoUnlabelledFragmentPayloadFintype
    (fragmentCount : Nat) :
    Fintype (WidthTwoUnlabelledFragmentPayload fragmentCount) := by
  letI : DecidableRel (fragmentReindexSetoid fragmentCount).r := by
    intro left right
    rw [← fragmentReindexEquivalent_iff_orbitRel]
    exact fragmentReindexEquivalentDecidableRel fragmentCount left right
  exact Quotient.fintype (fragmentReindexSetoid fragmentCount)

/-- Executable fixed-point count for one fragment permutation. -/
abbrev fixedFragmentPayloadCount (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) : Nat :=
  ((Finset.univ : Finset (WidthTwoFragmentPayload fragmentCount)).filter
    fun payload => reindexFragmentPayload payload permutation.symm = payload).card

theorem fixedFragmentPayloadCount_eq_card_fixedBy (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    fixedFragmentPayloadCount fragmentCount permutation =
      Fintype.card (MulAction.fixedBy
        (WidthTwoFragmentPayload fragmentCount) permutation) := by
  rw [Fintype.card_subtype]
  rfl

/-- The fixed-point side of Burnside's lemma is small enough to evaluate
directly, even though constructing the quotient's normal forms is not a good
kernel computation. -/
abbrev totalFixedFragmentPayloadCount (fragmentCount : Nat) : Nat :=
  ∑ permutation : Equiv.Perm (Fin fragmentCount),
    fixedFragmentPayloadCount fragmentCount permutation

/-- Fixed face-equivalence relations under one fragment permutation. -/
abbrev fixedFaceRelationCount (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) : Nat :=
  ((Finset.univ : Finset (WidthTwoFaceRelation fragmentCount)).filter
    fun face => reindexFaceRelation face permutation.symm = face).card

/-- Fixed port-incidence codes under one fragment permutation. -/
abbrev fixedPortIncidenceCount (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) : Nat :=
  ((Finset.univ : Finset (WidthTwoPortIncidenceCode fragmentCount)).filter
    fun incidence => reindexPortIncidence incidence permutation.symm = incidence).card

/-- Fixed cap assignments under one fragment permutation. -/
abbrev fixedFaceCapCount (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) : Nat :=
  ((Finset.univ : Finset (Fin fragmentCount → PositiveFaceLengthCap)).filter
    fun cap => (fun fragment => cap (permutation.symm fragment)) = cap).card

/-- Componentwise fixed-point sum for the permutation action. -/
abbrev totalComponentFixedFragmentPayloadCount (fragmentCount : Nat) : Nat :=
  ∑ permutation : Equiv.Perm (Fin fragmentCount),
    fixedFaceRelationCount fragmentCount permutation *
      fixedPortIncidenceCount fragmentCount permutation *
      fixedFaceCapCount fragmentCount permutation

/-- A fixed payload is exactly a fixed face relation, a fixed incidence code,
and a fixed cap assignment. -/
def fixedFragmentPayloadEquivComponents (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    { payload : WidthTwoFragmentPayload fragmentCount //
        reindexFragmentPayload payload permutation.symm = payload } ≃
      ({ face : WidthTwoFaceRelation fragmentCount //
          reindexFaceRelation face permutation.symm = face } ×
        { incidence : WidthTwoPortIncidenceCode fragmentCount //
          reindexPortIncidence incidence permutation.symm = incidence }) ×
      { cap : Fin fragmentCount → PositiveFaceLengthCap //
        (fun fragment => cap (permutation.symm fragment)) = cap } where
  toFun payload :=
    ⟨⟨⟨payload.1.face,
        congrArg WidthTwoFragmentPayload.face payload.2⟩,
      ⟨payload.1.incidence,
        congrArg WidthTwoFragmentPayload.incidence payload.2⟩⟩,
      ⟨payload.1.cap,
        congrArg WidthTwoFragmentPayload.cap payload.2⟩⟩
  invFun components :=
    ⟨⟨components.1.1.1, components.1.2.1, components.2.1⟩, by
      rw [WidthTwoFragmentPayload.mk.injEq]
      exact ⟨components.1.1.2, components.1.2.2, components.2.2⟩⟩
  left_inv payload := by
    rcases payload with ⟨⟨face, incidence, cap⟩, hfixed⟩
    rfl
  right_inv components := by
    rcases components with ⟨⟨⟨face, hface⟩, ⟨incidence, hincidence⟩⟩,
      ⟨cap, hcap⟩⟩
    rfl

theorem fixedFragmentPayloadCount_eq_components (fragmentCount : Nat)
    (permutation : Equiv.Perm (Fin fragmentCount)) :
    fixedFragmentPayloadCount fragmentCount permutation =
      fixedFaceRelationCount fragmentCount permutation *
        fixedPortIncidenceCount fragmentCount permutation *
        fixedFaceCapCount fragmentCount permutation := by
  rw [fixedFragmentPayloadCount_eq_card_fixedBy]
  change Fintype.card
      { payload : WidthTwoFragmentPayload fragmentCount //
        reindexFragmentPayload payload permutation.symm = payload } = _
  rw [Fintype.card_congr
    (fixedFragmentPayloadEquivComponents fragmentCount permutation)]
  simp only [Fintype.card_prod]
  rw [Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]

theorem totalFixedFragmentPayloadCount_eq_components (fragmentCount : Nat) :
    totalFixedFragmentPayloadCount fragmentCount =
      totalComponentFixedFragmentPayloadCount fragmentCount := by
  apply Finset.sum_congr rfl
  intro permutation _
  exact fixedFragmentPayloadCount_eq_components fragmentCount permutation

set_option maxRecDepth 100000 in
theorem totalComponentFixedFragmentPayloadCount_zero :
    totalComponentFixedFragmentPayloadCount 0 = 1 := by decide

set_option maxRecDepth 100000 in
theorem totalComponentFixedFragmentPayloadCount_one :
    totalComponentFixedFragmentPayloadCount 1 = 15 := by decide

set_option maxRecDepth 100000 in
theorem totalComponentFixedFragmentPayloadCount_two :
    totalComponentFixedFragmentPayloadCount 2 = 480 := by decide

set_option maxRecDepth 100000 in
theorem totalComponentFixedFragmentPayloadCount_three :
    totalComponentFixedFragmentPayloadCount 3 = 7950 := by decide

theorem totalFixedFragmentPayloadCount_eq_card_orbits_mul_card_group
    (fragmentCount : Nat) :
    totalFixedFragmentPayloadCount fragmentCount =
      Fintype.card (WidthTwoUnlabelledFragmentPayload fragmentCount) *
        Fintype.card (Equiv.Perm (Fin fragmentCount)) := by
  unfold totalFixedFragmentPayloadCount
  simp_rw [fixedFragmentPayloadCount_eq_card_fixedBy]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin fragmentCount))
    (WidthTwoFragmentPayload fragmentCount)

theorem card_widthTwoUnlabelledFragmentPayload_zero :
    Fintype.card (WidthTwoUnlabelledFragmentPayload 0) = 1 := by
  have h := totalFixedFragmentPayloadCount_eq_card_orbits_mul_card_group 0
  rw [totalFixedFragmentPayloadCount_eq_components,
    totalComponentFixedFragmentPayloadCount_zero] at h
  have hgroup : Fintype.card (Equiv.Perm (Fin 0)) = 1 := by decide
  rw [hgroup] at h
  omega

theorem card_widthTwoUnlabelledFragmentPayload_one :
    Fintype.card (WidthTwoUnlabelledFragmentPayload 1) = 15 := by
  have h := totalFixedFragmentPayloadCount_eq_card_orbits_mul_card_group 1
  rw [totalFixedFragmentPayloadCount_eq_components,
    totalComponentFixedFragmentPayloadCount_one] at h
  have hgroup : Fintype.card (Equiv.Perm (Fin 1)) = 1 := by decide
  rw [hgroup] at h
  omega

theorem card_widthTwoUnlabelledFragmentPayload_two :
    Fintype.card (WidthTwoUnlabelledFragmentPayload 2) = 240 := by
  have h := totalFixedFragmentPayloadCount_eq_card_orbits_mul_card_group 2
  rw [totalFixedFragmentPayloadCount_eq_components,
    totalComponentFixedFragmentPayloadCount_two] at h
  have hgroup : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by decide
  rw [hgroup] at h
  omega

theorem card_widthTwoUnlabelledFragmentPayload_three :
    Fintype.card (WidthTwoUnlabelledFragmentPayload 3) = 1325 := by
  have h := totalFixedFragmentPayloadCount_eq_card_orbits_mul_card_group 3
  rw [totalFixedFragmentPayloadCount_eq_components,
    totalComponentFixedFragmentPayloadCount_three] at h
  have hgroup : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide
  rw [hgroup] at h
  omega

end GoertzelV24WidthTwoFragmentReindexCompression

end Mettapedia.GraphTheory.FourColor
