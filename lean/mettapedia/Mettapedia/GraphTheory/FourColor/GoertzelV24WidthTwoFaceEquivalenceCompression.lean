import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoBoundarySemanticCompression

/-!
# Face-equivalence compression of width-two boundary profiles

For an actual regional-boundary profile, `faceContinues` is equality of the
ambient face labels carried by two fragments.  It is therefore an equivalence
relation, not an arbitrary symmetric Boolean matrix.  This file stores its
upper-triangular bits subject to transitivity and proves that the resulting
code remains lossless on graph-derived profiles.

At the four-fragment source bound the fifteen possible equivalence relations
replace sixty-four arbitrary symmetric matrices.  This is still an L7 carrier
compression, not a reachable-closure certificate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoFaceEquivalenceCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoProfileCompression

/-- An ordered representative of an unordered pair of distinct indices. -/
abbrev UpperPair (n : Nat) :=
  { pair : Fin n × Fin n // pair.1 < pair.2 }

/-- Reconstruct the reflexive symmetric relation encoded by upper-triangular
bits. -/
def faceRelation {n : Nat} (upper : UpperPair n → Bool)
    (left right : Fin n) : Bool :=
  if hEq : left = right then true
  else if hLt : left < right then upper ⟨(left, right), hLt⟩
  else upper ⟨(right, left),
    lt_of_le_of_ne (Nat.le_of_not_gt hLt) (Ne.symm hEq)⟩

/-- Upper-triangular codes whose reconstructed relation is transitive.  Its
diagonal and symmetry are built into `faceRelation`. -/
def FaceEquivalenceCode (n : Nat) :=
  { upper : UpperPair n → Bool //
    ∀ left middle right,
      faceRelation upper left middle = true →
      faceRelation upper middle right = true →
      faceRelation upper left right = true }

deriving instance Fintype for FaceEquivalenceCode
deriving instance DecidableEq for FaceEquivalenceCode

theorem card_faceEquivalenceCode_zero :
    Fintype.card (FaceEquivalenceCode 0) = 1 := by decide

theorem card_faceEquivalenceCode_one :
    Fintype.card (FaceEquivalenceCode 1) = 1 := by decide

theorem card_faceEquivalenceCode_two :
    Fintype.card (FaceEquivalenceCode 2) = 2 := by decide

theorem card_faceEquivalenceCode_three :
    Fintype.card (FaceEquivalenceCode 3) = 5 := by decide

set_option maxRecDepth 100000 in
theorem card_faceEquivalenceCode_four :
    Fintype.card (FaceEquivalenceCode 4) = 15 := by decide

/-- The actual face relation is transitive in addition to the earlier
boundary-semantic laws. -/
structure IsFaceEquivalenceSemantic {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount) : Prop extends
      IsBoundarySemantic profile where
  faceTransitive : ∀ left middle right,
    profile.faceContinues left middle = true →
    profile.faceContinues middle right = true →
    profile.faceContinues left right = true

/-- The encoded upper relation reconstructs the original face observation. -/
theorem faceRelation_compress_eq
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsFaceEquivalenceSemantic profile)
    (left right : Fin faceFragmentCount) :
    faceRelation
        (fun pair => profile.faceContinues pair.1.1 pair.1.2) left right =
      profile.faceContinues left right := by
  by_cases hEq : left = right
  · subst right
    simp [faceRelation, semantic.faceDiagonal]
  · by_cases hLt : left < right
    · simp [faceRelation, hEq, hLt]
    · have hgt : right < left :=
        lt_of_le_of_ne (Nat.le_of_not_gt hLt) (Ne.symm hEq)
      simp only [faceRelation, hEq, hLt, dite_false]
      exact semantic.faceSymmetric right left

/-- The face-equivalence refined profile. -/
structure WidthTwoFaceEquivalenceProfile (faceFragmentCount : Nat) where
  strand : WidthTwoStrandCode
  face : FaceEquivalenceCode faceFragmentCount
  fragmentContainsPort : Fin faceFragmentCount → NonemptyWidthTwoPortRow
  faceLengthCap : Fin faceFragmentCount → PositiveFaceLengthCap
  deriving DecidableEq

private def widthTwoFaceEquivalenceProfileEquiv (faceFragmentCount : Nat) :
    WidthTwoFaceEquivalenceProfile faceFragmentCount ≃
      WidthTwoStrandCode × FaceEquivalenceCode faceFragmentCount ×
        (Fin faceFragmentCount → NonemptyWidthTwoPortRow) ×
        (Fin faceFragmentCount → PositiveFaceLengthCap) where
  toFun profile :=
    (profile.strand, profile.face, profile.fragmentContainsPort,
      profile.faceLengthCap)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance widthTwoFaceEquivalenceProfileFintype
    (faceFragmentCount : Nat) :
    Fintype (WidthTwoFaceEquivalenceProfile faceFragmentCount) :=
  Fintype.ofEquiv _
    (widthTwoFaceEquivalenceProfileEquiv faceFragmentCount).symm

def widthTwoFaceEquivalenceProfileCount (faceFragmentCount : Nat) : Nat :=
  24 * Fintype.card (FaceEquivalenceCode faceFragmentCount) *
    3 ^ faceFragmentCount * 5 ^ faceFragmentCount

theorem card_widthTwoFaceEquivalenceProfile (faceFragmentCount : Nat) :
    Fintype.card (WidthTwoFaceEquivalenceProfile faceFragmentCount) =
      widthTwoFaceEquivalenceProfileCount faceFragmentCount := by
  rw [Fintype.card_congr
    (widthTwoFaceEquivalenceProfileEquiv faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun]
  rw [card_widthTwoStrandCode, card_nonemptyWidthTwoPortRow,
    card_positiveFaceLengthCap]
  simp only [widthTwoFaceEquivalenceProfileCount, Fintype.card_fin]
  ring

/-- Encode one face-equivalence semantic profile. -/
noncomputable def compressFaceEquivalence
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsFaceEquivalenceSemantic profile) :
    WidthTwoFaceEquivalenceProfile faceFragmentCount where
  strand := (compressBoundary profile semantic.toIsBoundarySemantic).strand
  face :=
    ⟨fun pair => profile.faceContinues pair.1.1 pair.1.2, by
      intro left middle right hleft hright
      rw [faceRelation_compress_eq profile semantic] at hleft hright ⊢
      exact semantic.faceTransitive left middle right hleft hright⟩
  fragmentContainsPort :=
    (compressBoundary profile semantic.toIsBoundarySemantic).fragmentContainsPort
  faceLengthCap :=
    (compressBoundary profile semantic.toIsBoundarySemantic).faceLengthCap

private theorem faceOffDiagonal_eq_of_upper_eq
    {faceFragmentCount : Nat}
    {left right : CorridorCutProfile 2 0 faceFragmentCount}
    (leftSemantic : IsFaceEquivalenceSemantic left)
    (rightSemantic : IsFaceEquivalenceSemantic right)
    (hupper :
      (fun pair : UpperPair faceFragmentCount =>
        left.faceContinues pair.1.1 pair.1.2) =
      (fun pair : UpperPair faceFragmentCount =>
        right.faceContinues pair.1.1 pair.1.2)) :
    (fun unordered : OffDiagonalPair (Fin faceFragmentCount) =>
      Sym2.lift ⟨left.faceContinues, leftSemantic.faceSymmetric⟩ unordered.1) =
    (fun unordered : OffDiagonalPair (Fin faceFragmentCount) =>
      Sym2.lift ⟨right.faceContinues, rightSemantic.faceSymmetric⟩ unordered.1) := by
  funext unordered
  rcases unordered with ⟨pair, hnotDiag⟩
  induction pair using Sym2.inductionOn with
  | _ first second =>
      change left.faceContinues first second =
        right.faceContinues first second
      have hne : first ≠ second := by
        intro heq
        subst second
        exact hnotDiag (by simp [Sym2.IsDiag])
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact congrFun hupper ⟨(first, second), hlt⟩
      · rw [leftSemantic.faceSymmetric first second,
          rightSemantic.faceSymmetric first second]
        exact congrFun hupper ⟨(second, first), hgt⟩

/-- Face-equivalence compression remains lossless on actual profiles. -/
theorem compressFaceEquivalence_injective
    {faceFragmentCount : Nat}
    {left right : CorridorCutProfile 2 0 faceFragmentCount}
    (leftSemantic : IsFaceEquivalenceSemantic left)
    (rightSemantic : IsFaceEquivalenceSemantic right)
    (heq : compressFaceEquivalence left leftSemantic =
      compressFaceEquivalence right rightSemantic) :
    left = right := by
  apply compressBoundary_injective leftSemantic.toIsBoundarySemantic
    rightSemantic.toIsBoundarySemantic
  change WidthTwoBoundarySemanticProfile.mk
      (compressBoundary left leftSemantic.toIsBoundarySemantic).strand
      (compressBoundary left leftSemantic.toIsBoundarySemantic).faceContinues
      (compressBoundary left leftSemantic.toIsBoundarySemantic).fragmentContainsPort
      (compressBoundary left leftSemantic.toIsBoundarySemantic).faceLengthCap =
    WidthTwoBoundarySemanticProfile.mk
      (compressBoundary right rightSemantic.toIsBoundarySemantic).strand
      (compressBoundary right rightSemantic.toIsBoundarySemantic).faceContinues
      (compressBoundary right rightSemantic.toIsBoundarySemantic).fragmentContainsPort
      (compressBoundary right rightSemantic.toIsBoundarySemantic).faceLengthCap
  rw [WidthTwoBoundarySemanticProfile.mk.injEq]
  refine ⟨by
      simpa [compressFaceEquivalence] using
        congrArg WidthTwoFaceEquivalenceProfile.strand heq,
    ?_, by
      simpa [compressFaceEquivalence] using
        congrArg WidthTwoFaceEquivalenceProfile.fragmentContainsPort heq,
    by
      simpa [compressFaceEquivalence] using
        congrArg WidthTwoFaceEquivalenceProfile.faceLengthCap heq⟩
  apply faceOffDiagonal_eq_of_upper_eq leftSemantic rightSemantic
  simpa [compressFaceEquivalence] using congrArg Subtype.val
    (congrArg WidthTwoFaceEquivalenceProfile.face heq)

/-- Actual indexed regional-boundary profiles have transitive face
continuation because it is literal equality of their face labels. -/
theorem regionalBoundaryProfile_isFaceEquivalenceSemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E)
    (hports : ∀ index, crossingEdge index ∈ region)
    (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0) :
    IsFaceEquivalenceSemantic
      ((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
        color hcolor) where
  toIsBoundarySemantic := regionalBoundaryProfile_isBoundarySemantic
    region crossingEdge hports color hcolor
  faceTransitive left middle right hleft hright := by
    change decide
      ((regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace left =
        (regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace middle) =
          true at hleft
    change decide
      ((regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace middle =
        (regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace right) =
          true at hright
    change decide
      ((regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace left =
        (regionalBoundaryGraphCutData RS region crossingEdge).fragmentFace right) =
          true
    simp only [decide_eq_true_eq] at hleft hright ⊢
    exact hleft.trans hright

/-- Bounded face-equivalence carrier. -/
structure BoundedWidthTwoFaceEquivalenceProfile
    (faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : WidthTwoFaceEquivalenceProfile faceFragmentCount.val
  deriving DecidableEq

private def boundedWidthTwoFaceEquivalenceProfileEquiv
    (faceFragmentBound : Nat) :
    BoundedWidthTwoFaceEquivalenceProfile faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        WidthTwoFaceEquivalenceProfile faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedWidthTwoFaceEquivalenceProfileFintype
    (faceFragmentBound : Nat) :
    Fintype (BoundedWidthTwoFaceEquivalenceProfile faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedWidthTwoFaceEquivalenceProfileEquiv faceFragmentBound).symm

def boundedWidthTwoFaceEquivalenceProfileCount
    (faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    widthTwoFaceEquivalenceProfileCount faceFragmentCount.val

theorem card_boundedWidthTwoFaceEquivalenceProfile
    (faceFragmentBound : Nat) :
    Fintype.card (BoundedWidthTwoFaceEquivalenceProfile faceFragmentBound) =
      boundedWidthTwoFaceEquivalenceProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedWidthTwoFaceEquivalenceProfileEquiv faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [card_widthTwoFaceEquivalenceProfile]
  rfl

abbrev BoundedIsFaceEquivalenceSemantic
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound) : Prop :=
  IsFaceEquivalenceSemantic profile.profile

noncomputable def compressFaceEquivalenceBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsFaceEquivalenceSemantic profile) :
    BoundedWidthTwoFaceEquivalenceProfile faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compressFaceEquivalence profile.profile semantic

theorem compressFaceEquivalenceBounded_injective
    {faceFragmentBound : Nat}
    {left right : BoundedCorridorCutProfile 2 0 faceFragmentBound}
    (leftSemantic : BoundedIsFaceEquivalenceSemantic left)
    (rightSemantic : BoundedIsFaceEquivalenceSemantic right)
    (heq : compressFaceEquivalenceBounded left leftSemantic =
      compressFaceEquivalenceBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedWidthTwoFaceEquivalenceProfileEquiv faceFragmentBound) heq
      obtain ⟨hcount, hprofileHeq⟩ := Sigma.mk.inj_iff.mp hsigma
      simp only [compressFaceEquivalenceBounded] at hcount hprofileHeq
      subst rightCount
      have hprofile :
          compressFaceEquivalence leftProfile leftSemantic =
            compressFaceEquivalence rightProfile rightSemantic :=
        eq_of_heq hprofileHeq
      have hraw : leftProfile = rightProfile :=
        compressFaceEquivalence_injective
          leftSemantic rightSemantic hprofile
      subst rightProfile
      rfl

theorem exists_separated_profile_eq_of_faceEquivalenceSemantic
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoFaceEquivalenceProfileCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index,
      BoundedIsFaceEquivalenceSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedWidthTwoFaceEquivalenceProfileCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedWidthTwoFaceEquivalenceProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoFaceEquivalenceProfile faceFragmentBound × Fin 4 :=
    fun index =>
      (compressFaceEquivalenceBounded (profiles index) (semantic index),
        ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hcode := congrArg Prod.fst heq
    have hprofile : profiles first = profiles second :=
      compressFaceEquivalenceBounded_injective
        (semantic first) (semantic second) hcode
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
    card_boundedWidthTwoFaceEquivalenceProfile, Fintype.card_fin] at hcard
  omega

/-- Exact four-fragment carrier after all three semantic compression layers. -/
theorem boundedWidthTwoFaceEquivalenceProfileCount_four :
    boundedWidthTwoFaceEquivalenceProfileCount 4 = 18641184 := by
  norm_num [boundedWidthTwoFaceEquivalenceProfileCount,
    widthTwoFaceEquivalenceProfileCount, Fin.sum_univ_succ,
    card_faceEquivalenceCode_zero, card_faceEquivalenceCode_one,
    card_faceEquivalenceCode_two, card_faceEquivalenceCode_three,
    card_faceEquivalenceCode_four]

theorem separated_boundedWidthTwoFaceEquivalenceProfileCount_four :
    4 * boundedWidthTwoFaceEquivalenceProfileCount 4 + 1 = 74564737 := by
  rw [boundedWidthTwoFaceEquivalenceProfileCount_four]

end GoertzelV24WidthTwoFaceEquivalenceCompression

end Mettapedia.GraphTheory.FourColor
