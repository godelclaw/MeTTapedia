import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCompression

/-!
# An executable codec for the lossless width-two profile carrier

The port-incidence compression previously supplied the injection needed for
the `L7` pigeonhole, but not a decoder.  A reachable-state computation needs
the converse direction as well: each finite code must reconstruct one raw
five-coordinate profile satisfying exactly the semantic laws built into the
code.

This file defines that decoder and proves that compression followed by
decoding is exact.  It does not claim that every decoded profile is realized
by a source corridor.  It only turns the already-proved semantic carrier into
an executable representation on which a sound over-approximate closure can be
computed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoPortIncidenceCodec

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open GoertzelV24WidthTwoProfileCompression
open GoertzelV24WindingClassification

/-- Reconstruct the tracked-connectivity matrix from its width-two diagonal
law and unique off-diagonal bit. -/
def decodeStrandConnected
    (code : WidthTwoStrandCode) (pair : TrackedColorPair)
    (left right : CorridorPort 2 0) : Bool :=
  match left, right with
  | .inl left, .inl right =>
      if left = right then
        decide (IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (code.1.1 left).toColor)
      else
        code.1.2 pair

/-- Reconstruct the complete five-coordinate raw profile represented by one
port-incidence code. -/
def decodePortIncidence
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount) :
    CorridorCutProfile 2 0 faceFragmentCount where
  edgeColor := code.strand.1.1
  strandConnected := decodeStrandConnected code.strand
  faceContinues := faceRelation code.face.1
  fragmentContainsPort fragment port :=
    match port with
    | .inl crossing => (code.fragmentContainsPort.1 fragment).1 crossing
  faceLengthCap fragment := (code.faceLengthCap fragment).1

@[simp] theorem decodePortIncidence_edgeColor
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount)
    (port : Fin 2) :
    (decodePortIncidence code).edgeColor port = code.strand.1.1 port :=
  rfl

@[simp] theorem decodePortIncidence_faceContinues
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount)
    (left right : Fin faceFragmentCount) :
    (decodePortIncidence code).faceContinues left right =
      faceRelation code.face.1 left right :=
  rfl

@[simp] theorem decodePortIncidence_fragmentContainsPort
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount)
    (fragment : Fin faceFragmentCount) (port : Fin 2) :
    (decodePortIncidence code).fragmentContainsPort fragment (.inl port) =
      (code.fragmentContainsPort.1 fragment).1 port :=
  rfl

@[simp] theorem decodePortIncidence_faceLengthCap
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount)
    (fragment : Fin faceFragmentCount) :
    (decodePortIncidence code).faceLengthCap fragment =
      (code.faceLengthCap fragment).1 :=
  rfl

@[simp] theorem decodeStrandConnected_diagonal
    (code : WidthTwoStrandCode) (pair : TrackedColorPair)
    (port : Fin 2) :
    decodeStrandConnected code pair (.inl port) (.inl port) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (code.1.1 port).toColor := by
  simp [decodeStrandConnected]

theorem decodeStrandConnected_symmetric
    (code : WidthTwoStrandCode) (pair : TrackedColorPair)
    (left right : Fin 2) :
    decodeStrandConnected code pair (.inl left) (.inl right) =
      decodeStrandConnected code pair (.inl right) (.inl left) := by
  fin_cases left <;> fin_cases right <;> simp [decodeStrandConnected]

theorem faceRelation_symmetric
    {n : Nat} (code : FaceEquivalenceCode n) (left right : Fin n) :
    faceRelation code.1 left right = faceRelation code.1 right left := by
  by_cases heq : left = right
  · subst right
    rfl
  · by_cases hlt : left < right
    · have hrev : right ≠ left := Ne.symm heq
      have hnlt : ¬ right < left := Nat.not_lt_of_ge (Nat.le_of_lt hlt)
      simp [faceRelation, heq, hrev, hlt, hnlt]
    · have hgt : right < left :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
      have hrev : right ≠ left := Ne.symm heq
      simp [faceRelation, heq, hrev, hlt, hgt]

/-- Every finite code decodes to a profile satisfying the complete semantic
laws used by the lossless compression. -/
theorem decodePortIncidence_isPortIncidenceSemantic
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount) :
    IsPortIncidenceSemantic (decodePortIncidence code) where
  strandDiagonal pair port := by
    exact decodeStrandConnected_diagonal code.strand pair port
  strandSymmetric pair left right := by
    exact decodeStrandConnected_symmetric code.strand pair left right
  faceDiagonal fragment := by
    simp [decodePortIncidence, faceRelation]
  faceSymmetric left right := by
    exact faceRelation_symmetric code.face left right
  strandCompatible pair hconnected := by
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have hbit : code.strand.1.2 pair = true := by
      simpa [decodePortIncidence, decodeStrandConnected, hne] using hconnected
    exact code.strand.2 pair hbit
  fragmentContainsPortNonempty fragment := by
    rcases (code.fragmentContainsPort.1 fragment).2 with ⟨port, hport⟩
    exact ⟨port, hport⟩
  faceLengthCapPositive fragment := by
    exact (code.faceLengthCap fragment).2
  faceTransitive left middle right hleft hright := by
    exact code.face.2 left middle right hleft hright
  portMultiplicity port := by
    simpa [decodePortIncidence] using code.fragmentContainsPort.2 port

/-- Decoding and re-encoding a finite code loses no information. -/
theorem compressPortIncidence_decodePortIncidence
    {faceFragmentCount : Nat}
    (code : WidthTwoPortIncidenceProfile faceFragmentCount) :
    compressPortIncidence (decodePortIncidence code)
        (decodePortIncidence_isPortIncidenceSemantic code) = code := by
  rw [WidthTwoPortIncidenceProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext pair
      simp [compressPortIncidence, compressFaceEquivalence, compressBoundary,
        decodePortIncidence, decodeStrandConnected]
  · apply Subtype.ext
    funext pair
    rcases pair with ⟨⟨left, right⟩, hlt⟩
    have hne : left ≠ right := ne_of_lt hlt
    simp [compressPortIncidence, compressFaceEquivalence,
      decodePortIncidence, faceRelation, hne, hlt]
  · apply Subtype.ext
    rfl
  · funext fragment
    apply Subtype.ext
    rfl

/-- Encoding and decoding a semantic raw profile recovers the complete raw
profile, including all five splice observables. -/
theorem decodePortIncidence_compressPortIncidence
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsPortIncidenceSemantic profile) :
    decodePortIncidence (compressPortIncidence profile semantic) = profile := by
  apply compressPortIncidence_injective
    (decodePortIncidence_isPortIncidenceSemantic
      (compressPortIncidence profile semantic)) semantic
  exact compressPortIncidence_decodePortIncidence
    (compressPortIncidence profile semantic)

/-- The semantic subtype of raw width-two profiles. -/
def PortIncidenceSemanticProfile (faceFragmentCount : Nat) :=
  { profile : CorridorCutProfile 2 0 faceFragmentCount //
    IsPortIncidenceSemantic profile }

/-- The finite code is equivalent, not merely injective, to the raw profiles
satisfying the encoded semantic laws. -/
noncomputable def portIncidenceCodecEquiv (faceFragmentCount : Nat) :
    WidthTwoPortIncidenceProfile faceFragmentCount ≃
      PortIncidenceSemanticProfile faceFragmentCount where
  toFun code :=
    ⟨decodePortIncidence code,
      decodePortIncidence_isPortIncidenceSemantic code⟩
  invFun profile := compressPortIncidence profile.1 profile.2
  left_inv code := compressPortIncidence_decodePortIncidence code
  right_inv profile := by
    apply Subtype.ext
    exact decodePortIncidence_compressPortIncidence profile.1 profile.2

/-- Decode the varying-fragment carrier used by the source-specific
three-face `L7` theorem. -/
def decodePortIncidenceBounded
    {faceFragmentBound : Nat}
    (code : BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :
    BoundedCorridorCutProfile 2 0 faceFragmentBound where
  faceFragmentCount := code.faceFragmentCount
  profile := decodePortIncidence code.profile

/-- Every decoded bounded code satisfies the same port-incidence laws. -/
theorem decodePortIncidenceBounded_semantic
    {faceFragmentBound : Nat}
    (code : BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :
    BoundedIsPortIncidenceSemantic (decodePortIncidenceBounded code) :=
  decodePortIncidence_isPortIncidenceSemantic code.profile

/-- The bounded codec is an exact retraction on finite codes. -/
theorem compressPortIncidenceBounded_decodePortIncidenceBounded
    {faceFragmentBound : Nat}
    (code : BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :
    compressPortIncidenceBounded (decodePortIncidenceBounded code)
        (decodePortIncidenceBounded_semantic code) = code := by
  cases code with
  | mk count profile =>
      simp only [compressPortIncidenceBounded,
        decodePortIncidenceBounded]
      rw [compressPortIncidence_decodePortIncidence]

/-- Encoding and decoding a bounded semantic profile is exact. -/
theorem decodePortIncidenceBounded_compressPortIncidenceBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsPortIncidenceSemantic profile) :
    decodePortIncidenceBounded
        (compressPortIncidenceBounded profile semantic) = profile := by
  cases profile with
  | mk count profile =>
      simp only [compressPortIncidenceBounded,
        decodePortIncidenceBounded]
      rw [decodePortIncidence_compressPortIncidence]

/-- The semantic subtype of bounded width-two profiles. -/
def BoundedPortIncidenceSemanticProfile (faceFragmentBound : Nat) :=
  { profile : BoundedCorridorCutProfile 2 0 faceFragmentBound //
    BoundedIsPortIncidenceSemantic profile }

/-- Executable bounded codes are equivalent to the complete bounded profiles
satisfying the encoded semantic laws. -/
noncomputable def boundedPortIncidenceCodecEquiv (faceFragmentBound : Nat) :
    BoundedWidthTwoPortIncidenceProfile faceFragmentBound ≃
      BoundedPortIncidenceSemanticProfile faceFragmentBound where
  toFun code :=
    ⟨decodePortIncidenceBounded code,
      decodePortIncidenceBounded_semantic code⟩
  invFun profile := compressPortIncidenceBounded profile.1 profile.2
  left_inv code :=
    compressPortIncidenceBounded_decodePortIncidenceBounded code
  right_inv profile := by
    apply Subtype.ext
    exact decodePortIncidenceBounded_compressPortIncidenceBounded
      profile.1 profile.2

noncomputable instance boundedPortIncidenceSemanticProfileFintype
    (faceFragmentBound : Nat) :
    Fintype (BoundedPortIncidenceSemanticProfile faceFragmentBound) :=
  Fintype.ofEquiv _ (boundedPortIncidenceCodecEquiv faceFragmentBound)

/-- The semantic subtype has exactly the previously computed finite carrier
size; `191184` at the source-specific three-fragment bound. -/
theorem card_boundedPortIncidenceSemanticProfile
    (faceFragmentBound : Nat) :
    Fintype.card (BoundedPortIncidenceSemanticProfile faceFragmentBound) =
      boundedWidthTwoPortIncidenceProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedPortIncidenceCodecEquiv faceFragmentBound).symm,
    card_boundedWidthTwoPortIncidenceProfile]

theorem card_boundedPortIncidenceSemanticProfile_three :
    Fintype.card (BoundedPortIncidenceSemanticProfile 3) = 191184 := by
  rw [card_boundedPortIncidenceSemanticProfile]
  norm_num [boundedWidthTwoPortIncidenceProfileCount,
    widthTwoPortIncidenceProfileCount, Fin.sum_univ_succ,
    card_faceEquivalenceCode_zero, card_faceEquivalenceCode_one,
    card_faceEquivalenceCode_two, card_faceEquivalenceCode_three,
    card_widthTwoPortIncidenceCode_zero,
    card_widthTwoPortIncidenceCode_one,
    card_widthTwoPortIncidenceCode_two,
    card_widthTwoPortIncidenceCode_three]

end GoertzelV24WidthTwoPortIncidenceCodec

end Mettapedia.GraphTheory.FourColor
