import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceCorridorProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalAwareProfileCompression

/-!
# Lossless terminal-aware compression of the manuscript-exact two-pair profile

The source's length profile records the connectivity pairing of the
`alpha ∪ beta` and `alpha ∪ gamma` walks crossing the cut.  It records no
third pairing.  `GoertzelV24TerminalAwareProfileCompression` compresses the
conservative three-pair carrier; this file gives the same lossless
compression for the two-pair carrier the manuscript actually names, so that a
state count reported for the source's profile is a count of the source's
profile.

The compression itself is unchanged in kind: crossing diagonals are
reconstructed from their stored colours, terminal diagonals are retained
explicitly, and each off-diagonal unordered port pair stores one value.  Only
the connectivity index changes, from three roles to two.

The three-pair engine is retained as an internal refinement rather than
replaced.  `toSourceCompressed` projects a three-pair code to its two-pair
code, and `compress_toSourceProfile` states that projecting and then
compressing agrees with compressing and then projecting.  Local transition
proofs may therefore continue to run in the conservative carrier, and only
the reported carrier size is taken in the source's own vocabulary.

As with the three-pair compressor this is a carrier compression: lossless on
profiles satisfying the graph laws, and not a claim that every compressed
code is realizable.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceTerminalAwareProfileCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SourceCorridorProfile
open GoertzelV24TerminalAwareProfileCompression
open GoertzelV24WidthTwoProfileCompression
open GoertzelV24WindingClassification

/-- The two-pair profile with symmetric matrices stored once.  Terminal
diagonals stay explicit for the same reason as in the three-pair carrier:
terminal colours are not separate raw profile coordinates. -/
structure SourceTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  edgeColor : Fin crossingEdgeCount → StrandColor
  terminalStrandDiagonal :
    SourceTrackedColorPair → Fin terminalCount → Bool
  strandConnected :
    SourceTrackedColorPair →
      OffDiagonalPair (CorridorPort crossingEdgeCount terminalCount) → Bool
  faceContinues : OffDiagonalPair (Fin faceFragmentCount) → Bool
  fragmentContainsPort :
    Fin faceFragmentCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceLengthCap : Fin faceFragmentCount → Fin 6
  deriving DecidableEq

private def sourceTerminalAwareCompressedProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    SourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
        faceFragmentCount ≃
      ((Fin crossingEdgeCount → StrandColor) ×
        (SourceTrackedColorPair → Fin terminalCount → Bool) ×
        (SourceTrackedColorPair →
          OffDiagonalPair (CorridorPort crossingEdgeCount terminalCount) → Bool) ×
        (OffDiagonalPair (Fin faceFragmentCount) → Bool) ×
        (Fin faceFragmentCount →
          CorridorPort crossingEdgeCount terminalCount → Bool) ×
        (Fin faceFragmentCount → Fin 6)) where
  toFun profile :=
    (profile.edgeColor, profile.terminalStrandDiagonal,
      profile.strandConnected, profile.faceContinues,
      profile.fragmentContainsPort, profile.faceLengthCap)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1,
      data.2.2.2.2.1, data.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance sourceTerminalAwareCompressedProfileFintype
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype (SourceTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentCount) :=
  Fintype.ofEquiv _
    (sourceTerminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount).symm

/-- Exact size of the fixed-fragment two-pair compressed carrier. -/
def sourceTerminalAwareCompressedProfileCount
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) : Nat :=
  3 ^ crossingEdgeCount *
    2 ^ (2 * terminalCount) *
    (2 ^ Nat.choose (crossingEdgeCount + terminalCount) 2) ^ 2 *
    2 ^ Nat.choose faceFragmentCount 2 *
    (2 ^ (crossingEdgeCount + terminalCount)) ^ faceFragmentCount *
    6 ^ faceFragmentCount

theorem card_sourceTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype.card (SourceTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentCount) =
      sourceTerminalAwareCompressedProfileCount crossingEdgeCount terminalCount
        faceFragmentCount := by
  rw [Fintype.card_congr
    (sourceTerminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [Sym2.card_subtype_not_diag, Sym2.card_subtype_not_diag]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  have hpair : Fintype.card SourceTrackedColorPair = 2 := by decide
  rw [hcolor, hpair]
  simp only [Fintype.card_sum, Fintype.card_fin,
    sourceTerminalAwareCompressedProfileCount, pow_mul, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

/-- Exactly the graph laws used by the two-pair compression.  The crossing
diagonal law is phrased through the standard colour-name gauge, so it is the
literal restriction of the three-pair law to the two named roles. -/
structure IsSourceTerminalGraphSemantic
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) : Prop where
  crossingStrandDiagonal : ∀ (pair : SourceTrackedColorPair)
      (port : Fin crossingEdgeCount),
    profile.strandConnected pair (.inl port) (.inl port) = true ↔
      IsTrackedColor (trackedColorPairColors pair.toTrackedColorPair).1
        (trackedColorPairColors pair.toTrackedColorPair).2
        (profile.edgeColor port).toColor
  strandSymmetric : ∀ (pair : SourceTrackedColorPair)
      (left right : CorridorPort crossingEdgeCount terminalCount),
    profile.strandConnected pair left right =
      profile.strandConnected pair right left
  faceDiagonal : ∀ fragment : Fin faceFragmentCount,
    profile.faceContinues fragment fragment = true
  faceSymmetric : ∀ left right : Fin faceFragmentCount,
    profile.faceContinues left right = profile.faceContinues right left

/-- The gauge is the manuscript's: the two retained roles are `alpha ∪ beta`
and `alpha ∪ gamma` for the standard ordered triple. -/
theorem sourceTrackedColorPairColors_eq_trackedColorPairColors
    (pair : SourceTrackedColorPair) :
    sourceTrackedColorPairColors red blue purple pair =
      trackedColorPairColors pair.toTrackedColorPair := by
  cases pair <;> rfl

/-- Store exactly the non-forced matrix data of one two-pair semantic profile. -/
noncomputable def compress
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (semantic : IsSourceTerminalGraphSemantic profile) :
    SourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentCount where
  edgeColor := profile.edgeColor
  terminalStrandDiagonal pair terminal :=
    profile.strandConnected pair (.inr terminal) (.inr terminal)
  strandConnected pair unordered :=
    Sym2.lift
      ⟨profile.strandConnected pair, semantic.strandSymmetric pair⟩ unordered.1
  faceContinues unordered :=
    Sym2.lift ⟨profile.faceContinues, semantic.faceSymmetric⟩ unordered.1
  fragmentContainsPort := profile.fragmentContainsPort
  faceLengthCap := profile.faceLengthCap

private theorem bool_eq_of_eq_true_iff_eq_true {left right : Bool}
    (h : (left = true ↔ right = true)) : left = right := by
  cases left <;> cases right <;> simp_all

/-- Compression is injective on two-pair semantic profiles, including every
terminal connectivity bit and every facial coordinate. -/
theorem compress_injective
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {left right : SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount}
    (leftSemantic : IsSourceTerminalGraphSemantic left)
    (rightSemantic : IsSourceTerminalGraphSemantic right)
    (heq : compress left leftSemantic = compress right rightSemantic) :
    left = right := by
  have hedge := congrArg SourceTerminalAwareCompressedProfile.edgeColor heq
  have hterminal := congrArg
    SourceTerminalAwareCompressedProfile.terminalStrandDiagonal heq
  have hstrand := congrArg
    SourceTerminalAwareCompressedProfile.strandConnected heq
  have hface := congrArg SourceTerminalAwareCompressedProfile.faceContinues heq
  have hcontains := congrArg
    SourceTerminalAwareCompressedProfile.fragmentContainsPort heq
  have hlength := congrArg
    SourceTerminalAwareCompressedProfile.faceLengthCap heq
  cases left with
  | mk leftEdge leftStrand leftFace leftContains leftLength =>
    cases right with
    | mk rightEdge rightStrand rightFace rightContains rightLength =>
      simp only [compress] at hedge hterminal hstrand hface hcontains hlength
      subst rightEdge
      have hstrand' : leftStrand = rightStrand := by
        funext pair leftPort rightPort
        by_cases hsame : leftPort = rightPort
        · subst rightPort
          rcases leftPort with crossing | terminal
          · apply bool_eq_of_eq_true_iff_eq_true
            rw [leftSemantic.crossingStrandDiagonal,
              rightSemantic.crossingStrandDiagonal]
          · simpa [compress] using
              congrFun (congrFun hterminal pair) terminal
        · let unordered :
              OffDiagonalPair
                (CorridorPort crossingEdgeCount terminalCount) :=
            ⟨s(leftPort, rightPort), by
              simpa [Sym2.mk_isDiag_iff] using hsame⟩
          have hvalue := congrFun (congrFun hstrand pair) unordered
          simpa [compress, unordered] using hvalue
      have hface' : leftFace = rightFace := by
        funext leftFragment rightFragment
        by_cases hsame : leftFragment = rightFragment
        · subst rightFragment
          apply bool_eq_of_eq_true_iff_eq_true
          constructor <;> intro _
          · exact rightSemantic.faceDiagonal leftFragment
          · exact leftSemantic.faceDiagonal leftFragment
        · let unordered : OffDiagonalPair (Fin faceFragmentCount) :=
            ⟨s(leftFragment, rightFragment), by
              simpa [Sym2.mk_isDiag_iff] using hsame⟩
          have hvalue := congrFun hface unordered
          simpa [compress, unordered] using hvalue
      have hcontains' : leftContains = rightContains := by
        simpa [compress] using hcontains
      have hlength' : leftLength = rightLength := by
        simpa [compress] using hlength
      subst rightStrand
      subst rightFace
      subst rightContains
      subst rightLength
      rfl

/-! ## The three-pair engine as an internal refinement -/

/-- The three-pair semantic laws restrict to the two named roles. -/
theorem isSourceTerminalGraphSemantic_toSourceProfile
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount}
    (semantic : IsTerminalGraphSemantic profile) :
    IsSourceTerminalGraphSemantic (toSourceProfile profile) where
  crossingStrandDiagonal pair port :=
    semantic.crossingStrandDiagonal pair.toTrackedColorPair port
  strandSymmetric pair := semantic.strandSymmetric pair.toTrackedColorPair
  faceDiagonal := semantic.faceDiagonal
  faceSymmetric := semantic.faceSymmetric

/-- Forget the conservative third role of a compressed code. -/
def TerminalAwareCompressedProfile.toSourceCompressed
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (code : TerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentCount) :
    SourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentCount where
  edgeColor := code.edgeColor
  terminalStrandDiagonal pair := code.terminalStrandDiagonal pair.toTrackedColorPair
  strandConnected pair := code.strandConnected pair.toTrackedColorPair
  faceContinues := code.faceContinues
  fragmentContainsPort := code.fragmentContainsPort
  faceLengthCap := code.faceLengthCap

/-- **The refinement square.**  Projecting to the manuscript's two roles and
then compressing agrees with compressing in the conservative carrier and then
projecting.  Transition proofs may therefore stay three-pair while the
reported carrier is two-pair. -/
theorem compress_toSourceProfile
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount}
    (semantic : IsTerminalGraphSemantic profile) :
    compress (toSourceProfile profile)
        (isSourceTerminalGraphSemantic_toSourceProfile semantic) =
      TerminalAwareCompressedProfile.toSourceCompressed
        (GoertzelV24TerminalAwareProfileCompression.compress profile
          semantic) := by
  rfl

/-! ## The bounded carrier, its exact size, and the pigeonhole -/

/-- One finite carrier when the dependent face count varies up to a fixed
bound. -/
structure BoundedSourceTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : SourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
    faceFragmentCount.val
  deriving DecidableEq

private def boundedSourceTerminalAwareCompressedProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
        faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        SourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
          faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedSourceTerminalAwareCompressedProfileFintype
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype (BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedSourceTerminalAwareCompressedProfileEquiv crossingEdgeCount
      terminalCount faceFragmentBound).symm

def boundedSourceTerminalAwareCompressedProfileCount
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    sourceTerminalAwareCompressedProfileCount crossingEdgeCount terminalCount
      faceFragmentCount.val

theorem card_boundedSourceTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype.card (BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentBound) =
      boundedSourceTerminalAwareCompressedProfileCount crossingEdgeCount
        terminalCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedSourceTerminalAwareCompressedProfileEquiv crossingEdgeCount
      terminalCount faceFragmentBound), Fintype.card_sigma]
  simp_rw [card_sourceTerminalAwareCompressedProfile]
  rfl

abbrev BoundedIsSourceTerminalGraphSemantic
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) : Prop :=
  IsSourceTerminalGraphSemantic profile.profile

noncomputable def compressBounded
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound)
    (semantic : BoundedIsSourceTerminalGraphSemantic profile) :
    BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compress profile.profile semantic

/-- Equality of bounded two-pair codes reconstructs equality of the complete
five-coordinate source profiles. -/
theorem compressBounded_injective
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    {left right : BoundedSourceCorridorCutProfile crossingEdgeCount
      terminalCount faceFragmentBound}
    (leftSemantic : BoundedIsSourceTerminalGraphSemantic left)
    (rightSemantic : BoundedIsSourceTerminalGraphSemantic right)
    (heq : compressBounded left leftSemantic =
      compressBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedSourceTerminalAwareCompressedProfileEquiv crossingEdgeCount
          terminalCount faceFragmentBound) heq
      obtain ⟨hcount, hprofileHeq⟩ := Sigma.mk.inj_iff.mp hsigma
      simp only [compressBounded] at hcount hprofileHeq
      subst rightCount
      have hprofile :
          compress leftProfile leftSemantic =
            compress rightProfile rightSemantic :=
        eq_of_heq hprofileHeq
      have hraw : leftProfile = rightProfile :=
        compress_injective leftSemantic rightSemantic hprofile
      subst rightProfile
      rfl

/-- Compression respects equality of raw bounded profiles independently of the
proof terms witnessing their semantic laws. -/
theorem compressBounded_eq_of_eq
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    {left right : BoundedSourceCorridorCutProfile crossingEdgeCount
      terminalCount faceFragmentBound}
    (leftSemantic : BoundedIsSourceTerminalGraphSemantic left)
    (rightSemantic : BoundedIsSourceTerminalGraphSemantic right)
    (heq : left = right) :
    compressBounded left leftSemantic =
      compressBounded right rightSemantic := by
  subst right
  congr

/-- Pigeonhole on the lossless two-pair semantic carrier. -/
theorem exists_ne_profile_eq_of_sourceTerminalSemantic
    {crossingEdgeCount terminalCount faceFragmentBound stateCount : Nat}
    (profiles : Fin stateCount →
      BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound)
    (semantic : ∀ index, BoundedIsSourceTerminalGraphSemantic (profiles index))
    (hlarge : boundedSourceTerminalAwareCompressedProfileCount crossingEdgeCount
      terminalCount faceFragmentBound < stateCount) :
    ∃ first second : Fin stateCount,
      first ≠ second ∧ profiles first = profiles second := by
  let encode : Fin stateCount →
      BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount
        terminalCount faceFragmentBound := fun index =>
    compressBounded (profiles index) (semantic index)
  have hcard :
      Fintype.card (BoundedSourceTerminalAwareCompressedProfile
          crossingEdgeCount terminalCount faceFragmentBound) <
        Fintype.card (Fin stateCount) := by
    rw [card_boundedSourceTerminalAwareCompressedProfile, Fintype.card_fin]
    exact hlarge
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt encode hcard
  exact ⟨first, second, hne,
    compressBounded_injective (semantic first) (semantic second) heq⟩

/-- A modulo-four tag buys the source's required gap of at least four while
retaining equality of the complete two-pair profiles. -/
theorem exists_separated_profile_eq_of_sourceTerminalSemantic
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedSourceTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1) →
      BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound)
    (semantic : ∀ index, BoundedIsSourceTerminalGraphSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedSourceTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedSourceTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1) →
      BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount
          terminalCount faceFragmentBound × Fin 4 := fun index =>
    (compressBounded (profiles index) (semantic index),
      ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hcode :
        compressBounded (profiles first) (semantic first) =
          compressBounded (profiles second) (semantic second) :=
      congrArg Prod.fst heq
    have hprofile : profiles first = profiles second :=
      compressBounded_injective (semantic first) (semantic second) hcode
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      simpa [encode] using hresidue
    apply Fin.ext
    by_contra hvalue
    rcases lt_or_gt_of_ne hvalue with hfirst | hsecond
    · have hfar : first.val + 3 < second.val := by omega
      exact False.elim (hseparated first second hfar hprofile)
    · have hfar : second.val + 3 < first.val := by omega
      exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  rw [Fintype.card_fin, Fintype.card_prod,
    card_boundedSourceTerminalAwareCompressedProfile, Fintype.card_fin] at hcard
  omega

/-! ## Exact sizes at the live corridor shape -/

/-- Exact two-pair carrier count for the live two-crossing, one-terminal,
three-fragment source state. -/
theorem boundedSourceTerminalAwareCompressedProfileCount_two_one_three :
    boundedSourceTerminalAwareCompressedProfileCount 2 1 3 = 2049161472 := by
  norm_num [boundedSourceTerminalAwareCompressedProfileCount,
    sourceTerminalAwareCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

/-- Exact two-pair carrier count at the four-fragment bound used by the
opened-source terminal profile. -/
theorem boundedSourceTerminalAwareCompressedProfileCount_two_one_four :
    boundedSourceTerminalAwareCompressedProfileCount 2 1 4 = 784806951168 := by
  norm_num [boundedSourceTerminalAwareCompressedProfileCount,
    sourceTerminalAwareCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

/-- Exact gap-at-least-four demand on the manuscript's own carrier. -/
theorem separated_sourceTerminalAwareCompressedProfileCount_two_one_four :
    4 * boundedSourceTerminalAwareCompressedProfileCount 2 1 4 + 1 =
      3139227804673 := by
  rw [boundedSourceTerminalAwareCompressedProfileCount_two_one_four]

/-- **The cost of the conservative third role, exactly.**  At the live corridor
shape the three-pair carrier is sixteen times the manuscript's own two-pair
carrier: one factor of two for the discarded terminal diagonal and eight for
its off-diagonal port pairs.  A repeat demand reported against the three-pair
count therefore overstates the source's demand by that factor. -/
theorem boundedTerminalAwareCompressedProfileCount_two_one_four_eq :
    GoertzelV24TerminalAwareProfileCompression.boundedTerminalAwareCompressedProfileCount
        2 1 4 =
      16 * boundedSourceTerminalAwareCompressedProfileCount 2 1 4 := by
  rw [GoertzelV24TerminalAwareProfileCompression.boundedTerminalAwareCompressedProfileCount_two_one_four,
    boundedSourceTerminalAwareCompressedProfileCount_two_one_four]

theorem boundedTerminalAwareCompressedProfileCount_two_one_three_eq :
    GoertzelV24TerminalAwareProfileCompression.boundedTerminalAwareCompressedProfileCount
        2 1 3 =
      16 * boundedSourceTerminalAwareCompressedProfileCount 2 1 3 := by
  rw [GoertzelV24TerminalAwareProfileCompression.boundedTerminalAwareCompressedProfileCount_two_one_three,
    boundedSourceTerminalAwareCompressedProfileCount_two_one_three]

end GoertzelV24SourceTerminalAwareProfileCompression

end Mettapedia.GraphTheory.FourColor
