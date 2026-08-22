import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoProfileCompression

/-!
# Lossless semantic compression with seam terminals

The source recurrence uses two crossing ports and one retained seam terminal.
The earlier width-two compressor covered only zero-terminal cuts.  This file
removes the same graph-impossible matrix freedom without forgetting the
terminal: crossing diagonals are reconstructed from their stored colours,
terminal diagonals are retained explicitly, and only one value is stored for
each off-diagonal unordered port pair.

The construction is generic in the crossing, terminal, and face counts.  It
is lossless on graph-derived profiles and therefore cannot identify two
different five-coordinate source states.  It is a carrier compression, not a
reachable-closure certificate or a claim that every compressed code is
realizable.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalAwareProfileCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WidthTwoProfileCompression
open GoertzelV24WindingClassification

/-- A complete profile with the symmetric matrices stored only once.
Terminal diagonals remain explicit because terminal colours are not separate
fields of `CorridorCutProfile`. -/
structure TerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  edgeColor : Fin crossingEdgeCount → StrandColor
  terminalStrandDiagonal :
    TrackedColorPair → Fin terminalCount → Bool
  strandConnected :
    TrackedColorPair →
      OffDiagonalPair (CorridorPort crossingEdgeCount terminalCount) → Bool
  faceContinues : OffDiagonalPair (Fin faceFragmentCount) → Bool
  fragmentContainsPort :
    Fin faceFragmentCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceLengthCap : Fin faceFragmentCount → Fin 6
  deriving DecidableEq

private def terminalAwareCompressedProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    TerminalAwareCompressedProfile crossingEdgeCount terminalCount
        faceFragmentCount ≃
      ((Fin crossingEdgeCount → StrandColor) ×
        (TrackedColorPair → Fin terminalCount → Bool) ×
        (TrackedColorPair →
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

noncomputable instance terminalAwareCompressedProfileFintype
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype (TerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentCount) :=
  Fintype.ofEquiv _
    (terminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount).symm

/-- Exact size of the fixed-fragment compressed carrier. -/
def terminalAwareCompressedProfileCount
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) : Nat :=
  3 ^ crossingEdgeCount *
    2 ^ (3 * terminalCount) *
    (2 ^ Nat.choose (crossingEdgeCount + terminalCount) 2) ^ 3 *
    2 ^ Nat.choose faceFragmentCount 2 *
    (2 ^ (crossingEdgeCount + terminalCount)) ^ faceFragmentCount *
    6 ^ faceFragmentCount

theorem card_terminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype.card (TerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentCount) =
      terminalAwareCompressedProfileCount crossingEdgeCount terminalCount
        faceFragmentCount := by
  rw [Fintype.card_congr
    (terminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [Sym2.card_subtype_not_diag, Sym2.card_subtype_not_diag]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  have hpair : Fintype.card TrackedColorPair = 3 := by decide
  rw [hcolor, hpair]
  simp only [Fintype.card_sum, Fintype.card_fin,
    terminalAwareCompressedProfileCount, pow_mul, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

/-- Exactly the graph laws used by the compression.  No law is imposed on a
terminal diagonal, because its colour is intentionally not a separate raw
profile coordinate. -/
structure IsTerminalGraphSemantic
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) : Prop where
  crossingStrandDiagonal : ∀ (pair : TrackedColorPair)
      (port : Fin crossingEdgeCount),
    profile.strandConnected pair (.inl port) (.inl port) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (profile.edgeColor port).toColor
  strandSymmetric : ∀ (pair : TrackedColorPair)
      (left right : CorridorPort crossingEdgeCount terminalCount),
    profile.strandConnected pair left right =
      profile.strandConnected pair right left
  faceDiagonal : ∀ fragment : Fin faceFragmentCount,
    profile.faceContinues fragment fragment = true
  faceSymmetric : ∀ left right : Fin faceFragmentCount,
    profile.faceContinues left right = profile.faceContinues right left

/-- Store exactly the non-forced matrix data of one semantic profile. -/
noncomputable def compress
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount)
    (semantic : IsTerminalGraphSemantic profile) :
    TerminalAwareCompressedProfile crossingEdgeCount terminalCount
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

/-- Compression is injective on semantic profiles, including every terminal
connectivity bit and every facial coordinate. -/
theorem compress_injective
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {left right : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount}
    (leftSemantic : IsTerminalGraphSemantic left)
    (rightSemantic : IsTerminalGraphSemantic right)
    (heq : compress left leftSemantic = compress right rightSemantic) :
    left = right := by
  have hedge := congrArg TerminalAwareCompressedProfile.edgeColor heq
  have hterminal := congrArg
    TerminalAwareCompressedProfile.terminalStrandDiagonal heq
  have hstrand := congrArg TerminalAwareCompressedProfile.strandConnected heq
  have hface := congrArg TerminalAwareCompressedProfile.faceContinues heq
  have hcontains := congrArg
    TerminalAwareCompressedProfile.fragmentContainsPort heq
  have hlength := congrArg TerminalAwareCompressedProfile.faceLengthCap heq
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

/-- Every graph-derived profile satisfies the semantic compression laws when
all named ports lie in the represented region. -/
theorem graphProfile_isTerminalGraphSemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (hports : data.PortsInRegion)
    (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    IsTerminalGraphSemantic (data.profile coloring hcoloring) where
  crossingStrandDiagonal pair port := by
    rw [data.profile_strandConnected_self_eq_true_iff
      hports coloring hcoloring]
    simpa [GraphCorridorCutData.portEdge] using
      (Iff.rfl :
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (coloring (data.crossingEdge port)) ↔
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (coloring (data.crossingEdge port)))
  strandSymmetric pair left right := by
    change regionalTrackedConnectivity RS data.regionEdges coloring pair
      (data.portEdge left) (data.portEdge right) = _
    exact regionalTrackedConnectivity_comm RS data.regionEdges coloring pair _ _
  faceDiagonal fragment := by
    simp [GraphCorridorCutData.profile]
  faceSymmetric left right := by
    simp [GraphCorridorCutData.profile, eq_comm]

/-- The same laws hold for a regional profile computed from an arbitrary
colour function nonzero on its crossing ports. -/
theorem regionalProfile_isTerminalGraphSemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (hports : data.PortsInRegion)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0) :
    IsTerminalGraphSemantic (data.regionalProfile color hcrossing) where
  crossingStrandDiagonal pair port := by
    rw [data.regionalProfile_strandConnected_self_eq_true_iff
      hports color hcrossing]
    simpa [GraphCorridorCutData.portEdge] using
      (Iff.rfl :
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (color (data.crossingEdge port)) ↔
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (color (data.crossingEdge port)))
  strandSymmetric pair left right := by
    change regionalTrackedConnectivity RS data.regionEdges color pair
      (data.portEdge left) (data.portEdge right) = _
    exact regionalTrackedConnectivity_comm RS data.regionEdges color pair _ _
  faceDiagonal fragment := by
    simp [GraphCorridorCutData.regionalProfile]
  faceSymmetric left right := by
    simp [GraphCorridorCutData.regionalProfile, eq_comm]

/-- One finite carrier when the dependent face count varies up to a fixed
bound. -/
structure BoundedTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : TerminalAwareCompressedProfile crossingEdgeCount terminalCount
    faceFragmentCount.val
  deriving DecidableEq

private def boundedTerminalAwareCompressedProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    BoundedTerminalAwareCompressedProfile crossingEdgeCount terminalCount
        faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        TerminalAwareCompressedProfile crossingEdgeCount terminalCount
          faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedTerminalAwareCompressedProfileFintype
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype (BoundedTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedTerminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound).symm

def boundedTerminalAwareCompressedProfileCount
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    terminalAwareCompressedProfileCount crossingEdgeCount terminalCount
      faceFragmentCount.val

theorem card_boundedTerminalAwareCompressedProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype.card (BoundedTerminalAwareCompressedProfile crossingEdgeCount
      terminalCount faceFragmentBound) =
      boundedTerminalAwareCompressedProfileCount crossingEdgeCount
        terminalCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedTerminalAwareCompressedProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound), Fintype.card_sigma]
  simp_rw [card_terminalAwareCompressedProfile]
  rfl

abbrev BoundedIsTerminalGraphSemantic
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) : Prop :=
  IsTerminalGraphSemantic profile.profile

noncomputable def compressBounded
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound)
    (semantic : BoundedIsTerminalGraphSemantic profile) :
    BoundedTerminalAwareCompressedProfile crossingEdgeCount terminalCount
      faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compress profile.profile semantic

/-- Equality of bounded semantic codes reconstructs equality of the complete
terminal-aware source profiles. -/
theorem compressBounded_injective
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    {left right : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound}
    (leftSemantic : BoundedIsTerminalGraphSemantic left)
    (rightSemantic : BoundedIsTerminalGraphSemantic right)
    (heq : compressBounded left leftSemantic =
      compressBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedTerminalAwareCompressedProfileEquiv crossingEdgeCount
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

/-- Pigeonhole on the lossless terminal-aware semantic carrier. -/
theorem exists_ne_profile_eq_of_terminalSemantic
    {crossingEdgeCount terminalCount faceFragmentBound stateCount : Nat}
    (profiles : Fin stateCount →
      BoundedCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound)
    (semantic : ∀ index,
      BoundedIsTerminalGraphSemantic (profiles index))
    (hlarge : boundedTerminalAwareCompressedProfileCount crossingEdgeCount
      terminalCount faceFragmentBound < stateCount) :
    ∃ first second : Fin stateCount,
      first ≠ second ∧ profiles first = profiles second := by
  let encode : Fin stateCount →
      BoundedTerminalAwareCompressedProfile crossingEdgeCount terminalCount
        faceFragmentBound := fun index =>
    compressBounded (profiles index) (semantic index)
  have hcard :
      Fintype.card (BoundedTerminalAwareCompressedProfile crossingEdgeCount
          terminalCount faceFragmentBound) <
        Fintype.card (Fin stateCount) := by
    rw [card_boundedTerminalAwareCompressedProfile, Fintype.card_fin]
    exact hlarge
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt encode hcard
  exact ⟨first, second, hne,
    compressBounded_injective (semantic first) (semantic second) heq⟩

/-- A modulo-four tag buys the source's required gap of at least four while
retaining equality of the complete terminal-aware profiles. -/
theorem exists_separated_profile_eq_of_terminalSemantic
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound)
    (semantic : ∀ index,
      BoundedIsTerminalGraphSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedTerminalAwareCompressedProfileCount crossingEdgeCount
          terminalCount faceFragmentBound + 1) →
      BoundedTerminalAwareCompressedProfile crossingEdgeCount terminalCount
          faceFragmentBound × Fin 4 := fun index =>
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
    card_boundedTerminalAwareCompressedProfile, Fintype.card_fin] at hcard
  omega

/-- Exact carrier count for the live two-crossing, one-terminal,
three-fragment source state. -/
theorem boundedTerminalAwareCompressedProfileCount_two_one_three :
    boundedTerminalAwareCompressedProfileCount 2 1 3 = 32786583552 := by
  norm_num [boundedTerminalAwareCompressedProfileCount,
    terminalAwareCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

/-- Exact gap-at-least-four demand for the live terminal-aware carrier. -/
theorem separated_terminalAwareCompressedProfileCount_two_one_three :
    4 * boundedTerminalAwareCompressedProfileCount 2 1 3 + 1 =
      131146334209 := by
  rw [boundedTerminalAwareCompressedProfileCount_two_one_three]

/-- Exact carrier count at the four-fragment bound used by the opened-source
terminal profile. -/
theorem boundedTerminalAwareCompressedProfileCount_two_one_four :
    boundedTerminalAwareCompressedProfileCount 2 1 4 =
      12556911218688 := by
  norm_num [boundedTerminalAwareCompressedProfileCount,
    terminalAwareCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

theorem separated_terminalAwareCompressedProfileCount_two_one_four :
    4 * boundedTerminalAwareCompressedProfileCount 2 1 4 + 1 =
      50227644874753 := by
  rw [boundedTerminalAwareCompressedProfileCount_two_one_four]

/-- The lossless semantic terminal-aware carrier is more than two million
times smaller than the arbitrary-matrix carrier used only as a fallback
finiteness witness. -/
theorem terminalAware_compressed_count_times_2087532_lt_raw_count :
    32786583552 * 2087532 < boundedCorridorCutProfileCount 2 1 3 := by
  norm_num [boundedCorridorCutProfileCount,
    GoertzelV24CorridorProfile.corridorCutProfileCount,
    Fin.sum_univ_succ]

/-- At the actual four-fragment source bound, the same lossless laws remove
more than thirty-three million copies of the arbitrary-matrix carrier. -/
theorem terminalAware_compressed_four_count_times_33472270_lt_raw_count :
    12556911218688 * 33472270 < boundedCorridorCutProfileCount 2 1 4 := by
  norm_num [boundedCorridorCutProfileCount,
    GoertzelV24CorridorProfile.corridorCutProfileCount,
    Fin.sum_univ_succ]

end GoertzelV24TerminalAwareProfileCompression

end Mettapedia.GraphTheory.FourColor
