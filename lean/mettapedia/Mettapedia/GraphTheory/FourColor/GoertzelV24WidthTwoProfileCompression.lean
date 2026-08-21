import Mathlib.Data.Sym.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Lossless semantic compression of width-two corridor profiles

The raw L7 carrier stores tracked connectivity and face continuation as
arbitrary directed Boolean matrices.  Profiles computed from an actual graph
do not range over those matrices: tracked connectivity is symmetric, its
diagonal is fixed by the two boundary colors, and face continuation is a
symmetric relation with a forced diagonal.

This file removes exactly that over-encoding.  It stores only off-diagonal
unordered pairs and proves that the resulting code is injective on profiles
with the graph-derived laws.  Thus equality of compressed codes still implies
equality of the complete five-field profile consumed by the splice.

This is an L7 carrier compression, not a reachable-closure certificate.  It
does not assert that every compressed state is realizable, nor that the
full source transfer visits the older twenty-mode Lemma-8.18 laboratory.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoProfileCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- An unordered pair of distinct coordinates. -/
abbrev OffDiagonalPair (α : Type*) := { pair : Sym2 α // ¬ pair.IsDiag }

/-- The width-two profile after deleting matrix entries forced by graph
semantics.  Face-fragment incidence and capped lengths are retained verbatim. -/
structure WidthTwoCompressedProfile (faceFragmentCount : Nat) where
  edgeColor : Fin 2 → StrandColor
  strandConnected : TrackedColorPair → OffDiagonalPair (Fin 2) → Bool
  faceContinues : OffDiagonalPair (Fin faceFragmentCount) → Bool
  fragmentContainsPort : Fin faceFragmentCount → Fin 2 → Bool
  faceLengthCap : Fin faceFragmentCount → Fin 6
  deriving DecidableEq

private def widthTwoCompressedProfileEquiv (faceFragmentCount : Nat) :
    WidthTwoCompressedProfile faceFragmentCount ≃
      ((Fin 2 → StrandColor) ×
        (TrackedColorPair → OffDiagonalPair (Fin 2) → Bool) ×
        (OffDiagonalPair (Fin faceFragmentCount) → Bool) ×
        (Fin faceFragmentCount → Fin 2 → Bool) ×
        (Fin faceFragmentCount → Fin 6)) where
  toFun profile :=
    (profile.edgeColor, profile.strandConnected, profile.faceContinues,
      profile.fragmentContainsPort, profile.faceLengthCap)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance widthTwoCompressedProfileFintype
    (faceFragmentCount : Nat) :
    Fintype (WidthTwoCompressedProfile faceFragmentCount) :=
  Fintype.ofEquiv _ (widthTwoCompressedProfileEquiv faceFragmentCount).symm

/-- Exact size of the compressed fixed-fragment carrier. -/
def widthTwoCompressedProfileCount (faceFragmentCount : Nat) : Nat :=
  3 ^ 2 *
    ((2 ^ Nat.choose 2 2) ^ 3 *
      (2 ^ Nat.choose faceFragmentCount 2 *
        ((2 ^ 2) ^ faceFragmentCount * 6 ^ faceFragmentCount)))

/-- L7 cardinality of the lossless symmetric-matrix encoding. -/
theorem card_widthTwoCompressedProfile (faceFragmentCount : Nat) :
    Fintype.card (WidthTwoCompressedProfile faceFragmentCount) =
      widthTwoCompressedProfileCount faceFragmentCount := by
  rw [Fintype.card_congr (widthTwoCompressedProfileEquiv faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [Sym2.card_subtype_not_diag, Sym2.card_subtype_not_diag]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  have hpair : Fintype.card TrackedColorPair = 3 := by decide
  rw [hcolor, hpair]
  simp only [Fintype.card_fin, widthTwoCompressedProfileCount]

/-- The graph-derived laws needed to reconstruct a raw width-two profile from
its compressed code.  They are conclusions for actual graph profiles, not
free fields added to the profile carrier. -/
structure IsGraphSemantic
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount) : Prop where
  strandDiagonal : ∀ (pair : TrackedColorPair) (port : Fin 2),
    profile.strandConnected pair (.inl port) (.inl port) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (profile.edgeColor port).toColor
  strandSymmetric : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    profile.strandConnected pair (.inl left) (.inl right) =
      profile.strandConnected pair (.inl right) (.inl left)
  faceDiagonal : ∀ fragment : Fin faceFragmentCount,
    profile.faceContinues fragment fragment = true
  faceSymmetric : ∀ left right : Fin faceFragmentCount,
    profile.faceContinues left right = profile.faceContinues right left

/-- Store the symmetric off-diagonal data of a semantically valid profile. -/
noncomputable def compress
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsGraphSemantic profile) :
    WidthTwoCompressedProfile faceFragmentCount where
  edgeColor := profile.edgeColor
  strandConnected pair unordered :=
    Sym2.lift
      ⟨fun left right =>
          profile.strandConnected pair (.inl left) (.inl right),
        semantic.strandSymmetric pair⟩ unordered.1
  faceContinues unordered :=
    Sym2.lift ⟨profile.faceContinues, semantic.faceSymmetric⟩ unordered.1
  fragmentContainsPort fragment port :=
    profile.fragmentContainsPort fragment (.inl port)
  faceLengthCap := profile.faceLengthCap

private theorem bool_eq_of_eq_true_iff_eq_true {left right : Bool}
    (h : (left = true ↔ right = true)) : left = right := by
  cases left <;> cases right <;> simp_all

/-- The compressed code is lossless on the semantic subset: no splice
observable is discarded. -/
theorem compress_injective
    {faceFragmentCount : Nat}
    {left right : CorridorCutProfile 2 0 faceFragmentCount}
    (leftSemantic : IsGraphSemantic left)
    (rightSemantic : IsGraphSemantic right)
    (heq : compress left leftSemantic = compress right rightSemantic) :
    left = right := by
  have hedge : left.edgeColor = right.edgeColor :=
    congrArg WidthTwoCompressedProfile.edgeColor heq
  have hstrand := congrArg WidthTwoCompressedProfile.strandConnected heq
  have hface := congrArg WidthTwoCompressedProfile.faceContinues heq
  have hcontains := congrArg WidthTwoCompressedProfile.fragmentContainsPort heq
  have hlength := congrArg WidthTwoCompressedProfile.faceLengthCap heq
  cases left with
  | mk leftEdge leftStrand leftFace leftContains leftLength =>
    cases right with
    | mk rightEdge rightStrand rightFace rightContains rightLength =>
      simp only at hedge hstrand hface hcontains hlength ⊢
      subst rightEdge
      have hstrand' : leftStrand = rightStrand := by
        funext pair leftPort rightPort
        rcases leftPort with leftPort | leftImpossible
        · rcases rightPort with rightPort | rightImpossible
          · by_cases hsame : leftPort = rightPort
            · subst rightPort
              apply bool_eq_of_eq_true_iff_eq_true
              rw [leftSemantic.strandDiagonal,
                rightSemantic.strandDiagonal]
            · let unordered : OffDiagonalPair (Fin 2) :=
                ⟨s(leftPort, rightPort), by
                  simpa [Sym2.mk_isDiag_iff] using hsame⟩
              have hvalue := congrFun (congrFun hstrand pair) unordered
              simpa [compress, unordered] using hvalue
          · exact Fin.elim0 rightImpossible
        · exact Fin.elim0 leftImpossible
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
        funext fragment port
        rcases port with port | impossible
        · simpa [compress] using congrFun (congrFun hcontains fragment) port
        · exact Fin.elim0 impossible
      have hlength' : leftLength = rightLength := by
        simpa [compress] using hlength
      subst rightStrand
      subst rightFace
      subst rightContains
      subst rightLength
      rfl

/-- An actual graph-derived width-two cut profile satisfies the compression
laws whenever its two named crossing ports lie in the region. -/
theorem graphProfile_isGraphSemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} {faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS 2 0 faceFragmentCount)
    (hports : data.PortsInRegion)
    (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    IsGraphSemantic (data.profile coloring hcoloring) where
  strandDiagonal pair port := by
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
      (data.crossingEdge left) (data.crossingEdge right) = _
    exact regionalTrackedConnectivity_comm RS data.regionEdges coloring pair _ _
  faceDiagonal fragment := by
    simp [GraphCorridorCutData.profile]
  faceSymmetric left right := by
    simp [GraphCorridorCutData.profile, eq_comm]

/-- The same laws hold for the open-region profile used by the source's
compositional interface.  No ambient Tait coloring is needed: only the
crossing colors and the fact that both ports lie in the displayed region. -/
theorem regionalProfile_isGraphSemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} {faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS 2 0 faceFragmentCount)
    (hports : data.PortsInRegion)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0) :
    IsGraphSemantic (data.regionalProfile color hcrossing) where
  strandDiagonal pair port := by
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
      (data.crossingEdge left) (data.crossingEdge right) = _
    exact regionalTrackedConnectivity_comm RS data.regionEdges color pair _ _
  faceDiagonal fragment := by
    simp [GraphCorridorCutData.regionalProfile]
  faceSymmetric left right := by
    simp [GraphCorridorCutData.regionalProfile, eq_comm]

/-- A common compressed carrier when the face-fragment count varies up to a
fixed bound. -/
structure BoundedWidthTwoCompressedProfile (faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : WidthTwoCompressedProfile faceFragmentCount.val
  deriving DecidableEq

private def boundedWidthTwoCompressedProfileEquiv (faceFragmentBound : Nat) :
    BoundedWidthTwoCompressedProfile faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        WidthTwoCompressedProfile faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedWidthTwoCompressedProfileFintype
    (faceFragmentBound : Nat) :
    Fintype (BoundedWidthTwoCompressedProfile faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedWidthTwoCompressedProfileEquiv faceFragmentBound).symm

def boundedWidthTwoCompressedProfileCount (faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    widthTwoCompressedProfileCount faceFragmentCount.val

theorem card_boundedWidthTwoCompressedProfile (faceFragmentBound : Nat) :
    Fintype.card (BoundedWidthTwoCompressedProfile faceFragmentBound) =
      boundedWidthTwoCompressedProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedWidthTwoCompressedProfileEquiv faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [card_widthTwoCompressedProfile]
  rfl

/-- The semantic laws required by the bounded compression are laws of its
dependent raw payload. -/
abbrev BoundedIsGraphSemantic
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound) : Prop :=
  IsGraphSemantic profile.profile

/-- Losslessly encode one semantically valid bounded width-two profile. -/
noncomputable def compressBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsGraphSemantic profile) :
    BoundedWidthTwoCompressedProfile faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compress profile.profile semantic

/-- Equality of bounded compressed codes reconstructs equality of the full
raw profiles. -/
theorem compressBounded_injective
    {faceFragmentBound : Nat}
    {left right : BoundedCorridorCutProfile 2 0 faceFragmentBound}
    (leftSemantic : BoundedIsGraphSemantic left)
    (rightSemantic : BoundedIsGraphSemantic right)
    (heq : compressBounded left leftSemantic =
      compressBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedWidthTwoCompressedProfileEquiv faceFragmentBound) heq
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

/-- Pigeonhole directly on the semantic width-two carrier.  This is the L7
replacement for pumping over arbitrary Boolean matrices: equality of the
compressed codes returns equality of the original splice profiles. -/
theorem exists_ne_profile_eq_of_semantic
    {faceFragmentBound stateCount : Nat}
    (profiles : Fin stateCount →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index, BoundedIsGraphSemantic (profiles index))
    (hlarge : boundedWidthTwoCompressedProfileCount faceFragmentBound <
      stateCount) :
    ∃ first second : Fin stateCount,
      first ≠ second ∧ profiles first = profiles second := by
  let encode : Fin stateCount →
      BoundedWidthTwoCompressedProfile faceFragmentBound := fun index =>
    compressBounded (profiles index) (semantic index)
  have hcard :
      Fintype.card (BoundedWidthTwoCompressedProfile faceFragmentBound) <
        Fintype.card (Fin stateCount) := by
    rw [card_boundedWidthTwoCompressedProfile, Fintype.card_fin]
    exact hlarge
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt encode hcard
  exact ⟨first, second, hne,
    compressBounded_injective (semantic first) (semantic second) heq⟩

/-- Adding a modulo-four tag buys three whole source positions of separation
without returning to the raw carrier count. -/
theorem exists_separated_profile_eq_of_semantic
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoCompressedProfileCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index, BoundedIsGraphSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedWidthTwoCompressedProfileCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedWidthTwoCompressedProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoCompressedProfile faceFragmentBound × Fin 4 :=
    fun index =>
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
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · have hfar : first.val + 3 < second.val := by omega
        exact False.elim (hseparated first second hfar hprofile)
      · have hfar : second.val + 3 < first.val := by omega
        exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  rw [Fintype.card_fin, Fintype.card_prod,
    card_boundedWidthTwoCompressedProfile, Fintype.card_fin] at hcard
  omega

/-- Exact compressed width-two L7 carrier size at the source-prefix
four-fragment bound. -/
theorem card_boundedWidthTwoCompressedProfile_four :
    Fintype.card (BoundedWidthTwoCompressedProfile 4) = 1536871176 := by
  rw [card_boundedWidthTwoCompressedProfile]
  norm_num [boundedWidthTwoCompressedProfileCount,
    widthTwoCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

theorem boundedWidthTwoCompressedProfileCount_four :
    boundedWidthTwoCompressedProfileCount 4 = 1536871176 := by
  norm_num [boundedWidthTwoCompressedProfileCount,
    widthTwoCompressedProfileCount, Fin.sum_univ_succ, Nat.choose]

/-- Exact separated-repeat demand after the lossless semantic compression. -/
theorem separated_widthTwoCompressedProfileCount_four :
    4 * boundedWidthTwoCompressedProfileCount 4 + 1 = 6147484705 := by
  rw [boundedWidthTwoCompressedProfileCount_four]

/-- The semantic carrier is more than five hundred thousand times smaller
than the old arbitrary-matrix carrier, with a strict remainder. -/
theorem compressed_count_times_521712_lt_raw_count :
    1536871176 * 521712 < boundedCorridorCutProfileCount 2 0 4 := by
  norm_num [boundedCorridorCutProfileCount,
    GoertzelV24CorridorProfile.corridorCutProfileCount,
    Fin.sum_univ_succ]

end GoertzelV24WidthTwoProfileCompression

end Mettapedia.GraphTheory.FourColor
