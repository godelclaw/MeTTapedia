import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoProfileCompression

/-!
# Boundary-semantic compression of width-two corridor profiles

The first width-two compression removes symmetric and forced-diagonal matrix
entries.  Actual boundary-local profiles satisfy three further laws:

* an off-diagonal tracked connection can be true only when both boundary
  colors belong to the tracked pair;
* every retained boundary face fragment contains a displayed crossing port;
* every retained fragment has positive capped length.

This file proves those laws for the generic regional-boundary construction and
stores only their admissible data.  Equality of the refined codes still
reconstructs equality of the complete raw profile.

This is a further L7 carrier compression.  It is not a claim that every code is
reachable by the heterogeneous one-Cell source transfer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoBoundarySemanticCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24WidthTwoProfileCompression
open GoertzelV24WindingClassification

/-- The colors and unique width-two off-diagonal tracked-connectivity bits,
restricted to color-compatible observations. -/
def WidthTwoStrandCode :=
  { state : (Fin 2 → StrandColor) × (TrackedColorPair → Bool) //
    ∀ pair, state.2 pair = true →
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (state.1 0).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (state.1 1).toColor }

deriving instance Fintype for WidthTwoStrandCode
deriving instance DecidableEq for WidthTwoStrandCode

/-- Exactly twenty-four color-compatible width-two strand states occur in the
refined carrier. -/
theorem card_widthTwoStrandCode : Fintype.card WidthTwoStrandCode = 24 := by
  decide

/-- A fragment row containing at least one of the two displayed ports. -/
def NonemptyWidthTwoPortRow :=
  { row : Fin 2 → Bool // ∃ port, row port = true }

deriving instance Fintype for NonemptyWidthTwoPortRow
deriving instance DecidableEq for NonemptyWidthTwoPortRow

theorem card_nonemptyWidthTwoPortRow :
    Fintype.card NonemptyWidthTwoPortRow = 3 := by
  decide

/-- A positive value in the source's cap-at-five face-length alphabet. -/
def PositiveFaceLengthCap := { cap : Fin 6 // cap.val ≠ 0 }

deriving instance Fintype for PositiveFaceLengthCap
deriving instance DecidableEq for PositiveFaceLengthCap

theorem card_positiveFaceLengthCap :
    Fintype.card PositiveFaceLengthCap = 5 := by
  decide

/-- The refined width-two state.  Face equivalence is still represented by
its symmetric off-diagonal bits; a later reachable-closure theorem may
canonicalize that relation further. -/
structure WidthTwoBoundarySemanticProfile (faceFragmentCount : Nat) where
  strand : WidthTwoStrandCode
  faceContinues : OffDiagonalPair (Fin faceFragmentCount) → Bool
  fragmentContainsPort : Fin faceFragmentCount → NonemptyWidthTwoPortRow
  faceLengthCap : Fin faceFragmentCount → PositiveFaceLengthCap
  deriving DecidableEq

private def widthTwoBoundarySemanticProfileEquiv (faceFragmentCount : Nat) :
    WidthTwoBoundarySemanticProfile faceFragmentCount ≃
      WidthTwoStrandCode ×
        (OffDiagonalPair (Fin faceFragmentCount) → Bool) ×
        (Fin faceFragmentCount → NonemptyWidthTwoPortRow) ×
        (Fin faceFragmentCount → PositiveFaceLengthCap) where
  toFun profile :=
    (profile.strand, profile.faceContinues, profile.fragmentContainsPort,
      profile.faceLengthCap)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance widthTwoBoundarySemanticProfileFintype
    (faceFragmentCount : Nat) :
    Fintype (WidthTwoBoundarySemanticProfile faceFragmentCount) :=
  Fintype.ofEquiv _
    (widthTwoBoundarySemanticProfileEquiv faceFragmentCount).symm

def widthTwoBoundarySemanticProfileCount (faceFragmentCount : Nat) : Nat :=
  24 * 2 ^ Nat.choose faceFragmentCount 2 *
    3 ^ faceFragmentCount * 5 ^ faceFragmentCount

theorem card_widthTwoBoundarySemanticProfile (faceFragmentCount : Nat) :
    Fintype.card (WidthTwoBoundarySemanticProfile faceFragmentCount) =
      widthTwoBoundarySemanticProfileCount faceFragmentCount := by
  rw [Fintype.card_congr
    (widthTwoBoundarySemanticProfileEquiv faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]
  rw [Sym2.card_subtype_not_diag, card_widthTwoStrandCode,
    card_nonemptyWidthTwoPortRow, card_positiveFaceLengthCap]
  simp only [widthTwoBoundarySemanticProfileCount, Fintype.card_fin]
  ring

/-- Additional boundary-local laws beyond symmetry and forced diagonals. -/
structure IsBoundarySemantic {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount) : Prop extends
      IsGraphSemantic profile where
  strandCompatible : ∀ pair,
    profile.strandConnected pair (.inl 0) (.inl 1) = true →
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (profile.edgeColor 0).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (profile.edgeColor 1).toColor
  fragmentContainsPortNonempty : ∀ fragment,
    ∃ port : Fin 2,
      profile.fragmentContainsPort fragment (.inl port) = true
  faceLengthCapPositive : ∀ fragment,
    (profile.faceLengthCap fragment).val ≠ 0

/-- Store only the data admitted by the boundary-semantic laws. -/
noncomputable def compressBoundary
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsBoundarySemantic profile) :
    WidthTwoBoundarySemanticProfile faceFragmentCount where
  strand :=
    ⟨(profile.edgeColor,
        fun pair => profile.strandConnected pair (.inl 0) (.inl 1)),
      semantic.strandCompatible⟩
  faceContinues unordered :=
    Sym2.lift ⟨profile.faceContinues, semantic.faceSymmetric⟩ unordered.1
  fragmentContainsPort fragment :=
    ⟨fun port => profile.fragmentContainsPort fragment (.inl port),
      semantic.fragmentContainsPortNonempty fragment⟩
  faceLengthCap fragment :=
    ⟨profile.faceLengthCap fragment,
      semantic.faceLengthCapPositive fragment⟩

/-- There is only one unordered off-diagonal pair of two ports. -/
theorem offDiagonalPair_fin_two_eq (pair : OffDiagonalPair (Fin 2)) :
    pair.1 = s(0, 1) := by
  rcases pair with ⟨unordered, hnotDiag⟩
  induction unordered using Sym2.inductionOn with
  | _ left right =>
      fin_cases left <;> fin_cases right
      · exact False.elim (hnotDiag (by simp [Sym2.IsDiag]))
      · rfl
      · exact Sym2.sound (Sym2.Rel.swap (1 : Fin 2) 0)
      · exact False.elim (hnotDiag (by simp [Sym2.IsDiag]))

/-- The boundary-semantic code is lossless on actual boundary profiles. -/
theorem compressBoundary_injective
    {faceFragmentCount : Nat}
    {left right : CorridorCutProfile 2 0 faceFragmentCount}
    (leftSemantic : IsBoundarySemantic left)
    (rightSemantic : IsBoundarySemantic right)
    (heq : compressBoundary left leftSemantic =
      compressBoundary right rightSemantic) :
    left = right := by
  apply compress_injective leftSemantic.toIsGraphSemantic
    rightSemantic.toIsGraphSemantic
  unfold compress
  rw [WidthTwoCompressedProfile.mk.injEq]
  refine ⟨congrArg (fun profile => profile.strand.1.1) heq, ?_,
    congrArg WidthTwoBoundarySemanticProfile.faceContinues heq, ?_, ?_⟩
  · funext pair unordered
    rw [offDiagonalPair_fin_two_eq unordered]
    exact congrFun
      (congrArg (fun profile => profile.strand.1.2) heq) pair
  · funext fragment port
    exact congrFun (congrArg Subtype.val
      (congrFun
        (congrArg WidthTwoBoundarySemanticProfile.fragmentContainsPort heq)
        fragment)) port
  · funext fragment
    exact congrArg Subtype.val
      (congrFun
        (congrArg WidthTwoBoundarySemanticProfile.faceLengthCap heq) fragment)

/-- Every boundary fragment of the generic indexed regional carrier contains
one displayed crossing port. -/
theorem regionalBoundaryProfile_fragmentContainsPortNonempty
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E) (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (indexedCrossingEdgeSet crossingEdge) region))) :
    ∃ port : Fin 2,
      ((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
        color hcolor).fragmentContainsPort fragment (.inl port) = true := by
  let data := regionalBoundaryGraphCutData RS region crossingEdge
  have hcolor' : ∀ index, color (data.crossingEdge index) ≠ 0 := by
    simpa [data, regionalBoundaryGraphCutData] using hcolor
  let boundaryFragment := boundaryRegionalFragmentAt RS
    (indexedCrossingEdgeSet crossingEdge) region fragment
  rcases boundaryFragment.2.2 with ⟨edge, hedgeFragment, hedgeCut⟩
  rcases (mem_indexedCrossingEdgeSet_iff crossingEdge edge).1 hedgeCut with
    ⟨port, hport⟩
  refine ⟨port,
    (data.regionalProfile_fragmentContainsPort_eq_true_iff
      color hcolor' fragment (.inl port)).2 ?_⟩
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    (regionalBoundaryGraphCutData RS region crossingEdge)
    (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
      RS region crossingEdge)]
  simpa [data, regionalBoundaryGraphCutData, GraphCorridorCutData.portEdge,
    boundaryRegionalFragmentEdges, boundaryFragment, hport] using hedgeFragment

/-- Every boundary fragment has positive capped length because it is a
nonempty connected component of an actual regional face. -/
theorem regionalBoundaryProfile_faceLengthCapPositive
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E) (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (indexedCrossingEdgeSet crossingEdge) region))) :
    (((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
      color hcolor).faceLengthCap fragment).val ≠ 0 := by
  let data := regionalBoundaryGraphCutData RS region crossingEdge
  have hcolor' : ∀ index, color (data.crossingEdge index) ≠ 0 := by
    simpa [data, regionalBoundaryGraphCutData] using hcolor
  change ((data.regionalProfile color hcolor').faceLengthCap fragment).val ≠ 0
  rw [data.regionalProfile_faceLengthCap_val color hcolor']
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    (regionalBoundaryGraphCutData RS region crossingEdge)
    (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
      RS region crossingEdge)]
  have hnonempty := boundaryRegionalFragmentEdges_nonempty RS
    (indexedCrossingEdgeSet crossingEdge) region
    (boundaryRegionalFragmentAt RS
      (indexedCrossingEdgeSet crossingEdge) region fragment)
  have hpositive : 0 < (boundaryRegionalFragmentEdges RS
      (indexedCrossingEdgeSet crossingEdge) region
      (boundaryRegionalFragmentAt RS
        (indexedCrossingEdgeSet crossingEdge) region fragment)).card :=
    Finset.card_pos.mpr hnonempty
  intro hzero
  rw [min_eq_zero] at hzero
  rcases hzero with hzero | hfive
  · exact (Finset.card_ne_zero.mpr hnonempty) hzero
  · norm_num at hfive

/-- The actual indexed regional-boundary profile satisfies every law used by
the refined compression. -/
theorem regionalBoundaryProfile_isBoundarySemantic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E)
    (hports : ∀ index, crossingEdge index ∈ region)
    (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0) :
    IsBoundarySemantic
      ((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
        color hcolor) where
  toIsGraphSemantic := regionalProfile_isGraphSemantic
    (regionalBoundaryGraphCutData RS region crossingEdge)
    (regionalBoundaryGraphCutData_portsInRegion
      RS region crossingEdge hports) color hcolor
  strandCompatible pair hconnected := by
    let data := regionalBoundaryGraphCutData RS region crossingEdge
    have hcolor' : ∀ index, color (data.crossingEdge index) ≠ 0 := by
      simpa [data, regionalBoundaryGraphCutData] using hcolor
    have hconnected' :
        (data.regionalProfile color hcolor').strandConnected
          pair (.inl 0) (.inl 1) = true := by
      simpa [data] using hconnected
    rw [data.regionalProfile_strandConnected_eq_true_iff] at hconnected'
    refine ⟨?_, ?_⟩
    · simpa [GraphCorridorCutData.portEdge] using hconnected'.2.2.1
    · simpa [GraphCorridorCutData.portEdge] using hconnected'.2.2.2.1
  fragmentContainsPortNonempty fragment :=
    regionalBoundaryProfile_fragmentContainsPortNonempty
      region crossingEdge color hcolor fragment
  faceLengthCapPositive fragment :=
    regionalBoundaryProfile_faceLengthCapPositive
      region crossingEdge color hcolor fragment

/-- A common refined carrier for boundary-local profiles with at most the
displayed number of face fragments. -/
structure BoundedWidthTwoBoundarySemanticProfile
    (faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : WidthTwoBoundarySemanticProfile faceFragmentCount.val
  deriving DecidableEq

private def boundedWidthTwoBoundarySemanticProfileEquiv
    (faceFragmentBound : Nat) :
    BoundedWidthTwoBoundarySemanticProfile faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        WidthTwoBoundarySemanticProfile faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedWidthTwoBoundarySemanticProfileFintype
    (faceFragmentBound : Nat) :
    Fintype (BoundedWidthTwoBoundarySemanticProfile faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedWidthTwoBoundarySemanticProfileEquiv faceFragmentBound).symm

def boundedWidthTwoBoundarySemanticProfileCount
    (faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    widthTwoBoundarySemanticProfileCount faceFragmentCount.val

theorem card_boundedWidthTwoBoundarySemanticProfile
    (faceFragmentBound : Nat) :
    Fintype.card (BoundedWidthTwoBoundarySemanticProfile faceFragmentBound) =
      boundedWidthTwoBoundarySemanticProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedWidthTwoBoundarySemanticProfileEquiv faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [card_widthTwoBoundarySemanticProfile]
  rfl

/-- Boundary-semantic validity of the dependent raw payload of a bounded
profile. -/
abbrev BoundedIsBoundarySemantic
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound) : Prop :=
  IsBoundarySemantic profile.profile

/-- Losslessly encode one bounded boundary-semantic profile. -/
noncomputable def compressBoundaryBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsBoundarySemantic profile) :
    BoundedWidthTwoBoundarySemanticProfile faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compressBoundary profile.profile semantic

theorem compressBoundaryBounded_injective
    {faceFragmentBound : Nat}
    {left right : BoundedCorridorCutProfile 2 0 faceFragmentBound}
    (leftSemantic : BoundedIsBoundarySemantic left)
    (rightSemantic : BoundedIsBoundarySemantic right)
    (heq : compressBoundaryBounded left leftSemantic =
      compressBoundaryBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedWidthTwoBoundarySemanticProfileEquiv faceFragmentBound) heq
      obtain ⟨hcount, hprofileHeq⟩ := Sigma.mk.inj_iff.mp hsigma
      simp only [compressBoundaryBounded] at hcount hprofileHeq
      subst rightCount
      have hprofile :
          compressBoundary leftProfile leftSemantic =
            compressBoundary rightProfile rightSemantic :=
        eq_of_heq hprofileHeq
      have hraw : leftProfile = rightProfile :=
        compressBoundary_injective leftSemantic rightSemantic hprofile
      subst rightProfile
      rfl

/-- A modulo-four tag turns cardinality into the gap-at-least-four source
repeat while retaining equality of the complete raw profiles. -/
theorem exists_separated_profile_eq_of_boundarySemantic
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoBoundarySemanticProfileCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index, BoundedIsBoundarySemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedWidthTwoBoundarySemanticProfileCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedWidthTwoBoundarySemanticProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoBoundarySemanticProfile faceFragmentBound × Fin 4 :=
    fun index =>
      (compressBoundaryBounded (profiles index) (semantic index),
        ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hcode :
        compressBoundaryBounded (profiles first) (semantic first) =
          compressBoundaryBounded (profiles second) (semantic second) :=
      congrArg Prod.fst heq
    have hprofile : profiles first = profiles second :=
      compressBoundaryBounded_injective
        (semantic first) (semantic second) hcode
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
    card_boundedWidthTwoBoundarySemanticProfile, Fintype.card_fin] at hcard
  omega

/-- Exact refined carrier size at the four-fragment source-prefix bound. -/
theorem boundedWidthTwoBoundarySemanticProfileCount_four :
    boundedWidthTwoBoundarySemanticProfileCount 4 = 78419184 := by
  norm_num [boundedWidthTwoBoundarySemanticProfileCount,
    widthTwoBoundarySemanticProfileCount, Fin.sum_univ_succ, Nat.choose]

/-- Exact gap-at-least-four L7 demand over the refined carrier. -/
theorem separated_boundedWidthTwoBoundarySemanticProfileCount_four :
    4 * boundedWidthTwoBoundarySemanticProfileCount 4 + 1 = 313676737 := by
  rw [boundedWidthTwoBoundarySemanticProfileCount_four]

/-- The refined carrier is more than ten million times smaller than the old
arbitrary-matrix source-prefix carrier. -/
theorem refined_count_times_10224605_lt_raw_count :
    78419184 * 10224605 < boundedCorridorCutProfileCount 2 0 4 := by
  norm_num [boundedCorridorCutProfileCount,
    GoertzelV24CorridorProfile.corridorCutProfileCount,
    Fin.sum_univ_succ]

end GoertzelV24WidthTwoBoundarySemanticCompression

end Mettapedia.GraphTheory.FourColor
