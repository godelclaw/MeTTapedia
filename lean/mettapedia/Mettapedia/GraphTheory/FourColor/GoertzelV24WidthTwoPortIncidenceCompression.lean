import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFaceEquivalenceCompression

/-!
# Port-incidence compression of width-two boundary profiles

Every displayed cut edge has exactly two darts.  Consequently an actual
regional-boundary profile can place either displayed port in at most two
occurrence-sensitive face fragments.  This remains true for a bridge whose
two dart occurrences lie on the same quotient face; no global two-sided-face
hypothesis is used.

This file adds that graph-semantic law to the lossless width-two carrier.  At
the four-fragment source bound it removes the impossible rows in which one
cut edge occurs in three or four fragments.  It is an L7 carrier compression,
not a reachable-closure certificate and not a base verification.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthTwoPortIncidenceCompression

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoFaceEquivalenceCompression
open SimpleGraphDartRotation

/-- Nonempty width-two incidence rows in which each displayed port occurs in
at most two fragments. -/
def WidthTwoPortIncidenceCode (faceFragmentCount : Nat) :=
  { rows : Fin faceFragmentCount → NonemptyWidthTwoPortRow //
    ∀ port : Fin 2,
      ((Finset.univ : Finset (Fin faceFragmentCount)).filter fun fragment =>
        (rows fragment).1 port = true).card ≤ 2 }

deriving instance Fintype for WidthTwoPortIncidenceCode
deriving instance DecidableEq for WidthTwoPortIncidenceCode

theorem card_widthTwoPortIncidenceCode_zero :
    Fintype.card (WidthTwoPortIncidenceCode 0) = 1 := by decide

theorem card_widthTwoPortIncidenceCode_one :
    Fintype.card (WidthTwoPortIncidenceCode 1) = 3 := by decide

theorem card_widthTwoPortIncidenceCode_two :
    Fintype.card (WidthTwoPortIncidenceCode 2) = 9 := by decide

theorem card_widthTwoPortIncidenceCode_three :
    Fintype.card (WidthTwoPortIncidenceCode 3) = 12 := by decide

set_option maxRecDepth 100000 in
theorem card_widthTwoPortIncidenceCode_four :
    Fintype.card (WidthTwoPortIncidenceCode 4) = 6 := by decide

/-- The actual profile laws used by the port-incidence compression. -/
structure IsPortIncidenceSemantic {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount) : Prop extends
      IsFaceEquivalenceSemantic profile where
  portMultiplicity : ∀ port : Fin 2,
    ((Finset.univ : Finset (Fin faceFragmentCount)).filter fun fragment =>
      profile.fragmentContainsPort fragment (.inl port) = true).card ≤ 2

/-- Face-equivalence profiles with the occurrence-sensitive port rows
restricted to graph-realizable multiplicities. -/
structure WidthTwoPortIncidenceProfile (faceFragmentCount : Nat) where
  strand : WidthTwoStrandCode
  face : FaceEquivalenceCode faceFragmentCount
  fragmentContainsPort : WidthTwoPortIncidenceCode faceFragmentCount
  faceLengthCap : Fin faceFragmentCount → PositiveFaceLengthCap
  deriving DecidableEq

private def widthTwoPortIncidenceProfileEquiv (faceFragmentCount : Nat) :
    WidthTwoPortIncidenceProfile faceFragmentCount ≃
      WidthTwoStrandCode × FaceEquivalenceCode faceFragmentCount ×
        WidthTwoPortIncidenceCode faceFragmentCount ×
        (Fin faceFragmentCount → PositiveFaceLengthCap) where
  toFun profile :=
    (profile.strand, profile.face, profile.fragmentContainsPort,
      profile.faceLengthCap)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance widthTwoPortIncidenceProfileFintype
    (faceFragmentCount : Nat) :
    Fintype (WidthTwoPortIncidenceProfile faceFragmentCount) :=
  Fintype.ofEquiv _
    (widthTwoPortIncidenceProfileEquiv faceFragmentCount).symm

def widthTwoPortIncidenceProfileCount (faceFragmentCount : Nat) : Nat :=
  24 * Fintype.card (FaceEquivalenceCode faceFragmentCount) *
    Fintype.card (WidthTwoPortIncidenceCode faceFragmentCount) *
    5 ^ faceFragmentCount

theorem card_widthTwoPortIncidenceProfile (faceFragmentCount : Nat) :
    Fintype.card (WidthTwoPortIncidenceProfile faceFragmentCount) =
      widthTwoPortIncidenceProfileCount faceFragmentCount := by
  rw [Fintype.card_congr
    (widthTwoPortIncidenceProfileEquiv faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun]
  rw [card_widthTwoStrandCode, card_positiveFaceLengthCap]
  simp only [widthTwoPortIncidenceProfileCount, Fintype.card_fin]
  ring

/-- Encode one port-incidence semantic profile. -/
noncomputable def compressPortIncidence
    {faceFragmentCount : Nat}
    (profile : CorridorCutProfile 2 0 faceFragmentCount)
    (semantic : IsPortIncidenceSemantic profile) :
    WidthTwoPortIncidenceProfile faceFragmentCount where
  strand := (compressFaceEquivalence profile
    semantic.toIsFaceEquivalenceSemantic).strand
  face := (compressFaceEquivalence profile
    semantic.toIsFaceEquivalenceSemantic).face
  fragmentContainsPort :=
    ⟨(compressFaceEquivalence profile
      semantic.toIsFaceEquivalenceSemantic).fragmentContainsPort,
      semantic.portMultiplicity⟩
  faceLengthCap := (compressFaceEquivalence profile
    semantic.toIsFaceEquivalenceSemantic).faceLengthCap

/-- Port-incidence compression remains lossless on actual profiles. -/
theorem compressPortIncidence_injective
    {faceFragmentCount : Nat}
    {left right : CorridorCutProfile 2 0 faceFragmentCount}
    (leftSemantic : IsPortIncidenceSemantic left)
    (rightSemantic : IsPortIncidenceSemantic right)
    (heq : compressPortIncidence left leftSemantic =
      compressPortIncidence right rightSemantic) :
    left = right := by
  apply compressFaceEquivalence_injective
    leftSemantic.toIsFaceEquivalenceSemantic
    rightSemantic.toIsFaceEquivalenceSemantic
  rw [WidthTwoFaceEquivalenceProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [compressPortIncidence] using
      congrArg WidthTwoPortIncidenceProfile.strand heq
  · simpa [compressPortIncidence] using
      congrArg WidthTwoPortIncidenceProfile.face heq
  · apply funext
    intro fragment
    have hrows := congrArg
      (fun profile => profile.fragmentContainsPort.1) heq
    exact congrFun hrows fragment
  · simpa [compressPortIncidence] using
      congrArg WidthTwoPortIncidenceProfile.faceLengthCap heq

section RegionalMultiplicity

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A cyclic position witnessing that a fixed edge belongs to a selected
boundary fragment. -/
noncomputable def boundaryRegionalFragmentEdgePosition
    (RS : RotationSystem V E) (cut region : Finset E) (edge : E)
    (fragment : { fragment : BoundaryRegionalFragment RS cut region //
      edge ∈ boundaryRegionalFragmentEdges RS cut region fragment }) :
    Fin (RS.faceOrbit (orbitFaceRoot RS fragment.1.1.1)).card :=
  Classical.choose <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1.1) region fragment.1.2.1 edge).1
        fragment.2

theorem boundaryRegionalFragmentEdgePosition_mem
    (RS : RotationSystem V E) (cut region : Finset E) (edge : E)
    (fragment : { fragment : BoundaryRegionalFragment RS cut region //
      edge ∈ boundaryRegionalFragmentEdges RS cut region fragment }) :
    boundaryRegionalFragmentEdgePosition RS cut region edge fragment ∈
      faceRegionalFragmentPositions RS
        (orbitFaceRoot RS fragment.1.1.1) region fragment.1.2.1 :=
  (Classical.choose_spec <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1.1) region fragment.1.2.1 edge).1
        fragment.2).1

theorem boundaryRegionalFragmentEdgePosition_edge
    (RS : RotationSystem V E) (cut region : Finset E) (edge : E)
    (fragment : { fragment : BoundaryRegionalFragment RS cut region //
      edge ∈ boundaryRegionalFragmentEdges RS cut region fragment }) :
    faceCycleEdge RS (orbitFaceRoot RS fragment.1.1.1)
        (boundaryRegionalFragmentEdgePosition RS cut region edge fragment) =
      edge :=
  (Classical.choose_spec <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1.1) region fragment.1.2.1 edge).1
        fragment.2).2

/-- Map each boundary fragment containing a fixed edge to the actual dart
occurrence of that edge in that fragment. -/
noncomputable def boundaryRegionalFragmentEdgeDart
    (RS : RotationSystem V E) (cut region : Finset E) (edge : E)
    (fragment : { fragment : BoundaryRegionalFragment RS cut region //
      edge ∈ boundaryRegionalFragmentEdges RS cut region fragment }) :
    { dart : RS.D // dart ∈ RS.dartsOn edge } :=
  ⟨faceCycleDart RS (orbitFaceRoot RS fragment.1.1.1)
      (boundaryRegionalFragmentEdgePosition RS cut region edge fragment),
    (RS.mem_dartsOn).2
      (boundaryRegionalFragmentEdgePosition_edge
        RS cut region edge fragment)⟩

/-- Distinct occurrence-sensitive fragments containing one edge use distinct
darts.  This is valid even when both darts lie on the same quotient face. -/
theorem boundaryRegionalFragmentEdgeDart_injective
    (RS : RotationSystem V E) (cut region : Finset E) (edge : E) :
    Function.Injective
      (boundaryRegionalFragmentEdgeDart RS cut region edge) := by
  intro left right heq
  have hdart :
      faceCycleDart RS (orbitFaceRoot RS left.1.1.1)
          (boundaryRegionalFragmentEdgePosition RS cut region edge left) =
        faceCycleDart RS (orbitFaceRoot RS right.1.1.1)
          (boundaryRegionalFragmentEdgePosition RS cut region edge right) :=
    congrArg Subtype.val heq
  have hface : left.1.1.1 = right.1.1.1 := by
    calc
      left.1.1.1 = dartOrbitFace RS
          (faceCycleDart RS (orbitFaceRoot RS left.1.1.1)
            (boundaryRegionalFragmentEdgePosition
              RS cut region edge left)) := by
        rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
      _ = dartOrbitFace RS
          (faceCycleDart RS (orbitFaceRoot RS right.1.1.1)
            (boundaryRegionalFragmentEdgePosition
              RS cut region edge right)) := by rw [hdart]
      _ = right.1.1.1 := by
        rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
  rcases left with
    ⟨⟨leftFace, ⟨leftFragment, leftTouches⟩⟩, leftEdge⟩
  rcases right with
    ⟨⟨rightFace, ⟨rightFragment, rightTouches⟩⟩, rightEdge⟩
  dsimp only at hface
  have hfaceSubtype : leftFace = rightFace := Subtype.ext hface
  subst rightFace
  have hposition :
      boundaryRegionalFragmentEdgePosition RS cut region edge
          ⟨⟨leftFace, ⟨leftFragment, leftTouches⟩⟩, leftEdge⟩ =
        boundaryRegionalFragmentEdgePosition RS cut region edge
          ⟨⟨leftFace, ⟨rightFragment, rightTouches⟩⟩, rightEdge⟩ := by
    apply faceCycleDart_injective RS (orbitFaceRoot RS leftFace.1)
    exact hdart
  have hfragment : leftFragment = rightFragment := by
    by_contra hne
    have hdisjoint := disjoint_faceRegionalFragmentPositions_of_ne RS
      (orbitFaceRoot RS leftFace.1) region hne
    have hleftMem := boundaryRegionalFragmentEdgePosition_mem RS cut region
      edge ⟨⟨leftFace, ⟨leftFragment, leftTouches⟩⟩, leftEdge⟩
    have hrightMem := boundaryRegionalFragmentEdgePosition_mem RS cut region
      edge ⟨⟨leftFace, ⟨rightFragment, rightTouches⟩⟩, rightEdge⟩
    exact (Finset.disjoint_left.1 hdisjoint) hleftMem
      (hposition ▸ hrightMem)
  subst rightFragment
  rfl

/-- For a literal indexed regional boundary, one displayed port occurs in at
most two fragments because its edge has exactly two dart occurrences. -/
theorem regionalBoundaryProfile_portMultiplicity
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E)
    (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0)
    (port : Fin 2) :
    ((Finset.univ : Finset
        (Fin (Fintype.card (BoundaryRegionalFragment RS
          (indexedCrossingEdgeSet crossingEdge) region)))).filter fun fragment =>
      ((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
        color hcolor).fragmentContainsPort fragment (.inl port) = true).card ≤
      2 := by
  let cut := indexedCrossingEdgeSet crossingEdge
  let data := regionalBoundaryGraphCutData RS region crossingEdge
  have hcolor' : ∀ index, color (data.crossingEdge index) ≠ 0 := by
    simpa [data, regionalBoundaryGraphCutData] using hcolor
  let FragmentAtPort :=
      { fragment : Fin (Fintype.card (BoundaryRegionalFragment RS cut region)) //
        (data.regionalProfile color hcolor').fragmentContainsPort
          fragment (.inl port) = true }
  let toFragment : FragmentAtPort →
      { fragment : BoundaryRegionalFragment RS cut region //
        crossingEdge port ∈
          boundaryRegionalFragmentEdges RS cut region fragment } :=
    fun fragment =>
      ⟨boundaryRegionalFragmentAt RS cut region fragment.1, by
        have hmember :=
          (data.regionalProfile_fragmentContainsPort_eq_true_iff
            color hcolor' fragment.1 (.inl port)).1 fragment.2
        rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
          (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
            RS region crossingEdge)] at hmember
        simpa [data, cut, regionalBoundaryGraphCutData,
          GraphCorridorCutData.portEdge] using hmember⟩
  let encode : FragmentAtPort →
      { dart : RS.D // dart ∈ RS.dartsOn (crossingEdge port) } :=
    fun fragment =>
      boundaryRegionalFragmentEdgeDart RS cut region (crossingEdge port)
        (toFragment fragment)
  have hinjective : Function.Injective encode := by
    intro left right heq
    have hfragments : toFragment left = toFragment right :=
      boundaryRegionalFragmentEdgeDart_injective RS cut region
        (crossingEdge port) heq
    apply Subtype.ext
    apply boundaryRegionalFragmentAt_injective RS cut region
    exact congrArg Subtype.val hfragments
  calc
    ((Finset.univ : Finset
        (Fin (Fintype.card (BoundaryRegionalFragment RS cut region)))).filter
      fun fragment =>
        (data.regionalProfile color hcolor').fragmentContainsPort
          fragment (.inl port) = true).card =
        Fintype.card FragmentAtPort := by
      rw [Fintype.card_subtype]
    _ ≤
        Fintype.card
          { dart : RS.D // dart ∈ RS.dartsOn (crossingEdge port) } :=
      Fintype.card_le_of_injective encode hinjective
    _ = (RS.dartsOn (crossingEdge port)).card := Fintype.card_coe _
    _ = 2 := RS.dartsOn_card_two (crossingEdge port)

/-- Actual indexed regional-boundary profiles satisfy every law used by the
port-incidence compression. -/
theorem regionalBoundaryProfile_isPortIncidenceSemantic
    {RS : RotationSystem V E} (region : Finset E)
    (crossingEdge : Fin 2 → E)
    (hports : ∀ index, crossingEdge index ∈ region)
    (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0) :
    IsPortIncidenceSemantic
      ((regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
        color hcolor) where
  toIsFaceEquivalenceSemantic :=
    regionalBoundaryProfile_isFaceEquivalenceSemantic
      region crossingEdge hports color hcolor
  portMultiplicity port :=
    regionalBoundaryProfile_portMultiplicity
      region crossingEdge color hcolor port

end RegionalMultiplicity

/-- Bounded port-incidence carrier. -/
structure BoundedWidthTwoPortIncidenceProfile
    (faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : WidthTwoPortIncidenceProfile faceFragmentCount.val
  deriving DecidableEq

private def boundedWidthTwoPortIncidenceProfileEquiv
    (faceFragmentBound : Nat) :
    BoundedWidthTwoPortIncidenceProfile faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        WidthTwoPortIncidenceProfile faceFragmentCount.val where
  toFun profile := ⟨profile.faceFragmentCount, profile.profile⟩
  invFun profile := ⟨profile.1, profile.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedWidthTwoPortIncidenceProfileFintype
    (faceFragmentBound : Nat) :
    Fintype (BoundedWidthTwoPortIncidenceProfile faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedWidthTwoPortIncidenceProfileEquiv faceFragmentBound).symm

def boundedWidthTwoPortIncidenceProfileCount
    (faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    widthTwoPortIncidenceProfileCount faceFragmentCount.val

theorem card_boundedWidthTwoPortIncidenceProfile
    (faceFragmentBound : Nat) :
    Fintype.card (BoundedWidthTwoPortIncidenceProfile faceFragmentBound) =
      boundedWidthTwoPortIncidenceProfileCount faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedWidthTwoPortIncidenceProfileEquiv faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [card_widthTwoPortIncidenceProfile]
  rfl

abbrev BoundedIsPortIncidenceSemantic
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound) : Prop :=
  IsPortIncidenceSemantic profile.profile

noncomputable def compressPortIncidenceBounded
    {faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : BoundedIsPortIncidenceSemantic profile) :
    BoundedWidthTwoPortIncidenceProfile faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := compressPortIncidence profile.profile semantic

theorem compressPortIncidenceBounded_injective
    {faceFragmentBound : Nat}
    {left right : BoundedCorridorCutProfile 2 0 faceFragmentBound}
    (leftSemantic : BoundedIsPortIncidenceSemantic left)
    (rightSemantic : BoundedIsPortIncidenceSemantic right)
    (heq : compressPortIncidenceBounded left leftSemantic =
      compressPortIncidenceBounded right rightSemantic) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      have hsigma := congrArg
        (boundedWidthTwoPortIncidenceProfileEquiv faceFragmentBound) heq
      obtain ⟨hcount, hprofileHeq⟩ := Sigma.mk.inj_iff.mp hsigma
      simp only [compressPortIncidenceBounded] at hcount hprofileHeq
      subst rightCount
      have hprofile :
          compressPortIncidence leftProfile leftSemantic =
            compressPortIncidence rightProfile rightSemantic :=
        eq_of_heq hprofileHeq
      have hraw : leftProfile = rightProfile :=
        compressPortIncidence_injective
          leftSemantic rightSemantic hprofile
      subst rightProfile
      rfl

theorem exists_separated_profile_eq_of_portIncidenceSemantic
    {faceFragmentBound : Nat}
    (profiles : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount faceFragmentBound + 1) →
      BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (semantic : ∀ index,
      BoundedIsPortIncidenceSemantic (profiles index)) :
    ∃ first second : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount faceFragmentBound + 1),
      first.val + 3 < second.val ∧ profiles first = profiles second := by
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount faceFragmentBound + 1) →
      BoundedWidthTwoPortIncidenceProfile faceFragmentBound × Fin 4 :=
    fun index =>
      (compressPortIncidenceBounded (profiles index) (semantic index),
        ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hcode := congrArg Prod.fst heq
    have hprofile : profiles first = profiles second :=
      compressPortIncidenceBounded_injective
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
    card_boundedWidthTwoPortIncidenceProfile, Fintype.card_fin] at hcard
  omega

/-- Exact four-fragment carrier after the occurrence-sensitive port bound. -/
theorem boundedWidthTwoPortIncidenceProfileCount_four :
    boundedWidthTwoPortIncidenceProfileCount 4 = 1541184 := by
  norm_num [boundedWidthTwoPortIncidenceProfileCount,
    widthTwoPortIncidenceProfileCount, Fin.sum_univ_succ,
    card_faceEquivalenceCode_zero, card_faceEquivalenceCode_one,
    card_faceEquivalenceCode_two, card_faceEquivalenceCode_three,
    card_faceEquivalenceCode_four,
    card_widthTwoPortIncidenceCode_zero,
    card_widthTwoPortIncidenceCode_one,
    card_widthTwoPortIncidenceCode_two,
    card_widthTwoPortIncidenceCode_three,
    card_widthTwoPortIncidenceCode_four]

theorem separated_boundedWidthTwoPortIncidenceProfileCount_four :
    4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1 = 6164737 := by
  rw [boundedWidthTwoPortIncidenceProfileCount_four]

end GoertzelV24WidthTwoPortIncidenceCompression

end Mettapedia.GraphTheory.FourColor
