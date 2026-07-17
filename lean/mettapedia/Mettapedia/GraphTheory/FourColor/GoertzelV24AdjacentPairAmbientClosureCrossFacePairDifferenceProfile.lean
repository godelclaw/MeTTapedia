import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairRepair

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossFacePairDifferenceProfileGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24MinimalFaceIntersections

/-- The two binary incidences of an ambient edge with the selected
source edge's left and right quotient faces. -/
def edgeCrossFaceProfile
    (graphData : Data G) (source edge : G.edgeSet) : Color :=
  (orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels (edgeLeftOrbitFace graphData source)) edge,
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
      (singletonOrbitFaceLabels (edgeRightOrbitFace graphData source)) edge)

/-- Recoloring the two face-incidence coordinates is exactly the paired
facial transfer. -/
theorem edgeTwoFaceColorTransfer_eq_colorBasisAddHom_edgeCrossFaceProfile
    (graphData : Data G) (source : G.edgeSet)
    (first second : Color) (edge : G.edgeSet) :
    edgeTwoFaceColorTransfer graphData source first second edge =
      colorBasisAddHom first second
        (edgeCrossFaceProfile graphData source edge) :=
  rfl

/-- Both face-incidence coordinates are one exactly on the selected
source edge. -/
theorem edgeCrossFaceProfile_eq_purple_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source edge : G.edgeSet) :
    edgeCrossFaceProfile graphData source edge = purple ↔ edge = source := by
  rw [Prod.ext_iff]
  change
    (orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeLeftOrbitFace graphData source))
          edge = 1 ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels (edgeRightOrbitFace graphData source))
          edge = 1) ↔ edge = source
  exact edgeLeft_right_singletonBoundary_eq_one_iff
    graphData minimal source edge

@[simp]
theorem edgeCrossFaceProfile_source
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) :
    edgeCrossFaceProfile graphData source source = purple :=
  (edgeCrossFaceProfile_eq_purple_iff graphData minimal source source).2 rfl

private theorem colorBasisAddHom_red_blue (color : Color) :
    colorBasisAddHom red blue color = color := by
  rcases color with ⟨first, second⟩
  ext <;> simp [colorBasisAddHom, red, blue]

/-- The paired binary incidence of the two cross-side faces is itself a
graph flow. -/
theorem edgeCrossFaceProfile_isGraphFlow
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) :
    IsGraphFlow G (edgeCrossFaceProfile graphData source) := by
  have hflow := edgeTwoFaceColorTransfer_isGraphFlow graphData minimal
    source red blue
  have heq : edgeTwoFaceColorTransfer graphData source red blue =
      edgeCrossFaceProfile graphData source := by
    funext edge
    rw [edgeTwoFaceColorTransfer_eq_colorBasisAddHom_edgeCrossFaceProfile,
      colorBasisAddHom_red_blue]
  rwa [heq] at hflow

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Coordinatewise disagreement between the exact two-closure cut and
the two singleton face cuts incident to the retained cross. -/
def CrossCentralExactFaceCutPair.crossFaceDifferenceProfile
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet) : Color :=
  pair.edgeTransfer edge +
    edgeCrossFaceProfile graphData
      (retainedEdgeToAmbientEdge data cross) edge

/-- Face labels for the first exact cut after toggling the singleton face
on the representative-dart side of the retained cross. -/
def CrossCentralExactFaceCutPair.prefixCrossFaceToggledLabels
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem) : F2 :=
  pair.prefixLabels face +
    singletonOrbitFaceLabels
      (edgeLeftOrbitFace graphData (retainedEdgeToAmbientEdge data cross)) face

/-- Face labels for the second exact cut after toggling the singleton face
on the opposite-dart side of the retained cross. -/
def CrossCentralExactFaceCutPair.suffixCrossFaceToggledLabels
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem) : F2 :=
  pair.suffixLabels face +
    singletonOrbitFaceLabels
      (edgeRightOrbitFace graphData (retainedEdgeToAmbientEdge data cross)) face

/-- The first disagreement bit is the facial boundary of the toggled
first-coordinate labels. -/
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_fst
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet) :
    (pair.crossFaceDifferenceProfile edge).1 =
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
        pair.prefixCrossFaceToggledLabels edge := by
  change
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
          pair.prefixLabels edge +
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels
            (edgeLeftOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross))) edge =
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (pair.prefixLabels + singletonOrbitFaceLabels
          (edgeLeftOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross))) edge
  rw [map_add]
  rfl

/-- The second disagreement bit is the facial boundary of the toggled
second-coordinate labels. -/
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_snd
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet) :
    (pair.crossFaceDifferenceProfile edge).2 =
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
        pair.suffixCrossFaceToggledLabels edge := by
  change
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
          pair.suffixLabels edge +
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          (singletonOrbitFaceLabels
            (edgeRightOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross))) edge =
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (pair.suffixLabels + singletonOrbitFaceLabels
          (edgeRightOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross))) edge
  rw [map_add]
  rfl

/-- The coordinate-disagreement profile is a graph flow: it is the sum
of the exact paired closure flow and the paired singleton-face flow. -/
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    IsGraphFlow G pair.crossFaceDifferenceProfile := by
  exact (pair.edgeTransfer_isGraphFlow minimal).add
    (edgeCrossFaceProfile_isGraphFlow graphData minimal
      (retainedEdgeToAmbientEdge data cross))

/-- The repaired chain is the singleton-zero chain plus the rebased
difference profile. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_apply_profile
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    pair.oneZeroCrossFacePairPerturbation C first second edge =
      oneZeroAmbientChain data C edge +
        colorBasisAddHom first second
          (pair.crossFaceDifferenceProfile edge) := by
  rw [pair.oneZeroCrossFacePairPerturbation_apply,
    pair.oneZeroClosureBasisPerturbation_apply,
    pair.edgeTransferInBasis_apply,
    edgeTwoFaceColorTransfer_eq_colorBasisAddHom_edgeCrossFaceProfile,
    CrossCentralExactFaceCutPair.crossFaceDifferenceProfile,
    map_add]
  abel

/-- A repaired zero is exactly an agreement between the reconstructed
color and the rebased difference profile. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_eq_zero_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    pair.oneZeroCrossFacePairPerturbation C first second edge = 0 ↔
      oneZeroAmbientChain data C edge =
        colorBasisAddHom first second
          (pair.crossFaceDifferenceProfile edge) := by
  rw [pair.oneZeroCrossFacePairPerturbation_apply_profile]
  exact add_eq_zero_iff_eq _ _

/-- Toggling both exact cut coordinates by their corresponding singleton
cross-side faces removes the retained cross from the paired profile. -/
@[simp]
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.crossFaceDifferenceProfile
        (retainedEdgeToAmbientEdge data cross) = 0 := by
  rw [CrossCentralExactFaceCutPair.crossFaceDifferenceProfile,
    pair.edgeTransfer_retainedCross minimal,
    edgeCrossFaceProfile_source graphData minimal, color_add_self]

/-- The toggled profile remains nonzero on the restored central edge,
because both singleton cross faces can meet together only on the retained
cross itself. -/
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_centralEdge_ne_zero
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.crossFaceDifferenceProfile (centralEdge data) ≠ 0 := by
  rw [CrossCentralExactFaceCutPair.crossFaceDifferenceProfile,
    pair.edgeTransfer_centralEdge minimal]
  intro hzero
  have hprofile : edgeCrossFaceProfile graphData
      (retainedEdgeToAmbientEdge data cross) (centralEdge data) =
        purple :=
    ((add_eq_zero_iff_eq purple _).1 hzero).symm
  have heq : centralEdge data = retainedEdgeToAmbientEdge data cross :=
    (edgeCrossFaceProfile_eq_purple_iff graphData minimal
      (retainedEdgeToAmbientEdge data cross) (centralEdge data)).1 hprofile
  exact (retainedEdgeToAmbientEdge_ne_centralEdge data cross) heq.symm

/-- Any repaired zero away from the central edge witnesses a genuine
coordinate disagreement between the exact closure cuts and the two
cross-side singleton face cuts. -/
theorem CrossCentralExactFaceCutPair.crossFaceDifferenceProfile_ne_zero_of_repaired_zero
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (first second : Color) (edge : G.edgeSet)
    (hedge : edge ≠ centralEdge data)
    (hzero : pair.oneZeroCrossFacePairPerturbation C first second edge = 0) :
    pair.crossFaceDifferenceProfile edge ≠ 0 := by
  intro hdifference
  have hagree :=
    (pair.oneZeroCrossFacePairPerturbation_eq_zero_iff
      C first second edge).1 hzero
  rw [hdifference, map_zero] at hagree
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  exact hedge
    ((oneZeroAmbientChain_eq_zero_iff data hcubic C hC edge).1 hagree)

private theorem six_color_disagreement_cases
    (exactProfile faceProfile : Color)
    (hexact : exactProfile ≠ purple)
    (hface : faceProfile ≠ purple)
    (hdifference : exactProfile + faceProfile ≠ 0) :
    (exactProfile = 0 ∧ faceProfile = red) ∨
      (exactProfile = red ∧ faceProfile = 0) ∨
      (exactProfile = 0 ∧ faceProfile = blue) ∨
      (exactProfile = blue ∧ faceProfile = 0) ∨
      (exactProfile = red ∧ faceProfile = blue) ∨
      (exactProfile = blue ∧ faceProfile = red) := by
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple exactProfile with
      he | he | he | he <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple faceProfile with
      hf | hf | hf | hf <;>
    simp_all [red, blue, purple]

/-- Away from the retained cross and central edge, every nonzero toggled
profile has exactly one of six forms: the exact cut and singleton-face
profiles are two distinct letters among `0`, `red`, and `blue`. -/
theorem CrossCentralExactFaceCutPair.crossFaceProfile_six_disagreement_cases
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet)
    (hcross : edge ≠ retainedEdgeToAmbientEdge data cross)
    (hcentral : edge ≠ centralEdge data)
    (hdifference : pair.crossFaceDifferenceProfile edge ≠ 0) :
    (pair.edgeTransfer edge = 0 ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = red) ∨
      (pair.edgeTransfer edge = red ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = 0) ∨
      (pair.edgeTransfer edge = 0 ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = blue) ∨
      (pair.edgeTransfer edge = blue ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = 0) ∨
      (pair.edgeTransfer edge = red ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = blue) ∨
      (pair.edgeTransfer edge = blue ∧
        edgeCrossFaceProfile graphData
          (retainedEdgeToAmbientEdge data cross) edge = red) := by
  have hexact : pair.edgeTransfer edge ≠ purple := by
    intro hpurple
    rcases (pair.edgeTransfer_eq_purple_iff minimal edge).1 hpurple with
      hsource | hcentralValue
    · exact hcross (Subtype.ext hsource)
    · exact hcentral (Subtype.ext hcentralValue)
  have hface : edgeCrossFaceProfile graphData
      (retainedEdgeToAmbientEdge data cross) edge ≠ purple := by
    intro hpurple
    exact hcross
      ((edgeCrossFaceProfile_eq_purple_iff graphData minimal
        (retainedEdgeToAmbientEdge data cross) edge).1 hpurple)
  apply six_color_disagreement_cases _ _ hexact hface
  simpa only [CrossCentralExactFaceCutPair.crossFaceDifferenceProfile]
    using hdifference

/-- Once the paired repair is nonzero on both endpoint stars and on the
central edge, some residual zero realizes one of the six strict cut-profile
disagreements away from the whole repaired configuration. -/
theorem CrossCentralExactFaceCutPair.exists_six_profile_disagreement_off_repaired_cross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) (entry exit : V)
    (hsourceIncident : retainedEdgeToAmbientEdge data cross ∈
      incidentEdgeFinset G entry)
    (hentry : ∀ edge ∈ incidentEdgeFinset G entry,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0)
    (hexit : ∀ edge ∈ incidentEdgeFinset G exit,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0)
    (hcentral : pair.oneZeroCrossFacePairPerturbation C first second
      (centralEdge data) ≠ 0) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C first second edge = 0 ∧
        pair.crossFaceDifferenceProfile edge ≠ 0 ∧
        ((pair.edgeTransfer edge = 0 ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = red) ∨
          (pair.edgeTransfer edge = red ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = 0) ∨
          (pair.edgeTransfer edge = 0 ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = blue) ∨
          (pair.edgeTransfer edge = blue ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = 0) ∨
          (pair.edgeTransfer edge = red ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = blue) ∨
          (pair.edgeTransfer edge = blue ∧
            edgeCrossFaceProfile graphData
              (retainedEdgeToAmbientEdge data cross) edge = red)) ∧
        edge ∉ incidentEdgeFinset G entry ∧
        edge ∉ incidentEdgeFinset G exit ∧
        edge ≠ centralEdge data := by
  rcases pair.exists_zero_off_repaired_cross minimal C hC hsame
      first second entry exit hentry hexit hcentral with
    ⟨edge, hzero, hentryOff, hexitOff, hcentralOff⟩
  have hcrossOff : edge ≠ retainedEdgeToAmbientEdge data cross := by
    intro heq
    subst edge
    exact hentryOff hsourceIncident
  have hdifference :=
    pair.crossFaceDifferenceProfile_ne_zero_of_repaired_zero
      minimal C hC first second edge hcentralOff hzero
  exact ⟨edge, hzero, hdifference,
    pair.crossFaceProfile_six_disagreement_cases minimal edge
      hcrossOff hcentralOff hdifference,
    hentryOff, hexitOff, hcentralOff⟩

/-- In the actual rejected `bc` state, a residual zero is a strict
disagreement between the exact closure profile and the cross-side face
profile, away from both cross endpoints and the central edge. -/
theorem EvenKempeFusionLens.bcCrossExactPair_exists_strict_profile_disagreement
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C b c edge = 0 ∧
        pair.edgeTransfer edge ≠
          edgeCrossFaceProfile graphData
            (retainedEdgeToAmbientEdge data site.1) edge ∧
        edge ∉ incidentEdgeFinset G
          (lens01.bRoute.firstCrossEntryVertex lens23.cRoute
            hab hbc site).1 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.bRoute.firstCrossExitDart lens23.cRoute
            hab hbc site).fst.1 ∧
        edge ≠ centralEdge data := by
  let entry := lens01.bRoute.firstCrossEntryVertex
    lens23.cRoute hab hbc site
  let exit := (lens01.bRoute.firstCrossExitDart
    lens23.cRoute hab hbc site).fst
  have hrepair := EvenKempeFusionLens.bcCrossExactPair_crossFacePair_repaired
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  have hentryRetained : entry ∈ (site.1.1 : Sym2 _) := by
    simpa only [entry] using
      lens01.bRoute.firstCrossEntryVertex_mem_site
        lens23.cRoute hab hbc site
  have hentryAmbient : entry.1 ∈
      ((retainedEdgeToAmbientEdge data site.1).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨entry, hentryRetained, rfl⟩
  have hsourceIncident : retainedEdgeToAmbientEdge data site.1 ∈
      incidentEdgeFinset G entry.1 := by
    simpa [incidentEdgeFinset] using hentryAmbient
  rcases pair.exists_six_profile_disagreement_off_repaired_cross
      minimal C hC hsame b c entry.1 exit.1 hsourceIncident
        hrepair.1 hrepair.2.1 hrepair.2.2 with
    ⟨edge, hzero, hdifference, _hcases,
      hentryOff, hexitOff, hcentralOff⟩
  have hprofiles : pair.edgeTransfer edge ≠
      edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data site.1) edge := by
    intro heq
    apply hdifference
    rw [CrossCentralExactFaceCutPair.crossFaceDifferenceProfile, heq,
      color_add_self]
  exact ⟨edge, hzero, hprofiles, hentryOff, hexitOff, hcentralOff⟩

/-- The symmetric rejected `cb` state has the same strict off-cross
profile disagreement. -/
theorem EvenKempeFusionLens.cbCrossExactPair_exists_strict_profile_disagreement
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C c b edge = 0 ∧
        pair.edgeTransfer edge ≠
          edgeCrossFaceProfile graphData
            (retainedEdgeToAmbientEdge data site.1) edge ∧
        edge ∉ incidentEdgeFinset G
          (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
            hac hbc.symm site).1 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.cRoute.firstCrossExitDart lens23.bRoute
            hac hbc.symm site).fst.1 ∧
        edge ≠ centralEdge data := by
  let entry := lens01.cRoute.firstCrossEntryVertex
    lens23.bRoute hac hbc.symm site
  let exit := (lens01.cRoute.firstCrossExitDart
    lens23.bRoute hac hbc.symm site).fst
  have hrepair := EvenKempeFusionLens.cbCrossExactPair_crossFacePair_repaired
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  have hentryRetained : entry ∈ (site.1.1 : Sym2 _) := by
    simpa only [entry] using
      lens01.cRoute.firstCrossEntryVertex_mem_site
        lens23.bRoute hac hbc.symm site
  have hentryAmbient : entry.1 ∈
      ((retainedEdgeToAmbientEdge data site.1).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨entry, hentryRetained, rfl⟩
  have hsourceIncident : retainedEdgeToAmbientEdge data site.1 ∈
      incidentEdgeFinset G entry.1 := by
    simpa [incidentEdgeFinset] using hentryAmbient
  rcases pair.exists_six_profile_disagreement_off_repaired_cross
      minimal C hC hsame c b entry.1 exit.1 hsourceIncident
        hrepair.1 hrepair.2.1 hrepair.2.2 with
    ⟨edge, hzero, hdifference, _hcases,
      hentryOff, hexitOff, hcentralOff⟩
  have hprofiles : pair.edgeTransfer edge ≠
      edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data site.1) edge := by
    intro heq
    apply hdifference
    rw [CrossCentralExactFaceCutPair.crossFaceDifferenceProfile, heq,
      color_add_self]
  exact ⟨edge, hzero, hprofiles, hentryOff, hexitOff, hcentralOff⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
