import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitBacktrackProfile

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCutPair

/-- The two binary global complements relating exact-cut pairs with the
same retained prefix and suffix paths. -/
def labelComplementProfile
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {sourceCross targetCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (source : CrossCentralExactFaceCutPair graphData data sourceCross)
    (target : CrossCentralExactFaceCutPair graphData data targetCross)
    (hprefixTrail : source.prefixTrail = target.prefixTrail)
    (hsuffixTrail : source.suffixTrail = target.suffixTrail) : F2 × F2 :=
  Classical.choose
    (source.existsUnique_labelComplementProfile_of_trails_eq minimal target
      hprefixTrail hsuffixTrail).exists

/-- The extracted complement profile realizes its two endpoint label
equations. -/
theorem labelComplementProfile_spec
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {sourceCross targetCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (source : CrossCentralExactFaceCutPair graphData data sourceCross)
    (target : CrossCentralExactFaceCutPair graphData data targetCross)
    (hprefixTrail : source.prefixTrail = target.prefixTrail)
    (hsuffixTrail : source.suffixTrail = target.suffixTrail) :
    (∀ face, target.prefixLabels face = source.prefixLabels face +
      (labelComplementProfile minimal source target hprefixTrail
        hsuffixTrail).1) ∧
    (∀ face, target.suffixLabels face = source.suffixLabels face +
      (labelComplementProfile minimal source target hprefixTrail
        hsuffixTrail).2) := by
  exact Classical.choose_spec
    (source.existsUnique_labelComplementProfile_of_trails_eq minimal target
      hprefixTrail hsuffixTrail).exists

/-- Any pair of shifts satisfying the endpoint equations is the extracted
complement profile. -/
theorem labelComplementProfile_eq_of_spec
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {sourceCross targetCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (source : CrossCentralExactFaceCutPair graphData data sourceCross)
    (target : CrossCentralExactFaceCutPair graphData data targetCross)
    (hprefixTrail : source.prefixTrail = target.prefixTrail)
    (hsuffixTrail : source.suffixTrail = target.suffixTrail)
    (profile : F2 × F2)
    (hspec :
      (∀ face, target.prefixLabels face =
        source.prefixLabels face + profile.1) ∧
      (∀ face, target.suffixLabels face =
        source.suffixLabels face + profile.2)) :
    labelComplementProfile minimal source target hprefixTrail hsuffixTrail =
      profile := by
  let anchor := dartOrbitFace graphData.toRotationSystem
    graphData.toRotationSystem.outer
  have hactual := labelComplementProfile_spec minimal source target
    hprefixTrail hsuffixTrail
  apply Prod.ext
  · exact add_left_cancel
      ((hactual.1 anchor).symm.trans (hspec.1 anchor))
  · exact add_left_cancel
      ((hactual.2 anchor).symm.trans (hspec.2 anchor))

/-- A pair compared with itself has the neutral complement profile. -/
theorem labelComplementProfile_self
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    labelComplementProfile minimal pair pair rfl rfl = 0 := by
  apply labelComplementProfile_eq_of_spec minimal pair pair rfl rfl 0
  constructor <;> intro face <;> simp

/-- Complement profiles compose by componentwise binary addition. This is
the transfer-monoid law for three exact-cut pairs sharing both retained
paths. -/
theorem labelComplementProfile_trans
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {firstCross secondCross thirdCross :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet}
    (first : CrossCentralExactFaceCutPair graphData data firstCross)
    (second : CrossCentralExactFaceCutPair graphData data secondCross)
    (third : CrossCentralExactFaceCutPair graphData data thirdCross)
    (hprefixFirstSecond : first.prefixTrail = second.prefixTrail)
    (hsuffixFirstSecond : first.suffixTrail = second.suffixTrail)
    (hprefixSecondThird : second.prefixTrail = third.prefixTrail)
    (hsuffixSecondThird : second.suffixTrail = third.suffixTrail) :
    labelComplementProfile minimal first third
        (hprefixFirstSecond.trans hprefixSecondThird)
        (hsuffixFirstSecond.trans hsuffixSecondThird) =
      labelComplementProfile minimal first second hprefixFirstSecond
          hsuffixFirstSecond +
        labelComplementProfile minimal second third hprefixSecondThird
          hsuffixSecondThird := by
  let firstProfile := labelComplementProfile minimal first second
    hprefixFirstSecond hsuffixFirstSecond
  let secondProfile := labelComplementProfile minimal second third
    hprefixSecondThird hsuffixSecondThird
  apply labelComplementProfile_eq_of_spec minimal first third
    (hprefixFirstSecond.trans hprefixSecondThird)
    (hsuffixFirstSecond.trans hsuffixSecondThird)
    (firstProfile + secondProfile)
  have hfirst := labelComplementProfile_spec minimal first second
    hprefixFirstSecond hsuffixFirstSecond
  have hsecond := labelComplementProfile_spec minimal second third
    hprefixSecondThird hsuffixSecondThird
  constructor
  · intro face
    rw [hsecond.1 face, hfirst.1 face]
    simp only [Prod.fst_add]
    rw [add_assoc]
  · intro face
    rw [hsecond.2 face, hfirst.2 face]
    simp only [Prod.snd_add]
    rw [add_assoc]

/-- Every complement transfer is its own additive inverse. -/
theorem labelComplementProfile_add_self
    (profile : F2 × F2) : profile + profile = 0 := by
  apply Prod.ext <;> exact zmod2_add_self _

/-- Reversing the two endpoints preserves their binary complement profile. -/
theorem labelComplementProfile_symm
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {sourceCross targetCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (source : CrossCentralExactFaceCutPair graphData data sourceCross)
    (target : CrossCentralExactFaceCutPair graphData data targetCross)
    (hprefixTrail : source.prefixTrail = target.prefixTrail)
    (hsuffixTrail : source.suffixTrail = target.suffixTrail) :
    labelComplementProfile minimal target source hprefixTrail.symm
        hsuffixTrail.symm =
      labelComplementProfile minimal source target hprefixTrail
        hsuffixTrail := by
  let profile := labelComplementProfile minimal source target
    hprefixTrail hsuffixTrail
  apply labelComplementProfile_eq_of_spec minimal target source
    hprefixTrail.symm hsuffixTrail.symm profile
  have hforward := labelComplementProfile_spec minimal source target
    hprefixTrail hsuffixTrail
  constructor
  · intro face
    calc
      source.prefixLabels face =
          source.prefixLabels face + (profile.1 + profile.1) := by
            rw [zmod2_add_self]
            simp
      _ = (source.prefixLabels face + profile.1) + profile.1 := by
            rw [add_assoc]
      _ = target.prefixLabels face + profile.1 := by
            rw [← hforward.1 face]
  · intro face
    calc
      source.suffixLabels face =
          source.suffixLabels face + (profile.2 + profile.2) := by
            rw [zmod2_add_self]
            simp
      _ = (source.suffixLabels face + profile.2) + profile.2 := by
            rw [add_assoc]
      _ = target.suffixLabels face + profile.2 := by
            rw [← hforward.2 face]

/-- The complement transfer monoid has exactly four elements. -/
theorem card_labelComplementProfile :
    Fintype.card (F2 × F2) = 4 := by
  change Fintype.card (ZMod 2 × ZMod 2) = 4
  rw [Fintype.card_prod, ZMod.card]

/-- Any five cumulative complement states contain a repetition. -/
theorem exists_repeated_labelComplementProfile_of_five
    (profiles : Fin 5 → F2 × F2) :
    ∃ first second, first ≠ second ∧
      profiles first = profiles second := by
  apply Fintype.exists_ne_map_eq_of_card_lt profiles
  rw [card_labelComplementProfile, Fintype.card_fin]
  omega

end CrossCentralExactFaceCutPair

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
