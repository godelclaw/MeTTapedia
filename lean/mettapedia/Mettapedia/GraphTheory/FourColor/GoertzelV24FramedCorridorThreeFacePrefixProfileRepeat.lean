import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPortIncidencePrefixProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixThreeFaceBound

/-!
# Source-prefix repetition over the proved three-face carrier

The generic width-two profile permits four boundary face fragments.  A literal
source Cell cross-section is sharper: its two crossings run through a simple
three-face dual path, and the cumulative-prefix geometry proves that at most
three boundary fragments occur.  This file transports the existing lossless
port-incidence encoding to that smaller, source-realized carrier.

The resulting `L7` repeat demand is an explicit improvement of the finite
carrier.  It is still not a reachable-closure certificate, a numerical `V0`,
or a verification of the bounded base.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedTrail
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding.SourceConsecutiveSlabInterface
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraphDartRotation

/-- Repackage a bounded profile in a smaller face-fragment carrier once its
actual dependent count has been proved to fit. -/
def narrowFaceFragmentBound
    {crossingEdgeCount terminalCount oldBound newBound : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      oldBound)
    (hbound : profile.faceFragmentCount.val ≤ newBound) :
    BoundedCorridorCutProfile crossingEdgeCount terminalCount newBound where
  faceFragmentCount :=
    ⟨profile.faceFragmentCount.val, Nat.lt_succ_of_le hbound⟩
  profile := profile.profile

/-- Narrowing only changes the proof-carrying outer bound.  Equality after
narrowing therefore reflects equality of the complete original profiles. -/
theorem narrowFaceFragmentBound_injective
    {crossingEdgeCount terminalCount oldBound newBound : Nat}
    {left right : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      oldBound}
    (hleft : left.faceFragmentCount.val ≤ newBound)
    (hright : right.faceFragmentCount.val ≤ newBound)
    (heq : narrowFaceFragmentBound left hleft =
      narrowFaceFragmentBound right hright) :
    left = right := by
  cases left with
  | mk leftCount leftProfile =>
    cases right with
    | mk rightCount rightProfile =>
      rw [BoundedCorridorCutProfile.mk.injEq] at heq ⊢
      rcases heq with ⟨hcount, hprofile⟩
      simp only [narrowFaceFragmentBound] at hcount hprofile
      have hval : leftCount.val = rightCount.val :=
        congrArg (fun count : Fin (newBound + 1) => count.val) hcount
      have hcount' : leftCount = rightCount := Fin.ext hval
      exact ⟨hcount', hprofile⟩

/-- Exact lossless carrier size after the source-specific three-fragment
bound and the already-proved port-incidence laws. -/
theorem boundedWidthTwoPortIncidenceProfileCount_three :
    boundedWidthTwoPortIncidenceProfileCount 3 = 191184 := by
  norm_num [boundedWidthTwoPortIncidenceProfileCount,
    widthTwoPortIncidenceProfileCount, Fin.sum_univ_succ,
    card_faceEquivalenceCode_zero, card_faceEquivalenceCode_one,
    card_faceEquivalenceCode_two, card_faceEquivalenceCode_three,
    card_widthTwoPortIncidenceCode_zero,
    card_widthTwoPortIncidenceCode_one,
    card_widthTwoPortIncidenceCode_two,
    card_widthTwoPortIncidenceCode_three]

/-- Four residue classes buy the already-required gap of at least four. -/
theorem separated_boundedWidthTwoPortIncidenceProfileCount_three :
    4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1 = 764737 := by
  rw [boundedWidthTwoPortIncidenceProfileCount_three]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorThreeFacePrefixEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- `L7`: literal cumulative source-prefix profiles repeat at gap at least
four after restricting the face-count coordinate to the proved `0`--`3`
fibers.  The conclusion remains equality of the complete original splice
profiles, not merely equality of their compressed codes. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_threeFace_separated
    {source : GoertzelV24FramedTrail.SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : 4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1 ≤
      blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1),
      first.val + 3 < second.val ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hbound : ∀ offset, (profiles offset).faceFragmentCount.val ≤ 3 := by
    intro offset
    exact localLayerLeftPrefixBoundedProfile_faceFragmentCount_le_three
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge offset)) coloring (fun step => hcoloring _)
  let narrowed : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1) →
      BoundedCorridorCutProfile 2 0 3 := fun offset =>
    narrowFaceFragmentBound (profiles offset) (hbound offset)
  have hsemantic : ∀ offset,
      BoundedIsPortIncidenceSemantic (narrowed offset) := by
    intro offset
    exact localLayerLeftPrefixBoundedProfile_isPortIncidenceSemantic
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge offset)) coloring (fun step => hcoloring _)
  rcases exists_separated_profile_eq_of_portIncidenceSemantic narrowed
      hsemantic with ⟨first, second, hfar, heq⟩
  exact ⟨first, second, hfar,
    narrowFaceFragmentBound_injective (hbound first) (hbound second) heq⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat

end Mettapedia.GraphTheory.FourColor
