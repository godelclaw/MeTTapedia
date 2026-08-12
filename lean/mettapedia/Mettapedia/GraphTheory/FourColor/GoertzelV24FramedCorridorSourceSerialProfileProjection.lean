import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceSerialTangleChain

/-!
# Projecting the source full-profile word to literal Cell color support

The source's one-Cell relation is indexed by the complete finite profile:
cut colors, tracked connectivity, face continuation, fragment incidence, and
capped face progress.  The literal heterogeneous tangle chain is indexed only
by boundary color words.  This file proves the safe direction between them.

Every realized full local-profile transition projects to a coloring accepted
by the corresponding literal Cell.  Consequently every exact path through the
source-ordered bounded local-profile word projects to an exact color-support
path and therefore colors the literal serial composite.  No converse is asserted:
color projection can merge distinct connectivity and face states.  Nor is the
tagged composite carrier identified with an ambient corridor region here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorTransferWord
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSourceSerialProfileProjectionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

private theorem forall₂_ofFn
    {α β : Type*} {relation : α → β → Prop} {n : Nat}
    (left : Fin n → α) (right : Fin n → β)
    (hpointwise : ∀ offset, relation (left offset) (right offset)) :
    List.Forall₂ relation (List.ofFn left) (List.ofFn right) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (hpointwise 0)
        (ih (fun offset => left offset.succ) (fun offset => right offset.succ)
          (fun offset => hpointwise offset.succ))

private theorem castCorridorCutProfile_edgeColor
    {crossingEdgeCount targetCrossingEdgeCount terminalCount
      faceFragmentCount : Nat}
    (hwidth : crossingEdgeCount = targetCrossingEdgeCount)
    (profile : GoertzelV24CorridorProfile.CorridorCutProfile
      crossingEdgeCount terminalCount faceFragmentCount)
    (step : Fin crossingEdgeCount) :
    ((cast
        (congrArg (fun width =>
          GoertzelV24CorridorProfile.CorridorCutProfile
            width terminalCount faceFragmentCount) hwidth)
        profile).edgeColor (finCongr hwidth step)) =
      profile.edgeColor step := by
  cases hwidth
  rfl

/-- The boundary-color coordinate of the common bounded local Cell profile. -/
def localLayerPairCellBoundedProfileColorWord
    (profile :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile) :
    Fin 2 → Color :=
  fun step => (profile.profile.edgeColor step).toColor

/-- One complete source Cell transition projects to the literal boundary-word
support of that same Cell.  Connectivity and face data are retained in the
premise and only forgotten after the concrete serial coloring is obtained. -/
theorem sourceSlabCellBoundedSerialProfileTransferAt_projects_to_tangleSupport
    {source : SourceTrail G}
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
    (offset : Fin (blockLength - 3))
    (left right :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile)
    (htransfer : sourceSlabCellBoundedSerialProfileTransferAt realization
      hcubic hrotation htwoSided hunique offset left right) :
    (sourceSlabCoordinatizedComplementTangleAt realization hcubic hrotation
        htwoSided hunique offset).AcceptsBoundaryWords
      (localLayerPairCellBoundedProfileColorWord left)
      (localLayerPairCellBoundedProfileColorWord right) := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  rcases htransfer with
    ⟨leftRaw, rightRaw, hleft, hright, hserial⟩
  have hpositive :
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCount
        embedded.cellulation.rotation boundary hcubic leftRaw rightRaw :=
    (pair.sourceCrosscutComplementSerialRealizesProfiles_iff
      embedded.cellulation.rotation boundary hcubic leftRaw rightRaw).1 hserial
  unfold CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
  change
    (pair.sourceCrosscutComplementTwoSidedOpenTangle
      embedded.cellulation.rotation boundary hcubic).AcceptsBoundaryWords
        _ _
  apply (pair.sourceCrosscutComplementTwoSidedOpenTangle_acceptsBoundaryWords_iff_exists_profilePair
    embedded.cellulation.rotation boundary hcubic _ _).2
  refine ⟨leftRaw, rightRaw, ?_, ?_, hpositive⟩
  · subst left
    funext step
    have hwidth : pair.left.walk.length = 2 := by
      simpa [pair, SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface] using interface.localLayer_walk_length_eq_two
    have hcast := castCorridorCutProfile_edgeColor hwidth leftRaw step
    change (leftRaw.edgeColor step).toColor =
      (((interface.localLayerPairCellProfileCode hcubic leftRaw).profile
        |>.edgeColor (finCongr hwidth step))).toColor
    simpa [SourceConsecutiveSlabInterface.localLayerPairCellProfileCode,
      interface, pair] using congrArg (fun color => color.toColor) hcast.symm
  · subst right
    funext step
    have hleftWidth : pair.left.walk.length = 2 := by
      simpa [pair, SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface] using interface.localLayer_walk_length_eq_two
    have hrightWidth : pair.right.walk.length = 2 := by
      simpa [pair, SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface] using interface.nextLocalLayer_walk_length_eq_two
    let leftStep : Fin pair.left.walk.length := Fin.cast pair.length_eq.symm step
    have hindex : finCongr hleftWidth leftStep = finCongr hrightWidth step := by
      apply Fin.ext
      rfl
    have hcast := castCorridorCutProfile_edgeColor hleftWidth rightRaw leftStep
    have hcast' :
        ((interface.localLayerPairCellProfileCode hcubic rightRaw).profile
            |>.edgeColor (finCongr hrightWidth step)) =
          rightRaw.edgeColor leftStep := by
      rw [← hindex]
      simpa [SourceConsecutiveSlabInterface.localLayerPairCellProfileCode,
        interface, pair] using hcast
    change (rightRaw.edgeColor leftStep).toColor =
      (((interface.localLayerPairCellProfileCode hcubic rightRaw).profile
        |>.edgeColor (finCongr hrightWidth step))).toColor
    exact congrArg (fun color => color.toColor) hcast'.symm

/-- The source-ordered bounded local-profile relation word projects pointwise
to the literal color-support word of the corresponding heterogeneous tangle chain.
The common `Fin` index is the source offset, so no permutation or homogeneous
transfer assumption enters the comparison. -/
theorem sourceCorridorCellSerialTransferWord_projects_to_tangleSupportWord
    {source : SourceTrail G}
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
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))) :
    List.Forall₂
      (fun profileStep colorStep =>
        ∀ left right, profileStep left right →
          colorStep
            (localLayerPairCellBoundedProfileColorWord left)
            (localLayerPairCellBoundedProfileColorWord right))
      (sourceCorridorCellSerialTransferWord realization hcubic hrotation
        htwoSided hunique)
      ((sourceCorridorCoordinatizedComplementTangles realization hcubic
        hrotation htwoSided hunique).map
          CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords) := by
  unfold sourceCorridorCellSerialTransferWord
    sourceCorridorCoordinatizedComplementTangles
  rw [List.map_ofFn]
  apply forall₂_ofFn
  intro offset left right htransfer
  exact sourceSlabCellBoundedSerialProfileTransferAt_projects_to_tangleSupport
    realization hcubic hrotation htwoSided hunique offset left right htransfer

/-- An exact path through the serial presentation of the bounded local-profile
word projects to an exact path through the literal Cell color supports. -/
theorem exactTransferWord_sourceCorridorCellSerialTransferWord_projects
    {source : SourceTrail G}
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
    {left right :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile}
    (hpath : ExactTransferWord
      (sourceCorridorCellSerialTransferWord realization hcubic hrotation
        htwoSided hunique) left right) :
    ExactTransferWord
      ((sourceCorridorCoordinatizedComplementTangles realization hcubic
        hrotation htwoSided hunique).map
          CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords)
      (localLayerPairCellBoundedProfileColorWord left)
      (localLayerPairCellBoundedProfileColorWord right) :=
  CoordinatizedTwoSidedOpenTangle.exactTransferWord_map_of_forall₂
    localLayerPairCellBoundedProfileColorWord
    (sourceCorridorCellSerialTransferWord_projects_to_tangleSupportWord
      realization hcubic hrotation htwoSided hunique) hpath

/-- The originally defined bounded local Cell-support word has the same safe
projection to literal color support.  This uses its proved identification with
the serial presentation, not a new transfer relation. -/
theorem exactTransferWord_sourceCorridorCellTransferWord_projects
    {source : SourceTrail G}
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
    {left right :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile}
    (hpath : ExactTransferWord
      (sourceCorridorCellTransferWord realization hcubic hrotation htwoSided
        hunique) left right) :
    ExactTransferWord
      ((sourceCorridorCoordinatizedComplementTangles realization hcubic
        hrotation htwoSided hunique).map
          CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords)
      (localLayerPairCellBoundedProfileColorWord left)
      (localLayerPairCellBoundedProfileColorWord right) := by
  apply exactTransferWord_sourceCorridorCellSerialTransferWord_projects
    realization hcubic hrotation htwoSided hunique
  rw [← sourceCorridorCellTransferWord_eq_serialTransferWord realization
    hcubic hrotation htwoSided hunique]
  exact hpath

/-- A bounded local-profile path through a positive-length source corridor
colors its assembled literal serial composite at the projected exterior
words.  This is the factorization direction from full local Cell data to
color support; it does not lift an arbitrary projected path back to profiles. -/
theorem sourceCorridorComplementSerialComposite_acceptsBoundaryWords_of_exactLocalProfilePath
    {source : SourceTrail G}
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
    (hcells : 0 < blockLength - 3)
    {left right :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile}
    (hpath : ExactTransferWord
      (sourceCorridorCellTransferWord realization hcubic hrotation htwoSided
        hunique) left right) :
    (sourceCorridorComplementSerialComposite realization hcubic hrotation
      htwoSided hunique hcells).AcceptsBoundaryWords
        (localLayerPairCellBoundedProfileColorWord left)
        (localLayerPairCellBoundedProfileColorWord right) := by
  apply (sourceCorridorComplementSerialComposite_acceptsBoundaryWords_iff
    realization hcubic hrotation htwoSided hunique hcells _ _).2
  exact exactTransferWord_sourceCorridorCellTransferWord_projects realization
    hcubic hrotation htwoSided hunique hpath

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
