import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFaceInputResidue

/-!
# A finite residual code for the serial face update

The literal serial prefix is not assumed to have only its displayed input
edges on the true frontier.  Consequently an outgoing face may contain an
old-prefix residue which is not itself an input boundary fragment.  This file
keeps that possibility explicit while removing the redundant `oldCap` field
from the finite receipt.

The selected input contribution is computed from the input profile and the
occurrence-sensitive `usesInput` matrix.  One additional cap-at-five residue
coordinate then reconstructs the complete old-prefix contribution exactly.
Together with the already finite local and overlap caps, this gives a
graph-free decoder for the outgoing face-length coordinate.

This is a finite support interface, not a proof that every abstract code is
geometrically realizable, a reachable-closure computation, or a numerical
threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open SimpleGraphDartRotation

/-- The facial part of a serial letter after the old-prefix contribution is
factored into visible input fragments and one capped residue. -/
structure BoundedSerialFaceResidualCode (faceFragmentBound : Nat) where
  inputCount : Fin (faceFragmentBound + 1)
  outputCount : Fin (faceFragmentBound + 1)
  usesInput : Fin outputCount.val → Fin inputCount.val → Bool
  residueCap : Fin outputCount.val → Fin 6
  localCap : Fin outputCount.val → Fin 6
  overlapCap : Fin outputCount.val → Fin 6

noncomputable instance (faceFragmentBound : Nat) :
    DecidableEq (BoundedSerialFaceResidualCode faceFragmentBound) :=
  Classical.decEq _

private def boundedSerialFaceResidualCodeEquiv (faceFragmentBound : Nat) :
    BoundedSerialFaceResidualCode faceFragmentBound ≃
      Σ inputCount : Fin (faceFragmentBound + 1),
        Σ outputCount : Fin (faceFragmentBound + 1),
          (Fin outputCount.val → Fin inputCount.val → Bool) ×
          (Fin outputCount.val → Fin 6) ×
          (Fin outputCount.val → Fin 6) ×
          (Fin outputCount.val → Fin 6) where
  toFun code := ⟨code.inputCount, code.outputCount, code.usesInput,
    code.residueCap, code.localCap, code.overlapCap⟩
  invFun code :=
    { inputCount := code.1
      outputCount := code.2.1
      usesInput := code.2.2.1
      residueCap := code.2.2.2.1
      localCap := code.2.2.2.2.1
      overlapCap := code.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (faceFragmentBound : Nat) :
    Fintype (BoundedSerialFaceResidualCode faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedSerialFaceResidualCodeEquiv faceFragmentBound).symm

/-- The visible old-prefix cap selected by one output coordinate. -/
def BoundedSerialFaceResidualCode.selectedInputCap
    {faceFragmentBound : Nat}
    (code : BoundedSerialFaceResidualCode faceFragmentBound)
    (inputCap : Fin code.inputCount.val → Fin 6)
    (output : Fin code.outputCount.val) : Nat :=
  min (∑ input, if code.usesInput output input then (inputCap input).val else 0) 5

/-- Reconstruct the complete old-prefix cap from visible input fragments and
the one explicit residue coordinate. -/
def BoundedSerialFaceResidualCode.oldCap
    {faceFragmentBound : Nat}
    (code : BoundedSerialFaceResidualCode faceFragmentBound)
    (inputCap : Fin code.inputCount.val → Fin 6)
    (output : Fin code.outputCount.val) : Nat :=
  min (code.selectedInputCap inputCap output + (code.residueCap output).val) 5

/-- Decode the outgoing face-length cap of the serial letter. -/
def BoundedSerialFaceResidualCode.outputCap
    {faceFragmentBound : Nat}
    (code : BoundedSerialFaceResidualCode faceFragmentBound)
    (inputCap : Fin code.inputCount.val → Fin 6)
    (output : Fin code.outputCount.val) : Nat :=
  min (code.oldCap inputCap output + (code.localCap output).val -
    (code.overlapCap output).val) 5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFaceResidualCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Boolean form of the occurrence-sensitive input-use predicate. -/
noncomputable def sourceCorridorSerialInputFaceUsedByOutputBoolAt
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
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (input : SerialCutFragmentIndex
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) : Bool := by
  classical
  exact decide (sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
    hrotation htwoSided hunique offset output input)

@[simp]
theorem sourceCorridorSerialInputFaceUsedByOutputBoolAt_eq_true_iff
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
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (input : SerialCutFragmentIndex
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
        hrotation htwoSided hunique offset output input = true ↔
      sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic hrotation
        htwoSided hunique offset output input := by
  simp [sourceCorridorSerialInputFaceUsedByOutputBoolAt]

/-- The input profile's capped face coordinate, with the dependent source
cut hidden behind a stable finite function. -/
noncomputable def sourceCorridorSerialInputFaceCapAt
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    SerialCutFragmentIndex
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset) → Fin 6 :=
  (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
    htwoSided hunique offset color hcolor).profile.faceLengthCap

/-- Two distinct selected input coordinates for one output have disjoint
regional supports.  The same-face test in `usesInput` is load-bearing here:
the two facial sides of one underlying edge must not be conflated. -/
theorem sourceCorridorSerialInputFragmentEdges_disjoint_of_used_ne
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
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (left right : SerialCutFragmentIndex
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (hleft : sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
      hrotation htwoSided hunique offset output left)
    (hright : sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
      hrotation htwoSided hunique offset output right)
    (hne : left ≠ right) :
    Disjoint
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges left)
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges right) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).localLayerPrefixCrossing)
  let region := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique offset
  let leftFragment := boundaryRegionalFragmentAt RS cut region left
  let rightFragment := boundaryRegionalFragmentAt RS cut region right
  have hface : leftFragment.1.1 = rightFragment.1.1 :=
    hleft.1.trans hright.1.symm
  have hfragmentNe : leftFragment ≠ rightFragment := by
    intro heq
    exact hne (boundaryRegionalFragmentAt_injective RS cut region heq)
  have hrawDisjoint : Disjoint
      (boundaryRegionalFragmentEdges RS cut region leftFragment)
      (boundaryRegionalFragmentEdges RS cut region rightFragment) := by
    rcases leftFragment with ⟨leftFace, ⟨leftComponent, leftTouches⟩⟩
    rcases rightFragment with ⟨rightFace, ⟨rightComponent, rightTouches⟩⟩
    dsimp only at hface
    have hfaceSubtype : leftFace = rightFace := Subtype.ext hface
    subst rightFace
    have hcomponent : leftComponent ≠ rightComponent := by
      intro heq
      apply hfragmentNe
      subst rightComponent
      rfl
    exact disjoint_faceRegionalFragmentEdges_of_ne RS htwoSided
      (orbitFaceRoot RS leftFace.1) region hcomponent
  rw [(sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
        (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS region
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing)),
    (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
        (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS region
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing))]
  change Disjoint
    (boundaryRegionalFragmentEdges RS cut region leftFragment)
    (boundaryRegionalFragmentEdges RS cut region rightFragment)
  exact hrawDisjoint

set_option maxHeartbeats 800000

/-- The selected-union cap is computed solely from the input profile's
face-length coordinates and the finite occurrence-sensitive incidence matrix. -/
theorem sourceCorridorSerialSelectedInputFaceUnionAt_cap_eq_profile_sum
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0)
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    min (sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic
          hrotation htwoSided hunique offset output).card 5 =
      min (∑ input,
        if sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
            hrotation htwoSided hunique offset output input then
          (sourceCorridorSerialInputFaceCapAt realization hcubic hrotation
            htwoSided hunique offset color hcolor input).val
        else 0) 5 := by
  classical
  let inputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let selected : Finset (SerialCutFragmentIndex inputData) :=
    Finset.univ.filter fun input =>
      sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
        hrotation htwoSided hunique offset output input
  let selectedProp : Finset (SerialCutFragmentIndex inputData) :=
    Finset.univ.filter fun input =>
      sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
        hrotation htwoSided hunique offset output input
  have hselected : selectedProp = selected := by
    ext input
    simp only [selectedProp, selected, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (sourceCorridorSerialInputFaceUsedByOutputBoolAt_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset output input).symm
  have hselectedUnion :
      sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic
          hrotation htwoSided hunique offset output =
        selected.biUnion inputData.regionalFragmentEdges := by
    change selectedProp.biUnion inputData.regionalFragmentEdges = _
    rw [hselected]
  have hcardUnion :
      (selected.biUnion inputData.regionalFragmentEdges).card =
        ∑ input ∈ selected, (inputData.regionalFragmentEdges input).card := by
    apply Finset.card_biUnion
    intro left hleft right hright hne
    have hleftUsed :=
      (sourceCorridorSerialInputFaceUsedByOutputBoolAt_eq_true_iff realization
        hcubic hrotation htwoSided hunique offset output left).1
          (Finset.mem_filter.1 hleft).2
    have hrightUsed :=
      (sourceCorridorSerialInputFaceUsedByOutputBoolAt_eq_true_iff realization
        hcubic hrotation htwoSided hunique offset output right).1
          (Finset.mem_filter.1 hright).2
    exact sourceCorridorSerialInputFragmentEdges_disjoint_of_used_ne
      realization hcubic hrotation htwoSided hunique offset output left right
      hleftUsed hrightUsed hne
  rw [hselectedUnion]
  rw [hcardUnion]
  rw [GoertzelV24TerminalProfileFaceSliceFragments.min_sum_eq_min_sum_min_five]
  simp only [selected, Finset.sum_filter]
  apply congrArg (fun value => min value 5)
  apply Finset.sum_congr rfl
  intro input _hinput
  by_cases hused :
      sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
        hrotation htwoSided hunique offset output input = true
  · have hcap :
        (sourceCorridorSerialInputFaceCapAt realization hcubic hrotation
          htwoSided hunique offset color hcolor input).val =
          min (inputData.regionalFragmentEdges input).card 5 := by
      simpa only [sourceCorridorSerialInputFaceCapAt,
        sourceCorridorSerialInputBoundedProfileAt,
        sourceCorridorSerialInputCutDataAt,
        regionalBoundaryBoundedProfile, inputData] using
          ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionalProfile_faceLengthCap_val color
              hcolor input)
    simp only [hused, if_true]
    omega
  · have hfalse :
        sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
          hrotation htwoSided hunique offset output input = false :=
      Bool.eq_false_of_not_eq_true hused
    simp [hfalse]

/-- The actual outgoing face cap is decoded from the old finite profile, the
visible input-incidence matrix, one residue cap, and the local/overlap caps.
No uncapped old-prefix cardinality remains in the formula. -/
theorem sourceCorridorSerialPrefix_faceLengthCap_eq_profile_residual
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
    (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0)
    (houtputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    (((sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color houtputColor).profile.faceLengthCap
      output).val) =
      min
        (min
            (min (∑ input,
                if sourceCorridorSerialInputFaceUsedByOutputBoolAt realization
                    hcubic hrotation htwoSided hunique offset output input then
                  (sourceCorridorSerialInputFaceCapAt realization hcubic
                    hrotation htwoSided hunique offset color hinputColor
                    input).val
                else 0) 5 +
              (sourceCorridorSerialOldFaceInputResidueCapAt realization hcubic
                hrotation htwoSided hunique offset output).val)
            5 +
          min (sourceCorridorSerialLocalFaceSliceAt realization hcubic
            hrotation htwoSided hunique offset output).card 5 -
          min ((sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
              htwoSided hunique offset output) ∩
            sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
              htwoSided hunique offset output).card 5)
        5 := by
  rw [sourceCorridorSerialPrefix_faceLengthCap_eq_factorSlices realization
    hcubic hrotation htwoSided hunique offset color houtputColor output]
  rw [sourceCorridorSerialOldFaceSliceAt_cap_eq_selected_add_residue
    realization hcubic hrotation htwoSided hunique offset output]
  rw [sourceCorridorSerialSelectedInputFaceUnionAt_cap_eq_profile_sum
    realization hcubic hrotation htwoSided hunique offset color hinputColor
    output]
  rfl

set_option maxHeartbeats 200000

/-- The source-extracted residual code.  Unlike the older receipt it stores
only the cap not already reconstructible from the input profile. -/
noncomputable def sourceCorridorSerialFaceResidualCodeAt
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
    (offset : Fin (blockLength - 3)) :
    BoundedSerialFaceResidualCode 4 := by
  let receipt := sourceCorridorSerialFaceFactorReceiptAt realization hcubic
    hrotation htwoSided hunique offset
  exact
    { inputCount := receipt.inputCount
      outputCount := receipt.outputCount
      usesInput := receipt.usesInput
      residueCap := fun output =>
        sourceCorridorSerialOldFaceInputResidueCapAt realization hcubic
          hrotation htwoSided hunique offset output
      localCap := receipt.localCap
      overlapCap := receipt.overlapCap }

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
