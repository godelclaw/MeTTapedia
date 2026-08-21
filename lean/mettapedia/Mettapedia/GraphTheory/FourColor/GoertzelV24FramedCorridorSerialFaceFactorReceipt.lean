import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceCapUpdate

/-!
# Finite face-factor receipts for one literal serial source Cell

The route-correct serial prefix may contain arbitrarily many Cells, so the
small geometric-prefix theorem saying that an old factor is a singleton is
not reused here.  Instead this module records the exact finite observations
needed at one literal update:

* which incoming boundary fragments occur inside each outgoing fragment;
* the capped contribution from the old serial prefix;
* the capped contribution from the literal Cell; and
* the capped size of their genuine overlap.

The receipt is graph-free and finite once the width-four face bound is fixed.
The source specialization below is extracted from the actual graph-derived
fragments; it does not assume that the old profile already determines the
receipt.  Proving that determination is the remaining compression theorem,
not a field smuggled into this interface.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

/-- A graph-free finite receipt for the facial part of one serial update.
Counts are exact rather than padded; every function is indexed only by the
real input and output fragment coordinates. -/
structure BoundedSerialFaceFactorReceipt (faceFragmentBound : Nat) where
  inputCount : Fin (faceFragmentBound + 1)
  outputCount : Fin (faceFragmentBound + 1)
  usesInput : Fin outputCount.val → Fin inputCount.val → Bool
  oldCap : Fin outputCount.val → Fin 6
  localCap : Fin outputCount.val → Fin 6
  overlapCap : Fin outputCount.val → Fin 6

noncomputable instance (faceFragmentBound : Nat) :
    DecidableEq (BoundedSerialFaceFactorReceipt faceFragmentBound) :=
  Classical.decEq _

private def boundedSerialFaceFactorReceiptEquiv (faceFragmentBound : Nat) :
    BoundedSerialFaceFactorReceipt faceFragmentBound ≃
      Σ inputCount : Fin (faceFragmentBound + 1),
        Σ outputCount : Fin (faceFragmentBound + 1),
          (Fin outputCount.val → Fin inputCount.val → Bool) ×
          (Fin outputCount.val → Fin 6) ×
          (Fin outputCount.val → Fin 6) ×
          (Fin outputCount.val → Fin 6) where
  toFun receipt := ⟨receipt.inputCount, receipt.outputCount,
    receipt.usesInput, receipt.oldCap, receipt.localCap,
    receipt.overlapCap⟩
  invFun receipt :=
    { inputCount := receipt.1
      outputCount := receipt.2.1
      usesInput := receipt.2.2.1
      oldCap := receipt.2.2.2.1
      localCap := receipt.2.2.2.2.1
      overlapCap := receipt.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (faceFragmentBound : Nat) :
    Fintype (BoundedSerialFaceFactorReceipt faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedSerialFaceFactorReceiptEquiv faceFragmentBound).symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFaceFactorReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The part of an outgoing fragment lying in the old serial region. -/
def sourceCorridorSerialOldFaceSliceAt
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
    (output : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing))
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1))))) :
    Finset G.edgeSet :=
  (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionalFragmentEdges output ∩
    sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset

/-- The part of an outgoing fragment contributed by the literal Cell. -/
def sourceCorridorSerialLocalFaceSliceAt
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
    (output : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing))
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1))))) :
    Finset G.edgeSet :=
  (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionalFragmentEdges output ∩
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset

/-- The literal serial face-factor receipt, extracted from the two actual
graph-derived cuts on either side of one source Cell. -/
noncomputable def sourceCorridorSerialFaceFactorReceiptAt
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
    BoundedSerialFaceFactorReceipt 4 := by
  let inputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let inputFragmentCount := Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing))
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset))
  let outputFragmentCount := Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing))
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique (offset.val + 1)))
  let inputCount : Fin 5 := ⟨inputFragmentCount,
    Nat.lt_succ_of_le (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing))⟩
  let outputCount : Fin 5 := ⟨outputFragmentCount,
    Nat.lt_succ_of_le (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1))
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing))⟩
  refine
    { inputCount := inputCount
      outputCount := outputCount
      usesInput := fun output input => decide
        (inputData.regionalFragmentEdges (Fin.cast (by rfl) input) ⊆
          outputData.regionalFragmentEdges (Fin.cast (by rfl) output))
      oldCap := fun output => ⟨
        min (sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      localCap := fun output => ⟨
        min (sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      overlapCap := fun output => ⟨
        min ((sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset output) ∩
          sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset output).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- The receipt stores the exact input and output fragment counts used by the
two graph-derived five-field profiles. -/
theorem sourceCorridorSerialFaceFactorReceiptAt_counts
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
    let receipt := sourceCorridorSerialFaceFactorReceiptAt realization hcubic
      hrotation htwoSided hunique offset
    receipt.inputCount.val =
        Fintype.card (BoundaryRegionalFragment
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPrefixCrossing))
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset)) ∧
      receipt.outputCount.val =
        Fintype.card (BoundaryRegionalFragment
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).nextLocalLayerPrefixCrossing))
          (sourceCorridorSerialPrefixRegion realization hcubic hrotation
            htwoSided hunique (offset.val + 1))) := by
  exact ⟨rfl, rfl⟩

/-- The old and literal-Cell slices cover the entire outgoing fragment.
This is the finite-set form of the exact serial region equation. -/
theorem sourceCorridorSerialOldFaceSliceAt_union_localFaceSliceAt
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
    (output : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing))
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1))))) :
    sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output ∪
        sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output =
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges output := by
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let oldRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique offset
  let localRegion := sourceSlabLiteralCellRegionAt realization hcubic
    hrotation htwoSided hunique offset
  have hregion : outputData.regionEdges = oldRegion ∪ localRegion := by
    exact sourceCorridorSerialPrefixCutDataAt_regionEdges_eq_input_union_cell
      realization hcubic hrotation htwoSided hunique offset
  ext edge
  simp only [sourceCorridorSerialOldFaceSliceAt,
    sourceCorridorSerialLocalFaceSliceAt, Finset.mem_union,
    Finset.mem_inter]
  constructor
  · rintro (⟨hedge, _⟩ | ⟨hedge, _⟩) <;> exact hedge
  · intro hedge
    have hregionMem : edge ∈ outputData.regionEdges := by
      exact (Finset.mem_inter.1 hedge).2
    rw [hregion] at hregionMem
    rcases Finset.mem_union.1 hregionMem with hold | hlocal
    · exact Or.inl ⟨hedge, hold⟩
    · exact Or.inr ⟨hedge, hlocal⟩

/-- Exact cap-at-five update for a literal serial face fragment.  The only
numerical side condition is that the genuine old/local overlap is below the
source cap.  The finite receipt stores all three quantities appearing here;
showing that its old term is reconstructed from the input profile is the
separate reachable-state compression obligation. -/
theorem sourceCorridorSerialPrefix_faceLengthCap_eq_factorSlices
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
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (output : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing))
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1)))))
    (hoverlap :
      ((sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset output) ∩
        sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output).card < 5) :
    (((sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hcolor).profile.faceLengthCap
      output).val) =
      min
        (min (sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset output).card 5 +
          min (sourceCorridorSerialLocalFaceSliceAt realization hcubic
            hrotation htwoSided hunique offset output).card 5 -
          ((sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
                htwoSided hunique offset output) ∩
            sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
              htwoSided hunique offset output).card)
        5 := by
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  change ((outputData.regionalProfile color hcolor).faceLengthCap output).val = _
  rw [outputData.regionalProfile_faceLengthCap_val color hcolor output]
  rw [← sourceCorridorSerialOldFaceSliceAt_union_localFaceSliceAt
    realization hcubic hrotation htwoSided hunique offset output]
  exact min_card_union_eq_min_caps_sub_inter_of_inter_card_lt _ _ 5 hoverlap

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
