import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementSerialSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceTransferWord

/-!
# Serial semantics of the heterogeneous source corridor word

The source corridor transfer word was constructed from the positive support
of each Cell's literal full-profile `Count` matrix.  Here every one of those
relations is identified with an actual two-sided serial open Cell realizing
the same two full profiles.  Pointwise equality then identifies the whole
heterogeneous word `M₁ ⋯ Mₙ` with its serial-open-tangle semantics.

Successive Cells remain distinct relations.  No power of one homogeneous
matrix, color-only profile, catalogue, or covering reduction is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSourceSerialTransferEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The concrete serial-open-tangle semantics of one indexed source Cell,
transported to the common bounded full-profile carrier.  States outside the
faithful raw-profile image have no transitions. -/
noncomputable def sourceSlabCellBoundedSerialProfileTransferAt
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
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile) : Prop :=
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  ∃ leftRaw rightRaw :
      SourceConsecutiveSlabInterface.LocalLayerPairCellProfile interface hcubic,
    interface.localLayerPairCellProfileCode hcubic leftRaw = left ∧
      interface.localLayerPairCellProfileCode hcubic rightRaw = right ∧
        interface.separatedLocalLayerPair.SourceCrosscutComplementSerialRealizesProfiles
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
          leftRaw rightRaw

/-- One indexed source transfer relation is exactly the serial semantics of
that concrete Cell, including colors, connectivity, and capped face progress. -/
theorem sourceSlabCellBoundedProfileTransferAt_eq_serial
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
    sourceSlabCellBoundedProfileTransferAt realization hcubic hrotation
        htwoSided hunique offset =
      sourceSlabCellBoundedSerialProfileTransferAt realization hcubic hrotation
        htwoSided hunique offset := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  apply funext
  intro left
  apply funext
  intro right
  apply propext
  change
    (∃ leftRaw rightRaw :
        SourceConsecutiveSlabInterface.LocalLayerPairCellProfile interface hcubic,
      interface.localLayerPairCellProfileCode hcubic leftRaw = left ∧
        interface.localLayerPairCellProfileCode hcubic rightRaw = right ∧
          interface.localLayerPairCellProfileTransfer hcubic leftRaw rightRaw) ↔
    (∃ leftRaw rightRaw :
        SourceConsecutiveSlabInterface.LocalLayerPairCellProfile interface hcubic,
      interface.localLayerPairCellProfileCode hcubic leftRaw = left ∧
        interface.localLayerPairCellProfileCode hcubic rightRaw = right ∧
          interface.separatedLocalLayerPair.SourceCrosscutComplementSerialRealizesProfiles
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
            leftRaw rightRaw)
  constructor
  · rintro ⟨leftRaw, rightRaw, hleft, hright, htransfer⟩
    refine ⟨leftRaw, rightRaw, hleft, hright, ?_⟩
    apply (interface.separatedLocalLayerPair
      |>.sourceCrosscutComplementSerialRealizesProfiles_iff
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
        leftRaw rightRaw).2
    exact htransfer
  · rintro ⟨leftRaw, rightRaw, hleft, hright, hserial⟩
    refine ⟨leftRaw, rightRaw, hleft, hright, ?_⟩
    exact (interface.separatedLocalLayerPair
      |>.sourceCrosscutComplementSerialRealizesProfiles_iff
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
        leftRaw rightRaw).1 hserial

/-- The source-ordered word of concrete serial Cell relations.  Its entries
are allowed to differ with their source positions. -/
noncomputable def sourceCorridorCellSerialTransferWord
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
    List (SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile →
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile → Prop) :=
  List.ofFn fun offset =>
    sourceSlabCellBoundedSerialProfileTransferAt realization hcubic hrotation
      htwoSided hunique offset

/-- The actual heterogeneous transfer word is the word of concrete serial
source Cells, entry for entry and in source order. -/
theorem sourceCorridorCellTransferWord_eq_serialTransferWord
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
    sourceCorridorCellTransferWord realization hcubic hrotation htwoSided hunique =
      sourceCorridorCellSerialTransferWord realization hcubic hrotation
        htwoSided hunique := by
  unfold sourceCorridorCellTransferWord sourceCorridorCellSerialTransferWord
  apply congrArg List.ofFn
  funext offset
  exact sourceSlabCellBoundedProfileTransferAt_eq_serial realization hcubic
    hrotation htwoSided hunique offset

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
