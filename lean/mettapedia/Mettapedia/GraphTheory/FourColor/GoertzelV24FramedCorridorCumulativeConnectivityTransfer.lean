import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixCombinedCell
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceSerialTransfer

/-!
# Cumulative connectivity transfer through one literal source Cell

The profile matrix of an isolated Cell records connectivity inside that Cell.
The corridor state is different: it records connectivity accumulated by the
composite to the left of the moving cut.  This file keeps those notions apart
and defines the connectivity coordinate of the actual cumulative transfer.

One transition is witnessed by a realizable combined four-port Cell profile.
The incoming cumulative components and the Cell components are then composed
by `SerialProfileConnectivity`.  No equality between adjacent ambient edge
carriers is asserted; source positions are matched through the explicit
left/right embeddings into the combined Cell carrier.

Only cut colors and tracked connectivity are constrained here.  The
occurrence-sensitive face fields must be added by the full transfer relation
before this coordinate may be used as the manuscript profile `Q`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfileSerialConnectivity
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorCumulativeConnectivityTransferEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Connectivity transfer on the exact dependent Cell-profile carrier.
Unlike the isolated Cell matrix, the output is constrained by serial closure
of the incoming state with one realizable combined Cell state. -/
def LocalLayerPairRawCumulativeConnectivityTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (input output : LocalLayerPairCellProfile interface hcubic) : Prop :=
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  ∃ combined : pair.SourceCrosscutComplementCombinedProfile
      embedded.cellulation.rotation boundary,
    pair.SourceCrosscutComplementCombinedProfileRealizable
        embedded.cellulation.rotation boundary hcubic combined ∧
      SerialProfileConnectivity input combined output
        (pair.sourceCrosscutComplementLeftCombinedIndex
          embedded.cellulation.rotation boundary)
        (pair.sourceCrosscutComplementRightCombinedIndex
          embedded.cellulation.rotation boundary)

/-- Every positive isolated-Cell `Count` entry supplies a genuine cumulative
connectivity transition.  This is one-way: cumulative transitions need not
identify their incoming state with the Cell's isolated left restriction. -/
theorem localLayerPairRawCumulativeConnectivityTransfer_of_cellTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (input output : LocalLayerPairCellProfile interface hcubic)
    (htransfer : interface.localLayerPairCellProfileTransfer hcubic
      input output) :
    interface.LocalLayerPairRawCumulativeConnectivityTransfer hcubic
      input output := by
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  rcases (pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_iff_exists_combined_serial
      embedded.cellulation.rotation boundary hcubic input output).1 htransfer with
    ⟨combined, hrealizable, _hleft, _hright, hserial⟩
  exact ⟨combined, hrealizable, hserial⟩

/-- The common bounded-carrier form of the cumulative connectivity
coordinate.  The input and output may have different actual fragment counts;
only their common width-two, bound-eight packaging is fixed. -/
def LocalLayerPairCumulativeConnectivityTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (input output : LocalLayerPairCellBoundedProfile) : Prop :=
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  ∃ combined : interface.LocalLayerPairCellCombinedProfile hcubic,
    pair.SourceCrosscutComplementCombinedProfileRealizable
        embedded.cellulation.rotation boundary hcubic combined ∧
    SerialProfileConnectivity input.profile combined output.profile
      (interface.localLayerPairCellLeftCombinedIndex hcubic)
      (interface.localLayerPairCellRightCombinedIndex hcubic)

noncomputable instance instDecidableRelLocalLayerPairCumulativeConnectivityTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    DecidableRel
      (interface.LocalLayerPairCumulativeConnectivityTransfer hcubic) :=
  fun _ _ => Classical.propDecidable _

/-- Package an explicit combined-state serial law as a bounded cumulative
transition. -/
theorem localLayerPairCumulativeConnectivityTransfer_of_combined
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (input output : LocalLayerPairCellBoundedProfile)
    (combined : interface.LocalLayerPairCellCombinedProfile hcubic)
    (hrealizable : interface.separatedLocalLayerPair
      |>.SourceCrosscutComplementCombinedProfileRealizable
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
        hcubic combined)
    (hserial : SerialProfileConnectivity input.profile combined output.profile
      (interface.localLayerPairCellLeftCombinedIndex hcubic)
      (interface.localLayerPairCellRightCombinedIndex hcubic)) :
    interface.LocalLayerPairCumulativeConnectivityTransfer hcubic
      input output :=
  ⟨combined, hrealizable, hserial⟩

/-- Every positive encoded Cell entry gives the corresponding special case of
the bounded cumulative connectivity relation.  This remains one-way: an
arbitrary cumulative input need not be the Cell's own left restriction. -/
theorem localLayerPairCumulativeConnectivityTransfer_of_cellBoundedTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (input output : LocalLayerPairCellBoundedProfile)
    (htransfer : interface.localLayerPairCellBoundedProfileTransfer hcubic
      input output) :
    interface.LocalLayerPairCumulativeConnectivityTransfer hcubic
      input output := by
  rcases htransfer with
    ⟨inputRaw, outputRaw, rfl, rfl, hraw⟩
  rcases interface.localLayerPairRawCumulativeConnectivityTransfer_of_cellTransfer
      hcubic inputRaw outputRaw hraw with
    ⟨combined, hrealizable, hserial⟩
  refine ⟨combined, hrealizable, ?_⟩
  exact hserial

end SourceConsecutiveSlabInterface

/-- The source-indexed cumulative connectivity coordinate for one literal
Cell.  Successive entries may be different relations. -/
noncomputable def sourceSlabCumulativeConnectivityTransferAt
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
    (offset : Fin (blockLength - 3)) :=
  (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset)
    |>.LocalLayerPairCumulativeConnectivityTransfer hcubic

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
