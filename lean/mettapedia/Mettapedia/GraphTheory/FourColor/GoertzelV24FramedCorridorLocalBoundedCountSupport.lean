import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalCountSupport

/-!
# A common finite carrier for literal source Cell profiles

The two interfaces of every realized Cell-3 region have width two, while the
face fragments are computed from the whole four-edge boundary of that region.
Consequently the raw profile type depends on the particular Cell through its
fragment count even though every such count is bounded by eight.

This module embeds those raw profiles into one existing bounded carrier.  It
does not identify the transfer matrices of different Cells.  It only removes
the dependent-carrier obstacle so a later source corridor can be represented
as an honest word of possibly different transfers over one finite state type.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorLocalBoundedCountSupportEdgeSetDecidableEq :
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

/-- The common finite carrier for every literal Cell-3 interface profile.
Width two is exact; eight is the occurrence-sensitive face-fragment bound for
the Cell's four-edge boundary. -/
abbrev LocalLayerPairCellBoundedProfile :=
  BoundedCorridorCutProfile 2 0 8

/-- The complementary Cell region has at most eight boundary-local face
fragments.  The bound is derived from its literal four-edge cut, not supplied
as a profile premise. -/
theorem localLayerPairCell_faceFragmentCount_le_eight
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    interface.separatedLocalLayerPair.sourceCrosscutComplementFaceFragmentCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) ≤ 8 := by
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let inside := (pair.componentSide boundary.component)ᶜ
  calc
    pair.sourceCrosscutComplementFaceFragmentCount
        embedded.cellulation.rotation boundary =
        Fintype.card (BoundaryRegionalFragment
          embedded.cellulation.rotation.toRotationSystem
          (vertexSetCrossingEdges
            embedded.cellulation.rotation.toRotationSystem inside)
          (vertexSetRegionEdges
            embedded.cellulation.rotation.toRotationSystem inside)) := rfl
    _ ≤ 2 * Fintype.card (VertexSetCrossingEdge
          embedded.cellulation.rotation.toRotationSystem inside) :=
      vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
        embedded.cellulation.rotation.toRotationSystem inside
    _ = 8 := by
      have hcard : Fintype.card (VertexSetCrossingEdge
          embedded.cellulation.rotation.toRotationSystem inside) =
          pair.left.walk.length + pair.right.walk.length := by
        simpa [inside] using
          (Fintype.card_congr
            (pair.sourceCrosscutComplementPort
              embedded.cellulation.rotation boundary)).symm
      rw [hcard]
      simp [pair, SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface.localLayer_walk_length_eq_two,
        interface.nextLocalLayer_walk_length_eq_two]

/-- Embed a raw graph-computed Cell profile into the one common finite
carrier.  No coordinate is discarded: the exact fragment count and the full
five-field profile are both retained. -/
noncomputable def localLayerPairCellProfileCode
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (profile : LocalLayerPairCellProfile interface hcubic) :
    LocalLayerPairCellBoundedProfile := by
  refine {
    faceFragmentCount := ⟨_, Nat.lt_succ_of_le
      (interface.localLayerPairCell_faceFragmentCount_le_eight hcubic)⟩
    profile := ?_ }
  have hwidth : interface.separatedLocalLayerPair.left.walk.length = 2 := by
    simpa [SourceConsecutiveSlabInterface.separatedLocalLayerPair] using
      interface.localLayer_walk_length_eq_two
  rw [← hwidth]
  exact profile

/-- The common-carrier encoding is faithful.  It changes only the dependent
packaging and therefore cannot merge two distinct full Cell profiles. -/
theorem localLayerPairCellProfileCode_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    Function.Injective (interface.localLayerPairCellProfileCode hcubic) := by
  intro left right heq
  dsimp only [localLayerPairCellProfileCode] at heq
  injection heq

/-- The transfer relation of one concrete Cell, transported to the common
finite carrier.  States outside the image of this Cell's exact fragment-count
coordinate have no transitions; no synthetic profile realization is added. -/
noncomputable def localLayerPairCellBoundedProfileTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (left right : LocalLayerPairCellBoundedProfile) : Prop :=
  ∃ leftRaw rightRaw : LocalLayerPairCellProfile interface hcubic,
    interface.localLayerPairCellProfileCode hcubic leftRaw = left ∧
      interface.localLayerPairCellProfileCode hcubic rightRaw = right ∧
        interface.localLayerPairCellProfileTransfer hcubic leftRaw rightRaw

/-- The transported relation remains a finite decidable relation. -/
noncomputable instance instDecidableRelLocalLayerPairCellBoundedProfileTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    DecidableRel (interface.localLayerPairCellBoundedProfileTransfer hcubic) := by
  classical
  intro left right
  unfold localLayerPairCellBoundedProfileTransfer
  infer_instance

/-- On real encoded states, the common-carrier relation is exactly the
original positive support relation of the literal Cell `Count` matrix. -/
theorem localLayerPairCellBoundedProfileTransfer_code_iff
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (left right : LocalLayerPairCellProfile interface hcubic) :
    interface.localLayerPairCellBoundedProfileTransfer hcubic
        (interface.localLayerPairCellProfileCode hcubic left)
        (interface.localLayerPairCellProfileCode hcubic right) ↔
      interface.localLayerPairCellProfileTransfer hcubic left right := by
  constructor
  · rintro ⟨leftRaw, rightRaw, hleft, hright, htransfer⟩
    have hleftRaw : leftRaw = left :=
      interface.localLayerPairCellProfileCode_injective hcubic hleft
    have hrightRaw : rightRaw = right :=
      interface.localLayerPairCellProfileCode_injective hcubic hright
    simpa only [hleftRaw, hrightRaw] using htransfer
  · intro htransfer
    exact ⟨left, right, rfl, rfl, htransfer⟩

/-- Concrete semantics of the common-carrier transfer: between two encoded
states it holds exactly when the removed Cell has a literal Tait coloring
realizing the corresponding two full profiles. -/
theorem localLayerPairCellBoundedProfileTransfer_code_iff_exists_coloring
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (left right : LocalLayerPairCellProfile interface hcubic) :
    interface.localLayerPairCellBoundedProfileTransfer hcubic
        (interface.localLayerPairCellProfileCode hcubic left)
        (interface.localLayerPairCellProfileCode hcubic right) ↔
      ∃ coloring : interface.separatedLocalLayerPair
          |>.SourceCrosscutComplementLiteralOpenTaitColoring
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic,
        (interface.separatedLocalLayerPair
            |>.sourceCrosscutComplementLiteralOpenLeftProfile
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
              hcubic coloring.1 coloring.2) = left ∧
          (interface.separatedLocalLayerPair
            |>.sourceCrosscutComplementLiteralOpenRightProfile
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
              hcubic coloring.1 coloring.2) = right := by
  rw [interface.localLayerPairCellBoundedProfileTransfer_code_iff hcubic]
  exact interface.localLayerPairCellProfileTransfer_iff_exists_coloring
    hcubic left right

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
