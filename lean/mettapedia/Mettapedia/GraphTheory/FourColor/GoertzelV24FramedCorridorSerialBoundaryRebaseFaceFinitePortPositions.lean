import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFinitePortLabels

/-!
# Position-coded successor face ports

On one two-sided ambient face, a named primal port occurs at zero or one
coordinates of the finite rebase switch.  A Boolean column therefore stores
more states than the literal geometry can realize.  This file replaces each
one-hot column by `Option (Fin n)`, proves an exact round trip for the closure
test, and bounds the complete two-port code by eighty-one possibilities.

Every literal boundary rebase supplies this compact code.  The result reduces
one field of the eventual heterogeneous transition receipt; it does not yet
assemble that receipt, measure its reachable closure, or derive a threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

/-- The compact location of each of the two displayed ports on one finite
facial switch carrier. -/
abbrev BoundedSerialBoundaryRebaseFacePortPositionCode
    (code : BoundedSerialBoundaryRebaseFaceStepCode) :=
  Fin 2 → Option (Fin code.localCode.vertexCount.val)

/-- The exact cardinality of the compact two-port position code. -/
theorem card_boundedSerialBoundaryRebaseFacePortPositionCode
    (code : BoundedSerialBoundaryRebaseFaceStepCode) :
    Fintype.card (BoundedSerialBoundaryRebaseFacePortPositionCode code) =
      (code.localCode.vertexCount.val + 1) ^ 2 := by
  simp [BoundedSerialBoundaryRebaseFacePortPositionCode]

/-- The at-most-eight-position switch admits at most `9² = 81` compact
two-port codes. -/
theorem card_boundedSerialBoundaryRebaseFacePortPositionCode_le_81
    (code : BoundedSerialBoundaryRebaseFaceStepCode) :
    Fintype.card (BoundedSerialBoundaryRebaseFacePortPositionCode code) ≤ 81 := by
  rw [card_boundedSerialBoundaryRebaseFacePortPositionCode]
  calc
    (code.localCode.vertexCount.val + 1) ^ 2 ≤ (8 + 1) ^ 2 :=
      Nat.pow_le_pow_left
        (Nat.succ_le_succ (Nat.le_of_lt_succ code.localCode.vertexCount.isLt)) 2
    _ = 81 := by norm_num

/-- Select the unique coordinate carrying a port, if it exists. -/
noncomputable def BoundedSerialBoundaryRebaseFacePortLabelCode.IsOneHot.position
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    {labels : BoundedSerialBoundaryRebaseFacePortLabelCode code}
    (_hlabels : labels.IsOneHot) :
    BoundedSerialBoundaryRebaseFacePortPositionCode code := by
  classical
  intro port
  exact if h : ∃ coordinate, labels coordinate port = true then
    some (Classical.choose h)
  else
    none

/-- The selected optional coordinate is present exactly at a true entry of
the original one-hot Boolean column. -/
theorem BoundedSerialBoundaryRebaseFacePortLabelCode.IsOneHot.position_eq_some_iff
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    {labels : BoundedSerialBoundaryRebaseFacePortLabelCode code}
    (hlabels : labels.IsOneHot) (port : Fin 2)
    (coordinate : Fin code.localCode.vertexCount.val) :
    hlabels.position port = some coordinate ↔
      labels coordinate port = true := by
  classical
  unfold BoundedSerialBoundaryRebaseFacePortLabelCode.IsOneHot.position
  split_ifs with hexists
  · constructor
    · intro heq
      have hcoordinate : Classical.choose hexists = coordinate := by
        exact Option.some.inj heq
      simpa [hcoordinate] using Classical.choose_spec hexists
    · intro hcoordinate
      congr 1
      exact hlabels port (Classical.choose hexists) coordinate
        (Classical.choose_spec hexists) hcoordinate
  · constructor
    · intro heq
      cases heq
    · intro hcoordinate
      exact False.elim (hexists ⟨coordinate, hcoordinate⟩)

/-- Graph-free closure decoder using the compact optional port positions. -/
def BoundedSerialBoundaryRebaseFacePortPositionCode.containsPort
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    (positions : BoundedSerialBoundaryRebaseFacePortPositionCode code)
    (start : Fin code.localCode.vertexCount.val) (port : Fin 2) : Prop :=
  ∃ occurrence, positions port = some occurrence ∧
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep code) start occurrence

/-- Replacing one-hot Boolean columns by optional positions preserves the
finite port-incidence closure test exactly. -/
theorem BoundedSerialBoundaryRebaseFacePortLabelCode.IsOneHot.containsPort_iff_position
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    {labels : BoundedSerialBoundaryRebaseFacePortLabelCode code}
    (hlabels : labels.IsOneHot)
    (start : Fin code.localCode.vertexCount.val) (port : Fin 2) :
    labels.containsPort start port ↔
      hlabels.position.containsPort start port := by
  constructor
  · rintro ⟨occurrence, hlabel, hclosure⟩
    exact ⟨occurrence,
      (hlabels.position_eq_some_iff port occurrence).2 hlabel, hclosure⟩
  · rintro ⟨occurrence, hposition, hclosure⟩
    exact ⟨occurrence,
      (hlabels.position_eq_some_iff port occurrence).1 hposition, hclosure⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFinitePortPositionsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Compact port positions extracted from one literal serial boundary rebase
on one ambient face. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFacePortPositionCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    BoundedSerialBoundaryRebaseFacePortPositionCode
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root) :=
  (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_isOneHot realization
    hcubic hrotation htwoSided hunique offset hnext root).position

/-- The literal successor profile's port-incidence coordinate is decoded by
the compact optional positions and finite closure. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_finitePositionCode
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
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext)
    (port : Fin 2) :
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.fragmentContainsPort fragment (.inl port) = true) ↔
      let RS := embedded.cellulation.rotation.toRotationSystem
      let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
      let root := orbitFaceRoot RS (data.fragmentFace fragment)
      let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root
      let positions := sourceCorridorSerialBoundaryRebaseFacePortPositionCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      BoundedSerialBoundaryRebaseFacePortPositionCode.containsPort
        (code := code) positions
        (carrierCoordinate carrier
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext fragment)) port := by
  rw [sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_finiteCode]
  exact
    (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_isOneHot realization
      hcubic hrotation htwoSided hunique offset hnext
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          |>.fragmentFace fragment))).containsPort_iff_position _ port

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
