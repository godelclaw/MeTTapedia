import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFiniteLocalCaps
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSuccessorPortIncidence

/-!
# Finite port labels for a serial boundary-rebase face step

The finite face-step code remembers occurrence-sensitive connectivity on the
eight-position switch carrier.  Successor port incidence still referred to
the ambient primal edge carried by each occurrence.  This file removes that
last ambient dependency by attaching a two-bit port-label table to the finite
carrier and proving that its closure test is exactly the literal successor
`fragmentContainsPort` coordinate.

The label table is extracted separately for every literal rebase.  It is one
field of the eventual heterogeneous transition receipt; it is not a quotient
by slab orientation and does not yet assemble the complete five-coordinate
transition or measure its reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

/-- The finite two-port label attached to every occurrence coordinate of one
facial step. -/
abbrev BoundedSerialBoundaryRebaseFacePortLabelCode
    (code : BoundedSerialBoundaryRebaseFaceStepCode) :=
  Fin code.localCode.vertexCount.val → Fin 2 → Bool

/-- Graph-free decoder: an output occurrence contains a displayed port when
its finite face-step component reaches some occurrence carrying that port. -/
def BoundedSerialBoundaryRebaseFacePortLabelCode.containsPort
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    (labels : BoundedSerialBoundaryRebaseFacePortLabelCode code)
    (start : Fin code.localCode.vertexCount.val) (port : Fin 2) : Prop :=
  ∃ occurrence, labels occurrence port = true ∧
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep code) start occurrence

/-- The source image uses at most one occurrence coordinate for each named
port on one two-sided ambient face.  Keeping this law explicit prevents the
finite label table from being mistaken for an arbitrary Boolean matrix. -/
def BoundedSerialBoundaryRebaseFacePortLabelCode.IsOneHot
    {code : BoundedSerialBoundaryRebaseFaceStepCode}
    (labels : BoundedSerialBoundaryRebaseFacePortLabelCode code) : Prop :=
  ∀ port left right,
    labels left port = true → labels right port = true → left = right

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFinitePortLabelsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Extract the exact two-port labels on the stable finite switch carrier of
one ambient face.  The coordinate is occurrence-sensitive even when the two
sides of a primal edge lie on the same orbit face. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt
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
    BoundedSerialBoundaryRebaseFacePortLabelCode
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root) := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  exact fun coordinate port => decide
    (faceCycleEdge RS root ((carrierCoordinate carrier).symm coordinate).1 =
      data.portEdge (.inl port))

@[simp]
theorem sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_eq_true_iff
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).localCode.vertexCount.val)
    (port : Fin 2) :
    sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root coordinate port = true ↔
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
              hcubic hrotation htwoSided hunique offset hnext root)).symm
            coordinate).1 =
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)).portEdge
          (.inl port) := by
  simp [sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt]

/-- Literal two-sided face geometry makes every extracted port-label column
one-hot. -/
theorem sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_isOneHot
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
    (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).IsOneHot := by
  intro port left right hleft hright
  have hleftEdge :=
    (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset hnext root left
        port).1 hleft
  have hrightEdge :=
    (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset hnext root right
        port).1 hright
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let coordinate := carrierCoordinate carrier
  apply coordinate.symm.injective
  apply Subtype.ext
  exact faceCycleEdge_injective
    embedded.cellulation.rotation.toRotationSystem htwoSided root
      (hleftEdge.trans hrightEdge.symm)

/-- The graph-level successor-port predicate is exactly the graph-free finite
label-and-closure decoder. -/
theorem sourceCorridorSerialBoundaryRebaseSuccessorFaceContainsPortAt_iff_finiteCode
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
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext)
    (port : Fin 2) :
    SourceCorridorSerialBoundaryRebaseSuccessorFaceContainsPortAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment port ↔
      let RS := embedded.cellulation.rotation.toRotationSystem
      let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
      let root := orbitFaceRoot RS (data.fragmentFace fragment)
      let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root
      let labels := sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      BoundedSerialBoundaryRebaseFacePortLabelCode.containsPort
        (code := code) labels
        (carrierCoordinate carrier
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext fragment)) port := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let coordinate := carrierCoordinate carrier
  let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let labels := sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  change
    (∃ occurrence : {position // position ∈ carrier},
      faceCycleEdge RS root occurrence.1 = data.portEdge (.inl port) ∧
        Relation.ReflTransGen
          (boundedSerialBoundaryRebaseFaceComponentStep code)
          (coordinate
            (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
              hcubic hrotation htwoSided hunique offset hnext fragment))
          (coordinate occurrence)) ↔
      BoundedSerialBoundaryRebaseFacePortLabelCode.containsPort
        (code := code) labels
        (coordinate
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext fragment)) port
  constructor
  · rintro ⟨occurrence, hedge, hclosure⟩
    refine ⟨coordinate occurrence, ?_, hclosure⟩
    apply (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        (coordinate occurrence) port).2
    simpa [coordinate, carrier, RS, data] using hedge
  · rintro ⟨occurrence, hlabel, hclosure⟩
    refine ⟨coordinate.symm occurrence, ?_, ?_⟩
    · have hedge :=
        (sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt_eq_true_iff
          realization hcubic hrotation htwoSided hunique offset hnext root
            occurrence port).1 hlabel
      simpa [coordinate, carrier, RS, data] using hedge
    · simpa using hclosure

/-- The literal successor profile's port-incidence coordinate is decoded
exactly by finite labels and finite face-step closure. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_finiteCode
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
      let labels := sourceCorridorSerialBoundaryRebaseFacePortLabelCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      BoundedSerialBoundaryRebaseFacePortLabelCode.containsPort
        (code := code) labels
        (carrierCoordinate carrier
          (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
            hcubic hrotation htwoSided hunique offset hnext fragment)) port := by
  rw [sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_faceStepCode]
  exact sourceCorridorSerialBoundaryRebaseSuccessorFaceContainsPortAt_iff_finiteCode
    realization hcubic hrotation htwoSided hunique offset hnext fragment port

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
