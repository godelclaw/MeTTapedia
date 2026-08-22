import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceStepCode

/-!
# A stable dart-occurrence carrier for one facial serial rebase

The preceding facial step code is organized separately on each ambient face.
For recurrence across literal Cells, the same primal switch edge may occur on
two different sides, so its underlying edge is not a sufficient coordinate.

This file uses the actual darts over the exact eight-edge rebase switch as a
single stable carrier.  The carrier has at most sixteen elements.  For every
face root, its existing switch-position carrier is equivalent to the fiber of
the global dart carrier on that orbit face.  Thus no facial occurrence is
identified merely because it lies over the same primal edge.

This is an occurrence ABI for the predecessor-state equation.  It does not yet
prove that the preceding five-field profile determines the old-component
submatrix or remove the finite facial residual.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceDartCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual dart occurrences over the exact eight-edge successor switch.
This is the stable facial coordinate carrier: the two darts over one primal
edge remain distinct. -/
abbrev SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt
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
    (hnext : offset.val + 1 < blockLength - 3) :=
  CutDartOccurrence embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext)

/-- The global occurrence carrier has at most two darts over each of the
at-most-eight switch edges. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt_card_le_sixteen
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
    (hnext : offset.val + 1 < blockLength - 3) :
    Nat.card
        (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt
          realization hcubic hrotation htwoSided hunique offset hnext) ≤ 16 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let switch := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  letI : Fintype (CutDartOccurrence RS switch) := Subtype.fintype _
  calc
    Nat.card
        (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt
          realization hcubic hrotation htwoSided hunique offset hnext) ≤
        2 * (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
          hcubic hrotation htwoSided hunique offset hnext).card :=
      by
        rw [Nat.card_eq_fintype_card]
        exact card_cutDartOccurrence_le_two_mul_card RS switch
    _ ≤ 2 * 8 := Nat.mul_le_mul_left 2
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight
        realization hcubic hrotation htwoSided hunique offset hnext)
    _ = 16 := by norm_num

/-- The part of the stable occurrence carrier lying on the orbit face of one
chosen root. -/
abbrev SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceOnFaceAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :=
  { occurrence :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext //
    dartOrbitFace embedded.cellulation.rotation.toRotationSystem occurrence.1 =
      dartOrbitFace embedded.cellulation.rotation.toRotationSystem root }

/-- Send one cyclic switch position on a fixed face to its actual dart in the
global switch carrier. -/
def sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
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
    ↑(sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root) →
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceOnFaceAt
        realization hcubic hrotation htwoSided hunique offset hnext root :=
  fun position =>
    ⟨⟨faceCycleDart embedded.cellulation.rotation.toRotationSystem root
        position.1, by
      change faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          position.1 ∈
        sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext
      exact
        (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
          realization hcubic hrotation htwoSided hunique offset hnext root
          position.1).1 position.2⟩,
      dartOrbitFace_faceCycleDart
        embedded.cellulation.rotation.toRotationSystem root position.1⟩

/-- The occurrence map remembers its literal dart definitionally. -/
@[simp]
theorem sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt_val
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
    (position :
      ↑(sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root)) :
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
      realization hcubic hrotation htwoSided hunique offset hnext root
      position).1.1 =
      faceCycleDart embedded.cellulation.rotation.toRotationSystem root
        position.1 :=
  rfl

/-- Distinct cyclic positions map to distinct dart occurrences without any
edge-level simplicity assumption. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt_injective
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
    Function.Injective
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
        realization hcubic hrotation htwoSided hunique offset hnext root) := by
  intro left right heq
  apply Subtype.ext
  apply faceCycleDart_injective
    embedded.cellulation.rotation.toRotationSystem root
  exact congrArg (fun occurrence => occurrence.1.1) heq

/-- Every switch dart on the chosen orbit face has a unique cyclic position,
so the old per-face carrier is exactly one fiber of the stable global carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartEquivAt
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
    ↑(sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root) ≃
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceOnFaceAt
        realization hcubic hrotation htwoSided hunique offset hnext root :=
  Equiv.ofBijective
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
      realization hcubic hrotation htwoSided hunique offset hnext root)
    ⟨sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt_injective
        realization hcubic hrotation htwoSided hunique offset hnext root,
      by
        intro occurrence
        let RS := embedded.cellulation.rotation.toRotationSystem
        have hdart : occurrence.1.1 ∈ RS.faceOrbit root := by
          rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root,
            mem_orbitFaceDarts_iff]
          exact occurrence.2
        rcases existsUnique_faceCycleDart_eq RS root occurrence.1.1 hdart with
          ⟨position, hposition, _huniquePosition⟩
        have hpositionMem : position ∈
            sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
              hcubic hrotation htwoSided hunique offset hnext root := by
          rw [mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff]
          change RS.edgeOf (faceCycleDart RS root position) ∈
            sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
              hrotation htwoSided hunique offset hnext
          rw [hposition]
          exact occurrence.1.2
        refine ⟨⟨position, hpositionMem⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hposition⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
