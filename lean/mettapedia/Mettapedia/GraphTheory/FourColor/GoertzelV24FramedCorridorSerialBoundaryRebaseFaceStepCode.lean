import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFiniteSwitch

/-!
# A finite occurrence-sensitive face step for one literal serial rebase

The successor face graph is the union of the accumulated prefix, the newly
displayed two-edge region, and their residual facial seam.  The seam alone has
an eight-position support code, but a recurrence must retain every switch
position, including a position isolated in the seam and used by another
factor.

For a fixed ambient face this file therefore takes all occurrences whose
underlying edge lies in the exact eight-edge rebase switch.  Two-sidedness
makes the edge projection injective, so there are at most eight such
positions.  The new-region and seam factors are transported together through
that one coordinate system; the old-prefix component relation is retained as
finite state on the same coordinates.  The resulting closure equation is
exact and graph-free after extraction.

This is the facial analogue of the tracked rebase step.  It does not yet prove
that the preceding five-field profile determines every old component entry or
compute the capped face-progress update.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SimpleGraphThreeFactorContraction
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

/-- One finite occurrence-sensitive facial successor step.  `localCode`
contains the newly displayed regional graph and the residual seam.  The
accumulated old-prefix component relation is state on the same coordinates. -/
structure BoundedSerialBoundaryRebaseFaceStepCode where
  localCode : BoundedCarrierGraphFamilyCode 8 0 Bool
  oldComponent :
    Fin localCode.vertexCount.val → Fin localCode.vertexCount.val → Bool

noncomputable instance :
    DecidableEq BoundedSerialBoundaryRebaseFaceStepCode :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseFaceStepCodeEquiv :
    BoundedSerialBoundaryRebaseFaceStepCode ≃
      Σ localCode : BoundedCarrierGraphFamilyCode 8 0 Bool,
        Fin localCode.vertexCount.val →
          Fin localCode.vertexCount.val → Bool where
  toFun code := ⟨code.localCode, code.oldComponent⟩
  invFun code :=
    { localCode := code.1
      oldComponent := code.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype BoundedSerialBoundaryRebaseFaceStepCode :=
  Fintype.ofEquiv _ boundedSerialBoundaryRebaseFaceStepCodeEquiv.symm

/-- One component move through the old face state, the newly displayed
regional graph, or the residual facial seam. -/
def boundedSerialBoundaryRebaseFaceComponentStep
    (code : BoundedSerialBoundaryRebaseFaceStepCode)
    (left right : Fin code.localCode.vertexCount.val) : Prop :=
  code.oldComponent left right = true ∨
    (code.localCode.graph false).Reachable left right ∨
    (code.localCode.graph true).Reachable left right

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceStepCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Occurrences of the exact eight-edge rebase switch on one ambient face
orbit.  Unlike the seam support, this carrier retains switch positions that
are isolated in one local factor. -/
def sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
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
    Finset
      (Fin (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :=
  faceRegionalPositions embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext)

@[simp]
theorem mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
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
    (position : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    position ∈ sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
        realization hcubic hrotation htwoSided hunique offset hnext root ↔
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          position ∈
        sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
  exact mem_faceRegionalPositions_iff _ _ _ _

/-- A two-sided face contains at most one occurrence of each switch edge, so
the occurrence carrier has cardinality at most eight. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_card_le_eight
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
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
      hcubic hrotation htwoSided hunique offset hnext root).card ≤ 8 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let switch := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let positions := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  calc
    positions.card = (positions.image (faceCycleEdge RS root)).card :=
      (Finset.card_image_of_injective positions
        (faceCycleEdge_injective RS htwoSided root)).symm
    _ = (orbitFaceBoundary RS (dartOrbitFace RS root) ∩ switch).card := by
      congr 1
      exact image_faceRegionalPositions_eq_boundary_inter_region
        RS htwoSided root switch
    _ ≤ switch.card := Finset.card_le_card (Finset.inter_subset_right)
    _ ≤ 8 := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext

/-- The two local facial factors: `false` is the newly displayed regional
graph and `true` is the residual seam. -/
def sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt
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
    (factor : Bool) :
    SimpleGraph
      (Fin (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :=
  if factor then
    sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root
  else
    faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext)

/-- Both local facial factors are supported on the exact occurrence carrier. -/
theorem sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt_support_subset_switch
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
    (factor : Bool) :
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext root factor).support ⊆
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root := by
  cases factor
  · intro position hposition
    rcases (SimpleGraph.mem_support _).1 hposition with ⟨neighbor, hadj⟩
    simp [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt] at hadj
    apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        position).2
    exact Finset.mem_union_right _ hadj.2.1
  · intro position hposition
    simp [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt] at hposition
    apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        position).2
    exact
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext root
          position hposition

/-- The two local face factors transported together to one canonical carrier
of at most eight occurrence positions. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt
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
    BoundedCarrierGraphFamilyCode 8 0 Bool :=
  boundedCarrierGraphFamilyCode
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
      hcubic hrotation htwoSided hunique offset hnext root)
    8 0
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext root)
    (fun point => Fin.elim0 point)
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext root)

/-- The local finite code preserves factor reachability between all switch
occurrences. -/
theorem sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_reachable_iff
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
    (factor : Bool)
    (first second : {position // position ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root}) :
    ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).graph factor).Reachable
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root) first)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root) second) ↔
      (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext root factor).Reachable
          first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
      hcubic hrotation htwoSided hunique offset hnext root)
    8 0
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext root)
    (fun point => Fin.elim0 point)
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    factor
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt_support_subset_switch
      realization hcubic hrotation htwoSided hunique offset hnext root factor)
    first second

/-- Reachability after one facial rebase is exactly the closure of the three
factor-component relations on the at-most-eight switch occurrences. -/
theorem sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceSwitchClosure
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
    (left right : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card)
    (hleft : left ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root)
    (hright : right ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root) :
    (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
      ).Reachable left right ↔
    Relation.ReflTransGen
      (SelectedThreeFactorComponentStep
        (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges)
        (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext))
        (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext root)
        (fun position => position ∈
          sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root))
      ⟨left, hleft⟩ ⟨right, hright⟩ := by
  rw [sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
    realization hcubic hrotation htwoSided hunique offset hnext root]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y hx hy hold hnew
    apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        middle).2
    have hinter := faceRegionalAmbientPositionGraph_switch_mem_inter
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext)
      hx hy hold hnew
    exact Finset.mem_union_right _ (Finset.mem_inter.1 hinter).2
  · intro x middle y _hx hy _hold hseam
    apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        middle).2
    apply
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext root
    exact SimpleGraph.mem_support_of_reachable hy hseam
  · intro x middle y _hx hy _hnew hseam
    apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        middle).2
    apply
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext root
    exact SimpleGraph.mem_support_of_reachable hy hseam

/-- Extract the exact finite facial state-and-letter step on one ambient face.
The old component matrix is the only accumulated prefix field. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceStepCodeAt
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
    BoundedSerialBoundaryRebaseFaceStepCode := by
  classical
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let localCode := sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  refine {
    localCode := localCode
    oldComponent := fun left right => by
      exact decide
        ((faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).Reachable
              ((carrierCoordinate carrier).symm left).1
              ((carrierCoordinate carrier).symm right).1) }

@[simp]
theorem sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
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
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).oldComponent left right =
        true ↔
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges).Reachable
            ((carrierCoordinate
              (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
                realization hcubic hrotation htwoSided hunique offset hnext
                  root)).symm left).1
            ((carrierCoordinate
              (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
                realization hcubic hrotation htwoSided hunique offset hnext
                  root)).symm right).1 := by
  simp [sourceCorridorSerialBoundaryRebaseFaceStepCodeAt]

/-- The exact successor facial connectivity between switch occurrences is
computed by closure of the finite old-component matrix and the two finite
local factor graphs. -/
theorem sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceStepCode
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
    (left right : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card)
    (hleft : left ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root)
    (hright : right ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root) :
    (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
      ).Reachable left right ↔
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep
        (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext root))
      (carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root) ⟨left, hleft⟩)
      (carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root) ⟨right, hright⟩) := by
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let coordinate := carrierCoordinate carrier
  let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  rw [sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceSwitchClosure
    realization hcubic hrotation htwoSided hunique offset hnext root left right
      hleft hright]
  have hstep (first second : {position // position ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
              htwoSided hunique offset).regionEdges)
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
              hrotation htwoSided hunique offset hnext))
          (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
            hrotation htwoSided hunique offset hnext root)
          (fun position => position ∈ carrier) first second ↔
        boundedSerialBoundaryRebaseFaceComponentStep code
          (coordinate first) (coordinate second) := by
    constructor
    · rintro (hold | hnew | hseam)
      · exact Or.inl
          ((sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
            realization hcubic hrotation htwoSided hunique offset hnext root
              (coordinate first) (coordinate second)).2 (by
                simpa [coordinate, carrier] using hold))
      · exact Or.inr (Or.inl
          ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext root
              false first second).2 (by
                simpa [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt]
                  using hnew)))
      · exact Or.inr (Or.inr
          ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext root
              true first second).2 (by
                simpa [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt]
                  using hseam)))
    · rintro (hold | hnew | hseam)
      · exact Or.inl (by
          have :=
            (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
              realization hcubic hrotation htwoSided hunique offset hnext root
                (coordinate first) (coordinate second)).1 hold
          simpa [coordinate, carrier] using this)
      · exact Or.inr (Or.inl (by
          have :=
            (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_reachable_iff
              realization hcubic hrotation htwoSided hunique offset hnext root
                false first second).1 hnew
          simpa [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt] using this))
      · exact Or.inr (Or.inr (by
          have :=
            (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_reachable_iff
              realization hcubic hrotation htwoSided hunique offset hnext root
                true first second).1 hseam
          simpa [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt] using this))
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift := Relation.ReflTransGen.lift coordinate.symm
      (fun first second h => (hstep (coordinate.symm first)
        (coordinate.symm second)).2 (by simpa using h)) hclosure
    simpa [coordinate, carrier] using hlift

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
