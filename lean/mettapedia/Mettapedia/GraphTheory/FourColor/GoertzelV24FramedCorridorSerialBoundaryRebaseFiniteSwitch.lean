import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseAttachmentCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# An eight-edge switch interface for a literal serial rebase

The exact successor update is a union of three tracked graphs: the accumulated
old prefix, the two newly displayed crossing edges, and the residual seam
between them.  A walk can switch factors only at one of the at-most-six old
attachment roles or at one of the two new edges.

This file packages those literal edges as a finite interface of cardinality at
most eight and contracts reachability in the three-factor update onto it.  It
does not yet replace the factor-component relations by a graph-free letter
code.  In particular, the old-prefix component relation is the residual-aware
state retained by the preceding factorization, while the new and seam
component relations still await their finite literal-Cell decoder.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceSpliceConnectivity
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphThreeFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFiniteSwitchEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal old edges named by the at-most-six rebase attachment roles. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt
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
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  Finset.univ.image
    (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
      hrotation htwoSided hunique offset)

/-- The old attachment edge set has cardinality at most six. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt_card_le_six
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
    (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt realization
      hcubic hrotation htwoSided hunique offset).card ≤ 6 := by
  calc
    _ ≤ (Finset.univ : Finset
        (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset)).card :=
      Finset.card_image_le
    _ = Fintype.card
        (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :=
      Finset.card_univ
    _ ≤ 6 :=
      sourceCorridorSerialBoundaryRebaseOldAttachmentRole_card_le_six offset

/-- The exact switch interface: six possible old contacts together with the
two newly displayed crossing edges. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFiniteSwitchAt
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
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt realization hcubic
      hrotation htwoSided hunique offset ∪
    sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext

/-- The switch interface contains at most eight literal primal edges. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight
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
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext).card ≤ 8 := by
  calc
    _ ≤
        (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt realization
          hcubic hrotation htwoSided hunique offset).card +
        (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext).card :=
      by
        simpa [sourceCorridorSerialBoundaryRebaseFiniteSwitchAt] using
          Finset.card_union_le
            (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt
              realization hcubic hrotation htwoSided hunique offset)
            (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
              hrotation htwoSided hunique offset hnext)
    _ ≤ 6 + 2 := Nat.add_le_add
      (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt_card_le_six
        realization hcubic hrotation htwoSided hunique offset)
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt_card_le_two realization
        hcubic hrotation htwoSided hunique offset hnext)
    _ = 8 := by norm_num

/-- Every old attachment role names an edge in the finite switch interface. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
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
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
        hrotation htwoSided hunique offset role ∈
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext := by
  apply Finset.mem_union_left
  exact Finset.mem_image.2 ⟨role, Finset.mem_univ role, rfl⟩

/-- Every newly displayed rebase crossing belongs to the finite switch
interface. -/
theorem sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
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
    (hnext : offset.val + 1 < blockLength - 3) (step : Fin 2) :
    sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic hrotation
        htwoSided hunique offset hnext step ∈
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext := by
  apply Finset.mem_union_right
  exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩

/-- Every non-isolated vertex of the residual tracked seam lies on the
eight-edge switch interface. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_finiteSwitch
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
    (color : G.edgeSet → Color) (first second : Color) :
    (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext color first second).support ⊆
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext color first second)).1 hedge
      with ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oriented_roles
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj with hold | hnew
  · rcases hold with ⟨role, hedgeEq, _⟩
    rw [hedgeEq]
    exact sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext role
  · rcases hnew with ⟨_, _, hedgeNew⟩
    exact Finset.mem_union_right _ hedgeNew

/-- Reachability between the two new cut edges after one literal rebase is
exactly the reflexive-transitive closure of the three factor-component
relations on the at-most-eight switch edges. -/
theorem sourceCorridorSerialInputTrackedGraph_next_reachable_iff_finiteSwitchClosure
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
    (color : G.edgeSet → Color) (first second : Color)
    (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        color first second).Reachable
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext left)
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext right) ↔
    Relation.ReflTransGen
      (SelectedThreeFactorComponentStep
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color first second)
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext) color first second)
        (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext color first second)
        (fun edge => edge ∈
          sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
            hrotation htwoSided hunique offset hnext))
      ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext left,
        sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
          realization hcubic hrotation htwoSided hunique offset hnext left⟩
      ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext right,
        sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
          realization hcubic hrotation htwoSided hunique offset hnext right⟩ := by
  rw [sourceCorridorSerialInputTrackedGraph_next_eq_rebase_three_factor
    realization hcubic hrotation htwoSided hunique offset hnext color first
      second]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y hx hy hold hnew
    have hinter := regionalTrackedEdgeGraph_switch_mem_inter
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext)
      color first second hx hy hold hnew
    exact Finset.mem_union_right _ (Finset.mem_inter.1 hinter).2
  · intro x middle y _hx hy _hold hseam
    apply
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext color first
          second
    exact SimpleGraph.mem_support_of_reachable hy hseam
  · intro x middle y _hx hy _hnew hseam
    apply
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext color first
          second
    exact SimpleGraph.mem_support_of_reachable hy hseam

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
