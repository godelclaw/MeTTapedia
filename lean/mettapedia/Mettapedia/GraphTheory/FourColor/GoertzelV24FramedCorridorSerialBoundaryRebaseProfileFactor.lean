import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseAttachmentCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphPortFactorContraction

/-!
# Factoring a serial rebase through the incoming boundary profile

The old side of a literal boundary rebase has at most six source attachment
roles.  This module proves the exact finite-state interface needed to replace
reachability through the accumulated prefix: each active role attaches to one
of the two old ports, and the incoming profile supplies the port-to-port
component relation.

The attachment relation remains an explicit argument.  Its soundness and
support coverage are the source-specific portal-completeness obligation; they
are not hidden in the decoder and no ambient-prefix residue is added to the
state.  Consequently this factorization is suitable for pumping once that
local geometric obligation is discharged.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphPortFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseProfileFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The finite relation obtained by attaching the at-most-six old rebase
roles to the two persistent ports and reading port connectivity from the
actual incoming profile. -/
def sourceCorridorSerialBoundaryRebaseProfileFactoredTrackedStep
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
    (pair : TrackedColorPair)
    (attaches : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset →
      Fin 2 → Prop)
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    Prop :=
  PortFactoredReachability
    (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
      hrotation htwoSided hunique offset)
    attaches
    (fun leftPort rightPort =>
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
        hrotation htwoSided hunique offset color hcolor).profile.strandConnected
          pair (.inl leftPort) (.inl rightPort) = true)
    left right

/-- Subject only to the explicit local attachment soundness and coverage
premises, literal old-prefix reachability on the six-role rebase interface is
exactly the finite relation computed from those attachments and the incoming
profile.

This theorem is the algebraic half of the rebase compression.  The two
premises are deliberately phrased on the literal source graph so that the
next geometric theorem has one precise target and cannot be replaced by an
extra state coordinate. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedReachable_iff_profileFactored
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
    (pair : TrackedColorPair)
    (attaches : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset →
      Fin 2 → Prop)
    (hattachSound : ∀ role port,
      attaches role port →
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
              hcubic hrotation htwoSided hunique offset role)
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).nextLocalLayerPrefixCrossing port))
    (hattachCoverage : ∀ role,
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
          hrotation htwoSided hunique offset role ∈
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).support →
      ∃ port, attaches role port)
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    (regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable
        (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset left)
        (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset right) ↔
      sourceCorridorSerialBoundaryRebaseProfileFactoredTrackedStep realization
        hcubic hrotation htwoSided hunique offset color hcolor pair attaches
          left right := by
  let graph := regionalTrackedEdgeGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges color
    (trackedColorPairColors pair).1
    (trackedColorPairColors pair).2
  let interfaceVertex :=
    sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
      hrotation htwoSided hunique offset
  let portVertex := fun port : Fin 2 =>
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing port
  let input := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hcolor
  let portConnected := fun leftPort rightPort : Fin 2 =>
    input.profile.strandConnected pair (.inl leftPort) (.inl rightPort) = true
  apply reachable_iff_portFactoredReachability graph interfaceVertex portVertex
    attaches portConnected hattachSound hattachCoverage
  · intro first second hconnected
    let data := sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset
    have hraw :
        (data.regionalProfile color hcolor).strandConnected pair
            (.inl first) (.inl second) = true := by
      simpa [input, sourceCorridorSerialPrefixBoundedProfileAt,
        sourceCorridorSerialPrefixCutDataAt, regionalBoundaryBoundedProfile,
        data, portConnected]
        using hconnected
    exact (data.regionalProfile_strandConnected_eq_true_iff
      color hcolor pair (.inl first) (.inl second)).1 hraw |>.2.2.2.2
  · intro first second hfirstSupport hsecondSupport hreachable
    let data := sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset
    rcases (SimpleGraph.mem_support graph).1 hfirstSupport with
      ⟨firstNeighbor, hfirstAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hsecondSupport with
      ⟨secondNeighbor, hsecondAdj⟩
    have hraw :
        (data.regionalProfile color hcolor).strandConnected pair
            (.inl first) (.inl second) = true :=
      (data.regionalProfile_strandConnected_eq_true_iff
        color hcolor pair (.inl first) (.inl second)).2
        ⟨sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
            hrotation htwoSided hunique offset (.inl first),
          sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
            hrotation htwoSided hunique offset (.inl second),
          hfirstAdj.1.2.1, hsecondAdj.1.2.1, hreachable⟩
    simpa [input, sourceCorridorSerialPrefixBoundedProfileAt,
      sourceCorridorSerialPrefixCutDataAt, regionalBoundaryBoundedProfile,
      data, portConnected] using hraw

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
