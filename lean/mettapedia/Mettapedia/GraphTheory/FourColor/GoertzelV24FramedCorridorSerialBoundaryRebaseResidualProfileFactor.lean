import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseProfileFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphPortResidualFactorContraction

/-!
# Exact residual-aware profile factorization of a serial rebase

The six old attachment roles of a literal boundary rebase need not all meet
the two persistent output ports.  Requiring that statement as portal coverage
would be stronger than the source geometry proved so far.  This module keeps
the exact alternative as finite state: a component either meets a persistent
port, or is port-free on the six-role interface.

The resulting factorization is unconditional.  It is also deliberately a
state refinement rather than a local-letter decoder: the residual matrix is
extracted from the accumulated prefix.  A later recurrence must compute this
finite matrix from the preceding refined state and the literal heterogeneous
Cell/rebase receipts before a reachable-state closure is claimed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseResidualProfileFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The exact finite residual-aware tracked state at one old-prefix rebase
interface, for all three tracked colour pairs. -/
abbrev SourceCorridorSerialBoundaryRebaseResidualTrackedCode
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :=
  TrackedColorPair →
    BoundedPortResidualCode
      (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) (Fin 2)

/-- Extract the exact six-role component state of the accumulated prefix.
The two ports are the outgoing crossings of the current literal Cell. -/
noncomputable def sourceCorridorSerialBoundaryRebaseResidualTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    SourceCorridorSerialBoundaryRebaseResidualTrackedCode offset :=
  fun pair =>
    exactPortResidualCode
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2)
      (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)

/-- The exact finite relation obtained from the residual-aware six-role state
and the persistent-port connectivity stored in the incoming profile. -/
def sourceCorridorSerialBoundaryRebaseResidualProfileFactoredTrackedStep
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
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    Prop :=
  PortResidualFactoredReachability
    (sourceCorridorSerialBoundaryRebaseResidualTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset color pair)
    (fun leftPort rightPort =>
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
        hrotation htwoSided hunique offset color hcolor).profile.strandConnected
          pair (.inl leftPort) (.inl rightPort) = true)
    left right

/-- Literal old-prefix reachability on all six possible rebase contacts is
exactly the finite residual-or-port relation.  Unlike the earlier pure-port
factorization, this theorem has no attachment-soundness or portal-coverage
premise. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedReachable_iff_residualProfileFactored
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
      sourceCorridorSerialBoundaryRebaseResidualProfileFactoredTrackedStep
        realization hcubic hrotation htwoSided hunique offset color hcolor pair
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
  apply reachable_iff_exactPortResidualFactoredReachability graph
    interfaceVertex portVertex portConnected
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
