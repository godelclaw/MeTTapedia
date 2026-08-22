import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceDartCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphPortResidualFactorContraction

/-!
# Residual-aware predecessor face state for a serial rebase

The facial rebase step stores old-prefix connectivity on literal dart
occurrences.  The predecessor profile, however, exposes only its canonical
boundary fragments.  A component of the finite switch may also miss every
such fragment, so a pure boundary-port factorization would be too strong.

This file retains the exact finite alternative.  Each switch occurrence is
either connected through one of the predecessor boundary fragments, or its
port-free component is recorded by an explicit residual bit.  Canonical
boundary-fragment darts are connected precisely when their fragment
coordinates agree, so the factorization contains no ambient graph relation
between ports.

This is predecessor state, not yet a history-independent source letter.  A
later recurrence must compute the residual bits from the preceding refined
state and the literal heterogeneous Cell/rebase receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceResidualProfileFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual predecessor boundary-fragment coordinates visible to one
serial rebase. -/
abbrev SourceCorridorSerialBoundaryRebaseFacePortAt
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
  SerialCutFragmentIndex
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset)

/-- The canonical literal dart occurrence representing one predecessor face
port. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFacePortDartAt
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
    (port : SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
      hrotation htwoSided hunique offset) :
    embedded.cellulation.rotation.toRotationSystem.D :=
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)
  let region :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  (boundaryRegionalFragmentDartOccurrence RS cut region
    (boundaryRegionalFragmentAt RS cut region port)).1

/-- Two predecessor face ports are connected in the old regional face graph
exactly when they are the same canonical fragment coordinate. -/
theorem sourceCorridorSerialBoundaryRebaseFacePortDartAt_reachable_iff_eq
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
    (left right : SourceCorridorSerialBoundaryRebaseFacePortAt realization
      hcubic hrotation htwoSided hunique offset) :
    (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges).Reachable
        (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
          hrotation htwoSided hunique offset left)
        (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
          hrotation htwoSided hunique offset right) ↔
      left = right := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)
  let region :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  rw [show sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
      hrotation htwoSided hunique offset left =
        (boundaryRegionalFragmentDartOccurrence RS cut region
          (boundaryRegionalFragmentAt RS cut region left)).1 by rfl]
  rw [show sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
      hrotation htwoSided hunique offset right =
        (boundaryRegionalFragmentDartOccurrence RS cut region
          (boundaryRegionalFragmentAt RS cut region right)).1 by rfl]
  rw [boundaryRegionalFragmentDartOccurrence_reachable_iff_eq]
  exact ⟨fun h => (boundaryRegionalFragmentAt_injective RS cut region) h,
    fun h => congrArg (boundaryRegionalFragmentAt RS cut region) h⟩

/-- The exact predecessor facial component state on the stable switch-dart
carrier, relative to the displayed predecessor boundary fragments. -/
abbrev SourceCorridorSerialBoundaryRebaseResidualFaceCodeAt
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
  BoundedPortResidualCode
    (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic hrotation
      htwoSided hunique offset)

/-- Extract the exact predecessor facial residual state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt
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
    SourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext :=
  exactPortResidualCode
    (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges)
    Subtype.val
    (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
      hrotation htwoSided hunique offset)

/-- Interpret the finite predecessor facial residual state.  Boundary ports
are component coordinates, so their graph-free relation is equality. -/
def sourceCorridorSerialBoundaryRebaseResidualFaceFactoredStep
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
    (left right :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) : Prop :=
  PortResidualFactoredReachability
    (sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    (fun leftPort rightPort => leftPort = rightPort)
    left right

/-- Literal old-prefix facial reachability on every switch dart occurrence is
exactly the finite residual-or-boundary-fragment relation. -/
theorem sourceCorridorSerialBoundaryRebaseFaceReachable_iff_residualFactored
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
    (left right :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) :
    (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges).Reachable left.1 right.1 ↔
      sourceCorridorSerialBoundaryRebaseResidualFaceFactoredStep realization
        hcubic hrotation htwoSided hunique offset hnext left right := by
  apply reachable_iff_exactPortResidualFactoredReachability
    (faceRegionalDartGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges)
    Subtype.val
    (sourceCorridorSerialBoundaryRebaseFacePortDartAt realization hcubic
      hrotation htwoSided hunique offset)
    (fun leftPort rightPort => leftPort = rightPort)
  · intro first second heq
    subst second
    exact SimpleGraph.Reachable.refl _
  · intro first second _hfirstSupport _hsecondSupport hreachable
    exact
      (sourceCorridorSerialBoundaryRebaseFacePortDartAt_reachable_iff_eq
        realization hcubic hrotation htwoSided hunique offset first second).1
        hreachable

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
