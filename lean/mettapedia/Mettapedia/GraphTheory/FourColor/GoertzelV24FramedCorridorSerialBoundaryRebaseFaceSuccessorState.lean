import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceDartCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFullProfileRelation

/-!
# Finite successor face coordinates for a serial boundary rebase

The facial rebase recurrence is computed on the stable carrier of dart
occurrences over the at-most-eight-edge switch.  The successor manuscript
profile is instead indexed by the open face fragments meeting its two newly
displayed crossing edges.  This file aligns those two finite presentations.

Every successor fragment has a canonical cut-dart occurrence.  Since its
chosen edge is one of the two new crossings, that dart belongs to the stable
switch carrier.  The resulting map is injective and transports the
successor profile's ambient-face equivalence bit exactly to equality of orbit
faces on the finite occurrence carrier.

This is a successor-state coordinate theorem.  It does not yet compute the
successor incidence or capped-length fields from the predecessor state, form
the complete alternating Cell/rebase recurrence, measure a reachable closure,
or derive a numerical threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

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

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceSuccessorStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual successor boundary-fragment coordinates visible after one
literal serial rebase. -/
abbrev SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
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
  SerialCutFragmentIndex
    (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))

/-- The canonical successor boundary fragment at one stored profile
coordinate. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt
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
    (port : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization
      hcubic hrotation htwoSided hunique offset hnext) :
    BoundaryRegionalFragment embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext)
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext)) :=
  boundaryRegionalFragmentAt
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext)) port

/-- The canonical cut dart of a successor boundary fragment, reindexed into
the stable at-most-sixteen-occurrence switch carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt
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
    (port : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization
      hcubic hrotation htwoSided hunique offset hnext) :
    SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
      hcubic hrotation htwoSided hunique offset hnext := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let region := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let fragment := sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext port
  let occurrence := boundaryRegionalFragmentDartOccurrence RS cut region fragment
  exact ⟨occurrence.1, Finset.mem_union_right _ occurrence.2⟩

/-- The successor-fragment occurrence map is injective: neither two sides of
one bridge nor two distinct regional components are collapsed. -/
theorem sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt_injective
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
    Function.Injective
      (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) := by
  intro left right heq
  apply boundaryRegionalFragmentAt_injective
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext))
  apply boundaryRegionalFragmentDartOccurrence_injective
  apply Subtype.ext
  exact congrArg (fun occurrence => occurrence.1) heq

/-- The canonical successor occurrence lies on exactly the orbit face named
by that successor fragment. -/
theorem dartOrbitFace_successorFaceOccurrenceAt
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
    (port : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization
      hcubic hrotation htwoSided hunique offset hnext) :
    dartOrbitFace embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt realization
          hcubic hrotation htwoSided hunique offset hnext port).1 =
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).fragmentFace port := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let region := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let fragment := sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt
    realization hcubic hrotation htwoSided hunique offset hnext port
  change dartOrbitFace RS
      (boundaryRegionalFragmentDartOccurrence RS cut region fragment).1 =
    fragment.1.1
  simp only [boundaryRegionalFragmentDartOccurrence]
  rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]

/-- The successor profile's face-continuation bit is exactly ambient orbit
face equality on its finite stable occurrence coordinates.  This keeps face
identity distinct from regional graph reachability. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_faceContinues_iff_occurrenceFace
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
    (left right : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceContinues left right = true) ↔
      dartOrbitFace embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt
            realization hcubic hrotation htwoSided hunique offset hnext left).1 =
        dartOrbitFace embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseSuccessorFaceOccurrenceAt
            realization hcubic hrotation htwoSided hunique offset hnext right).1 := by
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  change ((data.regionalProfile color hcolor).faceContinues left right = true) ↔ _
  rw [data.regionalProfile_faceContinues_eq_true_iff]
  rw [dartOrbitFace_successorFaceOccurrenceAt realization hcubic hrotation
    htwoSided hunique offset hnext left]
  rw [dartOrbitFace_successorFaceOccurrenceAt realization hcubic hrotation
    htwoSided hunique offset hnext right]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
