import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestrictionComposition

/-!
# Forgetting the local rail terminals of an aligned two-tile slab

The aligned two-tile boundary has two transverse input crossings, two
transverse output crossings, and two lateral rail crossings.  The rails are
terminal observations of this one slab, not persistent coordinates to be
identified between different slabs.  This file proves that forgetting them
recovers the already constructed crossing-only first and second restrictions
of the same six-edge regional profile.

These are local projection theorems.  They do not identify either restricted
profile with a cumulative corridor-prefix profile and do not supply the
semantic lifting direction of the splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TerminalProfileRestrictionComposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileTerminalForgettingEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Selecting the first moving block after the `4+2` partition is literally
the first transverse index of the ordered six-edge boundary. -/
@[simp]
theorem sourceTwoTileAlignedTransverseProfileIndexAt_firstTerminalCrossing
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
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic hrotation
        htwoSided hunique offset
        (sourceTwoTileAlignedFirstTerminalCrossingIndex step) =
      sourceTwoTileAlignedFirstProfileIndexAt realization hcubic hrotation
        htwoSided hunique offset step := by
  simp [sourceTwoTileAlignedTransverseProfileIndexAt,
    sourceTwoTileAlignedFirstTerminalCrossingIndex]

/-- Selecting the second moving block after the `4+2` partition is literally
the following transverse index of the ordered six-edge boundary. -/
@[simp]
theorem sourceTwoTileAlignedTransverseProfileIndexAt_secondTerminalCrossing
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
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic hrotation
        htwoSided hunique offset
        (sourceTwoTileAlignedSecondTerminalCrossingIndex step) =
      sourceTwoTileAlignedSecondProfileIndexAt realization hcubic hrotation
        htwoSided hunique offset step := by
  simp [sourceTwoTileAlignedTransverseProfileIndexAt,
    sourceTwoTileAlignedSecondTerminalCrossingIndex]

/-- The incoming terminal-aware raw cut is terminal augmentation of the
crossing-only incoming restriction. -/
theorem sourceTwoTileAlignedFirstTerminalProfileDataAt_eq_withTerminalEdges
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
    (offset : Fin (blockLength - 4)) :
    sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset =
      withTerminalEdges
        (sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
          hrotation htwoSided hunique offset)
        (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
          htwoSided hunique offset).terminalEdge := by
  unfold sourceTwoTileAlignedFirstTerminalProfileDataAt
  unfold sourceTwoTileAlignedFirstRestrictedProfileDataAt
  unfold sourceTwoTileAlignedTerminalProfileDataAt
  rw [restrictCrossings_partitionCrossings_eq_withTerminalEdges]
  congr 2
  funext step
  exact sourceTwoTileAlignedTransverseProfileIndexAt_firstTerminalCrossing
    realization hcubic hrotation htwoSided hunique offset step

/-- The outgoing terminal-aware raw cut is terminal augmentation of the
crossing-only outgoing restriction. -/
theorem sourceTwoTileAlignedSecondTerminalProfileDataAt_eq_withTerminalEdges
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
    (offset : Fin (blockLength - 4)) :
    sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset =
      withTerminalEdges
        (sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
          hrotation htwoSided hunique offset)
        (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
          htwoSided hunique offset).terminalEdge := by
  unfold sourceTwoTileAlignedSecondTerminalProfileDataAt
  unfold sourceTwoTileAlignedSecondRestrictedProfileDataAt
  unfold sourceTwoTileAlignedTerminalProfileDataAt
  rw [restrictCrossings_partitionCrossings_eq_withTerminalEdges]
  congr 2
  funext step
  exact sourceTwoTileAlignedTransverseProfileIndexAt_secondTerminalCrossing
    realization hcubic hrotation htwoSided hunique offset step

/-- Forgetting the two rail observations from an incoming graph-derived
regional profile recovers its crossing-only presentation exactly. -/
@[simp]
theorem forgetTerminals_sourceTwoTileAlignedFirstTerminalRegionalProfile
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hterminal : ∀ crossing,
      color ((sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0)
    (hcrossing : ∀ crossing,
      color ((sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    forgetTerminals
        ((sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hterminal) =
      (sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color hcrossing := by
  let cut := sourceTwoTileAlignedFirstRestrictedProfileDataAt realization
    hcubic hrotation htwoSided hunique offset
  let terminalEdge :=
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).terminalEdge
  have hdata :=
    sourceTwoTileAlignedFirstTerminalProfileDataAt_eq_withTerminalEdges
      realization hcubic hrotation htwoSided hunique offset
  have haugmented : ∀ crossing,
      color ((withTerminalEdges cut terminalEdge).crossingEdge crossing) ≠ 0 := by
    simpa [cut] using hcrossing
  have hprofile := graphCorridorCutData_regionalProfile_eq_of_eq hdata color
    hterminal haugmented
  rw [hprofile]
  simp [cut]

/-- The analogous local projection for the outgoing source transversal. -/
@[simp]
theorem forgetTerminals_sourceTwoTileAlignedSecondTerminalRegionalProfile
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hterminal : ∀ crossing,
      color ((sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0)
    (hcrossing : ∀ crossing,
      color ((sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    forgetTerminals
        ((sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hterminal) =
      (sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color hcrossing := by
  let cut := sourceTwoTileAlignedSecondRestrictedProfileDataAt realization
    hcubic hrotation htwoSided hunique offset
  let terminalEdge :=
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).terminalEdge
  have hdata :=
    sourceTwoTileAlignedSecondTerminalProfileDataAt_eq_withTerminalEdges
      realization hcubic hrotation htwoSided hunique offset
  have haugmented : ∀ crossing,
      color ((withTerminalEdges cut terminalEdge).crossingEdge crossing) ≠ 0 := by
    simpa [cut] using hcrossing
  have hprofile := graphCorridorCutData_regionalProfile_eq_of_eq hdata color
    hterminal haugmented
  rw [hprofile]
  simp [cut]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
