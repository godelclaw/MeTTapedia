import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSkeleton
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections

/-!
# L1: local face-intersection uniqueness through a literal opening

The closed minimal-counterexample geometry gives at most one shared interior
edge for two distinct ambient faces.  The source opens a region before using
its corridor, so the corresponding local statement must be transported to
the opened carrier rather than assumed there globally.

This file proves the exact local transport.  If two ambient faces are fully
retained, every shared edge of their opened images has a unique ambient
preimage.  Hence an ambient `card <= 1` bound remains true after opening.

The theorem is deliberately about one supplied pair of fully retained faces.
It does not assert pairwise uniqueness for arbitrary faces of an annulus;
boundary-spliced faces are outside its hypotheses.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionFaceIntersectionTransport

open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24HexCorridorSkeleton
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- One shared edge of two fully retained open faces comes from a shared
ambient edge.  The returned point on the left face remembers the exact opened
edge, so ambient uniqueness can be reflected back to the opened carrier. -/
theorem exists_ambient_shared_edge_of_mem_open_sharedInteriorEdges
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot)
    {edge : (rewiredDartSystem RS keep outer).Edge}
    (hedge : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))
      (openFaceOrbit RS keep outer leftRoot hleft)
      (openFaceOrbit RS keep outer rightRoot hright)) :
    ∃ left : {point // RS.phi.SameCycle leftRoot point},
      ∃ right : {point // RS.phi.SameCycle rightRoot point},
        RS.edgeOf left.1 = RS.edgeOf right.1 /\
        RS.edgeOf left.1 ∈ sharedInteriorEdges
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          (dartOrbitFace RS leftRoot)
          (dartOrbitFace RS rightRoot) /\
        edge = openFaceEdge RS keep outer leftRoot hleft left := by
  rcases (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).1
      hedge with ⟨_, hedgeLeft, hedgeRight⟩
  rw [mem_orbitFaceBoundary_iff] at hedgeLeft hedgeRight
  rcases hedgeLeft with ⟨leftDart, hleftDartFace, hleftEdge⟩
  rcases hedgeRight with ⟨rightDart, hrightDartFace, hrightEdge⟩
  have hleftCycle :
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep leftRoot hleft) leftDart := by
    rw [mem_orbitFaceDarts_iff] at hleftDartFace
    exact (Quotient.exact hleftDartFace).symm
  have hrightCycle :
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep rightRoot hright) rightDart := by
    rw [mem_orbitFaceDarts_iff] at hrightDartFace
    exact (Quotient.exact hrightDartFace).symm
  rcases (openFaceCycleEquiv RS keep outer leftRoot hleft).surjective
      ⟨leftDart, hleftCycle⟩ with ⟨left, hleftImage⟩
  rcases (openFaceCycleEquiv RS keep outer rightRoot hright).surjective
      ⟨rightDart, hrightCycle⟩ with ⟨right, hrightImage⟩
  have hleftImageDart :
      openFaceDart RS keep leftRoot hleft left = leftDart :=
    congrArg Subtype.val hleftImage
  have hrightImageDart :
      openFaceDart RS keep rightRoot hright right = rightDart :=
    congrArg Subtype.val hrightImage
  have hopenEdges :
      openFaceEdge RS keep outer leftRoot hleft left =
        openFaceEdge RS keep outer rightRoot hright right := by
    calc
      openFaceEdge RS keep outer leftRoot hleft left = edge := by
        unfold openFaceEdge
        rw [hleftImageDart]
        exact hleftEdge
      _ = openFaceEdge RS keep outer rightRoot hright right := by
        unfold openFaceEdge
        rw [hrightImageDart]
        exact hrightEdge.symm
  have hambientEdges : RS.edgeOf left.1 = RS.edgeOf right.1 :=
    ambient_edge_eq_of_openFaceEdge_eq_two_faces RS keep outer
      leftRoot rightRoot hleft hright left right hopenEdges
  have hleftBoundary : RS.edgeOf left.1 ∈
      orbitFaceBoundary RS (dartOrbitFace RS leftRoot) := by
    rw [mem_orbitFaceBoundary_iff]
    exact ⟨left.1, by
      rw [mem_orbitFaceDarts_iff]
      exact Quotient.sound left.2.symm, rfl⟩
  have hrightBoundary : RS.edgeOf left.1 ∈
      orbitFaceBoundary RS (dartOrbitFace RS rightRoot) := by
    rw [mem_orbitFaceBoundary_iff]
    exact ⟨right.1, by
      rw [mem_orbitFaceDarts_iff]
      exact Quotient.sound right.2.symm, hambientEdges.symm⟩
  have hinterior : RS.edgeOf left.1 ∈ interiorEdgeSupport
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) := by
    exact (mem_interiorEdgeSupport_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
        ⟨Finset.mem_biUnion.2
            ⟨dartOrbitFace RS leftRoot, Finset.mem_univ _, hleftBoundary⟩,
          totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
            (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))
            (orbitFace_incidence_le_two RS)
            (Finset.mem_univ _) (Finset.mem_univ _) hne
            hleftBoundary hrightBoundary⟩
  refine ⟨left, right, hambientEdges, ?_, ?_⟩
  · exact (mem_sharedInteriorEdges_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
        ⟨hinterior, hleftBoundary, hrightBoundary⟩
  · calc
      edge = (rotationSystem RS keep outer).edgeOf leftDart := hleftEdge.symm
      _ = openFaceEdge RS keep outer leftRoot hleft left := by
        unfold openFaceEdge
        rw [hleftImageDart]
        rfl

/-- **L1 local opening transport.** Two distinct fully retained ambient faces
which share at most one interior edge still share at most one interior edge
after the literal opening. -/
theorem openFaceOrbit_sharedInteriorEdges_card_le_one
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot)
    (hcard : (sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (dartOrbitFace RS leftRoot)
      (dartOrbitFace RS rightRoot)).card ≤ 1) :
    (sharedInteriorEdges
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))
      (openFaceOrbit RS keep outer leftRoot hleft)
      (openFaceOrbit RS keep outer rightRoot hright)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro first hfirst second hsecond
  rcases exists_ambient_shared_edge_of_mem_open_sharedInteriorEdges
      RS keep outer leftRoot rightRoot hleft hright hne hfirst with
    ⟨firstLeft, firstRight, _firstAmbientEq, firstAmbientMem, firstOpen⟩
  rcases exists_ambient_shared_edge_of_mem_open_sharedInteriorEdges
      RS keep outer leftRoot rightRoot hleft hright hne hsecond with
    ⟨secondLeft, secondRight, _secondAmbientEq, secondAmbientMem, secondOpen⟩
  have hambient : RS.edgeOf firstLeft.1 = RS.edgeOf secondLeft.1 :=
    (Finset.card_le_one.mp hcard) _ firstAmbientMem _ secondAmbientMem
  calc
    first = openFaceEdge RS keep outer leftRoot hleft firstLeft := firstOpen
    _ = openFaceEdge RS keep outer leftRoot hleft secondLeft :=
      openFaceEdge_eq_of_ambient_edge_eq RS keep outer leftRoot hleft
        firstLeft secondLeft hambient
    _ = second := secondOpen.symm

/-- Pairwise ambient uniqueness supplies the local hypothesis of the opening
transport without promoting it to a global assertion about the open annulus. -/
theorem openFaceOrbit_sharedInteriorEdges_card_le_one_of_pairwiseUnique
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot) :
    (sharedInteriorEdges
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))
      (openFaceOrbit RS keep outer leftRoot hleft)
      (openFaceOrbit RS keep outer rightRoot hright)).card ≤ 1 := by
  apply openFaceOrbit_sharedInteriorEdges_card_le_one RS keep outer
    leftRoot rightRoot hleft hright hne
  exact hunique _ (Finset.mem_univ _) _ (Finset.mem_univ _) hne

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **L1 source specialization.** Closed vertex-minimal face-intersection
uniqueness survives on any two fully retained face images of its literal
opening.  Minimality is consumed on the ambient closed carrier, never asserted
for the stub-bearing opened graph. -/
theorem openMinimalFaceOrbits_sharedInteriorEdges_card_le_one
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    (outer : Dart graphData.toRotationSystem keep)
    (leftRoot rightRoot : graphData.toRotationSystem.D)
    (hleft : FaceFullyRetained graphData.toRotationSystem keep leftRoot)
    (hright : FaceFullyRetained graphData.toRotationSystem keep rightRoot)
    (hne : dartOrbitFace graphData.toRotationSystem leftRoot ≠
      dartOrbitFace graphData.toRotationSystem rightRoot) :
    (sharedInteriorEdges
      (orbitFaceBoundary
        (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset (OrbitFace
        (rotationSystem graphData.toRotationSystem keep outer)))
      (openFaceOrbit graphData.toRotationSystem keep outer leftRoot hleft)
      (openFaceOrbit graphData.toRotationSystem keep outer rightRoot hright)).card ≤ 1 := by
  exact openFaceOrbit_sharedInteriorEdges_card_le_one_of_pairwiseUnique
    graphData.toRotationSystem keep outer leftRoot rightRoot hleft hright
      (pairwiseUniqueSharedInteriorEdges graphData minimal) hne

/-- **L1 corridor-facing specialization.** Distinct faces of a closed
vertex-minimal corridor still share at most one interior edge after the whole
corridor is transported through a literal opening, provided every corridor
face is fully retained.

The full-retention premise is intentionally visible: this theorem connects
the generic opening transport to the corridor consumer, but it does not select
the source corridor or prove that it avoids the deleted collar. -/
theorem openMinimalCorridorFaces_sharedInteriorEdges_card_le_one
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem corridorLength)
    (keep : V → Prop)
    (outer : Dart graphData.toRotationSystem keep)
    (hretained : ∀ offset,
      FaceFullyRetained graphData.toRotationSystem keep
        (Quotient.out (corridor.faceAt offset).1))
    {left right : Fin corridorLength}
    (hne : left ≠ right) :
    (sharedInteriorEdges
      (orbitFaceBoundary
        (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset (OrbitFace
        (rotationSystem graphData.toRotationSystem keep outer)))
      (openFaceOrbit graphData.toRotationSystem keep outer
        (Quotient.out (corridor.faceAt left).1) (hretained left))
      (openFaceOrbit graphData.toRotationSystem keep outer
        (Quotient.out (corridor.faceAt right).1) (hretained right))).card ≤ 1 := by
  have hfaceNe :
      (corridor.faceAt left).1 ≠ (corridor.faceAt right).1 := by
    intro hfaces
    exact corridor.faceAt_ne hne (Subtype.ext hfaces)
  have hambientNe :
      dartOrbitFace graphData.toRotationSystem
          (Quotient.out (corridor.faceAt left).1) ≠
        dartOrbitFace graphData.toRotationSystem
          (Quotient.out (corridor.faceAt right).1) := by
    simpa only [dartOrbitFace, Quotient.out_eq] using hfaceNe
  exact openMinimalFaceOrbits_sharedInteriorEdges_card_le_one
    graphData minimal keep outer
    (Quotient.out (corridor.faceAt left).1)
    (Quotient.out (corridor.faceAt right).1)
    (hretained left) (hretained right) hambientNe

end

end GoertzelV24OpenRegionFaceIntersectionTransport

end Mettapedia.GraphTheory.FourColor
