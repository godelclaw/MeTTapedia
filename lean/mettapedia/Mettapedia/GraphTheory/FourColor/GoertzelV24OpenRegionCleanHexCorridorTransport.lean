import Mettapedia.GraphTheory.FourColor.GoertzelV24CleanHexCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionHexCorridorTransport

/-!
# Boundary-clean hex corridors survive a literal opening

Transporting only the selected corridor faces is not enough for L1.  An open
face adjacent to a retained corridor face could otherwise be a boundary-cut
fragment of an ambient face.  This file proves the one-ring version: if every
ambient neighbour of every selected corridor face is also fully retained,
then every open neighbour is exactly the image of one such ambient neighbour.
Consequently a closed clean hex corridor constructs an open clean hex
corridor.

The one-ring retention premise is deliberately visible.  It is the precise
closed-to-open form of the source's boundary-clean Cell-3 selection, not an
automatic consequence of retaining the centre faces alone.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionCleanHexCorridorTransport

open GoertzelV24CleanHexCorridor
open GoertzelV24CubicFaceVertexSeparation
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionHexCorridorTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- **L1 (one-sided neighbour pullback).** Every open neighbour of a fully
retained face is the exact open image of an ambient neighbour, provided that
the ambient neighbour across each boundary edge is itself fully retained.

The ambient neighbour is recovered from the opposite dart of an actual shared
open edge.  Equality with the caller's open neighbour then follows from the
two-face incidence bound, not from a choice of matching face cardinality. -/
theorem exists_retained_ambient_neighbor_of_openFaceOrbit_adj
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (keep : V → Prop) (outer : Dart RS keep)
    (root : RS.D) (hroot : FaceFullyRetained RS keep root)
    (hneighborRetained : ∀ neighborRoot : RS.D,
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj
          ⟨dartOrbitFace RS root, Finset.mem_univ _⟩
          ⟨dartOrbitFace RS neighborRoot, Finset.mem_univ _⟩ →
        FaceFullyRetained RS keep neighborRoot)
    (neighbor : AmbientFace
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer))))
    (hopen : (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset
        (OrbitFace (rotationSystem RS keep outer)))).Adj
          ⟨openFaceOrbit RS keep outer root hroot, Finset.mem_univ _⟩
          neighbor) :
    ∃ neighborRoot : RS.D,
      ∃ hneighbor : FaceFullyRetained RS keep neighborRoot,
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Adj
            ⟨dartOrbitFace RS root, Finset.mem_univ _⟩
            ⟨dartOrbitFace RS neighborRoot, Finset.mem_univ _⟩ ∧
          neighbor.1 =
            openFaceOrbit RS keep outer neighborRoot hneighbor := by
  let openRS := rotationSystem RS keep outer
  let openRoot := openFaceRoot RS keep root hroot
  let openCenter := openFaceOrbit RS keep outer root hroot
  rcases (interiorDualGraph_adj_iff
      (orbitFaceBoundary openRS)
      (Finset.univ : Finset (OrbitFace openRS))).1 hopen with
    ⟨hcenterNeighbor, edge, _hedgeInterior, hedgeCenter, hedgeNeighbor⟩
  rcases (mem_orbitFaceBoundary_iff openRS openCenter edge).1
      hedgeCenter with ⟨centerDart, hcenterDartFace, hcenterEdge⟩
  have hcenterOrbit : centerDart ∈ openRS.faceOrbit openRoot := by
    have hopenFace : openCenter = dartOrbitFace openRS openRoot := rfl
    rw [hopenFace] at hcenterDartFace
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit openRS openRoot]
    exact hcenterDartFace
  let target : {point // openRS.phi.SameCycle openRoot point} :=
    ⟨centerDart, (openRS.mem_faceOrbit).1 hcenterOrbit⟩
  rcases (openFaceCycleEquiv RS keep outer root hroot).surjective target with
    ⟨source, hsource⟩
  have hsourceDart : openFaceDart RS keep root hroot source = centerDart :=
    congrArg Subtype.val hsource
  have hsourceFace : dartOrbitFace RS source.1 = dartOrbitFace RS root := by
    apply Quotient.sound
    exact source.2.symm
  let neighborRoot : RS.D := RS.alpha source.1
  have hambientNe : dartOrbitFace RS root ≠
      dartOrbitFace RS neighborRoot := by
    intro heq
    apply htwoSided source.1
    exact hsourceFace.trans heq
  have hambient : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨dartOrbitFace RS root, Finset.mem_univ _⟩
        ⟨dartOrbitFace RS neighborRoot, Finset.mem_univ _⟩ := by
    apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hambientNe
    · rw [← hsourceFace]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS source.1
    · change RS.edgeOf source.1 ∈ orbitFaceBoundary RS
        (dartOrbitFace RS (RS.alpha source.1))
      rw [← RS.edge_alpha source.1]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
        (RS.alpha source.1)
  let hneighbor : FaceFullyRetained RS keep neighborRoot :=
    hneighborRetained neighborRoot hambient
  let neighborPoint : {point // RS.phi.SameCycle neighborRoot point} :=
    ⟨neighborRoot, Equiv.Perm.SameCycle.refl RS.phi neighborRoot⟩
  have hopenEdges : openFaceEdge RS keep outer root hroot source =
      openFaceEdge RS keep outer neighborRoot hneighbor neighborPoint := by
    apply openFaceEdge_eq_of_ambient_edge_eq_two_faces
    simpa [neighborRoot, neighborPoint] using (RS.edge_alpha source.1).symm
  have hedgeCenterValue :
      openFaceEdge RS keep outer root hroot source = edge := by
    change openRS.edgeOf (openFaceDart RS keep root hroot source) = edge
    rw [hsourceDart]
    exact hcenterEdge
  have hedgeRight : edge ∈ orbitFaceBoundary openRS
      (openFaceOrbit RS keep outer neighborRoot hneighbor) := by
    rw [← hedgeCenterValue, hopenEdges]
    rw [mem_orbitFaceBoundary_iff]
    refine ⟨openFaceDart RS keep neighborRoot hneighbor neighborPoint, ?_, rfl⟩
    rw [mem_orbitFaceDarts_iff]
    apply Quotient.sound
    exact (openFaceCycleMap RS keep outer neighborRoot hneighbor
      neighborPoint).2.symm
  have hrightNeCenter :
      openFaceOrbit RS keep outer neighborRoot hneighbor ≠ openCenter := by
    exact openFaceOrbit_ne_of_ambient_ne RS keep outer neighborRoot root
      hneighbor hroot hambientNe.symm
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary openRS)
      (Finset.univ : Finset (OrbitFace openRS))
      (orbitFace_incidence_le_two openRS)
      (Finset.mem_univ openCenter) neighbor.2
      (Finset.mem_univ
        (openFaceOrbit RS keep outer neighborRoot hneighbor))
      hcenterNeighbor
      hedgeCenter hedgeNeighbor hedgeRight
  refine ⟨neighborRoot, hneighbor, hambient, ?_⟩
  rcases hcases with hrightCenter | hrightNeighbor
  · exact False.elim (hrightNeCenter hrightCenter)
  · exact hrightNeighbor.symm

/-- **L1 (boundary-clean corridor transport).** A clean closed corridor
whose complete radius-one face neighbourhood survives an opening constructs
a clean open corridor. -/
noncomputable def openCleanOrbitHexCorridorSkeleton
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (keep : V → Prop) (outer : Dart RS keep)
    (hretained : ∀ offset,
      FaceFullyRetained RS keep
        (orbitFaceRoot RS
          (clean.toOrbitHexCorridorSkeleton.faceAt offset).1))
    (hneighborRetained : ∀ offset,
      ∀ neighbor : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Adj
            (clean.toOrbitHexCorridorSkeleton.faceAt offset) neighbor →
          FaceFullyRetained RS keep (orbitFaceRoot RS neighbor.1)) :
    CleanOrbitHexCorridorSkeleton (rotationSystem RS keep outer)
      corridorLength := {
  toOrbitHexCorridorSkeleton :=
    openOrbitHexCorridorSkeleton RS htwoSided
      clean.toOrbitHexCorridorSkeleton keep outer hretained
  neighbor_hexagonal := by
    intro offset neighbor hopen
    let centerRoot := orbitFaceRoot RS
      (clean.toOrbitHexCorridorSkeleton.faceAt offset).1
    have hopen' : (interiorDualGraph
        (orbitFaceBoundary (rotationSystem RS keep outer))
        (Finset.univ : Finset
          (OrbitFace (rotationSystem RS keep outer)))).Adj
          ⟨openFaceOrbit RS keep outer centerRoot (hretained offset),
            Finset.mem_univ _⟩ neighbor := by
      simpa [openOrbitHexCorridorSkeleton, centerRoot] using hopen
    rcases exists_retained_ambient_neighbor_of_openFaceOrbit_adj
        RS htwoSided keep outer centerRoot (hretained offset)
        (fun neighborRoot hadj => by
          have hrep := hneighborRetained offset
            ⟨dartOrbitFace RS neighborRoot, Finset.mem_univ _⟩
            (by simpa [centerRoot] using hadj)
          intro point hpoint
          apply hrep point
          have hsame : RS.phi.SameCycle
              (orbitFaceRoot RS (dartOrbitFace RS neighborRoot))
              neighborRoot := by
            have heq : dartOrbitFace RS
                (orbitFaceRoot RS (dartOrbitFace RS neighborRoot)) =
                dartOrbitFace RS neighborRoot := by simp
            have hrelation := Quotient.exact heq
            change RS.phi.SameCycle
              (orbitFaceRoot RS (dartOrbitFace RS neighborRoot))
              neighborRoot at hrelation
            exact hrelation
          exact hsame.trans hpoint)
        neighbor hopen' with
      ⟨neighborRoot, hneighbor, hambient, hneighborEq⟩
    rw [hneighborEq,
      openFaceOrbit_boundary_card_eq_ambient RS htwoSided keep outer
        neighborRoot hneighbor]
    apply clean.neighbor_hexagonal offset
      ⟨dartOrbitFace RS neighborRoot, Finset.mem_univ _⟩
    simpa [centerRoot] using hambient
}

/-- The complete radius-one neighbourhood of a corridor avoids a displayed
ambient face.  This is the closed-map form of a boundary-clean corridor
relative to a cap deletion. -/
def CorridorOneRingAvoidsFace
    (RS : RotationSystem V E) {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (cap : OrbitFace RS) : Prop :=
  ∀ offset,
    ∀ face : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
      (face = corridor.faceAt offset ∨
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Adj
            (corridor.faceAt offset) face) →
        face.1 ≠ cap ∧
          ¬ (interiorDualGraph (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))).Adj
              face ⟨cap, Finset.mem_univ _⟩

/-- **L1 (boundary-clean cap opening).** If a clean closed corridor's whole
radius-one neighbourhood avoids a cap face, deleting the cap vertices
constructs a clean corridor in the literal opening. -/
noncomputable def openCleanOrbitHexCorridorSkeleton_compl_cap
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (capRoot : RS.D)
    (outer : Dart RS (fun vertex =>
      vertex ∉ orbitFaceVertices RS (dartOrbitFace RS capRoot)))
    (havoid : CorridorOneRingAvoidsFace RS
      clean.toOrbitHexCorridorSkeleton (dartOrbitFace RS capRoot)) :
    CleanOrbitHexCorridorSkeleton
      (rotationSystem RS
        (fun vertex => vertex ∉
          orbitFaceVertices RS (dartOrbitFace RS capRoot)) outer)
      corridorLength :=
  openCleanOrbitHexCorridorSkeleton RS htwoSided clean
    (fun vertex => vertex ∉
      orbitFaceVertices RS (dartOrbitFace RS capRoot)) outer
    (fun offset =>
      faceFullyRetained_compl_orbitFaceVertices_of_not_adj
        RS hcubic hrotation htwoSided capRoot
        (orbitFaceRoot RS
          (clean.toOrbitHexCorridorSkeleton.faceAt offset).1)
        (by
          simpa using (havoid offset
            (clean.toOrbitHexCorridorSkeleton.faceAt offset)
            (Or.inl rfl)).1)
        (by
          simpa using (havoid offset
            (clean.toOrbitHexCorridorSkeleton.faceAt offset)
            (Or.inl rfl)).2))
    (fun offset neighbor hadj =>
      faceFullyRetained_compl_orbitFaceVertices_of_not_adj
        RS hcubic hrotation htwoSided capRoot
        (orbitFaceRoot RS neighbor.1)
        (by simpa using (havoid offset neighbor (Or.inr hadj)).1)
        (by simpa using (havoid offset neighbor (Or.inr hadj)).2))

end

end GoertzelV24OpenRegionCleanHexCorridorTransport

end Mettapedia.GraphTheory.FourColor
