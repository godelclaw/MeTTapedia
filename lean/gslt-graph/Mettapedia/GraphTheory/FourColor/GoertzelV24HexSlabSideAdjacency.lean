import Mettapedia.GraphTheory.FourColor.GoertzelV24OrientedHexSlab

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexSlabSideAdjacency

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Standard side slots of a hexagon after deleting its two rung positions. -/
def hexSidePositions (incoming outgoing : Fin 6) : Finset (Fin 6) :=
  Finset.univ \ {incoming, outgoing}

/-- Directed cyclic steps whose two endpoints both survive as side slots. -/
def hexSideForwardSteps (incoming outgoing : Fin 6) : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter fun step =>
    step.1 ∈ hexSidePositions incoming outgoing ∧
    step.2 ∈ hexSidePositions incoming outgoing ∧
    step.2.val ≡ step.1.val + 1 [MOD 6]

/-- Every induced oriented slab has exactly two directed side steps. This is
the finite local compatibility table common to all three oriented types. -/
theorem card_hexSideForwardSteps_eq_two
    (incoming outgoing : Fin 6) (hne : incoming ≠ outgoing)
    (hnonadjacent : hexRungType incoming outgoing ≠ HexRungType.adjacent) :
    (hexSideForwardSteps incoming outgoing).card = 2 := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSideForwardSteps, hexSidePositions, hexRungType,
      hexCyclicDistance, hexForwardDistance, Nat.ModEq] at * <;>
    decide

/-- A successor congruence on bounded positions of one facial cycle is an
actual application of the face permutation, including wraparound. -/
theorem faceCycleDart_successor_of_modEq
    (RS : RotationSystem V E) (root : RS.D)
    (hcard : (RS.faceOrbit root).card = 6)
    (left right : Fin (RS.faceOrbit root).card)
    (hsuccessor : right.val ≡ left.val + 1 [MOD 6]) :
    faceCycleDart RS root right = RS.phi (faceCycleDart RS root left) := by
  have hmod : right.val ≡ left.val + 1
      [MOD (RS.faceOrbit root).card] := by
    simpa only [hcard] using hsuccessor
  have hpowers := ((faceOrbit_isCycleOn RS root).pow_apply_eq_pow_apply
    (RS.mem_faceOrbit_self root)).2 hmod
  simpa only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
    Function.comp_apply] using hpowers

/-- The selected face across a cyclic side position is exactly the quotient
face of the opposite dart at that position. -/
theorem placementSideNeighbor_eq_alphaFace
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    placementSideNeighbor clean htwoSided hunique placement position =
      ⟨dartOrbitFace RS
        (RS.alpha (faceCycleDart RS placement.root position.1)),
        Finset.mem_univ _⟩ := by
  let corridor := clean.toOrbitHexCorridorSkeleton
  let center := corridor.faceAt interior.center
  let side := placementSideEdge htwoSided placement position
  have hsideBoundary : side.1 ∈ orbitFaceBoundary RS center.1 :=
    ((mem_internalSideEdges_iff corridor hunique interior side.1).1 side.2).1
  let witness := orbitFaceAcrossEdgeWitness RS htwoSided center side.1
    hsideBoundary
  have hedgeAcross : RS.edgeOf (faceCycleDart RS placement.root position.1) ∈
      orbitFaceBoundary RS witness.across.1 := by
    change side.1 ∈ orbitFaceBoundary RS witness.across.1
    exact witness.edge_mem_across
  have hdartFace : dartOrbitFace RS
      (faceCycleDart RS placement.root position.1) = center.1 := by
    calc
      dartOrbitFace RS (faceCycleDart RS placement.root position.1) =
          dartOrbitFace RS placement.root :=
        dartOrbitFace_faceCycleDart RS placement.root position.1
      _ = center.1 := placement.root_face
  have hother : dartOrbitFace RS (faceCycleDart RS placement.root position.1) ≠
      witness.across.1 := by
    rw [hdartFace]
    exact fun heq => witness.face_ne_across (Subtype.ext heq)
  apply Subtype.ext
  change witness.across.1 =
    dartOrbitFace RS (RS.alpha (faceCycleDart RS placement.root position.1))
  exact (dartOrbitFace_alpha_eq_of_mem_other_face RS htwoSided
    (faceCycleDart RS placement.root position.1) witness.across.1
      hedgeAcross hother).symm

/-- Consecutive retained cyclic side slots map to adjacent external faces.
The witnessing primal edge is the third edge at their common cubic corner. -/
theorem placementSideNeighbors_adjacent_of_forwardStep
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (left right : {position // position ∈ placementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (placementSideNeighbor clean htwoSided hunique placement left)
        (placementSideNeighbor clean htwoSided hunique placement right) := by
  have hdarts := faceCycleDart_successor_of_modEq RS placement.root
    placement.orbit_card left.1 right.1 hsuccessor
  have hpositionsNe : left ≠ right := by
    intro heq
    have hvalEq : left.1.val = right.1.val :=
      congrArg (fun position => position.1.val) heq
    have hselfSuccessor : left.1.val ≡ left.1.val + 1 [MOD 6] := by
      simpa only [hvalEq] using hsuccessor
    have hleftBound : left.1.val < 6 := by
      simpa only [placement.orbit_card] using left.1.isLt
    interval_cases hleft : left.1.val <;>
      norm_num [Nat.ModEq, hleft] at hselfSuccessor
  have hfacesNe : dartOrbitFace RS
      (RS.alpha (faceCycleDart RS placement.root left.1)) ≠
      dartOrbitFace RS
        (RS.alpha (RS.phi (faceCycleDart RS placement.root left.1))) := by
    intro heq
    apply hpositionsNe
    apply placementSideNeighbor_injective clean htwoSided hunique placement
    rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement left,
      placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement right]
    apply Subtype.ext
    simpa only [hdarts] using heq
  have hadj := oppositeFaces_adjacent_at_cubic_corner RS hcubic hrotation
    (faceCycleDart RS placement.root left.1) hfacesNe
  rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement left,
    placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement right]
  convert hadj using 1
  apply Subtype.ext
  simp only [hdarts]

end

end GoertzelV24HexSlabSideAdjacency

end Mettapedia.GraphTheory.FourColor
