import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InducedHexCorridorTypes

open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A genuine cyclic vertex rotation is a single cycle on each stored dart
fiber. -/
theorem rho_isCycleOn_dartsAt (RS : RotationSystem V E)
    (hrotation : VertexRotationCyclic RS) (vertex : V) :
    RS.rho.IsCycleOn (RS.dartsAt vertex) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro dart hdart
    have hdart' : RS.vertOf dart = vertex := by
      simpa [RotationSystem.dartsAt] using hdart
    simpa [RotationSystem.dartsAt] using (RS.vert_rho dart).trans hdart'
  · intro left _hleft right _hright heq
    exact RS.rho.injective heq
  · intro dart hdart
    refine ⟨RS.rho.symm dart, ?_, by simp⟩
    have hdart' : RS.vertOf dart = vertex := by
      simpa [RotationSystem.dartsAt] using hdart
    have hrho := RS.vert_rho (RS.rho.symm dart)
    simp only [Equiv.apply_symm_apply] at hrho
    simpa [RotationSystem.dartsAt] using hrho.symm.trans hdart'
  · intro left hleft right hright
    have hleft' : RS.vertOf left = vertex := by
      simpa [RotationSystem.dartsAt] using hleft
    have hright' : RS.vertOf right = vertex := by
      simpa [RotationSystem.dartsAt] using hright
    exact hrotation left right (hleft'.trans hright'.symm)

/-- Cubicity makes the cyclic vertex rotation have period three on every
dart. -/
theorem rho_cube_apply_of_isCubic (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) (dart : RS.D) :
    RS.rho (RS.rho (RS.rho dart)) = dart := by
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt]
  have hpow := (rho_isCycleOn_dartsAt RS hrotation (RS.vertOf dart)).pow_card_apply hdart
  rw [hcubic (RS.vertOf dart)] at hpow
  simpa [pow_succ] using hpow

/-- If another quotient face contains a dart's edge, two-sidedness identifies
it with the face on the opposite dart. -/
theorem dartOrbitFace_alpha_eq_of_mem_other_face
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) (face : OrbitFace RS)
    (hedge : RS.edgeOf dart ∈ orbitFaceBoundary RS face)
    (hne : dartOrbitFace RS dart ≠ face) :
    dartOrbitFace RS (RS.alpha dart) = face := by
  have hmem : face ∈
      (Finset.univ.filter fun candidate : OrbitFace RS =>
        RS.edgeOf dart ∈ orbitFaceBoundary RS candidate) := by
    simp [hedge]
  rw [orbitFace_incidentFaces_eq_dartSide_pair RS htwoSided dart] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hsame | hopposite
  · exact (hne hsame.symm).elim
  · exact hopposite.symm

/-- At a cubic rotated corner, the two faces across its consecutive boundary
edges share the third edge at the corner. -/
theorem oppositeFaces_adjacent_at_cubic_corner
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (dart : RS.D)
    (hne : dartOrbitFace RS (RS.alpha dart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi dart))) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨dartOrbitFace RS (RS.alpha dart), Finset.mem_univ _⟩
        ⟨dartOrbitFace RS (RS.alpha (RS.phi dart)), Finset.mem_univ _⟩ := by
  let third := RS.rho (RS.phi dart)
  have hthirdRho : RS.rho third = RS.alpha dart := by
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation (RS.alpha dart)
    simpa only [third, RotationSystem.phi_apply] using hcube
  have hleftFace : dartOrbitFace RS (RS.alpha third) =
      dartOrbitFace RS (RS.alpha dart) := by
    calc
      dartOrbitFace RS (RS.alpha third) = dartOrbitFace RS (RS.rho third) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS third
      _ = dartOrbitFace RS (RS.alpha dart) := congrArg (dartOrbitFace RS) hthirdRho
  have hleft : RS.edgeOf third ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart)) := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha third)
    rw [RS.edge_alpha third, hleftFace] at hraw
    exact hraw
  have hright : RS.edgeOf third ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha (RS.phi dart))) := by
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho RS (RS.phi dart)]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS third
  exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hne hleft hright

/-- A bounded power of the face permutation stays in the quotient face of
its root. -/
theorem dartOrbitFace_faceCycleDart (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    dartOrbitFace RS (faceCycleDart RS root position) = dartOrbitFace RS root := by
  apply Quotient.sound
  exact ((RS.mem_faceOrbit).1 (faceCycleDart_mem RS root position)).symm

/-- Cyclic distance one on six positions means that one position is the
successor of the other modulo six. -/
theorem modEq_succ_or_reverse_of_hexCyclicDistance_eq_one
    (left right : Fin 6) (hdistance : hexCyclicDistance left right = 1) :
    right.val ≡ left.val + 1 [MOD 6] ∨
      left.val ≡ right.val + 1 [MOD 6] := by
  fin_cases left <;> fin_cases right <;>
    norm_num [hexCyclicDistance, hexForwardDistance, Nat.ModEq] at *

/-- Adjacent positions of a six-dart face cycle are related by one actual
application of the face permutation, including the wraparound case. -/
theorem faceCycleDart_successor_or_reverse_of_hexCyclicDistance_eq_one
    (RS : RotationSystem V E) (root : RS.D)
    (hcard : (RS.faceOrbit root).card = 6)
    (left right : Fin (RS.faceOrbit root).card)
    (hdistance : hexCyclicDistance (Fin.cast hcard left) (Fin.cast hcard right) = 1) :
    faceCycleDart RS root right = RS.phi (faceCycleDart RS root left) ∨
      faceCycleDart RS root left = RS.phi (faceCycleDart RS root right) := by
  rcases modEq_succ_or_reverse_of_hexCyclicDistance_eq_one
      (Fin.cast hcard left) (Fin.cast hcard right) hdistance with
    hforward | hreverse
  · left
    have hmod : right.val ≡ left.val + 1 [MOD (RS.faceOrbit root).card] := by
      simpa only [Fin.val_cast, hcard] using hforward
    have hpowers := ((faceOrbit_isCycleOn RS root).pow_apply_eq_pow_apply
      (RS.mem_faceOrbit_self root)).2 hmod
    simpa only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply] using hpowers
  · right
    have hmod : left.val ≡ right.val + 1 [MOD (RS.faceOrbit root).card] := by
      simpa only [Fin.val_cast, hcard] using hreverse
    have hpowers := ((faceOrbit_isCycleOn RS root).pow_apply_eq_pow_apply
      (RS.mem_faceOrbit_self root)).2 hmod
    simpa only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply] using hpowers

/-- The adjacent-rung type cannot occur on an internal face of an induced
hex corridor. At the shared endpoint of adjacent rungs, cubic rotation makes
the predecessor and successor faces share the third edge, contradicting the
absence of a dual chord. -/
theorem InternalHexRungPlacement.rungType_ne_adjacent
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS) :
    placement.rungType ≠ HexRungType.adjacent := by
  intro htype
  have hdistance : hexCyclicDistance placement.incomingPosition6
      placement.outgoingPosition6 = 1 := by
    rw [← placement.rungType_distance_eq, htype]
    rfl
  let incomingDart := faceCycleDart RS placement.root placement.incomingPosition
  let outgoingDart := faceCycleDart RS placement.root placement.outgoingPosition
  have hdartCases : outgoingDart = RS.phi incomingDart ∨
      incomingDart = RS.phi outgoingDart := by
    exact faceCycleDart_successor_or_reverse_of_hexCyclicDistance_eq_one
      RS placement.root placement.orbit_card placement.incomingPosition
        placement.outgoingPosition hdistance
  have hincomingFace : dartOrbitFace RS incomingDart =
      (corridor.faceAt interior.center).1 := by
    calc
      dartOrbitFace RS incomingDart = dartOrbitFace RS placement.root := by
        exact dartOrbitFace_faceCycleDart RS placement.root placement.incomingPosition
      _ = (corridor.faceAt interior.center).1 := placement.root_face
  have houtgoingFace : dartOrbitFace RS outgoingDart =
      (corridor.faceAt interior.center).1 := by
    calc
      dartOrbitFace RS outgoingDart = dartOrbitFace RS placement.root := by
        exact dartOrbitFace_faceCycleDart RS placement.root placement.outgoingPosition
      _ = (corridor.faceAt interior.center).1 := placement.root_face
  have hincomingEdge : RS.edgeOf incomingDart =
      corridor.rungEdge hunique interior.incoming := by
    exact placement.incoming_edge
  have houtgoingEdge : RS.edgeOf outgoingDart =
      corridor.rungEdge hunique interior.outgoing := by
    exact placement.outgoing_edge
  have hpreviousCenter :
      (corridor.faceAt interior.incoming.left).1 ≠
        (corridor.faceAt interior.center).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val at hvalues
    have hpositive := interior.center_pos
    omega
  have hcenterNext :
      (corridor.faceAt interior.center).1 ≠
        (corridor.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val = interior.center.val + 1 at hvalues
    omega
  have hpreviousNext :
      (corridor.faceAt interior.incoming.left).1 ≠
        (corridor.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val + 1 at hvalues
    have hpositive := interior.center_pos
    omega
  have hincomingPrevious : RS.edgeOf incomingDart ∈
      orbitFaceBoundary RS (corridor.faceAt interior.incoming.left).1 := by
    rw [hincomingEdge]
    exact corridor.rungEdge_mem_left hunique interior.incoming
  have houtgoingNext : RS.edgeOf outgoingDart ∈
      orbitFaceBoundary RS (corridor.faceAt interior.outgoing.right).1 := by
    rw [houtgoingEdge]
    exact corridor.rungEdge_mem_right hunique interior.outgoing
  have hincomingOpposite : dartOrbitFace RS (RS.alpha incomingDart) =
      (corridor.faceAt interior.incoming.left).1 := by
    apply dartOrbitFace_alpha_eq_of_mem_other_face RS htwoSided
      incomingDart (corridor.faceAt interior.incoming.left).1 hincomingPrevious
    rw [hincomingFace]
    exact hpreviousCenter.symm
  have houtgoingOpposite : dartOrbitFace RS (RS.alpha outgoingDart) =
      (corridor.faceAt interior.outgoing.right).1 := by
    apply dartOrbitFace_alpha_eq_of_mem_other_face RS htwoSided
      outgoingDart (corridor.faceAt interior.outgoing.right).1 houtgoingNext
    rw [houtgoingFace]
    exact hcenterNext
  have hnotAdjacent := corridor.separated_not_adjacent
    interior.incoming.left interior.outgoing.right (by
      change interior.center.val - 1 + 1 < interior.center.val + 1
      have hpositive := interior.center_pos
      omega)
  rcases hdartCases with hforward | hreverse
  · have hcornerNe : dartOrbitFace RS (RS.alpha incomingDart) ≠
        dartOrbitFace RS (RS.alpha (RS.phi incomingDart)) := by
      rw [← hforward, hincomingOpposite, houtgoingOpposite]
      exact hpreviousNext
    have hadj := oppositeFaces_adjacent_at_cubic_corner RS hcubic hrotation
      incomingDart hcornerNe
    apply hnotAdjacent
    convert hadj using 1 <;> apply Subtype.ext <;>
      simp only [hincomingOpposite, ← hforward, houtgoingOpposite]
  · have hcornerNe : dartOrbitFace RS (RS.alpha outgoingDart) ≠
        dartOrbitFace RS (RS.alpha (RS.phi outgoingDart)) := by
      rw [← hreverse, houtgoingOpposite, hincomingOpposite]
      exact hpreviousNext.symm
    have hadj := oppositeFaces_adjacent_at_cubic_corner RS hcubic hrotation
      outgoingDart hcornerNe
    apply hnotAdjacent
    convert hadj.symm using 1 <;> apply Subtype.ext <;>
      simp only [houtgoingOpposite, ← hreverse, hincomingOpposite]

/-- The two local types remaining on an induced cubic hex corridor. -/
abbrev InducedHexRungType :=
  {rungType : HexRungType // rungType ≠ HexRungType.adjacent}

@[simp]
theorem card_inducedHexRungType : Fintype.card InducedHexRungType = 2 := by
  decide

/-- The rung-type word of an induced cubic corridor, with the impossible
adjacent type removed. -/
noncomputable def inducedHexRungTypeWord {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    Fin (corridorLength - 2) → InducedHexRungType :=
  fun offset =>
    let placement := internalHexRungPlacement corridor htwoSided hunique offset
    ⟨placement.rungType,
      GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
        placement hcubic hrotation htwoSided⟩

/-- The induced-corridor local words have the sharper two-letter bound. -/
theorem card_inducedHexRungTypeWords (corridorLength : Nat) :
    Fintype.card (Fin (corridorLength - 2) → InducedHexRungType) =
      2 ^ (corridorLength - 2) := by
  simp

/-- In the large-fullerene corridor supplied by the structural L1 route,
every internal local type is non-adjacent; equivalently, the corridor has a
two-letter rung-separation word. -/
theorem orbitFaceFullerene_exists_inducedHexCorridor_with_twoRungTypes
    {G : SimpleGraph V} [DecidableRel G.Adj] (data : Data G)
    (hsphere : SphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hfullerene : OrbitFaceFullerene data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (13 * corridorLength - 1) <
      Fintype.card (OrbitFace data.toRotationSystem)) :
    ∃ corridor : OrbitHexCorridorSkeleton data.toRotationSystem corridorLength,
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        Function.Injective (corridor.rungEdge hunique) ∧
        ∀ offset : Fin (corridorLength - 2),
          (internalHexRungTypeWord corridor htwoSided hunique offset) ≠
            HexRungType.adjacent := by
  obtain ⟨corridor, hunique, hinjective, _htypeWord⟩ :=
    orbitFaceFullerene_exists_hexCorridor_with_internalRungTypeWord
      data hsphere htwoSided hfullerene hconnected hrotation hcyclicFive
        corridorLength hpositive hlarge
  exact ⟨corridor, hunique, hinjective, fun offset =>
    GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
      (internalHexRungPlacement corridor htwoSided hunique offset)
        hsphere.cubic hrotation htwoSided⟩

end

end GoertzelV24InducedHexCorridorTypes

end Mettapedia.GraphTheory.FourColor
