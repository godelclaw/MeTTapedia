import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSkeleton

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexFaceRungType

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The face permutation is a single cycle when restricted to one of its
actual dart orbits. -/
theorem faceOrbit_isCycleOn (RS : RotationSystem V E) (root : RS.D) :
    RS.phi.IsCycleOn (RS.faceOrbit root) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro dart hdart
    exact RS.phi_mem_faceOrbit hdart
  · intro left hleft right hright heq
    exact RS.phi.injective heq
  · intro dart hdart
    exact ⟨RS.phi.symm dart, RS.phi_symm_mem_faceOrbit hdart, by simp⟩
  · intro left hleft right hright
    exact ((RS.mem_faceOrbit).1 hleft).symm.trans
      ((RS.mem_faceOrbit).1 hright)

/-- The dart reached after a bounded number of face-permutation steps from a
chosen root. -/
def faceCycleDart (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) : RS.D :=
  (RS.phi ^ position.val) root

theorem faceCycleDart_mem (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    faceCycleDart RS root position ∈ RS.faceOrbit root := by
  exact (faceOrbit_isCycleOn RS root).1.mapsTo.perm_pow position.val
    (RS.mem_faceOrbit_self root)

/-- Bounded powers enumerate a facial dart cycle without repetition. -/
theorem faceCycleDart_injective (RS : RotationSystem V E) (root : RS.D) :
    Function.Injective (faceCycleDart RS root) := by
  intro left right heq
  apply Fin.ext
  exact ((faceOrbit_isCycleOn RS root).pow_apply_eq_pow_apply
      (RS.mem_faceOrbit_self root)).mp heq |>.eq_of_lt_of_lt
        left.isLt right.isLt

/-- Every dart in a face orbit occurs at a unique bounded power of `phi`. -/
theorem existsUnique_faceCycleDart_eq (RS : RotationSystem V E) (root dart : RS.D)
    (hdart : dart ∈ RS.faceOrbit root) :
    ∃! position : Fin (RS.faceOrbit root).card,
      faceCycleDart RS root position = dart := by
  rcases (faceOrbit_isCycleOn RS root).exists_pow_eq
      (RS.mem_faceOrbit_self root) hdart with ⟨power, hpower, rfl⟩
  refine ⟨⟨power, hpower⟩, rfl, ?_⟩
  intro other hother
  exact faceCycleDart_injective RS root hother

/-- The underlying boundary edge at one cyclic dart position. -/
def faceCycleEdge (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) : E :=
  RS.edgeOf (faceCycleDart RS root position)

theorem faceCycleEdge_mem (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    faceCycleEdge RS root position ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
  rw [orbitFaceBoundary_dartOrbitFace_eq_faceEdges]
  exact Finset.mem_image.2
    ⟨faceCycleDart RS root position, faceCycleDart_mem RS root position, rfl⟩

/-- On a two-sided facial cycle, the cyclic edge positions are distinct. -/
theorem faceCycleEdge_injective (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (root : RS.D) :
    Function.Injective (faceCycleEdge RS root) := by
  intro left right hedge
  apply faceCycleDart_injective RS root
  have hinjective : Set.InjOn RS.edgeOf (RS.faceOrbit root) := by
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root]
    apply Finset.card_image_iff.mp
    exact orbitFaceBoundarySimple_of_twoSided RS htwoSided
      (dartOrbitFace RS root)
  exact hinjective (faceCycleDart_mem RS root left)
    (faceCycleDart_mem RS root right) hedge

/-- Every boundary edge of a two-sided face has a unique cyclic position in
the actual face-permutation orbit. -/
theorem existsUnique_faceCycleEdge_eq (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (root : RS.D) (edge : E)
    (hedge : edge ∈ orbitFaceBoundary RS (dartOrbitFace RS root)) :
    ∃! position : Fin (RS.faceOrbit root).card,
      faceCycleEdge RS root position = edge := by
  rw [orbitFaceBoundary_dartOrbitFace_eq_faceEdges] at hedge
  rcases Finset.mem_image.1 hedge with ⟨dart, hdart, hdartEdge⟩
  rcases existsUnique_faceCycleDart_eq RS root dart hdart with
    ⟨position, hposition, _hpositionUnique⟩
  have hpositionEdge : faceCycleEdge RS root position = edge := by
    unfold faceCycleEdge
    rw [hposition]
    exact hdartEdge
  refine ⟨position, hpositionEdge, ?_⟩
  · intro other hother
    exact faceCycleEdge_injective RS htwoSided root
      (hother.trans hpositionEdge.symm)

/-- An internal face index of a corridor, with both a predecessor and a
successor. -/
structure CorridorInterior (corridorLength : Nat) where
  center : Fin corridorLength
  center_pos : 0 < center.val
  center_succ_lt : center.val + 1 < corridorLength

namespace CorridorInterior

/-- The corridor step entering an internal face. -/
def incoming {corridorLength : Nat}
    (interior : CorridorInterior corridorLength) :
    CorridorStep corridorLength where
  left := ⟨interior.center.val - 1, by
    have hcenter := interior.center.isLt
    omega⟩
  right_in_range := by
    change interior.center.val - 1 + 1 < corridorLength
    have hcenter := interior.center.isLt
    have hpositive := interior.center_pos
    omega

/-- The corridor step leaving an internal face. -/
def outgoing {corridorLength : Nat}
    (interior : CorridorInterior corridorLength) :
    CorridorStep corridorLength where
  left := interior.center
  right_in_range := interior.center_succ_lt

@[simp]
theorem incoming_right {corridorLength : Nat}
    (interior : CorridorInterior corridorLength) :
    interior.incoming.right = interior.center := by
  apply Fin.ext
  change interior.center.val - 1 + 1 = interior.center.val
  have hpositive := interior.center_pos
  omega

@[simp]
theorem outgoing_left {corridorLength : Nat}
    (interior : CorridorInterior corridorLength) :
    interior.outgoing.left = interior.center :=
  rfl

theorem incoming_ne_outgoing {corridorLength : Nat}
    (interior : CorridorInterior corridorLength) :
    interior.incoming ≠ interior.outgoing := by
  intro heq
  have hleft := congrArg (fun step : CorridorStep corridorLength => step.left.val) heq
  change interior.center.val - 1 = interior.center.val at hleft
  have hpositive := interior.center_pos
  omega

end CorridorInterior

/-- The two canonical corridor rungs, located on the actual six-dart
`phi`-cycle of one internal hexagonal face. -/
structure InternalHexRungPlacement {RS : RotationSystem V E}
    {corridorLength : Nat} (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) where
  root : RS.D
  root_face : dartOrbitFace RS root = (corridor.faceAt interior.center).1
  orbit_card : (RS.faceOrbit root).card = 6
  incomingPosition : Fin (RS.faceOrbit root).card
  outgoingPosition : Fin (RS.faceOrbit root).card
  incoming_edge : faceCycleEdge RS root incomingPosition =
    corridor.rungEdge hunique interior.incoming
  outgoing_edge : faceCycleEdge RS root outgoingPosition =
    corridor.rungEdge hunique interior.outgoing
  positions_ne : incomingPosition ≠ outgoingPosition

namespace InternalHexRungPlacement

/-- The incoming rung position transported to the standard six positions. -/
def incomingPosition6 {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) : Fin 6 :=
  Fin.cast placement.orbit_card placement.incomingPosition

/-- The outgoing rung position transported to the standard six positions. -/
def outgoingPosition6 {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) : Fin 6 :=
  Fin.cast placement.orbit_card placement.outgoingPosition

theorem positions6_ne {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    placement.incomingPosition6 ≠ placement.outgoingPosition6 := by
  exact fun heq => placement.positions_ne
    (Fin.cast_injective placement.orbit_card heq)

end InternalHexRungPlacement

/-- Every internal face of a two-sided hex corridor has its incoming and
outgoing rungs at two distinct positions of the real six-dart facial cycle. -/
theorem exists_internalHexRungPlacement {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) :
    Nonempty (InternalHexRungPlacement corridor hunique interior) := by
  rcases exists_dartOrbitFace_eq RS (corridor.faceAt interior.center).1 with
    ⟨root, hroot⟩
  have horbitCard : (RS.faceOrbit root).card = 6 := by
    calc
      (RS.faceOrbit root).card =
          (orbitFaceDarts RS (dartOrbitFace RS root)).card := by
        rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      _ = (orbitFaceBoundary RS (dartOrbitFace RS root)).card := by
        exact (orbitFaceBoundarySimple_of_twoSided RS htwoSided
          (dartOrbitFace RS root)).symm
      _ = (orbitFaceBoundary RS
          (corridor.faceAt interior.center).1).card := by rw [hroot]
      _ = 6 := corridor.hexagonal interior.center
  have hincomingMem : corridor.rungEdge hunique interior.incoming ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
    rw [hroot]
    simpa using corridor.rungEdge_mem_right hunique interior.incoming
  have houtgoingMem : corridor.rungEdge hunique interior.outgoing ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
    rw [hroot]
    exact corridor.rungEdge_mem_left hunique interior.outgoing
  rcases existsUnique_faceCycleEdge_eq RS htwoSided root
      (corridor.rungEdge hunique interior.incoming) hincomingMem with
    ⟨incomingPosition, hincomingEdge, _hincomingUnique⟩
  rcases existsUnique_faceCycleEdge_eq RS htwoSided root
      (corridor.rungEdge hunique interior.outgoing) houtgoingMem with
    ⟨outgoingPosition, houtgoingEdge, _houtgoingUnique⟩
  have hpositionsNe : incomingPosition ≠ outgoingPosition := by
    intro hpositions
    have hrungs : corridor.rungEdge hunique interior.incoming =
        corridor.rungEdge hunique interior.outgoing := by
      rw [← hincomingEdge, ← houtgoingEdge, hpositions]
    exact interior.incoming_ne_outgoing
      (corridor.rungEdge_injective htwoSided hunique hrungs)
  exact ⟨⟨root, hroot, horbitCard, incomingPosition, outgoingPosition,
    hincomingEdge, houtgoingEdge, hpositionsNe⟩⟩

/-- Forward distance between two positions on a directed hexagonal cycle. -/
def hexForwardDistance (left right : Fin 6) : Nat :=
  (right.val + 6 - left.val) % 6

/-- Unoriented cyclic distance between two positions of a hexagon. -/
def hexCyclicDistance (left right : Fin 6) : Nat :=
  min (hexForwardDistance left right) (hexForwardDistance right left)

/-- There are exactly three possible separations between two distinct edges
of a hexagonal facial cycle. -/
theorem hexCyclicDistance_eq_one_or_two_or_three (left right : Fin 6)
    (hne : left ≠ right) :
    hexCyclicDistance left right = 1 ∨
      hexCyclicDistance left right = 2 ∨
      hexCyclicDistance left right = 3 := by
  fin_cases left <;> fin_cases right <;>
    norm_num [hexCyclicDistance, hexForwardDistance] at *

/-- The finite local type of the two corridor rungs on an internal hexagon. -/
inductive HexRungType where
  | adjacent
  | oneEdgeBetween
  | opposite
  deriving DecidableEq, Fintype

/-- The cyclic separation represented by a local rung type. -/
def HexRungType.distance : HexRungType → Nat
  | .adjacent => 1
  | .oneEdgeBetween => 2
  | .opposite => 3

/-- Compute the local rung type from the two actual facial-cycle positions. -/
def hexRungType (left right : Fin 6) : HexRungType :=
  if hexCyclicDistance left right = 1 then .adjacent
  else if hexCyclicDistance left right = 2 then .oneEdgeBetween
  else .opposite

theorem hexRungType_distance_eq (left right : Fin 6) (hne : left ≠ right) :
    (hexRungType left right).distance = hexCyclicDistance left right := by
  rcases hexCyclicDistance_eq_one_or_two_or_three left right hne with
    hone | htwo | hthree
  · simp [hexRungType, hone, HexRungType.distance]
  · simp [hexRungType, htwo, HexRungType.distance]
  · simp [hexRungType, hthree, HexRungType.distance]

/-- The computed local rung type of an internally placed corridor face. -/
def InternalHexRungPlacement.rungType {RS : RotationSystem V E}
    {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    HexRungType :=
  hexRungType placement.incomingPosition6 placement.outgoingPosition6

theorem InternalHexRungPlacement.rungType_distance_eq
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    placement.rungType.distance =
      hexCyclicDistance placement.incomingPosition6 placement.outgoingPosition6 := by
  exact hexRungType_distance_eq _ _ placement.positions6_ne

@[simp]
theorem card_hexRungType : Fintype.card HexRungType = 3 := by
  decide

/-- The internal face corresponding to an offset in the corridor with its two
end faces removed. -/
def corridorInteriorOfOffset {corridorLength : Nat}
    (offset : Fin (corridorLength - 2)) : CorridorInterior corridorLength where
  center := ⟨offset.val + 1, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega⟩
  center_pos := by
    change 0 < offset.val + 1
    omega
  center_succ_lt := by
    change offset.val + 1 + 1 < corridorLength
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega

/-- Select a placement proved to come from the real rotation and incidence
data for each internal corridor face. -/
noncomputable def internalHexRungPlacement {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (offset : Fin (corridorLength - 2)) :
    InternalHexRungPlacement corridor hunique (corridorInteriorOfOffset offset) :=
  Classical.choice
    (exists_internalHexRungPlacement corridor htwoSided hunique
      (corridorInteriorOfOffset offset))

/-- The finite local rung-type word read from all internal hexagons of a
corridor. -/
noncomputable def internalHexRungTypeWord {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    Fin (corridorLength - 2) → HexRungType :=
  fun offset => (internalHexRungPlacement corridor htwoSided hunique offset).rungType

/-- There are at most `3^(length-2)` words at the rung-separation level of
the local hex-corridor classification. -/
theorem card_hexRungTypeWords (corridorLength : Nat) :
    Fintype.card (Fin (corridorLength - 2) → HexRungType) =
      3 ^ (corridorLength - 2) := by
  simp

/-- A sufficiently large graph-backed cellular fullerene in cyclically
5-edge-connected normal form contains an induced hex corridor whose distinct
canonical rungs determine a three-letter local type word on its internal
faces. -/
theorem orbitFaceFullerene_exists_hexCorridor_with_internalRungTypeWord
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
          (internalHexRungTypeWord corridor htwoSided hunique offset).distance =
            hexCyclicDistance
              (internalHexRungPlacement corridor htwoSided hunique offset).incomingPosition6
              (internalHexRungPlacement corridor htwoSided hunique offset).outgoingPosition6 := by
  obtain ⟨corridor, hunique, _huniqueRungs, hinjective⟩ :=
    orbitFaceFullerene_exists_hexCorridorSkeleton_with_uniqueRungs
      data hsphere htwoSided hfullerene hconnected hrotation hcyclicFive
        corridorLength hpositive hlarge
  exact ⟨corridor, hunique, hinjective,
    fun offset =>
      (internalHexRungPlacement corridor htwoSided hunique offset).rungType_distance_eq⟩

end

end GoertzelV24HexFaceRungType

end Mettapedia.GraphTheory.FourColor
