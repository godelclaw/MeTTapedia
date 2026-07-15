import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorColorTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24WindingClassification

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorFiniteColorTransition

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The unique three-symbol representative of a nonzero ambient Tait color. -/
def strandColorOfNonzero (color : Color) (hcolor : color ≠ 0) : StrandColor :=
  Classical.choose (StrandColor.existsUnique_toColor_eq_of_ne_zero color hcolor)

@[simp]
theorem strandColorOfNonzero_toColor (color : Color) (hcolor : color ≠ 0) :
    (strandColorOfNonzero color hcolor).toColor = color :=
  (Classical.choose_spec
    (StrandColor.existsUnique_toColor_eq_of_ne_zero color hcolor)).1

/-- The six boundary-edge colors of an actually placed corridor hexagon,
transported to the standard cyclic six-slot coordinate system. -/
def placedHexColorWord
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    Fin 6 → StrandColor :=
  fun position =>
    strandColorOfNonzero
      (C (faceCycleEdge RS placement.root
        (placementPositionOfSix placement position)))
      (hC _)

@[simp]
theorem placedHexColorWord_toColor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (position : Fin 6) :
    (placedHexColorWord placement C hC position).toColor =
      C (faceCycleEdge RS placement.root
        (placementPositionOfSix placement position)) := by
  simp [placedHexColorWord]

@[simp]
theorem placedHexColorWord_castPosition_toColor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (position : Fin (RS.faceOrbit placement.root).card) :
    (placedHexColorWord placement C hC
      (Fin.cast placement.orbit_card position)).toColor =
        C (faceCycleEdge RS placement.root position) := by
  rw [placedHexColorWord_toColor]
  congr 2

@[simp]
theorem placedHexColorWord_outgoing_toColor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (placedHexColorWord placement C hC placement.outgoingPosition6).toColor =
      C (corridor.rungEdge hunique interior.outgoing) := by
  rw [placedHexColorWord_toColor,
    placementPositionOfSix_outgoingPosition6, placement.outgoing_edge]

/-- Every graph-backed face word extracted from a Tait-colored cubic
rotation system is a proper cyclic six-color word. -/
theorem placedHexColorWord_isProper
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    IsProperCyclicColorWord (placedHexColorWord placement C hC) := by
  intro position hcolors
  let leftPosition := placementPositionOfSix placement position
  let rightPosition :=
    placementPositionOfSix placement (cyclicSucc position)
  have hsuccessor : rightPosition.val ≡ leftPosition.val + 1 [MOD 6] := by
    simp [rightPosition, leftPosition, cyclicSucc, Nat.ModEq]
  have hdarts : faceCycleDart RS placement.root rightPosition =
      RS.phi (faceCycleDart RS placement.root leftPosition) :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      leftPosition rightPosition hsuccessor
  have hcorner := cornerEdges_pairwise_ne_and_incident RS hcubic hrotation
    (faceCycleDart RS placement.root leftPosition)
  have hedgeAdj : RS.edgeAdjacencyGraph.Adj
      (faceCycleEdge RS placement.root leftPosition)
      (faceCycleEdge RS placement.root rightPosition) := by
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    · simpa only [faceCycleEdge, hdarts] using hcorner.1
    · simpa only [faceCycleEdge] using hcorner.2.2.2.1
    · simpa only [faceCycleEdge, hdarts] using hcorner.2.2.2.2.1
  have hproper := C.valid hedgeAdj
  apply hproper
  have hcolorsAmbient := congrArg StrandColor.toColor hcolors
  simpa only [placedHexColorWord_toColor] using hcolorsAmbient

/-- The abstract winding classification is realized by every actual
Tait-colored corridor hexagon. -/
theorem placedHexColorWord_windingScore_classification
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    windingScore (placedHexColorWord placement C hC) = 0 ∨
      windingScore (placedHexColorWord placement C hC) = 6 ∨
      windingScore (placedHexColorWord placement C hC) = -6 :=
  proper_hexagon_windingScore _
    (placedHexColorWord_isProper placement hcubic hrotation C hC)

/-- Raw finite color state of one corridor hexagon. Mathematical validity is
checked by `HexSlabColorState.Valid`; no conclusion is stored as a field. -/
structure HexSlabColorState where
  incoming : Fin 6
  outgoing : Fin 6
  color : Fin 6 → StrandColor
  deriving DecidableEq, Fintype

/-- Computed validity of a finite slab state: distinct non-adjacent rungs and
a proper cyclic boundary coloring. -/
def HexSlabColorState.Valid (state : HexSlabColorState) : Prop :=
  state.incoming ≠ state.outgoing ∧
    hexRungType state.incoming state.outgoing ≠ HexRungType.adjacent ∧
    IsProperCyclicColorWord state.color
  deriving Decidable

/-- Extract the finite state from a real placed hexagon and real Tait
coloring. -/
def hexSlabColorStateOfPlacement
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    HexSlabColorState where
  incoming := placement.incomingPosition6
  outgoing := placement.outgoingPosition6
  color := placedHexColorWord placement C hC

/-- Every state extracted from a real induced corridor placement is valid. -/
theorem hexSlabColorStateOfPlacement_valid
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (hexSlabColorStateOfPlacement placement C hC).Valid := by
  exact ⟨placement.positions6_ne,
    InternalHexRungPlacement.rungType_ne_adjacent
      placement hcubic hrotation htwoSided,
    placedHexColorWord_isProper placement hcubic hrotation C hC⟩

/-- Finite two-corner transition test between raw six-slot slab states.
It records exactly the two retained positions flanking the source's outgoing
rung and their forced target colors. -/
def FlankingTaitColorTransition
    (source target : HexSlabColorState) : Prop :=
  source.Valid ∧ target.Valid ∧
    ∃ sourceBefore sourceAfter targetBefore targetAfter : Fin 6,
      sourceBefore ≠ sourceAfter ∧ targetBefore ≠ targetAfter ∧
      sourceBefore ∈ hexSidePositions source.incoming source.outgoing ∧
      sourceAfter ∈ hexSidePositions source.incoming source.outgoing ∧
      targetBefore ∈ hexSidePositions target.incoming target.outgoing ∧
      targetAfter ∈ hexSidePositions target.incoming target.outgoing ∧
      source.outgoing.val ≡ sourceBefore.val + 1 [MOD 6] ∧
      sourceAfter.val ≡ source.outgoing.val + 1 [MOD 6] ∧
      (target.color targetBefore).toColor =
        (source.color sourceBefore).toColor +
          (source.color source.outgoing).toColor ∧
      (target.color targetAfter).toColor =
        (source.color source.outgoing).toColor +
          (source.color sourceAfter).toColor
  deriving Decidable

/-- Consecutive real placements in a clean induced hex corridor satisfy the
finite flanking transition test. The finite witnesses are extracted from the
actual shared edges; the transition is not postulated as corridor data. -/
theorem flankingTaitColorTransition_of_consecutivePlacements
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (leftInterior : CorridorInterior corridorLength)
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique
        (nextCorridorInterior leftInterior hnext))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    FlankingTaitColorTransition
      (hexSlabColorStateOfPlacement leftPlacement C hC)
      (hexSlabColorStateOfPlacement rightPlacement C hC) := by
  have hleftValid := hexSlabColorStateOfPlacement_valid leftPlacement
    hcubic hrotation htwoSided C hC
  have hrightValid := hexSlabColorStateOfPlacement_valid rightPlacement
    hcubic hrotation htwoSided C hC
  have hnonadjacent : leftPlacement.rungType ≠ HexRungType.adjacent :=
    InternalHexRungPlacement.rungType_ne_adjacent
      leftPlacement hcubic hrotation htwoSided
  rcases exists_two_hexSidePositions_flanking_outgoing
    leftPlacement.incomingPosition6 leftPlacement.outgoingPosition6
      leftPlacement.positions6_ne hnonadjacent with
    ⟨leftBefore6, leftAfter6, hleftBeforeAfter,
      hbeforeMod, hafterMod⟩
  let leftBefore := placementSidePositionOfSix leftPlacement leftBefore6
  let leftAfter := placementSidePositionOfSix leftPlacement leftAfter6
  have hbeforeActual : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6] := by
    simpa [leftBefore, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  have hafterActual : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [leftAfter, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hafterMod
  rcases exists_nextPlacementSideEdge_eq_beforeOutgoingCornerEdge
    clean hcubic hrotation htwoSided hunique leftInterior hnext leftPlacement
      leftBefore hbeforeActual rightPlacement with
    ⟨rightBefore, hrightBeforeEdge, hrightBeforeFace⟩
  rcases exists_nextPlacementSideEdge_eq_afterOutgoingCornerEdge
    clean hcubic hrotation htwoSided hunique leftInterior hnext leftPlacement
      leftAfter hafterActual rightPlacement with
    ⟨rightAfter, hrightAfterEdge, hrightAfterFace⟩
  let rightBefore6 := Fin.cast rightPlacement.orbit_card rightBefore.1
  let rightAfter6 := Fin.cast rightPlacement.orbit_card rightAfter.1
  have hrightBeforeAfter : rightBefore ≠ rightAfter := by
    intro heq
    apply hleftBeforeAfter
    have hleftEq : leftBefore = leftAfter := by
      apply placementSideNeighbor_injective clean htwoSided hunique leftPlacement
      calc
        placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore =
            placementSideNeighbor clean htwoSided hunique rightPlacement rightBefore :=
          hrightBeforeFace
        _ = placementSideNeighbor clean htwoSided hunique rightPlacement rightAfter := by
          rw [heq]
        _ = placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter :=
          hrightAfterFace.symm
    apply Subtype.ext
    have hvals := congrArg (fun position => position.1.val) hleftEq
    exact Fin.ext hvals
  have hrightBeforeAfter6 : rightBefore6 ≠ rightAfter6 := by
    intro heq
    apply hrightBeforeAfter
    apply Subtype.ext
    exact Fin.cast_injective rightPlacement.orbit_card heq
  have hleftBeforeAfter6 : leftBefore6.1 ≠ leftAfter6.1 := by
    intro heq
    exact hleftBeforeAfter (Subtype.ext heq)
  have hrightBeforeMem : rightBefore6 ∈
      hexSidePositions rightPlacement.incomingPosition6
        rightPlacement.outgoingPosition6 := by
    have hmem := (mem_placementSidePositions_iff rightPlacement rightBefore.1).1
      rightBefore.2
    simpa [rightBefore6, hexSidePositions,
      InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hmem
  have hrightAfterMem : rightAfter6 ∈
      hexSidePositions rightPlacement.incomingPosition6
        rightPlacement.outgoingPosition6 := by
    have hmem := (mem_placementSidePositions_iff rightPlacement rightAfter.1).1
      rightAfter.2
    simpa [rightAfter6, hexSidePositions,
      InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hmem
  have hbeforeColor :
      (placedHexColorWord rightPlacement C hC rightBefore6).toColor =
        (placedHexColorWord leftPlacement C hC leftBefore6.1).toColor +
          (placedHexColorWord leftPlacement C hC
            leftPlacement.outgoingPosition6).toColor := by
    calc
      (placedHexColorWord rightPlacement C hC rightBefore6).toColor =
          C (placementSideEdge htwoSided rightPlacement rightBefore) := by
        rw [show rightBefore6 =
            Fin.cast rightPlacement.orbit_card rightBefore.1 from rfl,
          placedHexColorWord_castPosition_toColor]
        rfl
      _ = C (beforeOutgoingCornerEdge leftPlacement) :=
        congrArg C hrightBeforeEdge
      _ = C (placementSideEdge htwoSided leftPlacement leftBefore) +
          C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
            leftInterior.outgoing) :=
        taitColor_beforeOutgoingCornerEdge_eq_add hcubic hrotation htwoSided
          leftPlacement leftBefore hbeforeActual C hC
      _ = (placedHexColorWord leftPlacement C hC leftBefore6.1).toColor +
          (placedHexColorWord leftPlacement C hC
            leftPlacement.outgoingPosition6).toColor := by
        rw [placedHexColorWord_outgoing_toColor,
          placedHexColorWord_toColor]
        rfl
  have hafterColor :
      (placedHexColorWord rightPlacement C hC rightAfter6).toColor =
        (placedHexColorWord leftPlacement C hC
          leftPlacement.outgoingPosition6).toColor +
          (placedHexColorWord leftPlacement C hC leftAfter6.1).toColor := by
    calc
      (placedHexColorWord rightPlacement C hC rightAfter6).toColor =
          C (placementSideEdge htwoSided rightPlacement rightAfter) := by
        rw [show rightAfter6 =
            Fin.cast rightPlacement.orbit_card rightAfter.1 from rfl,
          placedHexColorWord_castPosition_toColor]
        rfl
      _ = C (afterOutgoingCornerEdge leftPlacement) :=
        congrArg C hrightAfterEdge
      _ = C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
          leftInterior.outgoing) +
          C (placementSideEdge htwoSided leftPlacement leftAfter) :=
        taitColor_afterOutgoingCornerEdge_eq_add hcubic hrotation htwoSided
          leftPlacement leftAfter hafterActual C hC
      _ = (placedHexColorWord leftPlacement C hC
          leftPlacement.outgoingPosition6).toColor +
          (placedHexColorWord leftPlacement C hC leftAfter6.1).toColor := by
        rw [placedHexColorWord_outgoing_toColor,
          placedHexColorWord_toColor]
        rfl
  refine ⟨hleftValid, hrightValid, leftBefore6.1, leftAfter6.1,
    rightBefore6, rightAfter6, hleftBeforeAfter6, hrightBeforeAfter6,
    leftBefore6.2, leftAfter6.2, hrightBeforeMem, hrightAfterMem,
    hbeforeMod, hafterMod, ?_, ?_⟩
  · exact hbeforeColor
  · exact hafterColor

/-- The finite slab-state space has an explicit cardinality: two six-slot
rung positions and one of three colors at each of six boundary positions. -/
theorem card_hexSlabColorState : Fintype.card HexSlabColorState = 26244 := by
  let stateEquiv : HexSlabColorState ≃
      Fin 6 × Fin 6 × (Fin 6 → StrandColor) :=
    { toFun := fun state => (state.incoming, state.outgoing, state.color)
      invFun := fun data => ⟨data.1, data.2.1, data.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr stateEquiv]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  rw [hcolor]
  norm_num

end

end GoertzelV24HexCorridorFiniteColorTransition

end Mettapedia.GraphTheory.FourColor
