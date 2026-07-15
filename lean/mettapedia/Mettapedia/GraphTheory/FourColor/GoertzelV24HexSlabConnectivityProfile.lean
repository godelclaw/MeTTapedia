import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorColorStateWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphSplit

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexSlabConnectivityProfile

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The ambient color pair represented by each of the three profile labels. -/
def trackedColorPairColors : TrackedColorPair → Color × Color
  | .ab => (red, blue)
  | .ac => (red, purple)
  | .bc => (blue, purple)

/-- The tracked two-color line graph restricted to a specified finite edge
region. Keeping the original edge carrier makes interface edges usable
without subtype transports. -/
def regionalTrackedEdgeGraph (RS : RotationSystem V E)
    (region : Finset E) (C : E → Color) (a b : Color) : SimpleGraph E where
  Adj left right :=
    (RS.trackedEdgeGraph C a b).Adj left right ∧
      left ∈ region ∧ right ∈ region
  symm := ⟨by
    rintro left right ⟨hadj, hleft, hright⟩
    exact ⟨hadj.symm, hright, hleft⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact hedge.1.1.1 rfl⟩

/-- Computed regional two-color connectivity. The endpoint guards prevent
reflexive graph reachability from marking an untracked or out-of-region edge
as connected to itself. -/
def regionalTrackedConnectivity
    (RS : RotationSystem V E) (region : Finset E) (C : E → Color)
    (pair : TrackedColorPair) (left right : E) : Bool := by
  classical
  let colors := trackedColorPairColors pair
  exact decide (left ∈ region) && decide (right ∈ region) &&
    decide (IsTrackedColor colors.1 colors.2 (C left)) &&
    decide (IsTrackedColor colors.1 colors.2 (C right)) &&
    decide ((regionalTrackedEdgeGraph RS region C colors.1 colors.2).Reachable
      left right)

theorem regionalTrackedConnectivity_eq_true_iff
    (RS : RotationSystem V E) (region : Finset E) (C : E → Color)
    (pair : TrackedColorPair) (left right : E) :
    regionalTrackedConnectivity RS region C pair left right = true ↔
      left ∈ region ∧ right ∈ region ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C left) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C right) ∧
      (regionalTrackedEdgeGraph RS region C
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left right := by
  simp [regionalTrackedConnectivity, and_assoc]

/-- Enlarging the regional edge set can only add tracked adjacencies. -/
theorem regionalTrackedEdgeGraph_mono
    (RS : RotationSystem V E) (C : E → Color) (a b : Color)
    {region larger : Finset E} (hregion : region ⊆ larger) :
    regionalTrackedEdgeGraph RS region C a b ≤
      regionalTrackedEdgeGraph RS larger C a b := by
  intro left right hadj
  exact ⟨hadj.1, hregion hadj.2.1, hregion hadj.2.2⟩

/-- Regional tracked connectivity is symmetric because it is genuine
reachability in an undirected graph, with symmetric endpoint guards. -/
theorem regionalTrackedConnectivity_comm
    (RS : RotationSystem V E) (region : Finset E) (C : E → Color)
    (pair : TrackedColorPair) (left right : E) :
    regionalTrackedConnectivity RS region C pair left right =
      regionalTrackedConnectivity RS region C pair right left := by
  apply Bool.eq_iff_iff.mpr
  rw [regionalTrackedConnectivity_eq_true_iff,
    regionalTrackedConnectivity_eq_true_iff]
  constructor
  · rintro ⟨hleft, hright, hcolorLeft, hcolorRight, hreach⟩
    exact ⟨hright, hleft, hcolorRight, hcolorLeft, hreach.symm⟩
  · rintro ⟨hright, hleft, hcolorRight, hcolorLeft, hreach⟩
    exact ⟨hleft, hright, hcolorLeft, hcolorRight, hreach.symm⟩

/-- Regional tracked connectivity is transitive. Together with symmetry and
the guarded diagonal theorem, this makes the computed matrix a partial
equivalence relation whose support is exactly the tracked regional edges. -/
theorem regionalTrackedConnectivity_trans
    (RS : RotationSystem V E) (region : Finset E) (C : E → Color)
    (pair : TrackedColorPair) (left middle right : E)
    (hleftMiddle :
      regionalTrackedConnectivity RS region C pair left middle = true)
    (hmiddleRight :
      regionalTrackedConnectivity RS region C pair middle right = true) :
    regionalTrackedConnectivity RS region C pair left right = true := by
  rw [regionalTrackedConnectivity_eq_true_iff] at hleftMiddle hmiddleRight ⊢
  exact ⟨hleftMiddle.1, hmiddleRight.2.1, hleftMiddle.2.2.1,
    hmiddleRight.2.2.2.1, hleftMiddle.2.2.2.2.trans hmiddleRight.2.2.2.2⟩

/-- The diagonal entry records exactly whether the edge belongs to the
region and carries one of the tracked colors. -/
theorem regionalTrackedConnectivity_self_eq_true_iff
    (RS : RotationSystem V E) (region : Finset E) (C : E → Color)
    (pair : TrackedColorPair) (edge : E) :
    regionalTrackedConnectivity RS region C pair edge edge = true ↔
      edge ∈ region ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (C edge) := by
  rw [regionalTrackedConnectivity_eq_true_iff]
  constructor
  · rintro ⟨hmem, _, hcolor, _, _⟩
    exact ⟨hmem, hcolor⟩
  · rintro ⟨hmem, hcolor⟩
    exact ⟨hmem, hmem, hcolor, hcolor, .refl edge⟩

/-- Regional tracked connectivity is monotone under enlargement of the
allowed edge region. -/
theorem regionalTrackedConnectivity_mono
    (RS : RotationSystem V E) (C : E → Color) (pair : TrackedColorPair)
    {region larger : Finset E} (hregion : region ⊆ larger)
    (left right : E)
    (hconnected : regionalTrackedConnectivity RS region C pair left right = true) :
    regionalTrackedConnectivity RS larger C pair left right = true := by
  rw [regionalTrackedConnectivity_eq_true_iff] at hconnected ⊢
  rcases hconnected with
    ⟨hleft, hright, hcolorLeft, hcolorRight, hreach⟩
  exact ⟨hregion hleft, hregion hright, hcolorLeft, hcolorRight,
    hreach.mono (regionalTrackedEdgeGraph_mono RS C _ _ hregion)⟩

/-- Six-by-six regional strand-connectivity matrix on the actual boundary
edges of a placed corridor hexagon. -/
def placedHexRegionalConnectivityProfile
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color) :
    TrackedColorPair → Fin 6 → Fin 6 → Bool :=
  fun pair left right => regionalTrackedConnectivity RS region C pair
    (faceCycleEdge RS placement.root
      (placementPositionOfSix placement left))
    (faceCycleEdge RS placement.root
      (placementPositionOfSix placement right))

theorem placedHexRegionalConnectivityProfile_eq_true_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color)
    (pair : TrackedColorPair) (left right : Fin 6) :
    placedHexRegionalConnectivityProfile placement region C pair left right = true ↔
      let leftEdge := faceCycleEdge RS placement.root
        (placementPositionOfSix placement left)
      let rightEdge := faceCycleEdge RS placement.root
        (placementPositionOfSix placement right)
      leftEdge ∈ region ∧ rightEdge ∈ region ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C leftEdge) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C rightEdge) ∧
      (regionalTrackedEdgeGraph RS region C
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable leftEdge rightEdge := by
  exact regionalTrackedConnectivity_eq_true_iff RS region C pair _ _

theorem placedHexRegionalConnectivityProfile_comm
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color)
    (pair : TrackedColorPair) (left right : Fin 6) :
    placedHexRegionalConnectivityProfile placement region C pair left right =
      placedHexRegionalConnectivityProfile placement region C pair right left :=
  regionalTrackedConnectivity_comm RS region C pair _ _

theorem placedHexRegionalConnectivityProfile_mono
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (pair : TrackedColorPair)
    {region larger : Finset E} (hregion : region ⊆ larger)
    (left right : Fin 6)
    (hconnected : placedHexRegionalConnectivityProfile placement region C
      pair left right = true) :
    placedHexRegionalConnectivityProfile placement larger C pair left right = true :=
  regionalTrackedConnectivity_mono RS C pair hregion _ _ hconnected

/-- The graph-extracted six-edge boundary profile embedded in the existing
finite corridor-profile carrier. This first bridge has no terminals and no
open face fragments; subsequent cut models can add them without changing
the connectivity semantics. -/
def placedHexBoundaryCutProfile
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) : CorridorCutProfile 6 0 0 where
  edgeColor := placedHexColorWord placement C hC
  strandConnected pair left right :=
    match left, right with
    | .inl leftPosition, .inl rightPosition =>
        placedHexRegionalConnectivityProfile placement region C pair
          leftPosition rightPosition
    | .inl _, .inr impossible => Fin.elim0 impossible
    | .inr impossible, _ => Fin.elim0 impossible
  faceContinues impossible := Fin.elim0 impossible
  faceLengthCap impossible := Fin.elim0 impossible

@[simp]
theorem placedHexBoundaryCutProfile_edgeColor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (placedHexBoundaryCutProfile placement region C hC).edgeColor =
      placedHexColorWord placement C hC :=
  rfl

theorem placedHexBoundaryCutProfile_strandConnected_eq_true_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (region : Finset E) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (left right : Fin 6) :
    (placedHexBoundaryCutProfile placement region C hC).strandConnected pair
        (.inl left) (.inl right) = true ↔
      let leftEdge := faceCycleEdge RS placement.root
        (placementPositionOfSix placement left)
      let rightEdge := faceCycleEdge RS placement.root
        (placementPositionOfSix placement right)
      leftEdge ∈ region ∧ rightEdge ∈ region ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C leftEdge) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C rightEdge) ∧
      (regionalTrackedEdgeGraph RS region C
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable leftEdge rightEdge := by
  exact placedHexRegionalConnectivityProfile_eq_true_iff
    placement region C pair left right

end

end GoertzelV24HexSlabConnectivityProfile

end Mettapedia.GraphTheory.FourColor
