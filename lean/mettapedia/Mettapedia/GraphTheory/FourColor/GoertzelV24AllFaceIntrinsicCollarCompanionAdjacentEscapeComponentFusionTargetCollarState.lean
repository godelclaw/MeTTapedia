import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarSignature
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarTerminalSignature

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle.IntrinsicShortTargetEscapeCollar

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The number of collar edges used by each of the seven traversal classes. -/
def TargetCollarTraversalClass.edgeCount :
    TargetCollarTraversalClass → Nat
  | .firstBoundaryPair => 2
  | .secondBoundaryPair => 2
  | .bothBoundaryPairs => 4
  | .cross _ _ => 3

/-- The coordinate support records precisely the number of edges prescribed
by its traversal class. -/
theorem TargetCollarTraversalClass.card_coordinateFinset
    (traversalClass : TargetCollarTraversalClass) :
    traversalClass.coordinateFinset.card = traversalClass.edgeCount := by
  cases traversalClass with
  | firstBoundaryPair => decide
  | secondBoundaryPair => decide
  | bothBoundaryPairs => decide
  | cross firstUsesOne secondUsesThree =>
      cases firstUsesOne <;> cases secondUsesThree <;> decide

/-- The five-bit description of a traversal class is equivalent to
membership in its fixed coordinate support. -/
theorem TargetCollarTraversalClass.describes_coordinate_iff
    (traversalClass : TargetCollarTraversalClass)
    {centralUsed : Prop} {boundaryUsed : Fin 4 → Prop}
    (description : traversalClass.Describes centralUsed
      (boundaryUsed 0) (boundaryUsed 1) (boundaryUsed 2)
      (boundaryUsed 3)) (coordinate : Option (Fin 4)) :
    (match coordinate with
      | none => centralUsed
      | some port => boundaryUsed port) ↔
        coordinate ∈ traversalClass.coordinateFinset := by
  cases traversalClass with
  | firstBoundaryPair =>
      rcases description with ⟨hcentral, hzero, hone, htwo, hthree⟩
      cases coordinate with
      | none => simpa [TargetCollarTraversalClass.coordinateFinset] using hcentral
      | some port =>
          fin_cases port <;>
            simp [TargetCollarTraversalClass.coordinateFinset,
              hzero, hone, htwo, hthree]
  | secondBoundaryPair =>
      rcases description with ⟨hcentral, hzero, hone, htwo, hthree⟩
      cases coordinate with
      | none => simpa [TargetCollarTraversalClass.coordinateFinset] using hcentral
      | some port =>
          fin_cases port <;>
            simp [TargetCollarTraversalClass.coordinateFinset,
              hzero, hone, htwo, hthree]
  | bothBoundaryPairs =>
      rcases description with ⟨hcentral, hzero, hone, htwo, hthree⟩
      cases coordinate with
      | none => simpa [TargetCollarTraversalClass.coordinateFinset] using hcentral
      | some port =>
          fin_cases port <;>
            simp [TargetCollarTraversalClass.coordinateFinset,
              hzero, hone, htwo, hthree]
  | cross firstUsesOne secondUsesThree =>
      cases firstUsesOne <;> cases secondUsesThree <;>
        simp only [TargetCollarTraversalClass.Describes, if_true]
          at description <;>
        rcases description with ⟨hcentral, ⟨hzero, hone⟩,
          ⟨htwo, hthree⟩⟩ <;>
        cases coordinate with
        | none =>
            simp [TargetCollarTraversalClass.coordinateFinset,
              TargetCollarTraversalClass.firstCrossPort,
              TargetCollarTraversalClass.secondCrossPort, hcentral]
        | some port =>
            fin_cases port <;>
              simp [TargetCollarTraversalClass.coordinateFinset,
                TargetCollarTraversalClass.firstCrossPort,
                TargetCollarTraversalClass.secondCrossPort,
                hzero, hone, htwo, hthree]

/-- A joint finite state retaining both the exact trail support and the
actual locally realizable terminal correction word. -/
abbrev TargetCollarTraversalRawState :=
  TargetCollarTraversalClass × IntrinsicCollarTerminalRawState

/-- The raw joint collar alphabet has exactly
`7 * 42768 = 299376` states. -/
theorem natCard_targetCollarTraversalRawState :
    Nat.card TargetCollarTraversalRawState = 299376 := by
  have traversalCard : Nat.card TargetCollarTraversalClass = 7 :=
    (@Nat.card_eq_fintype_card TargetCollarTraversalClass inferInstance).trans
      TargetCollarTraversalClass.card_eq_seven
  have terminalCard : Nat.card IntrinsicCollarTerminalRawState = 42768 :=
    (@Nat.card_eq_fintype_card IntrinsicCollarTerminalRawState
      intrinsicCollarTerminalRawStateFintype).trans
        card_intrinsicCollarTerminalRawState
  rw [Nat.card_prod, traversalCard, terminalCard]

/-- Every raw joint state retains the balanced nonzero terminal signature
of its color component. -/
theorem TargetCollarTraversalRawState.hasAdmissibleTerminalSignature
    (state : TargetCollarTraversalRawState) :
    state.2.2.1.HasAdmissibleTerminalSignature state.2.1 :=
  state.2.hasAdmissibleTerminalSignature

/-- The joint collar state after quotienting simultaneous renaming of the
three nonzero colors. -/
abbrev TargetCollarTraversalColorState :=
  TargetCollarTraversalClass × IntrinsicCollarTerminalColorState

/-- Color symmetry reduces the joint collar alphabet to exactly
`7 * 7392 = 51744` states. -/
theorem natCard_targetCollarTraversalColorState :
    Nat.card TargetCollarTraversalColorState = 51744 := by
  have traversalCard : Nat.card TargetCollarTraversalClass = 7 :=
    (@Nat.card_eq_fintype_card TargetCollarTraversalClass inferInstance).trans
      TargetCollarTraversalClass.card_eq_seven
  have terminalCard : Nat.card IntrinsicCollarTerminalColorState = 7392 :=
    (@Nat.card_eq_fintype_card IntrinsicCollarTerminalColorState
      intrinsicCollarTerminalColorStateFintype).trans
        card_intrinsicCollarTerminalColorState
  rw [Nat.card_prod, traversalCard, terminalCard]

/-- Forget color names in a raw joint state while retaining its geometry
and exact traversal class. -/
noncomputable def TargetCollarTraversalRawState.toColorState
    (state : TargetCollarTraversalRawState) :
    TargetCollarTraversalColorState :=
  (state.1, (state.2.1, Quotient.mk'' state.2.2))

/-- Every color-orbit joint state has a raw representative with the same
traversal class and overlap geometry. -/
theorem TargetCollarTraversalRawState.toColorState_surjective :
    Function.Surjective TargetCollarTraversalRawState.toColorState := by
  rintro ⟨traversalClass, profile, orbit⟩
  refine Quotient.inductionOn orbit ?_
  intro correctionState
  exact ⟨(traversalClass, (profile, correctionState)), rfl⟩

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairFusionTargetCollarTraversal

variable (traversal :
  CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- Membership of every target-collar edge in the ambient fusion trail is
exactly membership of its fixed coordinate in the certified support. -/
theorem targetCoordinate_mem_ambientTrail_edges_iff
    (coordinate : Option (Fin 4)) :
    (adjacentPairCollarCoordinateEdge collar.targetData coordinate).1 ∈
        traversal.contact.fusion.ambientTrail.edges ↔
      coordinate ∈ traversal.traversalClass.coordinateFinset := by
  have description :=
    TargetCollarTraversalClass.describes_coordinate_iff
      traversal.traversalClass
      (centralUsed :=
        (centralEdge collar.targetData).1 ∈
          traversal.contact.fusion.ambientTrail.edges)
      (boundaryUsed := fun port =>
        (boundaryEdge collar.targetData port).1 ∈
          traversal.contact.fusion.ambientTrail.edges)
      traversal.exactUsage coordinate
  cases coordinate with
  | none =>
      simpa only [adjacentPairCollarCoordinateEdge] using description
  | some port =>
      simpa only [adjacentPairCollarCoordinateEdge] using description

/-- The exact finite set of target-collar coordinates used by the ambient
fusion trail. -/
noncomputable def usedTargetCollarCoordinates :
    Finset (Option (Fin 4)) :=
  Finset.univ.filter fun coordinate =>
    (adjacentPairCollarCoordinateEdge collar.targetData coordinate).1 ∈
      traversal.contact.fusion.ambientTrail.edges

/-- The trail's computed target-collar support equals its classified
coordinate support. -/
theorem usedTargetCollarCoordinates_eq_coordinateFinset :
    traversal.usedTargetCollarCoordinates =
      traversal.traversalClass.coordinateFinset := by
  ext coordinate
  simp only [usedTargetCollarCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact traversal.targetCoordinate_mem_ambientTrail_edges_iff coordinate

/-- The number of target-collar edges used by the fusion trail is exactly
the count prescribed by its traversal class. -/
theorem card_usedTargetCollarCoordinates :
    traversal.usedTargetCollarCoordinates.card =
      traversal.traversalClass.edgeCount := by
  rw [traversal.usedTargetCollarCoordinates_eq_coordinateFinset,
    TargetCollarTraversalClass.card_coordinateFinset]

/-- The actual traversal together with the color data supporting its two
fused Kempe paths, represented in the raw joint alphabet. -/
noncomputable def rawState : TargetCollarTraversalRawState :=
  (traversal.traversalClass,
    collar.intrinsicCollarTerminalRawState
      traversal.contact.fusion.lineFusion.normal.canonicalState)

/-- The actual traversal in the color-name quotient of the joint finite
alphabet. -/
noncomputable def colorState : TargetCollarTraversalColorState :=
  (traversal.traversalClass,
    collar.intrinsicCollarTerminalColorState
      traversal.contact.fusion.lineFusion.normal.canonicalState)

/-- The realized raw state has the traversal's exact geometric class. -/
@[simp]
theorem rawState_fst : traversal.rawState.1 = traversal.traversalClass := rfl

/-- The realized color-orbit state has the traversal's exact geometric
class. -/
@[simp]
theorem colorState_fst :
    traversal.colorState.1 = traversal.traversalClass := rfl

/-- Forgetting color names in the realized raw state gives the realized
color-orbit state. -/
theorem rawState_toColorState :
    traversal.rawState.toColorState = traversal.colorState := rfl

/-- The realized raw state carries a balanced nonzero terminal signature. -/
theorem rawState_hasAdmissibleTerminalSignature :
    traversal.rawState.2.2.1.HasAdmissibleTerminalSignature
      traversal.rawState.2.1 :=
  TargetCollarTraversalRawState.hasAdmissibleTerminalSignature
    traversal.rawState

end CompanionCrossPairFusionTargetCollarTraversal

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
