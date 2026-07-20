import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarState

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

/-- The local completion matrix before forgetting its two generating
boundary words and bridge color. -/
abbrev TargetCollarLocalMatrixState :=
  ↥(canonicalOwnBoundaryWords ×ˢ bridgeExtensionWordColors)

/-- The exact collar traversal class together with its local completion
matrix. -/
abbrev TargetCollarTraversalMatrixState :=
  TargetCollarTraversalClass × TargetCollarLocalMatrixState

/-- The local matrix contains exactly `6 * 12 = 72` states. -/
theorem card_targetCollarLocalMatrixState :
    Fintype.card TargetCollarLocalMatrixState = 72 := by
  rw [Fintype.card_coe, Finset.card_product,
    card_canonicalOwnBoundaryWords, card_bridgeExtensionWordColors]

/-- Adjoining the seven trail supports gives exactly 504 matrix states. -/
theorem card_targetCollarTraversalMatrixState :
    Fintype.card TargetCollarTraversalMatrixState = 504 := by
  rw [Fintype.card_prod, TargetCollarTraversalClass.card_eq_seven,
    card_targetCollarLocalMatrixState]

namespace TargetCollarLocalMatrixState

/-- The canonical boundary word of the deleted target pair. -/
def ownBoundaryWord (state : TargetCollarLocalMatrixState) :
    SquareBoundaryWord := state.1.1

/-- The target boundary word read in the source-pair coloring. -/
def crossBoundaryWord (state : TargetCollarLocalMatrixState) :
    SquareBoundaryWord := state.1.2.1

/-- The target central-edge color read in the source-pair coloring. -/
def bridgeColor (state : TargetCollarLocalMatrixState) : Color :=
  state.1.2.2

/-- A matrix state generates its five-coordinate correction half-word. -/
def correctionHalfWord (state : TargetCollarLocalMatrixState) :
    IntrinsicCollarCorrectionHalfWord :=
  localCorrectionHalfWord state.ownBoundaryWord
    state.crossBoundaryWord state.bridgeColor

/-- The own boundary word is nonzero and has the canonical adjacent
pairing. -/
theorem ownBoundaryWord_spec (state : TargetCollarLocalMatrixState) :
    state.ownBoundaryWord.Nonzero ∧
      state.ownBoundaryWord.Adjacent01_23 := by
  exact (mem_canonicalOwnBoundaryWords_iff state.ownBoundaryWord).1
    (Finset.mem_product.mp state.2).1

/-- The cross word and bridge color really restore the two target
vertices. -/
theorem bridgeExtension (state : TargetCollarLocalMatrixState) :
    IsTwoVertexBridgeExtension state.crossBoundaryWord state.bridgeColor := by
  exact (mem_bridgeExtensionWordColors_iff
    state.crossBoundaryWord state.bridgeColor).1
      (Finset.mem_product.mp state.2).2

/-- Forgetting the matrix generators gives a certified member of the
thirty-six-state correction-half alphabet. -/
noncomputable def toCorrectionHalfState
    (state : TargetCollarLocalMatrixState) :
    LocallyRealizableCorrectionHalfState :=
  ⟨state.correctionHalfWord,
    localCorrectionHalfWord_mem _ _ _
      state.ownBoundaryWord_spec.1 state.ownBoundaryWord_spec.2
      state.bridgeExtension⟩

/-- Every locally realizable correction half has a generating local
matrix. -/
theorem toCorrectionHalfState_surjective :
    Function.Surjective toCorrectionHalfState := by
  rintro ⟨word, hword⟩
  rw [locallyRealizableCorrectionHalfWords, Finset.mem_image] at hword
  rcases hword with ⟨data, hdata, rfl⟩
  exact ⟨⟨data, hdata⟩, rfl⟩

end TargetCollarLocalMatrixState

/-- The source coloring on a target-collar coordinate: the bridge at the
central coordinate and the cross-boundary word at the four ports. -/
def targetCollarMatrixColorAt
    (cross : SquareBoundaryWord) (bridge : Color) :
    Option (Fin 4) → Color
  | none => bridge
  | some port => cross port

/-- The colors seen on the exact support of a collar traversal class. -/
def TargetCollarTraversalClass.usedColorFinset
    (traversalClass : TargetCollarTraversalClass)
    (cross : SquareBoundaryWord) (bridge : Color) : Finset Color :=
  traversalClass.coordinateFinset.image
    (targetCollarMatrixColorAt cross bridge)

/-- A seam is a central traversal whose selected boundary edges have
different colors. -/
def TargetCollarTraversalClass.HasColorSeam
    (traversalClass : TargetCollarTraversalClass)
    (cross : SquareBoundaryWord) : Prop :=
  match traversalClass with
  | .cross firstUsesOne secondUsesThree =>
      cross (TargetCollarTraversalClass.firstCrossPort firstUsesOne) ≠
        cross (TargetCollarTraversalClass.secondCrossPort secondUsesThree)
  | _ => False

instance (traversalClass : TargetCollarTraversalClass)
    (cross : SquareBoundaryWord) :
    Decidable (traversalClass.HasColorSeam cross) := by
  cases traversalClass <;> simp only [TargetCollarTraversalClass.HasColorSeam] <;>
    infer_instance

/-- A locally extendable target collar uses exactly two colors on every
pair traversal and every unbroken central traversal, and exactly three
colors at a seam. -/
theorem TargetCollarTraversalClass.card_usedColorFinset
    (traversalClass : TargetCollarTraversalClass)
    (cross : SquareBoundaryWord) (bridge : Color)
    (hextension : IsTwoVertexBridgeExtension cross bridge) :
    (traversalClass.usedColorFinset cross bridge).card =
      if traversalClass.HasColorSeam cross then 3 else 2 := by
  cases traversalClass <;> decide +revert

/-- Every color used on an extendable target collar is a nonzero Tait
color. -/
theorem TargetCollarTraversalClass.mem_usedColorFinset_ne_zero
    (traversalClass : TargetCollarTraversalClass)
    (cross : SquareBoundaryWord) (bridge color : Color)
    (hextension : IsTwoVertexBridgeExtension cross bridge)
    (hcolor : color ∈ traversalClass.usedColorFinset cross bridge) :
    color ≠ 0 := by
  cases traversalClass <;> decide +revert

namespace TargetCollarTraversalMatrixState

/-- The colors used by the traversal support in a matrix state. -/
def usedColorFinset (state : TargetCollarTraversalMatrixState) :
    Finset Color :=
  state.1.usedColorFinset state.2.crossBoundaryWord state.2.bridgeColor

/-- Whether the matrix state contains the unique tricolored central
passage. -/
def HasColorSeam (state : TargetCollarTraversalMatrixState) : Prop :=
  state.1.HasColorSeam state.2.crossBoundaryWord

instance (state : TargetCollarTraversalMatrixState) :
    Decidable state.HasColorSeam := by
  change Decidable (state.1.HasColorSeam state.2.crossBoundaryWord)
  infer_instance

/-- Every one of the 504 matrix states obeys the exact two-color versus
three-color seam law. -/
theorem card_usedColorFinset (state : TargetCollarTraversalMatrixState) :
    state.usedColorFinset.card = if state.HasColorSeam then 3 else 2 :=
  by
    have hcard :=
      state.1.card_usedColorFinset state.2.crossBoundaryWord
        state.2.bridgeColor state.2.bridgeExtension
    by_cases hseam : state.1.HasColorSeam state.2.crossBoundaryWord
    · simpa [usedColorFinset, HasColorSeam, hseam] using hcard
    · simpa [usedColorFinset, HasColorSeam, hseam] using hcard

/-- Every color occurring on a matrix-state traversal is nonzero. -/
theorem mem_usedColorFinset_ne_zero
    (state : TargetCollarTraversalMatrixState) (color : Color)
    (hcolor : color ∈ state.usedColorFinset) : color ≠ 0 :=
  state.1.mem_usedColorFinset_ne_zero state.2.crossBoundaryWord
    state.2.bridgeColor color state.2.bridgeExtension hcolor

end TargetCollarTraversalMatrixState

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

/-- The genuine local completion matrix at the target collar, retaining
the two boundary words and bridge color that generate its correction
half-word. -/
noncomputable def localMatrixState : TargetCollarLocalMatrixState :=
  ⟨(collar.targetData.degreeTwoBoundaryData.colorWord
      collar.targetEscape.coloring,
    (collar.targetBoundaryWordInSource
        traversal.contact.fusion.lineFusion.normal.canonicalState,
      collar.targetBridgeColorInSource
        traversal.contact.fusion.lineFusion.normal.canonicalState)),
    Finset.mem_product.mpr ⟨
      (mem_canonicalOwnBoundaryWords_iff _).2 ⟨
        collar.targetOwnBoundaryWord_nonzero,
        collar.targetEscape.boundary_adjacent01_23⟩,
      (mem_bridgeExtensionWordColors_iff _ _).2
        (collar.targetBridgeExtensionInSource
          traversal.contact.fusion.lineFusion.normal.canonicalState)⟩⟩

/-- The genuine 504-state matrix record of a target-collar traversal. -/
noncomputable def matrixState : TargetCollarTraversalMatrixState :=
  (traversal.traversalClass, traversal.localMatrixState)

/-- The matrix retains the exact classified geometric support. -/
@[simp]
theorem matrixState_fst :
    traversal.matrixState.1 = traversal.traversalClass := rfl

/-- The matrix generator reconstructs the actual target correction
half-word definitionally. -/
theorem localMatrixState_correctionHalfWord :
    traversal.localMatrixState.correctionHalfWord =
      collar.targetLocalCorrectionHalfWord
        traversal.contact.fusion.lineFusion.normal.canonicalState := rfl

/-- Restricting the previously realized raw correction word to the target
collar recovers exactly the half-word generated by the matrix state. -/
theorem targetHalfWord_rawState_eq_localMatrixState :
    targetHalfWordOfCorrectionWord traversal.rawState.2.2.1 =
      traversal.localMatrixState.correctionHalfWord := by
  change targetHalfWordOfCorrectionWord
      (collar.intrinsicCollarCorrectionWord
        traversal.contact.fusion.lineFusion.normal.canonicalState) =
    traversal.localMatrixState.correctionHalfWord
  rw [
    collar.intrinsicCollarCorrectionWord_eq_correctionWordOfHalfWords,
    targetHalfWordOfCorrectionWord_correctionWordOfHalfWords,
    traversal.localMatrixState_correctionHalfWord]

/-- On each of the five target-collar coordinates, the matrix color is
literally the color supplied by the canonical source-pair coloring. -/
theorem targetCollarMatrixColorAt_eq_canonicalStateColor
    (coordinate : Option (Fin 4)) :
    targetCollarMatrixColorAt
        traversal.localMatrixState.crossBoundaryWord
        traversal.localMatrixState.bridgeColor coordinate =
      traversal.contact.fusion.lineFusion.normal.canonicalState.coloring
        (match coordinate with
        | none => collar.targetCentralInSource
        | some port => collar.targetBoundaryInSource port) := by
  cases coordinate <;> rfl

/-- The colors of the actually used target-collar coordinates in the
canonical source-pair coloring. -/
noncomputable def usedTargetCollarColors : Finset Color :=
  traversal.usedTargetCollarCoordinates.image fun coordinate =>
    traversal.contact.fusion.lineFusion.normal.canonicalState.coloring
      (match coordinate with
      | none => collar.targetCentralInSource
      | some port => collar.targetBoundaryInSource port)

/-- The matrix-state color support is exactly the color set on the actual
used target-collar edges. -/
theorem usedTargetCollarColors_eq_matrixState_usedColorFinset :
    traversal.usedTargetCollarColors =
      traversal.matrixState.usedColorFinset := by
  rw [usedTargetCollarColors,
    traversal.usedTargetCollarCoordinates_eq_coordinateFinset]
  apply Finset.image_congr
  intro coordinate _
  exact (traversal.targetCollarMatrixColorAt_eq_canonicalStateColor
    coordinate).symm

/-- The actual target-collar traversal is bicolored except precisely at a
three-color central seam. -/
theorem matrixState_card_usedColorFinset :
    traversal.matrixState.usedColorFinset.card =
      if traversal.matrixState.HasColorSeam then 3 else 2 :=
  traversal.matrixState.card_usedColorFinset

/-- The canonical source coloring therefore uses two colors on the
actual collar intersection, except for the exact three-color seam. -/
theorem card_usedTargetCollarColors :
    traversal.usedTargetCollarColors.card =
      if traversal.matrixState.HasColorSeam then 3 else 2 := by
  rw [traversal.usedTargetCollarColors_eq_matrixState_usedColorFinset]
  exact traversal.matrixState_card_usedColorFinset

/-- Every actual source-coloring color on the used target collar is
nonzero. -/
theorem matrixState_mem_usedColorFinset_ne_zero
    (color : Color) (hcolor : color ∈ traversal.matrixState.usedColorFinset) :
    color ≠ 0 :=
  traversal.matrixState.mem_usedColorFinset_ne_zero color hcolor

/-- Every color on an actually used target-collar edge is nonzero. -/
theorem usedTargetCollarColors_mem_ne_zero
    (color : Color) (hcolor : color ∈ traversal.usedTargetCollarColors) :
    color ≠ 0 := by
  rw [traversal.usedTargetCollarColors_eq_matrixState_usedColorFinset] at hcolor
  exact traversal.matrixState_mem_usedColorFinset_ne_zero color hcolor

end CompanionCrossPairFusionTargetCollarTraversal

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
