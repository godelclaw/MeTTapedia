import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionKempeRealization
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionLens

/-! Exact four-port action of a realized singleton Kempe component. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutKempeEscape
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

/-- Equal conditional swap outputs of distinct inputs force both inputs to
belong to the swapped pair and exactly one switch to be active. -/
theorem selected_and_switch_iff_not_of_conditionalSwap_eq
    {a b x y : Color} (hxy : x ≠ y)
    (switchX switchY : Prop) [Decidable switchX] [Decidable switchY]
    (heq : (if switchX then Equiv.swap a b x else x) =
      if switchY then Equiv.swap a b y else y) :
    (x = a ∨ x = b) ∧ (y = a ∨ y = b) ∧
      (switchX ↔ ¬ switchY) := by
  by_cases hxSwitch : switchX <;> by_cases hySwitch : switchY
  · simp only [hxSwitch, hySwitch, if_true] at heq
    exact False.elim (hxy ((Equiv.swap a b).injective heq))
  · simp only [hxSwitch, if_true, hySwitch, if_false] at heq
    have hxMoved : Equiv.swap a b x ≠ x := by
      intro hfixed
      exact hxy (hfixed.symm.trans heq)
    have hxSelected : x = a ∨ x = b :=
      (Equiv.swap_apply_ne_self_iff.mp hxMoved).2
    have hySelected : y = a ∨ y = b := by
      rcases hxSelected with hxa | hxb
      · apply Or.inr
        calc
          y = Equiv.swap a b x := heq.symm
          _ = Equiv.swap a b a := congrArg (Equiv.swap a b) hxa
          _ = b := Equiv.swap_apply_left a b
      · apply Or.inl
        calc
          y = Equiv.swap a b x := heq.symm
          _ = Equiv.swap a b b := congrArg (Equiv.swap a b) hxb
          _ = a := Equiv.swap_apply_right a b
    exact ⟨hxSelected, hySelected, iff_of_true hxSwitch hySwitch⟩
  · simp only [hxSwitch, if_false, hySwitch, if_true] at heq
    have hyMoved : Equiv.swap a b y ≠ y := by
      intro hfixed
      exact hxy (heq.trans hfixed)
    have hySelected : y = a ∨ y = b :=
      (Equiv.swap_apply_ne_self_iff.mp hyMoved).2
    have hxSelected : x = a ∨ x = b := by
      rcases hySelected with hya | hyb
      · apply Or.inr
        calc
          x = Equiv.swap a b y := heq
          _ = Equiv.swap a b a := congrArg (Equiv.swap a b) hya
          _ = b := Equiv.swap_apply_left a b
      · apply Or.inl
        calc
          x = Equiv.swap a b y := heq
          _ = Equiv.swap a b b := congrArg (Equiv.swap a b) hyb
          _ = a := Equiv.swap_apply_right a b
    exact ⟨hxSelected, hySelected,
      iff_of_false hxSwitch (not_not.mpr hySwitch)⟩
  · simp only [hxSwitch, hySwitch, if_false] at heq
    exact False.elim (hxy heq)

/-- For a selected input color, two conditional swaps agree exactly when
their switch propositions agree. -/
theorem conditionalSwap_eq_iff_switch_iff_of_selected
    {a b x : Color} (hab : ValidColorPair a b) (hx : x = a ∨ x = b)
    (first second : Prop) [Decidable first] [Decidable second] :
    ((if first then Equiv.swap a b x else x) =
        if second then Equiv.swap a b x else x) ↔
      (first ↔ second) := by
  have hmoved := equivSwap_ne_self_of_validColorPair hab hx
  by_cases hfirst : first <;> by_cases hsecond : second <;>
    simp [hfirst, hsecond, hmoved, Ne.symm hmoved]

/-- A component switch taking the canonical adjacent-pair word to an
all-equal word acts on exactly one of the two complete same-side port pairs. -/
theorem boundaryKempeSwap_adjacent01_23_allEqual_support_eq_sameSide
    (a b : Color) (support : Finset (Fin 4)) (word : SquareBoundaryWord)
    (hab : ValidColorPair a b) (hadjacent : word.Adjacent01_23)
    (hallEqual :
      SquareBoundaryWord.AllEqual
        (boundaryKempeSwap a b support word)) :
    support = {0, 1} ∨ support = {2, 3} := by
  classical
  let switched := boundaryKempeSwap a b support word
  have hswitchedZeroTwo : switched 0 = switched 2 :=
    hallEqual.1.trans hallEqual.2.1
  have hrepresentatives :
      (word 0 = a ∨ word 0 = b) ∧
        (word 2 = a ∨ word 2 = b) ∧
        (0 ∈ support ↔ 2 ∉ support) := by
    apply selected_and_switch_iff_not_of_conditionalSwap_eq
      hadjacent.2.2 (0 ∈ support) (2 ∈ support)
    simpa only [switched, boundaryKempeSwap] using hswitchedZeroTwo
  have hzeroOne : 0 ∈ support ↔ 1 ∈ support := by
    apply (conditionalSwap_eq_iff_switch_iff_of_selected
      hab hrepresentatives.1 (0 ∈ support) (1 ∈ support)).1
    have heq := hallEqual.1
    change switched 0 = switched 1 at heq
    simpa only [switched, boundaryKempeSwap, hadjacent.1] using heq
  have htwoThree : 2 ∈ support ↔ 3 ∈ support := by
    apply (conditionalSwap_eq_iff_switch_iff_of_selected
      hab hrepresentatives.2.1 (2 ∈ support) (3 ∈ support)).1
    have heq := hallEqual.2.2
    change switched 2 = switched 3 at heq
    simpa only [switched, boundaryKempeSwap, hadjacent.2.1] using heq
  by_cases hzero : 0 ∈ support
  · have hone : 1 ∈ support := hzeroOne.1 hzero
    have htwo : 2 ∉ support := hrepresentatives.2.2.1 hzero
    have hthree : 3 ∉ support := fun hthree =>
      htwo (htwoThree.2 hthree)
    exact Or.inl (by
      ext port
      fin_cases port <;> simp [hzero, hone, htwo, hthree])
  · have htwo : 2 ∈ support := by
      by_contra htwo
      exact hzero (hrepresentatives.2.2.2 htwo)
    have hthree : 3 ∈ support := htwoThree.1 htwo
    have hone : 1 ∉ support := fun hone =>
      hzero (hzeroOne.2 hone)
    exact Or.inr (by
      ext port
      fin_cases port <;> simp [hzero, hone, htwo, hthree])

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
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
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace SingletonCompanionTransferPath

variable {transfer : SingletonCompanionTransferPath collar sourceEscape}

namespace SourceDeletionKempeRealization

variable (realization : transfer.SourceDeletionKempeRealization)

/-- In the all-equal branch, the realized graph component meets exactly one
complete source side: ports `0,1` or ports `2,3`. -/
theorem kempePortSupport_eq_sameSide_of_boundary_allEqual
    (hallEqual : realization.boundaryWord.AllEqual) :
    collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {0, 1} ∨
      collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {2, 3} := by
  let support := collar.sourceData.degreeTwoBoundaryData.kempePortSupport
    sourceEscape.coloring
    (crossFaceZeroColor transfer.coordinate) realization.companion
    realization.component
  apply boundaryKempeSwap_adjacent01_23_allEqual_support_eq_sameSide
    (crossFaceZeroColor transfer.coordinate) realization.companion
      support
      (collar.sourceData.degreeTwoBoundaryData.colorWord
        sourceEscape.coloring)
      realization.validColorPair sourceEscape.boundary_adjacent01_23
  rw [realization.boundaryWord_eq_boundaryKempeSwap] at hallEqual
  simpa only [support] using hallEqual

/-- The all-equal alternative therefore retains an exact same-side source
connector together with target agreement on every singleton support edge. -/
theorem sameSideConnector_of_boundary_allEqual
    (hallEqual : realization.boundaryWord.AllEqual) :
    (collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {0, 1} ∨
      collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {2, 3}) ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        SourceDeletionKempeRealization.coloring transfer realization
            (collar.commonEdgeInSource edge.1) =
          collar.targetCommonColoring edge.1 :=
  ⟨realization.kempePortSupport_eq_sameSide_of_boundary_allEqual
      hallEqual,
    realization.agrees_on_support⟩

/-- The all-equal realization immediately supplies the two existing
same-side even Kempe fusion lenses.  Thus this branch rejoins the fusion
machinery with its actual realized coloring, rather than a fresh coloring
hypothesis. -/
theorem exists_evenKempeFusionLenses_of_boundary_allEqual
    (hallEqual : realization.boundaryWord.AllEqual) :
    ∃ constant other : Color,
      ValidColorPair constant other ∧
      (∀ port : Fin 4,
        collar.sourceData.degreeTwoBoundaryData.colorWord
            (SourceDeletionKempeRealization.coloring transfer realization)
              port = constant) ∧
      Nonempty
        (collar.sourceData.degreeTwoBoundaryData.EvenKempeFusionLens
          (SourceDeletionKempeRealization.coloring transfer realization)
          constant other (constant + other) 0 1) ∧
      Nonempty
        (collar.sourceData.degreeTwoBoundaryData.EvenKempeFusionLens
          (SourceDeletionKempeRealization.coloring transfer realization)
          constant other (constant + other) 2 3) := by
  let realizedColoring :=
    SourceDeletionKempeRealization.coloring transfer realization
  let constant := collar.sourceData.degreeTwoBoundaryData.colorWord
    realizedColoring 0
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hwell :=
    collar.sourceData.degreeTwoBoundaryData_wellFormed hcubic
  have hconstantNonzero : constant ≠ 0 :=
    collar.sourceData.degreeTwoBoundaryData.colorWord_ne_zero
      hwell realizedColoring 0
  have hconstant : ∀ port : Fin 4,
      collar.sourceData.degreeTwoBoundaryData.colorWord
          realizedColoring port = constant := by
    intro port
    fin_cases port
    · rfl
    · exact hallEqual.1.symm
    · exact (hallEqual.1.trans hallEqual.2.1).symm
    · exact (hallEqual.1.trans hallEqual.2.1 |>.trans
        hallEqual.2.2).symm
  rcases exists_validColorPair_with_first_of_ne_zero hconstantNonzero with
    ⟨other, hpair⟩
  have hlenses :=
    collar.sourceData.exists_two_evenKempeFusionLenses_of_constant_colorWord
      hcubic hnotColorable realizedColoring realization.isTait
        hpair hconstant
  exact ⟨constant, other, hpair, hconstant, hlenses⟩

end SourceDeletionKempeRealization

/-- Complete data retained by the all-equal straight branch: the realized
same-base swap, its exact one-side source support, and the two even fusion
lenses on the resulting constant boundary state. -/
structure AllEqualSourceFusionConnector where
  realization : transfer.SourceDeletionKempeRealization
  boundary_allEqual : realization.boundaryWord.AllEqual
  sourceSupport_sameSide :
    collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {0, 1} ∨
      collar.sourceData.degreeTwoBoundaryData.kempePortSupport
          sourceEscape.coloring
          (crossFaceZeroColor transfer.coordinate) realization.companion
          realization.component = {2, 3}
  constant : Color
  other : Color
  validPair : ValidColorPair constant other
  boundary_constant : ∀ port : Fin 4,
    collar.sourceData.degreeTwoBoundaryData.colorWord
        (SourceDeletionKempeRealization.coloring transfer realization) port =
      constant
  lens01 : Nonempty
    (collar.sourceData.degreeTwoBoundaryData.EvenKempeFusionLens
      (SourceDeletionKempeRealization.coloring transfer realization)
      constant other (constant + other) 0 1)
  lens23 : Nonempty
    (collar.sourceData.degreeTwoBoundaryData.EvenKempeFusionLens
      (SourceDeletionKempeRealization.coloring transfer realization)
      constant other (constant + other) 2 3)

/-- Complete data retained by the adjacent straight branch: the realized
same-base swap and the canonical escape package whose coloring is that swap. -/
structure AdjacentSourceOrbitReentry where
  realization : transfer.SourceDeletionKempeRealization
  successor : sourceNormal.KempeOrbitAdjacentEscape
  coloring_eq : successor.coloring = realization.coloring

/-- The straight singleton branch now has two fully constructed outcomes:
an all-equal same-side fusion connector, or a canonical adjacent escape in
the same source Kempe orbit. -/
theorem allEqualFusionConnector_or_adjacentEscape_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    Nonempty transfer.AllEqualSourceFusionConnector ∨
      Nonempty transfer.AdjacentSourceOrbitReentry := by
  rcases transfer.exists_allEqualRealization_or_adjacentEscape_of_straight
      hstraight with ⟨realization, hallEqual | hadjacent⟩
  · apply Or.inl
    rcases realization.exists_evenKempeFusionLenses_of_boundary_allEqual
        hallEqual with
      ⟨constant, other, hpair, hconstant, hlens01, hlens23⟩
    exact ⟨{
      realization := realization
      boundary_allEqual := hallEqual
      sourceSupport_sameSide :=
        realization.kempePortSupport_eq_sameSide_of_boundary_allEqual
          hallEqual
      constant := constant
      other := other
      validPair := hpair
      boundary_constant := hconstant
      lens01 := hlens01
      lens23 := hlens23 }⟩
  · rcases hadjacent with ⟨successor, heq⟩
    exact Or.inr ⟨{
      realization := realization
      successor := successor
      coloring_eq := heq }⟩

/-- A located companion change together with its exact position in the
support word and its resolved source-port, target-port, or transverse
cross-channel geometry. -/
structure ResolvedCompanionChange where
  before : List transfer.SupportEdge
  first : transfer.SupportEdge
  second : transfer.SupportEdge
  after : List transfer.SupportEdge
  firstSecond : collar.commonCore.lineGraph.Adj first.1 second.1
  word_eq : transfer.supportEdgeWord =
    before ++ first :: second :: after
  companion_ne :
    (transfer.supportEdgeState first).companionColor ≠
      (transfer.supportEdgeState second).companionColor
  location :
    (∃ sourcePort : Fin 4,
        SimpleGraph.lineGraphCommonVertex firstSecond =
          collar.sourcePortInCommonCore sourcePort) ∨
      (∃ targetPort : Fin 4,
        SimpleGraph.lineGraphCommonVertex firstSecond =
          collar.targetPortInCommonCore targetPort) ∨
      ∃ thirdEdge : collar.commonCore.edgeSet,
        collar.commonCore.lineGraph.Adj first.1 thirdEdge ∧
          collar.commonCore.lineGraph.Adj second.1 thirdEdge ∧
          collar.sourceCommonColoring sourceEscape thirdEdge +
              collar.targetCommonColoring thirdEdge =
            crossFaceZeroColor transfer.coordinate

/-- Exhaustive local outcome for the singleton companion trail.  Every
instance constructs an all-equal fusion connector, an adjacent source-orbit
reentry, or one explicitly resolved companion-change collar event. -/
theorem allEqualFusionConnector_or_adjacentReentry_or_resolvedChange :
    Nonempty transfer.AllEqualSourceFusionConnector ∨
      Nonempty transfer.AdjacentSourceOrbitReentry ∨
      Nonempty transfer.ResolvedCompanionChange := by
  rcases transfer.straightChain_or_exists_changedAdjacent with
    hstraight | ⟨before, first, second, after, hword,
      hfirstSecond, hcompanion⟩
  · rcases transfer.allEqualFusionConnector_or_adjacentEscape_of_straight
      hstraight with hallEqual | hadjacent
    · exact Or.inl hallEqual
    · exact Or.inr (Or.inl hadjacent)
  · apply Or.inr
    apply Or.inr
    exact ⟨{
      before := before
      first := first
      second := second
      after := after
      firstSecond := hfirstSecond
      word_eq := hword
      companion_ne := hcompanion
      location :=
        transfer.changedAdjacent_boundaryPort_or_transverseEmission
          first second hfirstSecond hcompanion }⟩

end SingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
