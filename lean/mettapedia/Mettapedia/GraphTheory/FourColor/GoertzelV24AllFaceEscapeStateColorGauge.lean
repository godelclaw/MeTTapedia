import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarAffineColorMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutColor

/-!
# Canonical color gauges on all-face escape states

The rotation-ordered boundary of every admissible adjacent-pair escape
contains two distinct nonzero colors.  Together with their sum, these colors
form an ordered Tait triple and hence a canonical zero-fixing color frame.
The linear color action assigned to a reentry is the change between its two
endpoint frames.  Such changes telescope on every path, so a closed reentry
orbit has literal identity color-name holonomy.  This conclusion is
independent of the translation carried by each affine step.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace RotationOrderedFusionEscapeColorState

open CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle.IntrinsicShortTargetEscapeCollar

/-- The actual four-port word retained by an admissible escape-color state. -/
def boundaryWord
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    SquareBoundaryWord :=
  (RecoveredRotationOrderedData graphData minimal state.1.1
    ).degreeTwoBoundaryData.colorWord state.1.2

/-- Admissibility makes the retained boundary word the canonical adjacent
pair class. -/
theorem boundaryWord_adjacent01_23
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    (boundaryWord state).Adjacent01_23 := by
  rcases state.2 with
    ⟨_normal, _outcome, escape, hcoloring⟩
  rw [boundaryWord, hcoloring]
  exact escape.boundary_adjacent01_23

/-- Every entry of the retained boundary word is nonzero. -/
theorem boundaryWord_nonzero
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    (boundaryWord state).Nonzero := by
  let data := RecoveredRotationOrderedData graphData minimal state.1.1
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  exact ⟨
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell state.1.2 0,
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell state.1.2 1,
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell state.1.2 2,
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell state.1.2 3⟩

/-- The two ordered boundary colors and their sum are the three distinct
nonzero Tait colors. -/
theorem boundaryColorTriple
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    IsTaitColorTriple
      (boundaryWord state 0)
      (boundaryWord state 2)
      (boundaryWord state 0 + boundaryWord state 2) := by
  have hnonzero := boundaryWord_nonzero state
  have hadjacent := boundaryWord_adjacent01_23 state
  have hthird := third_color_properties
    hnonzero.1 hnonzero.2.2.1 hadjacent.2.2
  exact ⟨hnonzero.1, hnonzero.2.2.1, hthird.1,
    hadjacent.2.2, hthird.2.1.symm, hthird.2.2.symm⟩

/-- The canonical color-name gauge of an admissible state sends
`(red, blue, purple)` to the two rotation-ordered boundary colors and their
sum. -/
noncomputable def colorGauge
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    ColorNameSymmetry :=
  ⟨GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv
      (boundaryColorTriple state),
    GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_zero
      (boundaryColorTriple state)⟩

@[simp]
theorem colorGauge_red
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    colorGauge state • red = boundaryWord state 0 := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_red
    (boundaryColorTriple state)

@[simp]
theorem colorGauge_blue
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    colorGauge state • blue = boundaryWord state 2 := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_blue
    (boundaryColorTriple state)

@[simp]
theorem colorGauge_purple
    (state : AdmissibleState (graphData := graphData) (minimal := minimal)) :
    colorGauge state • purple =
      boundaryWord state 0 + boundaryWord state 2 := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_purple
    (boundaryColorTriple state)

/-- Linear color transport between two states is their canonical change of
gauge. -/
noncomputable def colorGaugeLinear
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    ColorNameSymmetry :=
  colorGauge target * (colorGauge source)⁻¹

/-- A translation may be assigned independently to every genuine reentry;
the closed linear-holonomy theorem below does not constrain it. -/
abbrev ReentryTranslation :=
  AdmissibleState (graphData := graphData) (minimal := minimal) →
    AdmissibleState (graphData := graphData) (minimal := minimal) → Color

/-- The affine step associated to a genuine reentry and an arbitrary
translation assignment. -/
noncomputable def colorGaugeAffineStep
    (translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal))
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    : Color × ColorNameSymmetry :=
  (translation source target, colorGaugeLinear source target)

/-- A nonempty reentry path together with its exact affine color word. -/
inductive ReentryColorGaugeWord
    (translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal)) :
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    List (Color × ColorNameSymmetry) → Prop
  | single {source target}
      (step : AdmissibleReentry source target) :
      ReentryColorGaugeWord translation source target
        [colorGaugeAffineStep translation (source := source) (target := target)]
  | tail {source middle target word}
      (path : ReentryColorGaugeWord translation source middle word)
      (step : AdmissibleReentry middle target) :
      ReentryColorGaugeWord translation source target
        (word ++ [colorGaugeAffineStep translation
          (source := middle) (target := target)])

namespace ReentryColorGaugeWord

/-- Every nonempty genuine reentry path carries its affine gauge word. -/
theorem exists_of_transGen
    (translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal))
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (path : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      source target) :
    ∃ word, ReentryColorGaugeWord translation source target word := by
  induction path with
  | single step =>
      exact ⟨_, .single step⟩
  | tail _ step ih =>
      rcases ih with ⟨word, hword⟩
      exact ⟨_, .tail hword step⟩

/-- The linear action of a reentry word is exactly the endpoint gauge
change; all intermediate frames cancel. -/
theorem linear_eq_endpointGauge
    {translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal)}
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    {word : List (Color × ColorNameSymmetry)}
    (path : ReentryColorGaugeWord translation source target word) :
    colorAffineWordLinear word =
      colorGauge target * (colorGauge source)⁻¹ := by
  induction path with
  | single step =>
      simp [colorGaugeAffineStep, colorGaugeLinear,
        colorAffineWordLinear]
  | tail path step ih =>
      rw [colorAffineWordLinear_append, ih]
      simp [colorGaugeAffineStep, colorGaugeLinear,
        colorAffineWordLinear, mul_assoc]

/-- A closed reentry word has literal identity color-name holonomy. -/
theorem linear_eq_one_of_closed
    {translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal)}
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {word : List (Color × ColorNameSymmetry)}
    (path : ReentryColorGaugeWord translation state state word) :
    colorAffineWordLinear word = 1 := by
  rw [path.linear_eq_endpointGauge]
  exact mul_inv_cancel (colorGauge state)

/-- Consequently every closed genuine reentry word acts by an even
permutation of the four colors, for every choice of translations. -/
theorem transfer_sign_eq_one_of_closed
    {translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal)}
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {word : List (Color × ColorNameSymmetry)}
    (path : ReentryColorGaugeWord translation state state word) :
    Equiv.Perm.sign (colorAffineWordTransfer word) = 1 :=
  colorAffineWordTransfer_sign_eq_one_of_linear_eq_one
    path.linear_eq_one_of_closed

/-- Every nonempty closed orbit of actual escape-color states therefore
supplies a closed affine word with identity linear holonomy and even total
color action. -/
theorem exists_closed_word_of_reentry_cycle
    (translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal))
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    (cycle : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      state state) :
    ∃ word : List (Color × ColorNameSymmetry),
      ReentryColorGaugeWord translation state state word ∧
        colorAffineWordLinear word = 1 ∧
          Equiv.Perm.sign (colorAffineWordTransfer word) = 1 := by
  rcases exists_of_transGen translation cycle with ⟨word, hword⟩
  exact ⟨word, hword, hword.linear_eq_one_of_closed,
    hword.transfer_sign_eq_one_of_closed⟩

/-- An odd finite monodromy cannot be a coordinate conjugate of a closed
reentry gauge word. -/
theorem oddMonodromy_ne_closedGaugeWordConjugate
    {translation : ReentryTranslation
      (graphData := graphData) (minimal := minimal)}
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {word : List (Color × ColorNameSymmetry)}
    (path : ReentryColorGaugeWord translation state state word)
    {Support : Type*} [Fintype Support] [DecidableEq Support]
    (coordinates : Color ≃ Support)
    (monodromy : Equiv.Perm Support)
    (hodd : Equiv.Perm.sign monodromy = -1) :
    monodromy ≠ coordinates.permCongr (colorAffineWordTransfer word) := by
  intro heq
  have hsign := congrArg Equiv.Perm.sign heq
  rw [hodd, Equiv.Perm.sign_permCongr,
    path.transfer_sign_eq_one_of_closed] at hsign
  norm_num at hsign

end ReentryColorGaugeWord

end RotationOrderedFusionEscapeColorState

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing alias for the closed-gauge parity theorem. -/

alias GoertzelV24AllFaceEscapeStateColorGauge.transfer_sign_eq_one_of_closed :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.RotationOrderedFusionEscapeColorState.ReentryColorGaugeWord.transfer_sign_eq_one_of_closed

end Mettapedia.GraphTheory.FourColor
