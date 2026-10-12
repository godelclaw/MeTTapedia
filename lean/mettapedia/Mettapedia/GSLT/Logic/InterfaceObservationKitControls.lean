import Mettapedia.GSLT.Logic.InterfaceObservationKitRestriction
import Mettapedia.GSLT.Logic.InterfaceModalAdequacyControls

/-!
# Actual changing interfaces and a strict observer ceiling

The independently checked parallel-arrow reaction consumes one agent and
returns another. Its kit carries the actual source-changing and identity
context labels. One round separates the agents, while zero rounds do not.

A second kit retains contexts starting at the original interface. It still
admits the cross-interface firing, but has no observer at the result
interface. The returned agents then agree at every admitted depth although
an unrestricted actual diamond separates them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RedexRelativeCongruence InterfaceModalAdequacyControls

def fullKit : Kit WalkingParallelPair WalkingParallelPair where
  object := id
  Label first last := first ⟶ last
  context label := label

instance fullKit_labels_finite (first last : WalkingParallelPair) :
    Finite (fullKit.Label first last) := by
  change Finite (first ⟶ last)
  infer_instance

theorem actual_cross_interface_readout :
    Holds fullKit WalkingParallelPair.zero rules
      (.diamond WalkingParallelPairHom.left .top) (𝟙 WalkingParallelPair.zero) :=
  ⟨WalkingParallelPairHom.right, actual_cross_interface_firing, True.intro⟩

theorem zero_rounds_agree_but_one_round_separates :
    Rounds fullKit WalkingParallelPair.zero rules 0 WalkingParallelPairHom.left WalkingParallelPairHom.right ∧
      ¬ Rounds fullKit WalkingParallelPair.zero rules 1 WalkingParallelPairHom.left
        WalkingParallelPairHom.right := by
  refine ⟨True.intro, ?_⟩
  intro related
  obtain ⟨matched, impossible, _⟩ := related.1 WalkingParallelPair.one (𝟙 WalkingParallelPair.one)
    WalkingParallelPairHom.right actual_nonidentity_result_firing
  exact the_result_agent_cannot_match_the_firing matched impossible

theorem a_bounded_formula_and_actual_rounds_make_the_same_distinction :
    ¬ LogicallyEquivalent fullKit WalkingParallelPair.zero rules 1
      WalkingParallelPairHom.left WalkingParallelPairHom.right := by
  intro related
  exact zero_rounds_agree_but_one_round_separates.2
    ((bounded_adequacy fullKit WalkingParallelPair.zero rules 1 _ _).mp related)

theorem independent_characteristic_test_separates :
    Holds fullKit WalkingParallelPair.zero rules
      (characteristic fullKit WalkingParallelPair.zero rules 1 WalkingParallelPairHom.left)
        WalkingParallelPairHom.left ∧
      ¬ Holds fullKit WalkingParallelPair.zero rules
        (characteristic fullKit WalkingParallelPair.zero rules 1 WalkingParallelPairHom.left)
          WalkingParallelPairHom.right := by
  constructor
  · exact (characteristic_readout fullKit WalkingParallelPair.zero rules 1 _ _).mpr
      ((round_comparison fullKit WalkingParallelPair.zero rules 1 _ _).mpr
        (HennessyMilner.FiniteDepth.rounds_refl _ _ _))
  · intro held
    exact zero_rounds_agree_but_one_round_separates.2
      ((characteristic_readout fullKit WalkingParallelPair.zero rules 1 _ _).mp held)

def startsAtOriginal : ∀ {first last : WalkingParallelPair}, fullKit.Label first last → Prop :=
  fun {first} {_last} _label => first = WalkingParallelPair.zero

abbrev originalKit := restrict fullKit startsAtOriginal

theorem restricted_kit_still_has_the_actual_cross_interface_firing :
    Holds originalKit WalkingParallelPair.zero rules
      (.diamond ⟨WalkingParallelPairHom.left, rfl⟩ .top) (𝟙 WalkingParallelPair.zero) :=
  ⟨WalkingParallelPairHom.right, actual_cross_interface_firing, True.intro⟩

theorem admitted_kit_cannot_observe_the_result_interface (depth : Nat) :
    Rounds originalKit WalkingParallelPair.zero rules depth
      WalkingParallelPairHom.left WalkingParallelPairHom.right := by
  cases depth with
  | zero => exact True.intro
  | succ depth =>
      constructor
      · intro last label target _actual
        have impossible : WalkingParallelPair.one = WalkingParallelPair.zero := label.property
        cases impossible
      · intro last label target _actual
        have impossible : WalkingParallelPair.one = WalkingParallelPair.zero := label.property
        cases impossible

theorem restricted_agreement_does_not_reconstruct_unrestricted_observations (depth : Nat) :
    LogicallyEquivalent originalKit WalkingParallelPair.zero rules depth
      WalkingParallelPairHom.left WalkingParallelPairHom.right ∧
      (InterfaceModalLogic.Holds rules (.diamond (𝟙 WalkingParallelPair.one) .top)
        WalkingParallelPairHom.left ∧
        ¬ InterfaceModalLogic.Holds rules (.diamond (𝟙 WalkingParallelPair.one) .top)
          WalkingParallelPairHom.right) :=
  ⟨(bounded_adequacy originalKit WalkingParallelPair.zero rules depth _ _).mpr
      (admitted_kit_cannot_observe_the_result_interface depth),
    an_actual_diamond_separates_the_two_agents⟩

end Mettapedia.GSLT.InterfaceObservationKit.Controls
