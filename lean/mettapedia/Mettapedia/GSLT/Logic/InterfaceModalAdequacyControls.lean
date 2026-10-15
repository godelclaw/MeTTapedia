import Mettapedia.GSLT.Logic.InterfaceModalAdequacy
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# An earned finite all-interface modal domain with a proper firing

The actual parallel-arrow category has two different agents. One consumes
the left arrow and emits the right; the latter cannot match that firing.
Every candidate and its unique mediator are checked, and all target-agent
fibres are genuinely finite. A second step changes the origin interface to
the result interface. No finite-branching claim about an instrument grammar
is inferred from this categorical consumer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceModalAdequacyControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativePushout RedexRelativeCongruence InterfaceModalLogic

def rule : ReactionRule (WalkingParallelPair.zero) where
  codomain := .one
  redex := WalkingParallelPairHom.left
  reactum := WalkingParallelPairHom.right

def rules (selected : ReactionRule (WalkingParallelPair.zero)) : Prop := selected = rule

theorem actual_target_fibres_are_finite : ImageFinite rules :=
  imageFinite_of_finite_agents rules (fun _ => inferInstance)

theorem complete_candidate_factorization {interface : WalkingParallelPair}
    (agent : WalkingParallelPair.zero ⟶ interface) (label : interface ⟶ WalkingParallelPair.one)
    (square : agent ≫ label = WalkingParallelPairHom.left ≫ 𝟙 _) :
    IsIdemPushout agent WalkingParallelPairHom.left label (𝟙 _) square := by
  intro candidate
  rcases candidate with ⟨apex, first, second, down, commutes, firstFactor, secondFactor⟩
  cases apex with
  | zero => cases second
  | one =>
    cases second
    cases down
    refine ⟨𝟙 _, ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa only [Candidate.self, walkingParallelPairHom_id, Category.comp_id] using firstFactor.symm
    · rfl
    · rfl
    · intro mediator compatible
      cases mediator
      rfl

theorem actual_nonidentity_result_firing :
    ActIPO rules (𝟙 WalkingParallelPair.one) WalkingParallelPairHom.left WalkingParallelPairHom.right :=
  ⟨rule, rfl, 𝟙 _, rfl,
    complete_candidate_factorization WalkingParallelPairHom.left (𝟙 _) rfl, rfl⟩

theorem actual_cross_interface_firing :
    ActIPO rules WalkingParallelPairHom.left (𝟙 WalkingParallelPair.zero) WalkingParallelPairHom.right :=
  ⟨rule, rfl, 𝟙 _, rfl,
    complete_candidate_factorization (𝟙 _) WalkingParallelPairHom.left rfl, rfl⟩

theorem the_result_agent_cannot_match_the_firing (target : WalkingParallelPair.zero ⟶ WalkingParallelPair.one) :
    ¬ActIPO rules (𝟙 WalkingParallelPair.one) WalkingParallelPairHom.right target := by
  rintro ⟨selected, rfl, reaction, square, _minimal, _result⟩
  cases reaction
  cases square

theorem an_actual_diamond_separates_the_two_agents :
    Holds rules (.diamond (𝟙 WalkingParallelPair.one) .top) WalkingParallelPairHom.left ∧
      ¬Holds rules (.diamond (𝟙 WalkingParallelPair.one) .top) WalkingParallelPairHom.right := by
  refine ⟨⟨WalkingParallelPairHom.right, actual_nonidentity_result_firing, True.intro⟩, ?_⟩
  rintro ⟨target, actual, _holds⟩
  exact the_result_agent_cannot_match_the_firing target actual

theorem the_complete_modal_comparison_is_earned_at_both_interfaces
    {interface : WalkingParallelPair} (first second : WalkingParallelPair.zero ⟶ interface) :
    IPOBisimilar rules first second ↔ LogicallyEquivalent rules first second :=
  ipoBisimilar_iff_logicallyEquivalent rules actual_target_fibres_are_finite first second

theorem the_actual_agents_are_not_bisimilar :
    ¬IPOBisimilar rules WalkingParallelPairHom.left WalkingParallelPairHom.right := by
  intro related
  have compared := logicallyEquivalent_of_ipoBisimilar rules related
  exact an_actual_diamond_separates_the_two_agents.2
    ((compared _).mp an_actual_diamond_separates_the_two_agents.1)

theorem forgetting_the_diamond_cannot_separate_the_agents :
    Holds rules (.top : Formula WalkingParallelPair .one) WalkingParallelPairHom.left ↔
      Holds rules (.top : Formula WalkingParallelPair .one) WalkingParallelPairHom.right := Iff.rfl

end Mettapedia.GSLT.InterfaceModalAdequacyControls
