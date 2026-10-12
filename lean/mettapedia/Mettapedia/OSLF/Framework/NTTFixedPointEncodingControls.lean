import Mettapedia.GSLT.Logic.HigherOrderFixedPointEncodings
import Mettapedia.GSLT.Logic.InterfaceModalAdequacyControls

/-!
# Fixed-point formula controls and a genuine reactive cycle

The literal existential formula printed in NTT Section 4 always denotes
the complete predicate. The printed universal formula can be empty when
the greatest fixed point is complete. The corrected formulas distinguish
these cases and interpret the actual IPO transition family. Two authored
reaction rules form a cycle: its inductive progression is empty while its
coinductive predicate relates every agent to itself. One-way reactions
retain the existing operational separator between unequal agents.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NTTFixedPointEncodingControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.HigherOrderBisimulation

open Mettapedia.Order
open Mettapedia.GSLT

universe u

def printedExistential {State : Type u} (transformer : Set State → Set State) : Set State :=
  {state | ∃ predicate, (predicate ⊆ transformer predicate) → state ∈ predicate}

def printedUniversal {State : Type u} (transformer : Set State → Set State) : Set State :=
  {state | ∀ predicate, (transformer predicate ⊆ predicate) → state ∈ predicate}

theorem printed_existential_is_complete {State : Type u}
    (transformer : Set State → Set State) : printedExistential transformer = Set.univ := by
  ext state
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨Set.univ, fun _ => Set.mem_univ state⟩

def emptyOperator : Set Nat →o Set Nat :=
  ⟨fun _ => ∅, fun _ _ _ => Set.Subset.refl _⟩

theorem corrected_least_empty : PredicateFixedPointEncodings.least emptyOperator = ∅ :=
  Set.Subset.antisymm
    (PredicateFixedPointEncodings.least_induction emptyOperator ∅ (Set.Subset.refl _)) (Set.empty_subset _)

theorem printed_existential_is_not_least :
    printedExistential emptyOperator ≠ PredicateFixedPointEncodings.least emptyOperator := by
  intro same
  have member : 0 ∈ printedExistential emptyOperator := ⟨Set.univ, fun _ => trivial⟩
  rw [same, corrected_least_empty] at member
  exact member

theorem printed_universal_identity_is_empty :
    printedUniversal (OrderHom.id : Set Nat →o Set Nat) = ∅ := by
  apply Set.Subset.antisymm
  · intro state member
    exact member ∅ (Set.Subset.refl _)
  · exact Set.empty_subset _

theorem corrected_greatest_identity_is_complete :
    PredicateFixedPointEncodings.greatest (OrderHom.id : Set Nat →o Set Nat) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro state member
  exact ⟨Set.univ, Set.Subset.refl _, member⟩

theorem printed_universal_is_not_greatest :
    printedUniversal (OrderHom.id : Set Nat →o Set Nat) ≠
      PredicateFixedPointEncodings.greatest (OrderHom.id : Set Nat →o Set Nat) := by
  intro same
  have member : 0 ∈ PredicateFixedPointEncodings.greatest (OrderHom.id : Set Nat →o Set Nat) :=
    ⟨Set.univ, Set.Subset.refl _, trivial⟩
  rw [← same, printed_universal_identity_is_empty] at member
  exact member

def returnRule : ReactionRule WalkingParallelPair.zero where
  codomain := .one
  redex := WalkingParallelPairHom.right
  reactum := WalkingParallelPairHom.left

def cycleRules (selected : ReactionRule WalkingParallelPair.zero) : Prop :=
  selected = InterfaceModalAdequacyControls.rule ∨ selected = returnRule

theorem complete_cycle_factorization {interface : WalkingParallelPair}
    (agent : WalkingParallelPair.zero ⟶ interface)
    (redex : WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
    (label : interface ⟶ WalkingParallelPair.one)
    (square : agent ≫ label = redex ≫ 𝟙 _) :
    IsIdemPushout agent redex label (𝟙 _) square := by
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

theorem cycle_first_step : ActIPO cycleRules (𝟙 WalkingParallelPair.one)
    WalkingParallelPairHom.left WalkingParallelPairHom.right :=
  ⟨InterfaceModalAdequacyControls.rule, Or.inl rfl, 𝟙 _, rfl,
    complete_cycle_factorization _ _ _ rfl, rfl⟩

theorem cycle_return_step : ActIPO cycleRules (𝟙 WalkingParallelPair.one)
    WalkingParallelPairHom.right WalkingParallelPairHom.left :=
  ⟨returnRule, Or.inr rfl, 𝟙 _, rfl,
    complete_cycle_factorization _ _ _ rfl, rfl⟩

theorem cycle_first_target (next : WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
    (actual : ActIPO cycleRules (𝟙 WalkingParallelPair.one) WalkingParallelPairHom.left next) :
    next = WalkingParallelPairHom.right := by
  rcases actual with ⟨selected, selectedRule, reaction, square, _minimal, result⟩
  rcases selectedRule with rfl | rfl
  · cases reaction
    exact result
  · cases reaction
    cases square

theorem cycle_return_target (next : WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
    (actual : ActIPO cycleRules (𝟙 WalkingParallelPair.one) WalkingParallelPairHom.right next) :
    next = WalkingParallelPairHom.left := by
  rcases actual with ⟨selected, selectedRule, reaction, square, _minimal, result⟩
  rcases selectedRule with rfl | rfl
  · cases reaction
    cases square
  · cases reaction
    exact result

inductive Alternating : RelationFamily (fun interface : WalkingParallelPair =>
    WalkingParallelPair.zero ⟶ interface)
  | first : Alternating .one WalkingParallelPairHom.left WalkingParallelPairHom.right
  | second : Alternating .one WalkingParallelPairHom.right WalkingParallelPairHom.left

theorem alternating_is_bisimulation : IsIPOBisimulation cycleRules Alternating := by
  intro interface first second pair
  cases pair with
  | first =>
    constructor
    · intro nextInterface label next actual
      cases nextInterface with
      | zero => cases label
      | one =>
        cases label
        obtain rfl := cycle_first_target next actual
        exact ⟨WalkingParallelPairHom.left, cycle_return_step, Alternating.second⟩
    · intro nextInterface label next actual
      cases nextInterface with
      | zero => cases label
      | one =>
        cases label
        obtain rfl := cycle_return_target next actual
        exact ⟨WalkingParallelPairHom.right, cycle_first_step, Alternating.second⟩
  | second =>
    constructor
    · intro nextInterface label next actual
      cases nextInterface with
      | zero => cases label
      | one =>
        cases label
        obtain rfl := cycle_return_target next actual
        exact ⟨WalkingParallelPairHom.right, cycle_first_step, Alternating.first⟩
    · intro nextInterface label next actual
      cases nextInterface with
      | zero => cases label
      | one =>
        cases label
        obtain rfl := cycle_first_target next actual
        exact ⟨WalkingParallelPairHom.left, cycle_return_step, Alternating.first⟩

theorem cycle_distinct_agents_coinductively_related :
    (ipoSystem cycleRules).greatestRelation WalkingParallelPair.one
      WalkingParallelPairHom.left WalkingParallelPairHom.right :=
  (ipo_coinductive_iff cycleRules _ _).mpr
    ⟨Alternating, alternating_is_bisimulation, Alternating.first⟩

theorem every_cycle_agent_steps {interface : WalkingParallelPair}
    (agent : WalkingParallelPair.zero ⟶ interface) :
    ∃ (nextInterface : WalkingParallelPair) (label : interface ⟶ nextInterface)
      (next : WalkingParallelPair.zero ⟶ nextInterface), ActIPO cycleRules label agent next := by
  cases interface with
  | zero =>
    cases agent
    exact ⟨.one, WalkingParallelPairHom.left, WalkingParallelPairHom.right,
      InterfaceModalAdequacyControls.rule, Or.inl rfl, 𝟙 _, rfl,
      complete_cycle_factorization (𝟙 WalkingParallelPair.zero)
        WalkingParallelPairHom.left WalkingParallelPairHom.left rfl, rfl⟩
  | one =>
    cases agent with
    | left => exact ⟨.one, 𝟙 _, WalkingParallelPairHom.right, cycle_first_step⟩
    | right => exact ⟨.one, 𝟙 _, WalkingParallelPairHom.left, cycle_return_step⟩

theorem cycle_inductive_is_empty :
    PredicateFixedPointEncodings.least (ipoSystem cycleRules).progressOnJudgments = ∅ := by
  have closed : (ipoSystem cycleRules).progressOnJudgments
      (∅ : Set (Judgment (fun interface : WalkingParallelPair => WalkingParallelPair.zero ⟶ interface))) ≤
        (∅ : Set (Judgment (fun interface : WalkingParallelPair => WalkingParallelPair.zero ⟶ interface))) := by
    rintro ⟨interface, first, second⟩ progressed
    obtain ⟨nextInterface, label, next, actual⟩ := every_cycle_agent_steps first
    obtain ⟨matchedLabel, matched, _step, _labels, successors⟩ :=
      progressed.1 (literalLabel label) next actual
    exact successors
  exact Set.Subset.antisymm
    (PredicateFixedPointEncodings.least_induction _ ∅ closed) (Set.empty_subset _)

theorem cycle_coinductive_contains_actual_agent :
    (ipoSystem cycleRules).greatestRelation WalkingParallelPair.one
      WalkingParallelPairHom.left WalkingParallelPairHom.left :=
  ((ipoSystem cycleRules).greatestRelation_iff_bisimilar _ _).mpr
    ((ipoSystem cycleRules).bisimilar_refl _ _)

theorem cycle_inductive_cannot_be_bisimilarity :
    ¬(ipoSystem cycleRules).leastRelation WalkingParallelPair.one
      WalkingParallelPairHom.left WalkingParallelPairHom.left := by
  change ¬PredicateFixedPointEncodings.least (ipoSystem cycleRules).progressOnJudgments
    ⟨WalkingParallelPair.one, WalkingParallelPairHom.left, WalkingParallelPairHom.left⟩
  rw [cycle_inductive_is_empty]
  exact id

theorem corrected_coinduction_retains_the_operational_separator :
    ¬(ipoSystem InterfaceModalAdequacyControls.rules).greatestRelation WalkingParallelPair.one
      WalkingParallelPairHom.left WalkingParallelPairHom.right := by
  intro related
  exact InterfaceModalAdequacyControls.the_actual_agents_are_not_bisimilar
    ((ipo_coinductive_iff InterfaceModalAdequacyControls.rules _ _).mp related)

end Mettapedia.OSLF.Framework.NTTFixedPointEncodingControls
