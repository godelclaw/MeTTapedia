import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge

/-!
# Set-Theory ↔ WM Bridge Regression Fixtures

Concrete theorem fixtures consuming the set-theory bridge endpoints.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridgeRegression

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine

/-- Positive fixture:
derive `𝗭𝗙 ⊢ (⊥ ➝ ⊤)` via singleton-strength bridge, package it as a WM rule,
and execute it on a singleton set-theory WM state. -/
theorem zf_bottom_to_top_rule_singleton_fixture
    (S : SetPointed)
    (hS : S ⊧* 𝗭𝗙) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊥ : SetQuery) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊤ : SetQuery) := by
  let φ : SetQuery := (⊥ : SetQuery)
  let ψ : SetQuery := (⊤ : SetQuery)
  have hpoint : Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwiseImpliesOn
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies (fun S => S ⊧* 𝗭𝗙) φ ψ := by
    intro S' _hT hφ
    simp [φ, Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies] at hφ
  have hsing := (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwiseImpliesOn_iff_singletonStrengthLEOn
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies (fun S => S ⊧* 𝗭𝗙) φ ψ).1 hpoint
  have hprov : 𝗭𝗙 ⊢ (φ ➝ ψ) :=
    (provable_imp_iff_singletonStrengthLEOnZF (φ := φ) (ψ := ψ)).2 hsing
  let rule := wmConsequenceRuleOn_of_provable_imp_ZF (φ := φ) (ψ := ψ) hprov
  have hside : rule.side ({S} : SetState) := by
    intro S' hmem
    have hEq : S' = S := by
      simpa using (List.mem_singleton.mp hmem)
    cases hEq
    simpa using hS
  exact rule.sound hside

/-- Steelman positive fixture:
explicit singleton-universal characterization for ZF in the implication fragment. -/
theorem zf_provable_iff_all_model_singleton_strength_fixture
    (φ ψ : SetQuery) :
    (𝗭𝗙 ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* 𝗭𝗙 →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  simpa using
    (provable_imp_iff_all_model_singleton_strength (T := 𝗭𝗙) (φ := φ) (ψ := ψ))

/-- Steelman negative fixture:
outside ZF-model side conditions, singleton WM inequalities can fail. -/
theorem zf_outside_scope_top_bottom_counterexample_fixture
    (S : SetPointed)
    (hNotModel : ¬ S ⊧* 𝗭𝗙) :
    ¬ stateModelsZF ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) (⊤ : SetQuery) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) (⊥ : SetQuery)) := by
  have hTop : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S (⊤ : SetQuery) := by
    simp [Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies]
  have hBot : ¬ Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S (⊥ : SetQuery) := by
    simp [Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies]
  simpa [stateModelsZF] using
    (singleton_outside_theory_scope_counterexample
      (T := 𝗭𝗙) (S := S) (φ := (⊤ : SetQuery)) (ψ := (⊥ : SetQuery))
      hNotModel hTop hBot)

/-- Unified endpoint fixture:
provability transport plus the evidence-level Beck–Chevalley contract in one
theorem call. -/
theorem zf_provable_to_multiset_and_endpoint_contract_fixture
    (H : WMHyperdoctrine SetState)
    (φ ψ : SetQuery)
    (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    (∀ W : SetState, stateModelsZF W →
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ)
    ∧
    EndpointContract (H := H) := by
  simpa [stateModelsZF] using
    (provable_imp_to_multiset_and_endpoint_contract
      (H := H) (T := 𝗭𝗙) (φ := φ) (ψ := ψ) hprov)

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridgeRegression
