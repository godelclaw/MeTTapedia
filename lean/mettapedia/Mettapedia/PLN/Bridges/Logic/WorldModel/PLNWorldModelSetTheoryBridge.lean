import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness
import Foundation.FirstOrder.SetTheory.Universe
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge

/-!
# Set-Theory ↔ WM Consequence Bridge

This module specializes the generic FOL↔WM bridge to Foundation's set-theory
language `ℒₛₑₜ` and standard theories (`𝗭`, `𝗭𝗙`, `𝗭𝗖`, `𝗭𝗙𝗖`).

Interpretation:

- Set-theoretic semantic consequence/provability lives in Foundation FOL.
- WM consequence inequalities are derived as a sound target semantics.
- For implication queries, singleton WM consequence on `T`-models is equivalent
  to Foundation provability.

This gives a precise "WM as semantic lens on set-theoretic semantics" statement
for the implication fragment.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine

abbrev SetLang := ℒₛₑₜ
abbrev SetTheory := Theory SetLang
abbrev SetQuery := FOLQuery SetLang
abbrev SetPointed := PointedFOL SetLang
abbrev SetState := FOLState SetLang

/-- Steelman singleton-explicit form:
set-theoretic semantic consequence is equivalent to universal singleton WM
strength inequality over all pointed models of `T`. -/
theorem consequence_iff_all_model_singleton_strength
    (T : SetTheory) (φ ψ : SetQuery) :
    T ⊨[SmallStruc SetLang] (φ ➝ ψ) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  exact
    (consequence_iff_singletonStrengthLEOn (T := T) (φ := φ) (ψ := ψ))

/-- Steelman singleton-explicit form:
set-theoretic provability is equivalent to universal singleton WM
strength inequality over all pointed models of `T`. -/
theorem provable_imp_iff_all_model_singleton_strength
    (T : SetTheory) (φ ψ : SetQuery) :
    (T ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  exact
    (provable_imp_iff_singletonStrengthLEOn (T := T) (φ := φ) (ψ := ψ))

/-- Singleton negative criterion:
if a pointed structure satisfies `φ` but not `ψ`, singleton WM strength inequality
fails on that structure. -/
theorem singleton_strength_not_of_satisfies_and_not_satisfies
    (S : SetPointed) (φ ψ : SetQuery)
    (hφ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S ψ) :
    ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
          ({S} : SetState) φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
          ({S} : SetState) ψ) := by
  intro hle
  have himp :=
    (singletonStrengthLE_singleton_iff_imp folSatisfies S φ ψ).1 hle
  exact hnotψ (himp hφ)

/-- Outside-theory-scope counterexample family:
for a pointed structure not modeling `T`, singleton WM inequalities may fail even
when we only care about `T`-models in the bridge. -/
theorem singleton_outside_theory_scope_counterexample
    (T : SetTheory) (S : SetPointed) (φ ψ : SetQuery)
    (hNotModel : ¬ S ⊧* T)
    (hφ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S ψ) :
    ¬ stateModelsTheory T ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ) := by
  constructor
  · intro hstate
    exact hNotModel (hstate S (by simp))
  · exact singleton_strength_not_of_satisfies_and_not_satisfies
      (S := S) (φ := φ) (ψ := ψ) hφ hnotψ

/-- Full steelman split for Set↔WM implication transport:
positive exactness on theory models plus explicit outside-theory failure family. -/
theorem set_to_wm_expressivity_split
    (T : SetTheory) (φ ψ : SetQuery) (S : SetPointed)
    (hNotModel : ¬ S ⊧* T)
    (hφ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S ψ) :
    ((T ⊢ (φ ➝ ψ)) ↔
      ∀ S' : SetPointed, S' ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S'} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S'} : SetState) ψ)
    ∧
    (¬ stateModelsTheory T ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ)) := by
  constructor
  · exact provable_imp_iff_all_model_singleton_strength (T := T) (φ := φ) (ψ := ψ)
  · exact singleton_outside_theory_scope_counterexample
      (T := T) (S := S) (φ := φ) (ψ := ψ) hNotModel hφ hnotψ

/-- Unified endpoint pack:
from set-theoretic provability, we get WM multiset consequence transfer, and
every WM hyperdoctrine over set-theory states satisfies Beck–Chevalley at the
evidence layer. -/
theorem provable_imp_to_multiset_and_endpoint_contract
    (H : WMHyperdoctrine SetState)
    (T : SetTheory) (φ ψ : SetQuery)
    (hprov : T ⊢ (φ ➝ ψ)) :
    (∀ W : SetState, stateModelsTheory T W →
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ)
    ∧
    EndpointContract (H := H) := by
  constructor
  · intro W hW
    exact multiset_strength_le_of_provable_imp
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov
  · exact endpointContract_of_hyperdoctrine (H := H)

/-! ## Concrete theory wrappers (Z, ZF, ZC, ZFC) -/

abbrev stateModelsZ : SetState → Prop := stateModelsTheory 𝗭
abbrev stateModelsZF : SetState → Prop := stateModelsTheory 𝗭𝗙
abbrev stateModelsZC : SetState → Prop := stateModelsTheory 𝗭𝗖
abbrev stateModelsZFC : SetState → Prop := stateModelsTheory 𝗭𝗙𝗖

theorem provable_imp_iff_singletonStrengthLEOnZ
    (φ ψ : SetQuery) :
    (𝗭 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* 𝗭) φ ψ :=
  provable_imp_iff_singletonStrengthLEOn (T := 𝗭) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZF
    (φ ψ : SetQuery) :
    (𝗭𝗙 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* 𝗭𝗙) φ ψ :=
  provable_imp_iff_singletonStrengthLEOn (T := 𝗭𝗙) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZC
    (φ ψ : SetQuery) :
    (𝗭𝗖 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* 𝗭𝗖) φ ψ :=
  provable_imp_iff_singletonStrengthLEOn (T := 𝗭𝗖) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZFC
    (φ ψ : SetQuery) :
    (𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* 𝗭𝗙𝗖) φ ψ :=
  provable_imp_iff_singletonStrengthLEOn (T := 𝗭𝗙𝗖) (φ := φ) (ψ := ψ)

theorem multiset_strength_le_of_provable_imp_ZF
    (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsZF W)
    (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ :=
  multiset_strength_le_of_provable_imp (T := 𝗭𝗙) (W := W) (φ := φ) (ψ := ψ) hW hprov

theorem multiset_strength_le_of_provable_imp_ZFC
    (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsZFC W)
    (hprov : 𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ :=
  multiset_strength_le_of_provable_imp (T := 𝗭𝗙𝗖) (W := W) (φ := φ) (ψ := ψ) hW hprov

def wmConsequenceRuleOn_of_provable_imp_ZF
    (φ ψ : SetQuery) (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  wmConsequenceRuleOn_of_provable_imp (T := 𝗭𝗙) (φ := φ) (ψ := ψ) hprov

def wmConsequenceRuleOn_of_provable_imp_ZFC
    (φ ψ : SetQuery) (hprov : 𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  wmConsequenceRuleOn_of_provable_imp (T := 𝗭𝗙𝗖) (φ := φ) (ψ := ψ) hprov

/-- Category-facing endpoint: set-theory WM hyperdoctrines satisfy
Beck–Chevalley at the evidence layer. -/
theorem categorical_endpoint_contract
    (H : WMHyperdoctrine SetState) :
    EndpointContract (H := H) :=
  endpointContract_of_hyperdoctrine (H := H)

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge
