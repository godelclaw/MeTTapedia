import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
import Mettapedia.PLN.WorldModel.WorldModelCalculus
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
import Foundation.FirstOrder.Completeness.Completeness

/-!
# FOL WM Consequence/Completeness Bridge from Foundation Consequence

This module bridges Foundation first-order semantic consequence
`T ⊨[SmallStruc L] (φ ➝ ψ)` into WM singleton/multiset strength inequalities,
packages the result as `WMConsequenceRuleOn`, and provides a proof-theoretic
`provable ↔ singleton consequence` bridge for implication queries over `T`-models.

## Scope note
The historical filename `*FOLCompleteness` is retained for compatibility.
This module's strongest theorem-level claim is implication-fragment bridge
equivalence over `T`-models:
`(T ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* T) φ ψ`.
It is not a global completeness theorem for generic WM judgments.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness

open LO
open LO.FirstOrder
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open scoped ENNReal

universe u

abbrev FOLState (L : Language.{u}) := Multiset (PointedFOL L)

/-- State-side condition: every pointed structure in `W` is a model of `T`. -/
def stateModelsTheory {L : Language.{u}} (T : Theory L) (W : FOLState L) : Prop :=
  ∀ S ∈ W, S ⊧* T

/-- Foundation semantic consequence implies model-restricted pointwise implication. -/
theorem pointwiseImpliesOn_of_consequence {L : Language.{u}}
    {T : Theory L} {φ ψ : FOLQuery L}
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    pointwiseImpliesOn folSatisfies (fun S => S ⊧* T) φ ψ := by
  intro S hT hφ
  have hImp : S ⊧ (φ ➝ ψ) := hcons hT
  have hStep : S ⊧ φ → S ⊧ ψ :=
    (Semantics.Imp.models_imply (𝓜 := S) (φ := φ) (ψ := ψ)).mp hImp
  have hψ : S ⊧ ψ := hStep (by simpa [folSatisfies] using hφ)
  simpa [folSatisfies] using hψ

/-- Model-restricted pointwise implication yields Foundation semantic
consequence. -/
theorem consequence_of_pointwiseImpliesOn {L : Language.{u}}
    {T : Theory L} {φ ψ : FOLQuery L}
    (himp : pointwiseImpliesOn folSatisfies (fun S => S ⊧* T) φ ψ) :
    T ⊨[SmallStruc L] (φ ➝ ψ) := by
  intro S hT
  exact
    (Semantics.Imp.models_imply (𝓜 := S) (φ := φ) (ψ := ψ)).2
      (by
        intro hφ
        exact himp S hT (by simpa [folSatisfies] using hφ))

/-- Foundation semantic implication consequence iff model-restricted singleton
WM consequence. -/
theorem consequence_iff_singletonStrengthLEOn {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    T ⊨[SmallStruc L] (φ ➝ ψ) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* T) φ ψ := by
  constructor
  · intro hcons
    exact
      (pointwiseImpliesOn_iff_singletonStrengthLEOn folSatisfies (fun S => S ⊧* T) φ ψ).1
        (pointwiseImpliesOn_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons)
  · intro hsing
    exact
      consequence_of_pointwiseImpliesOn
        ((pointwiseImpliesOn_iff_singletonStrengthLEOn folSatisfies (fun S => S ⊧* T) φ ψ).2 hsing)

/-- Proof-theoretic bridge for FOL implication:
provability is equivalent to singleton WM consequence on `T`-models. -/
theorem provable_imp_iff_singletonStrengthLEOn {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    (T ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn folSatisfies (fun S => S ⊧* T) φ ψ := by
  constructor
  · intro hprov
    exact
      (consequence_iff_singletonStrengthLEOn
        (T := T) (φ := φ) (ψ := ψ)).1 (smallSound! hprov)
  · intro hsing
    exact
      FirstOrder.complete
        ((consequence_iff_singletonStrengthLEOn
          (T := T) (φ := φ) (ψ := ψ)).2 hsing)

/-- Bridge theorem requested for FOL:
Foundation semantic consequence gives WM multiset strength inequality. -/
theorem multiset_strength_le_of_consequence {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  have himp : pointwiseImpliesOn folSatisfies (fun S => S ⊧* T) φ ψ :=
    pointwiseImpliesOn_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons
  exact queryStrength_le_of_pointwise_on folSatisfies (fun S => S ⊧* T) W φ ψ hW himp

/-- Rule packaging for Foundation semantic consequence into WM inequalities. -/
def wmConsequenceRuleOn_of_consequence {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) where
  side := stateModelsTheory T
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      multiset_strength_le_of_consequence
        (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- Provability wrapper via Foundation soundness (`smallSound!`). -/
theorem multiset_strength_le_of_provable_imp {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  exact
    multiset_strength_le_of_consequence
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hprov)

/-- Rule packaging for provable implication into WM consequence rules. -/
def wmConsequenceRuleOn_of_provable_imp {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) :=
  wmConsequenceRuleOn_of_consequence
    (T := T) (φ := φ) (ψ := ψ) (smallSound! hprov)

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness
