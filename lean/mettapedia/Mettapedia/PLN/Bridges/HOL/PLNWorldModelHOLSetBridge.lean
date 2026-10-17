import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.HOL.Semantics.SetBased
import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge

/-!
# Set-Semantics -> HOL -> WM Bridge

This module packages the direct set-based HOL grounding into a public WM-facing
bridge.

Low-level architecture:

- `SetStructure M -> HOL` lives in `HOL/Semantics/SetBased.lean`
- the present file keeps the same pointed set structures used by the existing
  set-theory WM bridge
- and interprets genuine closed HOL queries over them via the direct HOL model
  induced by each pointed set structure.

This makes the comparison with the older `Set -> FOL -> WM` route completely
explicit on the very same states.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLSetBridge

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

abbrev SetLang := ℒₛₑₜ
abbrev SetTheory := Theory SetLang
abbrev SetPointed := SmallStruc SetLang
abbrev SetState := Multiset SetPointed

abbrev SetBaseTy := Mettapedia.Logic.HOL.Semantics.SetBased.SetBaseTy
abbrev SetConst := Mettapedia.Logic.HOL.Semantics.SetBased.SetConst
abbrev SetHOLQuery := Mettapedia.Logic.HOL.Semantics.SetBased.SetHOLQuery
abbrev SetHOLModel := Mettapedia.Logic.HOL.Semantics.SetBased.SetHOLModel

/-- Closed-formula HOL satisfaction over a pointed set structure, interpreted by
the directly induced set-based HOL model. -/
def setHolSatisfies (S : SetPointed) (φ : SetHOLQuery) : Prop :=
  ((Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S).denote φ (fun v => nomatch v)).down

/-- The set-based HOL world model: count the pointed set structures satisfying a
query. -/
noncomputable instance : BinaryWorldModel SetState SetHOLQuery :=
  crispWorldModel setHolSatisfies

/-! ## Comparison with the existing FOL-routed set bridge -/

abbrev SetQuery := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.SetQuery

private theorem setHolSatisfies_embedSentence_iff_of_mutual_consequence
    (T : SetTheory) (S : SetPointed)
    (hT : S ⊧* T)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  have hleφψ :=
    (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
      (T := T) (φ := φ) (ψ := ψ)).1 hφψ S hT
  have hleψφ :=
    (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
      (T := T) (φ := ψ) (ψ := φ)).1 hψφ S hT
  have himpφψ :=
    (singletonStrengthLE_singleton_iff_imp Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
      S φ ψ).1 hleφψ
  have himpψφ :=
    (singletonStrengthLE_singleton_iff_imp Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
      S ψ φ).1 hleψφ
  rw [show setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S φ by
        unfold setHolSatisfies Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
        exact
          (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
            (S := S) (φ := φ))]
  rw [show setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) ↔
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S ψ by
        unfold setHolSatisfies Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
        exact
          (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
            (S := S) (φ := ψ))]
  exact ⟨himpφψ, himpψφ⟩

/-- On embedded set-theory sentences, the direct HOL interpretation agrees
pointwise with the existing set-theory/FOL satisfaction relation. -/
theorem setHolSatisfies_embedSentence_iff
    (S : SetPointed) (φ : LO.FirstOrder.Sentence SetLang) :
    setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies S φ := by
  unfold setHolSatisfies Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
  exact
    (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
      (S := S) (φ := φ))

/-- BinaryEvidence for embedded set-theory sentences agrees exactly between the direct
`Set -> HOL -> WM` route and the older `Set -> FOL -> WM` route. -/
theorem evidence_embedSentence_eq_fol
    (W : SetState) (φ : LO.FirstOrder.Sentence SetLang) :
    crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      crispEvidence Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies W φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [crispEvidence, crispEvidence,
      setHolSatisfies_embedSentence_iff]
  · simp [crispEvidence, crispEvidence,
      setHolSatisfies_embedSentence_iff]

/-- On theory-model states, mutually implied embedded set-theory sentences yield
identical direct HOL-routed WM evidence. This is the set/HOL rewrite-style
endpoint corresponding to theory-restricted semantic equivalence. -/
theorem evidence_eq_of_mutual_consequence_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  classical
  have hiff :
      ∀ S ∈ W,
        setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
          setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
    intro S hS
    exact setHolSatisfies_embedSentence_iff_of_mutual_consequence
      (T := T) (S := S) (hT := hW S hS) (φ := φ) (ψ := ψ) hφψ hψφ
  have hpos :
      Multiset.countP
          (fun S => setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ))
          W =
        Multiset.countP
          (fun S => setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
          W := by
    refine Multiset.countP_congr rfl ?_
    intro S hS
    exact propext (hiff S hS)
  have hneg :
      Multiset.countP
          (fun S => ¬ setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ))
          W =
        Multiset.countP
          (fun S => ¬ setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
          W := by
    refine Multiset.countP_congr rfl ?_
    intro S hS
    exact propext (not_congr (hiff S hS))
  apply BinaryEvidence.ext'
  · simpa [crispEvidence] using congrArg (fun n : Nat => (n : ℝ≥0∞)) hpos
  · simpa [crispEvidence] using congrArg (fun n : Nat => (n : ℝ≥0∞)) hneg

/-- On theory-model states, mutually provable implications between embedded
set-theory sentences yield identical direct HOL-routed WM evidence. -/
theorem evidence_eq_of_mutual_provable_imp_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hφψ : T ⊢ (φ ➝ ψ))
    (hψφ : T ⊢ (ψ ➝ φ)) :
    crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  exact evidence_eq_of_mutual_consequence_embed
    (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hφψ) (smallSound! hψφ)

/-- Query strengths for embedded set-theory sentences agree exactly between the
direct HOL-routed bridge and the older FOL-routed bridge. -/
theorem queryStrength_embedSentence_eq_setQueryStrength
    (W : SetState) (φ : LO.FirstOrder.Sentence SetLang) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.SetState)
        (Query := SetQuery) W φ := by
  change
    BinaryEvidence.toStrength
      (crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ)) =
    BinaryEvidence.toStrength (crispEvidence Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies W φ)
  exact congrArg BinaryEvidence.toStrength
    (evidence_embedSentence_eq_fol (W := W) (φ := φ))

/-- On theory-model states, mutually implied embedded set-theory sentences have
equal direct HOL-routed WM strengths. -/
theorem queryStrength_eq_of_mutual_consequence_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  change BinaryEvidence.toStrength
      (crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ)) =
    BinaryEvidence.toStrength
      (crispEvidence setHolSatisfies W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
  exact congrArg BinaryEvidence.toStrength <|
    evidence_eq_of_mutual_consequence_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hφψ hψφ

/-- On theory-model states, mutually provable implications between embedded
set-theory sentences have equal direct HOL-routed WM strengths. -/
theorem queryStrength_eq_of_mutual_provable_imp_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hφψ : T ⊢ (φ ➝ ψ))
    (hψφ : T ⊢ (ψ ➝ φ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  exact queryStrength_eq_of_mutual_consequence_embed
    (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hφψ) (smallSound! hψφ)

/-- Model-restricted singleton HOL consequence for embedded set-theory
sentences is equivalent to Foundation semantic consequence. -/
theorem consequence_iff_all_model_singleton_strength_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang) :
    T ⊨[SmallStruc SetLang] (φ ➝ ψ) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  constructor
  · intro hcons S hT
    have hle :=
      (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
        (T := T) (φ := φ) (ψ := ψ)).1 hcons S hT
    simpa [queryStrength_embedSentence_eq_setQueryStrength
      (W := ({S} : SetState))] using hle
  · intro hhol
    have hfol :
        ∀ S : SetPointed, S ⊧* T →
          BinaryWorldModel.queryStrength
              (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.SetState)
              (Query := SetQuery)
              ({S} : SetState) φ ≤
            BinaryWorldModel.queryStrength
              (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.SetState)
              (Query := SetQuery)
              ({S} : SetState) ψ := by
      intro S hT
      have h := hhol S hT
      simpa [queryStrength_embedSentence_eq_setQueryStrength
        (W := ({S} : SetState))] using h
    exact
      (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
        (T := T) (φ := φ) (ψ := ψ)).2 hfol

/-- Model-restricted singleton HOL consequence for embedded set-theory
sentences is equivalent to Foundation provability. -/
theorem provable_imp_iff_all_model_singleton_strength_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang) :
    (T ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  constructor
  · intro hprov
    exact
      (consequence_iff_all_model_singleton_strength_embed (T := T) (φ := φ) (ψ := ψ)).1
        (smallSound! hprov)
  · intro hhol
    exact
      FirstOrder.complete
        ((consequence_iff_all_model_singleton_strength_embed
          (T := T) (φ := φ) (ψ := ψ)).2 hhol)

/-- On theory-model states, Foundation semantic consequence transports through
the direct HOL-routed set bridge to multiset WM strength inequality. -/
theorem multiset_strength_le_of_consequence_embed
    (T : SetTheory) (W : SetState) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := φ)]
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := ψ)]
  exact
    Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.multiset_strength_le_of_consequence
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- On theory-model states, Foundation provability transports through the
direct HOL-routed set bridge to multiset WM strength inequality. -/
theorem multiset_strength_le_of_provable_imp_embed
    (T : SetTheory) (W : SetState) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := φ)]
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := ψ)]
  exact
    Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.multiset_strength_le_of_provable_imp
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Public state-indexed WM consequence rule induced by Foundation semantic
consequence, but presented on embedded HOL queries over pointed set structures. -/
def wmConsequenceRuleOn_of_consequence_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetHOLQuery where
  side := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T
  premise := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ
  conclusion := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ
  sound := by
    intro W hW
    exact multiset_strength_le_of_consequence_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- Public state-indexed WM consequence rule induced by Foundation provability,
presented on embedded HOL queries over pointed set structures. -/
def wmConsequenceRuleOn_of_provable_imp_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetHOLQuery where
  side := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.stateModelsTheory T
  premise := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ
  conclusion := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ
  sound := by
    intro W hW
    exact multiset_strength_le_of_provable_imp_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Positive comparison canary: embedded truth has singleton strength `1` in the
direct HOL-routed set bridge. -/
theorem canary_singleton_embedTruth_strength_one
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState)
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence (⊤ : LO.FirstOrder.Sentence SetLang)) = 1 := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := ({S} : SetState))
    (φ := (⊤ : LO.FirstOrder.Sentence SetLang))]
  exact
    queryStrength_singleton_of_satisfies Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
      S (⊤ : LO.FirstOrder.Sentence SetLang) (by
        simp [Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies])

/-- Negative comparison canary: embedded falsity has singleton strength `0` in
the direct HOL-routed set bridge. -/
theorem canary_singleton_embedFalsum_strength_zero
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState)
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence (⊥ : LO.FirstOrder.Sentence SetLang)) = 0 := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := ({S} : SetState))
    (φ := (⊥ : LO.FirstOrder.Sentence SetLang))]
  exact
    queryStrength_singleton_of_not_satisfies Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies
      S (⊥ : LO.FirstOrder.Sentence SetLang) (by
        simp [Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies])

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLSetBridge
