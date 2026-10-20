import Mathlib.Data.Multiset.Count
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness
import Mettapedia.Logic.HOL.SevenVirtues.Completeness
import Mettapedia.Logic.HOL.Soundness

/-!
# Classical HOL theories over the Henkin world model

Theory-relative consequence for the Henkin world model
(`PLNWorldModelHOLCore`): pointwise implication on the models of a classical
HOL theory is singleton-strength consequence there, finite derivability
transports to it, and classical Henkin completeness turns it back into
provability and supplies singleton states of consistent theories:
- over `WithParams Const` (for parameter-free theories that prove every
  excluded-middle instance), and
- directly over the original signature `Const` via `SevenVirtues.Completeness`
  (for countable signatures with a closed inhabitant at each base type and the
  single excluded-middle axiom `SevenVirtues.excludedMiddle`).
The theory-free consequence theorems are the generic ones of
`PLNWorldModelCrispSpecialization` at `holSatisfies`.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness

open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
## Classical theory-model states for HO WM-PLN

The higher-order WM layer now exposes the actual classical Henkin footing as a
theory-model abstraction:

- theories are closed HOL theories over `WithParams Const`,
- states are multisets of pointed Henkin models satisfying such a theory,
- pointwise implication on those theory-model states transports to WM strength
  inequalities, and
- a consistent theory in which no parameter occurs and which proves every
  excluded-middle instance yields a concrete singleton WM state, by
  `ClosedTheorySet.henkin_model_exists_of_consistent_classical`.

The completeness theorems below take a surjective enumeration of the one-variable
bodies (a countable signature), parameter-freeness of the theory and of the query,
and provability of the excluded-middle schema.
`PLNHigherOrderHOLCompletenessControls` instantiates each of them with the single
excluded-middle axiom over the propositional signature.
-/

/-- The actual classical Henkin theory interface used by HO WM-PLN. -/
abbrev ClassicalHOLTheory := ClosedTheorySet (WithParams Const)

/-- Closed HOL queries over the parameter-extended classical interface. -/
abbrev ClassicalHOLQuery := HOLQuery (Base := Base) (WithParams Const)

/-- Pointed Henkin models over the parameter-extended classical interface. -/
abbrev ClassicalHOLPointed := Mettapedia.Logic.HOL.HenkinModel.{u, v, v} Base (WithParams Const)

/-- WM states built from classical Henkin models of a higher-order theory. -/
abbrev ClassicalHOLState := Multiset (Mettapedia.Logic.HOL.HenkinModel.{u, v, v} Base (WithParams Const))

/-- A pointed Henkin model is a model of a classical theory. -/
def modelsTheory (T : ClosedTheorySet (WithParams Const))
    (M : ClassicalHOLPointed (Base := Base) (Const := Const)) : Prop :=
  ∀ χ ∈ T, HenkinModel.models M χ

/-- State-side condition: every pointed Henkin model in `W` satisfies `T`. -/
def stateModelsTheory
    (T : ClosedTheorySet (WithParams Const))
    (W : ClassicalHOLState (Base := Base) (Const := Const)) : Prop :=
  ∀ M ∈ W, ∀ ψ ∈ T, HenkinModel.models M ψ

/-- Sound theory-relative implication interface for HO WM-PLN:
a finite higher-order derivation of `φ → ψ` from assumptions drawn from `T`. -/
def derivableImpOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) : Prop :=
  ∃ Γ : ClosedTheory (WithParams Const),
    (∀ χ, χ ∈ Γ → χ ∈ T) ∧
      Derivation (WithParams Const) Γ (.imp φ ψ)

/-- Finite theory-relative HOL derivability transports to pointwise implication
on classical theory-model states. -/
theorem derivableImpOnTheory_implies_pointwiseImpliesOn
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    pointwiseImpliesOn holSatisfies (modelsTheory T) φ ψ := by
  rcases hprov with ⟨Γ, hΓ, d⟩
  intro M hT hφ
  have hImp : HenkinModel.models M (.imp φ ψ) := by
    exact
      Mettapedia.Logic.HOL.Soundness.derivation_sound
        (Base := Base) (Const := WithParams Const) (d := d)
        (M := M) (ρ := fun v => nomatch v)
        (by
          intro τ v
          nomatch v)
        (by
          intro χ hχ
          exact hT χ (hΓ χ hχ))
  exact (HenkinModel.models_imp M).mp hImp hφ

/-- Finite theory-relative HOL derivability transports directly to singleton WM
consequence on classical theory-model states. -/
theorem derivableImpOnTheory_implies_singletonStrengthLEOn
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    singletonStrengthLEOn holSatisfies (modelsTheory T) φ ψ :=
  (pointwiseImpliesOn_iff_singletonStrengthLEOn holSatisfies (modelsTheory T) φ ψ).mp
    (derivableImpOnTheory_implies_pointwiseImpliesOn
      (Base := Base) (Const := Const) hprov)

private theorem provable_of_provable_notnot_closed_em
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hnn : ClosedTheorySet.Provable (Const := WithParams Const) T (.not (.not χ))) :
    ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  have hem :
      ClosedTheorySet.Provable (Const := WithParams Const) T (.or χ (.not χ)) :=
    hEM _ (emClosed_mem (Const := Const) χ)
  have hswap :
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.imp (.or χ (.not χ)) (.or (.not χ) χ)) :=
    ClosedTheorySet.Provable.or_elim
      (Const := WithParams Const)
      (T := T)
      (φ := χ)
      (ψ := .not χ)
      (χ := .or (.not χ) χ)
      (ClosedTheorySet.Provable.or_intro_right
        (Const := WithParams Const) (T := T) (.not χ) χ)
      (ClosedTheorySet.Provable.or_intro_left
        (Const := WithParams Const) (T := T) (.not χ) χ)
  have hemSwap :
      ClosedTheorySet.Provable (Const := WithParams Const) T (.or (.not χ) χ) :=
    ClosedTheorySet.Provable.imp_mp hswap hem
  exact
    provable_or_elim_left
      (Const := WithParams Const)
      (T := T)
      (φ := .not χ)
      (ψ := χ)
      hemSwap
      hnn

/-- If a theory that proves every excluded-middle instance does not prove `χ`,
adjoining `¬χ` remains consistent. This is the public countermodel-preparation lemma used by
the completeness-tight HO-PLN credal envelope. -/
theorem consistent_insert_not_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ClosedTheorySet.Consistent (Const := WithParams Const) (insert (.not χ) T) := by
  intro hIncon
  apply hNotProv
  exact
    provable_of_provable_notnot_closed_em
      (Base := Base)
      (Const := Const)
      hEM
      (provable_not_of_imp_bot
        (Const := WithParams Const)
        (T := T)
        (χ := .not χ)
        (provable_imp_of_insert
          (Const := WithParams Const)
          (T := T)
          (χ := .not χ)
          (ψ := .bot)
          hIncon))

/-- Classical Henkin completeness gives an actual `T`-model refuting any
param-free query that `T` does not prove, for a parameter-free `T` that proves
every excluded-middle instance. -/
theorem exists_model_not_models_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧ ¬ HenkinModel.models M χ := by
  have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not χ) T) :=
    consistent_insert_not_of_not_provable_classical
      (Base := Base) (Const := Const) (T := T) (χ := χ) hEM hNotProv
  obtain ⟨M, hM⟩ :=
    ClosedTheorySet.henkin_model_exists_of_consistent_classical
      (Base := Base)
      (Const := Const)
      (T := insert (.not χ) T)
      enum
      henum
      hInsertCons
      (by
        intro ψ hψ σ k
        rcases Set.mem_insert_iff.mp hψ with rfl | hψT
        · exact NoConstOccurrence.not (hχ0 σ k)
        · exact hT0 ψ hψT σ k)
      (by
        intro ψ hψ
        exact ClosedTheorySet.provable_mono (fun h => Set.mem_insert_of_mem _ h) (hEM ψ hψ))
  refine ⟨M, ?_, ?_⟩
  · intro ψ hψ
    exact hM ψ (Set.mem_insert_iff.mpr (.inr hψ))
  · have hNotχ : HenkinModel.models M (.not χ) :=
      hM (.not χ) (Set.mem_insert_iff.mpr (.inl rfl))
    exact (HenkinModel.models_not M).mp hNotχ

/-- Extensional classical Henkin completeness gives an actual `T`-model
refuting any param-free query that `T` does not prove, together with the
semantic congruence law needed for `ExtDerivation` soundness. -/
theorem exists_extensional_model_not_models_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        ¬ HenkinModel.models M χ ∧
          HenkinModel.FunctionsRespectEqv M := by
  have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not χ) T) :=
    consistent_insert_not_of_not_provable_classical
      (Base := Base) (Const := Const) (T := T) (χ := χ) hEM hNotProv
  obtain ⟨M, hM, hExt⟩ :=
    ClosedTheorySet.henkin_extensional_model_exists_of_consistent_classical
      (Base := Base)
      (Const := Const)
      (T := insert (.not χ) T)
      enum
      henum
      hInsertCons
      (by
        intro ψ hψ σ k
        rcases Set.mem_insert_iff.mp hψ with rfl | hψT
        · exact NoConstOccurrence.not (hχ0 σ k)
        · exact hT0 ψ hψT σ k)
      (by
        intro ψ hψ
        exact ClosedTheorySet.provable_mono (fun h => Set.mem_insert_of_mem _ h) (hEM ψ hψ))
  refine ⟨M, ?_, ?_, hExt⟩
  · intro ψ hψ
    exact hM ψ (Set.mem_insert_iff.mpr (.inr hψ))
  · have hNotχ : HenkinModel.models M (.not χ) :=
      hM (.not χ) (Set.mem_insert_iff.mpr (.inl rfl))
    exact (HenkinModel.models_not M).mp hNotχ

/-- Classical Henkin completeness gives an actual `T`-model satisfying `χ`
whenever `T` does not prove `¬χ`. -/
theorem exists_model_models_of_not_provable_not_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProvNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ)) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧ HenkinModel.models M χ := by
  obtain ⟨M, hMT, hNotNotχ⟩ :=
    exists_model_not_models_of_not_provable_classical
      (Base := Base)
      (Const := Const)
      (T := T)
      (χ := .not χ)
      enum
      henum
      hT0
      hEM
      (by
        intro σ k
        exact NoConstOccurrence.not (hχ0 σ k))
      hNotProvNot
  refine ⟨M, hMT, ?_⟩
  by_contra hχ
  exact hNotNotχ ((HenkinModel.models_not M).mpr hχ)

/-- Extensional classical Henkin completeness gives an actual `T`-model
satisfying `χ` whenever `T` does not prove `¬χ`, together with the semantic
congruence law needed for `ExtDerivation` soundness. -/
theorem exists_extensional_model_models_of_not_provable_not_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProvNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ)) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        HenkinModel.models M χ ∧
          HenkinModel.FunctionsRespectEqv M := by
  obtain ⟨M, hMT, hNotNotχ, hExt⟩ :=
    exists_extensional_model_not_models_of_not_provable_classical
      (Base := Base)
      (Const := Const)
      (T := T)
      (χ := .not χ)
      enum
      henum
      hT0
      hEM
      (by
        intro σ k
        exact NoConstOccurrence.not (hχ0 σ k))
      hNotProvNot
  refine ⟨M, hMT, ?_, hExt⟩
  by_contra hχ
  exact hNotNotχ ((HenkinModel.models_not M).mpr hχ)

/-- Classical completeness closes the theory-relative higher-order
provability/consequence bridge for implication queries over `T`-models. -/
theorem provable_imp_onTheory_of_pointwiseImpliesOn_classical
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T χ)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ))
    (himp : pointwiseImpliesOn holSatisfies (modelsTheory T) φ ψ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) := by
  by_cases hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T
  · by_contra hNotProv
    have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not (.imp φ ψ)) T) :=
      consistent_insert_not_of_not_provable_classical
        (Base := Base)
        (Const := Const)
        (T := T)
        (χ := .imp φ ψ)
        hEM
        hNotProv
    obtain ⟨M, hM⟩ :=
      ClosedTheorySet.henkin_model_exists_of_consistent_classical
        (Base := Base)
        (Const := Const)
        (T := insert (.not (.imp φ ψ)) T)
        enum
        henum
        hInsertCons
        (by
          intro χ hχ σ k
          rcases Set.mem_insert_iff.mp hχ with rfl | hχT
          · exact NoConstOccurrence.not (hImp0 σ k)
          · exact hT0 χ hχT σ k)
        (by
          intro χ hχ
          exact ClosedTheorySet.provable_mono (fun h => Set.mem_insert_of_mem _ h) (hEM χ hχ))
    have hMT : ∀ χ ∈ T, HenkinModel.models M χ := by
      intro χ hχ
      exact hM χ (Set.mem_insert_iff.mpr (.inr hχ))
    have hNotImp : HenkinModel.models M (.not (.imp φ ψ)) :=
      hM (.not (.imp φ ψ)) (Set.mem_insert_iff.mpr (.inl rfl))
    have hImp : HenkinModel.models M (.imp φ ψ) := by
      exact (HenkinModel.models_imp M).2 (himp M hMT)
    exact ((HenkinModel.models_not M).mp hNotImp) hImp
  · have hBot : ClosedTheorySet.Inconsistent (Const := WithParams Const) T := by
      exact not_not.mp hCons
    exact
      ClosedTheorySet.provable_mp
        (Const := WithParams Const)
        (T := T)
        (φ := (.bot : ClosedFormula (WithParams Const)))
        (ψ := (.imp φ ψ))
        (ClosedTheorySet.Provable.bot_imp
          (Const := WithParams Const)
          (T := T)
          (.imp φ ψ))
        hBot

/-- Classical completeness closes the semantic-to-proof direction for the
extensional closed-theory proof relation used by HOL completeness. -/
theorem provable_imp_onTheory_of_singletonStrengthLEOn_classical
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T χ)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ)) :
    singletonStrengthLEOn holSatisfies (modelsTheory T) φ ψ →
      ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) := by
  intro hsing
  exact
    provable_imp_onTheory_of_pointwiseImpliesOn_classical
      (Base := Base)
      (Const := Const)
      enum
      henum
      hT0
      hEM
      hImp0
      ((pointwiseImpliesOn_iff_singletonStrengthLEOn holSatisfies (modelsTheory T) φ ψ).mpr hsing)

/-- Package sound finite theory-relative HOL derivability as a state-indexed WM
consequence rule on classical theory-model states. -/
def wmConsequenceRuleOn_of_derivableImpOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const))
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    WMConsequenceRuleOn
      (ClassicalHOLState (Base := Base) (Const := Const))
      (HOLQuery (Base := Base) (WithParams Const)) where
  side := stateModelsTheory T
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      queryStrength_le_of_pointwise_on holSatisfies (modelsTheory T) W φ ψ hW
        (derivableImpOnTheory_implies_pointwiseImpliesOn
          (Base := Base)
          (Const := Const)
          hprov)

/-- Classical Henkin completeness yields a concrete pointed model of `T`. -/
theorem exists_model_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const), ∀ ψ ∈ T, HenkinModel.models M ψ := by
  exact
    ClosedTheorySet.henkin_model_exists_of_consistent_classical
      (Base := Base) (Const := Const) (T := T) enum henum hCons hT0 hEM

/-- Classical Henkin completeness yields a concrete extensional pointed model
of `T`, preserving the semantic congruence law needed by `ExtDerivation`
soundness. -/
theorem exists_extensional_model_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        HenkinModel.FunctionsRespectEqv M := by
  exact
    ClosedTheorySet.henkin_extensional_model_exists_of_consistent_classical
      (Base := Base) (Const := Const) (T := T) enum henum hCons hT0 hEM

/-- Completeness grounds a classical higher-order theory in a nonempty singleton WM state. -/
theorem exists_singletonStateModelsTheory_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ) :
    ∃ W : ClassicalHOLState (Base := Base) (Const := Const),
      stateModelsTheory T W := by
  obtain ⟨M, hM⟩ :=
    exists_model_of_consistent_classicalTheory
      (T := T) enum henum hCons hT0 hEM
  refine ⟨({M} : ClassicalHOLState (Base := Base) (Const := Const)), ?_⟩
  intro N hN ψ hψ
  have hNM : N = M := by simpa using hN
  subst hNM
  exact hM ψ hψ

/-- A theory member gets concrete WM support `1` in the singleton state supplied by completeness. -/
theorem exists_singletonState_with_member_strength_one_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    {φ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ClosedTheorySet.Provable (Const := WithParams Const) T ψ)
    (hφ : φ ∈ T) :
    ∃ W : ClassicalHOLState (Base := Base) (Const := Const),
      stateModelsTheory T W ∧
        BinaryWorldModel.queryStrength
            (State := ClassicalHOLState (Base := Base) (Const := Const))
            (Query := HOLQuery (Base := Base) (WithParams Const))
            W φ = 1 := by
  obtain ⟨M, hM⟩ :=
    exists_model_of_consistent_classicalTheory
      (T := T) enum henum hCons hT0 hEM
  refine ⟨({M} : ClassicalHOLState (Base := Base) (Const := Const)), ?_, ?_⟩
  · intro N hN ψ hψ
    have hNM : N = M := by simpa using hN
    subst hNM
    exact hM ψ hψ
  · exact
      queryStrength_singleton_of_satisfies holSatisfies M φ (hM φ hφ)

/-! ## Original-signature classical completeness via `SevenVirtues`

Over a countable signature `Const` with a closed term at every base type,
`SevenVirtues.Completeness` proves classical Henkin completeness directly over
`Const` with the single axiom `SevenVirtues.excludedMiddle`, avoiding the
parameter signature `WithParams Const` and manual `NoConstOccurrence` side
conditions. -/

/-- Extensional pointed Henkin models of a theory `T` over the original signature `Const`. -/
def modelsExtTheoryOrig (T : ClosedTheorySet Const)
    (M : HenkinModel.{u, v, v} Base Const) : Prop :=
  M.FunctionsRespectEqv ∧ ∀ χ ∈ T, HenkinModel.models M χ

/-- Multiset world-model state of extensional Henkin models over `Const`. -/
def stateModelsExtTheoryOrig (T : ClosedTheorySet Const)
    (W : Multiset (HenkinModel.{u, v, v} Base Const)) : Prop :=
  ∀ M ∈ W, modelsExtTheoryOrig T M

/-- `SevenVirtues.exists_model_of_consistent` yields a concrete extensional
pointed Henkin model of `T` over the original signature `Const`. -/
theorem exists_extensional_model_of_consistent_orig
    [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const}
    (hCons : ClosedTheorySet.Consistent (Const := Const) (insert SevenVirtues.excludedMiddle T)) :
    ∃ M : HenkinModel.{u, v, v} Base Const, modelsExtTheoryOrig T M :=
  SevenVirtues.exists_model_of_consistent inh hCons

/-- Over a countable signature with closed base inhabitants, provability of
`φ → ψ` from `insert SevenVirtues.excludedMiddle T` is equivalent to singleton
world-model consequence over extensional Henkin models of `T`. -/
theorem provable_imp_iff_singletonStrengthLEOn_orig
    [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b))
    (T : ClosedTheorySet Const)
    (φ ψ : HOLQuery Const) :
    ClosedTheorySet.Provable (Const := Const) (insert SevenVirtues.excludedMiddle T) (.imp φ ψ) ↔
      singletonStrengthLEOn holSatisfies (modelsExtTheoryOrig T) φ ψ := by
  rw [← pointwiseImpliesOn_iff_singletonStrengthLEOn holSatisfies (modelsExtTheoryOrig T) φ ψ]
  rw [SevenVirtues.provable_iff_valid inh T (.imp φ ψ)]
  constructor
  · intro hValid M ⟨hExt, hT⟩ hφ
    exact (HenkinModel.models_imp M).mp (hValid M hExt hT) hφ
  · intro hImp M hExt hT
    exact (HenkinModel.models_imp M).mpr (hImp M ⟨hExt, hT⟩)

/-- A consistent classical theory over the original signature `Const` yields a
singleton WM state in which every theory member has strength `1`. -/
theorem exists_singletonState_with_member_strength_one_of_consistent_orig
    [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const}
    {φ : HOLQuery Const}
    (hCons : ClosedTheorySet.Consistent (Const := Const) (insert SevenVirtues.excludedMiddle T))
    (hφ : φ ∈ T) :
    ∃ W : Multiset (HenkinModel.{u, v, v} Base Const),
      stateModelsExtTheoryOrig T W ∧
        BinaryWorldModel.queryStrength
            (State := Multiset (HenkinModel.{u, v, v} Base Const))
            (Query := HOLQuery Const)
            W φ = 1 := by
  obtain ⟨M, hExt, hM⟩ := exists_extensional_model_of_consistent_orig inh hCons
  refine ⟨({M} : Multiset (HenkinModel.{u, v, v} Base Const)), ?_, ?_⟩
  · intro N hN
    have hNM : N = M := by simpa using hN
    subst hNM
    exact ⟨hExt, hM⟩
  · exact queryStrength_singleton_of_satisfies holSatisfies M φ (hM φ hφ)

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
