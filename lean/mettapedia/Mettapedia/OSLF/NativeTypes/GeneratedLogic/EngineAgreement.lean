import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# The front door and the engine agree on aligned, equation-free languages

Many existing consumers state their semantics through the engine's one-step relation with a relation environment
(`langReducesUsing`), which is the least contextual relation over the environment's premises. On a language whose
rules the reference relation interprets alike (`ReferenceProfile`) and which has no equations, the front door's native
structure steps exactly where the engine does, between states (`step_any_iff_langReduces`). So a consumer's question
about a step is a native type at the front door:

- **some step to a given term** (`sat_possibly_is_iff`): `◇(is t)` at `s` holds exactly when the engine steps from `s`
  to `t`, for states `s` and `t`;
- **no step** (`sat_stuck_iff`): `□⊥` at a state holds exactly when the engine has no step to a state from it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile contextualStep_iff_step)
open Mettapedia.OSLF.Framework.TypeSynthesis (langReducesUsing)

variable {relEnv : RelationEnv} {language : LanguageDef}

/-- **On an aligned, equation-free language the front door steps where the engine does**, between states. -/
theorem step_any_iff_langReduces (profile : ReferenceProfile language) (free : language.isEquationFree = true)
    {source target : Pattern} :
    (referenceStructure relEnv language).step source .any target ↔
      IsState source ∧ IsState target ∧ langReducesUsing relEnv language source target := by
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, toRedex, -, valid, -, toTarget, -⟩
    rw [placed_iff rfl] at toRedex
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at toRedex toTarget
    subst toRedex toTarget
    exact ⟨sourceState, targetState,
      (contextualStep_iff_step relEnv language profile).mpr ⟨witness, valid⟩⟩
  · rintro ⟨sourceState, targetState, step⟩
    obtain ⟨witness, valid⟩ := (contextualStep_iff_step relEnv language profile).mp step
    exact ⟨sourceState, targetState, source, target, witness, Relation.EqvGen.refl _, sourceState, valid,
      targetState, Relation.EqvGen.refl _, rfl⟩

/-- **Some step to a given term** is the engine's step to it, between states. -/
theorem sat_possibly_is_iff (profile : ReferenceProfile language) (free : language.isEquationFree = true)
    {source target : Pattern} (sourceState : IsState source) (targetState : IsState target) :
    (referenceStructure relEnv language).sat Env.closed (.possibly .any (.is target)) source ↔
      langReducesUsing relEnv language source target := by
  change (∃ next, (referenceStructure relEnv language).step source .any next ∧
    (IsObject next ∧ ObjectEquivalent relEnv language .syntax next target)) ↔ _
  constructor
  · rintro ⟨next, step, -, same⟩
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at same
    subst same
    exact ((step_any_iff_langReduces profile free).mp step).2.2
  · intro step
    exact ⟨target, (step_any_iff_langReduces profile free).mpr ⟨sourceState, targetState, step⟩, targetState.2,
      Relation.EqvGen.refl _⟩

/-- **No step** at a state is the engine having no step to a state from it. -/
theorem sat_stuck_iff (profile : ReferenceProfile language) (free : language.isEquationFree = true)
    {source : Pattern} (sourceState : IsState source) :
    (referenceStructure relEnv language).sat Env.closed (.necessarily .any .bot) source ↔
      ∀ target, IsState target → ¬ langReducesUsing relEnv language source target := by
  change (∀ next, (referenceStructure relEnv language).step source .any next → False) ↔ _
  constructor
  · intro none target targetState step
    exact none target ((step_any_iff_langReduces profile free).mpr ⟨sourceState, targetState, step⟩)
  · intro none target step
    obtain ⟨-, targetState, step⟩ := (step_any_iff_langReduces profile free).mp step
    exact none target targetState step

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
