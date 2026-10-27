import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EngineAgreement

/-!
# Transition systems with declared observations at the front door

Many consumers state their semantics as a transition system over their own configurations, with observations of the
configurations, and their native types as diamonds over it. Such a system is a language with one rule whose step is
supplied as a relation, as MeTTa Zero's space is: `x ~> y` when `next(x, y)` (`systemLanguage`). Its observations are
declared relations of the language, which the generated logic reads with `inRelation` (`ObservedSystem.env`). So the
consumer's system is asked through the front door, with the front door's strategies running on the system itself.

- **The steps are the system's** (`step_iff`): between states, the front door's structure steps from `s` to `t`
  exactly when `t` is a successor of `s`; the observations are the declared ones (`sat_observe_iff`).
- **A system on a carrier, encoded as states** (`EncodedSystem`): its configurations are encoded as closed patterns
  and decoded back; at an encoded configuration the front door steps exactly to the encodings of its successors
  (`EncodedSystem.step_encode_iff`), so "some successor has the observation" is the native type
  `◇(inRelation name)` (`EncodedSystem.sat_possibly_iff`); in general `◇` and `□` at an encoded configuration range
  over the encodings of its successors (`sat_possibly_encode_iff`, `sat_necessarily_encode_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match (Bindings mergeBindings)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (rewriteAt engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.OSLF.Framework.TypeSynthesis (langReducesUsing langReducesUsing_iff_execUsing langReducesExecUsing)

/-- The rule `x ~> y` when `next(x, y)`. -/
def nextRule : RewriteRule :=
  { name := "Next", typeContext := [], premises := [.relationQuery "next" [.fvar "x", .fvar "y"]],
    left := .fvar "x", right := .fvar "y" }

/-- **The language of a transition system given by its successors**: one sort, no constructor, and the rule
`x ~> y` when `next(x, y)`. -/
def systemLanguage : LanguageDef :=
  { name := "System", types := ["State"], terms := [], equations := [], rewrites := [nextRule] }

/-- **A transition system with declared observations**, on patterns. -/
structure ObservedSystem where
  next : Pattern → List Pattern
  observe : String → Pattern → Bool

namespace ObservedSystem

variable (system : ObservedSystem)

/-- The successors as the relation `next`, and each observation as a unary relation. -/
def env : RelationEnv where
  tuples relation arguments := match relation, arguments with
    | "next", [source, _] => (system.next source).map fun target => [source, target]
    | name, [term] => if system.observe name term then [[term]] else []
    | _, _ => []

/-- The front door's reading of the system. -/
abbrev reading : NativeStructure Pattern := referenceStructure system.env systemLanguage

end ObservedSystem

theorem matchRelationArgs_next (source target : Pattern) :
    matchRelationArgs [("x", source)] [.fvar "x", .fvar "y"] [source, target] = [[("y", target)]] := by
  rw [matchRelationArgs.eq_def]
  simp [matchRelationArgument, Bindings.lookup, mergeBindings]
  rw [matchRelationArgs.eq_def]
  simp [matchRelationArgument, Bindings.lookup, mergeBindings, matchRelationArgs]

/-- **One engine step of the system's language is a successor.** -/
theorem rewriteAt_system (system : ObservedSystem) (source : Pattern) (fuel : ℕ) :
    rewriteAt (engineBasePremises system.env) systemLanguage (fuel + 1) source = system.next source := by
  simp [rewriteAt, systemLanguage, nextRule, Mettapedia.OSLF.MeTTaIL.ContextualStep.applyRuleUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern, Mettapedia.OSLF.MeTTaIL.ContextualStep.premisesUsing,
    Mettapedia.OSLF.MeTTaIL.ContextualStep.premiseStepUsing, engineBasePremises, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings, ObservedSystem.env, List.map_flatMap, List.flatMap_map,
    matchRelationArgs_next, mergeBindings]

theorem langReduces_system_iff (system : ObservedSystem) (source target : Pattern) :
    langReducesUsing system.env systemLanguage source target ↔ target ∈ system.next source := by
  rw [langReducesUsing_iff_execUsing]
  constructor
  · rintro ⟨fuel, found⟩
    cases fuel with
    | zero => simp [rewriteAt] at found
    | succ fuel => rwa [rewriteAt_system] at found
  · intro found
    exact ⟨1, by rwa [rewriteAt_system]⟩

theorem systemLanguage_profile : ReferenceProfile systemLanguage := by
  have checked : systemLanguage.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned = true := by
    decide +kernel
  exact fun rule member => List.all_eq_true.mp checked rule member

theorem systemLanguage_equationFree : systemLanguage.isEquationFree = true := by decide +kernel

namespace ObservedSystem

variable (system : ObservedSystem)

/-- **The steps are the system's**, between states. -/
theorem step_iff {source target : Pattern} :
    system.reading.step source .any target ↔ IsState source ∧ IsState target ∧ target ∈ system.next source := by
  rw [step_any_iff_langReduces systemLanguage_profile systemLanguage_equationFree, langReduces_system_iff]

/-- **The observations are the declared ones.** -/
theorem sat_observe_iff (name : String) {term : Pattern} (state : IsState term) :
    system.reading.sat Env.closed (.inRelation name) term ↔ system.observe name term = true := by
  change (IsObject term ∧ ∃ representative, ObjectEquivalent system.env systemLanguage .syntax term representative ∧
    [representative] ∈ builtinRelationTuples systemLanguage name [representative] ++
      system.env.tuples name [representative]) ↔ _
  constructor
  · rintro ⟨-, representative, same, found⟩
    rw [objectEquivalent_iff_eq_of_isEquationFree systemLanguage_equationFree] at same
    subst same
    rw [builtinRelationTuples_single, List.nil_append] at found
    simp only [env] at found
    split at found <;> simp_all
  · intro observed
    refine ⟨state.2, term, Relation.EqvGen.refl _, ?_⟩
    rw [builtinRelationTuples_single, List.nil_append]
    simp only [env]
    split <;> simp_all

end ObservedSystem

/-! ## Systems on a carrier -/

/-- **A transition system on a carrier, encoded as states**: configurations encoded as closed object patterns and
decoded back, their successors, and their observations. -/
structure EncodedSystem (Configuration : Type) where
  encode : Configuration → Pattern
  decode : Pattern → Option Configuration
  decode_encode : ∀ configuration, decode (encode configuration) = some configuration
  state : ∀ configuration, IsState (encode configuration)
  successors : Configuration → List Configuration
  observations : String → Configuration → Bool

namespace EncodedSystem

variable {Configuration : Type} (system : EncodedSystem Configuration)

/-- The system on patterns: a pattern's successors are those of the configuration it decodes to. -/
def observed : ObservedSystem where
  next term := match system.decode term with
    | some configuration => (system.successors configuration).map system.encode
    | none => []
  observe name term := match system.decode term with
    | some configuration => system.observations name configuration
    | none => false

/-- **At an encoded configuration the front door steps exactly to the encodings of its successors.** -/
theorem step_encode_iff (configuration : Configuration) {target : Pattern} :
    system.observed.reading.step (system.encode configuration) .any target ↔
      ∃ next ∈ system.successors configuration, target = system.encode next := by
  rw [ObservedSystem.step_iff]
  simp only [observed, system.decode_encode, List.mem_map]
  constructor
  · rintro ⟨-, -, next, member, rfl⟩
    exact ⟨next, member, rfl⟩
  · rintro ⟨next, member, rfl⟩
    exact ⟨system.state configuration, system.state next, next, member, rfl⟩

theorem sat_observe_encode_iff (name : String) (configuration : Configuration) :
    system.observed.reading.sat Env.closed (.inRelation name) (system.encode configuration) ↔
      system.observations name configuration = true := by
  rw [ObservedSystem.sat_observe_iff _ name (system.state configuration)]
  simp [observed, system.decode_encode]

/-- **Some successor has the observation** is the native type `◇(inRelation name)` at the encoded configuration. -/
theorem sat_possibly_iff (name : String) (configuration : Configuration) :
    system.observed.reading.sat Env.closed (.possibly .any (.inRelation name)) (system.encode configuration) ↔
      ∃ next ∈ system.successors configuration, system.observations name next = true := by
  change (∃ target, system.observed.reading.step (system.encode configuration) .any target ∧
    system.observed.reading.sat Env.closed (.inRelation name) target) ↔ _
  constructor
  · rintro ⟨target, step, observed⟩
    obtain ⟨next, member, rfl⟩ := (system.step_encode_iff configuration).mp step
    exact ⟨next, member, (system.sat_observe_encode_iff name next).mp observed⟩
  · rintro ⟨next, member, observed⟩
    exact ⟨system.encode next, (system.step_encode_iff configuration).mpr ⟨next, member, rfl⟩,
      (system.sat_observe_encode_iff name next).mpr observed⟩

/-- **Some successor satisfies a formula** exactly when `◇` of it holds at the encoded configuration. -/
theorem sat_possibly_encode_iff {n : ℕ} (env : Env Pattern n) (formula : Formula n) (configuration : Configuration) :
    system.observed.reading.sat env (.possibly .any formula) (system.encode configuration) ↔
      ∃ next ∈ system.successors configuration, system.observed.reading.sat env formula (system.encode next) := by
  change (∃ target, system.observed.reading.step (system.encode configuration) .any target ∧
    system.observed.reading.sat env formula target) ↔ _
  constructor
  · rintro ⟨target, step, holds⟩
    obtain ⟨next, member, rfl⟩ := (system.step_encode_iff configuration).mp step
    exact ⟨next, member, holds⟩
  · rintro ⟨next, member, holds⟩
    exact ⟨system.encode next, (system.step_encode_iff configuration).mpr ⟨next, member, rfl⟩, holds⟩

/-- **Every successor satisfies a formula** exactly when `□` of it holds at the encoded configuration. -/
theorem sat_necessarily_encode_iff {n : ℕ} (env : Env Pattern n) (formula : Formula n)
    (configuration : Configuration) :
    system.observed.reading.sat env (.necessarily .any formula) (system.encode configuration) ↔
      ∀ next ∈ system.successors configuration, system.observed.reading.sat env formula (system.encode next) := by
  change (∀ target, system.observed.reading.step (system.encode configuration) .any target →
    system.observed.reading.sat env formula target) ↔ _
  constructor
  · intro every next member
    exact every _ ((system.step_encode_iff configuration).mpr ⟨next, member, rfl⟩)
  · intro every target step
    obtain ⟨next, member, rfl⟩ := (system.step_encode_iff configuration).mp step
    exact every next member

end EncodedSystem

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
