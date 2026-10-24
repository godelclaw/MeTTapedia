import Mettapedia.OSLF.Framework.FiniteModelContexts
import Mettapedia.OSLF.Framework.FiniteModelContextual
import Mettapedia.OSLF.NativeTypes.Executable.FiniteSimulation
import Mettapedia.OSLF.Framework.SpanMapModal

/-!
# Certificates as finite Kripke models

The preorder of a certificate is a finite span on its carrier, with one step for each pair below each
other (`Certificate.span`, `Certificate.table`). A semantics whose steps from object states go down the
preorder maps into it, each state to its value (`Certificate.observation`). The root steps, the steps
inside declared contexts and the contextual semantics all go down (`rootGoesDown`, `contextsGoDown`,
`contextualGoesDown`).

So the value map is a simulation, and pulling native predicates back along it is a lax modal map
(`Certificate.laxModal`). The finite model checker decides two fragments through it, in both traversals
and with nested fixed points:
- a formula without negation and boxes fails at a state when it fails at the state's value in the
  preorder span (`not_satisfies_of_value`). The verdicts `refutes`, `refutesInContexts` and
  `refutesContextual` decide this;
- a formula without negation and diamonds holds at a state when it holds at the state's value
  (`satisfies_of_value`). The verdicts `proves`, `provesInContexts` and `provesContextual` decide this.

The verdicts take atoms that are native types the model selects, as sets of values. Refutations also
take atoms given by goal patterns, whose instances the certificate maps into the selected sets
(`refutesGoals`, `refutesContextualGoals`). The two theorems take any source predicates related to the
selected sets in the direction each needs.

The reachability verdicts are the instance `μ X. accepted ∨ ◇ X`. In the preorder span it fails at a
value exactly when no accepted element lies below it (`reach_fails_iff_apart`). So `cannotReachAccepted`
is `refutes` at that formula (`cannotReachAccepted_eq_refutes`).

Each fragment is decided in one direction only. The preorder is reflexive, so every value has a step,
while a state may have none: the certificate neither refutes "some step" there nor proves "no step".
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteModels

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan)
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal)
open Mettapedia.GSLT.ObservationSpans (SpanMap spanTheory)
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)

variable {A : Type} [DecidableEq A]

namespace Certificate

variable (certificate : Certificate A)

/-- **The preorder of a certificate as a span**: one step for each pair below each other. -/
def span : ReductionSpan A where
  Edge := {pair : A × A // certificate.below pair.1 pair.2 = true}
  source edge := edge.1.1
  target edge := edge.1.2

/-- The steps of the preorder span, as a table. -/
def table : FiniteGraph.Table certificate.span where
  edge := certificate.below
  exact source target := by
    constructor
    · intro low
      exact ⟨⟨(source, target), low⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨_, _⟩, low⟩, rfl, rfl⟩
      exact low

variable {certificate}

/-- **A semantics that goes down maps into the preorder span**, each object state to its value. -/
def observation {steps : ReductionSpan Pattern} (down : certificate.GoesDown steps) :
    SpanMap (between steps ObjectState) certificate.span where
  states := value certificate.model
  events event := ⟨(value certificate.model (steps.source event.1), value certificate.model (steps.target event.1)),
    down event.1 event.2.1⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- **A certificate is a lax modal map** from the native predicates of its preorder to those of every
semantics that goes down. -/
def laxModal {steps : ReductionSpan Pattern} (down : certificate.GoesDown steps) :
    IndexedModalFunctor.ForwardModalPredicateTheory.Hom ⟨spanTheory certificate.span⟩
      ⟨spanTheory (between steps ObjectState)⟩ :=
  (observation down).laxModal

/-- **Reachability in the preorder span is being below.** -/
theorem reaches_span_iff (preorder : certificate.preorderValid = true) {goal : A → Prop} {start : A} :
    Reaches certificate.span goal start ↔ ∃ reached, goal reached ∧ certificate.below start reached = true := by
  constructor
  · intro reaches
    induction reaches with
    | goal atGoal => exact ⟨_, atGoal, preorder_refl preorder _⟩
    | step event _ ih =>
      obtain ⟨reached, atGoal, low⟩ := ih
      exact ⟨reached, atGoal, preorder_trans preorder event.2 low⟩
  · rintro ⟨reached, atGoal, low⟩
    exact Reaches.step (span := certificate.span) ⟨(start, reached), low⟩ (Reaches.goal atGoal)

/-! ## Refuting native formulas -/

variable [Fintype A]

variable (certificate) in
/-- The values at which a formula holds in the preorder span. -/
def holdsAt {n : ℕ} (formula : Formula Traversal n) (environment : FiniteMuCalculus.Environment A n) : Finset A :=
  FiniteMuCalculus.evaluate (Executable.Finite.model certificate.table) formula environment

theorem mem_holdsAt_iff {n : ℕ} (formula : Formula Traversal n)
    (positive : Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment A n) (entry : A) :
    entry ∈ certificate.holdsAt formula environment ↔
      satisfies (transitionSystem certificate.span) environment.meaning formula entry :=
  FiniteMuCalculus.evaluate_correct (Executable.Finite.model certificate.table) formula positive environment entry

/-- **A formula that fails at the value fails at the state**, for every semantics that goes down, when
the values of the states in the source predicates lie in the selected sets. -/
theorem not_satisfies_of_value {steps : ReductionSpan Pattern} (down : certificate.GoesDown steps) {n : ℕ}
    {formula : Formula Traversal n} (existential : formula.existential = true)
    {environment : FiniteMuCalculus.Environment A n} {sourceEnv : Env Pattern n}
    (inside : ∀ index state, state ∈ sourceEnv index → value certificate.model state ∈ environment index)
    {state : Pattern} (fails : value certificate.model state ∉ certificate.holdsAt formula environment) :
    ¬ satisfies (transitionSystem (between steps ObjectState)) sourceEnv formula state :=
  not_satisfies_of_preserves (preservesTransitions_of_spanMap (observation down)) existential
    (fun index state member => Finset.mem_coe.mpr (inside index state member))
    fun holds => fails ((mem_holdsAt_iff formula (fixedPointsPositive_of_existential formula existential)
      environment _).mpr holds)

variable (certificate) in
/-- **Decide that a state fails a native formula**: the certificate is valid, the formula uses neither
negation nor boxes, and it fails at the value of the state in the preorder span. -/
def refutes (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.valid language && formula.existential &&
    !decide (value certificate.model state ∈ certificate.holdsAt formula environment)

theorem refutes_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.refutes language formula environment state = true) :
    ¬ satisfies (transitionSystem (between (languageSpan language) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [refutes, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at checked
  obtain ⟨⟨valid, existential⟩, fails⟩ := checked
  exact not_satisfies_of_value (rootGoesDown valid) existential (fun _ _ member => member) fails

variable (certificate) in
/-- **Decide that a state fails a native formula, with steps inside the declared contexts.** -/
def refutesInContexts (language : LanguageDef) (sites : List Site) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.refutes language formula environment state && certificate.sitesCheck sites

theorem refutesInContexts_of_check {language : LanguageDef} {sites : List Site} {n : ℕ}
    {formula : Formula Traversal n} {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.refutesInContexts language sites formula environment state = true) :
    ¬ satisfies (transitionSystem (between (contextSpan language sites) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [refutesInContexts, refutes, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at checked
  obtain ⟨⟨⟨valid, existential⟩, fails⟩, sitesChecked⟩ := checked
  exact not_satisfies_of_value (contextsGoDown valid sitesChecked) existential (fun _ _ member => member) fails

variable (certificate) in
/-- **Decide that a state fails a native formula under the contextual semantics.** -/
def refutesContextual (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.contextualValid language && formula.existential &&
    !decide (value certificate.model state ∈ certificate.holdsAt formula environment)

/-- The verdict holds for every evaluator of the other premises that only adds bindings. -/
theorem refutesContextual_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.refutesContextual language formula environment state = true)
    (base : BasePremiseEvaluator) (fromBase : BaseExtends base language) :
    ¬ satisfies (transitionSystem (between (contextualSpan base language) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [refutesContextual, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at checked
  obtain ⟨⟨valid, existential⟩, fails⟩ := checked
  exact not_satisfies_of_value (contextualGoesDown valid fromBase) existential (fun _ _ member => member) fails

/-! ### Atoms given by goal patterns -/

/-- Atoms given by patterns: atom `index` holds at the instances of `goals index`. -/
def goalEnv {n : ℕ} (goals : Fin n → List Pattern) : Env Pattern n :=
  fun index => {state | Goal (goals index) state}

variable (certificate) in
/-- Every instance of an atom's patterns has its value in the atom's selected set. -/
def goalsCheck {n : ℕ} (goals : Fin n → List Pattern) (environment : FiniteMuCalculus.Environment A n) : Bool :=
  (List.finRange n).all fun index =>
    (goals index).all (certificate.goalCheck fun entry => decide (entry ∈ environment index))

omit [Fintype A] in
theorem goalEnv_inside {n : ℕ} {goals : Fin n → List Pattern} {environment : FiniteMuCalculus.Environment A n}
    (checked : certificate.goalsCheck goals environment = true) :
    ∀ index state, state ∈ goalEnv goals index → value certificate.model state ∈ environment index := by
  rintro index _ ⟨goal, goalMember, bindings, rfl⟩
  have each := List.all_eq_true.mp checked index (List.mem_finRange index)
  simpa using goal_accepted (List.all_eq_true.mp each goal goalMember) bindings

variable (certificate) in
/-- **Decide that a state fails a native formula whose atoms are goal patterns.** -/
def refutesGoals (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n) (goals : Fin n → List Pattern)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.refutes language formula environment state && certificate.goalsCheck goals environment

theorem refutesGoals_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {goals : Fin n → List Pattern} {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.refutesGoals language formula goals environment state = true) :
    ¬ satisfies (transitionSystem (between (languageSpan language) ObjectState)) (goalEnv goals) formula state := by
  simp only [refutesGoals, refutes, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at checked
  obtain ⟨⟨⟨valid, existential⟩, fails⟩, goalsChecked⟩ := checked
  exact not_satisfies_of_value (rootGoesDown valid) existential (goalEnv_inside goalsChecked) fails

variable (certificate) in
/-- **Decide that a state fails a native formula whose atoms are goal patterns, under the contextual
semantics.** -/
def refutesContextualGoals (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n)
    (goals : Fin n → List Pattern) (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.refutesContextual language formula environment state && certificate.goalsCheck goals environment

/-- The verdict holds for every evaluator of the other premises that only adds bindings. -/
theorem refutesContextualGoals_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {goals : Fin n → List Pattern} {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.refutesContextualGoals language formula goals environment state = true)
    (base : BasePremiseEvaluator) (fromBase : BaseExtends base language) :
    ¬ satisfies (transitionSystem (between (contextualSpan base language) ObjectState)) (goalEnv goals) formula
      state := by
  simp only [refutesContextualGoals, refutesContextual, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at checked
  obtain ⟨⟨⟨valid, existential⟩, fails⟩, goalsChecked⟩ := checked
  exact not_satisfies_of_value (contextualGoesDown valid fromBase) existential (goalEnv_inside goalsChecked) fails

/-! ## Proving native formulas -/

/-- **A formula that holds at the value holds at the state**, for every semantics that goes down, when
the source predicates contain the states whose values lie in the selected sets. -/
theorem satisfies_of_value {steps : ReductionSpan Pattern} (down : certificate.GoesDown steps) {n : ℕ}
    {formula : Formula Traversal n} (universal : formula.universal = true)
    {environment : FiniteMuCalculus.Environment A n} {sourceEnv : Env Pattern n}
    (inside : ∀ index state, value certificate.model state ∈ environment index → state ∈ sourceEnv index)
    {state : Pattern} (holds : value certificate.model state ∈ certificate.holdsAt formula environment) :
    satisfies (transitionSystem (between steps ObjectState)) sourceEnv formula state :=
  satisfies_of_preserves_universal (preservesTransitions_of_spanMap (observation down)) formula universal
    (fun index state member => inside index state (Finset.mem_coe.mp member)) state
    ((mem_holdsAt_iff formula (fixedPointsPositive_of_universal formula universal) environment _).mp holds)

variable (certificate) in
/-- **Decide that a state satisfies a native formula**: the certificate is valid, the formula uses
neither negation nor diamonds, and it holds at the value of the state in the preorder span. -/
def proves (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.valid language && formula.universal &&
    decide (value certificate.model state ∈ certificate.holdsAt formula environment)

theorem proves_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.proves language formula environment state = true) :
    satisfies (transitionSystem (between (languageSpan language) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [proves, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨valid, universal⟩, holds⟩ := checked
  exact satisfies_of_value (rootGoesDown valid) universal (fun _ _ member => member) holds

variable (certificate) in
/-- **Decide that a state satisfies a native formula, with steps inside the declared contexts.** -/
def provesInContexts (language : LanguageDef) (sites : List Site) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.proves language formula environment state && certificate.sitesCheck sites

theorem provesInContexts_of_check {language : LanguageDef} {sites : List Site} {n : ℕ}
    {formula : Formula Traversal n} {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.provesInContexts language sites formula environment state = true) :
    satisfies (transitionSystem (between (contextSpan language sites) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [provesInContexts, proves, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨valid, universal⟩, holds⟩, sitesChecked⟩ := checked
  exact satisfies_of_value (contextsGoDown valid sitesChecked) universal (fun _ _ member => member) holds

variable (certificate) in
/-- **Decide that a state satisfies a native formula under the contextual semantics.** -/
def provesContextual (language : LanguageDef) {n : ℕ} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment A n) (state : Pattern) : Bool :=
  certificate.contextualValid language && formula.universal &&
    decide (value certificate.model state ∈ certificate.holdsAt formula environment)

/-- The verdict holds for every evaluator of the other premises that only adds bindings. -/
theorem provesContextual_of_check {language : LanguageDef} {n : ℕ} {formula : Formula Traversal n}
    {environment : FiniteMuCalculus.Environment A n} {state : Pattern}
    (checked : certificate.provesContextual language formula environment state = true)
    (base : BasePremiseEvaluator) (fromBase : BaseExtends base language) :
    satisfies (transitionSystem (between (contextualSpan base language) ObjectState))
      (pullEnvironment (value certificate.model) environment.meaning) formula state := by
  simp only [provesContextual, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨valid, universal⟩, holds⟩ := checked
  exact satisfies_of_value (contextualGoesDown valid fromBase) universal (fun _ _ member => member) holds

/-! ## Reachability is an instance -/

/-- The accepted elements, as the environment of one atom. -/
def accepted (accept : A → Bool) : FiniteMuCalculus.Environment A 1 :=
  fun _ => Finset.univ.filter fun entry => accept entry = true

/-- **Reachability of accepted values fails at a value exactly when no accepted element lies below it.** -/
theorem reach_fails_iff_apart (preorder : certificate.preorderValid = true) (accept : A → Bool) (start : A) :
    start ∉ certificate.holdsAt reachFormula (accepted accept) ↔ certificate.apart accept start = true := by
  rw [mem_holdsAt_iff reachFormula (fixedPointsPositive_of_existential _ reachFormula_existential),
    satisfies_reach_iff, reaches_span_iff preorder]
  simp only [apart, accepted, FiniteMuCalculus.Environment.meaning, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq, not_exists, not_and, List.all_eq_true, certificate.complete, forall_const, Bool.not_eq_true',
    Bool.and_eq_false_iff]
  exact forall_congr' fun entry => by cases accept entry <;> cases certificate.below start entry <;> simp

/-- **The reachability verdict is `refutes` at `μ X. accepted ∨ ◇ X`.** -/
theorem cannotReachAccepted_eq_refutes (language : LanguageDef) (accept : A → Bool) (state : Pattern) :
    certificate.cannotReachAccepted language accept state =
      certificate.refutes language reachFormula (accepted accept) state := by
  unfold cannotReachAccepted refutes
  cases valid : certificate.valid language with
  | false => rfl
  | true =>
    have equivalent := reach_fails_iff_apart (preorderValid_of_valid valid) accept (value certificate.model state)
    rw [reachFormula_existential]
    by_cases member : value certificate.model state ∈ certificate.holdsAt reachFormula (accepted accept)
    · simp only [member, decide_true, Bool.not_true, Bool.true_and, Bool.and_false]
      exact Bool.eq_false_iff.mpr fun apart => equivalent.mpr apart member
    · simp only [member, decide_false, Bool.not_false, Bool.true_and, Bool.and_true]
      exact equivalent.mp member

/-- **The contextual reachability verdict is `refutesContextual` at `μ X. accepted ∨ ◇ X`.** -/
theorem cannotReachContextualAccepted_eq_refutesContextual (language : LanguageDef) (accept : A → Bool)
    (state : Pattern) :
    certificate.cannotReachContextualAccepted language accept state =
      certificate.refutesContextual language reachFormula (accepted accept) state := by
  unfold cannotReachContextualAccepted refutesContextual
  cases valid : certificate.contextualValid language with
  | false => rfl
  | true =>
    have equivalent := reach_fails_iff_apart (contextual_preorder valid) accept (value certificate.model state)
    rw [reachFormula_existential]
    by_cases member : value certificate.model state ∈ certificate.holdsAt reachFormula (accepted accept)
    · simp only [member, decide_true, Bool.not_true, Bool.true_and, Bool.and_false]
      exact Bool.eq_false_iff.mpr fun apart => equivalent.mpr apart member
    · simp only [member, decide_false, Bool.not_false, Bool.true_and, Bool.and_true]
      exact equivalent.mp member

end Certificate

end Mettapedia.OSLF.Framework.FiniteModels
