import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.OSLF.Framework.HerbrandBridge
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# Backward search as evidence: reaching named goals

Reaching one of finitely many named terms is the generated formula `μX. (is g₁ ∨ … ∨ is gₖ) ∨ ◇X` (`reachFormula`),
and its dual says that none of them is ever reached.

- **Reaching is a least fixed point** (`sat_reachFormula`): in every native structure, the formula holds where a run of
  steps reaches a term the structure names as a goal.
- **The steps of a first-order language are its root reducts** (`step_iff_rootReducts`): in an equation-free language
  whose rules have no premises and are aligned, a step of the reference relation between states is a root rewrite.
- **So the Herbrand backward search decides the formula** (`sat_reachFormula_iff_reaches`): from a ground first-order
  term, with ground first-order goals, in a language whose rules are first-order and bind every variable of their right
  sides, the formula holds exactly when the term reaches a goal by root steps, which narrowing searches backward from
  the goals. A run that finds the term proves the formula; a saturated run that misses it refutes it, on infinite state
  spaces too (`reachEstablishes_sound`, `reachRefutes_sound`). Its dual is decided the other way round.
- **Ancestry is reachability backwards** (`sat_pastReachFormula`, `sat_pastReach_iff`): some ancestor of a term is a
  named goal, `μX. (is g₁ ∨ … ∨ is gₖ) ∨ ⧫X`, exactly when some goal reaches the term; backward searches from the term
  decide it, and its dual (`pastEstablishes_sound`, `pastRefutes_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings applyBindings)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts isUnconditionalAligned rewriteAt_succ_eq_rootReducts)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile ruleAligned contextualStep_iff_step)
open Mettapedia.OSLF.Framework.BackwardSearch (Reaches reaches_transfer Presentation)
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan)
open Mettapedia.OSLF.Framework.HerbrandBridge (encode encodeList encodeList_some_iff languageSpan Goal Profile
  profileCheck goalsCheck step_forward)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

/-! ## Reaching named goals -/

/-- One of the goals, by name. -/
def goalsFormula {n : ℕ} : List Pattern → Formula n
  | [] => .bot
  | [goal] => .is goal
  | goal :: next :: goals => .or (.is goal) (goalsFormula (next :: goals))

/-- **Reaching one of the goals**: `μX. (is g₁ ∨ … ∨ is gₖ) ∨ ◇X`. -/
def reachFormula (goals : List Pattern) : Formula 0 := .mu (.or (goalsFormula goals) (.possibly .any (.var 0)))

theorem sat_goalsFormula {Carrier : Type} (S : NativeStructure Carrier) {n : ℕ} (env : Env Carrier n) (element : Carrier) :
    ∀ goals : List Pattern, S.sat env (goalsFormula goals) element ↔ ∃ goal ∈ goals, S.named element goal
  | [] => by simp [goalsFormula, NativeStructure.sat]
  | [goal] => by simp [goalsFormula, NativeStructure.sat]
  | goal :: next :: goals => by
    simp only [goalsFormula, NativeStructure.sat, sat_goalsFormula S env element (next :: goals), List.mem_cons,
      exists_eq_or_imp]

/-- **Reaching is a least fixed point**: the formula holds where a run of steps reaches a named goal. -/
theorem sat_reachFormula {Carrier : Type} (S : NativeStructure Carrier) (goals : List Pattern) (element : Carrier) :
    S.sat Env.closed (reachFormula goals) element ↔
      Reaches (HigherOrder.stepSpan S) (fun other => ∃ goal ∈ goals, S.named other goal) element := by
  constructor
  · intro holds
    refine holds {other | Reaches (HigherOrder.stepSpan S) (fun other => ∃ goal ∈ goals, S.named other goal) other} ?_
    intro other prefixed
    rcases prefixed with atGoal | ⟨next, step, inside⟩
    · exact .goal ((sat_goalsFormula S _ other goals).mp atGoal)
    · exact Reaches.step (span := HigherOrder.stepSpan S) ⟨(other, next), step⟩ inside
  · intro reaches closed prefixed
    induction reaches with
    | goal atGoal => exact prefixed _ (.inl ((sat_goalsFormula S _ _ goals).mpr atGoal))
    | step event _ inside => exact prefixed _ (.inr ⟨_, event.2, inside⟩)

/-! ## Ground first-order terms -/

theorem exists_of_forall₂ {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second → ∀ element ∈ first, ∃ other, relation element other
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons head tail, element, member => by
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨_, head⟩
    · exact exists_of_forall₂ tail element inTail

theorem encode_arguments {label : String} {arguments : List Pattern}
    {encoded : Mettapedia.Logic.LP.Term Mettapedia.OSLF.Framework.HerbrandBridge.Labels}
    (read : encode [] (.apply label arguments) = some encoded) :
    ∀ argument ∈ arguments, ∃ term, encode [] argument = some term := by
  cases arguments with
  | nil => intro _ member; cases member
  | cons first rest =>
    simp only [encode] at read
    split at read
    · rename_i term terms firstRead restRead
      intro argument member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨term, firstRead⟩
      · exact exists_of_forall₂ ((encodeList_some_iff [] rest terms).mp restRead) argument inRest
    · cases read

theorem isWellScopedListAt_of_forall {depth : ℕ} :
    ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, pattern.isWellScopedAt depth = true) →
      Pattern.isWellScopedListAt depth patterns = true
  | [], _ => rfl
  | pattern :: patterns, all => by
    simp only [Pattern.isWellScopedListAt, all pattern List.mem_cons_self,
      isWellScopedListAt_of_forall fun other member => all other (List.mem_cons_of_mem _ member), Bool.and_self]

theorem isObjectPatternList_of_forall :
    ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, isObjectPattern pattern = true) →
      isObjectPatternList patterns = true
  | [], _ => rfl
  | pattern :: patterns, all => by
    simp only [isObjectPatternList, all pattern List.mem_cons_self,
      isObjectPatternList_of_forall fun other member => all other (List.mem_cons_of_mem _ member), Bool.and_self]

/-- **A ground first-order term is a state.** -/
theorem isState_of_encode {pattern : Pattern} : ∀ {encoded}, encode [] pattern = some encoded → IsState pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => intro _ read; simp [encode] at read
  | hfvar _ => intro _ read; simp [encode] at read
  | happly label arguments ih =>
    intro _ read
    have each := encode_arguments read
    refine ⟨?_, ?_⟩
    · show Pattern.isWellScopedListAt 0 arguments = true
      exact isWellScopedListAt_of_forall fun argument member => by
        obtain ⟨_, argumentRead⟩ := each argument member
        exact (ih argument member argumentRead).1
    · show isObjectPatternList arguments = true
      exact isObjectPatternList_of_forall fun argument member => by
        obtain ⟨_, argumentRead⟩ := each argument member
        exact (ih argument member argumentRead).2
  | hlambda _ _ _ => intro _ read; simp [encode] at read
  | hmultiLambda _ _ _ _ => intro _ read; simp [encode] at read
  | hsubst _ _ _ _ => intro _ read; simp [encode] at read
  | hcollection _ _ _ _ => intro _ read; simp [encode] at read

/-- **Bindings leave a ground first-order term as it is.** -/
theorem applyBindings_of_encode (bindings : Bindings) {pattern : Pattern} :
    ∀ {encoded}, encode [] pattern = some encoded → applyBindings bindings pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => intro _ read; simp [encode] at read
  | hfvar _ => intro _ read; simp [encode] at read
  | happly label arguments ih =>
    intro _ read
    have each := encode_arguments read
    rw [applyBindings]
    congr 1
    conv_rhs => rw [← List.map_id' arguments]
    exact List.map_congr_left fun argument member => by
      obtain ⟨_, argumentRead⟩ := each argument member
      exact ih argument member argumentRead
  | hlambda _ _ _ => intro _ read; simp [encode] at read
  | hmultiLambda _ _ _ _ => intro _ read; simp [encode] at read
  | hsubst _ _ _ _ => intro _ read; simp [encode] at read
  | hcollection _ _ _ _ => intro _ read; simp [encode] at read

/-! ## The steps of a first-order language -/

variable {relEnv : RelationEnv} {language : LanguageDef}

/-- **The reference steps of an equation-free, unconditional, aligned language are its root rewrites.** -/
theorem step_iff_rootReducts (free : language.isEquationFree = true) (profile : ReferenceProfile language)
    (unconditional : isUnconditionalAligned language = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) {source target : Pattern} :
    (referenceStructure relEnv language reading).step source .any target ↔
      IsState source ∧ IsState target ∧ target ∈ rootReducts language source := by
  rw [referenceStructure_eq_of_isEquationFree free reading, reference]
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, before, _, valid, _, after, _⟩
    rw [(objectEquivalent_iff_eq_of_isEquationFree free).mp before] at sourceState ⊢
    rw [← (objectEquivalent_iff_eq_of_isEquationFree free).mp after]
    refine ⟨sourceState, (objectEquivalent_iff_eq_of_isEquationFree free).mp after ▸ targetState, ?_⟩
    obtain ⟨fuel, member⟩ := Mettapedia.OSLF.MeTTaIL.ContextualStep.exists_mem_rewriteAt_iff_step.mpr
      ((contextualStep_iff_step relEnv language profile).mpr ⟨witness, valid⟩)
    cases fuel with
    | zero => simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt] at member
    | succ fuel => rwa [rewriteAt_succ_eq_rootReducts _ language unconditional fuel] at member
  · rintro ⟨sourceState, targetState, member⟩
    have stepped : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises relEnv) language source target :=
      Mettapedia.OSLF.MeTTaIL.ContextualStep.exists_mem_rewriteAt_iff_step.mp
        ⟨1, by rwa [rewriteAt_succ_eq_rootReducts _ language unconditional 0]⟩
    obtain ⟨witness, valid⟩ := (contextualStep_iff_step relEnv language profile).mp stepped
    exact ⟨sourceState, targetState, source, target, witness, Relation.EqvGen.refl _, sourceState, valid, targetState,
      Relation.EqvGen.refl _, rfl⟩

/-- Reaching with goals that agree on an invariant, along spans that agree on it. -/
theorem reaches_iff_of_agree {X : Type} {first second : ReductionSpan X} {firstGoal secondGoal : X → Prop}
    (good : X → Prop) (closed : ∀ event : first.Edge, good (first.source event) → good (first.target event))
    (agree : ∀ source target, good source →
      ((∃ event : first.Edge, first.source event = source ∧ first.target event = target) ↔
        ∃ event : second.Edge, second.source event = source ∧ second.target event = target))
    (goals : ∀ state, good state → (firstGoal state ↔ secondGoal state)) {state : X} (stateGood : good state) :
    Reaches first firstGoal state ↔ Reaches second secondGoal state := by
  have retarget : Reaches first firstGoal state ↔ Reaches first secondGoal state := by
    constructor
    · intro reaches
      induction reaches with
      | goal atGoal => exact .goal ((goals _ stateGood).mp atGoal)
      | step event _ ih => exact .step event (ih (closed event stateGood))
    · intro reaches
      induction reaches with
      | goal atGoal => exact .goal ((goals _ stateGood).mpr atGoal)
      | step event _ ih => exact .step event (ih (closed event stateGood))
  exact retarget.trans (reaches_transfer good closed agree stateGood)

/-- **From a ground first-order term, the reach formula holds exactly when the term reaches a goal by root steps.** -/
theorem sat_reachFormula_iff_reaches (free : language.isEquationFree = true) (profile : ReferenceProfile language)
    (unconditional : isUnconditionalAligned language = true) (herbrand : Profile language) {reading : LanguageReading}
    (reference : reading.rules = .reference) {goals : List Pattern}
    (groundGoals : ∀ goal ∈ goals, ∃ encoded, encode [] goal = some encoded) {term : Pattern} {encoded}
    (termRead : encode [] term = some encoded) :
    (referenceStructure relEnv language reading).sat Env.closed (reachFormula goals) term ↔
      Reaches (languageSpan language) (Goal goals) term := by
  rw [sat_reachFormula]
  refine (reaches_iff_of_agree (fun pattern => ∃ encoded, encode [] pattern = some encoded) ?_ ?_ ?_
    ⟨encoded, termRead⟩).symm
  · rintro ⟨⟨source, target⟩, member⟩ ⟨sourceEncoded, sourceRead⟩
    obtain ⟨targetEncoded, targetRead, _⟩ := step_forward herbrand sourceRead member
    exact ⟨targetEncoded, targetRead⟩
  · rintro source target ⟨sourceEncoded, sourceRead⟩
    constructor
    · rintro ⟨⟨⟨_, _⟩, member⟩, rfl, rfl⟩
      obtain ⟨targetEncoded, targetRead, _⟩ := step_forward herbrand sourceRead member
      exact ⟨⟨_, (step_iff_rootReducts free profile unconditional reference).mpr
        ⟨isState_of_encode sourceRead, isState_of_encode targetRead, member⟩⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨_, _⟩, step⟩, rfl, rfl⟩
      exact ⟨⟨_, ((step_iff_rootReducts free profile unconditional reference).mp step).2.2⟩, rfl, rfl⟩
  · rintro state ⟨_, stateRead⟩
    constructor
    · rintro ⟨goal, member, bindings, applied⟩
      obtain ⟨_, goalRead⟩ := groundGoals goal member
      rw [applyBindings_of_encode bindings goalRead] at applied
      subst applied
      exact ⟨goal, member, (isState_of_encode stateRead).2, Relation.EqvGen.refl _⟩
    · rintro ⟨goal, member, _, equivalent⟩
      have same := (objectEquivalent_iff_eq_of_isEquationFree (reading := reading) free).mp equivalent
      subst same
      obtain ⟨_, goalRead⟩ := groundGoals state member
      exact ⟨state, member, [], applyBindings_of_encode [] goalRead⟩

/-! ## The evidence -/

/-- **Whether backward search applies to a language**: equation-free, its rules without premises, aligned, first-order
and binding every variable of their right sides. -/
def backwardApplies (language : LanguageDef) : Bool :=
  language.isEquationFree && isUnconditionalAligned language && language.rewrites.all ruleAligned && profileCheck language

/-- The goals of a disjunction of names. -/
def goalsOf? {n : ℕ} : Formula n → Option (List Pattern)
  | .bot => some []
  | .is goal => some [goal]
  | .or (.is goal) rest => match goalsOf? rest with
    | some (next :: goals) => some (goal :: next :: goals)
    | _ => none
  | _ => none

theorem goalsOf?_eq {n : ℕ} : ∀ {formula : Formula n} {goals : List Pattern}, goalsOf? formula = some goals →
    formula = goalsFormula goals
  | .bot, goals, read => by
    simp only [goalsOf?, Option.some.injEq] at read
    subst read; rfl
  | .is goal, goals, read => by
    simp only [goalsOf?, Option.some.injEq] at read
    subst read; rfl
  | .or (.is goal) rest, goals, read => by
    simp only [goalsOf?] at read
    split at read
    · rename_i next tail tailRead
      simp only [Option.some.injEq] at read
      subst read
      rw [goalsOf?_eq tailRead]; rfl
    · cases read

/-- The goals of a reach formula. -/
def reachGoals? : Formula 0 → Option (List Pattern)
  | .mu (.or goals (.possibly .any (.var _))) => goalsOf? goals
  | _ => none

theorem reachGoals?_eq {formula : Formula 0} {goals : List Pattern} (read : reachGoals? formula = some goals) :
    formula = reachFormula goals := by
  unfold reachGoals? at read
  split at read
  · rename_i body index
    rw [goalsOf?_eq read, Fin.fin_one_eq_zero index]; rfl
  · cases read

/-- Every goal is a ground first-order term. -/
def groundGoals (goals : List Pattern) : Bool := goalsCheck goals && goals.all fun goal => (encode [] goal).isSome

/-- Some run of breadth-first backward search, up to the rounds, gives the answer. -/
def backwardDecides (language : LanguageDef) (goals : List Pattern) (term : Pattern) (rounds : ℕ)
    (answer : Presentation.Answer) : Bool :=
  (List.range (rounds + 1)).any fun fuel =>
    Mettapedia.OSLF.Framework.HerbrandBridge.answer language goals
      Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst fuel term == answer

/-- **Backward search establishes a reach formula**: it reaches the goals, or its dual saturates without them. -/
def reachEstablishes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match reachGoals? formula with
  | some goals => backwardApplies language && groundGoals goals && backwardDecides language goals term rounds .reaches
  | none => match reachGoals? formula.dual with
    | some goals => backwardApplies language && groundGoals goals && backwardDecides language goals term rounds .cannotReach
    | none => false

/-- **Backward search refutes a reach formula**: it saturates without the goals, or its dual reaches them. -/
def reachRefutes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match reachGoals? formula with
  | some goals => backwardApplies language && groundGoals goals && backwardDecides language goals term rounds .cannotReach
  | none => match reachGoals? formula.dual with
    | some goals => backwardApplies language && groundGoals goals && backwardDecides language goals term rounds .reaches
    | none => false

theorem backwardApplies_parts (applies : backwardApplies language = true) :
    language.isEquationFree = true ∧ ReferenceProfile language ∧ isUnconditionalAligned language = true ∧
      Profile language := by
  simp only [backwardApplies, Bool.and_eq_true] at applies
  exact ⟨applies.1.1.1, fun rule member => List.all_eq_true.mp applies.1.2 rule member, applies.1.1.2,
    Profile.of_check applies.2⟩

theorem groundGoals_parts {goals : List Pattern} (ground : groundGoals goals = true) :
    goalsCheck goals = true ∧ ∀ goal ∈ goals, ∃ encoded, encode [] goal = some encoded := by
  simp only [groundGoals, Bool.and_eq_true] at ground
  exact ⟨ground.1, fun goal member => Option.isSome_iff_exists.mp (List.all_eq_true.mp ground.2 goal member)⟩

theorem encode_of_answer {goals : List Pattern} {fuel : ℕ} {term : Pattern} {answer : Presentation.Answer}
    (decisive : answer ≠ .unknown)
    (read : Mettapedia.OSLF.Framework.HerbrandBridge.answer language goals
      Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst fuel term = answer) :
    ∃ encoded, encode [] term = some encoded := by
  unfold Mettapedia.OSLF.Framework.HerbrandBridge.answer at read
  split at read
  · rename_i encoded found
    exact ⟨encoded, found⟩
  · exact absurd read.symm decisive

/-- **What backward search decides about reaching the goals.** -/
theorem sat_reach_of_backward (applies : backwardApplies language = true) {goals : List Pattern}
    (ground : groundGoals goals = true) {reading : LanguageReading} (reference : reading.rules = .reference)
    {term : Pattern} {rounds : ℕ} :
    (backwardDecides language goals term rounds .reaches = true →
      (referenceStructure relEnv language reading).sat Env.closed (reachFormula goals) term) ∧
    (backwardDecides language goals term rounds .cannotReach = true →
      ¬ (referenceStructure relEnv language reading).sat Env.closed (reachFormula goals) term) := by
  obtain ⟨free, profile, unconditional, herbrand⟩ := backwardApplies_parts applies
  obtain ⟨checked, groundEach⟩ := groundGoals_parts ground
  constructor
  · intro decided
    obtain ⟨fuel, _, read⟩ := List.any_eq_true.mp decided
    have read := beq_iff_eq.mp read
    obtain ⟨encoded, termRead⟩ := encode_of_answer (by decide) read
    exact (sat_reachFormula_iff_reaches free profile unconditional herbrand reference groundEach termRead).mpr
      (Mettapedia.OSLF.Framework.HerbrandBridge.answer_reaches herbrand checked read)
  · intro decided
    obtain ⟨fuel, _, read⟩ := List.any_eq_true.mp decided
    have read := beq_iff_eq.mp read
    obtain ⟨encoded, termRead⟩ := encode_of_answer (by decide) read
    rw [sat_reachFormula_iff_reaches free profile unconditional herbrand reference groundEach termRead]
    exact Mettapedia.OSLF.Framework.HerbrandBridge.answer_cannotReach herbrand checked read

/-- **What backward search establishes of a reach formula holds.** -/
theorem reachEstablishes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : reachEstablishes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold reachEstablishes at checked
  cases read : reachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked
    rw [reachGoals?_eq read]
    exact (sat_reach_of_backward checked.1.1 checked.1.2 reference).1 checked.2
  | none =>
    cases readDual : reachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked
      have same : formula = (reachFormula goals).dual := by rw [← reachGoals?_eq readDual, Formula.dual_dual]
      rw [same, NativeStructure.sat_dual_closed]
      exact (sat_reach_of_backward checked.1.1 checked.1.2 reference).2 checked.2
    | none => simp [read, readDual] at checked

/-- **What backward search refutes of a reach formula fails.** -/
theorem reachRefutes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : reachRefutes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold reachRefutes at checked
  cases read : reachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked
    rw [reachGoals?_eq read]
    exact (sat_reach_of_backward checked.1.1 checked.1.2 reference).2 checked.2
  | none =>
    cases readDual : reachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked
      have same : formula = (reachFormula goals).dual := by rw [← reachGoals?_eq readDual, Formula.dual_dual]
      rw [same, NativeStructure.sat_dual_closed, not_not]
      exact (sat_reach_of_backward checked.1.1 checked.1.2 reference).1 checked.2
    | none => simp [read, readDual] at checked

/-- **Backward evidence persists**: what some rounds decide, more rounds decide. -/
theorem backwardDecides_mono {goals : List Pattern} {term : Pattern} {answer : Presentation.Answer} {rounds more : ℕ}
    (le : rounds ≤ more) (decided : backwardDecides language goals term rounds answer = true) :
    backwardDecides language goals term more answer = true := by
  obtain ⟨fuel, member, read⟩ := List.any_eq_true.mp decided
  exact List.any_eq_true.mpr ⟨fuel, List.mem_range.mpr (by have := List.mem_range.mp member; omega), read⟩

theorem reachEstablishes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : reachEstablishes language formula term rounds = true) :
    reachEstablishes language formula term more = true := by
  unfold reachEstablishes at checked ⊢
  cases read : reachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, backwardDecides_mono le checked.2⟩
  | none =>
    cases readDual : reachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, backwardDecides_mono le checked.2⟩
    | none => simp [read, readDual] at checked

theorem reachRefutes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : reachRefutes language formula term rounds = true) :
    reachRefutes language formula term more = true := by
  unfold reachRefutes at checked ⊢
  cases read : reachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, backwardDecides_mono le checked.2⟩
  | none =>
    cases readDual : reachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, backwardDecides_mono le checked.2⟩
    | none => simp [read, readDual] at checked

/-! ## Ancestors -/

/-- **Some ancestor is one of the goals**: `μX. (is g₁ ∨ … ∨ is gₖ) ∨ ⧫X`. -/
def pastReachFormula (goals : List Pattern) : Formula 0 := .mu (.or (goalsFormula goals) (.sometimeBefore .any (.var 0)))

/-- A run of steps from one element reaches another. -/
abbrev ReachesTo {Carrier : Type} (S : NativeStructure Carrier) (source target : Carrier) : Prop :=
  Reaches (HigherOrder.stepSpan S) (fun other => other = target) source

theorem reachesTo_snoc {Carrier : Type} {S : NativeStructure Carrier} {source middle target : Carrier}
    (reaches : ReachesTo S source middle) (step : S.step middle .any target) : ReachesTo S source target := by
  induction reaches with
  | goal atMiddle =>
    subst atMiddle
    exact Reaches.step (span := HigherOrder.stepSpan S) ⟨(_, target), step⟩ (.goal rfl)
  | step event _ ih => exact Reaches.step (span := HigherOrder.stepSpan S) event ih

/-- **Ancestry is a least fixed point**: the formula holds where some ancestor is named as a goal. -/
theorem sat_pastReachFormula {Carrier : Type} (S : NativeStructure Carrier) (goals : List Pattern) (element : Carrier) :
    S.sat Env.closed (pastReachFormula goals) element ↔
      ∃ goal ∈ goals, ∃ ancestor, S.named ancestor goal ∧ ReachesTo S ancestor element := by
  constructor
  · intro holds
    refine holds {other | ∃ goal ∈ goals, ∃ ancestor, S.named ancestor goal ∧ ReachesTo S ancestor other} ?_
    intro other prefixed
    rcases prefixed with atGoal | ⟨previous, step, inside⟩
    · obtain ⟨goal, member, named⟩ := (sat_goalsFormula S _ other goals).mp atGoal
      exact ⟨goal, member, other, named, .goal rfl⟩
    · obtain ⟨goal, member, ancestor, named, reaches⟩ := inside
      exact ⟨goal, member, ancestor, named, reachesTo_snoc reaches step⟩
  · rintro ⟨goal, member, ancestor, named, reaches⟩ closed prefixed
    have ancestorIn : ancestor ∈ closed :=
      prefixed _ (.inl ((sat_goalsFormula S _ ancestor goals).mpr ⟨goal, member, named⟩))
    clear named
    revert ancestorIn
    induction reaches with
    | goal atElement => intro inside; subst atElement; exact inside
    | step event _ ih =>
      intro inside
      exact ih (prefixed _ (.inr ⟨_, event.2, inside⟩))

/-- **An ancestor named by a ground goal is the goal reaching the term**, in an equation-free language. -/
theorem sat_pastReach_iff (free : language.isEquationFree = true) {reading : LanguageReading} {goals : List Pattern}
    (groundGoals : ∀ goal ∈ goals, ∃ encoded, encode [] goal = some encoded) {term : Pattern} {encoded}
    (termRead : encode [] term = some encoded) :
    (referenceStructure relEnv language reading).sat Env.closed (pastReachFormula goals) term ↔
      ∃ goal ∈ goals, (referenceStructure relEnv language reading).sat Env.closed (reachFormula [term]) goal := by
  have named : ∀ other, (referenceStructure relEnv language reading).named other term ↔ other = term := by
    intro other
    show IsObject other ∧ _ ↔ _
    rw [objectEquivalent_iff_eq_of_isEquationFree free]
    constructor
    · exact fun holds => holds.2
    · rintro rfl
      exact ⟨(isState_of_encode termRead).2, rfl⟩
  have samePredicate : (fun other => ∃ goal ∈ [term], (referenceStructure relEnv language reading).named other goal) =
      fun other => other = term := by
    funext other
    simp only [List.mem_singleton, exists_eq_left, named]
  rw [sat_pastReachFormula]
  constructor
  · rintro ⟨goal, member, ancestor, isGoal, reaches⟩
    have same : ancestor = goal := by
      have := isGoal.2
      rwa [objectEquivalent_iff_eq_of_isEquationFree free] at this
    subst same
    refine ⟨ancestor, member, (sat_reachFormula _ [term] ancestor).mpr ?_⟩
    rw [samePredicate]
    exact reaches
  · rintro ⟨goal, member, holds⟩
    have reaches := (sat_reachFormula _ [term] goal).mp holds
    rw [samePredicate] at reaches
    obtain ⟨_, goalRead⟩ := groundGoals goal member
    exact ⟨goal, member, goal, ⟨(isState_of_encode goalRead).2, Relation.EqvGen.refl _⟩, reaches⟩

/-- The goals of an ancestry formula. -/
def pastReachGoals? : Formula 0 → Option (List Pattern)
  | .mu (.or goals (.sometimeBefore .any (.var _))) => goalsOf? goals
  | _ => none

theorem pastReachGoals?_eq {formula : Formula 0} {goals : List Pattern} (read : pastReachGoals? formula = some goals) :
    formula = pastReachFormula goals := by
  unfold pastReachGoals? at read
  split at read
  · rename_i body index
    rw [goalsOf?_eq read, Fin.fin_one_eq_zero index]; rfl
  · cases read

/-- Some goal reaches the term, by backward search from the term. -/
def pastFound (language : LanguageDef) (goals : List Pattern) (term : Pattern) (rounds : ℕ) : Bool :=
  goals.any fun goal => backwardDecides language [term] goal rounds .reaches

/-- No goal reaches the term, by backward search from the term. -/
def pastExcluded (language : LanguageDef) (goals : List Pattern) (term : Pattern) (rounds : ℕ) : Bool :=
  goals.all fun goal => backwardDecides language [term] goal rounds .cannotReach

/-- **What backward search decides about ancestry.** -/
theorem sat_past_of_backward (applies : backwardApplies language = true) {goals : List Pattern}
    (ground : groundGoals goals = true) {term : Pattern} (termGround : groundGoals [term] = true)
    {reading : LanguageReading} (reference : reading.rules = .reference) {rounds : ℕ} :
    (pastFound language goals term rounds = true →
      (referenceStructure relEnv language reading).sat Env.closed (pastReachFormula goals) term) ∧
    (pastExcluded language goals term rounds = true →
      ¬ (referenceStructure relEnv language reading).sat Env.closed (pastReachFormula goals) term) := by
  obtain ⟨free, _, _, _⟩ := backwardApplies_parts applies
  obtain ⟨_, groundEach⟩ := groundGoals_parts ground
  obtain ⟨encoded, termRead⟩ := (groundGoals_parts termGround).2 term List.mem_cons_self
  constructor
  · intro found
    obtain ⟨goal, member, decided⟩ := List.any_eq_true.mp found
    exact (sat_pastReach_iff free groundEach termRead).mpr
      ⟨goal, member, (sat_reach_of_backward applies termGround reference).1 decided⟩
  · intro excluded holds
    obtain ⟨goal, member, reaches⟩ := (sat_pastReach_iff free groundEach termRead).mp holds
    exact (sat_reach_of_backward applies termGround reference).2 (List.all_eq_true.mp excluded goal member) reaches

/-- **Backward search establishes an ancestry formula**: a goal reaches the term, or, for the dual, none does. -/
def pastEstablishes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match pastReachGoals? formula with
  | some goals => backwardApplies language && groundGoals goals && groundGoals [term] &&
      pastFound language goals term rounds
  | none => match pastReachGoals? formula.dual with
    | some goals => backwardApplies language && groundGoals goals && groundGoals [term] &&
        pastExcluded language goals term rounds
    | none => false

/-- **Backward search refutes an ancestry formula**: no goal reaches the term, or, for the dual, one does. -/
def pastRefutes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match pastReachGoals? formula with
  | some goals => backwardApplies language && groundGoals goals && groundGoals [term] &&
      pastExcluded language goals term rounds
  | none => match pastReachGoals? formula.dual with
    | some goals => backwardApplies language && groundGoals goals && groundGoals [term] &&
        pastFound language goals term rounds
    | none => false

theorem pastEstablishes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : pastEstablishes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold pastEstablishes at checked
  cases read : pastReachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked
    rw [pastReachGoals?_eq read]
    exact (sat_past_of_backward checked.1.1.1 checked.1.1.2 checked.1.2 reference).1 checked.2
  | none =>
    cases readDual : pastReachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked
      have same : formula = (pastReachFormula goals).dual := by rw [← pastReachGoals?_eq readDual, Formula.dual_dual]
      rw [same, NativeStructure.sat_dual_closed]
      exact (sat_past_of_backward checked.1.1.1 checked.1.1.2 checked.1.2 reference).2 checked.2
    | none => simp [read, readDual] at checked

theorem pastRefutes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : pastRefutes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold pastRefutes at checked
  cases read : pastReachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked
    rw [pastReachGoals?_eq read]
    exact (sat_past_of_backward checked.1.1.1 checked.1.1.2 checked.1.2 reference).2 checked.2
  | none =>
    cases readDual : pastReachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked
      have same : formula = (pastReachFormula goals).dual := by rw [← pastReachGoals?_eq readDual, Formula.dual_dual]
      rw [same, NativeStructure.sat_dual_closed, not_not]
      exact (sat_past_of_backward checked.1.1.1 checked.1.1.2 checked.1.2 reference).1 checked.2
    | none => simp [read, readDual] at checked

theorem pastFound_mono {goals : List Pattern} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (found : pastFound language goals term rounds = true) : pastFound language goals term more = true := by
  obtain ⟨goal, member, decided⟩ := List.any_eq_true.mp found
  exact List.any_eq_true.mpr ⟨goal, member, backwardDecides_mono le decided⟩

theorem pastExcluded_mono {goals : List Pattern} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (excluded : pastExcluded language goals term rounds = true) : pastExcluded language goals term more = true :=
  List.all_eq_true.mpr fun goal member => backwardDecides_mono le (List.all_eq_true.mp excluded goal member)

theorem pastEstablishes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : pastEstablishes language formula term rounds = true) :
    pastEstablishes language formula term more = true := by
  unfold pastEstablishes at checked ⊢
  cases read : pastReachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, pastFound_mono le checked.2⟩
  | none =>
    cases readDual : pastReachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, pastExcluded_mono le checked.2⟩
    | none => simp [read, readDual] at checked

theorem pastRefutes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : pastRefutes language formula term rounds = true) :
    pastRefutes language formula term more = true := by
  unfold pastRefutes at checked ⊢
  cases read : pastReachGoals? formula with
  | some goals =>
    simp only [read, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, pastExcluded_mono le checked.2⟩
  | none =>
    cases readDual : pastReachGoals? formula.dual with
    | some goals =>
      simp only [read, readDual, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, pastFound_mono le checked.2⟩
    | none => simp [read, readDual] at checked

/-! ## Backward evidence -/

/-- **Backward search establishes the formula**: a reach formula or an ancestry formula, or the dual of one. -/
def backwardEstablishes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  reachEstablishes language formula term rounds || pastEstablishes language formula term rounds

/-- **Backward search refutes the formula.** -/
def backwardRefutes (language : LanguageDef) (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  reachRefutes language formula term rounds || pastRefutes language formula term rounds

theorem backwardEstablishes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : backwardEstablishes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  rcases Bool.or_eq_true_iff.mp checked with reach | past
  · exact reachEstablishes_sound reach reference
  · exact pastEstablishes_sound past reference

theorem backwardRefutes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : backwardRefutes language formula term rounds = true) {reading : LanguageReading}
    (reference : reading.rules = .reference) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term := by
  rcases Bool.or_eq_true_iff.mp checked with reach | past
  · exact reachRefutes_sound reach reference
  · exact pastRefutes_sound past reference

theorem backwardEstablishes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : backwardEstablishes language formula term rounds = true) :
    backwardEstablishes language formula term more = true := by
  rcases Bool.or_eq_true_iff.mp checked with reach | past
  · exact Bool.or_eq_true_iff.mpr (.inl (reachEstablishes_mono le reach))
  · exact Bool.or_eq_true_iff.mpr (.inr (pastEstablishes_mono le past))

theorem backwardRefutes_mono {formula : Formula 0} {term : Pattern} {rounds more : ℕ} (le : rounds ≤ more)
    (checked : backwardRefutes language formula term rounds = true) :
    backwardRefutes language formula term more = true := by
  rcases Bool.or_eq_true_iff.mp checked with reach | past
  · exact Bool.or_eq_true_iff.mpr (.inl (reachRefutes_mono le reach))
  · exact Bool.or_eq_true_iff.mpr (.inr (pastRefutes_mono le past))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
