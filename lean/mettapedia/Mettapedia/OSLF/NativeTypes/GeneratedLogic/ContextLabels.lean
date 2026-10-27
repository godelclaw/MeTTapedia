import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedExploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms

/-!
# Context labels: the steps of a term placed in a context

A context label `.context x C ℓ` ranges over the steps, with label `ℓ`, of the term placed in the context `C`: a
pattern whose metavariable `x` the term instantiates, as a rule's right side is instantiated (`plug`). These are the
labelled transitions of reactive systems, whose labels are what the environment supplies for the term to step.

- **A context step is a step of a placed presentation of the term** (`step_context_iff`): the term is read up to its
  equations, so the context receives any presentation of it.
- **In a congruent context it is a step of the term itself, placed** (`step_context_iff_plug`). Every context of an
  equation-free language is congruent (`congruent_of_isEquationFree`).
- **Placing a closed term at a fresh metavariable of a one-hole context is filling the hole** (`plug_fill`), so the
  context labels include the one-hole contexts of the language's presented context theory.
- **The modalities of a context label are the modalities at the placed term** (`sat_possibly_context_iff`,
  `sat_necessarily_context_iff`).
- **Complete successors decide the modal formulas** (`Successors`, `modalEval_exact`): with every label's successors of
  a term listed up to the equations, the connectives and the modalities are evaluated at the listed successors, and
  every other formula is left to a base decider.
- **Canonical forms list the successors** (`canonicalSuccessors`): at an admitted state, the steps listed at its
  canonical form; for a context label, those of the placed term, when the language's contexts are congruent on the
  domain (`CongruentOn`). They are in an equation-free language, with the identity as canonical forms
  (`equationFreeSuccessors`), and with sorted bags (`BagForms.congruentOn`, `bagSuccessors`), so context-labelled
  modalities are decided at the front door (`modalDecider`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

/-! ## Steps in a context -/

/-- **A context step is a step of a placed presentation of the term.** -/
theorem step_context_iff {hole : String} {context : Pattern} {label : StepLabel} {source target : Pattern} :
    (referenceStructure relEnv language reading).step source (.context hole context label) target ↔
      IsState source ∧ ∃ presentation, ObjectEquivalent relEnv language reading source presentation ∧
        IsState presentation ∧
          (referenceStructure relEnv language reading).step (plug hole context presentation) label target := by
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, ⟨presentation, presents, state, placedState, placed⟩,
      redexState, valid, contractumState, after, admits⟩
    exact ⟨sourceState, presentation, presents, state, placedState, targetState, redex, contractum, witness, placed,
      redexState, valid, contractumState, after, admits⟩
  · rintro ⟨sourceState, presentation, presents, state, placedState, targetState, redex, contractum, witness, placed,
      redexState, valid, contractumState, after, admits⟩
    exact ⟨sourceState, targetState, redex, contractum, witness, ⟨presentation, presents, state, placedState, placed⟩,
      redexState, valid, contractumState, after, admits⟩

variable (relEnv language reading) in
/-- **A congruent context**: equivalent states placed in it are equivalent states. -/
def Congruent (hole : String) (context : Pattern) : Prop :=
  ∀ ⦃first second : Pattern⦄, IsState first → IsState second →
    ObjectEquivalent relEnv language reading first second → IsState (plug hole context first) →
      IsState (plug hole context second) ∧
        ObjectEquivalent relEnv language reading (plug hole context first) (plug hole context second)

/-- **In a congruent context a context step is a step of the term itself, placed.** -/
theorem step_context_iff_plug {hole : String} {context : Pattern} (congruent : Congruent relEnv language reading hole context)
    {label : StepLabel} {source target : Pattern} (state : IsState source) :
    (referenceStructure relEnv language reading).step source (.context hole context label) target ↔
      (referenceStructure relEnv language reading).step (plug hole context source) label target := by
  rw [step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, presentationState, step⟩
    obtain ⟨placedState, same⟩ :=
      congruent presentationState state (ObjectEquivalent.equivalence.symm presents) step.1
    exact (referenceStructure_saturated relEnv language reading).stepSource
      (Indistinct.of_states step.1 placedState same) step
  · intro step
    exact ⟨state, source, Relation.EqvGen.refl _, state, step⟩

/-- **Every context of an equation-free language is congruent.** -/
theorem congruent_of_isEquationFree (free : language.isEquationFree = true) (hole : String) (context : Pattern) :
    Congruent relEnv language reading hole context := by
  intro first second _ _ equivalent placed
  rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
  subst equivalent
  exact ⟨placed, Relation.EqvGen.refl _⟩

/-- **Some step in a congruent context leads to a formula exactly when some step of the placed term does.** -/
theorem sat_possibly_context_iff {hole : String} {context : Pattern}
    (congruent : Congruent relEnv language reading hole context) {label : StepLabel} {source : Pattern}
    (state : IsState source) {n : ℕ} (env : Env Pattern n) (formula : Formula n) :
    (referenceStructure relEnv language reading).sat env (.possibly (.context hole context label) formula) source ↔
      (referenceStructure relEnv language reading).sat env (.possibly label formula) (plug hole context source) := by
  change (∃ next, _ ∧ _) ↔ (∃ next, _ ∧ _)
  simp only [step_context_iff_plug congruent state]

/-- **Every step in a congruent context leads to a formula exactly when every step of the placed term does.** -/
theorem sat_necessarily_context_iff {hole : String} {context : Pattern}
    (congruent : Congruent relEnv language reading hole context) {label : StepLabel} {source : Pattern}
    (state : IsState source) {n : ℕ} (env : Env Pattern n) (formula : Formula n) :
    (referenceStructure relEnv language reading).sat env (.necessarily (.context hole context label) formula) source ↔
      (referenceStructure relEnv language reading).sat env (.necessarily label formula) (plug hole context source) := by
  change (∀ next, _ → _) ↔ (∀ next, _ → _)
  simp only [step_context_iff_plug congruent state]

/-! ## Placing in a one-hole context -/

open Mettapedia.OSLF.MeTTaIL.Match (applyBindingsScoped applyBindingsScopedList_eq_map restSplice)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

mutual
/-- **A pattern that avoids a hole's name**: it has no metavariable or rest of that name, and no pending substitution. -/
def avoidsHole (hole : String) : Pattern → Bool
  | .bvar _ => true
  | .fvar name => name != hole
  | .apply _ arguments => avoidsHoleList hole arguments
  | .lambda _ body => avoidsHole hole body
  | .multiLambda _ _ body => avoidsHole hole body
  | .subst _ _ => false
  | .collection _ elements rest => avoidsHoleList hole elements && rest != some hole

/-- Every pattern of a list avoids the hole's name. -/
def avoidsHoleList (hole : String) : List Pattern → Bool
  | [] => true
  | pattern :: patterns => avoidsHole hole pattern && avoidsHoleList hole patterns
end

theorem avoidsHoleList_iff {hole : String} : ∀ {patterns : List Pattern},
    avoidsHoleList hole patterns = true ↔ ∀ pattern ∈ patterns, avoidsHole hole pattern = true
  | [] => by simp [avoidsHoleList]
  | _ :: _ => by simp [avoidsHoleList, avoidsHoleList_iff]

/-- **Instantiating the hole leaves a pattern that avoids it unchanged.** -/
theorem applyBindingsScoped_avoids {hole : String} (term : Pattern) :
    ∀ (pattern : Pattern) (depth : ℕ), avoidsHole hole pattern = true →
      applyBindingsScoped (.fvar hole) [(hole, term)] depth pattern = pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar _ => intro _ _; simp [applyBindingsScoped]
  | hfvar name =>
    intro _ avoids
    simp only [avoidsHole, bne_iff_ne, ne_eq] at avoids
    have differs : (hole == name) = false := beq_false_of_ne (Ne.symm avoids)
    simp [applyBindingsScoped, List.find?, differs]
  | happly constructor arguments inner =>
    intro depth avoids
    simp only [avoidsHole, avoidsHoleList_iff] at avoids
    simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]
    congr 1
    conv => rhs; rw [← List.map_id arguments]
    exact List.map_congr_left fun argument member => inner argument member depth (avoids argument member)
  | hlambda _ body inner =>
    intro depth avoids
    simp only [avoidsHole] at avoids
    simp only [applyBindingsScoped]
    rw [inner _ avoids]
  | hmultiLambda _ _ body inner =>
    intro depth avoids
    simp only [avoidsHole] at avoids
    simp only [applyBindingsScoped]
    rw [inner _ avoids]
  | hsubst _ _ _ _ => intro _ avoids; simp [avoidsHole] at avoids
  | hcollection kind elements rest inner =>
    intro depth avoids
    simp only [avoidsHole, Bool.and_eq_true, avoidsHoleList_iff, bne_iff_ne, ne_eq] at avoids
    have elementsSame : elements.map (applyBindingsScoped (.fvar hole) [(hole, term)] depth) = elements := by
      conv => rhs; rw [← List.map_id elements]
      exact List.map_congr_left fun element member => inner element member depth (avoids.1 element member)
    have restSame : restSplice (.fvar hole) [(hole, term)] depth kind rest = ([], rest) := by
      cases rest with
      | none => rfl
      | some name =>
        have differs : (hole == name) = false :=
          beq_false_of_ne fun same => avoids.2 (by rw [same])
        simp [restSplice, List.find?, differs]
    simp only [applyBindingsScoped, applyBindingsScopedList_eq_map, elementsSame, restSame, List.append_nil]

/-- **A one-hole context that avoids a hole's name**: its sides avoid it, it has no pending substitution around the
hole, and no rest of that name. -/
def contextAvoidsHole (hole : String) : OneHoleContext → Bool
  | .hole => true
  | .apply _ before inner after =>
    avoidsHoleList hole before && contextAvoidsHole hole inner && avoidsHoleList hole after
  | .lambda _ inner => contextAvoidsHole hole inner
  | .multiLambda _ _ inner => contextAvoidsHole hole inner
  | .substBody _ _ => false
  | .substReplacement _ _ => false
  | .collection _ before inner after rest =>
    avoidsHoleList hole before && contextAvoidsHole hole inner && avoidsHoleList hole after &&
      rest != some hole

theorem map_applyBindingsScoped_avoids {hole : String} (term : Pattern) (depth : ℕ) {patterns : List Pattern}
    (avoids : avoidsHoleList hole patterns = true) :
    patterns.map (applyBindingsScoped (.fvar hole) [(hole, term)] depth) = patterns := by
  conv => rhs; rw [← List.map_id patterns]
  exact List.map_congr_left fun pattern member =>
    applyBindingsScoped_avoids term pattern depth (avoidsHoleList_iff.mp avoids pattern member)

/-- **Placing a closed term in a one-hole context that avoids the hole's name fills it**: the scope-correct
instantiation of the hole is the textual filling, at any depth. -/
theorem applyBindingsScoped_fill {hole : String} {term : Pattern} (closed : term.isWellScopedAt 0 = true) :
    ∀ (context : OneHoleContext) (depth : ℕ), contextAvoidsHole hole context = true →
      applyBindingsScoped (.fvar hole) [(hole, term)] depth (context.fill (.fvar hole)) = context.fill term
  | .hole, depth, _ => by
    simp [OneHoleContext.fill, applyBindingsScoped, List.find?, Mettapedia.OSLF.MeTTaIL.Match.captureDepth,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt closed]
  | .apply constructor before inner after, depth, avoids => by
    simp only [contextAvoidsHole, Bool.and_eq_true] at avoids
    simp only [OneHoleContext.fill, applyBindingsScoped, applyBindingsScopedList_eq_map, List.map_append,
      List.map_cons, map_applyBindingsScoped_avoids term depth avoids.1.1,
      map_applyBindingsScoped_avoids term depth avoids.2, applyBindingsScoped_fill closed inner depth avoids.1.2]
  | .lambda binder inner, depth, avoids => by
    simp only [contextAvoidsHole] at avoids
    simp only [OneHoleContext.fill, applyBindingsScoped, applyBindingsScoped_fill closed inner (depth + 1) avoids]
  | .multiLambda arity binders inner, depth, avoids => by
    simp only [contextAvoidsHole] at avoids
    simp only [OneHoleContext.fill, applyBindingsScoped, applyBindingsScoped_fill closed inner (depth + arity) avoids]
  | .substBody _ _, _, avoids => by simp [contextAvoidsHole] at avoids
  | .substReplacement _ _, _, avoids => by simp [contextAvoidsHole] at avoids
  | .collection kind before inner after rest, depth, avoids => by
    simp only [contextAvoidsHole, Bool.and_eq_true, bne_iff_ne, ne_eq] at avoids
    have restSame : restSplice (.fvar hole) [(hole, term)] depth kind rest = ([], rest) := by
      cases rest with
      | none => rfl
      | some name =>
        have differs : (hole == name) = false :=
          beq_false_of_ne fun same => avoids.2 (by rw [same])
        simp [restSplice, List.find?, differs]
    simp only [OneHoleContext.fill, applyBindingsScoped, applyBindingsScopedList_eq_map, List.map_append,
      List.map_cons, map_applyBindingsScoped_avoids term depth avoids.1.1.1,
      map_applyBindingsScoped_avoids term depth avoids.1.2, applyBindingsScoped_fill closed inner depth avoids.1.1.2,
      restSame, List.append_nil]

/-- **Placing a closed term in a one-hole context that avoids the hole's name is filling it.** -/
theorem plug_fill {hole : String} (context : OneHoleContext) (avoids : contextAvoidsHole hole context = true)
    {term : Pattern} (closed : term.isWellScopedAt 0 = true) :
    plug hole (context.fill (.fvar hole)) term = context.fill term :=
  applyBindingsScoped_fill closed context 0 avoids

/-! ## Complete successors decide the modal formulas -/

variable (relEnv language reading) in
/-- **Complete successors**: for a label and a term, a list of terms the term steps to with the label, holding a
representative, up to the equations, of every one. -/
structure Successors where
  list : StepLabel → Pattern → Option (List Pattern)
  sound : ∀ {label term next}, list label term = some next → ∀ target ∈ next,
    (referenceStructure relEnv language reading).step term label target
  complete : ∀ {label term next}, list label term = some next → ∀ target,
    (referenceStructure relEnv language reading).step term label target →
      ∃ listed ∈ next, ObjectEquivalent relEnv language reading listed target

/-- Some answer is yes, or every answer is no. -/
def anyOf (answers : List (Option Bool)) : Option Bool :=
  if answers.any (· == some true) then some true else if answers.all (· == some false) then some false else none

/-- Every answer is yes, or some answer is no. -/
def allOf (answers : List (Option Bool)) : Option Bool :=
  if answers.any (· == some false) then some false else if answers.all (· == some true) then some true else none

theorem anyOf_true {answers : List (Option Bool)} (found : anyOf answers = some true) :
    ∃ answer ∈ answers, answer = some true := by
  unfold anyOf at found
  split at found
  · rename_i some
    simpa using some
  · split at found <;> cases found

theorem anyOf_false {answers : List (Option Bool)} (found : anyOf answers = some false) :
    ∀ answer ∈ answers, answer = some false := by
  unfold anyOf at found
  split at found
  · cases found
  · split at found
    · rename_i every
      simpa using every
    · cases found

theorem allOf_true {answers : List (Option Bool)} (found : allOf answers = some true) :
    ∀ answer ∈ answers, answer = some true := by
  unfold allOf at found
  split at found
  · cases found
  · split at found
    · rename_i every
      simpa using every
    · cases found

theorem allOf_false {answers : List (Option Bool)} (found : allOf answers = some false) :
    ∃ answer ∈ answers, answer = some false := by
  unfold allOf at found
  split at found
  · rename_i some
    simpa using some
  · split at found <;> cases found

/-- How deep the connectives and step modalities nest. -/
def Formula.modalHeight : {n : ℕ} → Formula n → ℕ
  | _, .and left right | _, .or left right => max left.modalHeight right.modalHeight + 1
  | _, .possibly _ inner | _, .necessarily _ inner => inner.modalHeight + 1
  | _, _ => 0

variable (successors : Successors relEnv language reading) (base : Formula 0 → Pattern → Option Bool)

/-- **The modal formulas, evaluated at the listed successors to a depth**: the connectives and the step modalities,
every other formula, and every formula beyond the depth, left to the base. -/
def modalEvalAt : ℕ → Formula 0 → Pattern → Option Bool
  | 0, formula, term => base formula term
  | depth + 1, formula, term =>
    match formula with
    | .top => some true
    | .bot => some false
    | .and left right =>
      match modalEvalAt depth left term, modalEvalAt depth right term with
      | some first, some second => some (first && second)
      | _, _ => none
    | .or left right =>
      match modalEvalAt depth left term, modalEvalAt depth right term with
      | some first, some second => some (first || second)
      | _, _ => none
    | .possibly label inner =>
      match successors.list label term with
      | some next => anyOf (next.map fun target => modalEvalAt depth inner target)
      | none => none
    | .necessarily label inner =>
      match successors.list label term with
      | some next => allOf (next.map fun target => modalEvalAt depth inner target)
      | none => none
    | other => base other term

/-- **The modal formulas, evaluated at the listed successors**, deep enough to reach their innermost formers. -/
def modalEval (formula : Formula 0) (term : Pattern) : Option Bool :=
  modalEvalAt successors base (formula.modalHeight + 1) formula term

variable {successors base}

/-- **The evaluation is exact** where the base is, at every depth. -/
theorem modalEvalAt_exact
    (baseExact : ∀ {formula term answer}, base formula term = some answer →
      ((referenceStructure relEnv language reading).sat Env.closed formula term ↔ answer = true)) :
    ∀ (depth : ℕ) (formula : Formula 0) {term : Pattern} {answer : Bool},
      modalEvalAt successors base depth formula term = some answer →
        ((referenceStructure relEnv language reading).sat Env.closed formula term ↔ answer = true)
  | 0, _, _, _, decided => baseExact decided
  | depth + 1, formula, term, answer, decided => by
    have innerExact : ∀ (inner : Formula 0) (target : Pattern) {answer : Bool},
        modalEvalAt successors base depth inner target = some answer →
          ((referenceStructure relEnv language reading).sat Env.closed inner target ↔ answer = true) :=
      fun inner _ _ => modalEvalAt_exact baseExact depth inner
    unfold modalEvalAt at decided
    split at decided
    · cases decided
      exact iff_of_true trivial rfl
    · cases decided
      exact iff_of_false id Bool.false_ne_true
    · rename_i left right
      split at decided
      · rename_i first second leftDecided rightDecided
        cases decided
        change (_ ∧ _) ↔ _
        rw [innerExact left term leftDecided, innerExact right term rightDecided, Bool.and_eq_true]
      · cases decided
    · rename_i left right
      split at decided
      · rename_i first second leftDecided rightDecided
        cases decided
        change (_ ∨ _) ↔ _
        rw [innerExact left term leftDecided, innerExact right term rightDecided, Bool.or_eq_true]
      · cases decided
    · rename_i label inner
      split at decided
      · rename_i next listed
        change (∃ next, _ ∧ _) ↔ _
        cases answer with
        | true =>
          obtain ⟨found, member, same⟩ := anyOf_true decided
          obtain ⟨target, targetMember, rfl⟩ := List.mem_map.mp member
          exact iff_of_true ⟨target, successors.sound listed target targetMember, (innerExact inner target same).mpr rfl⟩
            rfl
        | false =>
          refine iff_of_false ?_ Bool.false_ne_true
          rintro ⟨target, step, holds⟩
          obtain ⟨listedTarget, member, equivalent⟩ := successors.complete listed target step
          have answered := anyOf_false decided _ (List.mem_map_of_mem member)
          have listedStep := successors.sound listed listedTarget member
          exact Bool.false_ne_true ((innerExact inner listedTarget answered).mp
            ((sat_respects_equivalent relEnv language inner listedStep.2.1 step.2.1 equivalent).mpr holds))
      · cases decided
    · rename_i label inner
      split at decided
      · rename_i next listed
        change (∀ next, _ → _) ↔ _
        cases answer with
        | true =>
          refine iff_of_true ?_ rfl
          intro target step
          obtain ⟨listedTarget, member, equivalent⟩ := successors.complete listed target step
          have answered := allOf_true decided _ (List.mem_map_of_mem member)
          have listedStep := successors.sound listed listedTarget member
          exact (sat_respects_equivalent relEnv language inner listedStep.2.1 step.2.1 equivalent).mp
            ((innerExact inner listedTarget answered).mpr rfl)
        | false =>
          refine iff_of_false ?_ Bool.false_ne_true
          intro every
          obtain ⟨found, member, same⟩ := allOf_false decided
          obtain ⟨target, targetMember, rfl⟩ := List.mem_map.mp member
          exact Bool.false_ne_true
            ((innerExact inner target same).mp (every target (successors.sound listed target targetMember)))
      · cases decided
    · exact baseExact decided

/-- **A certified decider of the modal formulas**: the evaluation at listed successors, with a decider as the base. -/
def modalDecider (successors : Successors relEnv language reading) (base : Decider relEnv language reading) :
    Decider relEnv language reading where
  decide := modalEval successors base.decide
  exact := modalEvalAt_exact base.exact _ _

/-! ## Successors from canonical forms -/

section Canonical

variable (relEnv language) (fuel : ℕ) (canon : Pattern → Pattern) (domain : Pattern → Bool)
  (presentations : Pattern → List Pattern) (reading)

/-- **Contexts congruent on the domain**: placing equivalent states keeps being a state or not, and, where the placed
term is admitted, gives equivalent terms. -/
def CongruentOn : Prop :=
  ∀ (hole : String) (context : Pattern) ⦃first second : Pattern⦄, IsState first → IsState second →
    ObjectEquivalent relEnv language reading first second →
      (IsState (plug hole context first) ↔ IsState (plug hole context second)) ∧
        (IsState (plug hole context first) → domain (plug hole context second) = true →
          ObjectEquivalent relEnv language reading (plug hole context first) (plug hole context second))

/-- **The successors read off canonical forms**: at an admitted state the fuel lists completely at its canonical form,
the steps listed there whose witness the label admits, when they are admitted states; for a context label, those of
the placed term, when it is admitted. A term that is no state has none. -/
def canonicalList : StepLabel → Pattern → Option (List Pattern)
  | .context hole context label, term =>
    if isStateBool term then
      if isStateBool (plug hole context term) then
        if domain (plug hole context term) then canonicalList label (plug hole context term) else none
      else some []
    else some []
  | .any, term => listedOwn .any term
  | .rule index, term => listedOwn (.rule index) term
  | .under index label, term => listedOwn (.under index label) term
where
  /-- The listed steps of the term's own, with a label of its own. -/
  listedOwn (label : StepLabel) (term : Pattern) : Option (List Pattern) :=
    if isStateBool term then
      if domain term && enoughAt relEnv language fuel presentations (canon term) reading.rules &&
          (presentations (canon term)).all (fun shown => domain shown && canon shown == canon term) then
        if ((listedAt relEnv language fuel presentations (canon term) reading.rules).filter
            fun entry => label.admits entry.1).all fun entry => isStateBool entry.2 && domain entry.2 then
          some (((listedAt relEnv language fuel presentations (canon term) reading.rules).filter
            fun entry => label.admits entry.1).map (·.2))
        else none
      else none
    else some []

variable {relEnv language fuel canon domain presentations reading}

theorem listedOwn_sound (canonical : Canonical relEnv language canon domain reading) {label : StepLabel}
    {term : Pattern} {next : List Pattern}
    (listed : canonicalList.listedOwn relEnv language reading fuel canon domain presentations label term = some next) :
    ∀ target ∈ next, (referenceStructure relEnv language reading).step term label target := by
  intro target member
  unfold canonicalList.listedOwn at listed
  split at listed
  · rename_i termState
    split at listed
    · rename_i checks
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checks
      obtain ⟨⟨termAdmitted, -⟩, shownCanonical⟩ := checks
      split at listed
      · rename_i statesAdmitted
        cases listed
        obtain ⟨entry, kept, rfl⟩ := List.mem_map.mp member
        obtain ⟨listedEntry, admitted⟩ := List.mem_filter.mp kept
        have entryChecks := List.all_eq_true.mp statesAdmitted entry kept
        simp only [Bool.and_eq_true] at entryChecks
        obtain ⟨shown, shownMember, stepped⟩ := mem_listedAt.mp listedEntry
        obtain ⟨shownAdmitted, shownCanon⟩ := shownCanonical shown shownMember
        have canonState := canonical.state termAdmitted (isState_of_bool termState)
        have shownState := canonical.state_of_canon shownAdmitted (shownCanon ▸ canonState)
        have toShown : ObjectEquivalent relEnv language reading term shown :=
          Relation.EqvGen.trans _ _ _ (canonical.equivalent termAdmitted)
            (shownCanon ▸ ObjectEquivalent.equivalence.symm (canonical.equivalent shownAdmitted))
        exact ⟨isState_of_bool termState, isState_of_bool entryChecks.1, shown, entry.2, entry.1,
          (placed_iff (StepLabel.isContext_of_admits admitted)).mpr toShown, shownState,
          ruleValid_of_mem_ruleSteps stepped, isState_of_bool entryChecks.1, Relation.EqvGen.refl _,
          StepLabel.base_admits admitted⟩
      · cases listed
    · cases listed
  · cases listed
    cases member

theorem listedOwn_complete (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading) {label : StepLabel}
    (own : label.isContext = false) {term : Pattern} {next : List Pattern}
    (listed : canonicalList.listedOwn relEnv language reading fuel canon domain presentations label term = some next) :
    ∀ target, (referenceStructure relEnv language reading).step term label target →
      ∃ listed ∈ next, ObjectEquivalent relEnv language reading listed target := by
  rintro target ⟨termState, targetState, redex, contractum, witness, before, redexState, valid, contractumState, after,
    admits⟩
  rw [placed_iff own] at before
  unfold canonicalList.listedOwn at listed
  rw [if_pos (isStateBool_of_isState termState)] at listed
  split at listed
  · rename_i checks
    simp only [Bool.and_eq_true] at checks
    obtain ⟨⟨termAdmitted, complete⟩, -⟩ := checks
    split at listed
    · rename_i statesAdmitted
      cases listed
      obtain ⟨entry, member, sameLabels, sameCanon⟩ :=
        coherent (canonical.state termAdmitted termState) (canonical.admitted_canon termAdmitted)
          (canonical.idempotent termAdmitted) complete
          (Relation.EqvGen.trans _ _ _ (ObjectEquivalent.equivalence.symm (canonical.equivalent termAdmitted)) before)
          redexState valid
      have kept : entry ∈ (listedAt relEnv language fuel presentations (canon term) reading.rules).filter
          fun entry => label.admits entry.1 :=
        List.mem_filter.mpr ⟨member, (sameLabels label).symm.trans (StepLabel.admits_of_base own admits)⟩
      have entryChecks := List.all_eq_true.mp statesAdmitted entry kept
      simp only [Bool.and_eq_true] at entryChecks
      have contractumAdmitted : domain contractum = true :=
        canonical.stepsAdmitted (canonical.invariant termAdmitted before) redexState valid
          (sameCanon ▸ canonical.admitted_canon entryChecks.2)
      exact ⟨entry.2, List.mem_map_of_mem kept, Relation.EqvGen.trans _ _ _
        ((canonical.equivalent_iff entryChecks.2 contractumAdmitted).mpr sameCanon) after⟩
    · cases listed
  · cases listed

theorem canonicalList_sound (canonical : Canonical relEnv language canon domain reading) :
    ∀ {label : StepLabel} {term : Pattern} {next : List Pattern},
      canonicalList relEnv language reading fuel canon domain presentations label term = some next →
        ∀ target ∈ next, (referenceStructure relEnv language reading).step term label target
  | .context hole context label, term, next, listed => by
    intro target member
    unfold canonicalList at listed
    split at listed
    · rename_i termState
      split at listed
      · split at listed
        · exact step_context_iff.mpr ⟨isState_of_bool termState, term, Relation.EqvGen.refl _,
            isState_of_bool termState, canonicalList_sound canonical listed target member⟩
        · cases listed
      · cases listed
        cases member
    · cases listed
      cases member
  | .any, _, _, listed => listedOwn_sound canonical listed
  | .rule _, _, _, listed => listedOwn_sound canonical listed
  | .under _ _, _, _, listed => listedOwn_sound canonical listed

theorem canonicalList_complete (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (congruent : CongruentOn relEnv language reading domain) :
    ∀ {label : StepLabel} {term : Pattern} {next : List Pattern},
      canonicalList relEnv language reading fuel canon domain presentations label term = some next →
        ∀ target, (referenceStructure relEnv language reading).step term label target →
          ∃ listed ∈ next, ObjectEquivalent relEnv language reading listed target
  | .context hole context label, term, next, listed => by
    intro target step
    obtain ⟨termState, presentation, presents, presentationState, placedStep⟩ := step_context_iff.mp step
    obtain ⟨sameState, sameTerm⟩ := congruent hole context presentationState termState
      (ObjectEquivalent.equivalence.symm presents)
    unfold canonicalList at listed
    rw [if_pos (isStateBool_of_isState termState),
      if_pos (isStateBool_of_isState (sameState.mp placedStep.1))] at listed
    split at listed
    · rename_i placedAdmitted
      have moved : (referenceStructure relEnv language reading).step (plug hole context term) label target :=
        (referenceStructure_saturated relEnv language reading).stepSource
          (Indistinct.of_states placedStep.1 (sameState.mp placedStep.1) (sameTerm placedStep.1 placedAdmitted))
          placedStep
      exact canonicalList_complete canonical coherent congruent listed target moved
    · cases listed
  | .any, _, _, listed => listedOwn_complete canonical coherent rfl listed
  | .rule _, _, _, listed => listedOwn_complete canonical coherent rfl listed
  | .under _ _, _, _, listed => listedOwn_complete canonical coherent rfl listed

variable (fuel presentations) in
/-- **The successors read off canonical forms**, context labels included, for contexts congruent on the domain. -/
def canonicalSuccessors (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (congruent : CongruentOn relEnv language reading domain) : Successors relEnv language reading where
  list := canonicalList relEnv language reading fuel canon domain presentations
  sound := canonicalList_sound canonical
  complete := canonicalList_complete canonical coherent congruent

end Canonical

/-! ## Named terms by canonical forms -/

variable (canon : Pattern → Pattern) (domain : Pattern → Bool) in
/-- **Named terms decided by canonical forms**: an admitted term is an admitted object term exactly when they have one
canonical form. -/
def namedDecider (canonical : Canonical relEnv language canon domain reading) : Decider relEnv language reading where
  decide formula term :=
    match formula with
    | .is named => if domain term && domain named then some (canon term == canon named) else none
    | .isNot named => if domain term && domain named then some !(canon term == canon named) else none
    | _ => none
  exact := by
    intro formula term answer decided
    split at decided
    · rename_i named
      split at decided
      · rename_i admitted
        simp only [Bool.and_eq_true] at admitted
        cases decided
        change (IsObject term ∧ ObjectEquivalent relEnv language reading term named) ↔ _
        rw [beq_iff_eq, ← canonical.equivalent_iff admitted.1 admitted.2]
        exact and_iff_right (canonical.object admitted.1)
      · cases decided
    · rename_i named
      split at decided
      · rename_i admitted
        simp only [Bool.and_eq_true] at admitted
        cases decided
        change ¬ (IsObject term ∧ ObjectEquivalent relEnv language reading term named) ↔ _
        rw [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, ← canonical.equivalent_iff admitted.1 admitted.2]
        exact not_congr (and_iff_right (canonical.object admitted.1))
      · cases decided
    · cases decided

/-! ## Equation-free languages and sorted bags -/

/-- **In an equation-free language every context is congruent.** -/
theorem congruentOn_of_isEquationFree (free : language.isEquationFree = true) (domain : Pattern → Bool) :
    CongruentOn relEnv language reading domain := by
  intro hole context first second _ _ equivalent
  rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
  subst equivalent
  exact ⟨Iff.rfl, fun _ _ => Relation.EqvGen.refl _⟩

variable (fuel : ℕ) in
/-- **The successors of an equation-free language**: its identity canonical forms. -/
def equationFreeSuccessors (free : language.isEquationFree = true) : Successors relEnv language .syntax :=
  canonicalSuccessors fuel List.singleton (identity_canonical free) (identity_coherent free)
    (congruentOn_of_isEquationFree free _)

/-- **With sorted bags every context is congruent on the domain**: equivalent terms have one canonical form, so their
placements do, and admitted terms with one canonical form are equivalent. -/
theorem BagForms.congruentOn (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) :
    CongruentOn relEnv language .syntax (BagForms.domain language) := by
  intro hole context first second _ _ equivalent
  have same : Mettapedia.OSLF.MeTTaIL.CanonicalBags.Same (plug hole context first) (plug hole context second) :=
    BagForms.applyBindingsScoped_same (.fvar hole) (left := [(hole, first)]) (right := [(hole, second)])
      (.cons ⟨rfl, BagForms.canon_eq_of_equivalent noEquations noAlgebra equivalent⟩ .nil) 0 context
  have stateIff : ∀ {term : Pattern}, IsState term ↔
      (Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon term).isWellScopedAt 0 = true ∧
        isObjectPattern (Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon term) = true := by
    intro term
    rw [BagForms.canon_wellScoped, BagForms.canon_object]
  refine ⟨by rw [stateIff, stateIff, same], fun placedState secondAdmitted => ?_⟩
  have firstAdmitted : BagForms.domain language (plug hole context first) = true := by
    unfold BagForms.domain at secondAdmitted ⊢
    rw [BagForms.sortBags_eq_canon] at secondAdmitted ⊢
    rw [same]
    exact secondAdmitted
  exact ((BagForms.canonical noEquations noAlgebra).equivalent_iff firstAdmitted secondAdmitted).mpr
    (by rw [BagForms.sortBags_eq_canon]; exact same)

variable (fuel : ℕ) in
/-- **The successors of a language with sorted bags**, context labels included. -/
def bagSuccessors (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (guarded : language.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true) :
    Successors relEnv language .syntax :=
  canonicalSuccessors fuel List.singleton (BagForms.canonical noEquations noAlgebra)
    (BagForms.coherent noEquations noAlgebra guarded fuel) (BagForms.congruentOn noEquations noAlgebra)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
