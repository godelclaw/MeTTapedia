import Mettapedia.Logic.HostingStyles.AmbientRegions.AllHeaded
import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedNested

/-!
# Every root step headed: what the presentation hosts, and what it pays

For `allHeaded`, the presentation in which the ambient root step and the root
step of a run are both headed by the constructors of atoms:

* **Nothing is lost for tables without a variable as a left side**
  (`allHeaded_atom_step_iff`, `allHeaded_hostOf_tabularAt`,
  `allHeaded_hostOf_scopedTabularAt`): at the space of such a table the
  presentation is a host of its theories, on terms and with all contexts.
* **The run of the atom of a term computes by such rules of its space, at
  every ambient space** (`allHeaded_runAtom_step_iff`): positive
  `allHeaded_runCoin_steps`, negative `allHeaded_runCoin_normal`.
* **A run in a run, instances** (`allHeaded_nested_inner_steps`,
  `allHeaded_nested_outer_unseen`): the inner run steps by its own space and
  sees neither the outer space nor the ambient space, whatever they store.
  In `headedContained` the outer space rewrites the inner run as a whole
  (`headed_nested_presentations_differ`).
* **What is paid** (`allHeaded_variableRule_not_preserved`): a rule whose left
  side is a variable does not fire on a bound variable inside a run either;
  in `headedContained` it does.
* **A weak evaluator, containment and static spaces together**
  (`allHeaded_weak_contained_static`): the unchanged evaluator answers by
  stored rules, the steps of a run are the runs of the steps of its subject
  in the member at its space, and no space and no name has a transition.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory inst substitute inst_eq_substitute patternVars usesOnly
    withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Logic.HostingStyles.LocatedAtoms (takeAll)

variable {admits : Pattern → Bool}

/-! ## Atoms outside a run: tables without a variable as a left side -/

/-- A step from the atom of a term is the atom of a step of the term, in
every theory whose steps at the root include what the ambient space answers
for the atoms of terms. -/
theorem allHeaded_atom_stepAt_sound {ambientSpace : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ admittedAnswers admits ambientSpace (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) allHeaded fuel (atomAt depth source) target →
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, shape, applied⟩ := beta_inv matched premises
          obtain ⟨function, argumentTerm, rfl, functionEq, rfl⟩ := atomAt_eq_app shape
          obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam functionEq.symm
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          exact ⟨subst0 argumentTerm bodyTerm, by rw [applied, instantiateBVar_atomAt],
            Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appFunction_inv matched premises
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.app nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.appFunction .hole second)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appArgument_inv matched premises
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.app first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.appArgument first .hole)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piDomain_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.pi nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.piDomain .hole second)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piBody_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.pi first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.piBody first .hole)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ :=
            lamDomain_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.lam nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.lamDomain .hole second)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := lamBody_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.lam first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.lamBody first .hole)⟩
        · exact absurd matched (atomAt_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers found
        exact ⟨nextTerm, applied, rootStep⟩
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
        rw [shape] at matched
        exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
        rw [shape] at matched
        exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
        rw [shape] at matched
        exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))

/-- Every step of a term, by the rules of a list none of whose left sides is
a variable, is a step between the atoms. -/
theorem allHeaded_atom_stepAt_complete (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (regionEvaluator admits (ruleSpace rules)) allHeaded fuel
      (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              have fired := step_beta (base := regionEvaluator admits (ruleSpace rules))
                (lang := allHeaded) (allHeaded_mem_plain (by simp))
                (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
              rw [instantiateBVar_atomAt] at fired
              exact ⟨1, fired⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_headedRoot_atomAt (fun other inRoots => allHeaded_mem_root inRoots)
                (atomAt_inst_ne_bvar (firstOrder rule (listed rule member)).1
                  (headed rule (listed rule member)) assignment depth) ?_⟩
              refine mem_admittedAnswers.mpr ⟨?_, ?_⟩
              · rw [contract_atomAt]
                exact admitsAtoms _ _
              · rw [contract_ruleSpace, contract_atomAt]
                exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (allHeaded_mem_plain (by simp))
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (allHeaded_mem_plain (by simp))
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (allHeaded_mem_plain (by simp))
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (allHeaded_mem_plain (by simp))
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (allHeaded_mem_plain (by simp))
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (allHeaded_mem_plain (by simp))
            (atomAt depth domain) none inner⟩

/-- **Outside a run the presentation computes, on the atom of a term, by beta
and by the rules that the ambient space stores**, for a list of rules none of
whose left sides is a variable. -/
theorem allHeaded_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) allHeaded (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    refine allHeaded_atom_stepAt_sound (fun found => ?_) fuel step
    have inSpace := (mem_admittedAnswers.mp found).2
    rw [contract_ruleSpace, contract_atomAt] at inSpace
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound inSpace
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment ((rulesIff rule).mpr inRules))⟩
  · rintro ⟨next, rfl, step⟩
    exact allHeaded_atom_stepAt_complete admitsAtoms firstOrder bound headed
      (fun rule member => (rulesIff rule).mp member) undefined step depth

/-- **The run of the atom of a term computes by the rules of its space, at
every ambient space**, for a list of rules none of whose left sides is a
variable: its steps are the runs of the atoms of the steps of the term by
those rules. -/
theorem allHeaded_runAtom_step_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) allHeaded
        (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  rw [allHeaded_run_step_iff]
  constructor
  · rintro ⟨reached, rfl, step⟩
    obtain ⟨next, rfl, sourceStep⟩ :=
      (allHeaded_atom_step_iff admitsAtoms firstOrder bound headed rulesIff undefined).mp step
    exact ⟨next, rfl, sourceStep⟩
  · rintro ⟨next, rfl, step⟩
    exact ⟨_, rfl, (allHeaded_atom_step_iff admitsAtoms firstOrder bound headed rulesIff
      undefined).mpr ⟨next, rfl, step⟩⟩

variable {declared : Contexts.Interface → Prop}

/-- **On terms: at the space of a table of first-order rules with bound right
sides none of whose left sides is a variable, the presentation is a host of
the theories given by that table.** -/
theorem allHeaded_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (allHeadedTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨termsMapIn theory _ allHeaded_carriesAtoms,
    termsMapIn_hosting allHeaded_carriesAtoms allHeaded_quoteDropOnly
      allHeaded_quoteDropSorted allHeaded_namesOnlyDropped
      (allHeaded_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With contexts: a reading of the presentation, at the space of such a
table, in which the holes of atoms are free is a host, with all contexts, of
the theories given by the table** on the terms with free variables below a
width, for every width. -/
theorem allHeaded_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) (free : AtomsFree declared) :
    HostOf ((allHeadedTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMapIn theory _ allHeaded_carriesAtoms free width,
    scopedMapIn_hosting allHeaded_carriesAtoms allHeaded_quoteDropOnly
      allHeaded_quoteDropSorted allHeaded_namesOnlyDropped
      (allHeaded_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

/-! ## Instances, and what is paid -/

/-- **Positive**: the run of `choose heads tails` in the space of the two
rules of choice steps, at every ambient space and without a guard. -/
theorem allHeaded_runCoin_steps (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) allHeaded
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin))
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "heads"))) :=
  (allHeaded_runAtom_step_iff anySubject_admitsAtoms ambientSpace choiceRules_admitted.1
    choiceRules_admitted.2 choiceRules_headed withChoice_rules (fun _ => rfl)).mpr
    ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- **Negative**: the run of `choose heads tails` in the empty space has no
step, at every ambient space and without a guard. -/
theorem allHeaded_runCoin_normal (ambientSpace target : Pattern) :
    ¬ Step (regionEvaluator anySubject ambientSpace) allHeaded
      (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (allHeaded_runAtom_step_iff anySubject_admitsAtoms
    ambientSpace (rules := []) noRules_admitted.1 noRules_admitted.2
    (fun _ member => absurd member List.not_mem_nil) (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **Positive, a run in a run**: the inner run steps by its own space,
whatever the outer space and the ambient space are. -/
theorem allHeaded_nested_inner_steps (ambientSpace outer : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) allHeaded
      (runPattern outer (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin)))
      (runPattern outer
        (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "heads")))) :=
  allHeaded_run_step_iff.mpr ⟨_, rfl, allHeaded_runCoin_steps outer⟩

/-- **Negative, a run in a run**: the inner run sees neither the outer space
nor the ambient space, whatever they store.  The run of `choose heads tails`
in the empty space, inside a run in any space, has no step at any ambient
space. -/
theorem allHeaded_nested_outer_unseen (ambientSpace outer target : Pattern) :
    ¬ Step (regionEvaluator anySubject ambientSpace) allHeaded
      (runPattern outer (runPattern (ruleSpace []) (atomAt 0 coin))) target := by
  intro step
  obtain ⟨next, -, inner⟩ := allHeaded_run_step_iff.mp step
  exact allHeaded_runCoin_normal outer next inner

/-- **A run in a run, in the two presentations with headed root steps.**  In
the space of the rule `x ⟶ u` the run of `choose heads tails` in the empty
space steps to `u` in `headedContained`, and has no step here: the outer
space is asked for no run. -/
theorem headed_nested_presentations_differ (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) headedContained
        (runPattern (ruleSpace [takeAll]) (runPattern (ruleSpace []) (atomAt 0 coin)))
        (runPattern (ruleSpace [takeAll]) (atomAt 0 (.con "u"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject ambientSpace) allHeaded
          (runPattern (ruleSpace [takeAll]) (runPattern (ruleSpace []) (atomAt 0 coin)))
          target :=
  ⟨headed_nested_outer_rewrites ambientSpace, allHeaded_nested_outer_unseen ambientSpace _⟩

/-- **What is paid, against `headedContained`.**  In the space of the rule
`x ⟶ u` the run of a variable that a binder binds steps in `headedContained`
and has no step here: a rule whose left side is a variable does not fire on a
bound variable inside a run either. -/
theorem allHeaded_variableRule_not_preserved (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) headedContained
        (runPattern (ruleSpace [takeAll]) (atomAt 1 (.var 0)))
        (runPattern (ruleSpace [takeAll]) (atomAt 1 (.con "u"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject ambientSpace) allHeaded
          (runPattern (ruleSpace [takeAll]) (atomAt 1 (.var 0))) target := by
  refine ⟨(headed_runRoot_unheaded ambientSpace).1, fun target => ?_⟩
  rw [(headed_runRoot_unheaded ambientSpace).2.1]
  exact allHeaded_runVariable_normal ambientSpace _ 0 target

/-- **A weak evaluator, containment and static spaces together, under the
unchanged evaluator.**  Without a guard the evaluator answers the queries of
the eight root steps and of the eight root steps of a run by one function
that answers by stored rules; the steps of a run are the runs of the steps of
its subject in the member at its space, at every ambient space; and no space
and no name has a transition, at every stage and under every evaluator. -/
theorem allHeaded_weak_contained_static :
    (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "AmbientStep" [subject, .fvar "answer"]) =
          (admittedAnswers anySubject ambientSpace (applyBindings bindings subject)).map
            fun result => ("answer", result) :: bindings) ∧
      (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) =
          (admittedAnswers anySubject (applyBindings bindings (.fvar "space"))
            (applyBindings bindings subject)).map fun result => ("answer", result) :: bindings) ∧
      AuthoredEvaluators.AnswersByStoredRules (admittedAnswers anySubject) ∧
      (∀ ambientSpace space subject target : Pattern,
        Step (regionEvaluator anySubject ambientSpace) allHeaded (runPattern space subject)
            target ↔
          ∃ next, target = runPattern space next ∧
            Step (regionEvaluator anySubject space) allHeaded subject next) ∧
      (∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
          (term next : Contexts.Term allHeaded ⟨.base "Space", stage⟩),
        ¬ TermStep base allHeaded term next) ∧
      ∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
        (term next : Contexts.Term allHeaded ⟨.base "CandidateName", stage⟩),
        ¬ TermStep base allHeaded term next :=
  ⟨regionEvaluator_ambientQuery anySubject, regionEvaluator_runQuery anySubject,
    admittedAnswers_any_answersByStoredRules, fun _ _ _ _ => allHeaded_run_step_iff,
    fun _ _ term next => allHeaded_space_static term next,
    fun _ _ term next => allHeaded_name_static term next⟩

#print axioms allHeaded_atom_stepAt_sound
#print axioms allHeaded_atom_stepAt_complete
#print axioms allHeaded_atom_step_iff
#print axioms allHeaded_runAtom_step_iff
#print axioms allHeaded_hostOf_tabularAt
#print axioms allHeaded_hostOf_scopedTabularAt
#print axioms allHeaded_runCoin_steps
#print axioms allHeaded_runCoin_normal
#print axioms allHeaded_nested_inner_steps
#print axioms allHeaded_nested_outer_unseen
#print axioms headed_nested_presentations_differ
#print axioms allHeaded_variableRule_not_preserved
#print axioms allHeaded_weak_contained_static

end Mettapedia.Logic.HostingStyles.AmbientRegions
