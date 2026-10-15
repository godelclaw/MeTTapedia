import Mettapedia.Logic.HostingStyles.AmbientRegions.TwoSpaces

/-!
# A run in a run: what the inner run sees of the outer space

In both presentations the answer is: **nothing**.  No rewrite hands the space
of a run to a run inside its subject.  The two presentations differ by what
else the inner run sees.

* **Contained** (`contained_nested_step_iff`, `contained_nestedAtom_step_iff`):
  the steps of `run(outer, run(inner, subject))` are the runs of the steps of
  `subject` in the member at `inner`.  The inner run sees its own space, and
  neither the outer space nor the ambient space.
  Positive `contained_nested_inner_steps`, negative
  `contained_nested_outer_unseen`.
* **Scoped** (`scoped_nested_step_iff`, `scoped_nestedAtom_step_iff`): the
  steps of `run(outer, run(inner, subject))` are the runs of the steps of
  `subject` in the scoped member at the ambient space and in the ambient
  presentation at `inner`.  The inner run sees its own space and the ambient
  space, and not the space of the run around it.
  Positive `scoped_nested_ambient_seen`, negative `scoped_nested_outer_unseen`.

So the scoped run is no lexical scope: an inner run is scoped to the ambient
space, not to the runs around it.  A rewrite that would hand the outer space
down is stated in the header of `Summary`; it is in neither presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti
  (Theory patternVars usesOnly withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

variable {admits : Pattern → Bool}

/-! ## Contained -/

/-- **A run in a run, contained**: its steps are the runs of the steps of the
inner subject in the member at the inner space.  The outer space and the
ambient space are not in the statement. -/
theorem contained_nested_step_iff {ambientSpace outer inner subject target : Pattern}
    (silent : RunSilent admits ambientSpace) (outerSilent : RunSilent admits outer)
    (side : tokens runLabel subject = 0 ∨ RunSilent admits inner) :
    Step (regionEvaluator admits ambientSpace) containedRun
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        Step (regionEvaluator admits inner) containedRun subject next := by
  rw [contained_run_step_iff silent (.inr outerSilent)]
  constructor
  · rintro ⟨middle, rfl, step⟩
    obtain ⟨next, rfl, innerStep⟩ := (contained_run_step_iff outerSilent side).mp step
    exact ⟨next, rfl, innerStep⟩
  · rintro ⟨next, rfl, innerStep⟩
    exact ⟨runPattern inner next, rfl,
      (contained_run_step_iff outerSilent side).mpr ⟨next, rfl, innerStep⟩⟩

/-- **For the atom of a term in the space of a list of rules, inside another
run**: the steps are those of the term by the rules of the inner space. -/
theorem contained_nestedAtom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {ambientSpace outer : Pattern} (silent : RunSilent admits ambientSpace)
    (outerSilent : RunSilent admits outer) {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) containedRun
        (runPattern outer (runPattern (ruleSpace rules) (atomAt depth source))) target ↔
      ∃ next, target = runPattern outer (runPattern (ruleSpace rules) (atomAt depth next)) ∧
        Dedukti.Step theory source next := by
  rw [contained_nested_step_iff silent outerSilent (.inl (tokens_run_atomAt source depth))]
  constructor
  · rintro ⟨reached, rfl, step⟩
    obtain ⟨next, rfl, sourceStep⟩ :=
      (contained_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mp step
    exact ⟨next, rfl, sourceStep⟩
  · rintro ⟨next, rfl, sourceStep⟩
    exact ⟨atomAt depth next, rfl,
      (contained_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mpr
        ⟨next, rfl, sourceStep⟩⟩

/-- **Positive, contained**: the inner run steps by its own space.  The run
of `choose heads tails` in the space of the two rules of choice, inside a run
in the empty space, at the empty ambient space. -/
theorem contained_nested_inner_steps (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [])) containedRun
      (runPattern (ruleSpace []) (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin)))
      (runPattern (ruleSpace [])
        (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "heads")))) :=
  (contained_nestedAtom_step_iff admitsAtoms (runSilent_emptySpace admits)
    (runSilent_emptySpace admits) choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules
    (fun _ => rfl)).mpr ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- **Negative, contained**: the inner run sees neither the outer space nor
the ambient space.  The run of `choose heads tails` in the empty space, inside
a run in the space of the two rules of choice, has no step at the ambient
space of the two rules of choice. -/
theorem contained_nested_outer_unseen (admitsAtoms : AdmitsAtoms admits) (target : Pattern) :
    ¬ Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (runPattern (ruleSpace []) (atomAt 0 coin)))
      target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (contained_nestedAtom_step_iff admitsAtoms
    (choiceSpace_runSilent admits) (choiceSpace_runSilent admits) (rules := [])
    noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-! ## Scoped -/

/-- **In the ambient presentation a run has no step at a space that answers
nothing for a run**: no rewrite of that presentation is about a run. -/
theorem ambient_run_normal {space : Pattern} (silent : RunSilent admits space)
    (inner subject target : Pattern) :
    ¬ Step (regionEvaluator admits space) ambient (runPattern inner subject) target := by
  rintro ⟨fuel, step⟩
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
        rw [silent inner subject] at found
        cases found

/-- **A run in a run, scoped**: its steps are the runs of the steps of the
inner subject in the scoped member at the ambient space, and in the ambient
presentation at the inner space.  The outer space is not in the statement. -/
theorem scoped_nested_step_iff {ambientSpace outer inner subject target : Pattern}
    (silent : RunSilent admits ambientSpace) (outerSilent : RunSilent admits outer) :
    Step (regionEvaluator admits ambientSpace) scopedRun
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        (Step (regionEvaluator admits ambientSpace) scopedRun subject next ∨
          Step (regionEvaluator admits inner) ambient subject next) := by
  rw [scoped_run_step_iff silent]
  constructor
  · rintro ⟨middle, rfl, viaAmbient | viaOuter⟩
    · obtain ⟨next, rfl, either⟩ := (scoped_run_step_iff silent).mp viaAmbient
      exact ⟨next, rfl, either⟩
    · exact absurd viaOuter (ambient_run_normal outerSilent inner subject middle)
  · rintro ⟨next, rfl, either⟩
    exact ⟨runPattern inner next, rfl, .inl ((scoped_run_step_iff silent).mpr ⟨next, rfl, either⟩)⟩

/-- **For the atom of a term in the space of a list of rules, inside another
run, at the ambient space of another list**: the steps are those of the term
by the rules of the inner space and of the ambient space. -/
theorem scoped_nestedAtom_step_iff (admitsAtoms : AdmitsAtoms admits) {outer : Pattern}
    (outerSilent : RunSilent admits outer) {innerRules ambientRules : List Dedukti.RewriteRule}
    (silent : RunSilent admits (ruleSpace ambientRules))
    (firstOrder : ∀ rule ∈ innerRules ++ ambientRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ innerRules ++ ambientRules,
      usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ innerRules ++ ambientRules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace ambientRules)) scopedRun
        (runPattern outer (runPattern (ruleSpace innerRules) (atomAt depth source))) target ↔
      ∃ next, target = runPattern outer (runPattern (ruleSpace innerRules) (atomAt depth next)) ∧
        Dedukti.Step theory source next := by
  rw [scoped_run_step_iff silent]
  constructor
  · rintro ⟨middle, rfl, viaAmbient | viaOuter⟩
    · obtain ⟨next, rfl, sourceStep⟩ := (scoped_runAtom_step_iff admitsAtoms silent firstOrder
        bound rulesIff undefined).mp viaAmbient
      exact ⟨next, rfl, sourceStep⟩
    · exact absurd viaOuter (ambient_run_normal outerSilent _ _ middle)
  · rintro ⟨next, rfl, sourceStep⟩
    exact ⟨_, rfl, .inl ((scoped_runAtom_step_iff admitsAtoms silent firstOrder bound rulesIff
      undefined).mpr ⟨next, rfl, sourceStep⟩)⟩

/-- **Positive, scoped**: the inner run sees the ambient space.  The run of
`choose heads tails` in the empty space, inside a run in the empty space,
steps at the ambient space of the two rules of choice. -/
theorem scoped_nested_ambient_seen (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
      (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 coin)))
      (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 (.con "heads")))) :=
  (scoped_nestedAtom_step_iff admitsAtoms (runSilent_emptySpace admits) (innerRules := [])
    (choiceSpace_runSilent admits) choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules
    (fun _ => rfl)).mpr ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- **Negative, scoped**: the inner run does not see the space of the run
around it.  The run of `choose heads tails` in the empty space, inside a run
in the space of the two rules of choice, has no step at the empty ambient
space. -/
theorem scoped_nested_outer_unseen (admitsAtoms : AdmitsAtoms admits) (target : Pattern) :
    ¬ Step (regionEvaluator admits (ruleSpace [])) scopedRun
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (runPattern (ruleSpace []) (atomAt 0 coin)))
      target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (scoped_nestedAtom_step_iff admitsAtoms
    (choiceSpace_runSilent admits) (innerRules := []) (ambientRules := [])
    (runSilent_emptySpace admits) noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **The same nested run, in the two presentations, at one ambient space.**
At the ambient space of the two rules of choice the run of `choose heads
tails` in the empty space inside a run in the empty space steps in the scoped
presentation and has no step in the contained one. -/
theorem nested_presentations_differ (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
        (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 coin)))
        (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 (.con "heads")))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
          (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 coin))) target := by
  refine ⟨scoped_nested_ambient_seen admitsAtoms, fun target step => ?_⟩
  obtain ⟨next, -, sourceStep⟩ := (contained_nestedAtom_step_iff admitsAtoms
    (choiceSpace_runSilent admits) (runSilent_emptySpace admits) (rules := [])
    noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

#print axioms contained_nested_step_iff
#print axioms contained_nestedAtom_step_iff
#print axioms contained_nested_inner_steps
#print axioms contained_nested_outer_unseen
#print axioms ambient_run_normal
#print axioms scoped_nested_step_iff
#print axioms scoped_nestedAtom_step_iff
#print axioms scoped_nested_ambient_seen
#print axioms scoped_nested_outer_unseen
#print axioms nested_presentations_differ

end Mettapedia.Logic.HostingStyles.AmbientRegions
