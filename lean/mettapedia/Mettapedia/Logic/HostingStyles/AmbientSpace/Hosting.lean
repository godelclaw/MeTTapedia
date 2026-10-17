import Mettapedia.Logic.HostingStyles.AmbientSpace.Steps

/-!
# On terms: a theory given by a table is hosted by the member at the space of its table

* **Hosting** (`memberMap_hosting`).  For a table of rules without binder
  whose right sides mention only variables of their left sides, every theory
  given by the table is hosted, on all its terms, by the member of the family
  at the space of the table.  A term is read as its **plain atom**: no run,
  and no space in the term.  No two terms get one image, a step (beta, or a
  rule of the table, at any position) is a step of the image, and a step of
  the image is the image of a step.  One step is one step
  (`memberMap_steps`).
* Every theory of the class that the candidate with a run hosts is hosted by
  a member (`firstOrderTabular_hostedBy_member`).  The member depends on the
  table: the class is hosted by the family, one member for each table.
* **A positive and a negative member.**  At the space of the two rules of
  choice the atom of `choose heads tails` has two transitions whose results
  are apart (`choiceMember_two_reducts`).  At the empty space the member is
  the pure calculus (`emptyMember_hosts_pure`) and that atom has no
  transition (`emptyMember_choice_normal`).
* Beta is a rewrite of the presentation: a beta step is a step of every
  member (`ambient_pure_stepAt_complete`), so no member has a rank
  (`ambientMember_not_rank`).
* What the reading does not reach, with witnesses: a rule whose right side
  binds (`ambient_bindingRule_not_preserved`), and a rule whose right side has
  a variable that its left side does not bind
  (`ambient_freeRule_not_preserved`).  Both are as for the candidate with a
  run: they are about the evaluator, which is the same.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory inst patternVars usesOnly constantFunctionRule choiceTable
    withChoice withChoice_empty_tabular chooseLeft chooseRight choose omega omega_step
    normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce

/-! ## Beta, under every evaluator -/

/-- **Every beta step of a term is a step of the presentation between the
atoms**, at every depth and under every evaluator of its premises. -/
theorem ambient_pure_stepAt_complete {base : BasePremiseEvaluator} {source next : LF.Term}
    (step : Dedukti.Step Theory.empty source next) :
    ∀ depth : Nat, ∃ fuel, StepAt base ambient fuel (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument => exact ⟨1, ambient_beta_stepAt depth domain body argument⟩
          | delta defined => cases defined
          | rule assignment member => exact member.elim
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [ambient_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [ambient_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩

/-- `(λ x. x x) (λ x. x x)`, as an atom, has a transition to itself in every
member, and under every evaluator. -/
theorem ambient_omega_cycle (base : BasePremiseEvaluator) :
    TermStep base ambient (atomTerm 0 omega) (atomTerm 0 omega) := by
  obtain ⟨fuel, fired⟩ := ambient_pure_stepAt_complete (base := base) (omega_step Theory.empty) 0
  exact ⟨atomTerm 0 omega, atomTerm 0 omega, Relation.EqvGen.refl _, ⟨fuel, fired⟩,
    Relation.EqvGen.refl _⟩

/-- **No member of the family has a rank.** -/
theorem ambientMember_not_rank (space : SpaceTerm) : IsEmpty (ambientTheory space).Rank :=
  ⟨fun ranked => ranked.not_cycle (.single (ambient_omega_cycle (ambientEvaluator space.1)))⟩

/-! ## The hosting map -/

/-- **A theory, in the member at the space of a list of rules**: a term is
read as its plain atom. -/
def listMap (theory : Theory) (rules : List Dedukti.RewriteRule) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone (ambientTheory (listSpace rules)) :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := ambientTheory (listSpace rules)) AtomsReduce.closedAtom
    (fun term => atomTerm 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **The member at the space of a list of first-order rules with bound right
sides hosts, on terms, every theory whose rules are those of the list and
which has no definition.** -/
theorem listMap_hosting {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) : (listMap theory rules).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := ambientTheory (listSpace rules)) AtomsReduce.closedAtom
    (fun term => atomTerm 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : atomTerm 0 second = atomTerm 0 first :=
      eq_atomTerm_of_related (base := ambientEvaluator (ruleSpace rules)) (depth := 0) related
    exact (atomTerm_injective 0 same).symm
  · intro first next step
    exact (termStep_atomTerm_iff firstOrder bound rulesIff undefined (depth := 0)).mpr
      ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTerm_iff firstOrder bound rulesIff undefined (depth := 0)).mp step
    exact ⟨nextTerm, sourceStep, Relation.EqvGen.refl _⟩

/-- **A theory given by a table, in the member at the space of the table.** -/
noncomputable def memberMap (theory : Theory) (table : RuleTable) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone (ambientTheory (tableSpace table)) :=
  listMap theory table.toList

/-- **The member at the space of a table of first-order rules with bound
right sides hosts, on terms, every theory given by the table**: no two terms
get one image, a step of the theory (beta, or a rule of the table, at any
position) is a step of the image, and a step of the image is the image of a
step. -/
theorem memberMap_hosting {theory : Theory} {table : RuleTable} (tabular : theory.Tabular table)
    (admitted : BoundFirstOrder table) : (memberMap theory table).Hosting :=
  listMap_hosting admitted.listed.1 admitted.listed.2
    (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined

/-- **One step of the theory is one step of the member**: a reduction of
`count` steps is a reduction of `count` steps between the atoms. -/
theorem memberMap_steps {theory : Theory} {table : RuleTable} (tabular : theory.Tabular table)
    (admitted : BoundFirstOrder table) {count : Nat} {first final : LF.Term}
    (steps : ((rewritingTheory theory).gslt ()).termsAlone.Steps (interface := PUnit.unit) count
      first final) :
    (ambientTheory (tableSpace table)).Steps count (atomTerm 0 first) (atomTerm 0 final) :=
  (memberMap theory table).steps_of_preserves (memberMap_hosting tabular admitted).preserves steps

/-- **The member at the space of a table is a host, on terms, of the theories
given by that table.** -/
theorem member_hostOf_tabularAt {table : RuleTable} (admitted : BoundFirstOrder table) :
    HostOf (ambientTheory (tableSpace table))
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨memberMap theory table, memberMap_hosting tabular admitted⟩

/-- **The sentence for the member, with its evaluator named.** -/
theorem ambientMember_hosts_tabularAt {table : RuleTable} (admitted : BoundFirstOrder table) :
    (ambientMember (tableSpace table)).Hosts
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting :=
  member_hostOf_tabularAt admitted

/-- **Every theory given by a table of first-order rules with bound right
sides is hosted, on all its terms, by a member of the family**: the member at
the space of its table. -/
theorem firstOrderTabular_hostedBy_member {source : ContextTheory.{0}}
    (member : FirstOrderTabular source) :
    ∃ table : RuleTable, BoundFirstOrder table ∧
      ∀ interface : source.Interface,
        HostedBy (source.gslt interface).termsAlone (ambientTheory (tableSpace table)) := by
  obtain ⟨theory, table, tabular, admitted, rfl⟩ := member
  exact ⟨table, admitted, fun _ => ⟨memberMap theory table, memberMap_hosting tabular admitted⟩⟩

/-! ## A positive and a negative member -/

/-- The two rules of choice are first-order with bound right sides. -/
theorem choiceRules_admitted :
    (∀ rule ∈ [chooseLeft, chooseRight],
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ [chooseLeft, chooseRight], usesOnly (patternVars rule.lhs) 0 rule.rhs = true := by
  decide

/-- The rules of the calculus with choice are the two rules of choice. -/
theorem withChoice_rules (rule : Dedukti.RewriteRule) :
    (withChoice Theory.empty).rule rule ↔ rule ∈ [chooseLeft, chooseRight] := by
  simp [withChoice, Theory.empty]

/-- The space of the two rules of choice. -/
def choiceSpace : SpaceTerm := listSpace [chooseLeft, chooseRight]

/-- `choose heads tails`. -/
def coin : LF.Term := choose (.con "heads") (.con "tails")

/-- **Positive member: at the space of the two rules of choice, the atom of
`choose heads tails` has a transition to the atom of each of the two, and the
two results are apart.** -/
theorem choiceMember_two_reducts :
    (ambientTheory choiceSpace).rewrites (atomTerm 0 coin) (atomTerm 0 (.con "heads")) ∧
      (ambientTheory choiceSpace).rewrites (atomTerm 0 coin) (atomTerm 0 (.con "tails")) ∧
        ¬ ((ambientTheory choiceSpace).equations AtomsReduce.closedAtom).r
          (atomTerm 0 (.con "heads")) (atomTerm 0 (.con "tails")) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (termStep_atomTerm_iff choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules
      (fun _ => rfl) (depth := 0)).mpr ⟨_, Dedukti.step_choose_left Theory.empty _ _, rfl⟩
  · exact (termStep_atomTerm_iff choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules
      (fun _ => rfl) (depth := 0)).mpr ⟨_, Dedukti.step_choose_right Theory.empty _ _, rfl⟩
  · intro related
    have same := eq_atomTerm_of_related related
    exact absurd (atomTerm_injective 0 same) (by decide)

/-- No rule: the conditions on a list of rules hold of the empty list. -/
theorem noRules_admitted :
    (∀ rule ∈ ([] : List Dedukti.RewriteRule),
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ ([] : List Dedukti.RewriteRule), usesOnly (patternVars rule.lhs) 0 rule.rhs = true :=
  ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **Negative member: at the empty space the member is the pure calculus.**
It hosts the pure λΠ-calculus on all its terms, by beta alone. -/
theorem emptyMember_hosts_pure :
    HostedBy ((rewritingTheory Theory.empty).gslt ()).termsAlone (ambientTheory emptySpaceTerm) :=
  ⟨listMap Theory.empty [], listMap_hosting noRules_admitted.1 noRules_admitted.2
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)⟩

/-- The cover of the pure calculus: no definition and no rule. -/
def pureCover : Theory.empty.Cover where
  rigid := fun _ => true
  rules := []
  rigid_sound := fun _ _ => rfl
  rules_sound := fun _ member => member.elim

/-- **At the empty space the atom of `choose heads tails` has no
transition**: the member at a space computes by the rules that the space
stores, and the empty space stores none. -/
theorem emptyMember_choice_normal (target : Contexts.Term ambient AtomsReduce.closedAtom) :
    ¬ (ambientTheory emptySpaceTerm).rewrites (atomTerm 0 coin) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ :=
    (termStep_atomTerm_iff (rules := []) noRules_admitted.1 noRules_admitted.2
      (theory := Theory.empty)
      (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
      (fun _ => rfl) (depth := 0)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-! ## What the reading does not reach -/

/-- **The atom of `k c` has no transition at the space of the rule
`k x ⟶ λ y : Type. x`**: the evaluator answers nothing for an equation whose
right side binds, and `k c` has no beta step. -/
theorem ambient_bindingRule_normal (target : Contexts.Term ambient AtomsReduce.closedAtom) :
    ¬ (ambientTheory (listSpace [constantFunctionRule])).rewrites
      (atomTerm 0 (.app (.con "k") (.con "c"))) target := by
  rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, -⟩
  obtain rfl := eq_atomTerm_of_related before
  obtain ⟨next, -, step⟩ := ambient_stepAt_sound_of (theory := Theory.empty)
    (space := ruleSpace [constantFunctionRule])
    (fun found => by
      rw [contract_ruleSpace, matchResults_constantFunctionRule] at found
      cases found) fuel fired
  exact normal_of_normalTest pureCover _ (by decide) _ step

/-- **A rule whose right side binds is not hosted by this reading**: the
theory contracts `k c`, and the atom of `k c` has no transition in the member
at the space of the rule. -/
theorem ambient_bindingRule_not_preserved :
    Dedukti.Step (Theory.ofTable {constantFunctionRule}) (.app (.con "k") (.con "c"))
        (.lam (.srt .type) (.con "c")) ∧
      ∀ target : Contexts.Term ambient AtomsReduce.closedAtom,
        ¬ (ambientTheory (listSpace [constantFunctionRule])).rewrites
          (atomTerm 0 (.app (.con "k") (.con "c"))) target :=
  ⟨bindingRule_step, ambient_bindingRule_normal⟩

/-- An application of a constructor other than the symbol matches no atom of
a constant. -/
theorem constantAtom_not_matched {label : String} (other : label ≠ "prime-symbol")
    {parameters : List Pattern} {depth : Nat} {name : String} {bindings : Bindings} :
    bindings ∉ matchPattern (.apply label parameters) (atomAt depth (.con name)) := by
  intro matched
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  simp only [atomAt, symbolAtom, Pattern.apply.injEq] at shape
  exact other shape.1.symm

/-- **The atom of the constant `c` steps by an answer of the space alone**:
it has no beta step and no part. -/
theorem constant_stepAt_inv {space : Pattern} {fuel : Nat} {target : Pattern}
    (step : StepAt (ambientEvaluator space) ambient fuel (atomAt 0 (.con "c")) target) :
    target ∈ matchResults (contract space) (atomAt 0 (.con "c")) := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd matched (constantAtom_not_matched (label := "App") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "App") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "App") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "Pi") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "Pi") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "Lam") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "Lam") (by decide))
      · exact absurd matched (constantAtom_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨answer, found, applied⟩ := root_inv matched premises
        rw [contract_atomAt] at found
        rw [applied]
        exact found

/-- **The atom of `c` has at most one result at the space of the rule
`c ⟶ x`**: two transitions to atoms of terms are transitions to one atom. -/
theorem ambient_freeRule_unique {first second : LF.Term}
    (firstStep : (ambientTheory (listSpace [freeRule])).rewrites (atomTerm 0 (.con "c"))
      (atomTerm 0 first))
    (secondStep : (ambientTheory (listSpace [freeRule])).rewrites (atomTerm 0 (.con "c"))
      (atomTerm 0 second)) : first = second := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := firstStep
  obtain ⟨otherRedex, otherContractum, otherBefore, ⟨otherFuel, otherFired⟩, otherAfter⟩ :=
    secondStep
  obtain rfl := eq_atomTerm_of_related before
  obtain rfl := eq_atomTerm_of_related otherBefore
  obtain rfl := eq_atomTerm_of_related
    ((termSetoid (ambientEvaluator (ruleSpace [freeRule])) ambient (atomInterface 0)).iseqv.symm
      after)
  obtain rfl := eq_atomTerm_of_related
    ((termSetoid (ambientEvaluator (ruleSpace [freeRule])) ambient (atomInterface 0)).iseqv.symm
      otherAfter)
  have found := constant_stepAt_inv fired
  have otherFound := constant_stepAt_inv otherFired
  have short : (matchResults (contract (ruleSpace [freeRule])) (atomAt 0 (.con "c"))).length ≤ 1 := by
    refine (matchResults_length_le _ _).trans ?_
    rw [contract_ruleSpace, ruleSpace, storedAtoms_spaceOfAtoms]
    simp
  exact atomAt_injective 0 (eq_of_mem_of_length_le_one short found otherFound)

/-- **A rule whose right side has a variable that its left side does not bind
is not hosted by this reading**: `c` steps to the sort of types and to the
sort of kinds, and its atom does not step to the atoms of both. -/
theorem ambient_freeRule_not_preserved :
    Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .type) ∧
      Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .kind) ∧
        ¬ ((ambientTheory (listSpace [freeRule])).rewrites (atomTerm 0 (.con "c"))
              (atomTerm 0 (.srt .type)) ∧
            (ambientTheory (listSpace [freeRule])).rewrites (atomTerm 0 (.con "c"))
              (atomTerm 0 (.srt .kind))) :=
  ⟨freeRule_step _, freeRule_step _, fun both =>
    absurd (ambient_freeRule_unique both.1 both.2) (by decide)⟩

#print axioms ambient_pure_stepAt_complete
#print axioms ambient_omega_cycle
#print axioms ambientMember_not_rank
#print axioms listMap_hosting
#print axioms memberMap_hosting
#print axioms memberMap_steps
#print axioms member_hostOf_tabularAt
#print axioms ambientMember_hosts_tabularAt
#print axioms firstOrderTabular_hostedBy_member
#print axioms choiceMember_two_reducts
#print axioms emptyMember_hosts_pure
#print axioms emptyMember_choice_normal
#print axioms ambient_bindingRule_normal
#print axioms ambient_bindingRule_not_preserved
#print axioms constant_stepAt_inv
#print axioms ambient_freeRule_unique
#print axioms ambient_freeRule_not_preserved

end Mettapedia.Logic.HostingStyles.AmbientSpace
