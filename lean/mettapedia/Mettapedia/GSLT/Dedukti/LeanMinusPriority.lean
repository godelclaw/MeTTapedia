import Mettapedia.GSLT.Dedukti.LeanMinusLevels

/-!
# The two rules on `v` tried in order: the delimited strategy

The paper says that its two rules on `v`, `v (inst l) _ ↪ l` and
`v _ i ↪ B(i)`, "must be tried in the given order".  This module defines that
reading as a relation on terms and states what it does and does not give.

## The ordered relation

`OrderedRoot signature rules` contracts the root by beta, by the unfolding of
a definition, or by the **first** rule of the list whose left side has an
instance equal to the term.  `OrderedStep` closes it under one-hole contexts.
On the paper's rules (`leanSig`, `leanRules`), it contains the two clauses of
the earlier audit (`ordered_inst_step`, `ordered_fallback_step`).

* **Not stable under substitution** (`ordered_not_substitution_stable`):
  `v x 0 ⟶ B(0)` by the fallback, and the instance `v (inst zero) 0 ⟶ B(0)`
  is not a step: the first rule takes precedence.
* **Its conversion relates every two terms** (`ordered_conv_collapses`):
  `(λx. v x 0) (inst t)` reduces to `t` by beta first, and to `B(0)` by the
  fallback under the binder first.

## Restricting the fallback

* **"Not on a bound variable" is not enough** (`notBound_conv_collapses`): if
  the fallback may fire on any first argument other than a bound variable, it
  fires on `(λy. y) (inst t)`, which beta turns into `inst t`.  It still fires
  on a free variable, so it is not stable under substitution either
  (`notBound_not_substitution_stable`).
* **The fallback on frozen parameters only.**  When the level parameters of
  the declaration being checked are frozen, written `frz n` instead of a
  variable, the fallback becomes the rule `v (frz n) i ↪ B(i)`, disjoint from
  `v (inst l) _ ↪ l`.  With `∧` given by its orthogonal rules, the result is
  an orthogonal theory (`frozenTheory_orthogonal`): confluent, and its steps
  and conversion are stable under every substitution (`Step.subst`,
  `Conv.subst`).  On an orthogonal list the order of the rules does not matter
  (`orderedStep_iff_of_orthogonal`), so on this fragment the ordered relation
  itself is confluent (`frozen_ordered_confluent`) and stable under
  substitution (`frozen_ordered_subst`).  This is the largest fragment found:
  instantiating a frozen parameter is not a substitution, and it breaks the
  step (`frozen_instantiation_breaks`).

## Agreement with the explicit substitution of `LeanMinusExplicit`

* **Refuted with the paper's rules** (`frozen_disagrees_with_explicit`): on the
  translations of the levels `max 1 α` and `α`, the frozen strategy converts
  and the explicit substitution does not.  The cause is defect D1 of
  `LeanMinusLevels`, not the strategy.  Defect D2 also survives the strategy:
  the translations of two equivalent levels stay apart
  (`frozen_add_incomplete`).
* **With the corrected rules**, the frozen strategy separates that pair too
  (`frozenCorrected_separates_max_one_var`) and joins the pair of D2
  (`frozenCorrected_joins_add_pair`), as the explicit substitution does.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## The ordered relation -/

/-- The number of binders above the hole of a context. -/
def contextDepth : Context → Nat
  | .hole => 0
  | .piDomain rest _ => contextDepth rest
  | .piBody _ rest => contextDepth rest + 1
  | .lamDomain rest _ => contextDepth rest
  | .lamBody _ rest => contextDepth rest + 1
  | .appFunction rest _ => contextDepth rest
  | .appArgument _ rest => contextDepth rest

/-- No rule of the list before position `index` has an instance equal to
`term`. -/
def NoEarlierMatch (rules : List RewriteRule) (index : Nat) (term : Term) : Prop :=
  ∀ earlier < index, ∀ other, rules[earlier]? = some other →
    ∀ assignment : Nat → Term, term ≠ inst assignment other.lhs

/-- **One contraction at the root, the rules tried in order**: beta, the
unfolding of a definition, or the first rule whose left side matches. -/
inductive OrderedRoot (signature : Sig) (rules : List RewriteRule) : Term → Term → Prop where
  | beta (domain body argument : Term) :
      OrderedRoot signature rules (.app (.lam domain body) argument) (subst0 argument body)
  | delta {name : String} {body : Term} :
      lookupBody signature name = some body → OrderedRoot signature rules (.con name) body
  | rule {index : Nat} {rule : RewriteRule} (assignment : Nat → Term) :
      rules[index]? = some rule → NoEarlierMatch rules index (inst assignment rule.lhs) →
        OrderedRoot signature rules (inst assignment rule.lhs) (inst assignment rule.rhs)

/-- A root relation that may depend on the number of binders above it, closed
under one-hole contexts. -/
inductive AtDepth (root : Nat → Term → Term → Prop) : Term → Term → Prop where
  | inContext (context : Context) {source target : Term} :
      root (contextDepth context) source target →
        AtDepth root (context.plug source) (context.plug target)

/-- **The ordered relation**: the first matching rule at the root, closed under
contexts, with beta. -/
abbrev OrderedStep (signature : Sig) (rules : List RewriteRule) : Term → Term → Prop :=
  AtDepth fun _ => OrderedRoot signature rules

/-- The equivalence generated by the ordered relation. -/
abbrev OrderedConv (signature : Sig) (rules : List RewriteRule) : Term → Term → Prop :=
  Relation.EqvGen (OrderedStep signature rules)

/-- A step of the ordered relation is a step of the theory of its rules. -/
theorem OrderedStep.step {signature : Sig} {rules : List RewriteRule} {source target : Term}
    (step : OrderedStep signature rules source target) :
    Step (Theory.ofSig signature rules) source target := by
  cases step with
  | inContext context root =>
      refine Step.inContext context ?_
      cases root with
      | beta domain body argument => exact .beta domain body argument
      | delta defined => exact .delta defined
      | rule assignment found _ =>
          exact .rule assignment (List.mem_of_getElem? found)

/-- **On an orthogonal list of rules the order does not matter**: the ordered
relation is the step relation of the theory, since two rules with a common
instance are one rule (`Theory.Orthogonal.rootUnique`). -/
theorem orderedStep_iff_of_orthogonal {signature : Sig} {rules : List RewriteRule}
    (orthogonal : (Theory.ofSig signature rules).Orthogonal) {source target : Term} :
    OrderedStep signature rules source target ↔ Step (Theory.ofSig signature rules) source target := by
  refine ⟨OrderedStep.step, fun step => ?_⟩
  cases step with
  | inContext context root =>
      refine AtDepth.inContext context ?_
      cases root with
      | beta domain body argument => exact .beta domain body argument
      | delta defined => exact .delta defined
      | @rule declared assignment member =>
          have found : ∃ index, rules[index]? = some declared := List.mem_iff_getElem?.mp member
          refine OrderedRoot.rule assignment (Nat.find_spec found) ?_
          intro earlier below other atEarlier otherAssignment same
          have equal : declared = other :=
            orthogonal.rootUnique declared other member (List.mem_of_getElem? atEarlier)
              assignment otherAssignment same
          subst equal
          exact Nat.find_min found below atEarlier

/-! ## The paper's rules, in order -/

theorem leanRules_inst_position : leanRules[50]? = some instRule := by decide

theorem leanRules_variable_position : leanRules[51]? = some variableRule := by decide

theorem leanRules_variable_unique :
    ∀ index, leanRules[index]? = some variableRule → index = 51 := by
  intro index found
  have bound : index < leanRules.length := (List.getElem?_eq_some_iff.mp found).1
  have length : leanRules.length = 55 := by decide
  rw [length] at bound
  revert found
  revert index
  decide

/-- The rules before position `50` are those of `ΣU` and `ΣP`. -/
theorem leanRules_before_poly {earlier : Nat} {other : RewriteRule} (below : earlier < 50)
    (found : leanRules[earlier]? = some other) : other ∈ pureRules := by
  have length : pureRules.length = 50 := by decide
  have inPure : pureRules[earlier]? = some other := by
    have same : leanRules[earlier]? = pureRules[earlier]? := by
      show (pureRules ++ rulesPoly ++ rulesLean)[earlier]? = pureRules[earlier]?
      rw [List.append_assoc, List.getElem?_append_left (by rw [length]; exact below)]
    rw [← same]
    exact found
  exact List.mem_of_getElem? inPure

/-- No rule of `ΣU` or `ΣP` has a left side headed by `v`. -/
theorem pureRules_clash_v : ∀ other ∈ pureRules,
    clashes instRule.lhs other.lhs = true ∧ clashes variableRule.lhs other.lhs = true := by
  decide +kernel

theorem noEarlierMatch_inst (level other : Term) :
    NoEarlierMatch leanRules 50 (inst (assign [level, other]) instRule.lhs) := by
  intro earlier below rule found assignment same
  exact ne_inst_of_clashes (pureRules_clash_v rule (leanRules_before_poly below found)).1
    (assign [level, other]) assignment same

/-- `v (inst l) x ⟶ l` at the root, by the first rule on `v`. -/
theorem ordered_inst_root (level other : Term) :
    OrderedRoot leanSig leanRules (ap "v" [instOf level, other]) level := by
  have root := OrderedRoot.rule (signature := leanSig) (assign [level, other])
    leanRules_inst_position (noEarlierMatch_inst level other)
  have source : inst (assign [level, other]) instRule.lhs = ap "v" [instOf level, other] := by
    rw [instRule_closed]; simp [assign, ap, apT, instOf]
  have target : inst (assign [level, other]) instRule.rhs = level := by
    rw [instRule_closed]; simp [assign]
  rw [source, target] at root
  exact root

/-- `v (inst l) x ⟶ l` is a step of the ordered relation. -/
theorem ordered_inst_step (level other : Term) :
    OrderedStep leanSig leanRules (ap "v" [instOf level, other]) level :=
  AtDepth.inContext .hole (ordered_inst_root level other)

/-- A term that is not `inst` applied to something is not an instance of the
first argument of the first rule on `v`. -/
theorem noEarlierMatch_variable {first index : Term} (notInst : ∀ level, first ≠ instOf level) :
    NoEarlierMatch leanRules 51 (inst (assign [first, index]) variableRule.lhs) := by
  intro earlier below rule found assignment same
  rcases Nat.lt_or_ge earlier 50 with before | atPoly
  · exact ne_inst_of_clashes (pureRules_clash_v rule (leanRules_before_poly before found)).2
      (assign [first, index]) assignment same
  · have isFifty : earlier = 50 := by omega
    subst isFifty
    rw [leanRules_inst_position] at found
    obtain rfl := Option.some.inj found
    rw [variableRule_closed, instRule_closed] at same
    simp only [inst_app, inst_con, inst_var, ap, apT, List.foldl, instOf, Term.app.injEq] at same
    exact notInst (assignment 0) (by simpa [assign, instOf, ap, apT] using same.1.2)

/-- `v w i ⟶ B(i)` at the root, when `w` is not of the form `inst l`. -/
theorem ordered_fallback_root {first index : Term} (notInst : ∀ level, first ≠ instOf level) :
    OrderedRoot leanSig leanRules (ap "v" [first, index]) (levelVariable index) := by
  have root := OrderedRoot.rule (signature := leanSig) (assign [first, index])
    leanRules_variable_position (noEarlierMatch_variable notInst)
  have source : inst (assign [first, index]) variableRule.lhs = ap "v" [first, index] := by
    rw [variableRule_closed]; simp [assign, ap, apT]
  have target : inst (assign [first, index]) variableRule.rhs = levelVariable index := by
    rw [variableRule_closed]; simp [assign, levelVariable, ap, apT, zeroN]
  rw [source, target] at root
  exact root

/-- `v w i ⟶ B(i)`, when `w` is not of the form `inst l`, is a step of the
ordered relation. -/
theorem ordered_fallback_step {first index : Term} (notInst : ∀ level, first ≠ instOf level) :
    OrderedStep leanSig leanRules (ap "v" [first, index]) (levelVariable index) :=
  AtDepth.inContext .hole (ordered_fallback_root notInst)

/-! ## Not stable under substitution -/

theorem AtDepth.app_inv {root : Nat → Term → Term → Prop} {function argument target : Term}
    (step : AtDepth root (.app function argument) target) :
    root 0 (.app function argument) target ∨
      (∃ function', AtDepth root function function' ∧ target = .app function' argument) ∨
      (∃ argument', AtDepth root argument argument' ∧ target = .app function argument') := by
  generalize same : Term.app function argument = source at step
  cases step with
  | inContext context rootStep =>
      cases context with
      | hole =>
          simp only [Context.plug] at same
          subst same
          exact Or.inl rootStep
      | appFunction rest other =>
          simp only [Context.plug, Term.app.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inl ⟨_, .inContext rest rootStep, rfl⟩)
      | appArgument other rest =>
          simp only [Context.plug, Term.app.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inr ⟨_, .inContext rest rootStep, rfl⟩)
      | piDomain rest other => simp [Context.plug] at same
      | piBody other rest => simp [Context.plug] at same
      | lamDomain rest other => simp [Context.plug] at same
      | lamBody other rest => simp [Context.plug] at same

/-- Every rule of the paper's list other than the two on `v` clashes with
`v (inst zero) 0`. -/
theorem leanRules_clash_instZero : ∀ rule ∈ leanRules,
    rule = instRule ∨ rule = variableRule ∨ clashes rule.lhs (ap "v" [instOf zero, zeroN]) = true := by
  decide +kernel

/-- What a root step of the ordered relation is. -/
theorem OrderedRoot.inv {signature : Sig} {rules : List RewriteRule} {source target : Term}
    (root : OrderedRoot signature rules source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = subst0 argument body) ∨
      (∃ name, source = .con name ∧ lookupBody signature name = some target) ∨
      ∃ index rule assignment, rules[index]? = some rule ∧
        NoEarlierMatch rules index (inst assignment rule.lhs) ∧
        source = inst assignment rule.lhs ∧ target = inst assignment rule.rhs := by
  cases root with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => exact Or.inr (Or.inl ⟨_, rfl, defined⟩)
  | rule assignment found noEarlier =>
      exact Or.inr (Or.inr ⟨_, _, assignment, found, noEarlier, rfl, rfl⟩)

/-- **After instantiation, the fallback step is not a step**: `v (inst zero) 0`
does not step to `B(0)`, since the first rule matches. -/
theorem ordered_not_after_instantiation :
    ¬ OrderedStep leanSig leanRules (ap "v" [instOf zero, zeroN]) (levelVariable zeroN) := by
  intro step
  rcases AtDepth.app_inv step with root | ⟨_, _, same⟩ | ⟨_, _, same⟩
  · rcases root.inv with ⟨_, _, _, source, _⟩ | ⟨_, source, _⟩ |
        ⟨index, rule, assignment, found, noEarlier, sourceEq, targetEq⟩
    · simp [ap, apT, instOf] at source
    · simp [ap, apT, instOf] at source
    · have member := List.mem_of_getElem? found
      rcases leanRules_clash_instZero rule member with rfl | rfl | clash
      · rw [instRule_closed] at sourceEq targetEq
        have isZero : assignment 0 = zero := by
          simp only [inst_app, inst_con, inst_var, ap, apT, List.foldl, instOf, Term.app.injEq,
            true_and] at sourceEq
          exact sourceEq.1.symm
        simp only [inst_var] at targetEq
        rw [isZero] at targetEq
        exact absurd targetEq (by decide)
      · have position := leanRules_variable_unique index found
        subst position
        exact noEarlier 50 (by omega) instRule leanRules_inst_position (assign [zero, zeroN])
          (by rw [← sourceEq, instRule_closed]; simp [assign, ap, apT, instOf])
      · exact ne_inst_of_clashes clash assignment (fun _ => zeroN) (by
          rw [← sourceEq]
          exact (Closed.inst (wellScoped_of_test _ 0 (by decide)) _).symm)
  · simp [levelVariable, ap, apT, zeroN] at same
  · simp [levelVariable, ap, apT, zeroN] at same

/-- **The ordered relation is not stable under substitution**: `v x 0 ⟶ B(0)`,
and its instance at `x := inst zero` is not a step. -/
theorem ordered_not_substitution_stable :
    OrderedStep leanSig leanRules (ap "v" [.var 0, zeroN]) (levelVariable zeroN) ∧
      ¬ OrderedStep leanSig leanRules (subst0 (instOf zero) (ap "v" [.var 0, zeroN]))
        (subst0 (instOf zero) (levelVariable zeroN)) := by
  refine ⟨ordered_fallback_step (fun level same => by cases same), ?_⟩
  have source : subst0 (instOf zero) (ap "v" [.var 0, zeroN]) = ap "v" [instOf zero, zeroN] := by
    decide
  have target : subst0 (instOf zero) (levelVariable zeroN) = levelVariable zeroN := by decide
  rw [source, target]
  exact ordered_not_after_instantiation

/-! ## The ordered conversion relates every two terms -/

/-- `(λx. v x 0) (inst t)`. -/
def betaWitness (term : Term) : Term := .app (.lam L (ap "v" [.var 0, zeroN])) (instOf term)

theorem ordered_beta_first (term : Term) :
    OrderedStep leanSig leanRules (betaWitness term) (ap "v" [instOf term, zeroN]) := by
  have root := OrderedRoot.beta (signature := leanSig) (rules := leanRules) L (ap "v" [.var 0, zeroN])
    (instOf term)
  have computed : subst0 (instOf term) (ap "v" [.var 0, zeroN]) = ap "v" [instOf term, zeroN] := by
    simp [ap, apT, subst0, subst, zeroN]
  rw [computed] at root
  exact AtDepth.inContext .hole root

theorem ordered_binder_first (term : Term) :
    OrderedStep leanSig leanRules (betaWitness term) (.app (.lam L (levelVariable zeroN)) (instOf term)) :=
  AtDepth.inContext (.appFunction (.lamBody L .hole) (instOf term))
    (ordered_fallback_root (first := .var 0) (index := zeroN) (fun level same => by cases same))

theorem ordered_then_beta (term : Term) :
    OrderedStep leanSig leanRules (.app (.lam L (levelVariable zeroN)) (instOf term))
      (levelVariable zeroN) := by
  have root := OrderedRoot.beta (signature := leanSig) (rules := leanRules) L (levelVariable zeroN)
    (instOf term)
  have computed : subst0 (instOf term) (levelVariable zeroN) = levelVariable zeroN := rfl
  rw [computed] at root
  exact AtDepth.inContext .hole root

/-- **The ordered conversion relates every two terms**: trying the first rule
on `v` first does not repair the conversion when beta and the fallback are
both available under binders. -/
theorem ordered_conv_collapses (left right : Term) : OrderedConv leanSig leanRules left right := by
  have through (term : Term) : OrderedConv leanSig leanRules term (levelVariable zeroN) :=
    .trans _ _ _
      (.symm _ _ (.trans _ _ _ (.rel _ _ (ordered_beta_first term))
        (.rel _ _ (ordered_inst_step term zeroN))))
      (.trans _ _ _ (.rel _ _ (ordered_binder_first term)) (.rel _ _ (ordered_then_beta term)))
  exact .trans _ _ _ (through left) (.symm _ _ (through right))

/-! ## "Not on a bound variable" is not enough -/

/-- The fallback restricted at depth `depth`: it fires only when the first
argument of `v` is not a variable bound in the surrounding term. -/
inductive NotBoundRoot (signature : Sig) (rules : List RewriteRule) (depth : Nat) :
    Term → Term → Prop where
  | ordered {source target : Term} :
      OrderedRoot signature rules source target →
        (∀ first index, source = ap "v" [first, index] → target = levelVariable index →
          ∀ bound, first = .var bound → depth ≤ bound) →
        NotBoundRoot signature rules depth source target

/-- The ordered relation with the fallback never on a bound variable. -/
abbrev NotBoundStep (signature : Sig) (rules : List RewriteRule) : Term → Term → Prop :=
  AtDepth (NotBoundRoot signature rules)

/-- `v ((λy. y) (inst t)) 0`. -/
def redexWitness (term : Term) : Term := ap "v" [.app (.lam L (.var 0)) (instOf term), zeroN]

theorem notBound_fallback (term : Term) :
    NotBoundStep leanSig leanRules (redexWitness term) (levelVariable zeroN) := by
  refine AtDepth.inContext .hole (NotBoundRoot.ordered
    (ordered_fallback_root (first := .app (.lam L (.var 0)) (instOf term)) (index := zeroN)
      (fun level same => by simp [instOf, ap, apT] at same)) ?_)
  intro first index sourceEq _ bound firstEq
  subst firstEq
  simp [ap, apT] at sourceEq

theorem notBound_beta (term : Term) :
    NotBoundStep leanSig leanRules (redexWitness term) (ap "v" [instOf term, zeroN]) := by
  have root : NotBoundRoot leanSig leanRules 0 (.app (.lam L (.var 0)) (instOf term)) (instOf term) := by
    refine NotBoundRoot.ordered ?_ ?_
    · have beta := OrderedRoot.beta (signature := leanSig) (rules := leanRules) L (.var 0) (instOf term)
      have computed : subst0 (instOf term) (Term.var 0) = instOf term := by
        simp [subst0, subst]
      rw [computed] at beta
      exact beta
    · intro first index sourceEq
      simp [ap, apT] at sourceEq
  exact AtDepth.inContext (.appFunction (.appArgument (.con "v") .hole) zeroN) root

theorem notBound_inst (term : Term) :
    NotBoundStep leanSig leanRules (ap "v" [instOf term, zeroN]) term := by
  refine AtDepth.inContext .hole (NotBoundRoot.ordered (ordered_inst_root term zeroN) ?_)
  intro first index sourceEq _ bound firstEq
  subst firstEq
  simp [instOf, ap, apT] at sourceEq

/-- **"Never on a bound variable" does not repair the conversion**: the
fallback fires on `(λy. y) (inst t)`, which is not a variable, and beta turns
that argument into `inst t`; so every two terms are related. -/
theorem notBound_conv_collapses (left right : Term) :
    Relation.EqvGen (NotBoundStep leanSig leanRules) left right := by
  have through (term : Term) :
      Relation.EqvGen (NotBoundStep leanSig leanRules) term (levelVariable zeroN) :=
    .trans _ _ _
      (.symm _ _ (.trans _ _ _ (.rel _ _ (notBound_beta term)) (.rel _ _ (notBound_inst term))))
      (.rel _ _ (notBound_fallback term))
  exact .trans _ _ _ (through left) (.symm _ _ (through right))

/-- A step of the restricted relation is a step of the ordered relation. -/
theorem NotBoundStep.ordered {signature : Sig} {rules : List RewriteRule} {source target : Term}
    (step : NotBoundStep signature rules source target) : OrderedStep signature rules source target := by
  cases step with
  | inContext context root =>
      cases root with
      | ordered root _ => exact AtDepth.inContext context root

/-- **"Not on a bound variable" is not stable under substitution either**: the
fallback fires on the free variable of `v x 0`, and not on its instance at
`x := inst zero`. -/
theorem notBound_not_substitution_stable :
    NotBoundStep leanSig leanRules (ap "v" [.var 0, zeroN]) (levelVariable zeroN) ∧
      ¬ NotBoundStep leanSig leanRules (subst0 (instOf zero) (ap "v" [.var 0, zeroN]))
        (subst0 (instOf zero) (levelVariable zeroN)) :=
  ⟨AtDepth.inContext .hole (NotBoundRoot.ordered
      (ordered_fallback_root (fun level same => by cases same))
      (fun _ _ _ _ _ _ => Nat.zero_le _)),
    fun step => ordered_not_substitution_stable.2 step.ordered⟩

/-! ## The fallback on frozen parameters -/

/-- A frozen level parameter: `frz n`. -/
def frzOf (index : Term) : Term := ap "frz" [index]

/-- The frozen parameter numbered `index`. -/
def frzVar (index : Nat) : Term := frzOf (numeral index)

def sigmaFrozen : Sig := [.const "frz" (arrow N L)]

/-- `v (frz n) i ↪ codeOf i`: the fallback, on frozen parameters only. -/
def frozenFallback (codeOf : Term → Term) : RewriteRule :=
  mkRule ["n", "i"] (ap "v" [frzOf (nv "n"), nv "i"]) (codeOf (nv "i"))

def frozenSig : Sig := leanSig ++ sigmaFrozen

/-- The paper's rules, the fallback on frozen parameters only, `∧` given by its
orthogonal rules. -/
def frozenRules : List RewriteRule :=
  paperLevelRules ++ [instRule, frozenFallback levelVariable] ++ rulesLean

/-- **The frozen-parameter strategy over the paper's rules**, as a theory. -/
def frozenTheory : Theory := Theory.ofSig frozenSig frozenRules

/-- The same rules with the two corrections of `LeanMinusLevels`: the fallback
returns the code with its guard, and `Add` is corrected. -/
def frozenRulesCorrected : List RewriteRule :=
  pureRulesExplicit ++ [instRule, frozenFallback varCode] ++ rulesLean

/-- The frozen-parameter strategy over the corrected rules. -/
def frozenTheoryCorrected : Theory := Theory.ofSig frozenSig frozenRulesCorrected

theorem frozenSig_closed : closedSigTest frozenSig = true := by
  decide +kernel

/-- **The frozen-parameter strategy is orthogonal**: the two rules on `v` no
longer overlap. -/
theorem frozenTheory_orthogonal : frozenTheory.Orthogonal :=
  orthogonal_of_check_closed frozenRules (fun _ member => member)
    (closedBodies_of_test frozenRules frozenSig_closed)
    (undefinedOnLeft_of_test (by decide +kernel)) (by decide +kernel)

theorem frozenTheoryCorrected_orthogonal : frozenTheoryCorrected.Orthogonal :=
  orthogonal_of_check_closed frozenRulesCorrected (fun _ member => member)
    (closedBodies_of_test frozenRulesCorrected frozenSig_closed)
    (undefinedOnLeft_of_test (by decide +kernel)) (by decide +kernel)

/-- **The frozen-parameter strategy is confluent.** -/
theorem frozenTheory_confluent : Confluent (Step frozenTheory) :=
  confluent_of_orthogonal frozenTheory_orthogonal

theorem frozenTheoryCorrected_confluent : Confluent (Step frozenTheoryCorrected) :=
  confluent_of_orthogonal frozenTheoryCorrected_orthogonal

/-- **Its conversion is stable under every substitution.** -/
theorem frozenTheory_conv_subst {source target : Term} (convertible : Conv frozenTheory source target)
    (index : Nat) (replacement : Term) :
    Conv frozenTheory (subst index replacement source) (subst index replacement target) :=
  convertible.subst frozenTheory_orthogonal.closedBodies index replacement

/-- **On the frozen fragment, the ordered relation is confluent**: tried in
order or not, the rules give the steps of `frozenTheory`. -/
theorem frozen_ordered_confluent : Confluent (OrderedStep frozenSig frozenRules) := by
  have same : OrderedStep frozenSig frozenRules = Step frozenTheory := by
    funext source target
    exact propext (orderedStep_iff_of_orthogonal (signature := frozenSig) (rules := frozenRules)
      frozenTheory_orthogonal)
  rw [same]
  exact frozenTheory_confluent

/-- **On the frozen fragment, the ordered relation is stable under every
substitution.** -/
theorem frozen_ordered_subst {source target : Term}
    (step : OrderedStep frozenSig frozenRules source target) (index : Nat) (replacement : Term) :
    OrderedStep frozenSig frozenRules (subst index replacement source)
      (subst index replacement target) :=
  (orderedStep_iff_of_orthogonal (signature := frozenSig) (rules := frozenRules)
      frozenTheory_orthogonal).2
    (((orderedStep_iff_of_orthogonal (signature := frozenSig) (rules := frozenRules)
      frozenTheory_orthogonal).1 step).subst frozenTheory_orthogonal.closedBodies index replacement)

theorem frozenRules_linear : ∀ rule ∈ frozenRules, (patternVars rule.lhs).Nodup :=
  fun rule member => frozenTheory_orthogonal.leftLinear rule member

theorem frozenRulesCorrected_linear : ∀ rule ∈ frozenRulesCorrected, (patternVars rule.lhs).Nodup :=
  fun rule member => frozenTheoryCorrected_orthogonal.leftLinear rule member

/-- `v (frz 0) 0 ⟶ B(0)`. -/
theorem frozen_fallback_step : Reduces frozenTheory (ap "v" [frzVar 0, zeroN]) (levelVariable zeroN) :=
  Reduces.of_evaluate frozenRules_linear (fuel := 2) (by decide +kernel)

/-- **Instantiating a frozen parameter breaks the step**: `v (frz 0) 0 ⟶ B(0)`,
while `v (inst zero) 0` and `B(0)` are not even convertible.  Instantiation
replaces the constant `frz 0`; it is not a substitution of a variable. -/
theorem frozen_instantiation_breaks :
    Reduces frozenTheory (ap "v" [frzVar 0, zeroN]) (levelVariable zeroN) ∧
      ¬ Conv frozenTheory (ap "v" [instOf zero, zeroN]) (levelVariable zeroN) := by
  refine ⟨frozen_fallback_step, fun convertible => ?_⟩
  have algebraicRules : ∀ rule ∈ frozenRules, algebraic true rule.lhs = true :=
    fun rule member => frozenTheory_orthogonal.leftAlgebraic rule member
  have reduced : Reduces frozenTheory (ap "v" [instOf zero, zeroN]) levelZero :=
    Reduces.of_evaluate frozenRules_linear (fuel := 6) (by decide +kernel)
  exact not_conv_of_normal frozenTheory_confluent
    (normal_of_stepOnce algebraicRules (term := levelZero) (by decide +kernel))
    (normal_of_stepOnce algebraicRules (term := levelVariable zeroN) (by decide +kernel))
    (by decide) (.trans _ _ _ (.symm _ _ reduced.conv) convertible)

/-! ## Agreement with the explicit substitution, on the translation of levels -/

/-- **The frozen strategy over the paper's rules converts the translations of
`max 1 α` and `α`.** -/
theorem frozen_relates_max_one_var :
    Conv frozenTheory (paperLevel frzVar maxOneVar) (paperLevel frzVar alpha) :=
  Joinable.conv ⟨levelVariable zeroN,
    Reduces.of_evaluate frozenRules_linear (fuel := 200) (by decide +kernel),
    Reduces.of_evaluate frozenRules_linear (fuel := 2) (by decide +kernel)⟩

/-- **Agreement with the explicit substitution is refuted on the image of the
paper's translation**: the frozen strategy over the paper's rules converts the
translations of `max 1 α` and `α`, the explicit substitution does not. -/
theorem frozen_disagrees_with_explicit :
    Conv frozenTheory (paperLevel frzVar maxOneVar) (paperLevel frzVar alpha) ∧
      ¬ Conv leanTheoryExplicit (code maxOneVar) (code alpha) :=
  ⟨frozen_relates_max_one_var, explicit_separates_max_one_var⟩

/-- **Theorem 3 fails for the frozen strategy over the paper's rules**: the
translations of the equivalent levels `max (succ α) (max 2 α)` and
`max 2 (succ α)` are not convertible (defect D2 of `LeanMinusLevels`). -/
theorem frozen_add_incomplete :
    LeanLevel.Equiv addPairLeft addPairRight ∧
      ¬ Conv frozenTheory (paperLevel frzVar addPairLeft) (paperLevel frzVar addPairRight) := by
  refine ⟨addPair_equiv, fun convertible => ?_⟩
  have algebraicRules : ∀ rule ∈ frozenRules, algebraic true rule.lhs = true :=
    fun rule member => frozenTheory_orthogonal.leftAlgebraic rule member
  have left : Reduces frozenTheory (paperLevel frzVar addPairLeft) addPairLeftNormal :=
    Reduces.of_evaluate frozenRules_linear (fuel := 2000) (by decide +kernel)
  have right : Reduces frozenTheory (paperLevel frzVar addPairRight) addPairRightNormal :=
    Reduces.of_evaluate frozenRules_linear (fuel := 2000) (by decide +kernel)
  exact not_conv_of_normal frozenTheory_confluent
    (normal_of_stepOnce algebraicRules (term := addPairLeftNormal) (by decide +kernel))
    (normal_of_stepOnce algebraicRules (term := addPairRightNormal) (by decide +kernel)) (by decide)
    (.trans _ _ _ (.symm _ _ left.conv) (.trans _ _ _ convertible right.conv))

/-- **With the corrected rules, the frozen strategy separates `max 1 α` and
`α`**, as the explicit substitution does. -/
theorem frozenCorrected_separates_max_one_var :
    ¬ Conv frozenTheoryCorrected (paperLevel frzVar maxOneVar) (paperLevel frzVar alpha) := by
  intro convertible
  have algebraicRules : ∀ rule ∈ frozenRulesCorrected, algebraic true rule.lhs = true :=
    fun rule member => frozenTheoryCorrected_orthogonal.leftAlgebraic rule member
  have left : Reduces frozenTheoryCorrected (paperLevel frzVar maxOneVar) maxOneVarNormal :=
    Reduces.of_evaluate frozenRulesCorrected_linear (fuel := 400) (by decide +kernel)
  have right : Reduces frozenTheoryCorrected (paperLevel frzVar alpha) (varCode zeroN) :=
    Reduces.of_evaluate frozenRulesCorrected_linear (fuel := 2) (by decide +kernel)
  exact not_conv_of_normal frozenTheoryCorrected_confluent
    (normal_of_stepOnce algebraicRules (term := maxOneVarNormal) (by decide +kernel))
    (normal_of_stepOnce algebraicRules (term := varCode zeroN) (by decide +kernel)) (by decide)
    (.trans _ _ _ (.symm _ _ left.conv) (.trans _ _ _ convertible right.conv))

/-- **With the corrected rules, the frozen strategy joins the pair of D2**, as
the explicit substitution does. -/
theorem frozenCorrected_joins_add_pair :
    Conv frozenTheoryCorrected (paperLevel frzVar addPairLeft) (paperLevel frzVar addPairRight) :=
  Joinable.conv ⟨addPairExplicitNormal,
    Reduces.of_evaluate frozenRulesCorrected_linear (fuel := 4000) (by decide +kernel),
    Reduces.of_evaluate frozenRulesCorrected_linear (fuel := 4000) (by decide +kernel)⟩

/-! ## The audit of C0, folded in

The two theorems below are those of C0's (Co-HS) priority audit of
2026-10-08, file `PriorityAudit.lean`, kept with their statements and proofs.  `selectV` selects between the two rules
on `v` only; `AuditStep` closes that selection and beta under contexts.
`auditStep_ordered` places `AuditStep` inside the ordered relation of this
module, which tries every rule of the paper in order.  The executable side,
with the Dedukti checker, is `artifacts/dedukti-sigma-poly-negative-20261008/`
of the Lean package. -/

namespace PriorityAudit

/-- First matching rule, restricted to the two clauses defining `v`. -/
def selectV : Term → Option Term
  | .app (.app (.con "v") (.app (.con "inst") level)) _ => some level
  | .app (.app (.con "v") _) index => some (levelVariable index)
  | _ => none

theorem select_inst (level index : Term) :
    selectV (ap "v" [instOf level, index]) = some level := rfl

theorem select_free_variable (index : Term) :
    selectV (ap "v" [.var 0, index]) = some (levelVariable index) := rfl

/-- A variable is already in head normal form, but instantiation changes
which of the two clauses is selected. -/
theorem selection_not_substitution_stable :
    selectV (subst0 (instOf zero) (ap "v" [.var 0, zeroN])) ≠
      (selectV (ap "v" [.var 0, zeroN])).map (subst0 (instOf zero)) := by
  decide

/-- The two `v` clauses selected in order, together with ordinary beta. -/
inductive AuditRoot : Term → Term → Prop where
  | beta (domain body argument : Term) :
      AuditRoot (.app (.lam domain body) argument) (subst0 argument body)
  | selected {source target : Term} : selectV source = some target → AuditRoot source target

/-- Close those local contractions under the existing one-hole contexts. -/
inductive AuditStep : Term → Term → Prop where
  | inContext (context : Context) {source target : Term} :
      AuditRoot source target → AuditStep (context.plug source) (context.plug target)

abbrev AuditConv := Relation.EqvGen AuditStep

def openBody : Term := ap "v" [.var 0, zeroN]
def application (term : Term) : Term := .app (.lam L openBody) (instOf term)

theorem beta_first (term : Term) :
    AuditStep (application term) (ap "v" [instOf term, zeroN]) := by
  have step := AuditStep.inContext Context.hole (AuditRoot.beta L openBody (instOf term))
  simpa [application, openBody, ap, apT, subst0, subst, lift, zeroN, Context.plug] using step

theorem then_inst (term : Term) : AuditStep (ap "v" [instOf term, zeroN]) term :=
  AuditStep.inContext .hole (.selected (select_inst term zeroN))

theorem binder_first (term : Term) :
    AuditStep (application term) (.app (.lam L collapsePoint) (instOf term)) :=
  AuditStep.inContext (.appFunction (.lamBody L .hole) (instOf term))
    (.selected (select_free_variable zeroN))

theorem then_beta (term : Term) :
    AuditStep (.app (.lam L collapsePoint) (instOf term)) collapsePoint := by
  have step := AuditStep.inContext Context.hole (AuditRoot.beta L collapsePoint (instOf term))
  simpa [collapsePoint, levelVariable, ap, apT, subst0, subst, zeroN, Context.plug] using step

/-- Giving the instance rule first place does not repair the equational
closure if fallback can fire on bound variables and beta is contextual. -/
theorem priority_contextual_conversion_collapses (left right : Term) :
    AuditConv left right := by
  have through (term : Term) : AuditConv term collapsePoint :=
    .trans _ _ _
      (.symm _ _ (.trans _ _ _ (.rel _ _ (beta_first term)) (.rel _ _ (then_inst term))))
      (.trans _ _ _ (.rel _ _ (binder_first term)) (.rel _ _ (then_beta term)))
  exact .trans _ _ _ (through left) (.symm _ _ (through right))

/-- **The audit's relation is part of the ordered relation**: every step of
`AuditStep` is a step of the paper's rules tried in order. -/
theorem auditStep_ordered {source target : Term} (step : AuditStep source target) :
    OrderedStep leanSig leanRules source target := by
  cases step with
  | inContext context root =>
      refine AtDepth.inContext context ?_
      cases root with
      | beta domain body argument => exact .beta domain body argument
      | @selected source target selected =>
          unfold selectV at selected
          split at selected
          · rename_i level other
            obtain rfl := Option.some.inj selected
            exact ordered_inst_root level other
          · rename_i first index notInst
            obtain rfl := Option.some.inj selected
            exact ordered_fallback_root (fun level same => notInst level same)
          · cases selected

end PriorityAudit

/-! ## Negative control: the paper's own rule set -/

/-- **The paper's rule set is not confluent**: were it confluent, `|0|` and
`|1|` would have distinct normal forms, while its conversion relates every two
terms (`leanTheory_conv_all`). -/
theorem leanTheory_not_confluent : ¬ Confluent (Step leanTheory) := by
  intro confluent
  have zeroReduces : Reduces leanTheory zero levelZero := zero_reduces.mono pureTheory_extends
  have oneReduces : Reduces leanTheory (succ zero) levelOne := one_reduces.mono pureTheory_extends
  exact not_conv_of_normal confluent levelZero_normal levelOne_normal (by decide)
    (.trans _ _ _ (.symm _ _ zeroReduces.conv)
      (.trans _ _ _ (leanTheory_conv_all zero (succ zero)) oneReduces.conv))

/-- Hence **the paper's rule set is not orthogonal** (`confluent_of_orthogonal`). -/
theorem leanTheory_not_orthogonal : ¬ leanTheory.Orthogonal :=
  fun orthogonal => leanTheory_not_confluent (confluent_of_orthogonal orthogonal)

#print axioms leanTheory_not_confluent
#print axioms PriorityAudit.selection_not_substitution_stable
#print axioms PriorityAudit.priority_contextual_conversion_collapses
#print axioms PriorityAudit.auditStep_ordered
#print axioms leanTheory_not_orthogonal
#print axioms orderedStep_iff_of_orthogonal
#print axioms ordered_inst_step
#print axioms ordered_fallback_step
#print axioms ordered_not_substitution_stable
#print axioms ordered_conv_collapses
#print axioms notBound_conv_collapses
#print axioms notBound_not_substitution_stable
#print axioms frozenTheory_orthogonal
#print axioms frozenTheory_confluent
#print axioms frozenTheory_conv_subst
#print axioms frozen_ordered_confluent
#print axioms frozen_ordered_subst
#print axioms frozen_instantiation_breaks
#print axioms frozen_disagrees_with_explicit
#print axioms frozen_add_incomplete
#print axioms frozenCorrected_separates_max_one_var
#print axioms frozenCorrected_joins_add_pair

end Mettapedia.GSLT.Dedukti.LeanMinus
