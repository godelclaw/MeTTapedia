import Mettapedia.GSLT.Dedukti.LanguageDefEncoding

/-!
# The language definition of a theory of the λΠ-calculus modulo, and its steps

`dkLanguage names rules` is `DerivedHosting.lfLanguageDef` with one name
constructor for each constant, beta with an explicit substitution node, the
six congruences, and the declared rules; it has no equation.

**The steps of the language on encodings are the steps of the theory**
(`step_encode_iff`): for a theory whose rules are those of the list, with
algebraic left sides that determine their right sides and no definition
(`Presents`), a step of the language from the encoding of a term is the
encoding of a step of the theory, and every step of the theory is one.  This
holds for every term, open or closed, and for every evaluator of the
premises other than congruence: the rules carry no other premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Language

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern GrammarRule LanguageDef Premise)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_correct)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList liftBVars_zero instantiateBVarAt
  instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator StepAt PremiseAt PremisesAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule
  applyBindingsForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued
  matchPattern_applyBindings_complete)

/-! ## The language -/

/-- The name constructor of a constant. -/
def nameRule (symbol : String) : GrammarRule :=
  { label := nameLabel symbol, category := "LFName", params := [], syntaxPattern := [] }

/-- `App(Lam(A, x. B), X)`. -/
def betaLeft : Pattern := .apply "App" [.apply "Lam" [.fvar "A", .lambda none (.fvar "B")], .fvar "X"]

/-- `App(Lam(A, x. B), X) ~> B[X/x]`, with the substitution node that the rule
semantics executes. -/
def betaRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "Beta", typeContext := [], premises := [], left := betaLeft,
    right := .subst (.fvar "B") (.fvar "X") }

/-- `App(F, X)`. -/
def appLeft : Pattern := .apply "App" [.fvar "F", .fvar "X"]

/-- `Pi(A, x. B)`. -/
def piLeft : Pattern := .apply "Pi" [.fvar "A", .lambda none (.fvar "B")]

/-- `Lam(A, x. B)`. -/
def lamLeft : Pattern := .apply "Lam" [.fvar "A", .lambda none (.fvar "B")]

/-- `F ~> G ⊢ App(F, X) ~> App(G, X)`. -/
def appFunctionRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "AppFunction", typeContext := [], premises := [.congruence (.fvar "F") (.fvar "G")],
    left := appLeft, right := .apply "App" [.fvar "G", .fvar "X"] }

/-- `X ~> Y ⊢ App(F, X) ~> App(F, Y)`. -/
def appArgumentRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "AppArgument", typeContext := [], premises := [.congruence (.fvar "X") (.fvar "Y")],
    left := appLeft, right := .apply "App" [.fvar "F", .fvar "Y"] }

/-- `A ~> C ⊢ Pi(A, x. B) ~> Pi(C, x. B)`. -/
def piDomainRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "PiDomain", typeContext := [], premises := [.congruence (.fvar "A") (.fvar "C")],
    left := piLeft, right := .apply "Pi" [.fvar "C", .lambda none (.fvar "B")] }

/-- `B ~> D ⊢ Pi(A, x. B) ~> Pi(A, x. D)`. -/
def piBodyRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "PiBody", typeContext := [], premises := [.congruence (.fvar "B") (.fvar "D")],
    left := piLeft, right := .apply "Pi" [.fvar "A", .lambda none (.fvar "D")] }

/-- `A ~> C ⊢ Lam(A, x. B) ~> Lam(C, x. B)`. -/
def lamDomainRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "LamDomain", typeContext := [], premises := [.congruence (.fvar "A") (.fvar "C")],
    left := lamLeft, right := .apply "Lam" [.fvar "C", .lambda none (.fvar "B")] }

/-- `B ~> D ⊢ Lam(A, x. B) ~> Lam(A, x. D)`. -/
def lamBodyRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "LamBody", typeContext := [], premises := [.congruence (.fvar "B") (.fvar "D")],
    left := lamLeft, right := .apply "Lam" [.fvar "A", .lambda none (.fvar "D")] }

/-- A declared rule as a rule of the language. -/
def declaredRule (index : Nat) (rule : RewriteRule) : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { «name» := "Rule" ++ toString index, typeContext := [], premises := [],
    left := toPattern 0 rule.lhs, right := toPattern 0 rule.rhs }

/-- Beta and the congruences. -/
def fixedRules : List Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule, lamBodyRule]

/-- **The language definition of a theory of the λΠ-calculus modulo**: the
sorts and constructors of `lfLanguageDef`, a name constructor for each
constant, no equation, beta, the congruences and the declared rules. -/
def dkLanguage (names : List String) (rules : List RewriteRule) : LanguageDef :=
  { «name» := "LambdaPiModulo"
    «types» := DerivedHosting.lfLanguageDef.types
    «terms» := DerivedHosting.lfLanguageDef.terms ++ names.map nameRule
    «equations» := []
    «rewrites» := fixedRules ++ rules.mapIdx declaredRule }

/-- A theory whose declared rules are those of a list, with algebraic left
sides that determine their right sides, and no transparent definition. -/
structure Presents (theory : Theory) (rules : List RewriteRule) : Prop where
  undefined : ∀ symbol, theory.body symbol = none
  rule_iff : ∀ rule, theory.rule rule ↔ rule ∈ rules
  leftAlgebraic : ∀ rule ∈ rules, algebraic true rule.lhs = true
  rightDetermined : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true

/-! ## Matching the fixed left sides -/

theorem matchPattern_appLeft (function argument : Term) :
    matchPattern appLeft (encode (.app function argument)) =
      [[("X", encode argument), ("F", encode function)]] := by
  simp [appLeft, encode, matchPattern, matchArgs, mergeBindings]

theorem matchPattern_piLeft (domain body : Term) :
    matchPattern piLeft (encode (.pi domain body)) =
      [[("B", encode body), ("A", encode domain)]] := by
  simp [piLeft, encode, matchPattern, matchArgs, mergeBindings]

theorem matchPattern_lamLeft (domain body : Term) :
    matchPattern lamLeft (encode (.lam domain body)) =
      [[("B", encode body), ("A", encode domain)]] := by
  simp [lamLeft, encode, matchPattern, matchArgs, mergeBindings]

theorem matchPattern_betaLeft (domain body argument : Term) :
    matchPattern betaLeft (encode (.app (.lam domain body) argument)) =
      [[("X", encode argument), ("B", encode body), ("A", encode domain)]] := by
  simp [betaLeft, encode, matchPattern, matchArgs, mergeBindings]

theorem mem_matchPattern_appLeft {source : Term} {bindings : Bindings}
    (member : bindings ∈ matchPattern appLeft (encode source)) :
    ∃ function argument, source = .app function argument ∧
      bindings = [("X", encode argument), ("F", encode function)] := by
  cases source with
  | app function argument =>
      rw [matchPattern_appLeft] at member
      exact ⟨function, argument, rfl, List.mem_singleton.mp member⟩
  | srt sort => cases sort <;> simp [appLeft, encode, matchPattern] at member
  | _ => simp [appLeft, encode, matchPattern] at member

theorem mem_matchPattern_piLeft {source : Term} {bindings : Bindings}
    (member : bindings ∈ matchPattern piLeft (encode source)) :
    ∃ domain body, source = .pi domain body ∧
      bindings = [("B", encode body), ("A", encode domain)] := by
  cases source with
  | pi domain body =>
      rw [matchPattern_piLeft] at member
      exact ⟨domain, body, rfl, List.mem_singleton.mp member⟩
  | srt sort => cases sort <;> simp [piLeft, encode, matchPattern] at member
  | _ => simp [piLeft, encode, matchPattern] at member

theorem mem_matchPattern_lamLeft {source : Term} {bindings : Bindings}
    (member : bindings ∈ matchPattern lamLeft (encode source)) :
    ∃ domain body, source = .lam domain body ∧
      bindings = [("B", encode body), ("A", encode domain)] := by
  cases source with
  | lam domain body =>
      rw [matchPattern_lamLeft] at member
      exact ⟨domain, body, rfl, List.mem_singleton.mp member⟩
  | srt sort => cases sort <;> simp [lamLeft, encode, matchPattern] at member
  | _ => simp [lamLeft, encode, matchPattern] at member

theorem mem_matchPattern_betaLeft {source : Term} {bindings : Bindings}
    (member : bindings ∈ matchPattern betaLeft (encode source)) :
    ∃ domain body argument, source = .app (.lam domain body) argument ∧
      bindings = [("X", encode argument), ("B", encode body), ("A", encode domain)] := by
  cases source with
  | app function argument =>
      cases function with
      | lam domain body =>
          rw [matchPattern_betaLeft] at member
          exact ⟨domain, body, argument, rfl, List.mem_singleton.mp member⟩
      | srt sort => cases sort <;> simp [betaLeft, encode, matchPattern, matchArgs] at member
      | _ => simp [betaLeft, encode, matchPattern, matchArgs] at member
  | srt sort => cases sort <;> simp [betaLeft, encode, matchPattern] at member
  | _ => simp [betaLeft, encode, matchPattern] at member

/-! ## Applying the fixed right sides -/

theorem apply_betaRule (domain body argument : Term) :
    applyRuleBindings betaRule [("X", encode argument), ("B", encode body), ("A", encode domain)] =
      encode (subst0 argument body) := by
  rw [← instantiateBVar_encode]
  simp [applyRuleBindings, betaRule, betaLeft, applyBindingsScoped, captureDepth, captureDepthList,
    liftBVars_zero, instantiateBVar]

theorem apply_appFunctionRule (function argument : Pattern) (candidate : Pattern) :
    applyRuleBindings appFunctionRule [("G", candidate), ("X", argument), ("F", function)] =
      .apply "App" [candidate, argument] := by
  simp [applyRuleBindings, appFunctionRule, appLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

theorem apply_appArgumentRule (function argument : Pattern) (candidate : Pattern) :
    applyRuleBindings appArgumentRule [("Y", candidate), ("X", argument), ("F", function)] =
      .apply "App" [function, candidate] := by
  simp [applyRuleBindings, appArgumentRule, appLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

theorem apply_piDomainRule (domain body : Pattern) (candidate : Pattern) :
    applyRuleBindings piDomainRule [("C", candidate), ("B", body), ("A", domain)] =
      .apply "Pi" [candidate, .lambda none body] := by
  simp [applyRuleBindings, piDomainRule, piLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

theorem apply_piBodyRule (domain body : Pattern) (candidate : Pattern) :
    applyRuleBindings piBodyRule [("D", candidate), ("B", body), ("A", domain)] =
      .apply "Pi" [domain, .lambda none candidate] := by
  simp [applyRuleBindings, piBodyRule, piLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

theorem apply_lamDomainRule (domain body : Pattern) (candidate : Pattern) :
    applyRuleBindings lamDomainRule [("C", candidate), ("B", body), ("A", domain)] =
      .apply "Lam" [candidate, .lambda none body] := by
  simp [applyRuleBindings, lamDomainRule, lamLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

theorem apply_lamBodyRule (domain body : Pattern) (candidate : Pattern) :
    applyRuleBindings lamBodyRule [("D", candidate), ("B", body), ("A", domain)] =
      .apply "Lam" [domain, .lambda none candidate] := by
  simp [applyRuleBindings, lamBodyRule, lamLeft, applyBindingsScoped, captureDepth,
    captureDepthList, liftBVars_zero]

/-! ## Congruence premises -/

variable {base : BasePremiseEvaluator} {lang : LanguageDef}

/-- What one congruence premise between two metavariables gives. -/
theorem premisesAt_congruence_inv {fuel : Nat} {initial final : Bindings} {source target : String}
    (premises : PremisesAt base lang fuel initial [.congruence (.fvar source) (.fvar target)] final) :
    ∃ candidate, StepAt base lang fuel (applyBindings initial (.fvar source)) candidate ∧
      mergeBindings initial [(target, candidate)] = some final := by
  cases premises with
  | cons premise rest =>
      cases rest with
      | nil =>
          cases premise with
          | congruence step matched merged =>
              simp only [matchPattern, List.mem_singleton] at matched
              subst matched
              exact ⟨_, step, merged⟩

/-- One congruence premise between two metavariables, from a step. -/
theorem premisesAt_congruence {fuel : Nat} {initial final : Bindings} {source target : String}
    {candidate : Pattern}
    (step : StepAt base lang fuel (applyBindings initial (.fvar source)) candidate)
    (merged : mergeBindings initial [(target, candidate)] = some final) :
    PremisesAt base lang fuel initial [.congruence (.fvar source) (.fvar target)] final :=
  .cons (.congruence step (by simp [matchPattern]) merged) (.nil final)

/-! ## Declared rules -/

/-- The bindings of an assignment on a list of pattern variables. -/
def assignmentBindings (indices : List Nat) (assignment : Nat → Term) : Bindings :=
  indices.map fun index => (metaName index, encode (assignment index))

theorem lookupOrFvar_assignmentBindings (assignment : Nat → Term) :
    ∀ {indices : List Nat} {index : Nat}, index ∈ indices →
      lookupOrFvar (assignmentBindings indices assignment) (metaName index) =
        encode (assignment index) := by
  intro indices
  induction indices with
  | nil => intro index member; simp at member
  | cons head rest ih =>
      intro index member
      by_cases same : head = index
      · subst same
        simp [assignmentBindings, lookupOrFvar, applyBindings]
      · have other : metaName head ≠ metaName index := fun equal => same (metaName_injective equal)
        have inRest : index ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have recursive := ih inRest
        have differs : (metaName head == metaName index) = false := beq_false_of_ne other
        simp only [assignmentBindings, lookupOrFvar, applyBindings, List.map_cons,
          List.find?_cons, differs] at recursive ⊢
        exact recursive

/-- The pattern of an algebraic left side, under the bindings of an assignment,
is the encoding of the instance. -/
theorem applyBindings_toPattern (bindings : Bindings) (assignment : Nat → Term) :
    ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
      (∀ index ∈ patternVars term, lookupOrFvar bindings (metaName index) = encode (assignment index)) →
        applyBindings bindings (toPattern 0 term) = encode (inst assignment term) := by
  intro term
  induction term with
  | var index =>
      intro headed _ values
      have value := values index (List.mem_singleton.mpr rfl)
      simpa [toPattern, lookupOrFvar] using value
  | srt sort => intro headed _ _; cases sort <;> simp [toPattern, encode, applyBindings]
  | con symbol => intro headed _ _; simp [toPattern, encode, applyBindings]
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic values
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      simp only [toPattern, applyBindings, List.map_cons, List.map_nil, inst_app, encode]
      rw [ihFunction functionAlgebraic fun index member =>
          values index (List.mem_append_left _ member),
        ihArgument argumentAlgebraic fun index member =>
          values index (List.mem_append_right _ member)]

/-- **A declared rule fires on an encoding exactly at the instances of its
left side, and gives the encoding of the instance of its right side.** -/
theorem declared_root_sound {rule : RewriteRule} (algebraicLeft : algebraic true rule.lhs = true)
    (determined : usesOnly (patternVars rule.lhs) 0 rule.rhs = true) {source : Term}
    {bindings : Bindings} (matched : bindings ∈ matchPattern (toPattern 0 rule.lhs) (encode source)) :
    ∃ assignment : Nat → Term, source = inst assignment rule.lhs ∧
      applyBindingsScoped (toPattern 0 rule.lhs) bindings 0 (toPattern 0 rule.rhs) =
        encode (inst assignment rule.rhs) := by
  have correct := matchPattern_correct matched (toPattern_matchCorrect algebraicLeft)
  obtain ⟨assignment, sourceEq, values⟩ :=
    exists_assignment_of_applyBindings bindings algebraicLeft source correct
  exact ⟨assignment, sourceEq,
    applyBindingsScoped_toPattern algebraicLeft bindings assignment values rule.rhs 0 determined⟩

theorem declared_root_complete {rule : RewriteRule} (algebraicLeft : algebraic true rule.lhs = true)
    (determined : usesOnly (patternVars rule.lhs) 0 rule.rhs = true) (assignment : Nat → Term) :
    ∃ bindings ∈ matchPattern (toPattern 0 rule.lhs) (encode (inst assignment rule.lhs)),
      applyBindingsScoped (toPattern 0 rule.lhs) bindings 0 (toPattern 0 rule.rhs) =
        encode (inst assignment rule.rhs) := by
  have applied := applyBindings_toPattern (assignmentBindings (patternVars rule.lhs) assignment)
    assignment algebraicLeft fun index member => lookupOrFvar_assignmentBindings assignment member
  obtain ⟨found, matched, -⟩ := matchPattern_applyBindings_complete
    (bs := assignmentBindings (patternVars rule.lhs) assignment) (toPattern_matchCorrect algebraicLeft)
  rw [applied] at matched
  obtain ⟨other, sameInstance, applyEq⟩ := declared_root_sound algebraicLeft determined matched
  refine ⟨found, matched, ?_⟩
  rw [applyEq]
  have agree := eq_of_inst_eq algebraicLeft sameInstance.symm
  rw [show inst other rule.rhs = inst assignment rule.rhs from
    instantiate_congr_of_usesOnly agree rule.rhs 0 determined]

/-! ## The steps of the language on encodings -/

variable {theory : Theory} {names : List String} {rules : List RewriteRule}

theorem fixed_mem {rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule} (member : rule ∈ fixedRules) :
    rule ∈ (dkLanguage names rules).rewrites :=
  List.mem_append_left _ member

theorem declared_mem {index : Nat} (bound : index < rules.length) :
    declaredRule index rules[index] ∈ (dkLanguage names rules).rewrites :=
  List.mem_append_right _ (List.mem_mapIdx.mpr ⟨index, bound, rfl⟩)

/-- **Soundness**: a step of the language from an encoding is the encoding of a
step of the theory. -/
theorem stepAt_encode_sound (presents : Presents theory rules) :
    ∀ (fuel : Nat) {source : Term} {target : Pattern},
      StepAt base (dkLanguage names rules) fuel (encode source) target →
        ∃ next, target = encode next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      cases step with
      | rule member matched premises targetEq =>
          rw [matchPatternForRule_eq_syntactic] at matched
          rw [applyBindingsForRule_eq_syntactic] at targetEq
          rcases List.mem_append.mp member with fixed | declared
          · simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at fixed
            rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · obtain ⟨domain, body, argument, rfl, rfl⟩ := mem_matchPattern_betaLeft matched
              cases premises
              exact ⟨_, by rw [← targetEq, apply_betaRule],
                Dedukti.Step.root (.beta domain body argument)⟩
            · obtain ⟨function, argument, rfl, rfl⟩ := mem_matchPattern_appLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.app next argument, by rw [← targetEq, apply_appFunctionRule]; rfl,
                innerStep.plug (.appFunction .hole argument)⟩
            · obtain ⟨function, argument, rfl, rfl⟩ := mem_matchPattern_appLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.app function next, by rw [← targetEq, apply_appArgumentRule]; rfl,
                innerStep.plug (.appArgument function .hole)⟩
            · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_piLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.pi next body, by rw [← targetEq, apply_piDomainRule]; rfl,
                innerStep.plug (.piDomain .hole body)⟩
            · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_piLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.pi domain next, by rw [← targetEq, apply_piBodyRule]; rfl,
                innerStep.plug (.piBody domain .hole)⟩
            · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_lamLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.lam next body, by rw [← targetEq, apply_lamDomainRule]; rfl,
                innerStep.plug (.lamDomain .hole body)⟩
            · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_lamLeft matched
              obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
              simp [applyBindings] at inner
              obtain ⟨next, rfl, innerStep⟩ := ih inner
              simp [mergeBindings] at merged
              subst merged
              exact ⟨.lam domain next, by rw [← targetEq, apply_lamBodyRule]; rfl,
                innerStep.plug (.lamBody domain .hole)⟩
          · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp declared
            have ruleMember : rules[index] ∈ rules := List.getElem_mem bound
            cases premises
            obtain ⟨assignment, rfl, applied⟩ :=
              declared_root_sound (presents.leftAlgebraic _ ruleMember)
                (presents.rightDetermined _ ruleMember) matched
            exact ⟨_, by rw [← targetEq]; exact applied,
              Dedukti.Step.root (.rule assignment ((presents.rule_iff _).mpr ruleMember))⟩

/-- A step by a rule with one congruence premise between two metavariables. -/
theorem stepAt_of_congruence {fuel : Nat} {rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule}
    (member : rule ∈ lang.rewrites) {source target candidate : Pattern} {initial final : Bindings}
    {premiseSource premiseTarget : String}
    (premisesEq : rule.premises = [.congruence (.fvar premiseSource) (.fvar premiseTarget)])
    (matched : initial ∈ matchPattern rule.left source)
    (inner : StepAt base lang fuel (applyBindings initial (.fvar premiseSource)) candidate)
    (merged : mergeBindings initial [(premiseTarget, candidate)] = some final)
    (applied : applyRuleBindings rule final = target) :
    StepAt base lang (fuel + 1) source target := by
  refine StepAt.rule (initialBindings := initial) (finalBindings := final) member ?_ ?_ ?_
  · rw [matchPatternForRule_eq_syntactic]
    exact matched
  · rw [premisesEq]
    exact premisesAt_congruence inner merged
  · rw [applyBindingsForRule_eq_syntactic]
    exact applied

/-- A step by a premise-free rule. -/
theorem stepAt_of_premiseFree {rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule}
    (member : rule ∈ lang.rewrites) {source target : Pattern} {initial : Bindings}
    (premisesEq : rule.premises = []) (matched : initial ∈ matchPattern rule.left source)
    (applied : applyRuleBindings rule initial = target) :
    StepAt base lang 1 source target := by
  refine StepAt.rule (initialBindings := initial) (finalBindings := initial) member ?_ ?_ ?_
  · rw [matchPatternForRule_eq_syntactic]
    exact matched
  · rw [premisesEq]
    exact .nil initial
  · rw [applyBindingsForRule_eq_syntactic]
    exact applied

/-- **Completeness**: every step of the theory is a step of the language
between the encodings. -/
theorem stepAt_encode_complete (presents : Presents theory rules) {source next : Term}
    (step : Dedukti.Step theory source next) :
    ∃ fuel, StepAt base (dkLanguage names rules) fuel (encode source) (encode next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          cases root with
          | beta domain body argument =>
              refine ⟨1, stepAt_of_premiseFree (rule := betaRule) (fixed_mem (by simp [fixedRules]))
                rfl ?_ (apply_betaRule domain body argument)⟩
              show _ ∈ matchPattern betaLeft (encode (.app (.lam domain body) argument))
              rw [matchPattern_betaLeft]
              exact List.mem_singleton.mpr rfl
          | delta defined => rw [presents.undefined] at defined; cases defined
          | @rule rule assignment member =>
              have ruleMember := (presents.rule_iff rule).mp member
              obtain ⟨index, bound, ruleEq⟩ := List.getElem_of_mem ruleMember
              subst ruleEq
              obtain ⟨bindings, matched, applied⟩ := declared_root_complete
                (presents.leftAlgebraic _ ruleMember) (presents.rightDetermined _ ruleMember) assignment
              exact ⟨1, stepAt_of_premiseFree (declared_mem bound) rfl matched applied⟩
      | appFunction rest argument ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := appFunctionRule)
            (initial := [("X", encode argument), ("F", encode (rest.plug redex))]) (candidate := encode (rest.plug contractum))
            (final := ("G", encode (rest.plug contractum)) :: [("X", encode argument), ("F", encode (rest.plug redex))])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_appFunctionRule _ _ _)⟩
          show _ ∈ matchPattern appLeft (encode (.app (rest.plug _) argument))
          rw [matchPattern_appLeft]
          exact List.mem_singleton.mpr rfl
      | appArgument function rest ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := appArgumentRule)
            (initial := [("X", encode (rest.plug redex)), ("F", encode function)]) (candidate := encode (rest.plug contractum))
            (final := ("Y", encode (rest.plug contractum)) :: [("X", encode (rest.plug redex)), ("F", encode function)])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_appArgumentRule _ _ _)⟩
          show _ ∈ matchPattern appLeft (encode (.app function (rest.plug _)))
          rw [matchPattern_appLeft]
          exact List.mem_singleton.mpr rfl
      | piDomain rest body ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := piDomainRule)
            (initial := [("B", encode body), ("A", encode (rest.plug redex))]) (candidate := encode (rest.plug contractum))
            (final := ("C", encode (rest.plug contractum)) :: [("B", encode body), ("A", encode (rest.plug redex))])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_piDomainRule _ _ _)⟩
          show _ ∈ matchPattern piLeft (encode (.pi (rest.plug _) body))
          rw [matchPattern_piLeft]
          exact List.mem_singleton.mpr rfl
      | piBody domain rest ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := piBodyRule)
            (initial := [("B", encode (rest.plug redex)), ("A", encode domain)]) (candidate := encode (rest.plug contractum))
            (final := ("D", encode (rest.plug contractum)) :: [("B", encode (rest.plug redex)), ("A", encode domain)])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_piBodyRule _ _ _)⟩
          show _ ∈ matchPattern piLeft (encode (.pi domain (rest.plug _)))
          rw [matchPattern_piLeft]
          exact List.mem_singleton.mpr rfl
      | lamDomain rest body ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := lamDomainRule)
            (initial := [("B", encode body), ("A", encode (rest.plug redex))]) (candidate := encode (rest.plug contractum))
            (final := ("C", encode (rest.plug contractum)) :: [("B", encode body), ("A", encode (rest.plug redex))])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_lamDomainRule _ _ _)⟩
          show _ ∈ matchPattern lamLeft (encode (.lam (rest.plug _) body))
          rw [matchPattern_lamLeft]
          exact List.mem_singleton.mpr rfl
      | lamBody domain rest ih =>
          obtain ⟨fuel, inner⟩ := ih
          refine ⟨fuel + 1, stepAt_of_congruence (rule := lamBodyRule)
            (initial := [("B", encode (rest.plug redex)), ("A", encode domain)]) (candidate := encode (rest.plug contractum))
            (final := ("D", encode (rest.plug contractum)) :: [("B", encode (rest.plug redex)), ("A", encode domain)])
            (fixed_mem (by simp [fixedRules])) rfl ?_ (by simpa [applyBindings] using inner)
            (by simp [mergeBindings]) (apply_lamBodyRule _ _ _)⟩
          show _ ∈ matchPattern lamLeft (encode (.lam domain (rest.plug _)))
          rw [matchPattern_lamLeft]
          exact List.mem_singleton.mpr rfl

/-- **The steps of the language on encodings are the steps of the theory.** -/
theorem step_encode_iff (presents : Presents theory rules) {source : Term} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (dkLanguage names rules) (encode source) target ↔
      ∃ next, target = encode next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact stepAt_encode_sound presents fuel step
  · rintro ⟨next, rfl, step⟩
    exact stepAt_encode_complete presents step

#print axioms step_encode_iff

end Mettapedia.GSLT.Dedukti.Language
