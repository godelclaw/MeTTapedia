import Mettapedia.GSLT.Dedukti.Confluence

/-!
# A sound and complete one-step evaluator for theories given by finite lists

For a theory `Theory.ofSig signature rules` whose declared rules are linear on
the left:

* `matchPattern pattern term` matches a first-order pattern;
* `rootReduct` contracts the root of a term: beta, the unfolding of a
  definition, or the first rule of the list whose left side matches;
* `stepOnce` contracts the leftmost outermost redex;
* `evaluate fuel` iterates `stepOnce` at most `fuel` times.

They are sound: what `stepOnce` computes is a step (`stepOnce_sound`) and what
`evaluate` computes is a reduction (`evaluate_sound`).  When moreover every left
side is a headed algebraic pattern, `stepOnce` is complete: a term on which it
computes nothing has no step at all (`normal_of_stepOnce`).  So a concrete
reduction, and the normality of a concrete term, become computations that the
kernel checks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (IsNormal)

/-! ## Matching -/

/-- First-order matching of a pattern against a term: the bindings of the
pattern variables, in the order of their occurrences. -/
def matchPattern : Term → Term → Option (List (Nat × Term))
  | .var index, term => some [(index, term)]
  | .con name, .con other => if name = other then some [] else none
  | .srt sort, .srt other => if sort = other then some [] else none
  | .app function argument, .app function' argument' =>
      match matchPattern function function', matchPattern argument argument' with
      | some first, some second => some (first ++ second)
      | _, _ => none
  | _, _ => none

/-- The assignment read off a list of bindings. -/
def assignmentOf (bindings : List (Nat × Term)) (index : Nat) : Term :=
  (bindings.lookup index).getD (.srt .type)

/-- Every assignment that agrees with the bindings instantiates the pattern to
the term. -/
theorem matchPattern_inst :
    ∀ {pattern term : Term} {bindings : List (Nat × Term)},
      matchPattern pattern term = some bindings →
        ∀ assignment : Nat → Term, (∀ binding ∈ bindings, assignment binding.1 = binding.2) →
          inst assignment pattern = term := by
  intro pattern
  induction pattern with
  | var index =>
      intro term bindings matched assignment agrees
      simp only [matchPattern, Option.some.injEq] at matched
      subst matched
      rw [inst_var]
      exact agrees (index, term) (List.mem_singleton.mpr rfl)
  | con name =>
      intro term bindings matched assignment _
      cases term with
      | con other =>
          simp only [matchPattern] at matched
          split at matched
          · rename_i same
            subst same
            rfl
          · cases matched
      | _ => simp [matchPattern] at matched
  | srt sort =>
      intro term bindings matched assignment _
      cases term with
      | srt other =>
          simp only [matchPattern] at matched
          split at matched
          · rename_i same
            subst same
            rfl
          · cases matched
      | _ => simp [matchPattern] at matched
  | pi domain body _ _ =>
      intro term bindings matched
      cases term <;> simp [matchPattern] at matched
  | lam domain body _ _ =>
      intro term bindings matched
      cases term <;> simp [matchPattern] at matched
  | app function argument ihFunction ihArgument =>
      intro term bindings matched assignment agrees
      cases term with
      | app function' argument' =>
          simp only [matchPattern] at matched
          split at matched
          · rename_i first second firstMatched secondMatched
            obtain rfl := Option.some.inj matched
            rw [inst_app, ihFunction firstMatched assignment
              (fun binding member => agrees binding (List.mem_append_left _ member)),
              ihArgument secondMatched assignment
              (fun binding member => agrees binding (List.mem_append_right _ member))]
          · cases matched
      | _ => simp [matchPattern] at matched

/-- The bound variables are the variables of the pattern. -/
theorem matchPattern_keys :
    ∀ {pattern term : Term} {bindings : List (Nat × Term)},
      matchPattern pattern term = some bindings → bindings.map Prod.fst = patternVars pattern := by
  intro pattern
  induction pattern with
  | var index =>
      intro term bindings matched
      simp only [matchPattern, Option.some.injEq] at matched
      subst matched
      rfl
  | con name =>
      intro term bindings matched
      cases term with
      | con other =>
          simp only [matchPattern] at matched
          split at matched
          · obtain rfl := Option.some.inj matched
            rfl
          · cases matched
      | _ => simp [matchPattern] at matched
  | srt sort =>
      intro term bindings matched
      cases term with
      | srt other =>
          simp only [matchPattern] at matched
          split at matched
          · obtain rfl := Option.some.inj matched
            rfl
          · cases matched
      | _ => simp [matchPattern] at matched
  | pi domain body _ _ =>
      intro term bindings matched
      cases term <;> simp [matchPattern] at matched
  | lam domain body _ _ =>
      intro term bindings matched
      cases term <;> simp [matchPattern] at matched
  | app function argument ihFunction ihArgument =>
      intro term bindings matched
      cases term with
      | app function' argument' =>
          simp only [matchPattern] at matched
          split at matched
          · rename_i first second firstMatched secondMatched
            obtain rfl := Option.some.inj matched
            rw [List.map_append, ihFunction firstMatched, ihArgument secondMatched]
            rfl
          · cases matched
      | _ => simp [matchPattern] at matched

/-- In a list whose keys are distinct, the lookup of a key finds its value. -/
theorem lookup_of_nodup :
    ∀ {bindings : List (Nat × Term)}, (bindings.map Prod.fst).Nodup →
      ∀ binding ∈ bindings, bindings.lookup binding.1 = some binding.2 := by
  intro bindings
  induction bindings with
  | nil => intro _ binding member; cases member
  | cons head rest ih =>
      intro nodup binding member
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
      rcases List.mem_cons.mp member with rfl | inRest
      · simp [List.lookup]
      · have distinct : binding.1 ≠ head.1 := fun same =>
          nodup.1 ⟨binding, inRest, same⟩
        have notSame : (binding.1 == head.1) = false := by simpa using distinct
        have found := ih nodup.2 binding inRest
        simp [List.lookup, notSame, found]

/-- **Matching is sound** for a pattern linear in its variables. -/
theorem matchPattern_sound {pattern term : Term} {bindings : List (Nat × Term)}
    (matched : matchPattern pattern term = some bindings) (linear : (patternVars pattern).Nodup) :
    inst (assignmentOf bindings) pattern = term := by
  have nodup : (bindings.map Prod.fst).Nodup := by
    rw [matchPattern_keys matched]
    exact linear
  refine matchPattern_inst matched _ fun binding member => ?_
  simp [assignmentOf, lookup_of_nodup nodup binding member]

/-- **Matching is complete** for an algebraic pattern. -/
theorem matchPattern_complete (assignment : Nat → Term) :
    ∀ {pattern : Term} {headed : Bool}, algebraic headed pattern = true →
      (matchPattern pattern (inst assignment pattern)).isSome = true := by
  intro pattern
  induction pattern with
  | var index => intro headed _; simp [matchPattern]
  | srt sort => intro headed _; simp [matchPattern, inst, instantiate]
  | con name => intro headed _; simp [matchPattern, inst, instantiate]
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      obtain ⟨first, firstMatched⟩ := Option.isSome_iff_exists.mp (ihFunction functionAlgebraic)
      obtain ⟨second, secondMatched⟩ :=
        Option.isSome_iff_exists.mp (ihArgument argumentAlgebraic)
      rw [inst_app]
      simp [matchPattern, firstMatched, secondMatched]

/-! ## One step at the root -/

/-- The first rule of the list whose left side matches, applied. -/
def ruleReduct (rules : List RewriteRule) (term : Term) : Option Term :=
  rules.findSome? fun rule =>
    (matchPattern rule.lhs term).map fun bindings => inst (assignmentOf bindings) rule.rhs

/-- Contract the root: beta, the unfolding of a definition, or the first
matching rule. -/
def rootReduct (signature : Sig) (rules : List RewriteRule) (term : Term) : Option Term :=
  match term with
  | .app (.lam _ body) argument => some (subst0 argument body)
  | .con name =>
      match lookupBody signature name with
      | some body => some body
      | none => ruleReduct rules term
  | _ => ruleReduct rules term

variable {signature : Sig} {rules : List RewriteRule}

theorem ruleReduct_sound {declared : List RewriteRule}
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup)
    (covered : ∀ rule ∈ rules, rule ∈ declared) {term next : Term}
    (reduced : ruleReduct rules term = some next) :
    RootStep (Theory.ofSig signature declared) term next := by
  obtain ⟨rule, member, found⟩ := List.exists_of_findSome?_eq_some reduced
  obtain ⟨bindings, matched, rfl⟩ := Option.map_eq_some_iff.mp found
  have same := matchPattern_sound matched (linear rule member)
  rw [← same]
  exact .rule (assignmentOf bindings) (covered rule member)

/-- **The root contraction computed is a root step.** -/
theorem rootReduct_sound {declared : List RewriteRule}
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup)
    (covered : ∀ rule ∈ rules, rule ∈ declared) {term next : Term}
    (reduced : rootReduct signature rules term = some next) :
    RootStep (Theory.ofSig signature declared) term next := by
  unfold rootReduct at reduced
  split at reduced
  · obtain rfl := Option.some.inj reduced
    exact .beta _ _ _
  · split at reduced
    · rename_i name body defined
      obtain rfl := Option.some.inj reduced
      exact .delta defined
    · exact ruleReduct_sound linear covered reduced
  · exact ruleReduct_sound linear covered reduced

/-! ## One step anywhere -/

/-- Contract the leftmost outermost redex. -/
def stepOnce (signature : Sig) (rules : List RewriteRule) : Term → Option Term
  | .app function argument =>
      match rootReduct signature rules (.app function argument) with
      | some next => some next
      | none =>
          match stepOnce signature rules function with
          | some next => some (.app next argument)
          | none => (stepOnce signature rules argument).map (.app function ·)
  | .pi domain body =>
      match stepOnce signature rules domain with
      | some next => some (.pi next body)
      | none => (stepOnce signature rules body).map (.pi domain ·)
  | .lam domain body =>
      match stepOnce signature rules domain with
      | some next => some (.lam next body)
      | none => (stepOnce signature rules body).map (.lam domain ·)
  | term => rootReduct signature rules term

/-- **The step computed is a step.** -/
theorem stepOnce_sound {declared : List RewriteRule}
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup)
    (covered : ∀ rule ∈ rules, rule ∈ declared) :
    ∀ {term next : Term}, stepOnce signature rules term = some next →
      Step (Theory.ofSig signature declared) term next := by
  intro term
  induction term with
  | var index =>
      intro next reduced
      exact Step.root (rootReduct_sound linear covered reduced)
  | srt sort =>
      intro next reduced
      exact Step.root (rootReduct_sound linear covered reduced)
  | con name =>
      intro next reduced
      exact Step.root (rootReduct_sound linear covered reduced)
  | app function argument ihFunction ihArgument =>
      intro next reduced
      simp only [stepOnce] at reduced
      split at reduced
      · rename_i root rootReduced
        obtain rfl := Option.some.inj reduced
        exact Step.root (rootReduct_sound linear covered rootReduced)
      · split at reduced
        · rename_i inner innerReduced
          obtain rfl := Option.some.inj reduced
          exact (ihFunction innerReduced).plug (.appFunction .hole argument)
        · obtain ⟨inner, innerReduced, rfl⟩ := Option.map_eq_some_iff.mp reduced
          exact (ihArgument innerReduced).plug (.appArgument function .hole)
  | pi domain body ihDomain ihBody =>
      intro next reduced
      simp only [stepOnce] at reduced
      split at reduced
      · rename_i inner innerReduced
        obtain rfl := Option.some.inj reduced
        exact (ihDomain innerReduced).plug (.piDomain .hole body)
      · obtain ⟨inner, innerReduced, rfl⟩ := Option.map_eq_some_iff.mp reduced
        exact (ihBody innerReduced).plug (.piBody domain .hole)
  | lam domain body ihDomain ihBody =>
      intro next reduced
      simp only [stepOnce] at reduced
      split at reduced
      · rename_i inner innerReduced
        obtain rfl := Option.some.inj reduced
        exact (ihDomain innerReduced).plug (.lamDomain .hole body)
      · obtain ⟨inner, innerReduced, rfl⟩ := Option.map_eq_some_iff.mp reduced
        exact (ihBody innerReduced).plug (.lamBody domain .hole)

/-- Iterate `stepOnce` at most `fuel` times. -/
def evaluate (signature : Sig) (rules : List RewriteRule) : Nat → Term → Term
  | 0, term => term
  | fuel + 1, term =>
      match stepOnce signature rules term with
      | some next => evaluate signature rules fuel next
      | none => term

/-- **What `evaluate` computes is a reduction.** -/
theorem evaluate_sound (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup) :
    ∀ (fuel : Nat) (term : Term),
      Reduces (Theory.ofSig signature rules) term (evaluate signature rules fuel term) := by
  intro fuel
  induction fuel with
  | zero => intro term; exact .refl
  | succ fuel ih =>
      intro term
      simp only [evaluate]
      split
      · rename_i next reduced
        exact .head (stepOnce_sound linear (fun _ member => member) reduced) (ih next)
      · exact .refl

/-- A computed reduction, as a reduction. -/
theorem Reduces.of_evaluate (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup)
    {fuel : Nat} {source target : Term} (computed : evaluate signature rules fuel source = target) :
    Reduces (Theory.ofSig signature rules) source target :=
  computed ▸ evaluate_sound linear fuel source

/-! ## Completeness: a term with no computed step is normal -/

theorem ruleReduct_isSome {term : Term} {rule : RewriteRule} (assignment : Nat → Term)
    (member : rule ∈ rules) (isAlgebraic : algebraic true rule.lhs = true)
    (same : term = inst assignment rule.lhs) : (ruleReduct rules term).isSome = true := by
  subst same
  obtain ⟨bindings, matched⟩ :=
    Option.isSome_iff_exists.mp (matchPattern_complete assignment isAlgebraic)
  cases found : ruleReduct rules (inst assignment rule.lhs) with
  | some value => rfl
  | none =>
      unfold ruleReduct at found
      have absent := List.findSome?_eq_none_iff.mp found rule member
      rw [matched] at absent
      simp at absent

/-- A root step is found by `rootReduct`, when every left side is a headed
algebraic pattern. -/
theorem rootReduct_isSome (algebraicRules : ∀ rule ∈ rules, algebraic true rule.lhs = true)
    {term next : Term} (step : RootStep (Theory.ofSig signature rules) term next) :
    (rootReduct signature rules term).isSome = true := by
  cases step with
  | beta domain body argument => simp [rootReduct]
  | delta defined =>
      change lookupBody signature _ = _ at defined
      simp [rootReduct, defined]
  | @rule rule assignment member =>
      have isSome := ruleReduct_isSome assignment member (algebraicRules rule member) rfl
      unfold rootReduct
      split
      · rfl
      · split
        · rfl
        · exact isSome
      · exact isSome

/-- **A term on which `stepOnce` computes nothing has no step**, when every
left side is a headed algebraic pattern. -/
theorem normal_of_stepOnce (algebraicRules : ∀ rule ∈ rules, algebraic true rule.lhs = true) :
    ∀ {term : Term}, stepOnce signature rules term = none →
      IsNormal (Step (Theory.ofSig signature rules)) term := by
  have headed : (Theory.ofSig signature rules).Headed := fun rule member =>
    headConst_of_algebraic (algebraicRules rule member)
  intro term
  induction term with
  | var index =>
      intro computed next step
      exact RootStep.not_var headed step.var_inv
  | srt sort =>
      intro computed next step
      exact RootStep.not_srt headed step.srt_inv
  | con name =>
      intro computed next step
      have isSome := rootReduct_isSome algebraicRules step.con_inv
      simp only [stepOnce] at computed
      rw [computed] at isSome
      cases isSome
  | app function argument ihFunction ihArgument =>
      intro computed next step
      simp only [stepOnce] at computed
      split at computed
      · cases computed
      · rename_i rootNone
        split at computed
        · cases computed
        · rename_i functionNone
          have argumentNone : stepOnce signature rules argument = none := by
            cases inner : stepOnce signature rules argument with
            | none => rfl
            | some value => rw [inner] at computed; cases computed
          rcases step.app_inv with root | ⟨inner, innerStep, _⟩ | ⟨inner, innerStep, _⟩
          · have isSome := rootReduct_isSome algebraicRules root
            rw [rootNone] at isSome
            cases isSome
          · exact ihFunction functionNone inner innerStep
          · exact ihArgument argumentNone inner innerStep
  | pi domain body ihDomain ihBody =>
      intro computed next step
      simp only [stepOnce] at computed
      split at computed
      · cases computed
      · rename_i domainNone
        have bodyNone : stepOnce signature rules body = none := by
          cases inner : stepOnce signature rules body with
          | none => rfl
          | some value => rw [inner] at computed; cases computed
        rcases step.pi_inv with root | ⟨inner, innerStep, _⟩ | ⟨inner, innerStep, _⟩
        · exact RootStep.not_pi headed root
        · exact ihDomain domainNone inner innerStep
        · exact ihBody bodyNone inner innerStep
  | lam domain body ihDomain ihBody =>
      intro computed next step
      simp only [stepOnce] at computed
      split at computed
      · cases computed
      · rename_i domainNone
        have bodyNone : stepOnce signature rules body = none := by
          cases inner : stepOnce signature rules body with
          | none => rfl
          | some value => rw [inner] at computed; cases computed
        rcases step.lam_inv with root | ⟨inner, innerStep, _⟩ | ⟨inner, innerStep, _⟩
        · exact RootStep.not_lam headed root
        · exact ihDomain domainNone inner innerStep
        · exact ihBody bodyNone inner innerStep

#print axioms matchPattern_sound
#print axioms matchPattern_complete
#print axioms stepOnce_sound
#print axioms evaluate_sound
#print axioms normal_of_stepOnce

end Mettapedia.GSLT.Dedukti
