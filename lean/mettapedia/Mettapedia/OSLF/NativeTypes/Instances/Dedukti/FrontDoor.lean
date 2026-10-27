import Mettapedia.GSLT.Dedukti.StepScope
import Mettapedia.GSLT.Dedukti.Evaluator
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# Theories of the λΠ-calculus modulo at the front door

A theory presented by a list of rules (`Presents`) is the language `dkLanguage names rules`: λΠ terms, beta with a
substitution node, the six congruences and the declared rules. Its native types are asked at the encodings of closed
terms, through the front door.

- **The language is aligned and equation-free** (`profile`, `equationFree`): beta and the congruences are aligned, and a
  declared rule has no premise. So its reference steps are its contextual steps.
- **Encodings of closed terms are states** (`isState_encode`), and steps keep terms closed (`Step.wellScoped`).
- **A step of the front door's structure from an encoding is the encoding of a step of the theory** (`step_iff`), so
  "some step" and "no step" hold exactly where the theory steps and where the term is normal (`sat_steps_iff`,
  `sat_normal_iff`).
- **The one-step evaluator is a corollary** (`stepOnce_none_iff`): for linear rules with headed algebraic left sides,
  `stepOnce` finds nothing exactly where the front door's native type "no step" holds, and the front door's verdicts
  agree with it (`ask_normal_proved`, `ask_normal_refuted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Dedukti

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match (captureDepth captureDepthList)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ruleAligned ReferenceProfile extraNotDeeper extraNotDeeperList
  extraSites premiseAligned captureSites contextualStep_iff_step)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.Dedukti.Language (dkLanguage fixedRules declaredRule Presents encode step_encode_iff nameRule)
open Mettapedia.GSLT.LanguageDef.LF (Term WellScoped)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

/-- A declared rule of a theory of the λΠ-calculus modulo. -/
abbrev DkRule := Mettapedia.GSLT.Dedukti.RewriteRule

/-- A step of a theory of the λΠ-calculus modulo. -/
abbrev DkStep := Mettapedia.GSLT.Dedukti.Step

/-- A finite signature of constants. -/
abbrev DkSig := Mettapedia.GSLT.LanguageDef.LFTyping.Sig
open Mettapedia.Logic.Relation (IsNormal)

/-! ## The language is aligned and equation-free -/

mutual
theorem extraNotDeeper_nil (lhs : Pattern) : ∀ (depth : ℕ) (pattern : Pattern),
    extraNotDeeper lhs [] depth pattern = true
  | _, .fvar name => by
    simp only [extraNotDeeper]
    split <;> rfl
  | _, .bvar _ => rfl
  | depth, .apply _ arguments => by simp only [extraNotDeeper]; exact extraNotDeeperList_nil lhs depth arguments
  | depth, .lambda _ body => by simp only [extraNotDeeper]; exact extraNotDeeper_nil lhs (depth + 1) body
  | depth, .multiLambda n _ body => by simp only [extraNotDeeper]; exact extraNotDeeper_nil lhs (depth + n) body
  | depth, .subst body replacement => by
    simp only [extraNotDeeper, extraNotDeeper_nil lhs (depth + 1) body, extraNotDeeper_nil lhs depth replacement,
      Bool.and_self]
  | depth, .collection _ elements rest => by
    simp only [extraNotDeeper, extraNotDeeperList_nil lhs depth elements, Bool.true_and]
    split
    · split <;> rfl
    · rfl

theorem extraNotDeeperList_nil (lhs : Pattern) : ∀ (depth : ℕ) (patterns : List Pattern),
    extraNotDeeperList lhs [] depth patterns = true
  | _, [] => rfl
  | depth, pattern :: patterns => by
    simp only [extraNotDeeperList, extraNotDeeper_nil lhs depth pattern, extraNotDeeperList_nil lhs depth patterns,
      Bool.and_self]
end

/-- **A rule with no premise is aligned.** -/
theorem ruleAligned_of_premises_nil {rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule} (none : rule.premises = []) :
    ruleAligned rule = true := by
  have sites : extraSites rule = [] := by simp [extraSites, none]
  simp only [ruleAligned, none, List.all_nil, Bool.true_and, sites, extraNotDeeper_nil]

theorem fixedRules_aligned : fixedRules.all ruleAligned = true := by decide +kernel

/-- **The language of a theory is aligned**: its reference steps are its contextual steps. -/
theorem profile (names : List String) (rules : List DkRule) : ReferenceProfile (dkLanguage names rules) := by
  intro rule member
  rcases List.mem_append.mp member with fixed | declared
  · exact List.all_eq_true.mp fixedRules_aligned rule fixed
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp declared
    exact ruleAligned_of_premises_nil rfl

theorem equationFree (names : List String) (rules : List DkRule) :
    (dkLanguage names rules).isEquationFree = true := by
  have bags : (Mettapedia.GSLT.LanguageDef.DerivedHosting.lfLanguageDef.terms.any fun rule =>
      rule.params.any fun parameter => (TermParam.typeExpr parameter).mentionsCollection .hashBag) = false := by
    decide +kernel
  have sets : (Mettapedia.GSLT.LanguageDef.DerivedHosting.lfLanguageDef.terms.any fun rule =>
      rule.params.any fun parameter => (TermParam.typeExpr parameter).mentionsCollection .hashSet) = false := by
    decide +kernel
  have algebra : (Mettapedia.GSLT.LanguageDef.DerivedHosting.lfLanguageDef.terms.any fun rule =>
      rule.algebra?.isSome) = false := by decide +kernel
  simp only [LanguageDef.isEquationFree, LanguageDef.usesCollection, LanguageDef.hasAlgebraDeclarations,
    Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff]
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · rw [show (dkLanguage names rules).terms = _ ++ names.map nameRule from rfl, List.any_append, bags]
    simp [nameRule]
  · rw [show (dkLanguage names rules).terms = _ ++ names.map nameRule from rfl, List.any_append, sets]
    simp [nameRule]
  · rw [show (dkLanguage names rules).terms = _ ++ names.map nameRule from rfl, List.any_append, algebra]
    simp [nameRule]

/-! ## Encodings of closed terms are states -/

theorem encode_isObject (term : Term) : isObjectPattern (encode term) = true := by
  induction term with
  | srt sort => cases sort <;> simp [encode, isObjectPattern, isObjectPatternList]
  | _ => simp_all [encode, isObjectPattern, isObjectPatternList]

theorem encode_wellScopedAt {term : Term} {depth : Nat} (wellScoped : WellScoped depth term) :
    (encode term).isWellScopedAt depth = true := by
  induction wellScoped with
  | @srt _ sort => cases sort <;> simp [encode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | con => simp [encode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | var bound => simp [encode, Pattern.isWellScopedAt, bound]
  | _ => simp_all [encode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- **The encoding of a closed term is a state.** -/
theorem isState_encode {term : Term} (closed : WellScoped 0 term) : IsState (encode term) :=
  ⟨encode_wellScopedAt closed, encode_isObject term⟩

/-! ## Steps -/

/-- The front door's reading of the language of a theory. -/
abbrev Dk (names : List String) (rules : List DkRule) : NativeStructure Pattern :=
  referenceStructure RelationEnv.empty (dkLanguage names rules)

variable {theory : Theory} {names : List String} {rules : List DkRule}

/-- **A reference step from an encoding is the encoding of a step of the theory.** -/
theorem referenceStep_encode_iff (presents : Presents theory rules) {source : Term} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.Step RelationEnv.empty (dkLanguage names rules) (encode source) target ↔
      ∃ next, target = encode next ∧ DkStep theory source next := by
  rw [← contextualStep_iff_step RelationEnv.empty _ (profile names rules)]
  exact step_encode_iff presents

/-- **A step of the front door's structure from the encoding of a closed term is the encoding of a step of the
theory.** -/
theorem step_iff (presents : Presents theory rules) {source : Term} (closed : WellScoped 0 source)
    {target : Pattern} :
    (Dk names rules).step (encode source) .any target ↔ ∃ next, target = encode next ∧ DkStep theory source next := by
  have free := equationFree names rules
  constructor
  · rintro ⟨-, -, redex, contractum, witness, toRedex, -, valid, -, toTarget, -⟩
    rw [placed_iff rfl] at toRedex
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at toRedex toTarget
    subst toRedex toTarget
    exact (referenceStep_encode_iff presents).mp ⟨witness, valid⟩
  · rintro ⟨next, rfl, step⟩
    obtain ⟨witness, valid⟩ := (referenceStep_encode_iff (names := names) presents).mpr ⟨next, rfl, step⟩
    have nextClosed := Step.wellScoped presents step closed
    exact ⟨isState_encode closed, isState_encode nextClosed, encode source, encode next, witness,
      Relation.EqvGen.refl _, isState_encode closed, valid, isState_encode nextClosed, Relation.EqvGen.refl _, rfl⟩

/-- **Some step**, at the encoding of a closed term, is a step of the theory. -/
theorem sat_steps_iff (presents : Presents theory rules) {source : Term} (closed : WellScoped 0 source) :
    (Dk names rules).sat Env.closed (.possibly .any .top) (encode source) ↔ ∃ next, DkStep theory source next := by
  change (∃ next, (Dk names rules).step (encode source) .any next ∧ True) ↔ _
  constructor
  · rintro ⟨target, step, -⟩
    obtain ⟨next, -, step⟩ := (step_iff presents closed).mp step
    exact ⟨next, step⟩
  · rintro ⟨next, step⟩
    exact ⟨encode next, (step_iff presents closed).mpr ⟨next, rfl, step⟩, trivial⟩

/-- **No step**, at the encoding of a closed term, is normality in the theory. -/
theorem sat_normal_iff (presents : Presents theory rules) {source : Term} (closed : WellScoped 0 source) :
    (Dk names rules).sat Env.closed (.necessarily .any .bot) (encode source) ↔ IsNormal (DkStep theory) source := by
  change (∀ next, (Dk names rules).step (encode source) .any next → False) ↔ _
  constructor
  · intro none next step
    exact none (encode next) ((step_iff presents closed).mpr ⟨next, rfl, step⟩)
  · intro normal target step
    obtain ⟨next, -, step⟩ := (step_iff presents closed).mp step
    exact normal next step

/-! ## The one-step evaluator is a corollary -/

variable {signature : DkSig}

/-- **The evaluator finds nothing exactly where "no step" holds at the front door**, for linear rules with headed
algebraic left sides. -/
theorem stepOnce_none_iff (presents : Presents (Theory.ofSig signature rules) rules)
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup) {source : Term} (closed : WellScoped 0 source) :
    stepOnce signature rules source = none ↔
      (Dk names rules).sat Env.closed (.necessarily .any .bot) (encode source) := by
  rw [sat_normal_iff presents closed]
  constructor
  · exact normal_of_stepOnce presents.leftAlgebraic
  · intro normal
    cases found : stepOnce signature rules source with
    | none => rfl
    | some next => exact absurd (stepOnce_sound linear (fun _ member => member) found) (normal next)

/-- **What the front door proves about normality, the evaluator confirms.** -/
theorem ask_normal_proved (presents : Presents (Theory.ofSig signature rules) rules)
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup) {source : Term} (closed : WellScoped 0 source)
    {modelSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel rounds : ℕ}
    {hint : Option CertificateCandidate} {evidence : Evidence}
    (answered : ask RelationEnv.empty modelSignature (dkLanguage names rules) fuel (.necessarily .any .bot)
      (encode source) hint rounds = .proved evidence) :
    stepOnce signature rules source = none :=
  (stepOnce_none_iff presents linear closed).mpr (ask_proved answered)

/-- **What the front door refutes about normality, the evaluator confirms**: it finds a step. -/
theorem ask_normal_refuted (presents : Presents (Theory.ofSig signature rules) rules)
    (linear : ∀ rule ∈ rules, (patternVars rule.lhs).Nodup) {source : Term} (closed : WellScoped 0 source)
    {modelSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel rounds : ℕ}
    {hint : Option CertificateCandidate} {evidence : Evidence}
    (answered : ask RelationEnv.empty modelSignature (dkLanguage names rules) fuel (.necessarily .any .bot)
      (encode source) hint rounds = .refuted evidence) :
    stepOnce signature rules source ≠ none := fun none =>
  ask_refuted answered ((stepOnce_none_iff presents linear closed).mp none)

end Mettapedia.OSLF.NativeTypes.Instances.Dedukti
