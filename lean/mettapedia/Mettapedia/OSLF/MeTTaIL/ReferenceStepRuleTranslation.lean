import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! Rule-index transport on a domain closed under congruence children.
Every selected target row is the original row. Witness transport preserves
bindings, candidates and premise order while changing only rule indices. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ReflectiveCanonical

mutual
  def Witness.mapRules (indices : Nat → Nat) : Witness → Witness
    | .base result => .base result
    | .premiseStep child candidate matched result =>
        .premiseStep (child.mapRules indices) candidate matched result
    | .rule index initial premises => .rule (indices index) initial (Witness.mapRulesList indices premises)
    | .forAll bodies => .forAll (Witness.mapRulesList indices bodies)

  def Witness.mapRulesList (indices : Nat → Nat) : List Witness → List Witness
    | [] => []
    | first :: rest => first.mapRules indices :: Witness.mapRulesList indices rest
end

mutual
  theorem Witness.mapRules_comp (first second : Nat → Nat) (witness : Witness) :
      (witness.mapRules first).mapRules second = witness.mapRules (second ∘ first) := by
    cases witness with
    | base result => rfl
    | premiseStep child candidate matched result =>
      simp only [Witness.mapRules, Witness.mapRules_comp first second child]
    | rule index initial premises =>
      simp only [Witness.mapRules, Witness.mapRulesList_comp first second premises, Function.comp_apply]
    | forAll bodies => simp only [Witness.mapRules, Witness.mapRulesList_comp first second bodies]
  termination_by sizeOf witness
  decreasing_by all_goals simp_all <;> omega

  theorem Witness.mapRulesList_comp (first second : Nat → Nat) (witnesses : List Witness) :
      Witness.mapRulesList second (Witness.mapRulesList first witnesses) =
        Witness.mapRulesList (second ∘ first) witnesses := by
    cases witnesses with
    | nil => rfl
    | cons witness rest =>
      simp only [Witness.mapRulesList, Witness.mapRules_comp first second witness,
        Witness.mapRulesList_comp first second rest]
  termination_by sizeOf witnesses
  decreasing_by all_goals simp_all <;> omega
end

mutual
  theorem Witness.mapRules_id (witness : Witness) : witness.mapRules id = witness := by
    cases witness with
    | base result => rfl
    | premiseStep child candidate matched result => simp only [Witness.mapRules, Witness.mapRules_id child]
    | rule index initial premises => simp only [Witness.mapRules, Witness.mapRulesList_id premises, id_eq]
    | forAll bodies => simp only [Witness.mapRules, Witness.mapRulesList_id bodies]
  termination_by sizeOf witness
  decreasing_by all_goals simp_all <;> omega

  theorem Witness.mapRulesList_id (witnesses : List Witness) : Witness.mapRulesList id witnesses = witnesses := by
    cases witnesses with
    | nil => rfl
    | cons witness rest => simp only [Witness.mapRulesList, Witness.mapRules_id witness, Witness.mapRulesList_id rest]
  termination_by sizeOf witnesses
  decreasing_by all_goals simp_all <;> omega
end

theorem Witness.mapRules_add_sub (offset : Nat) (witness : Witness) :
    (witness.mapRules (· + offset)).mapRules (· - offset) = witness := by
  rw [Witness.mapRules_comp]
  have cancel : (fun index => index - offset) ∘ (fun index => index + offset) = id := by
    funext index
    simp
  rw [cancel, Witness.mapRules_id]

theorem Witness.mapRules_add_injective (offset : Nat) : Function.Injective (Witness.mapRules (· + offset)) := by
  intro first second equal
  have reversed := congrArg (Witness.mapRules (· - offset)) equal
  simpa only [Witness.mapRules_add_sub] using reversed

/-- Congruence children stay in the domain at their actual capture depth. -/
def CongruenceClosed (domain : Pattern → Prop) (sites : Pattern) (premise : Premise) : Prop :=
  ∃ source target, premise = .congruence source target ∧
    ∀ bindings, domain (applyBindingsScoped sites bindings (stepDepth sites premise) source)

/-- A rule selection with unchanged rows and a checked child-closed domain. -/
structure RuleTranslation (source target : LanguageDef) (domain : Pattern → Prop) where
  indices : Nat → Nat
  selected : ∀ redex, domain redex → ∀ (index : Nat) (rule : RewriteRule),
    source.rewrites[index]? = some rule → ∀ initial,
      initial ∈ matchPattern rule.left redex → target.rewrites[indices index]? = some rule
  children : ∀ redex, domain redex → ∀ (index : Nat) (rule : RewriteRule),
    source.rewrites[index]? = some rule → ∀ initial,
      initial ∈ matchPattern rule.left redex →
        ∀ premise ∈ rule.premises, CongruenceClosed domain (captureSites rule) premise

variable {source target : LanguageDef} {domain : Pattern → Prop}

mutual
  theorem stepValid_mapRules (translation : RuleTranslation source target domain)
      (environment : RelationEnv) (redex : Pattern) (inside : domain redex)
      {witness : Witness} {result : Pattern}
      (valid : StepValid environment source redex witness result) :
      StepValid environment target redex (witness.mapRules translation.indices) result := by
    cases valid with
    | @rule _ index rule initial final witnesses found matched premises =>
      have ordinary : initial ∈ matchPattern rule.left redex := by
        simpa only [matchPatternForRule_eq_syntactic] using matched
      exact .rule (translation.selected redex inside index rule found initial ordinary)
        (by simpa only [matchPatternForRule_eq_syntactic] using ordinary)
        (premisesValid_mapRules translation environment _ _ _ _
          (translation.children redex inside index rule found initial ordinary) premises)
  termination_by sizeOf witness
  decreasing_by
    all_goals subst_vars
    all_goals simp only [Witness.rule.sizeOf_spec]
    all_goals omega

  theorem premisesValid_mapRules (translation : RuleTranslation source target domain)
      (environment : RelationEnv) (sites : Pattern) (initial final : Bindings) (premises : List Premise)
      (closed : ∀ premise ∈ premises, CongruenceClosed domain sites premise)
      {witnesses : List Witness}
      (valid : PremisesValid environment source sites initial premises witnesses final) :
      PremisesValid environment target sites initial premises
        (Witness.mapRulesList translation.indices witnesses) final := by
    cases valid with
    | nil => exact .nil _
    | @cons _ initial middle final premise premises witness witnesses first rest =>
      obtain ⟨childSource,childTarget,premiseEqual,childClosed⟩ := closed premise List.mem_cons_self
      subst premise
      have translated : PremiseValid environment target sites initial (.congruence childSource childTarget)
          (witness.mapRules translation.indices) middle := by
        cases first with
        | base base _ => cases base
        | step endpoints child matched merged =>
          simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
          obtain ⟨rfl,rfl⟩ := endpoints
          exact .step rfl
            (stepValid_mapRules translation environment _ (childClosed initial) child) matched merged
      exact .cons translated
        (premisesValid_mapRules translation environment sites middle final premises
          (fun premise member => closed premise (List.mem_cons_of_mem _ member)) rest)
  termination_by sizeOf witnesses
  decreasing_by
    all_goals subst_vars
    all_goals simp only [Witness.premiseStep.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

theorem step_mapRules (translation : RuleTranslation source target domain)
    (environment : RelationEnv) {redex result : Pattern} (inside : domain redex)
    (stepped : Step environment source redex result) : Step environment target redex result := by
  obtain ⟨witness,valid⟩ := stepped
  exact ⟨witness.mapRules translation.indices, stepValid_mapRules translation environment redex inside valid⟩

#print axioms stepValid_mapRules
#print axioms premisesValid_mapRules
#print axioms step_mapRules

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
