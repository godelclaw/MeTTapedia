import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! Existential views of the reference relation, exposing ordered premise
threading and the original child steps. The views preserve existence of the
actual witnesses and add no alternate evaluator or admission policy. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ReflectiveCanonical

variable (environment : RelationEnv) (language : LanguageDef)

theorem premises_nil_iff (sites : Pattern) (initial final : Bindings) :
    (∃ witnesses, PremisesValid environment language sites initial [] witnesses final) ↔
      initial = final := by
  constructor
  · rintro ⟨witnesses, valid⟩
    cases valid
    rfl
  · rintro rfl
    exact ⟨[], .nil _⟩

theorem premises_cons_iff (sites : Pattern) (initial final : Bindings)
    (premise : Premise) (premises : List Premise) :
    (∃ witnesses, PremisesValid environment language sites initial (premise :: premises) witnesses final) ↔
      ∃ middle, (∃ witness, PremiseValid environment language sites initial premise witness middle) ∧
        (∃ witnesses, PremisesValid environment language sites middle premises witnesses final) := by
  constructor
  · rintro ⟨witnesses, valid⟩
    cases valid with
    | cons first rest => exact ⟨_, ⟨_,first⟩, ⟨_,rest⟩⟩
  · rintro ⟨middle, ⟨first, firstValid⟩, ⟨rest, restValid⟩⟩
    exact ⟨first :: rest, .cons firstValid restValid⟩

theorem congruence_iff (sites : Pattern) (initial final : Bindings) (source target : Pattern) :
    (∃ witness, PremiseValid environment language sites initial (.congruence source target) witness final) ↔
      ∃ candidate matched,
        Step environment language
          (applyBindingsScoped sites initial (stepDepth sites (.congruence source target)) source) candidate ∧
        matched ∈ matchPattern target candidate ∧ mergeBindings initial matched = some final := by
  constructor
  · rintro ⟨witness, valid⟩
    cases valid with
    | base base _ => cases base
    | step endpoints child matched merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl,rfl⟩ := endpoints
      exact ⟨_,_,⟨_,child⟩,matched,merged⟩
  · rintro ⟨candidate, matched, ⟨child, childValid⟩, matchedValid, merged⟩
    exact ⟨.premiseStep child candidate matched final, .step rfl childValid matchedValid merged⟩

theorem step_rule_iff (source target : Pattern) :
    Step environment language source target ↔
      ∃ (index : Nat) (rule : RewriteRule), language.rewrites[index]? = some rule ∧
        ∃ initial, initial ∈ matchPattern rule.left source ∧
          ∃ final, (∃ witnesses, PremisesValid environment language (captureSites rule)
            initial rule.premises witnesses final) ∧
            applyBindingsScoped (captureSites rule) final 0 rule.right = target := by
  constructor
  · rintro ⟨witness, valid⟩
    cases valid with
    | rule found matched premises =>
      exact ⟨_,_,found,_,by simpa only [matchPatternForRule_eq_syntactic] using matched,
        _,⟨_,premises⟩,rfl⟩
  · rintro ⟨index, rule, found, initial, matched, final, ⟨witnesses,premises⟩, rfl⟩
    exact ⟨.rule index initial witnesses, .rule found
      (by simpa only [matchPatternForRule_eq_syntactic] using matched) premises⟩

#print axioms premises_nil_iff
#print axioms premises_cons_iff
#print axioms congruence_iff
#print axioms step_rule_iff

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
