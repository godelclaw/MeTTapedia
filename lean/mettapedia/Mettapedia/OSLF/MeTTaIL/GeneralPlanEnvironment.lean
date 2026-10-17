import Mettapedia.OSLF.MeTTaIL.GeneralLanguageTyping
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Operational environments retaining authored plan positions

Child execution uses the selected annotated declarations in their original
order. The selected execution index and the source declaration index are
separate; matching rule names or equal rule bodies never identifies them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

open Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

def environment (plan : Plan) : GeneralPremise.Environment where
  language := {plan.snapshot.language with rewrites := plan.rules.map RulePlan.rule}
  free := plan.snapshot.free
  provider := plan.snapshot.provider
  specifications := plan.rules.zipIdx.map fun (rule, index) => (index, rule.binding.spec)
  reflection := plan.permissions.reflection

theorem grammar (plan : Plan) : (environment plan).language.terms = plan.snapshot.language.terms := rfl

theorem typing_iff (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) :
    OpenPatternWellSorted (environment plan).language (environment plan).free bound type pattern ↔
      OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type pattern :=
  ⟨GeneralLanguageTyping.open_transport (grammar plan),
    GeneralLanguageTyping.open_transport (grammar plan).symm⟩

theorem selected_rule (plan : Plan) {ordinal : Nat} {rule : RulePlan}
    (position : plan.rules[ordinal]? = some rule) :
    (environment plan).language.rewrites[ordinal]? = some rule.rule := by
  simp only [environment, List.getElem?_map, position, Option.map_some]

private theorem find_unique {α : Type} (items : List α) (predicate : α → Bool) (chosen : α)
    (member : chosen ∈ items) (accepted : predicate chosen = true)
    (unique : ∀ item ∈ items, predicate item = true → item = chosen) :
    items.find? predicate = some chosen := by
  cases found : items.find? predicate with
  | none =>
      have rejected := List.find?_eq_none.mp found chosen member
      exact False.elim (rejected accepted)
  | some item =>
      have same := unique item (List.mem_of_find?_eq_some found) (List.find?_some found)
      cases same
      rfl

theorem selected_specification (plan : Plan) {ordinal : Nat} {rule : RulePlan}
    (position : plan.rules[ordinal]? = some rule) :
    GeneralPremise.specification? (environment plan) ordinal = some rule.binding.spec := by
  have member : (rule, ordinal) ∈ plan.rules.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr position
  have mapped : (ordinal, rule.binding.spec) ∈ (environment plan).specifications :=
    List.mem_map.mpr ⟨(rule, ordinal), member, rfl⟩
  have unique : ∀ item ∈ (environment plan).specifications,
      (item.1 == ordinal) = true → item = (ordinal, rule.binding.spec) := by
    intro item occurs accepted
    obtain ⟨⟨actual, index⟩, declared, same⟩ := List.mem_map.mp occurs
    cases same
    have indexSame : index = ordinal := by simpa only [beq_iff_eq] using accepted
    subst index
    have actualPosition := List.mk_mem_zipIdx_iff_getElem?.mp declared
    have actualSame : actual = rule := Option.some.inj (actualPosition.symm.trans position)
    subst actual
    rfl
  have found := find_unique (environment plan).specifications
    (fun entry => entry.1 == ordinal) (ordinal, rule.binding.spec) mapped (beq_self_eq_true _) unique
  simp only [GeneralPremise.specification?, found, Option.map_some]

/-- Install the independently specified primitive service for this plan. The
selected declarations, source occurrence indices and typing context are retained. -/
def environmentWith (plan : Plan) (dynamic : GeneralPremise.DynamicProvider) : GeneralPremise.Environment :=
  {environment plan with dynamic := dynamic}

@[simp] theorem environmentWith_empty (plan : Plan) :
    environmentWith plan GeneralPremise.DynamicProvider.empty = environment plan := rfl

@[simp] theorem environmentWith_language (plan : Plan) (dynamic : GeneralPremise.DynamicProvider) :
    (environmentWith plan dynamic).language = (environment plan).language := rfl

@[simp] theorem environmentWith_free (plan : Plan) (dynamic : GeneralPremise.DynamicProvider) :
    (environmentWith plan dynamic).free = plan.snapshot.free := rfl

@[simp] theorem environmentWith_provider (plan : Plan) (dynamic : GeneralPremise.DynamicProvider) :
    (environmentWith plan dynamic).provider = plan.snapshot.provider := rfl

@[simp] theorem environmentWith_dynamic (plan : Plan) (dynamic : GeneralPremise.DynamicProvider) :
    (environmentWith plan dynamic).dynamic = dynamic := rfl

theorem selected_rule_with (plan : Plan) (dynamic : GeneralPremise.DynamicProvider)
    {ordinal : Nat} {rule : RulePlan} (position : plan.rules[ordinal]? = some rule) :
    (environmentWith plan dynamic).language.rewrites[ordinal]? = some rule.rule :=
  selected_rule plan position

theorem selected_specification_with (plan : Plan) (dynamic : GeneralPremise.DynamicProvider)
    {ordinal : Nat} {rule : RulePlan} (position : plan.rules[ordinal]? = some rule) :
    GeneralPremise.specification? (environmentWith plan dynamic) ordinal = some rule.binding.spec :=
  selected_specification plan position

theorem compiled_environment (snapshot : Snapshot) (permissions : Permissions) :
    (environment (compile snapshot permissions)).language = executionLanguage snapshot permissions := rfl

end Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
