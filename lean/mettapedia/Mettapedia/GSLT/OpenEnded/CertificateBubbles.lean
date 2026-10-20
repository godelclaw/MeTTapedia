import Mettapedia.GSLT.LanguageDef.CertificateGSLTAmbient
import Mettapedia.GSLT.LanguageDef.CertificateGSLT
import Mettapedia.GSLT.LanguageDef.InferenceRuleSupport
import Mettapedia.GSLT.OpenEnded.RuleTables
import Mettapedia.Util.LinearHash

/-!
# Bubbles of validated certificate-GSLT definitions

This file places the least-sufficient-bubble question inside the existing
category of validated calculus definitions and strict rule-retaining arrows
(`CertificateGSLT.RuleRetaining`).

* **Bubbles are validated sub-presentations.** Restricting a validated
  definition to a list of rule identifiers is again validated
  (`restrictRules_isValid`), and the restriction has a strict arrow into the
  source (`bubbleArrow`). Restrictions are monotone in the identifiers
  (`bubble_mono`).
* **The checker sees rule tables.** Strict arrows are exactly the order of the
  definitions' rule tables (`refines_iff_tableOf_le`); a definition's table is
  finite (`finTableOf`); derivability of a definition is derivability over its
  table for the definition-independent rule-application relation
  (`nonempty_derivation_iff_derives`); a bubble's table is the restriction of
  the source table (`tableOf_bubble`); and every finite stage below a
  definition is the table of one of its validated bubbles (`stage_is_bubble`).
* **The top of a growing family of definitions.** A directed family of
  validated definitions generates an ideal of finite stages (`growthIdeal`).
  Its realized table is the least upper bound of the family's tables
  (`le_realize_growth`, `realize_growth_le`). A judgment derivable over that
  top is derivable in one definition of the family (`growth_derives_iff`).
  When the realized table has infinite support, no validated definition bounds
  the family (`no_definition_bound_of_infinite_support`): such a top is a point
  of the completion and not a validated definition.
* **Sufficiency is carried by derivation supports.** A bubble containing the
  rule support of one derivation is sufficient (`sufficient_of_support`), and
  every derivation in a bubble uses only the bubble's identifiers
  (`support_of_sufficient`).
* **No least sufficient bubble in general.** The existing two-route fixture
  (one judgment, a direct rule and a two-rule detour) has two sufficient
  bubbles, `[direct]` and `[via-axiom, via-step]` (`direct_sufficient`,
  `detour_sufficient`), each minimal (`direct_minimal`, `detour_minimal`),
  whose meet derives nothing (`meet_insufficient`). Hence no least sufficient
  bubble exists (`no_least_sufficient_bubble`).
* **Inclusion and cost disagree.** Every derivation of the judgment in the
  detour bubble has size at least two (`detour_derivation_size`), while the
  whole definition, which strictly contains the detour bubble, has a
  derivation of size one (`cost_inclusion_disagree`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.CertificateBubbles

open Set
open Order
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.OpenEnded.RuleTables
open Mettapedia.GSLT.OpenEnded.RuleTables.Table

/-! ## Validated restrictions -/

/-- **Restricting the rule table keeps a definition validated.** -/
theorem restrictRules_isValid {definition : CalculusLanguageDef}
    (valid : definition.isValid = true) (ids : List RuleId) :
    (Ambient.restrictRules definition ids).isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  obtain ⟨⟨⟨⟨⟨language, locally⟩, distinct⟩, signature⟩, rulesValid⟩, conversion⟩ := valid
  refine ⟨⟨⟨⟨⟨language, ?_⟩, ?_⟩, signature⟩, ?_⟩, conversion⟩
  · rw [List.all_eq_true] at locally ⊢
    intro rule member
    exact locally rule (List.mem_of_mem_filter member)
  · have nodup := (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mp distinct
    exact (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr
      (nodup.sublist ((List.filter_sublist).map _))
  · rw [List.all_eq_true] at rulesValid ⊢
    intro rule member
    exact rulesValid rule (List.mem_of_mem_filter member)

/-- The bubble of a validated definition at a list of rule identifiers. -/
def bubble (definition : ValidatedCalculusLanguageDef) (ids : List RuleId) :
    ValidatedCalculusLanguageDef :=
  ⟨Ambient.restrictRules definition.1 ids, restrictRules_isValid definition.2 ids⟩

theorem bubble_lookup_of_mem {definition : ValidatedCalculusLanguageDef} {ids : List RuleId}
    {id : RuleId} (member : ids.contains id = true) :
    (bubble definition ids).1.lookupRule? id = definition.1.lookupRule? id :=
  Ambient.lookupRule?_restrictRules ids member

theorem bubble_lookup_of_not_mem {definition : ValidatedCalculusLanguageDef}
    {ids : List RuleId} {id : RuleId} (absent : ids.contains id = false) :
    (bubble definition ids).1.lookupRule? id = none := by
  unfold CalculusLanguageDef.lookupRule?
  rw [List.find?_eq_none]
  intro rule member same
  have kept := (List.mem_filter.mp
    (show rule ∈ definition.1.rules.filter (fun rule => ids.contains rule.id) from member)).2
  have equal : rule.id = id := of_decide_eq_true same
  rw [equal, absent] at kept
  cases kept

theorem bubble_refines (definition : ValidatedCalculusLanguageDef) (ids : List RuleId) :
    RuleLookupRefines (bubble definition ids) definition := by
  intro id rule found
  cases inIds : ids.contains id
  · rw [bubble_lookup_of_not_mem inIds] at found
    cases found
  · rwa [bubble_lookup_of_mem inIds] at found

theorem bubble_mono (definition : ValidatedCalculusLanguageDef) {ids ids' : List RuleId}
    (included : ∀ id, ids.contains id = true → ids'.contains id = true) :
    RuleLookupRefines (bubble definition ids) (bubble definition ids') := by
  intro id rule found
  cases inIds : ids.contains id
  · rw [bubble_lookup_of_not_mem inIds] at found
    cases found
  · rw [bubble_lookup_of_mem inIds] at found
    rw [bubble_lookup_of_mem (included id inIds)]
    exact found

/-- The strict certificate-GSLT arrow from a bubble into its source. -/
def bubbleArrow (definition : ValidatedCalculusLanguageDef) (ids : List RuleId) :
    RuleRetaining.ofDefinition (bubble definition ids) ⟶ RuleRetaining.ofDefinition definition :=
  ⟨bubble_refines definition ids⟩

/-! ## Rule tables of definitions -/

/-- The rule table a checker consults. -/
def tableOf (definition : ValidatedCalculusLanguageDef) : Table RuleId RuleSchema :=
  ⟨definition.1.lookupRule?⟩

theorem refines_iff_tableOf_le {source target : ValidatedCalculusLanguageDef} :
    RuleLookupRefines source target ↔ tableOf source ≤ tableOf target :=
  Iff.rfl

theorem tableOf_support_finite (definition : ValidatedCalculusLanguageDef) :
    (tableOf definition).support.Finite := by
  apply (List.finite_toSet (definition.1.rules.map (·.id))).subset
  intro id member
  change (definition.1.lookupRule? id).isSome at member
  obtain ⟨rule, found⟩ := Option.isSome_iff_exists.mp member
  unfold CalculusLanguageDef.lookupRule? at found
  have same : rule.id = id :=
    of_decide_eq_true (List.find?_some (p := fun candidate : RuleSchema => decide (candidate.id = id)) found)
  change id ∈ definition.1.rules.map (·.id)
  exact List.mem_map.mpr ⟨rule, List.mem_of_find?_eq_some found, same⟩

/-- A validated definition as a finite stage. -/
def finTableOf (definition : ValidatedCalculusLanguageDef) : FinTable RuleId RuleSchema :=
  ⟨tableOf definition, tableOf_support_finite definition⟩

theorem tableOf_bubble (definition : ValidatedCalculusLanguageDef) (ids : List RuleId) :
    tableOf (bubble definition ids) =
      (tableOf definition).restrictTo {id | ids.contains id = true} := by
  ext : 1
  funext id
  by_cases member : ids.contains id = true
  · rw [restrictTo_lookup_of_mem _ (show id ∈ {id | ids.contains id = true} from member)]
    exact bubble_lookup_of_mem member
  · rw [restrictTo_lookup_of_not_mem _ (show id ∉ {id | ids.contains id = true} from member)]
    exact bubble_lookup_of_not_mem (Bool.eq_false_iff.mpr member)

/-- **Every finite stage below a definition is one of its validated bubbles.** -/
theorem stage_is_bubble {definition : ValidatedCalculusLanguageDef}
    (stage : FinTable RuleId RuleSchema) (le : stage.1 ≤ tableOf definition) :
    tableOf (bubble definition stage.2.toFinset.toList) = stage.1 := by
  rw [tableOf_bubble]
  have same : {id | stage.2.toFinset.toList.contains id = true} = stage.1.support := by
    ext id
    simp
  rw [same]
  exact restrictTo_support_of_le le

/-- The rule-application relation, which does not depend on the definition. -/
def certInstance (rule : RuleSchema) (premises : List Pattern) (conclusion : Pattern) : Prop :=
  ∃ arguments : List Pattern, argumentsValidAt rule.metavariables arguments = true ∧
    RuleSchema.sideConditionsHold rule arguments = true ∧
    InstantiatesList rule.metavariables arguments rule.premises premises ∧
    Instantiates rule.metavariables arguments rule.conclusion conclusion

private theorem derivationList_of_forall {definition : ValidatedCalculusLanguageDef} :
    ∀ premises : List Pattern, (∀ p ∈ premises, Nonempty (Derivation definition p)) →
      Nonempty (DerivationList definition premises)
  | [], _ => ⟨.nil⟩
  | head :: tail, derivable => by
      obtain ⟨headDerivation⟩ := derivable head (List.mem_cons_self ..)
      obtain ⟨tailDerivations⟩ :=
        derivationList_of_forall tail (fun p member => derivable p (List.mem_cons_of_mem _ member))
      exact ⟨.cons headDerivation tailDerivations⟩

/-- **Derivability of a definition is derivability over its rule table.** -/
theorem nonempty_derivation_iff_derives (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔ Derives certInstance (tableOf definition) goal := by
  constructor
  · rintro ⟨derivation⟩
    refine Derivation.sound_of_ruleApplications
      (meaning := Derives certInstance (tableOf definition)) ?_ derivation
    intro ruleInstance premises conclusion application premisesDerive
    cases application with
    | intro rule lookup arguments sideConditions premisesInstantiate conclusionInstantiates =>
        exact .byRule ruleInstance.ruleId rule premises lookup
          ⟨ruleInstance.arguments, arguments, sideConditions, premisesInstantiate,
            conclusionInstantiates⟩ premisesDerive
  · intro derives
    induction derives with
    | byRule i rule premises lookup instance_ _ ih =>
        obtain ⟨arguments, valid, sideConditions, premisesInstantiate, conclusionInstantiates⟩ :=
          instance_
        obtain ⟨children⟩ := derivationList_of_forall premises ih
        exact ⟨.byRule ⟨i, arguments⟩
          (.intro rule lookup valid sideConditions premisesInstantiate conclusionInstantiates)
          children⟩

/-! ## The top of a growing family of definitions -/

section Growth

variable {ι : Type} (family : ι → ValidatedCalculusLanguageDef)

/-- The finite stages lying below some definition of the family. -/
noncomputable def growthIdeal [Nonempty ι]
    (directed : ∀ first second, ∃ upper,
      RuleLookupRefines (family first) (family upper) ∧
        RuleLookupRefines (family second) (family upper)) :
    Ideal (FinTable RuleId RuleSchema) where
  carrier := {stage | ∃ k, stage.1 ≤ tableOf (family k)}
  lower' := by
    rintro first second below ⟨k, firstBelow⟩
    exact ⟨k, le_trans (show second.1 ≤ first.1 from below) firstBelow⟩
  nonempty' := by
    obtain ⟨k⟩ := ‹Nonempty ι›
    exact ⟨finTableOf (family k), k, le_rfl⟩
  directed' := by
    rintro first ⟨k, firstBelow⟩ second ⟨k', secondBelow⟩
    obtain ⟨upper, kUpper, k'Upper⟩ := directed k k'
    have finite : (first.1.support ∪ second.1.support).Finite := first.2.union second.2
    refine ⟨finRestrict (tableOf (family upper)) finite, ⟨upper, restrictTo_le _ _⟩, ?_, ?_⟩
    · intro i r found
      have inSupport : i ∈ first.1.support ∪ second.1.support :=
        Or.inl (by change (first.1.lookup i).isSome; rw [found]; rfl)
      change ((tableOf (family upper)).restrictTo _).lookup i = some r
      rw [restrictTo_lookup_of_mem _ inSupport]
      exact kUpper i r (firstBelow i r found)
    · intro i r found
      have inSupport : i ∈ first.1.support ∪ second.1.support :=
        Or.inr (by change (second.1.lookup i).isSome; rw [found]; rfl)
      change ((tableOf (family upper)).restrictTo _).lookup i = some r
      rw [restrictTo_lookup_of_mem _ inSupport]
      exact k'Upper i r (secondBelow i r found)

variable [Nonempty ι]
  (directed : ∀ first second, ∃ upper,
    RuleLookupRefines (family first) (family upper) ∧
      RuleLookupRefines (family second) (family upper))

/-- Every definition of the family lies below the realized top. -/
theorem le_realize_growth (k : ι) :
    tableOf (family k) ≤ realize (growthIdeal family directed) :=
  stage_le_realize (stage := finTableOf (family k)) ⟨k, le_rfl⟩

/-- **The realized top is the least upper bound of the family's tables.** -/
theorem realize_growth_le {upper : Table RuleId RuleSchema}
    (bounds : ∀ k, tableOf (family k) ≤ upper) :
    realize (growthIdeal family directed) ≤ upper := by
  intro i r found
  obtain ⟨stage, ⟨k, below⟩, foundStage⟩ := realize_lookup_eq_some found
  exact bounds k i r (below i r foundStage)

/-- **Compactness for certificate growth.** A judgment is derivable over the
realized top exactly when one definition of the family derives it. -/
theorem growth_derives_iff (goal : Pattern) :
    Derives certInstance (realize (growthIdeal family directed)) goal ↔
      ∃ k, Nonempty (Derivation (family k) goal) := by
  rw [derives_realize_iff]
  constructor
  · rintro ⟨stage, ⟨k, below⟩, derivation⟩
    exact ⟨k, (nonempty_derivation_iff_derives _ _).mpr (derives_mono below derivation)⟩
  · rintro ⟨k, derivation⟩
    exact ⟨finTableOf (family k), ⟨k, le_rfl⟩,
      (nonempty_derivation_iff_derives _ _).mp derivation⟩

/-- **An unbounded growth has no bound among validated definitions.** -/
theorem no_definition_bound_of_infinite_support
    (infinite : (realize (growthIdeal family directed)).support.Infinite) :
    ¬ ∃ bound : ValidatedCalculusLanguageDef, ∀ k, RuleLookupRefines (family k) bound := by
  rintro ⟨bound, bounds⟩
  have below := realize_growth_le family directed (upper := tableOf bound) bounds
  exact infinite ((tableOf_support_finite bound).subset (support_mono below))

end Growth

/-! ## Sufficiency and derivation supports -/

open Mettapedia.GSLT.LanguageDef.InferenceRuleSupport

/-- A bubble is sufficient for a goal when it derives the goal. -/
def Sufficient (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (ids : List RuleId) : Prop :=
  Nonempty (Derivation (bubble definition ids) goal)

theorem sufficient_mono {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    {ids ids' : List RuleId} (included : ∀ id, ids.contains id = true → ids'.contains id = true)
    (sufficient : Sufficient definition goal ids) : Sufficient definition goal ids' := by
  obtain ⟨derivation⟩ := sufficient
  exact ⟨derivation.transport (bubble_mono definition included)⟩

/-- **A bubble containing the rule support of one derivation is sufficient.** -/
theorem sufficient_of_support {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) {ids : List RuleId}
    (covers : ∀ id ∈ ruleSupport derivation.erase, ids.contains id = true) :
    Sufficient definition goal ids := by
  have agree : Agreement definition (bubble definition ids) (ruleSupport derivation.erase) :=
    fun id member => bubble_lookup_of_mem (covers id member)
  have accepted : checkRaw (bubble definition ids) goal derivation.erase = true := by
    rw [checkRaw_eq_of_agreement goal derivation.erase agree]
    exact checkRaw_erase derivation
  exact checkRaw_soundness accepted

mutual

private theorem derivation_support_found {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → (derivation : Derivation definition goal) →
      ∀ id ∈ ruleSupport derivation.erase, (definition.1.lookupRule? id).isSome
  | _, .byRule ruleInstance application children => by
      intro id member
      simp only [Derivation.erase, ruleSupport] at member
      rcases List.mem_cons.mp member with same | inChildren
      · subst same
        cases application with
        | intro rule lookup _ _ _ _ => rw [lookup]; rfl
      · exact derivationList_support_found children id inChildren

private theorem derivationList_support_found {definition : ValidatedCalculusLanguageDef} :
    {premises : List Pattern} → (derivations : DerivationList definition premises) →
      ∀ id ∈ childrenSupport derivations.erase, (definition.1.lookupRule? id).isSome
  | _, .nil => by
      intro id member
      simp [DerivationList.erase, childrenSupport] at member
  | _, .cons head tail => by
      intro id member
      simp only [DerivationList.erase, childrenSupport, List.mem_append] at member
      rcases member with inHead | inTail
      · exact derivation_support_found head id inHead
      · exact derivationList_support_found tail id inTail

end

/-- **Every derivation in a bubble is a derivation of the source whose rule
support lies inside the bubble.** -/
theorem support_of_sufficient {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    {ids : List RuleId} (sufficient : Sufficient definition goal ids) :
    ∃ derivation : Derivation definition goal,
      ∀ id ∈ ruleSupport derivation.erase, ids.contains id = true := by
  obtain ⟨inBubble⟩ := sufficient
  refine ⟨inBubble.transport (bubble_refines definition ids), fun id member => ?_⟩
  rw [Derivation.erase_transport] at member
  have found := derivation_support_found inBubble id member
  by_contra absent
  rw [bubble_lookup_of_not_mem (Bool.eq_false_iff.mpr absent)] at found
  cases found

/-! ## The two-route fixture: no least sufficient bubble -/

section TwoRoutes

/-- The existing fixture: one judgment with a direct rule and a two-rule detour. -/
abbrev routes : ValidatedCalculusLanguageDef := Ambient.ambientValidated

def directId : RuleId := ⟨"amb-direct"⟩
def axiomId : RuleId := ⟨"amb-via-axiom"⟩
def stepId : RuleId := ⟨"amb-via-step"⟩

/-- The judgment both routes derive. -/
abbrev goal : Pattern := Ambient.goalJ Ambient.target

/-- The intermediate judgment of the detour. -/
def middleGoal : Pattern := Ambient.goalJ (.apply "amb-middle" [])

theorem routes_rule_ids :
    ∀ rule ∈ routes.1.rules, rule.id = directId ∨ rule.id = axiomId ∨ rule.id = stepId := by
  decide

theorem routes_lookup_ids {id : RuleId} {rule : RuleSchema}
    (found : routes.1.lookupRule? id = some rule) :
    id = directId ∨ id = axiomId ∨ id = stepId := by
  unfold CalculusLanguageDef.lookupRule? at found
  have same : rule.id = id :=
    of_decide_eq_true (List.find?_some (p := fun candidate : RuleSchema => decide (candidate.id = id)) found)
  rw [← same]
  exact routes_rule_ids rule (List.mem_of_find?_eq_some found)

theorem routes_ground {id : RuleId} {rule : RuleSchema}
    (found : routes.1.lookupRule? id = some rule) : rule.metavariables = [] := by
  rcases routes_lookup_ids found with rfl | rfl | rfl <;>
  · revert found
    decide +revert

theorem direct_instantiates :
    instantiateRule? routes ⟨directId, []⟩ = some ([], goal) := by
  decide +kernel

theorem axiom_instantiates :
    instantiateRule? routes ⟨axiomId, []⟩ = some ([], middleGoal) := by
  decide +kernel

theorem step_instantiates :
    instantiateRule? routes ⟨stepId, []⟩ = some ([middleGoal], goal) := by
  decide +kernel

/-- What a rule application in any bubble of the fixture can be. -/
theorem bubble_application_cases {ids : List RuleId} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication (bubble routes ids) ruleInstance premises conclusion) :
    (ids.contains directId = true ∧ premises = [] ∧ conclusion = goal) ∨
      (ids.contains axiomId = true ∧ premises = [] ∧ conclusion = middleGoal) ∨
      (ids.contains stepId = true ∧ premises = [middleGoal] ∧ conclusion = goal) := by
  have computed := instantiateRule?_eq_some_iff_application.mpr application
  obtain ⟨rule, lookup, valid, _, _, _⟩ := application
  have inIds : ids.contains ruleInstance.ruleId = true := by
    by_contra absent
    rw [bubble_lookup_of_not_mem (Bool.eq_false_iff.mpr absent)] at lookup
    cases lookup
  rw [bubble_lookup_of_mem inIds] at lookup
  have noArguments : ruleInstance.arguments = [] := by
    rw [routes_ground lookup] at valid
    cases arguments : ruleInstance.arguments with
    | nil => rfl
    | cons _ _ => rw [arguments] at valid; simp [argumentsValidAt] at valid
  have sameInstance : ruleInstance = ⟨ruleInstance.ruleId, []⟩ := by
    cases ruleInstance
    simp only at noArguments
    rw [noArguments]
  have agree := InferenceRuleSupport.instantiateRule_eq_of_lookup (source := routes)
    (target := bubble routes ids) ruleInstance (bubble_lookup_of_mem inIds)
  rw [agree, sameInstance] at computed
  rcases routes_lookup_ids lookup with same | same | same
  · rw [same] at computed inIds
    rw [direct_instantiates] at computed
    cases computed
    exact Or.inl ⟨inIds, rfl, rfl⟩
  · rw [same] at computed inIds
    rw [axiom_instantiates] at computed
    cases computed
    exact Or.inr (Or.inl ⟨inIds, rfl, rfl⟩)
  · rw [same] at computed inIds
    rw [step_instantiates] at computed
    cases computed
    exact Or.inr (Or.inr ⟨inIds, rfl, rfl⟩)

/-- The direct rule alone is sufficient. -/
theorem direct_sufficient : Sufficient routes goal [directId] := by
  refine sufficient_of_support Ambient.shortProof ?_
  intro id member
  have support : ruleSupport Ambient.shortProof.erase = [directId] := by decide +kernel
  rw [support] at member
  rw [List.mem_singleton.mp member]
  decide

/-- The detour alone is sufficient. -/
theorem detour_sufficient : Sufficient routes goal [axiomId, stepId] := by
  refine sufficient_of_support Ambient.longProof ?_
  intro id member
  have support : ruleSupport Ambient.longProof.erase = [stepId, axiomId] := by decide +kernel
  rw [support] at member
  rcases List.mem_cons.mp member with same | rest
  · rw [same]; decide
  · rw [List.mem_singleton.mp rest]; decide

/-- A bubble containing none of the fixture's rules derives nothing. -/
theorem nothing_derivable_of_disjoint {ids : List RuleId}
    (noDirect : ids.contains directId = false) (noAxiom : ids.contains axiomId = false)
    (noStep : ids.contains stepId = false) (pattern : Pattern) :
    ¬ Nonempty (Derivation (bubble routes ids) pattern) := by
  rintro ⟨derivation⟩
  refine Derivation.sound_of_ruleApplications (meaning := fun _ => False) ?_ derivation
  intro ruleInstance premises conclusion application _
  rcases bubble_application_cases application with ⟨inIds, _⟩ | ⟨inIds, _⟩ | ⟨inIds, _⟩
  · rw [noDirect] at inIds; cases inIds
  · rw [noAxiom] at inIds; cases inIds
  · rw [noStep] at inIds; cases inIds

/-- **The meet of the two sufficient bubbles is insufficient.** -/
theorem meet_insufficient : ¬ Sufficient routes goal [] :=
  nothing_derivable_of_disjoint rfl rfl rfl goal

/-- Without the detour's axiom, nothing is derivable: every remaining rule
application needs a premise. -/
theorem nothing_derivable_without_detour_start {ids : List RuleId}
    (noDirect : ids.contains directId = false) (noAxiom : ids.contains axiomId = false)
    (pattern : Pattern) : ¬ Nonempty (Derivation (bubble routes ids) pattern) := by
  rintro ⟨derivation⟩
  refine Derivation.sound_of_ruleApplications (meaning := fun _ => False) ?_ derivation
  intro ruleInstance premises conclusion application premisesHold
  rcases bubble_application_cases application with
    ⟨inIds, _⟩ | ⟨inIds, _⟩ | ⟨_, rfl, _⟩
  · rw [noDirect] at inIds; cases inIds
  · rw [noAxiom] at inIds; cases inIds
  · exact premisesHold middleGoal (List.mem_singleton_self _)

theorem goal_ne_middleGoal : goal ≠ middleGoal := by decide

/-- Without the detour's step, the goal is not derivable: the remaining rule
only concludes the intermediate judgment. -/
theorem goal_not_derivable_without_step {ids : List RuleId}
    (noDirect : ids.contains directId = false) (noStep : ids.contains stepId = false) :
    ¬ Nonempty (Derivation (bubble routes ids) goal) := by
  rintro ⟨derivation⟩
  refine Derivation.sound_of_ruleApplications (meaning := fun pattern => pattern ≠ goal) ?_
    derivation rfl
  intro ruleInstance premises conclusion application _
  rcases bubble_application_cases application with
    ⟨inIds, _⟩ | ⟨_, _, rfl⟩ | ⟨inIds, _⟩
  · rw [noDirect] at inIds; cases inIds
  · exact goal_ne_middleGoal.symm
  · rw [noStep] at inIds; cases inIds

/-- **The direct bubble is minimal.** -/
theorem direct_minimal {ids : List RuleId}
    (within : ∀ id, ids.contains id = true → [directId].contains id = true)
    (sufficient : Sufficient routes goal ids) : ids.contains directId = true := by
  by_contra absent
  have noAxiom : ids.contains axiomId = false := by
    by_contra present
    have inside := within axiomId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  have noStep : ids.contains stepId = false := by
    by_contra present
    have inside := within stepId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  exact nothing_derivable_of_disjoint (Bool.eq_false_iff.mpr absent) noAxiom noStep goal sufficient

/-- **The detour bubble is minimal.** -/
theorem detour_minimal {ids : List RuleId}
    (within : ∀ id, ids.contains id = true → [axiomId, stepId].contains id = true)
    (sufficient : Sufficient routes goal ids) :
    ids.contains axiomId = true ∧ ids.contains stepId = true := by
  have noDirect : ids.contains directId = false := by
    by_contra present
    have inside := within directId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  constructor
  · by_contra absent
    exact nothing_derivable_without_detour_start noDirect (Bool.eq_false_iff.mpr absent) goal sufficient
  · by_contra absent
    exact goal_not_derivable_without_step noDirect (Bool.eq_false_iff.mpr absent) sufficient

/-- **No least sufficient bubble.** No bubble of the fixture is sufficient and
contained in every sufficient bubble. -/
theorem no_least_sufficient_bubble :
    ¬ ∃ least : List RuleId, Sufficient routes goal least ∧
      ∀ ids, Sufficient routes goal ids →
        ∀ id, least.contains id = true → ids.contains id = true := by
  rintro ⟨least, sufficient, smallest⟩
  have inDirect := smallest _ direct_sufficient
  have inDetour := smallest _ detour_sufficient
  have noDirect : least.contains directId = false := by
    by_contra present
    have inside := inDetour directId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  have noAxiom : least.contains axiomId = false := by
    by_contra present
    have inside := inDirect axiomId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  have noStep : least.contains stepId = false := by
    by_contra present
    have inside := inDirect stepId (Bool.not_eq_false _ ▸ present)
    revert inside
    decide
  exact nothing_derivable_of_disjoint noDirect noAxiom noStep goal sufficient

/-! ### Monos are not conservative extensions -/

/-- Every strict arrow is a monomorphism: the category is thin. -/
theorem bubbleArrow_mono (ids : List RuleId) :
    CategoryTheory.Mono (bubbleArrow routes ids) :=
  ⟨fun _ _ _ => RuleRetaining.hom_ext _ _⟩

/-- The intermediate judgment is derivable in the whole fixture. -/
theorem middleGoal_derivable : Nonempty (Derivation routes middleGoal) :=
  ⟨.byRule ⟨axiomId, []⟩ (instantiateRule?_eq_some_iff_application.mp axiom_instantiates) .nil⟩

/-- The direct bubble does not derive the intermediate judgment. -/
theorem middleGoal_not_in_direct : ¬ Nonempty (Derivation (bubble routes [directId]) middleGoal) := by
  rintro ⟨derivation⟩
  refine Derivation.sound_of_ruleApplications (meaning := fun pattern => pattern ≠ middleGoal) ?_
    derivation rfl
  intro ruleInstance premises conclusion application _
  rcases bubble_application_cases application with
    ⟨_, _, rfl⟩ | ⟨inIds, _⟩ | ⟨inIds, _⟩
  · exact goal_ne_middleGoal
  · exact absurd inIds (by decide)
  · exact absurd inIds (by decide)

/-- **A mono need not be conservative.** The arrow from the direct bubble into
the fixture is a monomorphism, yet the fixture derives a judgment of the
bubble's own vocabulary that the bubble does not: conservativity is a property
relative to a class of judgments, not a shape of arrow. -/
theorem mono_not_conservative :
    CategoryTheory.Mono (bubbleArrow routes [directId]) ∧
      Nonempty (Derivation routes middleGoal) ∧
      ¬ Nonempty (Derivation (bubble routes [directId]) middleGoal) :=
  ⟨bubbleArrow_mono _, middleGoal_derivable, middleGoal_not_in_direct⟩

/-! ### Inclusion order against cost order -/

open Ambient

theorem derivationSize_pos {definition : ValidatedCalculusLanguageDef} {pattern : Pattern}
    (derivation : Derivation definition pattern) : 1 ≤ derivationSize derivation := by
  cases derivation with
  | byRule _ _ children => simp [derivationSize]

/-- **Every derivation of the goal in the detour bubble has size at least
two.** -/
theorem detour_derivation_size (derivation : Derivation (bubble routes [axiomId, stepId]) goal) :
    2 ≤ derivationSize derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      rcases bubble_application_cases application with
        ⟨inIds, _⟩ | ⟨_, _, same⟩ | ⟨_, rfl, _⟩
      · exact absurd inIds (by decide)
      · exact absurd same goal_ne_middleGoal
      · cases children with
        | cons head tail =>
            cases tail with
            | nil =>
                have headPositive := derivationSize_pos head
                simp only [derivationSize, derivationListSize]
                omega

/-- **Inclusion and cost disagree.** The detour bubble is a strict
sub-presentation of the whole definition, yet the whole definition checks the
goal with a strictly smaller certificate. -/
theorem cost_inclusion_disagree :
    RuleLookupRefines (bubble routes [axiomId, stepId]) routes ∧
      ¬ RuleLookupRefines routes (bubble routes [axiomId, stepId]) ∧
      (∀ derivation : Derivation (bubble routes [axiomId, stepId]) goal,
        2 ≤ derivationSize derivation) ∧
      derivationSize shortProof = 1 := by
  refine ⟨bubble_refines routes _, ?_, detour_derivation_size, rfl⟩
  intro refines
  cases lookup : routes.1.lookupRule? directId with
  | none =>
      revert lookup
      decide
  | some rule =>
      have retained := refines directId rule lookup
      rw [bubble_lookup_of_not_mem (by decide)] at retained
      cases retained

end TwoRoutes

#print axioms restrictRules_isValid
#print axioms bubble_refines
#print axioms tableOf_bubble
#print axioms stage_is_bubble
#print axioms nonempty_derivation_iff_derives
#print axioms realize_growth_le
#print axioms growth_derives_iff
#print axioms no_definition_bound_of_infinite_support
#print axioms sufficient_of_support
#print axioms support_of_sufficient
#print axioms direct_sufficient
#print axioms detour_sufficient
#print axioms meet_insufficient
#print axioms direct_minimal
#print axioms detour_minimal
#print axioms no_least_sufficient_bubble
#print axioms mono_not_conservative
#print axioms detour_derivation_size
#print axioms cost_inclusion_disagree

end Mettapedia.GSLT.OpenEnded.CertificateBubbles
