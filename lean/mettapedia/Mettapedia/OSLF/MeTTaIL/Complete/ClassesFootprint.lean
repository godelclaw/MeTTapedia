import Mettapedia.OSLF.MeTTaIL.Complete.Classes
import Mettapedia.OSLF.MeTTaIL.Complete.DeepFootprint
import Mettapedia.OSLF.Framework.DisplayedContextProfile

/-!
# The search modulo equations stays within the declared names

A footprint that lists every declared free name covers every well-sorted term: a sorted object
pattern mentions only declared names. Rule jobs, equation lanes and their premise searches start
from well-sorted sources, and every member the search discovers is well sorted (a forward target
passes the sort check, a backward candidate has lanes only when it is sorted). So every lane of
every reached state stays within the footprint, and the table restricted to the footprint is the
plan's free-type context itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Footprint

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise GeneralExecutionAdmission ScopedRuleMatching RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open StructuralDescent.Scheduled (Goal Result)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)

/-- The footprint lists every declared free name. -/
def Declared : Prop := ∀ name type, plan.snapshot.free name = some type → name ∈ footprint

/-- What a search needs of the plan and the footprint. -/
structure Scope : Prop where
  declared : Declared plan footprint
  finite : plan.snapshot.provider.dynamicRelations = []
  provider : ∀ name ∈ providerFreeNames plan.snapshot.provider, name ∈ footprint
  admitted : ∀ equation ∈ plan.equations, admittedFor equation.rule equation.binding.spec = true

variable {plan bound expected footprint}

theorem full_table (declared : Declared plan footprint) :
    FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint) = plan.snapshot.free := by
  funext name
  rw [FreeTypeContext.ofList_entriesOn]
  by_cases member : name ∈ footprint
  · rw [if_pos member]
  · rw [if_neg member]
    cases found : plan.snapshot.free name with
    | none => rfl
    | some type => exact absurd (declared name type found) member

theorem sorted_within (declared : Declared plan footprint) {language : LanguageDef} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (checked : checkOpenPatternWellSorted language plan.snapshot.free bound type pattern = true) :
    ∀ name ∈ pattern.freeFvarNames, name ∈ footprint := by
  intro name member
  have sound := Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound checked
  obtain ⟨type, found⟩ :=
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType.freeType_of_mem_freeFvarNames_of_isObjectPattern sound.1
      sound.2.2.1 member
  exact declared name type found

theorem fill_within {context : DerivedContexts.OneHoleContext} {focus : Pattern}
    (outside : ∀ name ∈ Mettapedia.OSLF.Framework.DisplayedContextProfile.externalFreeFvarNames context,
      name ∈ footprint)
    (inside : ∀ name ∈ focus.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ (context.fill focus).freeFvarNames, name ∈ footprint := by
  intro name member
  rcases (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mp member with
    out | ins
  · exact outside name out
  · exact inside name ins

theorem context_within {language : LanguageDef} {free : FreeTypeContext} {permissions : GeneralTypedSites.OperationalPermissions}
    {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed language free permissions bound expected
      source site)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ Mettapedia.OSLF.Framework.DisplayedContextProfile.externalFreeFvarNames site.context,
      name ∈ footprint := by
  intro name member
  apply covered
  rw [← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq licensed]
  exact (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mpr (.inl member)

theorem focus_within {language : LanguageDef} {free : FreeTypeContext} {permissions : GeneralTypedSites.OperationalPermissions}
    {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed language free permissions bound expected
      source site)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ site.focus.freeFvarNames, name ∈ footprint := by
  intro name member
  apply covered
  rw [← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq licensed]
  exact (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mpr (.inr member)

theorem erase_within {pattern : Pattern} (covered : ∀ name ∈ pattern.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ pattern.eraseBinderMetadata.freeFvarNames, name ∈ footprint := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.eraseBinderMetadata, Pattern.freeFvarNames]
  | hfvar name => simpa [Pattern.eraseBinderMetadata, Pattern.freeFvarNames] using covered
  | happly label arguments ih =>
    simp only [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, List.mem_flatMap, List.mem_map] at covered ⊢
    rintro name ⟨_, ⟨argument, member, rfl⟩, inside⟩
    exact ih argument member (fun other occurs => covered other ⟨argument, member, occurs⟩) name inside
  | hlambda binder body ih =>
    simpa [Pattern.eraseBinderMetadata, Pattern.freeFvarNames] using
      ih (by simpa [Pattern.freeFvarNames] using covered)
  | hmultiLambda arity binders body ih =>
    simpa [Pattern.eraseBinderMetadata, Pattern.freeFvarNames] using
      ih (by simpa [Pattern.freeFvarNames] using covered)
  | hsubst body replacement bodyIH replacementIH =>
    simp only [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, List.mem_append] at covered ⊢
    rintro name (inside | inside)
    · exact bodyIH (fun other occurs => covered other (.inl occurs)) name inside
    · exact replacementIH (fun other occurs => covered other (.inr occurs)) name inside
  | hcollection kind elements rest ih =>
    simp only [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, List.mem_append, List.mem_flatMap,
      List.mem_map] at covered ⊢
    rintro name (⟨_, ⟨element, member, rfl⟩, inside⟩ | inside)
    · exact ih element member (fun other occurs => covered other (.inl ⟨element, member, occurs⟩)) name inside
    · exact covered name (.inr inside)

/-! ## Equation lanes -/

/-- An outcome's completed assignment stays within the footprint. -/
def OutcomeWithin (footprint : List String) (outcome : EquationJob.Outcome) : Prop :=
  assignmentFreeWithin footprint outcome.completed

theorem lane_source_within (declared : Declared plan footprint) {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) :
    ∀ name ∈ source.freeFvarNames, name ∈ footprint :=
  sorted_within declared ((EquationJob.mem_lanes plan bound expected).mp member).1

theorem lane_licensed {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) :
    GeneralEquationJobs.LicensedJob plan bound expected source lane.job :=
  (GeneralEquationJobs.jobs_iff plan bound expected source lane.job).mp
    ((EquationJob.mem_lanes plan bound expected).mp member).2.1

theorem lane_answer_within (declared : Declared plan footprint) {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) :
    assignmentFreeWithin footprint lane.answer.assignment := by
  have facts := (EquationJob.mem_lanes plan bound expected).mp member
  have focused := focus_within (lane_licensed member).2 (lane_source_within declared member)
  exact GeneralScopedMatchMachine.matcher_answer_free_within _ _
    (GeneralEquationJobExecution.finishMatcher_reachable .start) lane.answer facts.2.2.1 footprint
    (by intro entry inside; cases inside)
    (erase_within focused)

theorem lane_admitted (scope : Scope plan footprint) {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) :
    admittedFor lane.job.equation.rule lane.job.equation.binding.spec = true :=
  scope.admitted _ (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp (lane_licensed member).1))

/-- An equation lane's premise search stays within the footprint. -/
theorem lane_footprinted (scope : Scope plan footprint) {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) :
    Deep.Footprinted (EquationJob.family plan lane) footprint (OutcomeWithin footprint) where
  goals _ := ⟨lane_admitted scope member, lane_answer_within scope.declared member⟩
  reads result covered := by
    cases result with
    | premises completed events valid => exact covered.2
  provider := provider_coverage_mono _ footprint plan.snapshot.provider scope.provider
    (provider_covered_by_own_names plan.snapshot.provider)
  dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint _ scope.finite

theorem reduct_within (scope : Scope plan footprint) {source : Pattern} {lane : EquationJob.Lane}
    (member : lane ∈ EquationJob.lanes plan bound expected source) {completed : Assignment}
    (stored : assignmentFreeWithin footprint completed) {raw : Pattern}
    (reduced : reduct? lane.job.equation.rule lane.job.equation.binding.spec lane.job.site.focusBound.length completed =
      some raw) :
    ∀ name ∈ raw.freeFvarNames, name ∈ footprint :=
  admitted_instantiate_with_free_within footprint Substitution.instantiateBVar
    (Substitution.instantiate_bvar_free_within footprint) lane.job.equation.rule lane.job.equation.binding.spec
    (lane_admitted scope member) _ .right [] 0 completed lane.job.equation.rule.right raw stored reduced

theorem well_sorted_within (declared : Declared plan footprint) {language : LanguageDef} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language plan.snapshot.free bound type
      pattern) :
    ∀ name ∈ pattern.freeFvarNames, name ∈ footprint := by
  intro name member
  obtain ⟨type, found⟩ :=
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType.freeType_of_mem_freeFvarNames_of_isObjectPattern sorted.1
      sorted.2.2.1 member
  exact declared name type found

theorem lift_target_within (declared : Declared plan footprint) {lane : EquationJob.Lane}
    {outcome : EquationJob.Outcome} {receipt : GeneralEquationJobs.Receipt}
    (lifted : EquationJob.lift plan bound expected lane outcome = some receipt) :
    ∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint := by
  obtain ⟨_, _, raw, _, accepted, rfl⟩ := GeneralEquationJobs.finish_readout plan bound expected lane.job
    lane.answer.trace lane.answer.assignment outcome.completed outcome.history receipt lifted
  exact well_sorted_within declared accepted.2.2

/-! ## Rule jobs -/

/-- A firing's target, put back in the job's context, stays within the footprint. -/
def FiringWithin (footprint : List String) (job : GeneralRuleJobs.Job) (firing : DeepRoot.Firing) : Prop :=
  ∀ name ∈ (job.site.context.fill firing.target).freeFvarNames, name ∈ footprint

/-- A licensed rule job's search stays within the footprint. -/
theorem job_footprinted (scope : Scope plan footprint) {source : Pattern} {job : GeneralRuleJobs.Job}
    (licensed : job.Valid plan bound expected source) (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    Deep.Footprinted (Step.family plan job) footprint (FiringWithin footprint job) where
  goals _ := focus_within licensed.2 covered
  reads result inside := by
    cases result with
    | root trace captured completed events target valid =>
      exact fill_within (context_within licensed.2 covered) inside.2.2.2
  provider := provider_coverage_mono _ footprint plan.snapshot.provider scope.provider
    (provider_covered_by_own_names plan.snapshot.provider)
  dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint _ scope.finite

end Mettapedia.OSLF.MeTTaIL.Complete.Footprint
