import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariants
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.Complete.Presented

/-!
# Collection matching at authored typed occurrences

Requests extend the existing rule-job enumeration with its finite residual
context variants. The original occurrence and allocation history remain
available when the reconstructed match enters the original typed/premise
continuation and receipt constructor. This establishes source soundness;
whole-source coverage and profile admission are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching CanonicalBags GeneralTypedSites CollectionSelection
open Mettapedia.GSLT.LanguageDef WellSorted GeneralTypedOccurrence
open RecursiveCollectionHandoff

structure Job where
  origin : GeneralRuleJobs.Job
  variant : SiteVariant
  deriving Repr

def jobs (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : List Job :=
  (GeneralRuleJobs.jobs plan bound expected source).flatMap fun origin =>
    (siteVariants origin.site).map fun variant => ⟨origin, variant⟩

def Job.Valid (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (job : Job) : Prop :=
  job.origin.Valid plan bound expected source ∧ job.variant ∈ siteVariants job.origin.site

theorem jobs_exact (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (job : Job) :
    job ∈ jobs plan bound expected source ↔ job.Valid plan bound expected source := by
  constructor
  · intro present
    obtain ⟨origin, declared, mapped⟩ := List.mem_flatMap.mp present
    obtain ⟨variant, selected, same⟩ := List.mem_map.mp mapped
    cases same
    exact ⟨(GeneralRuleJobs.jobs_spec ..).mp declared, selected⟩
  · rintro ⟨declared, selected⟩
    exact List.mem_flatMap.mpr ⟨job.origin, (GeneralRuleJobs.jobs_spec ..).mpr declared,
      List.mem_map.mpr ⟨job.variant, selected, by cases job; rfl⟩⟩

def Job.request (job : Job) : RecursiveCollectionMachine.Request :=
  ⟨job.origin.declaration.rule, job.origin.declaration.binding.spec, job.variant.site.focusBound.length,
    .left, [], 0, [], job.origin.declaration.rule.left, job.variant.site.focus⟩

def Job.preparedJob (job : Job) (prepared : Prepared) : GeneralRuleJobs.Job :=
  { job.origin with site := refocus job.variant.site prepared.source }

def Job.presentedSource (job : Job) (prepared : Prepared) : Pattern :=
  job.variant.site.context.fill prepared.source

theorem Job.variant_licensed {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source) :
    Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free plan.permissions.sites
      bound expected (job.variant.site.context.fill job.variant.site.focus) job.variant.site :=
  siteVariants_licensed valid.1.2 valid.2

/-- The ordinary job retains the actual dependent occurrence and selected
declaration. Only its focused presentation changes. -/
theorem Job.prepared_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source) {answer : RecursiveCollectionMachine.Answer}
    {prepared : Prepared} (matching : prepared.Valid job.request answer) :
    (job.preparedJob prepared).Valid plan bound expected (job.presentedSource prepared) :=
  ⟨valid.1.1, refocus_licensed (Job.variant_licensed valid) matching.source⟩

theorem Job.source_same {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source) {answer : RecursiveCollectionMachine.Answer}
    {prepared : Prepared} (matching : prepared.Valid job.request answer) :
    Same source (job.presentedSource prepared) := by
  rw [← valid.1.2.source_eq]
  exact (siteVariants_source valid.2).trans (context_fill_same _ matching.source)

theorem Job.prepared_focus {job : Job} {prepared : Prepared} :
    (job.preparedJob prepared).site.focus = prepared.source ∧
      (job.preparedJob prepared).site.focusBound = job.variant.site.focusBound ∧
      (job.preparedJob prepared).site.focusType = job.variant.site.focusType ∧
      (job.preparedJob prepared).site.typingFrames = job.variant.site.typingFrames ∧
      (job.preparedJob prepared).site.address = job.variant.site.address :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Job.original_occurrence {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source) : job.variant.original = job.origin.site :=
  siteVariants_original valid.2

/-- Completed premise evidence is handed to the existing receipt constructor;
the compiler does not introduce a second interpretation of a guarded rule. -/
def finish? (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (job : Job) (prepared : Prepared) (completed : Assignment) (history : List GeneralPremise.Event) :=
  GeneralRuleJobs.finish? plan bound expected (job.preparedJob prepared)
    prepared.ordinary.trace prepared.ordinary.assignment completed history

theorem finish_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source)
    {answer : RecursiveCollectionMachine.Answer} {prepared : Prepared}
    (matching : prepared.Valid job.request answer)
    {completed : Assignment} {history : List GeneralPremise.Event} {receipt : GeneralRuleJobs.Receipt}
    (premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan)
      (job.preparedJob prepared).context job.origin.declaration.rule.premises
      prepared.ordinary.assignment completed history)
    (emitted : finish? plan bound expected job prepared completed history = some receipt) :
    receipt.Valid plan bound expected (job.presentedSource prepared) :=
  GeneralRuleJobs.finish_sound (job.prepared_valid valid matching) matching.matching premises emitted

theorem same_model_equiv (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) {first second : Pattern} (same : Same first second) :
    Complete.Presented.ModelEquiv plan bound expected first second := by
  have firstCanonical := Complete.Presented.canon_equiv plan bound expected first
  have secondCanonical := Complete.Presented.canon_equiv plan bound expected second
  rw [show canon first = canon second from same] at firstCanonical
  exact .trans _ _ _ firstCanonical (.symm _ _ secondCanonical)

/-- Every emitted nested conditional receipt is a step of the existing
presented GSLT. This theorem is independent of search order and profiles. -/
theorem finish_source_step {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound expected source)
    {answer : RecursiveCollectionMachine.Answer} {prepared : Prepared}
    (matching : prepared.Valid job.request answer)
    {completed : Assignment} {history : List GeneralPremise.Event} {receipt : GeneralRuleJobs.Receipt}
    (premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan)
      (job.preparedJob prepared).context job.origin.declaration.rule.premises
      prepared.ordinary.assignment completed history)
    (emitted : finish? plan bound expected job prepared completed history = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  exact ⟨job.presentedSource prepared, receipt,
    same_model_equiv plan bound expected (job.source_same valid matching),
    finish_valid valid matching premises emitted, .refl _⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff
