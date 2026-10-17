import Mettapedia.OSLF.NativeTypes.Modal.CatalogueCoverage
import Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction

open Mettapedia.OSLF.Framework

/-!
# An executable abstraction root outside finite program classification

The authored rule lambda Wrap(Done) to lambda Done is a genuine directed
change. It is sorted at arrow A Term for every A and executes through the
actual rule checks. Its raw positions remain generated, while the finite
source-carrier pool contains only Term. The admission readout marks this
unsupported classification; an empty typed catalogue is not exhaustive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers

def carrier : TypeExpr := .base "Term"
def done : Pattern := .apply "Done" []
def wrap (body : Pattern) : Pattern := .apply "Wrap" [body]
def source : Pattern := .lambda none (wrap done)
def target : Pattern := .lambda none done

def rule : RewriteRule where
  name := "top-level-abstraction-reduction"
  typeContext := []
  premises := []
  left := source
  right := target

def doneGrammar : GrammarRule :=
  {label := "Done", category := "Term", params := [], syntaxPattern := []}
def wrapGrammar : GrammarRule :=
  {label := "Wrap", category := "Term", params := [.simple "body" carrier], syntaxPattern := []}
def language : LanguageDef where
  name := "unclassified-abstraction-source"
  types := ["Term"]
  terms := [doneGrammar, wrapGrammar]
  equations := []
  rewrites := [rule]

def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
def permissions : Permissions := {sites := .all}
def binding : GeneralRuleBindingInference.BindingPlan :=
  ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩
def declaration : RulePlan := ⟨0, rule, binding⟩
def runtimePlan : Plan := ⟨snapshot, permissions, [declaration], [], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

theorem actual_candidates : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates language declaration.rule = [carrier] := by cbv

theorem source_marked_unclassified : carrierStatus language declaration.rule = .unclassifiedSource := rfl

theorem all_raw_positions_retained : (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length = 3 := by decide +kernel

theorem finite_typed_catalogue_empty : Mettapedia.OSLF.NativeTypes.Generation.schemas runtimePlan = [] := by cbv

theorem done_typed (bound : List TypeExpr) : HasType language snapshot.free bound done carrier := by
  apply HasType.constructor (rule := doneGrammar)
  · exact List.mem_cons_self
  · simp [UsesBareCollection, doneGrammar]
  · exact .nil

theorem wrap_done_typed (bound : List TypeExpr) : HasType language snapshot.free bound (wrap done) carrier := by
  apply HasType.constructor (rule := wrapGrammar)
  · exact List.mem_cons.mpr (.inr List.mem_cons_self)
  · simp [UsesBareCollection, wrapGrammar, carrier]
  · exact .cons trivial rfl (done_typed bound) .nil

/-- The unsupported root has an unbounded family of genuine arrow typings,
rather than being rejected because no independent sort derivation exists. -/
theorem all_arrow_domains_typed (domain : TypeExpr) :
    HasType language snapshot.free [] source (.arrow domain carrier) :=
  .lambda (wrap_done_typed [domain])

theorem source_proper (domain : TypeExpr) :
    OpenPatternWellSorted language snapshot.free [] (.arrow domain carrier) source :=
  ⟨all_arrow_domains_typed domain, by cbv, by cbv, by cbv⟩

theorem target_proper (domain : TypeExpr) :
    OpenPatternWellSorted language snapshot.free [] (.arrow domain carrier) target :=
  ⟨.lambda (done_typed [domain]), by cbv, by cbv, by cbv⟩

theorem actual_root_licensed (domain : TypeExpr) :
    Licensed language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule) .all [] (.arrow domain carrier)
      declaration.rule.left (SiteData.here [] (.arrow domain carrier) source) := by
  apply Licensed.here rfl (by cbv)
  exact all_arrow_domains_typed domain

theorem missing_root_typing (domain : TypeExpr) :
    Licensed language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule) .all [] (.arrow domain carrier)
      declaration.rule.left (SiteData.here [] (.arrow domain carrier) source) ∧
      ¬ ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas runtimePlan,
        schema.programCarrier = .arrow domain carrier := by
  refine ⟨actual_root_licensed domain, ?_⟩
  rintro ⟨schema, member, _⟩
  rw [finite_typed_catalogue_empty] at member
  exact List.not_mem_nil member

def primitive (domain : TypeExpr) : GeneralRuleJobs.Receipt where
  job := ⟨0, declaration, SiteData.here [] (.arrow domain carrier) source⟩
  matcherTrace := []
  captured := []
  completed := []
  premiseHistory := []
  localTarget := target
  target := target

private theorem actual_matching :
    GeneralScopedMatchMachine.TracedMatches declaration.rule declaration.binding.spec 0
      .left [] 0 [] declaration.rule.left source [] [] := by
  apply GeneralScopedMatchMachine.TracedMatches.binder
  apply GeneralScopedMatchMachine.TracedMatches.constructor
  apply GeneralScopedMatchMachine.TracedArguments.cons (headTrace := []) (tailTrace := []) (middle := [])
  · exact .constructor .nil
  · exact .nil

theorem primitive_valid (domain : TypeExpr) :
    (primitive domain).Valid runtimePlan [] (.arrow domain carrier) source := by
  have sourceTyped := (GeneralPlanEnvironment.typing_iff runtimePlan [] (.arrow domain carrier) source).mpr
    (source_proper domain)
  have targetTyped := (GeneralPlanEnvironment.typing_iff runtimePlan [] (.arrow domain carrier) target).mpr
    (target_proper domain)
  have licensed : (primitive domain).job.Valid runtimePlan [] (.arrow domain carrier) source :=
    ⟨List.mem_cons_self, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩
  refine ⟨licensed, ?_, rfl, rfl, targetTyped⟩
  refine GeneralPremise.RootFiring.fire (GeneralRuleJobs.Job.selected_rule licensed)
    (GeneralRuleJobs.Job.selected_specification licensed) (by cbv) sourceTyped actual_matching
    ?_ .nil (by cbv) targetTyped
  exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
    fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩

theorem actual_primitive_executes (domain : TypeExpr) :
    GeneralRuleJobs.finish? runtimePlan [] (.arrow domain carrier) (primitive domain).job [] [] [] [] =
      some (primitive domain) :=
  GeneralRuleJobs.finish_complete (primitive_valid domain)

theorem actual_nonidentity_step (domain : TypeExpr) :
    (GeneralOccurrenceSemantics.gslt runtimePlan [] (.arrow domain carrier)).Step source target ∧
      source ≠ target := by
  refine ⟨?_, by decide +kernel⟩
  let receipt : GeneralOccurrenceSemantics.Receipt := ⟨source, [], primitive domain⟩
  exact GeneralOccurrenceSemantics.Receipt.semantic_step runtimePlan [] (.arrow domain carrier)
    (receipt := receipt) ⟨.nil _, primitive_valid domain⟩

end Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls
