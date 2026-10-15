import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
import Mettapedia.OSLF.NativeTypes.Generation.Core

open Mettapedia.OSLF.Framework

/-!
# Literal-channel COMM with authored parallel reduction contexts

Collection descent is compiled from congruence declarations, separately from
the structural positions used to form type schemas. The generic compiler
below handles unrestricted collection remainder frames. Its admission law
compares the executable permissions with an independent closure of authored
context authority.

The rho consumer retains the existing scoped COMM interpretation, including
literal repeated-channel matching. It selects no equation closure. Its
parallel contexts agree with the authored ParCong authority; this does not
claim equality with full rho reduction modulo canonical name equations.
ParCong supplies context authority here; only COMM emits primitive receipts.
The receipt address retains the selected parallel occurrence, while a full
authored ParCong premise tree remains a separate comparison obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts

open Mettapedia.OSLF.MeTTaIL
open Syntax DerivedContexts GeneralTypedSites
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

def remainderFrameKind? : OneHoleContext → Option CollType
  | .collection kind [] .hole [] (some _) => some kind
  | _ => none

def authoredCollectionKinds (language : LanguageDef) : List CollType :=
  (language.rewrites.flatMap compileRuleContexts).filterMap remainderFrameKind?

def authoredCollectionPermissions (language : LanguageDef) : OperationalPermissions :=
  { collectionKinds := authoredCollectionKinds language }

/-- Independent authority: one congruence rule replaces the chosen component
while retaining an arbitrary collection remainder. -/
def CollectionAuthority (language : LanguageDef) (kind : CollType) : Prop :=
  ∃ rule ∈ language.rewrites, ∃ rest,
    RuleAuthorizesContext rule (.collection kind [] .hole [] (some rest))

theorem remainderFrameKind_exact {context : OneHoleContext} {kind : CollType} :
    remainderFrameKind? context = some kind ↔
      ∃ rest, context = .collection kind [] .hole [] (some rest) := by
  cases context <;> simp [remainderFrameKind?]
  case collection frameKind before inner after rest =>
    cases before <;> cases inner <;> cases after <;> cases rest <;>
      simp

theorem authored_collection_kinds_exact (language : LanguageDef) (kind : CollType) :
    kind ∈ authoredCollectionKinds language ↔ CollectionAuthority language kind := by
  constructor
  · intro present
    obtain ⟨context, compiled, found⟩ := List.mem_filterMap.mp present
    obtain ⟨rule, declared, contextual⟩ := List.mem_flatMap.mp compiled
    obtain ⟨rest, frame⟩ := remainderFrameKind_exact.mp found
    refine ⟨rule, declared, rest, ?_⟩
    rw [frame] at contextual
    exact compileRuleContexts_sound contextual
  · rintro ⟨rule, declared, rest, authorized⟩
    apply List.mem_filterMap.mpr
    refine ⟨.collection kind [] .hole [] (some rest), ?_, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨rule, declared, compileRuleContexts_complete authorized⟩

inductive AuthoredCollectionContext (language : LanguageDef) : OneHoleContext → Prop where
  | hole : AuthoredCollectionContext language .hole
  | collection {kind : CollType} {before after : List Pattern} {inner : OneHoleContext} :
      CollectionAuthority language kind →
      AuthoredCollectionContext language inner →
      AuthoredCollectionContext language (.collection kind before inner after none)

/-- This is a whole-context theorem: arbitrary depth, positions and siblings
are admitted exactly when every frame has independent authored authority. -/
theorem authored_collection_contexts_exact (language : LanguageDef) (context : OneHoleContext) :
    (authoredCollectionPermissions language).permitsContext context = true ↔
      AuthoredCollectionContext language context := by
  constructor
  · intro permitted
    induction context with
    | hole => exact .hole
    | apply => simp [authoredCollectionPermissions, OperationalPermissions.permitsContext,
        OperationalPermissions.permitsArgument] at permitted
    | lambda => simp [authoredCollectionPermissions, OperationalPermissions.permitsContext] at permitted
    | multiLambda => simp [authoredCollectionPermissions, OperationalPermissions.permitsContext] at permitted
    | substBody => simp [OperationalPermissions.permitsContext] at permitted
    | substReplacement => simp [OperationalPermissions.permitsContext] at permitted
    | collection kind before inner after rest ih =>
        simp only [OperationalPermissions.permitsContext, authoredCollectionPermissions,
          Bool.and_eq_true] at permitted
        obtain ⟨⟨authority, closed⟩, innerPermitted⟩ := permitted
        have restNone : rest = none := Option.isNone_iff_eq_none.mp closed
        subst rest
        exact .collection ((authored_collection_kinds_exact language kind).mp
          (of_decide_eq_true authority))
          (ih innerPermitted)
  · intro admitted
    induction admitted with
    | hole => rfl
    | collection authority _ ih =>
        simp only [OperationalPermissions.permitsContext, authoredCollectionPermissions,
          Bool.and_eq_true, Option.isNone_none, and_true]
        exact ⟨decide_eq_true ((authored_collection_kinds_exact language _).mpr authority), ih⟩

def rhoSites : OperationalPermissions := authoredCollectionPermissions rhoCalc

theorem rho_sites_computed_from_authored_rules :
    authoredCollectionKinds rhoCalc = [.hashBag] := by
  simp [authoredCollectionKinds, rhoCalc, compile_rhoCommRewrite_nil,
    compile_rhoParCongRewrite, rhoParallelContext, remainderFrameKind?]

theorem rho_collection_authority_exact (kind : CollType) :
    CollectionAuthority rhoCalc kind ↔ kind = .hashBag := by
  rw [← authored_collection_kinds_exact, rho_sites_computed_from_authored_rules]
  simp

/-- Every admitted rho context is built solely from the source-authorized
parallel frame, so it transports an existing paper reduction. -/
theorem rho_context_preserves_reduction {context : OneHoleContext}
    (permitted : rhoSites.permitsContext context = true)
    {source target : Pattern} (step : Nonempty (Reduces source target)) :
    Nonempty (Reduces (context.fill source) (context.fill target)) := by
  have admitted := (authored_collection_contexts_exact rhoCalc context).mp permitted
  clear permitted
  induction admitted with
  | hole => exact step
  | @collection kind before after inner authority _ ih =>
      have kindEq := (rho_collection_authority_exact kind).mp authority
      subst kind
      exact rhoParallelInstance_sound before after ih

theorem rho_blocks_constructor_descent (constructor : String)
    (before after : List Pattern) (inner : OneHoleContext) :
    rhoSites.permitsContext (.apply constructor before inner after) = false := by
  simp [rhoSites, authoredCollectionPermissions, OperationalPermissions.permitsContext,
    OperationalPermissions.permitsArgument]

theorem rho_blocks_binder_descent (binder : Option String) (inner : OneHoleContext) :
    rhoSites.permitsContext (.lambda binder inner) = false := by
  rfl

def permissions : GeneralExecutionAdmission.Permissions :=
  { GeneralRho.permissions with sites := rhoSites }

def plan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile GeneralRho.snapshot permissions

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment := { operational := permissions }

def chosen : GeneralExecutionAdmission.Snapshot :=
  Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot GeneralRho.snapshot fragment

theorem chosen_snapshot : chosen = GeneralRho.snapshot := by
  change ({GeneralRho.snapshot with language :=
    Mettapedia.OSLF.NativeTypes.Generation.selectedLanguage GeneralRho.language ⟨none, permissions⟩} :
      GeneralExecutionAdmission.Snapshot) = _
  rw [Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]
  rfl

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated : Mettapedia.OSLF.NativeTypes.Generation.Generated :=
  Mettapedia.OSLF.NativeTypes.Generation.generate GeneralRho.snapshot fragment
    Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem generated_plan : generated.plan = plan := by
  change GeneralExecutionAdmission.compile chosen permissions = plan
  rw [chosen_snapshot]
  rfl

theorem compiled_plan_retains_rule_evidence :
    plan = { GeneralRho.plan with permissions := permissions } := by
  rfl

theorem compiled_plan_admitted : plan.complete = true := by
  rw [compiled_plan_retains_rule_evidence]
  exact GeneralRho.compilation_complete

def runtimePlan : GeneralExecutionAdmission.Plan :=
  { GeneralRho.FrontierControls.runtimePlan with permissions := permissions }

theorem compiled_runtime_plan : plan = runtimePlan := by
  rw [compiled_plan_retains_rule_evidence, GeneralRho.FrontierControls.runtime_plan_actual]
  rfl

def request (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  .fromSnapshot GeneralRho.snapshot permissions [] (.base "Proc") source

def runtimeRequest (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan, [], .base "Proc", source⟩

theorem request_actual (source : Pattern) : request source = runtimeRequest source := by
  change (⟨plan, [], .base "Proc", source⟩ : GeneralOccurrenceFrontier.Request) = _
  rw [compiled_runtime_plan]
  rfl

theorem generated_request (source : Pattern) :
    generated.request [] (.base "Proc") source = request source := by
  change GeneralOccurrenceFrontier.Request.fromSnapshot chosen permissions [] (.base "Proc") source = _
  rw [chosen_snapshot]
  rfl

theorem every_generated_job_has_authored_context {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {job : GeneralRuleJobs.Job}
    (present : job ∈ GeneralRuleJobs.jobs plan bound type source) :
    AuthoredCollectionContext rhoCalc job.site.context := by
  have permitted := ((GeneralRuleJobs.jobs_spec plan bound type source job).mp present).2.permitted
  exact (authored_collection_contexts_exact rhoCalc job.site.context).mp permitted

theorem every_valid_receipt_has_authored_context {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound type source) :
    AuthoredCollectionContext rhoCalc receipt.job.site.context := by
  exact (authored_collection_contexts_exact rhoCalc receipt.job.site.context).mp valid.1.2.permitted

theorem constructor_context_forces_root {context : OneHoleContext} {focus : Pattern}
    (constructor : String) (arguments : List Pattern)
    (admitted : AuthoredCollectionContext rhoCalc context)
    (filled : context.fill focus = .apply constructor arguments) :
    context = .hole ∧ focus = .apply constructor arguments := by
  cases admitted with
  | hole => exact ⟨rfl, filled⟩
  | collection => cases filled

/-- Independent firing semantics cannot reduce inside any constructor under
this profile, and COMM cannot match a constructor at the root. -/
theorem constructor_has_no_primitive {bound : List TypeExpr} {type : TypeExpr}
    (constructor : String) (arguments : List Pattern) (receipt : GeneralRuleJobs.Receipt) :
    ¬receipt.Valid plan bound type (.apply constructor arguments) := by
  intro valid
  have context := every_valid_receipt_has_authored_context valid
  have filled := valid.1.2.source_eq
  obtain ⟨_root, focus⟩ := constructor_context_forces_root constructor arguments context filled
  have declared := List.fst_mem_of_mem_zipIdx valid.1.1
  rw [compiled_runtime_plan] at declared
  change receipt.job.declaration ∈ [GeneralRho.declaration] at declared
  have declarationEq := List.mem_singleton.mp declared
  have selected := GeneralRuleJobs.Job.selected_rule valid.1
  cases valid.2.1 with
  | fire declaredRule _ _ _ matching _ _ _ _ =>
      have ruleEq := Option.some.inj (declaredRule.symm.trans selected)
      rw [ruleEq, declarationEq, focus] at matching
      change GeneralScopedMatchMachine.TracedMatches _ _ _ .left [] 0 []
        (.collection .hashBag _ _) (.apply constructor arguments) _ _ at matching
      cases matching

theorem selected_equations_empty : plan.equations = [] := by
  rw [compiled_plan_retains_rule_evidence]
  exact GeneralRho.compilation_has_no_equations

theorem no_selected_equation {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} :
    ¬GeneralOccurrenceSemantics.Equation plan bound type source target := by
  rintro ⟨receipt, valid, _⟩
  have declared := valid.job.1
  rw [selected_equations_empty] at declared
  exact List.not_mem_nil declared

theorem selected_equation_classes_are_literal {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern}
    (equivalent : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound type)
      source target) : source = target := by
  induction equivalent with
  | rel _ _ equation => exact False.elim (no_selected_equation equation)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem constructor_has_no_selected_step {bound : List TypeExpr} {type : TypeExpr}
    (constructor : String) (arguments : List Pattern) (target : Pattern) :
    ¬(GeneralOccurrenceSemantics.gslt plan bound type).Step
      (.apply constructor arguments) target := by
  rintro ⟨representative, receipt, sourceEq, valid, _⟩
  have same := selected_equation_classes_are_literal sourceEq
  rw [← same] at valid
  exact constructor_has_no_primitive constructor arguments receipt valid

open Mettapedia.GSLT.LanguageDef.WellSorted

theorem runtime_start {source : Pattern}
    (canonical : source.hasCanonicalBinderMetadata = true)
    (checked : checkOpenPatternWellSorted GeneralRho.language GeneralRho.snapshot.free
      [] (.base "Proc") source = true) :
    GeneralOccurrenceFrontier.start (runtimeRequest source) =
      { agenda := [.visit ⟨source, [], by
          rw [show (runtimeRequest source).root = source from
            Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
          exact .nil source⟩, .universe] } := by
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root,
    runtimeRequest, runtimePlan, GeneralRho.FrontierControls.runtimePlan,
    Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]
  change (if checkOpenPatternWellSorted GeneralRho.language GeneralRho.snapshot.free
    [] (.base "Proc") source then _ else _) = _
  rw [checked]
  rfl

def readouts (source : Pattern) (fuel : Nat) : List GeneralRho.FrontierControls.Readout :=
  GeneralRho.FrontierControls.readouts (request source) fuel

def payloadSource : Pattern :=
  GeneralRho.output GeneralRho.FrontierControls.channel GeneralRho.FrontierControls.rootSource

def guardedSource : Pattern :=
  GeneralRho.input GeneralRho.FrontierControls.channel GeneralRho.FrontierControls.rootSource

def quotedChannelSource : Pattern :=
  GeneralRho.output (.apply "NQuote" [GeneralRho.FrontierControls.rootSource])
    GeneralRho.FrontierControls.zero

def jobAddresses (source : Pattern) : List (List Nat) :=
  (GeneralRuleJobs.jobs runtimePlan [] (.base "Proc") source).map (fun job => job.site.address)

theorem payload_jobs_do_not_descend : jobAddresses payloadSource = [[]] := by
  decide +kernel

theorem guarded_jobs_do_not_descend : jobAddresses guardedSource = [[]] := by
  decide +kernel

theorem quoted_channel_jobs_do_not_descend : jobAddresses quotedChannelSource = [[]] := by
  decide +kernel

theorem payload_source_has_no_selected_step (target : Pattern) :
    ¬(GeneralOccurrenceSemantics.gslt plan [] (.base "Proc")).Step payloadSource target :=
  constructor_has_no_selected_step "POutput" _ target

theorem guarded_source_has_no_selected_step (target : Pattern) :
    ¬(GeneralOccurrenceSemantics.gslt plan [] (.base "Proc")).Step guardedSource target :=
  constructor_has_no_selected_step "PInput" _ target

theorem quoted_channel_source_has_no_selected_step (target : Pattern) :
    ¬(GeneralOccurrenceSemantics.gslt plan [] (.base "Proc")).Step quotedChannelSource target :=
  constructor_has_no_selected_step "POutput" _ target

/-- These actual finite runs retain pending certification. The semantic
non-reduction proofs above do not infer absence from these empty readouts. -/
theorem blocked_context_execution_remains_incomplete :
    readouts payloadSource 3 = [] ∧ readouts guardedSource 3 = [] ∧
    readouts quotedChannelSource 3 = [] ∧
    GeneralOccurrenceFrontier.complete (request payloadSource)
      (GeneralOccurrenceFrontier.run (request payloadSource) 3
        (GeneralOccurrenceFrontier.start (request payloadSource))) = false ∧
    GeneralOccurrenceFrontier.complete (request guardedSource)
      (GeneralOccurrenceFrontier.run (request guardedSource) 3
        (GeneralOccurrenceFrontier.start (request guardedSource))) = false ∧
    GeneralOccurrenceFrontier.complete (request quotedChannelSource)
      (GeneralOccurrenceFrontier.run (request quotedChannelSource) 3
        (GeneralOccurrenceFrontier.start (request quotedChannelSource))) = false := by
  unfold readouts
  repeat rw [request_actual]
  unfold GeneralRho.FrontierControls.readouts
  repeat rw [runtime_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem actual_root_receipt :
    readouts GeneralRho.FrontierControls.rootSource 30 =
      [⟨0, [], [], GeneralRho.commTrace,
        some GeneralRho.FrontierControls.receivedBody,
        GeneralRho.FrontierControls.rootTarget⟩] := by
  unfold readouts
  rw [request_actual]
  unfold GeneralRho.FrontierControls.readouts
  rw [runtime_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem actual_parallel_receipt :
    readouts GeneralRho.FrontierControls.parallelSource 55 =
      [⟨0, [1], [], GeneralRho.commTrace,
        some GeneralRho.FrontierControls.receivedBody,
        GeneralRho.FrontierControls.parallelTarget⟩] := by
  unfold readouts
  rw [request_actual]
  unfold GeneralRho.FrontierControls.readouts
  rw [runtime_start (by decide +kernel) (by decide +kernel)]
  decide +kernel

#guard authoredCollectionKinds rhoCalc = [.hashBag]
#guard (readouts GeneralRho.FrontierControls.rootSource 30).length == 1
#guard (readouts GeneralRho.FrontierControls.parallelSource 55).length == 1
#guard jobAddresses payloadSource == [[]]
#guard jobAddresses guardedSource == [[]]
#guard jobAddresses quotedChannelSource == [[]]

#print axioms authored_collection_kinds_exact
#print axioms authored_collection_contexts_exact
#print axioms rho_context_preserves_reduction
#print axioms every_valid_receipt_has_authored_context
#print axioms generated_plan
#print axioms constructor_has_no_selected_step
#print axioms actual_root_receipt
#print axioms actual_parallel_receipt
#print axioms blocked_context_execution_remains_incomplete

end Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts
