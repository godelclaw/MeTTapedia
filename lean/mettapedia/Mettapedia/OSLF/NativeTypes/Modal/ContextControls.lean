import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples
import Mettapedia.OSLF.NativeTypes.Modal.ContextEquations

open Mettapedia.OSLF.Framework

/-!
# Equations lift through contexts independently of reduction permissions

The reduction profile remains root-only. Its Alpha = Beta equation still
lifts through Wrap, so Wrap(Beta) can reach Done through equation conversion
and the original Wrap(Alpha) rule. Both equivalent focus representatives
inhabit the specified-contractum modality. The retained source receipt makes
its administrative conversion and primitive origin explicit.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ContextControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples (carrier alpha beta done equation binding permissions oriented)

def wrap (term : Pattern) : Pattern := .apply "Wrap" [term]

def rule : RewriteRule where
  name := "wrap-alpha-done"
  typeContext := []
  premises := []
  left := wrap alpha
  right := done

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.language with
    name := "disabled-context-equation-separator"
    terms := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.language.terms ++
      [{label := "Wrap", category := "Term", params := [.simple "term" carrier], syntaxPattern := []}]
    rewrites := [rule]}

def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
def declaration : RulePlan := ⟨0, rule, binding⟩
def runtimePlan : Plan :=
  ⟨snapshot, permissions, [declaration], [oriented .forward, oriented .reverse], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

private theorem alpha_typed : OpenPatternWellSorted language snapshot.free [] carrier alpha := by
  apply checkOpenPatternWellSorted_sound
  cbv

private theorem beta_typed : OpenPatternWellSorted language snapshot.free [] carrier beta := by
  apply checkOpenPatternWellSorted_sound
  cbv

private theorem wrap_alpha_typed : OpenPatternWellSorted language snapshot.free [] carrier (wrap alpha) := by
  apply checkOpenPatternWellSorted_sound
  cbv

private theorem done_typed : OpenPatternWellSorted language snapshot.free [] carrier done := by
  apply checkOpenPatternWellSorted_sound
  cbv

def equationReceipt : GeneralEquationJobs.Receipt where
  job := ⟨0, oriented .forward, SiteData.here [] carrier alpha⟩
  matcherTrace := []
  captured := []
  completed := []
  premiseHistory := []
  rawReduct := beta
  target := beta

theorem equation_completed :
    GeneralEquationJobs.Completion runtimePlan [] carrier alpha equationReceipt := by
  apply GeneralEquationJobs.finish_sound (job := equationReceipt.job)
    (trace := []) (captured := []) (completed := []) (history := [])
  · refine ⟨List.mem_cons_self, .here rfl rfl ?_⟩
    exact ((GeneralPlanEnvironment.typing_iff runtimePlan [] carrier alpha).mpr alpha_typed).1
  · exact (GeneralPlanEnvironment.typing_iff runtimePlan [] carrier alpha).mpr alpha_typed
  · have left : equationReceipt.job.equation.rule.left = alpha := by cbv
    have focus : equationReceipt.job.site.focus.eraseBinderMetadata = alpha := by cbv
    rw [left, focus]
    exact .constructor .nil
  · exact .nil
  · cbv

theorem focus_equivalent : Relation.EqvGen
    (GeneralOccurrenceSemantics.Equation runtimePlan [] carrier) alpha beta :=
  .rel _ _ ⟨equationReceipt, equation_completed, rfl⟩

def wrappedEquationReceipt : GeneralEquationJobs.Receipt :=
  {equationReceipt with
    job := {equationReceipt.job with
      site := equationReceipt.job.site.wrapApplication 4 "Wrap" [alpha] 0}
    target := wrap beta}

theorem wrapped_equation_completed :
    GeneralEquationJobs.Completion runtimePlan [] carrier (wrap alpha) wrappedEquationReceipt := by
  apply GeneralEquationJobs.finish_sound (job := wrappedEquationReceipt.job)
    (trace := []) (captured := []) (completed := []) (history := [])
  · refine ⟨List.mem_cons_self, ?_⟩
    apply generate_sound
    cbv
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact (GeneralPlanEnvironment.typing_iff runtimePlan [] carrier (wrap alpha)).mpr wrap_alpha_typed
  · have left : wrappedEquationReceipt.job.equation.rule.left = alpha := by cbv
    have focus : wrappedEquationReceipt.job.site.focus.eraseBinderMetadata = alpha := by cbv
    rw [left, focus]
    exact .constructor .nil
  · exact .nil
  · cbv

theorem context_equations_preserved :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation runtimePlan [] carrier) alpha beta ∧
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation runtimePlan [] carrier)
        (wrap alpha) (wrap beta) :=
  ⟨focus_equivalent, .rel _ _ ⟨wrappedEquationReceipt, wrapped_equation_completed, rfl⟩⟩

private theorem wrap_matching {actual : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial captured : ScopedRuleMatching.Assignment} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice}
    (matched : GeneralScopedMatchMachine.TracedMatches actual spec ambient site path depth initial
      (wrap alpha) target trace captured) : target = wrap alpha := by
  cases matched with
  | constructor arguments =>
      cases arguments with
      | cons first rest =>
          cases rest
          have same := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.nullary_matching first
          cases same
          rfl

theorem wrap_beta_has_no_primitive_step :
    ¬ ∃ firing : GeneralRuleJobs.Receipt, firing.Valid runtimePlan [] carrier (wrap beta) := by
  rintro ⟨firing, valid⟩
  have root := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.root_only_site valid.1.2
  have selected := firing.job.selected_rule valid.1
  have declared : firing.job.declaration = declaration := by
    have present := List.fst_mem_of_mem_zipIdx valid.1.1
    simpa only [runtimePlan, List.mem_singleton] using present
  have primitive := valid.2.1
  rw [root] at primitive
  cases primitive with
  | @fire _ _ _ _ _ actual _ _ _ _ _ selectedRule _ _ _ matched _ _ _ _ =>
      have selectedEq := Option.some.inj (selectedRule.symm.trans selected)
      have left : actual.left = wrap alpha := by rw [selectedEq, declared]; cbv
      rw [left] at matched
      have impossible := wrap_matching matched
      exact (by decide : wrap beta ≠ wrap alpha) impossible

def schema : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := List.mem_cons_self
  position := (RedexPosition.positions rule.left)[1]?.getD []
  bound := []
  programCarrier := carrier
  focusBound := []
  focusCarrier := carrier

theorem schema_position : schema.position = [0] := by cbv

theorem schema_fill (assignment : ScopedRuleMatching.Assignment) (term : Pattern) :
    schema.fill? assignment term = some (wrap term) := by
  unfold Schema.fill?
  rw [schema_position]
  have left : schema.declaration.rule.left = wrap alpha := by cbv
  rw [left]
  simp only [wrap, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fillArgs?,
    ScopedRuleMatching.instantiateArgsWith?, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]

theorem schema_rhs (assignment : ScopedRuleMatching.Assignment) :
    schema.rhs? assignment = some done := by
  exact Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.nullary_reduct schema.operation schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length assignment "Done" rfl

def continuation : Continuation := fun _ target => PLift (target = done)

private theorem request_nil (anchor : ScopedRuleMatching.Assignment) :
    TypedRequest schema (fun _ _ => False) anchor [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have names : schema.relyNames = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)
  · exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
      fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
  · have names : schema.matchedNames = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)
  · have names : RedexPosition.fvarNames schema.declaration.rule.left ++
        RedexPosition.fvarNames schema.declaration.rule.right = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)

private theorem typed_request_is_nil {assignment : ScopedRuleMatching.Assignment}
    (request : TypedRequest schema (fun _ _ => False) [] assignment) : assignment = [] := by
  cases assignment with
  | nil => rfl
  | cons pair rest =>
      obtain ⟨name, value⟩ := pair
      obtain ⟨dependencies, expected, declared, _⟩ := request.2.1.1 name value List.mem_cons_self
      simp only [Schema.context, schema, declaration, binding, dependencies?, List.filter_nil] at declared
      cases declared

private def alphaIntroduction : IntroductionCase schema alpha [] continuation where
  source := wrap alpha
  target := done
  trace := []
  captured := []
  history := []
  focus := by
    rw [schema_position]
    apply Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance.application (index := 0) (argument := alpha) rfl
    apply Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance.here
    cbv
  sourceInstance := by cbv
  sourceTyped := (GeneralPlanEnvironment.typing_iff runtimePlan [] carrier (wrap alpha)).mpr wrap_alpha_typed
  admitted := by cbv
  matching := .constructor (.cons (.constructor .nil) .nil)
  capturedTyped := (request_nil []).2.1
  premises := .nil
  reduct := schema_rhs []
  targetTyped := (GeneralPlanEnvironment.typing_iff runtimePlan [] carrier done).mpr done_typed
  certificate := ⟨rfl⟩

def alphaEvidence : Evidence schema (fun _ _ => False) continuation alpha :=
  m_intro rfl alpha_typed.1 [] (request_nil []).2.1
    (by
      have names : schema.matchedNames = [] := by cbv
      intro name present
      rw [names] at present
      exact False.elim (List.not_mem_nil present))
    (fun assignment request => by
      have same := typed_request_is_nil request
      subst assignment
      exact alphaIntroduction)

theorem alpha_inhabits : Inhabits schema (fun _ _ => False) continuation alpha := ⟨alphaEvidence⟩

def betaEvidence : Evidence schema (fun _ _ => False) continuation beta where
  carrier := beta_typed.1
  anchor := alphaEvidence.anchor
  anchorTyped := alphaEvidence.anchorTyped
  anchorPresent := alphaEvidence.anchorPresent
  respond assignment request := by
    let outcome := alphaEvidence.respond assignment request
    have sourceEq : outcome.source = wrap alpha :=
      Option.some.inj (outcome.filling.symm.trans (schema_fill assignment alpha))
    have path : GeneralOccurrenceSemantics.ConversionPath runtimePlan [] carrier
        (wrap beta) outcome.source [.reverse wrappedEquationReceipt] := by
      rw [sourceEq]
      exact .back wrapped_equation_completed rfl (.nil (wrap alpha))
    exact
      { source := wrap beta
        target := outcome.target
        filling := schema_fill assignment beta
        rhs := outcome.rhs
        receipt := Equations.rebase [.reverse wrappedEquationReceipt] outcome.receipt
        valid := Equations.rebase_valid path outcome.valid
        targetConversion := outcome.targetConversion
        certificate := outcome.certificate }

theorem beta_inhabits : Inhabits schema (fun _ _ => False) continuation beta := ⟨betaEvidence⟩

theorem wrap_beta_steps_done :
    (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step (wrap beta) done := by
  obtain ⟨source, target, filling, rhs, step⟩ := m_step betaEvidence [] (request_nil betaEvidence.anchor)
  have sourceEq : source = wrap beta := Option.some.inj (filling.symm.trans (schema_fill [] beta))
  have targetEq : target = done := Option.some.inj (rhs.symm.trans (schema_rhs []))
  change (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step source target at step
  simpa only [sourceEq, targetEq] using step

/-- The same declared equation preserves both contextual native inhabitants,
while root-only reduction still excludes a primitive rewrite at Wrap(Beta). -/
theorem modal_focus_equation_invariance :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation runtimePlan [] carrier) alpha beta ∧
      Inhabits schema (fun _ _ => False) continuation alpha ∧
      Inhabits schema (fun _ _ => False) continuation beta :=
  ⟨focus_equivalent, alpha_inhabits, beta_inhabits⟩

end Mettapedia.OSLF.NativeTypes.Modal.ContextControls
