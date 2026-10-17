import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineExactness
import Mettapedia.GSLT.LanguageDef.BindingDecisionAdequacy
import Mettapedia.GSLT.Distinction.OrderedAdministration

/-!
# Adequacy of the ordered-match machine language for the fused evaluator

The reference machine of the ordered-match machine language reaches a result
from a fused program on a subject exactly when the fused program's evaluator
lists that result, with every leaf run by binding-decision matching, ordered
premise evaluation through the source relation environment, and template
instantiation.  Through the exactness theorem this transfers to the language
itself: the language's own multi-step reduction from an encoded program to
an encoded result is membership in the evaluator's output, and, for programs
fused from first-order rule plans, membership in the plan interpreter's
output.  The retained receipt interface strengthens this to equality of whole
ordered firing lists, with capture bindings, final bindings, rule occurrences
and actual provider-row choices.  Every machine path has a decreasing work
rank; complete frontier traversal and arbitrary fuel slices preserve the
ordered observation and exact remaining control.  The phase interpretation
used in this equality is independent of recursive machine execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan PremisePlan RulePlan RuleEmission runPremisePlans runPremiseReceipts patternPlansWork)
open Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix (lowerSubject)
open Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
  (isBoundAt isConstructorOf eval_checkBound_eq eval_checkConstructor_eq mem_eval_join_iff)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

variable (relations : RelationEnv) (source : LanguageDef)

/-! ## Reachability in the reference machine -/

/-- One machine step as a relation. -/
def MachineStep (state next : MachineState) : Prop :=
  next ∈ machineStep relations source state

/-- Finitely many machine steps. -/
def Reaches : MachineState → MachineState → Prop :=
  Relation.ReflTransGen (MachineStep relations source)

theorem machineStep_done (result : Pattern) : machineStep relations source (.done result) = [] := rfl

/-- A run from a non-terminal state to a result goes through one of the
state's successors. -/
theorem reaches_done_iff_succ {state : MachineState}
    (notDone : ∀ result, state ≠ .done result) (result : Pattern) :
    Reaches relations source state (.done result) ↔
      ∃ next ∈ machineStep relations source state,
        Reaches relations source next (.done result) := by
  constructor
  · intro run
    rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, rest⟩
    · exact absurd equal (notDone result)
    · exact ⟨next, step, rest⟩
  · rintro ⟨next, step, rest⟩
    exact Relation.ReflTransGen.head step rest

/-- A result reaches only itself. -/
theorem reaches_done_done_iff (value result : Pattern) :
    Reaches relations source (.done value) (.done result) ↔ result = value := by
  constructor
  · intro run
    rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, _⟩
    · exact (MachineState.done.inj equal).symm
    · change next ∈ machineStep relations source (.done value) at step
      simp [machineStep_done] at step
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-! ## Instantiation -/

/-- What the instantiation continuation makes of a finished value. -/
def runInstantiateKont (bindings : Bindings) : List InstantiateFrame → Pattern → Pattern
  | [], value => value
  | .argument constructor accumulated remaining :: rest, value =>
      runInstantiateKont bindings rest
        (.apply constructor
          ((value :: accumulated).reverse ++ remaining.map (PatternPlan.instantiate bindings)))

/-- Remaining instantiation work stored in a continuation. -/
def kontWork : List InstantiateFrame → Nat
  | [] => 0
  | .argument _ _ remaining :: rest => 4 * patternPlansWork remaining + 2 + kontWork rest

private theorem instantiation_reaches (result : Pattern) : ∀ n : Nat,
    (∀ (template : PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame),
      4 * template.work + kontWork kont ≤ n →
        (Reaches relations source (.instantiate template bindings kont) (.done result) ↔
          result = runInstantiateKont bindings kont (template.instantiate bindings))) ∧
    (∀ (constructor : String) (accumulated : List Pattern) (remaining : List PatternPlan)
        (bindings : Bindings) (kont : List InstantiateFrame),
      4 * patternPlansWork remaining + kontWork kont + 3 ≤ n →
        (Reaches relations source
            (.instantiateArguments constructor accumulated remaining bindings kont)
            (.done result) ↔
          result = runInstantiateKont bindings kont
            (.apply constructor
              (accumulated.reverse ++ remaining.map (PatternPlan.instantiate bindings))))) ∧
    (∀ (value : Pattern) (bindings : Bindings) (kont : List InstantiateFrame),
      kontWork kont + 2 ≤ n →
        (Reaches relations source (.instantiated value bindings kont) (.done result) ↔
          result = runInstantiateKont bindings kont value)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro template bindings kont bound
        have := PatternPlan.work_pos template
        omega
      · intro constructor accumulated remaining bindings kont bound
        omega
      · intro value bindings kont bound
        omega
  | succ n inductionHypothesis =>
      obtain ⟨templateHypothesis, argumentsHypothesis, valueHypothesis⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_⟩
      · intro template bindings kont bound
        cases template with
        | metavariable name =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (lookupOrVariable bindings name) bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [instantiate_metavariable]
        | bound index =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (.bvar index) bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [PatternPlan.instantiate]
        | application constructor arguments =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [argumentsHypothesis constructor [] arguments bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [PatternPlan.instantiate]
            simp
      · intro constructor accumulated remaining bindings kont bound
        cases remaining with
        | nil =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (.apply constructor accumulated.reverse) bindings kont
              (by simp [patternPlansWork] at bound; omega)]
            simp
        | cons template templates =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [templateHypothesis template bindings (.argument constructor accumulated templates :: kont)
              (by simp [patternPlansWork, kontWork] at bound ⊢; omega)]
            simp [runInstantiateKont, List.reverse_cons, List.append_assoc]
      · intro value bindings kont bound
        cases kont with
        | nil =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [reaches_done_done_iff]
            rfl
        | cons frame rest =>
            cases frame with
            | argument constructor accumulated remaining =>
                rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
                simp only [machineStep, List.mem_singleton, exists_eq_left]
                rw [argumentsHypothesis constructor (value :: accumulated) remaining bindings rest
                  (by simp [kontWork] at bound; omega)]
                rfl

/-- Instantiating a template under a continuation reaches exactly the value
the continuation makes of the instantiated template. -/
theorem reaches_instantiate_iff (template : PatternPlan) (bindings : Bindings)
    (kont : List InstantiateFrame) (result : Pattern) :
    Reaches relations source (.instantiate template bindings kont) (.done result) ↔
      result = runInstantiateKont bindings kont (template.instantiate bindings) :=
  (instantiation_reaches relations source result _).1 template bindings kont le_rfl

/-! ## Premises -/

/-- Premise evaluation reaches exactly the instantiations of the template
under the ordered premise results. -/
theorem reaches_premises_iff (queries : List PremisePlan) :
    ∀ (template : PatternPlan) (bindings : Bindings) (result : Pattern),
      Reaches relations source (.premises queries template bindings) (.done result) ↔
        ∃ final ∈ runPremisePlans relations source queries bindings,
          result = template.instantiate final := by
  induction queries with
  | nil =>
      intro template bindings result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_instantiate_iff]
      simp [runPremisePlans, runInstantiateKont]
  | cons query queries inductionHypothesis =>
      intro template bindings result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_map, runPremisePlans, List.mem_flatMap]
      constructor
      · rintro ⟨next, ⟨extended, member, rfl⟩, run⟩
        obtain ⟨final, finalMember, equal⟩ := (inductionHypothesis template extended result).mp run
        exact ⟨final, ⟨extended, member, finalMember⟩, equal⟩
      · rintro ⟨final, ⟨extended, member, finalMember⟩, equal⟩
        exact ⟨.premises queries template extended, ⟨extended, member, rfl⟩,
          (inductionHypothesis template extended result).mpr ⟨final, finalMember, equal⟩⟩

/-! ## Matching -/

/-- Matching reaches a result exactly through some binding the decision
evaluator lists, returned to the continuation. -/
theorem reaches_bdRun_iff (decision : Decision) :
    ∀ (subject : Pattern) (kont : List Frame) (result : Pattern),
      Reaches relations source (.bdRun decision subject kont) (.done result) ↔
        ∃ bindings ∈ decision.eval subject,
          Reaches relations source (.bdRet bindings subject kont) (.done result) := by
  induction decision with
  | succeed =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, Decision.eval]
  | capture path name =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection, Decision.eval]
      | some focused => simp [machineStep, projection, Decision.eval]
  | checkBound path expected =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion),
        eval_checkBound_eq]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection]
      | some focused =>
          cases bound : isBoundAt focused expected <;> simp [machineStep, projection, bound]
  | checkConstructor path expected arity children inductionHypothesis =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion),
        eval_checkConstructor_eq]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection]
      | some focused =>
          cases constructorTest : isConstructorOf focused expected arity with
          | false => simp [machineStep, projection, constructorTest]
          | true =>
              simp only [machineStep, projection, constructorTest, if_true, List.mem_singleton,
                exists_eq_left]
              exact inductionHypothesis subject kont result
  | join head tail headHypothesis tailHypothesis =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [headHypothesis]
      constructor
      · rintro ⟨headBindings, headMember, run⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)] at run
        simp only [machineStep, List.mem_singleton, exists_eq_left] at run
        rw [tailHypothesis] at run
        obtain ⟨tailBindings, tailMember, run⟩ := run
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)] at run
        cases merge : mergeBindings headBindings tailBindings with
        | none => simp [machineStep, merge] at run
        | some merged =>
            simp only [machineStep, merge, List.mem_singleton, exists_eq_left] at run
            exact ⟨merged, (mem_eval_join_iff head tail subject merged).mpr
              ⟨headBindings, headMember, tailBindings, tailMember, merge⟩, run⟩
      · rintro ⟨merged, mergedMember, run⟩
        obtain ⟨headBindings, headMember, tailBindings, tailMember, merge⟩ :=
          (mem_eval_join_iff head tail subject merged).mp mergedMember
        refine ⟨headBindings, headMember, ?_⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [tailHypothesis]
        refine ⟨tailBindings, tailMember, ?_⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, merge, List.mem_singleton, exists_eq_left]
        exact run

/-- The frame after matching hands the bindings to premise evaluation. -/
theorem reaches_bdRet_afterMatch_iff (bindings : Bindings) (subject : Pattern)
    (premises : List PremisePlan) (template : PatternPlan) (kont : List Frame) (result : Pattern) :
    Reaches relations source (.bdRet bindings subject (.afterMatch premises template :: kont))
        (.done result) ↔
      Reaches relations source (.premises premises template bindings) (.done result) := by
  rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
  simp [machineStep]

/-! ## Leaves -/

/-- What one leaf produces on a subject: matched bindings, then ordered
premises, then the instantiated template.  This is the plan interpreter's
shape with the binding decision in place of the pattern plan. -/
def runLeaf (subject : Pattern) (leaf : Leaf) : List Pattern :=
  (leaf.plan.decision.eval subject).flatMap fun bindings =>
    (runPremisePlans relations source leaf.plan.premises bindings).map
      leaf.plan.template.instantiate

/-- Running a leaf reaches exactly its results. -/
theorem reaches_leaf_iff (leaf : Leaf) (subject result : Pattern) :
    Reaches relations source
        (.bdRun leaf.plan.decision subject [.afterMatch leaf.plan.premises leaf.plan.template])
        (.done result) ↔
      result ∈ runLeaf relations source subject leaf := by
  rw [reaches_bdRun_iff]
  simp only [runLeaf, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨bindings, member, run⟩
    rw [reaches_bdRet_afterMatch_iff, reaches_premises_iff] at run
    obtain ⟨final, finalMember, equal⟩ := run
    exact ⟨bindings, member, final, finalMember, equal.symm⟩
  · rintro ⟨bindings, member, final, finalMember, equal⟩
    refine ⟨bindings, member, ?_⟩
    rw [reaches_bdRet_afterMatch_iff, reaches_premises_iff]
    exact ⟨final, finalMember, equal.symm⟩

/-! ## The structural prefilter -/

mutual
  def matrixPatternSize : MatrixPattern → Nat
    | .wildcard => 1
    | .node _ children => 1 + patternsSize children

  def patternsSize : List MatrixPattern → Nat
    | [] => 0
    | pattern :: patterns => matrixPatternSize pattern + patternsSize patterns
end

theorem patternsSize_append (first second : List MatrixPattern) :
    patternsSize (first ++ second) = patternsSize first + patternsSize second := by
  induction first with
  | nil => simp [patternsSize]
  | cons pattern patterns inductionHypothesis =>
      simp only [List.cons_append, patternsSize, inductionHypothesis]
      omega

/-- The prefilter reaches a result exactly when the residual patterns match
the lowered cursor structurally and the leaf produces the result. -/
theorem reaches_prefilter_iff (leaf : Leaf) (subject result : Pattern) :
    ∀ (patterns : List MatrixPattern) (cursor : List Pattern),
      Reaches relations source (.prefilter patterns cursor leaf subject) (.done result) ↔
        (OPM.structuralMatchList patterns (cursor.map lowerSubject) = true ∧
          result ∈ runLeaf relations source subject leaf)
  | [], [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_leaf_iff]
      simp [OPM.structuralMatchList]
  | [], focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .wildcard :: patterns, [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .wildcard :: patterns, focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_prefilter_iff leaf subject result patterns cursor]
      simp [OPM.structuralMatchList, OPM.structuralMatch]
  | .node head children :: patterns, [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .node head children :: patterns, focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep]
      by_cases keyTest : subjectKey focused = (⟨head, children.length⟩ : Key)
      · rw [if_pos keyTest]
        simp only [List.mem_singleton, exists_eq_left]
        rw [reaches_prefilter_iff leaf subject result (children ++ patterns)
          (subjectChildren focused ++ cursor)]
        simp only [subjectKey,
          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.ConstructorKey.mk.injEq]
          at keyTest
        obtain ⟨headEqual, lengthEqual⟩ := keyTest
        rw [List.map_cons, List.map_append, lowerSubject_eq focused, OPM.structuralMatchList,
          OPM.structuralMatch,
          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.structuralMatchList_append
            children patterns _ _ (by simp [lengthEqual])]
        simp [headEqual]
      · rw [if_neg keyTest]
        simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
        intro structural
        exfalso
        rw [List.map_cons, lowerSubject_eq focused, OPM.structuralMatchList, OPM.structuralMatch]
          at structural
        by_cases headEqual : head = subjectHead focused
        · have lengthDifferent : (subjectChildren focused).length ≠ children.length := by
            intro lengthEqual
            apply keyTest
            simp [subjectKey, headEqual, lengthEqual]
          rw [Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.structuralMatchList_eq_false_of_length_ne
            children _ (by simpa using lengthDifferent.symm)] at structural
          simp at structural
        · simp [headEqual] at structural
termination_by patterns _ => patternsSize patterns
decreasing_by
  all_goals simp [patternsSize, matrixPatternSize, patternsSize_append]

/-! ## Programs -/

mutual
  /-- Running a program reaches a result exactly when the fused evaluator
  lists it, every leaf run by the machine's leaf semantics. -/
  theorem reaches_run_iff :
      ∀ (program : Program) (subject : Pattern) (cursor : List Pattern) (result : Pattern),
        Reaches relations source (.run program subject cursor) (.done result) ↔
          result ∈ program.evalAll (runLeaf relations source subject) (cursor.map lowerSubject)
    | .failure, subject, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, subject, [], result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, subject, focused :: cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [reaches_run_iff next subject cursor result]
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .tryRule leaf patterns onFailure, subject, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [
          machineStep, List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or,
          exists_eq_left]
        rw [reaches_prefilter_iff relations source leaf subject result patterns cursor,
          reaches_run_iff onFailure subject cursor result]
        simp only [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        by_cases structural : OPM.structuralMatchList patterns (cursor.map lowerSubject) = true
        · simp [structural]
        · simp [structural]
    | .switch branches default, subject, [], result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [reaches_run_iff default subject [] result]
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .switch branches default, subject, focused :: cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [
          machineStep, List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or,
          exists_eq_left]
        rw [reaches_run_iff default subject (focused :: cursor) result,
          reaches_dispatch_iff branches subject focused cursor result]
        rw [List.map_cons, lowerSubject_eq focused]
        simp only [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll,
          List.mem_append, List.length_map, List.map_append]
        rfl
  /-- Dispatching on the focused subject's key reaches a result exactly when
  the matching branch's evaluation lists it. -/
  theorem reaches_dispatch_iff :
      ∀ (branches : Branches) (subject focused : Pattern) (cursor : List Pattern)
        (result : Pattern),
        Reaches relations source (.dispatch branches subject focused cursor) (.done result) ↔
          result ∈ Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll
            (runLeaf relations source subject) (subjectKey focused)
            ((subjectChildren focused ++ cursor).map lowerSubject) branches
    | .nil, subject, focused, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep,
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
    | .cons key program rest, subject, focused, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep]
        by_cases keyTest : subjectKey focused = key
        · rw [if_pos keyTest]
          simp only [List.mem_singleton, exists_eq_left]
          rw [reaches_run_iff program subject (subjectChildren focused ++ cursor) result]
          simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            keyTest]
        · rw [if_neg keyTest]
          simp only [List.mem_singleton, exists_eq_left]
          rw [reaches_dispatch_iff rest subject focused cursor result]
          simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            keyTest]
end

/-- The machine computes exactly the fused evaluator from a fresh cursor. -/
theorem reaches_iff_mem_evalAll (program : Program) (subject result : Pattern) :
    Reaches relations source (.run program subject [subject]) (.done result) ↔
      result ∈ program.evalAll (runLeaf relations source subject) [lowerSubject subject] := by
  simpa using reaches_run_iff relations source program subject [subject] result

/-! ## Transfer to the language -/

/-- Finitely many steps of the language itself. -/
def LanguageReaches : Pattern → Pattern → Prop :=
  Relation.ReflTransGen (ir relations source).semantics.Step

theorem languageReaches_of_reaches {state target : MachineState}
    (run : Reaches relations source state target) :
    LanguageReaches relations source (encodeState state) (encodeState target) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step inductionHypothesis =>
      exact Relation.ReflTransGen.tail inductionHypothesis
        (step_of_machineStep relations source step)

theorem reaches_of_languageReaches {state : MachineState} {target : Pattern}
    (run : LanguageReaches relations source (encodeState state) target) :
    ∃ final : MachineState, target = encodeState final ∧ Reaches relations source state final := by
  induction run with
  | refl => exact ⟨state, rfl, Relation.ReflTransGen.refl⟩
  | tail _ step inductionHypothesis =>
      obtain ⟨middle, rfl, run⟩ := inductionHypothesis
      obtain ⟨next, machineStep, rfl⟩ := machineStep_of_step relations source step
      exact ⟨next, rfl, Relation.ReflTransGen.tail run machineStep⟩

/-- The language reaches an encoded result from an encoded program on a
subject exactly when the fused evaluator lists the result. -/
theorem languageReaches_iff_mem_evalAll (program : Program) (subject result : Pattern) :
    LanguageReaches relations source (encodeState (.run program subject [subject]))
        (encodeState (.done result)) ↔
      result ∈ program.evalAll (runLeaf relations source subject) [lowerSubject subject] := by
  constructor
  · intro run
    obtain ⟨final, equal, machineRun⟩ := reaches_of_languageReaches relations source run
    rw [← encodeState_injective equal] at machineRun
    exact (reaches_iff_mem_evalAll relations source program subject result).mp machineRun
  · intro member
    exact languageReaches_of_reaches relations source
      ((reaches_iff_mem_evalAll relations source program subject result).mpr member)

/-! ## Programs fused from first-order rule plans -/

/-- The machine's plan for a first-order rule plan: the left-hand side
compiled to a binding decision, the premises, and the right-hand side. -/
def toMachinePlan (plan : RulePlan) : MachinePlan :=
  ⟨compile plan.left, plan.premises, plan.right⟩

mutual
  /-- Re-index occurrences and translate leaves of a fused program. -/
  def mapProgram {Rule Plan : Type} (occurrence : Rule → Nat) (plan : Plan → MachinePlan) :
      Fusion.Program Head Rule Plan → Program
    | .failure => .failure
    | .drop next => .drop (mapProgram occurrence plan next)
    | .tryRule compiled patterns onFailure =>
        .tryRule ⟨occurrence compiled.occurrence, plan compiled.plan⟩ patterns
          (mapProgram occurrence plan onFailure)
    | .switch branches default =>
        .switch (mapBranches occurrence plan branches) (mapProgram occurrence plan default)

  def mapBranches {Rule Plan : Type} (occurrence : Rule → Nat) (plan : Plan → MachinePlan) :
      Fusion.Branches Head Rule Plan → Branches
    | .nil => .nil
    | .cons key program rest =>
        .cons key (mapProgram occurrence plan program) (mapBranches occurrence plan rest)
end

mutual
  theorem evalAll_mapProgram {Rule Plan Result : Type} (occurrence : Rule → Nat)
      (plan : Plan → MachinePlan) (runLeaf : Leaf → List Result) :
      ∀ (program : Fusion.Program Head Rule Plan) (subjects : List (OPM.Subject Head)),
        (mapProgram occurrence plan program).evalAll runLeaf subjects =
          program.evalAll (fun compiled => runLeaf ⟨occurrence compiled.occurrence, plan compiled.plan⟩)
            subjects
    | .failure, subjects => by
        simp [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, [] => by
        simp [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, _ :: subjects => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        exact evalAll_mapProgram occurrence plan runLeaf next subjects
    | .tryRule compiled patterns onFailure, subjects => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        rw [evalAll_mapProgram occurrence plan runLeaf onFailure subjects]
    | .switch branches default, [] => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        exact evalAll_mapProgram occurrence plan runLeaf default []
    | .switch branches default, .node head children :: rest => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        rw [evalBranchAll_mapBranches occurrence plan runLeaf branches,
          evalAll_mapProgram occurrence plan runLeaf default]

  theorem evalBranchAll_mapBranches {Rule Plan Result : Type} (occurrence : Rule → Nat)
      (plan : Plan → MachinePlan) (runLeaf : Leaf → List Result) :
      ∀ (branches : Fusion.Branches Head Rule Plan) (query : Key)
        (subjects : List (OPM.Subject Head)),
        Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll runLeaf query
            subjects (mapBranches occurrence plan branches) =
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll
            (fun compiled => runLeaf ⟨occurrence compiled.occurrence, plan compiled.plan⟩)
            query subjects branches
    | .nil, query, subjects => by
        simp [mapBranches, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
    | .cons key program rest, query, subjects => by
        simp only [mapBranches,
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
        rw [evalAll_mapProgram occurrence plan runLeaf program subjects,
          evalBranchAll_mapBranches occurrence plan runLeaf rest query subjects]
end

/-- The machine's leaf semantics of a translated rule plan is the plan
interpreter. -/
theorem runLeaf_toMachinePlan (subject : Pattern) (occurrence : Nat) (plan : RulePlan) :
    runLeaf relations source subject ⟨occurrence, toMachinePlan plan⟩ =
      plan.run relations source subject := by
  simp [runLeaf, toMachinePlan, RulePlan.run, eval_compile]

/-- For a program fused from first-order rule plans, the language reaches an
encoded result exactly when the fused evaluator with the plan interpreter at
its leaves lists it. -/
theorem languageReaches_mapProgram_iff {Rule : Type}
    (program : Fusion.Program Head Rule RulePlan) (occurrence : Rule → Nat)
    (subject result : Pattern) :
    LanguageReaches relations source
        (encodeState (.run (mapProgram occurrence toMachinePlan program) subject [subject]))
        (encodeState (.done result)) ↔
      result ∈ program.evalAll (fun compiled => compiled.plan.run relations source subject)
        [lowerSubject subject] := by
  rw [languageReaches_iff_mem_evalAll, evalAll_mapProgram]
  simp only [runLeaf_toMachinePlan]

/-! ## Ranked ordered execution with retained receipts -/

/-- Matching work accounts for both sides of a nonlinear consistency join. -/
def decisionWork : Decision → Nat
  | .succeed | .capture _ _ | .checkBound _ _ => 1
  | .checkConstructor _ _ _ children => decisionWork children + 1
  | .join head tail => decisionWork head + decisionWork tail + 3

def bindingFrameWork : Frame → Nat
  | .joinRight tail => decisionWork tail + 2
  | .joinMerge _ => 1
  | .afterMatch queries template => queries.length + 4 * template.work + 2

def bindingKontWork : List Frame → Nat
  | [] => 0
  | frame :: rest => bindingFrameWork frame + bindingKontWork rest

mutual
  /-- Residual decision work includes the independent fallback and leaf work. -/
  def programWork : Program → Nat
    | .failure => 1
    | .drop next => programWork next + 1
    | .tryRule leaf patterns onFailure =>
        patternsSize patterns + decisionWork leaf.plan.decision +
          bindingFrameWork (.afterMatch leaf.plan.premises leaf.plan.template) +
          programWork onFailure + 3
    | .switch branches default => branchesWork branches + programWork default + 1

  def branchesWork : Branches → Nat
    | .nil => 1
    | .cons _ program rest => programWork program + branchesWork rest + 1
end

/-- Every individual administrative path has finite strictly decreasing work.
Query branching may add frontier entries but cannot extend a path's rank. -/
def machineRank : MachineState → Nat
  | .run program _ _ => programWork program
  | .dispatch branches _ _ _ => branchesWork branches
  | .prefilter patterns _ leaf _ =>
      patternsSize patterns + decisionWork leaf.plan.decision +
        bindingFrameWork (.afterMatch leaf.plan.premises leaf.plan.template) + 2
  | .bdRun decision _ kont => decisionWork decision + bindingKontWork kont + 1
  | .bdRet _ _ kont => bindingKontWork kont + 1
  | .bdDone _ => 0
  | .premises queries template _ => queries.length + 4 * template.work + 1
  | .instantiate template _ kont => 4 * template.work + kontWork kont
  | .instantiateArguments _ _ remaining _ kont =>
      4 * patternPlansWork remaining + kontWork kont + 3
  | .instantiated _ _ kont => kontWork kont + 2
  | .done _ => 0

theorem machineStep_rank {state next : MachineState}
    (step : next ∈ machineStep relations source state) :
    machineRank next < machineRank state := by
  cases state with
  | run program subject cursor =>
      cases program with
      | failure => simp [machineStep] at step
      | drop nextProgram =>
          cases cursor <;> simp [machineStep] at step
          subst next
          simp [machineRank, programWork]
      | tryRule leaf patterns onFailure =>
          simp only [machineStep, List.mem_cons, List.not_mem_nil, or_false] at step
          rcases step with rfl | rfl <;> simp only [machineRank, programWork] <;> omega
      | switch branches default =>
          cases cursor with
          | nil =>
              simp only [machineStep, List.mem_singleton] at step
              subst next
              simp only [machineRank, programWork]
              omega
          | cons focused cursor =>
              simp only [machineStep, List.mem_cons, List.not_mem_nil, or_false] at step
              rcases step with rfl | rfl <;> simp only [machineRank, programWork] <;> omega
  | dispatch branches subject focused cursor =>
      cases branches with
      | nil => simp [machineStep] at step
      | cons key program rest =>
          simp only [machineStep] at step
          split at step <;> simp only [List.mem_singleton] at step <;>
            subst next <;> simp only [machineRank, branchesWork] <;> omega
  | prefilter patterns cursor leaf subject =>
      cases patterns with
      | nil =>
          cases cursor <;> simp [machineStep] at step
          subst next
          simp [machineRank, patternsSize, bindingKontWork]
      | cons pattern patterns =>
          cases cursor with
          | nil => simp [machineStep] at step
          | cons focused cursor =>
              cases pattern with
              | wildcard =>
                  simp only [machineStep, List.mem_singleton] at step
                  subst next
                  simp [machineRank, patternsSize, matrixPatternSize]
              | node head children =>
                  simp only [machineStep] at step
                  split at step
                  · simp only [List.mem_singleton] at step
                    subst next
                    simp only [machineRank, patternsSize, matrixPatternSize,
                      patternsSize_append]
                    omega
                  · simp at step
  | bdRun decision subject kont =>
      cases decision with
      | succeed =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, decisionWork]
      | capture path name =>
          simp only [machineStep] at step
          split at step
          · simp only [List.mem_singleton] at step
            subst next
            simp [machineRank, decisionWork]
          · simp at step
      | checkBound path expected =>
          simp only [machineStep] at step
          split at step
          · split at step
            · simp only [List.mem_singleton] at step
              subst next
              simp [machineRank, decisionWork]
            · simp at step
          · simp at step
      | checkConstructor path expected arity children =>
          simp only [machineStep] at step
          split at step
          · split at step
            · simp only [List.mem_singleton] at step
              subst next
              simp [machineRank, decisionWork]
            · simp at step
          · simp at step
      | join head tail =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, decisionWork, bindingKontWork, bindingFrameWork]
          omega
  | bdRet bindings subject kont =>
      cases kont with
      | nil =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, bindingKontWork]
      | cons frame kont =>
          cases frame with
          | joinRight tail =>
              simp only [machineStep, List.mem_singleton] at step
              subst next
              simp [machineRank, bindingKontWork, bindingFrameWork]
              omega
          | joinMerge head =>
              simp only [machineStep] at step
              split at step
              · simp only [List.mem_singleton] at step
                subst next
                simp [machineRank, bindingKontWork, bindingFrameWork]
              · simp at step
          | afterMatch queries template =>
              simp only [machineStep, List.mem_singleton] at step
              subst next
              simp [machineRank, bindingKontWork, bindingFrameWork]
              omega
  | bdDone bindings => simp [machineStep] at step
  | premises queries template bindings =>
      cases queries with
      | nil =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, kontWork]
      | cons query queries =>
          simp only [machineStep, List.mem_map] at step
          obtain ⟨bindings, _, rfl⟩ := step
          simp [machineRank]
  | instantiate template bindings kont =>
      cases template <;> simp only [machineStep, List.mem_singleton] at step <;>
        subst next <;> simp only [machineRank, PatternPlan.work]
      · omega
      · omega
      · omega
  | instantiateArguments constructor accumulated remaining bindings kont =>
      cases remaining with
      | nil =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, patternPlansWork]
      | cons template templates =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp only [machineRank, patternPlansWork, kontWork]
          omega
  | instantiated value bindings kont =>
      cases kont with
      | nil =>
          simp only [machineStep, List.mem_singleton] at step
          subst next
          simp [machineRank, kontWork]
      | cons frame kont =>
          cases frame with
          | argument constructor accumulated remaining =>
              simp only [machineStep, List.mem_singleton] at step
              subst next
              simp [machineRank, kontWork]
              omega
  | done result => simp [machineStep] at step

theorem annotatedStep_rank {current next : ReceiptState}
    (step : next ∈ annotatedStep relations source current) :
    machineRank next.state < machineRank current.state := by
  apply machineStep_rank relations source
  rw [← annotatedStep_erase relations source current]
  exact List.mem_map_of_mem step

/-- Complete ordered observation obtained by recursively advancing the actual
machine operations.  Strict rank decrease proves that this fold terminates. -/
def allEmissions (relations : RelationEnv) (source : LanguageDef) (current : ReceiptState) : List (MeTTaILFirstOrderRuleCompilation.RuleEmission Nat) :=
  match current.state with
  | .done _ => current.emission?.toList
  | _ => (annotatedStep relations source current).attach.flatMap fun next => allEmissions relations source next.val
termination_by machineRank current.state
decreasing_by exact annotatedStep_rank _ _ next.property

/-- Number of frontier operations in complete depth-first traversal, counting
failed and terminal states as well as successful publications. -/
def completionWork (relations : RelationEnv) (source : LanguageDef) (current : ReceiptState) : Nat :=
  match current.state with
  | .done _ => 1
  | _ => 1 + ((annotatedStep relations source current).attach.map fun next => completionWork relations source next.val).sum
termination_by machineRank current.state
decreasing_by exact annotatedStep_rank _ _ next.property

/-- Unfold exactly one machine operation, retaining recursive calls opaque. -/
theorem allEmissions_unfold (current : ReceiptState) :
    allEmissions relations source current =
      match current.state with
      | .done _ => current.emission?.toList
      | _ => (annotatedStep relations source current).flatMap (allEmissions relations source) := by
  rw [allEmissions]
  simp only [List.flatMap_subtype, List.unattach_attach]

theorem completionWork_unfold (current : ReceiptState) :
    completionWork relations source current =
      match current.state with
      | .done _ => 1
      | _ => 1 + ((annotatedStep relations source current).map (completionWork relations source)).sum := by
  rw [completionWork]
  simp only [List.map_subtype, List.unattach_attach]

def frontierEmissions (pending : List ReceiptState) :
    List (MeTTaILFirstOrderRuleCompilation.RuleEmission Nat) :=
  pending.flatMap (allEmissions relations source)

def frontierWork (pending : List ReceiptState) : Nat :=
  (pending.map (completionWork relations source)).sum

/-- One actual frontier operation preserves the complete ordered observation
as its published prefix followed by the remaining licensed work. -/
theorem frontierStep_observation (pending : List ReceiptState) :
    frontierEmissions relations source pending =
      (frontierStep relations source pending).emissions ++
        frontierEmissions relations source (frontierStep relations source pending).pending := by
  cases pending with
  | nil => rfl
  | cons current rest =>
      simp only [frontierEmissions, List.flatMap_cons]
      rw [allEmissions_unfold]
      cases state : current.state <;>
        simp [frontierStep, state,
          List.flatMap_append]

theorem frontierStep_work (current : ReceiptState) (rest : List ReceiptState) :
    frontierWork relations source (current :: rest) =
      frontierWork relations source (frontierStep relations source (current :: rest)).pending + 1 := by
  simp only [frontierWork, List.map_cons, List.sum_cons]
  rw [completionWork_unfold]
  cases state : current.state <;>
    simp [frontierStep, state, List.sum_append] <;> omega

/-- Every finite slice preserves exact ordered completion of its residual. -/
theorem runFrontier_observation (fuel : Nat) (pending : List ReceiptState) :
    frontierEmissions relations source pending =
      (runFrontier relations source fuel pending).emissions ++
        frontierEmissions relations source (runFrontier relations source fuel pending).pending := by
  induction fuel generalizing pending with
  | zero => simp [runFrontier]
  | succ fuel ih =>
      rw [frontierStep_observation relations source pending]
      rw [ih (frontierStep relations source pending).pending]
      simp [runFrontier, List.append_assoc]

theorem completionWork_pos (current : ReceiptState) :
    0 < completionWork relations source current := by
  rw [completionWork_unfold]
  cases state : current.state <;> simp

theorem frontierWork_eq_zero (pending : List ReceiptState) :
    frontierWork relations source pending = 0 ↔ pending = [] := by
  cases pending with
  | nil => simp [frontierWork]
  | cons current rest =>
      have positive := completionWork_pos relations source current
      simp only [frontierWork, List.map_cons, List.sum_cons]
      constructor
      · intro empty
        omega
      · intro empty
        cases empty

/-- The actual finite machine frontier has an explicit complete budget. -/
theorem runFrontier_completed (fuel : Nat) (pending : List ReceiptState)
    (enough : frontierWork relations source pending ≤ fuel) :
    (runFrontier relations source fuel pending).pending = [] := by
  induction fuel generalizing pending with
  | zero =>
      have empty := (frontierWork_eq_zero relations source pending).mp (by omega)
      subst pending
      rfl
  | succ fuel ih =>
      cases pending with
      | nil => simp
      | cons current rest =>
          have work := frontierStep_work relations source current rest
          have remaining :
              frontierWork relations source (frontierStep relations source (current :: rest)).pending ≤ fuel := by
            omega
          exact ih _ remaining

/-- A completed slice publishes exactly the whole ordered machine observation. -/
theorem runFrontier_emissions_of_completed (fuel : Nat) (pending : List ReceiptState)
    (enough : frontierWork relations source pending ≤ fuel) :
    (runFrontier relations source fuel pending).emissions =
      frontierEmissions relations source pending := by
  have observed := runFrontier_observation relations source fuel pending
  rw [runFrontier_completed relations source fuel pending enough] at observed
  simpa [frontierEmissions] using observed.symm

/-! ## Independent ordered meanings of the retained phases -/

/-- Leaf meaning uses the decision evaluator and authored premise interpreter,
independently of the state machine's recursive operational observation. -/
def runLeafEmissions (subject : Pattern) (leaf : Leaf) : List (RuleEmission Nat) :=
  (leaf.plan.decision.eval subject).flatMap fun initial =>
    (runPremiseReceipts relations source leaf.plan.premises initial).map fun final =>
      ⟨leaf.occurrence, initial, final.bindings, final.choices,
        leaf.plan.template.instantiate final.bindings⟩

private def finishPremiseReceipts (queries : List PremisePlan) (template : PatternPlan)
    (bindings : Bindings) (context : FiringContext) : List (RuleEmission Nat) :=
  (runPremiseReceipts relations source queries bindings).flatMap fun final =>
    (ReceiptState.emission?
      ⟨.done (template.instantiate final.bindings),
        { context with
          bindings := final.bindings
          choices := context.choices ++ final.choices }⟩).toList

private def finishBindingReceipts (subject : Pattern) (context : FiringContext) :
    List Frame → Bindings → List (RuleEmission Nat)
  | [], _ => []
  | .joinRight tail :: rest, headBindings =>
      (tail.eval subject).flatMap fun tailBindings =>
        (mergeBindings headBindings tailBindings).toList.flatMap
          (finishBindingReceipts subject context rest)
  | .joinMerge headBindings :: rest, tailBindings =>
      (mergeBindings headBindings tailBindings).toList.flatMap
        (finishBindingReceipts subject context rest)
  | .afterMatch queries template :: _, bindings =>
      finishPremiseReceipts relations source queries template bindings
        { context with initialBindings := some bindings, bindings }

/-- Phase meanings use ordered leaf semantics, binding joins, authored premise
folds and template interpretation; they do not call `allEmissions`. -/
def receiptMeaning (current : ReceiptState) : List (RuleEmission Nat) :=
  match current.state with
  | .run program subject cursor =>
      program.evalAll (runLeafEmissions relations source subject) (cursor.map lowerSubject)
  | .dispatch branches subject focused cursor =>
      OrderedDecisionRuleFusion.Program.evalBranchAll
        (runLeafEmissions relations source subject) (subjectKey focused)
        ((subjectChildren focused ++ cursor).map lowerSubject) branches
  | .prefilter patterns cursor leaf subject =>
      if OPM.structuralMatchList patterns (cursor.map lowerSubject) then
        runLeafEmissions relations source subject leaf
      else []
  | .bdRun decision subject kont =>
      (decision.eval subject).flatMap (finishBindingReceipts relations source subject current.context kont)
  | .bdRet bindings subject kont =>
      finishBindingReceipts relations source subject current.context kont bindings
  | .bdDone _ => []
  | .premises queries template bindings =>
      finishPremiseReceipts relations source queries template bindings current.context
  | .instantiate template bindings kont =>
      (ReceiptState.emission?
        ⟨.done (runInstantiateKont bindings kont (template.instantiate bindings)), current.context⟩).toList
  | .instantiateArguments constructor accumulated remaining bindings kont =>
      (ReceiptState.emission?
        ⟨.done (runInstantiateKont bindings kont
          (.apply constructor (accumulated.reverse ++ remaining.map (PatternPlan.instantiate bindings)))),
          current.context⟩).toList
  | .instantiated value bindings kont =>
      (ReceiptState.emission? ⟨.done (runInstantiateKont bindings kont value), current.context⟩).toList
  | .done _ => current.emission?.toList

/-- Translating a first-order row preserves the entire emission, including
its actual capture bindings and ordered row witnesses. -/
theorem runLeafEmissions_toMachinePlan (subject : Pattern) (occurrence : Nat) (plan : RulePlan) :
    runLeafEmissions relations source subject ⟨occurrence, toMachinePlan plan⟩ =
      plan.runEmissions relations source occurrence subject := by
  simp [runLeafEmissions, toMachinePlan, RulePlan.runEmissions, eval_compile]

private theorem receiptMeaning_step (current : ReceiptState) :
    receiptMeaning relations source current =
      match current.state with
      | .done _ => current.emission?.toList
      | _ => (annotatedStep relations source current).flatMap (receiptMeaning relations source) := by
  rcases current with ⟨state, context⟩
  cases state with
  | run program subject cursor =>
      cases program with
      | failure => rfl
      | drop next =>
          cases cursor <;>
            dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
              OrderedDecisionRuleFusion.Program.evalAll] <;>
            simp [receiptMeaning, OrderedDecisionRuleFusion.Program.evalAll]
      | tryRule leaf patterns onFailure =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            OrderedDecisionRuleFusion.Program.evalAll]
          split <;> simp_all [receiptMeaning]
      | switch branches default =>
          cases cursor with
          | nil =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                OrderedDecisionRuleFusion.Program.evalAll]
              simp [receiptMeaning]
          | cons focused cursor =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
              simp [OrderedDecisionRuleFusion.Program.evalAll, List.map_append,
                subjectKey, receiptMeaning, lowerSubject_eq focused]
  | dispatch branches subject focused cursor =>
      cases branches with
      | nil => rfl
      | cons key program rest =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            OrderedDecisionRuleFusion.Program.evalBranchAll]
          split <;> simp_all [receiptMeaning]
  | prefilter patterns cursor leaf subject =>
      cases patterns with
      | nil =>
          cases cursor with
          | nil =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                OPM.structuralMatchList, runLeafEmissions, finishBindingReceipts,
                finishPremiseReceipts, ReceiptState.emission?]
              simp [receiptMeaning, finishBindingReceipts, finishPremiseReceipts,
                ReceiptState.emission?, List.map_eq_flatMap]
          | cons focused cursor => rfl
      | cons pattern patterns =>
          cases cursor with
          | nil => rfl
          | cons focused cursor =>
              cases pattern with
              | wildcard =>
                  dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                    OPM.structuralMatchList, OPM.structuralMatch]
                  simp [receiptMeaning, OPM.structuralMatchList, OPM.structuralMatch]
              | node head children =>
                  dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
                  by_cases keyTest : subjectKey focused = (⟨head, children.length⟩ : Key)
                  · rw [if_pos keyTest]
                    dsimp [List.map, List.flatMap, receiptMeaning]
                    simp only [subjectKey,
                      Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.ConstructorKey.mk.injEq]
                      at keyTest
                    obtain ⟨headEqual, lengthEqual⟩ := keyTest
                    have structural :
                        OPM.structuralMatchList (.node head children :: patterns)
                            (lowerSubject focused :: cursor.map lowerSubject) =
                          OPM.structuralMatchList (children ++ patterns)
                            ((subjectChildren focused ++ cursor).map lowerSubject) := by
                      rw [lowerSubject_eq focused, List.map_append,
                        OPM.structuralMatchList, OPM.structuralMatch,
                        OrderedPatternMatrixCompilation.structuralMatchList_append
                          children patterns _ _ (by simp [lengthEqual])]
                      simp [headEqual]
                    simp only [structural, List.append_nil]
                  · rw [if_neg keyTest]
                    dsimp [List.map, List.flatMap]
                    have failed :
                        OPM.structuralMatchList (.node head children :: patterns)
                          (lowerSubject focused :: cursor.map lowerSubject) = false := by
                      rw [lowerSubject_eq focused, OPM.structuralMatchList, OPM.structuralMatch]
                      by_cases headEqual : head = subjectHead focused
                      · have lengthDifferent : (subjectChildren focused).length ≠ children.length := by
                          intro lengthEqual
                          apply keyTest
                          simp [subjectKey, headEqual, lengthEqual]
                        rw [OrderedPatternMatrixCompilation.structuralMatchList_eq_false_of_length_ne
                          children _ (by simpa using lengthDifferent.symm)]
                        simp
                      · simp [headEqual]
                    simp [failed]
  | bdRun decision subject kont =>
      cases decision with
      | succeed =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext, Decision.eval]
          simp [receiptMeaning]
      | capture path name =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext, Decision.eval]
          cases path.project? subject <;> simp [receiptMeaning]
      | checkBound path expected =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
          rw [eval_checkBound_eq]
          cases projected : path.project? subject with
          | none => simp
          | some focused =>
              by_cases selected : isBoundAt focused expected = true <;>
                simp [selected, receiptMeaning]
      | checkConstructor path expected arity children =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
          rw [eval_checkConstructor_eq]
          cases projected : path.project? subject with
          | none => simp
          | some focused =>
              by_cases selected : isConstructorOf focused expected arity = true <;>
                simp [selected, receiptMeaning]
      | join head tail =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            Decision.eval, finishBindingReceipts]
          simp [receiptMeaning, finishBindingReceipts, List.flatMap_assoc,
            List.filterMap_eq_flatMap_toList]
  | bdRet bindings subject kont =>
      cases kont with
      | nil => rfl
      | cons frame kont =>
          cases frame with
          | joinRight tail =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                finishBindingReceipts]
              simp [receiptMeaning, finishBindingReceipts]
          | joinMerge head =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                finishBindingReceipts]
              cases mergeBindings head bindings <;> simp [receiptMeaning]
          | afterMatch queries template =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                finishBindingReceipts]
              simp [receiptMeaning]
  | bdDone bindings => rfl
  | premises queries template bindings =>
      cases queries with
      | nil =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            finishPremiseReceipts, runPremiseReceipts, runInstantiateKont]
          simp [receiptMeaning, runInstantiateKont]
      | cons query queries =>
          dsimp [receiptMeaning, annotatedStep, finishPremiseReceipts, runPremiseReceipts]
          simp only [List.flatMap_map, List.flatMap_assoc]
          apply List.flatMap_congr
          intro first _
          simp [receiptMeaning, finishPremiseReceipts, List.append_assoc]
  | instantiate template bindings kont =>
      cases template with
      | metavariable name =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
          rw [instantiate_metavariable]
          simp [receiptMeaning]
      | bound index =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            PatternPlan.instantiate]
          simp [receiptMeaning, PatternPlan.instantiate]
      | application constructor arguments =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            PatternPlan.instantiate]
          simp [receiptMeaning, PatternPlan.instantiate]
  | instantiateArguments constructor accumulated remaining bindings kont =>
      cases remaining with
      | nil =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
          simp [receiptMeaning]
      | cons template templates =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext]
          simp [receiptMeaning, runInstantiateKont, List.reverse_cons, List.append_assoc]
  | instantiated value bindings kont =>
      cases kont with
      | nil =>
          dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
            runInstantiateKont]
          simp [receiptMeaning]
      | cons frame kont =>
          cases frame with
          | argument constructor accumulated remaining =>
              dsimp [receiptMeaning, annotatedStep, machineStep, retainFiringContext,
                runInstantiateKont]
              simp [receiptMeaning, List.reverse_cons, List.append_assoc]
  | done target => rfl

/-- The complete ordered machine observation equals the independent phase
interpretation.  The proof uses local operation laws and strict rank decrease. -/
theorem allEmissions_eq_receiptMeaning (current : ReceiptState) :
    allEmissions relations source current = receiptMeaning relations source current := by
  induction rank : machineRank current.state using Nat.strong_induction_on generalizing current with
  | h n ih =>
      rw [allEmissions_unfold, receiptMeaning_step]
      cases state : current.state <;> try rfl
      all_goals
        apply List.flatMap_congr
        intro next member
        exact ih (machineRank next.state)
          (rank ▸ annotatedStep_rank relations source member) next rfl

/-- Starting the actual machine produces every ordered leaf firing, exactly,
with no missing, spurious, reordered or merged receipt. -/
theorem frontierEmissions_start (program : Program) (subject : Pattern) :
    frontierEmissions relations source (startFrontier program subject) =
      program.evalAll (runLeafEmissions relations source subject) [lowerSubject subject] := by
  simp only [frontierEmissions, startFrontier, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, allEmissions_eq_receiptMeaning, receiptMeaning, List.map_cons,
    List.map_nil]

/-- Any suspension consists of the actual delivered prefix and its retained
frontier, whose completion is exactly the remaining ordered leaf semantics. -/
theorem runFrontier_start_observation (program : Program) (subject : Pattern) (fuel : Nat) :
    program.evalAll (runLeafEmissions relations source subject) [lowerSubject subject] =
      (runFrontier relations source fuel (startFrontier program subject)).emissions ++
        frontierEmissions relations source
          (runFrontier relations source fuel (startFrontier program subject)).pending := by
  rw [← frontierEmissions_start relations source program subject]
  exact runFrontier_observation relations source fuel _

/-- A completed run of the actual machine equals the whole ordered fused
emission list, including overlap and duplicate query/rule occurrences. -/
theorem runFrontier_start_completed (program : Program) (subject : Pattern) (fuel : Nat)
    (enough : frontierWork relations source (startFrontier program subject) ≤ fuel) :
    (runFrontier relations source fuel (startFrontier program subject)).emissions =
      program.evalAll (runLeafEmissions relations source subject) [lowerSubject subject] := by
  rw [runFrontier_emissions_of_completed relations source fuel _ enough,
    frontierEmissions_start]

/-- Translation of a fused first-order program retains complete occurrence
receipts, rather than just the support of its target terms. -/
theorem frontierEmissions_mapProgram {Rule : Type}
    (program : Fusion.Program Head Rule RulePlan) (occurrence : Rule → Nat) (subject : Pattern) :
    frontierEmissions relations source
        (startFrontier (mapProgram occurrence toMachinePlan program) subject) =
      program.evalAll
        (fun leaf => leaf.plan.runEmissions relations source (occurrence leaf.occurrence) subject)
        [lowerSubject subject] := by
  rw [frontierEmissions_start, evalAll_mapProgram]
  simp only [runLeafEmissions_toMachinePlan]

theorem runFrontier_mapProgram_completed {Rule : Type}
    (program : Fusion.Program Head Rule RulePlan) (occurrence : Rule → Nat)
    (subject : Pattern) (fuel : Nat)
    (enough : frontierWork relations source
      (startFrontier (mapProgram occurrence toMachinePlan program) subject) ≤ fuel) :
    (runFrontier relations source fuel
        (startFrontier (mapProgram occurrence toMachinePlan program) subject)).emissions =
      program.evalAll
        (fun leaf => leaf.plan.runEmissions relations source (occurrence leaf.occurrence) subject)
        [lowerSubject subject] := by
  rw [runFrontier_emissions_of_completed relations source fuel _ enough,
    frontierEmissions_mapProgram]

/-- Erasing receipts preserves the exact original ordered result semantics. -/
theorem runLeafEmissions_targets (subject : Pattern) (leaf : Leaf) :
    (runLeafEmissions relations source subject leaf).map RuleEmission.target =
      runLeaf relations source subject leaf := by
  simp only [runLeafEmissions, runLeaf, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro initial _
  rw [← MeTTaILFirstOrderRuleCompilation.runPremiseReceipts_bindings
    relations source leaf.plan.premises initial, List.map_map]
  rfl

theorem frontierEmissions_targets (program : Program) (subject : Pattern) :
    (frontierEmissions relations source (startFrontier program subject)).map RuleEmission.target =
      program.evalAll (runLeaf relations source subject) [lowerSubject subject] := by
  rw [frontierEmissions_start, OrderedDecisionRuleFusion.Program.evalAll_map]
  simp only [runLeafEmissions_targets]

/-! ## Local candidate enumeration up to administration

The source of this comparison consists of terminal firing receipts.  It is
not a language rewrite system: settling enumerates one finite matching and
premise search, including rejected alternatives, before any next invocation.
-/

/-- Provenance required at each phase reached by an annotated firing.  Early
decision phases have not selected a row; matching has selected its origin;
premise and instantiation phases have also retained its actual captures. -/
def ReceiptState.WellFormed (current : ReceiptState) : Prop :=
  match current.state with
  | .run .. | .dispatch .. | .prefilter .. | .bdDone .. => True
  | .bdRun .. | .bdRet .. => current.context.origin.isSome = true
  | .premises .. | .instantiate .. | .instantiateArguments .. | .instantiated .. | .done .. =>
      current.context.origin.isSome = true ∧ current.context.initialBindings.isSome = true

private theorem machineStep_wellFormed (current : ReceiptState) (well : current.WellFormed)
    {next : MachineState} (member : next ∈ machineStep relations source current.state) :
    (ReceiptState.mk next (retainFiringContext current.state current.context)).WellFormed := by
  rcases current with ⟨state, context⟩
  cases state with
  | run program subject cursor =>
      cases program with
      | failure => simp [machineStep] at member
      | drop program =>
          cases cursor <;> simp_all [machineStep, ReceiptState.WellFormed]
      | tryRule leaf patterns fallback =>
          simp only [machineStep, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> trivial
      | switch branches fallback =>
          cases cursor <;> simp only [machineStep, List.mem_cons, List.not_mem_nil, or_false] at member
          · subst next; trivial
          · rcases member with rfl | rfl <;> trivial
  | dispatch branches subject focused cursor =>
      cases branches with
      | nil => simp [machineStep] at member
      | cons key program branches =>
          simp only [machineStep] at member
          split at member <;> simp only [List.mem_singleton] at member <;> subst next <;> trivial
  | prefilter patterns cursor leaf subject =>
      cases patterns with
      | nil =>
          cases cursor with
          | nil =>
              simp only [machineStep, List.mem_singleton] at member
              subst next
              rfl
          | cons focused cursor => simp [machineStep] at member
      | cons pattern patterns =>
          cases cursor with
          | nil => simp [machineStep] at member
          | cons focused cursor =>
              cases pattern with
              | wildcard =>
                  simp only [machineStep, List.mem_singleton] at member
                  subst next
                  trivial
              | node head children =>
                  simp only [machineStep] at member
                  split at member
                  · simp only [List.mem_singleton] at member
                    subst next
                    trivial
                  · cases member
  | bdRun decision subject kont =>
      cases decision with
      | succeed =>
          simp only [machineStep, List.mem_singleton] at member
          subst next
          exact well
      | capture path name =>
          simp only [machineStep] at member
          split at member
          · simp only [List.mem_singleton] at member
            subst next
            exact well
          · cases member
      | checkBound path expected =>
          simp only [machineStep] at member
          split at member
          · split at member
            · simp only [List.mem_singleton] at member
              subst next
              exact well
            · cases member
          · cases member
      | checkConstructor path expected arity children =>
          simp only [machineStep] at member
          split at member
          · split at member
            · simp only [List.mem_singleton] at member
              subst next
              exact well
            · cases member
          · cases member
      | join head tail =>
          simp only [machineStep, List.mem_singleton] at member
          subst next
          exact well
  | bdRet bindings subject kont =>
      cases kont with
      | nil =>
          simp only [machineStep, List.mem_singleton] at member
          subst next
          trivial
      | cons frame kont =>
          cases frame with
          | joinRight tail =>
              simp only [machineStep, List.mem_singleton] at member
              subst next
              exact well
          | joinMerge headBindings =>
              simp only [machineStep] at member
              split at member
              · simp only [List.mem_singleton] at member
                subst next
                exact well
              · cases member
          | afterMatch queries template =>
              simp only [machineStep, List.mem_singleton] at member
              subst next
              exact ⟨well, rfl⟩
  | bdDone bindings => simp [machineStep] at member
  | premises queries template bindings =>
      cases queries with
      | nil =>
          simp only [machineStep, List.mem_singleton] at member
          subst next
          exact well
      | cons query queries =>
          simp only [machineStep, List.mem_map] at member
          obtain ⟨_, _, rfl⟩ := member
          exact well
  | instantiate template bindings kont =>
      cases template <;> simp only [machineStep, List.mem_singleton] at member <;>
        subst next <;> exact well
  | instantiateArguments constructor accumulated remaining bindings kont =>
      cases remaining <;> simp only [machineStep, List.mem_singleton] at member <;>
        subst next <;> exact well
  | instantiated value bindings kont =>
      cases kont with
      | nil =>
          simp only [machineStep, List.mem_singleton] at member
          subst next
          exact well
      | cons frame kont =>
          cases frame
          simp only [machineStep, List.mem_singleton] at member
          subst next
          exact well
  | done value => simp [machineStep] at member

/-- Actual query receipt updates retain both fields required by later phases. -/
theorem annotatedStep_wellFormed {current next : ReceiptState} (well : current.WellFormed)
    (member : next ∈ annotatedStep relations source current) : next.WellFormed := by
  rcases current with ⟨state, context⟩
  cases state <;> try
    (simp only [annotatedStep, List.mem_map] at member
     obtain ⟨_, member, rfl⟩ := member
     exact machineStep_wellFormed relations source _ well member)
  rename_i queries template bindings
  cases queries with
  | nil =>
      simp only [annotatedStep, List.mem_map] at member
      obtain ⟨_, member, rfl⟩ := member
      exact machineStep_wellFormed relations source _ well member
  | cons query queries =>
      simp only [annotatedStep, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact well

theorem startFrontier_wellFormed (program : Program) (subject : Pattern)
    {current : ReceiptState} (member : current ∈ startFrontier program subject) :
    current.WellFormed := by
  simp only [startFrontier, List.mem_singleton] at member
  subst current
  trivial

theorem frontierStep_wellFormed (pending : List ReceiptState)
    (well : ∀ current ∈ pending, current.WellFormed) {next : ReceiptState}
    (member : next ∈ (frontierStep relations source pending).pending) : next.WellFormed := by
  cases pending with
  | nil => simp [frontierStep] at member
  | cons current rest =>
      have currentWell := well current (List.mem_cons_self ..)
      have restWell : ∀ next ∈ rest, next.WellFormed := fun next present =>
        well next (List.mem_cons_of_mem _ present)
      cases state : current.state <;> simp only [frontierStep, state] at member
      all_goals try
        (rcases List.mem_append.mp member with advanced | retained
         · exact annotatedStep_wellFormed relations source currentWell advanced
         · exact restWell next retained)
      exact restWell next member

theorem runFrontier_wellFormed (fuel : Nat) (pending : List ReceiptState)
    (well : ∀ current ∈ pending, current.WellFormed) {next : ReceiptState}
    (member : next ∈ (runFrontier relations source fuel pending).pending) : next.WellFormed := by
  induction fuel generalizing pending with
  | zero => exact well next member
  | succ fuel ih =>
      exact ih _ (fun current present => frontierStep_wellFormed relations source pending well present) member

theorem runFrontier_start_wellFormed (program : Program) (subject : Pattern) (fuel : Nat)
    {current : ReceiptState}
    (member : current ∈ (runFrontier relations source fuel (startFrontier program subject)).pending) :
    current.WellFormed :=
  runFrontier_wellFormed relations source fuel _
    (fun _ present => startFrontier_wellFormed program subject present) member

/-- The provenance invariant restricts the existing machine; it does not
change or filter any of its successors. -/
abbrev ValidReceiptState := { current : ReceiptState // current.WellFormed }

def localStart (program : Program) (subject : Pattern) : ValidReceiptState :=
  ⟨⟨.run program subject [subject], {}⟩, trivial⟩

theorem localStart_frontier (program : Program) (subject : Pattern) :
    [(localStart program subject).val] = startFrontier program subject := rfl

/-- Every syntactic result is stable, including a result that would lack
provenance outside the invariant. -/
def localStable (current : ValidReceiptState) : Bool :=
  match current.val.state with
  | .done _ => true
  | _ => false

/-- The target's operational steps are the actual annotated steps, with only
the earned invariant attached to each successor. -/
def localTarget : Mettapedia.GSLT.Distinction.OrderedSystem ValidReceiptState where
  step current := (annotatedStep relations source current.val).attach.map fun next =>
    ⟨next.val, annotatedStep_wellFormed relations source current.property next.property⟩
  halted := localStable

theorem localTarget_step_erase (current : ValidReceiptState) :
    ((localTarget relations source).step current).map Subtype.val =
      annotatedStep relations source current.val := by
  simp [localTarget, List.map_map, Function.comp_def]

theorem localTarget_step_done (current : ValidReceiptState) (stable : localStable current = true) :
    (localTarget relations source).step current = [] := by
  rcases current with ⟨⟨state, context⟩, well⟩
  cases state <;> simp_all [localStable, localTarget, annotatedStep, machineStep]

/-- Settled valid states always carry a full actual firing receipt. -/
theorem localStable_emission (current : ValidReceiptState) (stable : localStable current = true) :
    ∃ emission, current.val.emission? = some emission := by
  rcases current with ⟨⟨state, context⟩, well⟩
  cases state <;> simp only [localStable, Bool.false_eq_true] at stable
  rename_i target
  obtain ⟨origin, originPresent⟩ := Option.isSome_iff_exists.mp well.1
  obtain ⟨initial, initialPresent⟩ := Option.isSome_iff_exists.mp well.2
  change context.origin = some origin at originPresent
  change context.initialBindings = some initial at initialPresent
  exact ⟨⟨origin, initial, context.bindings, context.choices, target⟩,
    by simp [ReceiptState.emission?, originPresent, initialPresent]⟩

private theorem emission_none_of_administrative (current : ValidReceiptState)
    (administrative : localStable current = false) : current.val.emission? = none := by
  cases published : current.val.emission? with
  | none => rfl
  | some emission =>
      have finished := emission?_target current.val emission published
      simp [localStable, finished] at administrative

/-- Source occurrences are terminal firing receipts from this one local
enumeration. There is no next language rewrite in this source system. -/
def localReceipts : Mettapedia.GSLT.Distinction.OrderedSystem (RuleEmission Nat) where
  step _ := []
  halted _ := true

/-- The block is the independently interpreted remaining candidate meaning,
not a recursive machine observation or a precomputed expected answer list. -/
def localBlock (occurrences : List (RuleEmission Nat)) (current : ValidReceiptState) : Prop :=
  occurrences = receiptMeaning relations source current.val

private theorem localStable_meaning (current : ValidReceiptState)
    (stable : localStable current = true) :
    ∃ emission, current.val.emission? = some emission ∧
      receiptMeaning relations source current.val = [emission] := by
  obtain ⟨emission, published⟩ := localStable_emission current stable
  have finished := emission?_target current.val emission published
  refine ⟨emission, published, ?_⟩
  rw [receiptMeaning_step]
  simp only [finished, published, Option.toList_some]

private theorem localTarget_meanings (current : ValidReceiptState) :
    (((localTarget relations source).step current).map
      (fun next => receiptMeaning relations source next.val)).flatten =
    (annotatedStep relations source current.val).flatMap (receiptMeaning relations source) := by
  rw [← localTarget_step_erase relations source current]
  rw [List.flatMap_map]
  rfl

/-- The actual finite candidate machine is a block simulation of terminal
receipts. Rejected candidates contribute zero occurrences and overlapping or
duplicate successes contribute their complete ordered blocks. -/
theorem localBlockSimulation : Mettapedia.GSLT.Distinction.BlockSimulation
    localReceipts (localTarget relations source) localStable (localBlock relations source) where
  stable_single := by
    intro occurrences current blocked stable
    obtain ⟨emission, _, meaning⟩ := localStable_meaning relations source current stable
    exact ⟨emission, blocked.trans meaning, stable⟩
  stable_step := by
    intro emission current _ stable
    refine ⟨[], ?_, rfl⟩
    rw [localTarget_step_done relations source current stable]
    exact .nil
  administrative_split := by
    intro occurrences current blocked administrative
    refine ⟨((localTarget relations source).step current).map
      (fun next => receiptMeaning relations source next.val), ?_, ?_⟩
    · exact List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl)
    · rw [localTarget_meanings]
      change occurrences = receiptMeaning relations source current.val at blocked
      rw [receiptMeaning_step] at blocked
      cases state : current.val.state <;> simp only [state] at blocked
      all_goals try exact blocked.symm
      simp [localStable, state] at administrative

/-- Rank decrease is inherited from the actual annotated machine step. -/
theorem localRanked : (localTarget relations source).AdministrationRanked localStable
    (fun current => machineRank current.val.state) := by
  intro current _ next member
  apply annotatedStep_rank relations source
  rw [← localTarget_step_erase relations source current]
  exact List.mem_map_of_mem member

/-- Settling past the local work rank preserves the entire ordered firing
list, with one actual valid terminal per full receipt. -/
theorem settle_receipts (current : ValidReceiptState) (fuel : Nat)
    (bound : machineRank current.val.state < fuel) :
    List.Forall₂ (fun emission settled => settled.val.emission? = some emission)
      (receiptMeaning relations source current.val)
      ((localTarget relations source).settle localStable fuel current) := by
  have settled := (localBlockSimulation relations source).block_settle
    (localRanked relations source) fuel bound (show localBlock relations source
      (receiptMeaning relations source current.val) current from rfl)
  apply settled.imp
  intro emission terminal pair
  obtain ⟨other, published, meaning⟩ := localStable_meaning relations source terminal pair.2
  have equal : emission = other := List.singleton_inj.mp (pair.1.trans meaning)
  exact equal ▸ published

theorem settle_start_receipts (program : Program) (subject : Pattern) :
    List.Forall₂ (fun emission settled => settled.val.emission? = some emission)
      (program.evalAll (runLeafEmissions relations source subject) [lowerSubject subject])
      ((localTarget relations source).settle localStable
        (machineRank (.run program subject [subject]) + 1) (localStart program subject)) :=
  settle_receipts relations source (localStart program subject) _ (Nat.lt_succ_self _)

/-- Full optional receipt readout of the actual settled states is literal list
equality; no stable state is omitted by a filtering observation. -/
theorem settle_receipts_readout (current : ValidReceiptState) (fuel : Nat)
    (bound : machineRank current.val.state < fuel) :
    (((localTarget relations source).settle localStable fuel current).map
      (fun terminal => terminal.val.emission?)) =
      (receiptMeaning relations source current.val).map some := by
  have pairs := settle_receipts relations source current fuel bound
  generalize receiptMeaning relations source current.val = emissions at pairs ⊢
  generalize (localTarget relations source).settle localStable fuel current = terminals at pairs ⊢
  induction pairs with
  | nil => rfl
  | cons published _ ih => simp only [List.map_cons, published, ih]

/-- Every observable firing receipt is a stable boundary. -/
theorem localObservableStable : Mettapedia.GSLT.Distinction.OrderedSystem.ObservableStable
    localStable (fun current => current.val.emission?) := by
  intro current visible
  cases stable : localStable current with
  | false => exact False.elim (visible (emission_none_of_administrative current stable))
  | true => rfl

/-- A dead administrative candidate has empty independent receipt meaning
and no firing publication. This licence concerns local firing receipts only;
it supplies no licence to erase an external effect or committed history. -/
theorem localErasureLicensed : (localTarget relations source).ErasureLicensed localStable
    (fun current => receiptMeaning relations source current.val = [] ∧
      current.val.emission? = none) := by
  intro current administrative dead
  refine ⟨?_, emission_none_of_administrative current administrative⟩
  have erased := localTarget_step_erase relations source current
  rw [dead, List.map_nil] at erased
  rw [receiptMeaning_step]
  cases state : current.val.state <;> simp only [← erased, List.flatMap_nil]
  simp [localStable, state] at administrative

/-- Administrative transitions publish no firing event in the real frontier
operation, independently of the retained candidate provenance. -/
theorem localAdministrationSilent : (localTarget relations source).AdministrationSilent localStable
    (fun current _ => (frontierStep relations source [current.val]).emissions) := by
  intro current administrative _ _
  rcases current with ⟨⟨state, context⟩, well⟩
  cases state <;> simp_all [localStable, frontierStep]

namespace ReceiptControls

private def value : Pattern := .apply "Left" []
private def other : Pattern := .apply "Right" []
private def input : Pattern := .apply "Input" []
private def fixtureLanguage : LanguageDef := LanguageDef.empty "ordered-receipts"

private def provider : RelationEnv where
  tuples relation _ :=
    if relation = "pick" then
      [[.apply "Other" []], [.apply "Box" [value]], [.apply "Box" [value]]]
    else []

private def query : PremisePlan :=
  ⟨"pick", [.application "Box" [.metavariable "x"]]⟩

private def providerLeaf : Leaf :=
  ⟨4, ⟨.succeed, [query], .metavariable "x"⟩⟩

private def providerProgram : Program :=
  .tryRule providerLeaf [.wildcard] .failure

private def completed : OrderedCut :=
  runFrontier provider fixtureLanguage 15 (startFrontier providerProgram input)

/-- Failed row zero does not emit; equal successful rows keep their original
positions one and two. -/
theorem failed_and_duplicate_provider_rows :
    completed.emissions.map (fun emission => emission.choices.map (fun choice => choice.rowIndex)) =
      [[1], [2]] := by decide +kernel

theorem equal_provider_targets_remain_two :
    completed.emissions.map RuleEmission.target = [value, value] := by decide +kernel

theorem provider_bindings_are_actual :
    completed.emissions.map (fun emission => (emission.initialBindings, emission.bindings)) =
      [([], [("x", value)]), ([], [("x", value)])] := by decide +kernel

theorem provider_completed : completed.pending = [] := by
  apply List.eq_nil_of_length_eq_zero
  decide +kernel

/-- Pausing immediately after one publication retains the second premise
continuation and the failed fallback; it does not restart the first firing. -/
theorem provider_pause_retains_frontier :
    let paused := runFrontier provider fixtureLanguage 10 (startFrontier providerProgram input)
    paused.emissions.map RuleEmission.target = [value] ∧
      paused.pending.length = 2 ∧
      (runFrontier provider fixtureLanguage 5 paused.pending).emissions.map
        (fun emission => emission.choices.map (fun choice => choice.rowIndex)) = [[2]] := by
  decide +kernel

/-- A deliberate restart repeats the already published provider occurrence. -/
theorem restarting_replays_provider_row :
    let start := startFrontier providerProgram input
    let paused := runFrontier provider fixtureLanguage 10 start
    let restarted := runFrontier provider fixtureLanguage 15 start
    (paused.emissions ++ restarted.emissions).map
      (fun emission => emission.choices.map (fun choice => choice.rowIndex)) = [[1], [1], [2]] := by
  decide +kernel

/-- Equal targets do not justify dropping a retained provider occurrence. -/
theorem dropping_equal_receipt_changes_observation :
    (completed.emissions.take 1).length ≠ completed.emissions.length := by decide +kernel

theorem reversing_equal_receipts_changes_choices :
    completed.emissions.reverse.map
        (fun emission => emission.choices.map (fun choice => choice.rowIndex)) ≠
      completed.emissions.map
        (fun emission => emission.choices.map (fun choice => choice.rowIndex)) := by
  decide +kernel

private def constantLeaf (origin : Nat) : Leaf :=
  ⟨origin, ⟨.succeed, [], .application "Same" []⟩⟩

private def overlapProgram : Program :=
  .switch
    (.cons (subjectKey input)
      (.tryRule (constantLeaf 7) [] (.tryRule (constantLeaf 9) [] .failure)) .nil)
    (.tryRule (constantLeaf 11) [.wildcard] .failure)

/-- The constructor branch precedes the overlapping default, and equal
targets preserve all three distinct rule occurrences. -/
theorem switch_overlap_order :
    (runFrontier provider fixtureLanguage 40 (startFrontier overlapProgram input)).emissions.map
      RuleEmission.origin = [7, 9, 11] := by decide +kernel

theorem equal_targets_do_not_deduplicate :
    (runFrontier provider fixtureLanguage 40 (startFrontier overlapProgram input)).emissions.length = 3 := by
  decide +kernel

private def nonlinearPlan : RulePlan :=
  { name := "Repeated"
    typeContext := []
    premises := []
    left := .application "Pair" [.metavariable "x", .metavariable "x"]
    right := .application "Accepted" [] }

private def nonlinearProgram : Program :=
  .tryRule ⟨0, toMachinePlan nonlinearPlan⟩ [.wildcard] .failure

/-- A conflicting nonlinear candidate has pending work initially and an empty
completed observation.  Those cuts have different remaining control. -/
theorem nonlinear_failure_pending_then_completed :
    let start := startFrontier nonlinearProgram (.apply "Pair" [value, other])
    (runFrontier provider fixtureLanguage 0 start).emissions = [] ∧
      (runFrontier provider fixtureLanguage 0 start).pending.length = 1 ∧
      (runFrontier provider fixtureLanguage 40 start).emissions = [] ∧
      (runFrontier provider fixtureLanguage 40 start).pending = [] := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · apply List.eq_nil_of_length_eq_zero
    decide +kernel
  · apply List.eq_nil_of_length_eq_zero
    decide +kernel

private def deepPlan : Nat → PatternPlan
  | 0 => .metavariable "x"
  | depth + 1 => .application "Nest" [deepPlan depth]

private def deepTerm (payload : Pattern) : Nat → Pattern
  | 0 => payload
  | depth + 1 => .apply "Nest" [deepTerm payload depth]

private theorem deep_match (depth : Nat) (payload : Pattern) :
    (deepPlan depth).run (deepTerm payload depth) = [[("x", payload)]] := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [deepPlan, deepTerm, PatternPlan.run, MeTTaILFirstOrderRuleCompilation.runPlans,
        ih, mergeBindings]

/-- Arbitrary constructor depth still returns the captured literal tree. -/
theorem arbitrary_depth_literal (depth : Nat) (payload : Pattern) :
    let plan : RulePlan :=
      { name := "Deep"
        typeContext := []
        premises := []
        left := deepPlan depth
        right := .metavariable "x" }
    let program : Program := .tryRule ⟨0, toMachinePlan plan⟩ [.wildcard] .failure
    (frontierEmissions provider fixtureLanguage (startFrontier program (deepTerm payload depth))).map
      RuleEmission.target = [payload] := by
  dsimp only
  rw [frontierEmissions_targets]
  simp [OrderedDecisionRuleFusion.Program.evalAll, OPM.structuralMatchList,
    OPM.structuralMatch, runLeaf_toMachinePlan, RulePlan.run, deep_match,
    MeTTaILFirstOrderRuleCompilation.runPremisePlans, PatternPlan.instantiate]

/-- A constructor that looks like an evaluation request is retained as data. -/
theorem callable_looking_literal :
    let payload := Pattern.apply "!" [.apply "Tick" []]
    let plan : RulePlan :=
      { name := "Literal"
        typeContext := []
        premises := []
        left := .metavariable "x"
        right := .metavariable "x" }
    let program : Program := .tryRule ⟨0, toMachinePlan plan⟩ [.wildcard] .failure
    (runFrontier provider fixtureLanguage 20 (startFrontier program payload)).emissions.map
      RuleEmission.target = [payload] := by decide +kernel

private def providerSettled : List ValidReceiptState :=
  (localTarget provider fixtureLanguage).settle localStable
    (machineRank (.run providerProgram input [input]) + 1) (localStart providerProgram input)

/-- Actual block settlement keeps both equal results and their different
provider-row occurrences, in their original order. -/
theorem settled_provider_duplicates :
    providerSettled.map (fun terminal => terminal.val.emission?.map
      (fun emission => (emission.target, emission.choices.map (fun choice => choice.rowIndex)))) =
      [some (value, [1]), some (value, [2])] := by
  have receipts := settle_receipts_readout provider fixtureLanguage
    (localStart providerProgram input) _ (Nat.lt_succ_self _)
  calc
    _ = (receiptMeaning provider fixtureLanguage (localStart providerProgram input).val).map
        (fun emission => some (emission.target, emission.choices.map (fun choice => choice.rowIndex))) := by
      simpa only [providerSettled, localStart, List.map_map, Function.comp_def, Option.map_some] using
        congrArg (List.map (Option.map
          (fun emission => (emission.target, emission.choices.map (fun choice => choice.rowIndex))))) receipts
    _ = _ := by cbv

/-- Rejected matching candidates settle to no receipts or stable states. -/
theorem rejected_candidate_settles_empty :
    (localTarget provider fixtureLanguage).settle localStable
      (machineRank (.run nonlinearProgram (.apply "Pair" [value, other])
        [.apply "Pair" [value, other]]) + 1)
      (localStart nonlinearProgram (.apply "Pair" [value, other])) = [] := by
  have pairs := settle_start_receipts provider fixtureLanguage nonlinearProgram
    (.apply "Pair" [value, other])
  apply List.eq_nil_of_length_eq_zero
  rw [← pairs.length_eq]
  decide +kernel

/-- A raw malformed terminal would publish nothing, but it fails the
reachable-provenance invariant and cannot be silently treated as rejection. -/
theorem malformed_terminal_excluded (target : Pattern) :
    (ReceiptState.mk (.done target) {}).emission? = none ∧
      ¬ (ReceiptState.mk (.done target) {}).WellFormed := by
  exact ⟨rfl, by simp [ReceiptState.WellFormed]⟩

#print axioms settled_provider_duplicates
#print axioms rejected_candidate_settles_empty
#print axioms malformed_terminal_excluded

#print axioms failed_and_duplicate_provider_rows
#print axioms equal_provider_targets_remain_two
#print axioms provider_bindings_are_actual
#print axioms provider_completed
#print axioms provider_pause_retains_frontier
#print axioms restarting_replays_provider_row
#print axioms dropping_equal_receipt_changes_observation
#print axioms reversing_equal_receipts_changes_choices
#print axioms switch_overlap_order
#print axioms equal_targets_do_not_deduplicate
#print axioms nonlinear_failure_pending_then_completed
#print axioms arbitrary_depth_literal
#print axioms callable_looking_literal

end ReceiptControls

#print axioms allEmissions_eq_receiptMeaning
#print axioms evalAll_mapProgram
#print axioms evalBranchAll_mapBranches
#print axioms frontierEmissions_start
#print axioms runFrontier_start_observation
#print axioms runFrontier_start_completed
#print axioms frontierEmissions_mapProgram
#print axioms runFrontier_mapProgram_completed
#print axioms runLeafEmissions_targets
#print axioms frontierEmissions_targets

#print axioms runLeafEmissions_toMachinePlan

#print axioms frontierStep_observation
#print axioms allEmissions_unfold
#print axioms completionWork_unfold
#print axioms frontierStep_work
#print axioms runFrontier_observation
#print axioms completionWork_pos
#print axioms frontierWork_eq_zero
#print axioms runFrontier_completed
#print axioms runFrontier_emissions_of_completed

#print axioms machineStep_rank
#print axioms annotatedStep_rank

#print axioms annotatedStep_wellFormed
#print axioms startFrontier_wellFormed
#print axioms frontierStep_wellFormed
#print axioms runFrontier_wellFormed
#print axioms runFrontier_start_wellFormed
#print axioms localStart_frontier
#print axioms localTarget_step_erase
#print axioms localTarget_step_done
#print axioms localStable_emission
#print axioms localBlockSimulation
#print axioms localRanked
#print axioms settle_receipts
#print axioms settle_start_receipts
#print axioms settle_receipts_readout
#print axioms localObservableStable
#print axioms localErasureLicensed
#print axioms localAdministrationSilent

#print axioms reaches_iff_mem_evalAll
#print axioms languageReaches_iff_mem_evalAll
#print axioms languageReaches_mapProgram_iff

end Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
