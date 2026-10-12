import Mettapedia.OSLF.MeTTaIL.GeneralRhoSites
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseResolvedTrees
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTotalityReadiness
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCaptureRepresentations
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesFocus
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobResolution

/-!
# Universal resolved COMM execution in the selected rho profile

The original COMM schema captures an arbitrary input body with its Name
dependency, an arbitrary payload, and the actual finite residual bag. The
proof uses the independent match derivation and the actual typed-assignment
gate. It does not reconstruct a selected source family or assume the rest
capture's representation from its declared type alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution GeneralExecutionAdmission
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

def commContext (bound : List TypeExpr) : Context := ⟨0, comm, scopedCommBindingSpec, bound, 0, 0⟩

theorem body_dependency : dependencies? scopedCommBindingSpec "p" = some [.name] := by decide +kernel
theorem payload_dependency : dependencies? scopedCommBindingSpec "q" = some [] := by decide +kernel
theorem rest_dependency : dependencies? scopedCommBindingSpec "rest" = some [] := by decide +kernel
theorem rest_type : comm.typeContext.lookup "rest" = some (.collection .hashBag .proc) := by decide +kernel

theorem typed_body_capture {bound : List TypeExpr} {assignment : Assignment} {value : ContextualValue}
    (typed : TypedAssignment executionEnvironment (commContext bound) assignment)
    (found : lookup assignment "p" = some value) :
    value = bodyValue bound.length value.body ∧ value.body.isWellScopedAt (bound.length + 1) = true := by
  obtain ⟨dependencies, expected, declared, _, metadata, ambient, sorted⟩ :=
    typed.1 "p" value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  have deps : dependencies = [.name] := Option.some.inj (declared.symm.trans body_dependency)
  have scopeProof := sorted.isWellScopedAt
  simp only [deps, List.length_append, List.length_cons, List.length_nil] at scopeProof
  have sameDeps : value.dependencies = [.name] := metadata.trans deps
  have same : value = bodyValue bound.length value.body := by
    cases value with
    | mk actual caller body =>
        simp only at sameDeps
        simp only [commContext] at ambient
        subst actual caller
        rfl
  exact ⟨same, by simpa only [commContext, Nat.zero_add, Nat.add_comm] using scopeProof⟩

theorem typed_root_capture {bound : List TypeExpr} {assignment : Assignment} {value : ContextualValue}
    {name : String} (declaredName : dependencies? scopedCommBindingSpec name = some [])
    (typed : TypedAssignment executionEnvironment (commContext bound) assignment)
    (found : lookup assignment name = some value) :
    value = rootValue bound.length value.body ∧ value.body.isWellScopedAt bound.length = true := by
  obtain ⟨dependencies, expected, declared, _, metadata, ambient, sorted⟩ :=
    typed.1 name value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  have deps : dependencies = [] := Option.some.inj (declared.symm.trans declaredName)
  have scopeProof := sorted.isWellScopedAt
  simp only [deps, List.nil_append] at scopeProof
  have sameDeps : value.dependencies = [] := metadata.trans deps
  have same : value = rootValue bound.length value.body := by
    cases value with
    | mk actual caller body =>
        simp only at sameDeps
        simp only [commContext] at ambient
        subst actual caller
        rfl
  exact ⟨same, scopeProof⟩

theorem matching_names {ambient : Nat} {source : Pattern} {assignment : Assignment}
    (matching : GeneralScopedMatch.Matches comm scopedCommBindingSpec ambient .left [] 0 []
      comm.left source assignment) : BoundNames assignment ["n", "p", "n", "q", "rest"] := by
  have names : comm.left.freeFvarNames = ["n", "p", "n", "q", "rest"] := by
    change (Pattern.collection .hashBag
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest")).freeFvarNames = _
    simp [Pattern.freeFvarNames]
  simpa only [names] using matching_bound_names matching

theorem universal_reduct_total {bound : List TypeExpr} {source : Pattern} {assignment : Assignment}
    (matching : GeneralScopedMatch.Matches comm scopedCommBindingSpec bound.length .left [] 0 []
      comm.left source assignment)
    (typed : TypedAssignment executionEnvironment (commContext bound) assignment)
    (operation : Pattern → Pattern → Pattern) :
    ∃ target, reductWith? operation comm scopedCommBindingSpec bound.length assignment = some target := by
  have names := matching_names matching
  obtain ⟨processValue, processFound⟩ := names "p" (by simp)
  obtain ⟨payloadValue, payloadFound⟩ := names "q" (by simp)
  have finite := matching_finite_restCaptures matching
  have restNames : restCaptureNames comm.left = ["rest"] := by
    change restCaptureNames (Pattern.collection .hashBag
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest")) = _
    simp [restCaptureNames]
  rw [restNames] at finite
  obtain ⟨restValue, kind, residual, restFound, restShape⟩ := finite "rest" (by simp)
  obtain ⟨dependencies, expected, declared, declaredType, metadata, ambient, sorted⟩ :=
    typed.1 "rest" restValue (ConditionalEquationExecution.lookup_assignment_member _ _ _ restFound)
  have deps : dependencies = [] := Option.some.inj (declared.symm.trans rest_dependency)
  have expectedType : expected = .collection .hashBag .proc :=
    Option.some.inj (declaredType.symm.trans rest_type)
  rw [deps, List.nil_append, expectedType, restShape] at sorted
  have kindSame : kind = .hashBag := by cases sorted; rfl
  subst kind
  obtain ⟨processSame, processScope⟩ := typed_body_capture typed processFound
  obtain ⟨payloadSame, payloadScope⟩ := typed_root_capture payload_dependency typed payloadFound
  obtain ⟨restSame, restScope⟩ := typed_root_capture rest_dependency typed restFound
  have processRead : instantiateValue? processValue bound.length 1 [.bvar 0] = some processValue.body := by
    rw [processSame]
    exact instantiate_body processScope
  have payloadRead : instantiateValue? payloadValue bound.length 0 [] = some payloadValue.body := by
    rw [payloadSame]
    exact instantiate_root payloadScope
  have restRead : instantiateValue? restValue bound.length 0 [] = some (.collection .hashBag residual none) := by
    rw [restSame]
    simpa only [restShape] using instantiate_root restScope
  have processArguments : arguments? comm scopedCommBindingSpec "p" .right [0, 0] = some [.bvar 0] := by decide +kernel
  have payloadArguments : arguments? comm scopedCommBindingSpec "q" .right [0, 1, 0] = some [] := by decide +kernel
  have restArguments : arguments? comm scopedCommBindingSpec "rest" .right [1] = some [] := by decide +kernel
  refine ⟨.collection .hashBag (operation (.apply "NQuote" [payloadValue.body]) processValue.body :: residual) none, ?_⟩
  unfold reductWith?
  change instantiateWith? operation comm scopedCommBindingSpec bound.length .right [] 0 assignment
    (.collection .hashBag [.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])] (some "rest")) = _
  simp only [instantiateWith?, instantiateArgsWith?, List.nil_append, List.cons_append,
    processFound, payloadFound, restFound, processArguments, payloadArguments, restArguments,
    processRead, payloadRead, restRead, Option.bind_eq_bind, Option.bind_some,
    Nat.zero_add, List.length_singleton]
  rfl

def resolved_comm_body {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (declared : executionEnvironment.language.rewrites[0]? = some comm)
    (specified : specification? executionEnvironment 0 = some scopedCommBindingSpec)
    (admitted : admittedFor comm scopedCommBindingSpec = true)
    (sorted : OpenPatternWellSorted executionEnvironment.language executionEnvironment.free bound type source)
    (matching : GeneralScopedMatchMachine.TracedMatches comm scopedCommBindingSpec bound.length .left [] 0 []
      comm.left source trace captured)
    (typed : TypedAssignment executionEnvironment (commContext bound) captured)
    (outer : Goal) (tail : Continuation executionEnvironment (.root bound type source 0) outer)
    (continued : ResolvedContinued executionEnvironment outer _ tail) :
    ResolvedTree executionEnvironment outer
      (.evaluate (.premises (commContext bound) [] captured)
        (.rootBody bound type source 0 comm scopedCommBindingSpec declared specified admitted sorted
          trace captured matching typed tail)) := by
  refine .branch rfl (.cons ?_ (.nil _ _))
  have projected : (reductWith?
      (ScopedReflectiveExecution.binderOperation executionEnvironment.reflection comm)
      comm scopedCommBindingSpec bound.length captured).isSome = true :=
    Option.isSome_iff_exists.mpr (universal_reduct_total matching.matching typed _)
  apply ResolvedTree.branch
  · simp only [expand, delivered]
    split
    rename_i actual current history held same
    cases same
    split
    · rename_i absent
      rw [absent] at projected
      cases projected
    · split <;> rfl
  · simp only [expand, delivered]
    split
    rename_i actual current history held same
    cases same
    split
    · rename_i absent
      rw [absent] at projected
      cases projected
    · split
      · exact .cons (continued _) (.nil _ _)
      · exact .nil _ _

theorem selected_comm : executionEnvironment.language.rewrites[0]? = some comm := by
  have position : plan.rules[0]? = some declaration := by rw [compiled_rules]; rfl
  exact GeneralPlanEnvironment.selected_rule plan position

theorem specified_comm : specification? executionEnvironment 0 = some scopedCommBindingSpec := by
  have position : plan.rules[0]? = some declaration := by rw [compiled_rules]; rfl
  exact GeneralPlanEnvironment.selected_specification plan position

def resolved_comm_root {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sorted : OpenPatternWellSorted executionEnvironment.language executionEnvironment.free bound type source)
    (outer : Goal) (tail : Continuation executionEnvironment (.root bound type source 0) outer)
    (continued : ResolvedContinued executionEnvironment outer _ tail) :
    ResolvedTree executionEnvironment outer (.evaluate (.root bound type source 0) tail) := by
  have checked := checkOpenPatternWellSorted_complete sorted
  apply ResolvedTree.branch
  · apply checkGoalReady_sound
    simp only [checkGoalReady, selected_comm, specified_comm, comm_admitted, checked, Bool.and_self]
  · simp only [expand, evaluate]
    unfold evaluateRoot
    split
    · rename_i absent
      rw [selected_comm] at absent
      cases absent
    · rename_i rule found
      have same : rule = comm := Option.some.inj (found.symm.trans selected_comm)
      subst rule
      split
      · rename_i absent
        rw [specified_comm] at absent
        cases absent
      · rename_i spec found
        have same : spec = scopedCommBindingSpec := Option.some.inj (found.symm.trans specified_comm)
        subst spec
        split
        · exact .cons
            (resolvedRootMatch _ _ _ (fun answer valid typed =>
              resolved_comm_body selected_comm specified_comm comm_admitted
                (checkOpenPatternWellSorted_sound checked) valid typed outer tail continued)) (.nil _ _)
        · rename_i rejected
          exact False.elim (rejected comm_admitted)

theorem comm_root_resolved {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sorted : OpenPatternWellSorted executionEnvironment.language executionEnvironment.free bound type source) :
    (Execution.finish executionEnvironment (.root bound type source 0)).unresolved = [] :=
  finish_resolved_of_tree _ _ (resolved_comm_root sorted _ _ (resolvedDone _ _))

theorem rule_job_resolved {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {job : GeneralRuleJobs.Job}
    (sourceTyped : OpenPatternWellSorted language snapshot.free bound type source)
    (licensed : job.Valid plan bound type source) :
    (GeneralRuleJobExecution.finishState ⟨plan, bound, type, source, job⟩ licensed).unresolved = [] := by
  apply GeneralRuleJobExecution.finishState_resolved
  have sorted := licensed.2.focus_sorted sourceTyped.2.1
  have position := licensed.1
  rw [compiled_rules] at position
  change (job.declaration, job.ordinal) ∈ [(declaration, 0)] at position
  have index : job.ordinal = 0 := congrArg Prod.snd (List.mem_singleton.mp position)
  change (Execution.finish executionEnvironment
    (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).unresolved = []
  rw [index]
  exact comm_root_resolved sorted

#print axioms universal_reduct_total
#print axioms comm_root_resolved
#print axioms rule_job_resolved

end Mettapedia.OSLF.MeTTaIL.GeneralRho
