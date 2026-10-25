import Mettapedia.OSLF.MeTTaIL.StructuralDescentAdmission
import Mettapedia.OSLF.MeTTaIL.StructuralDescentFiniteServices
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionFrames

/-!
# Generic finite-depth execution of typed recursive premises

Every recursive call visits all original declaration indices. Its source and
binders are read from the authored premise, not from a language-specific
congruence table. Root and target matches use the complete certified matcher;
finite provider calls use the complete query machine. Successful receipts
carry the independent `RootFiring` judgment and every ordered child history.

The depth parameter bounds nested rule calls only. It is not an operational
step count, a work budget, or an exhaustive-coverage certificate by itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Execution

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

structure RootAnswer (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) where
  index : Nat
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  completed : Assignment
  history : List Event
  target : Pattern
  valid : RootFiring environment bound type source index trace captured completed history target

abbrev Oracle (environment : Environment) :=
  ∀ bound type source, List (RootAnswer environment bound type source)

structure PremiseAnswer (environment : Environment) (context : Context)
    (premise : Premise) (initial : Assignment) where
  assignment : Assignment
  event : Event
  valid : PremiseHolds environment context premise initial assignment event

structure PremisesAnswer (environment : Environment) (context : Context)
    (premises : List Premise) (initial : Assignment) where
  assignment : Assignment
  history : List Event
  valid : PremisesHold environment context premises initial assignment history

structure ElementsAnswer (environment : Environment) (context : Context)
    (parameter : String) (body : Premise) (index : Nat)
    (elements : List Pattern) (initial : Assignment) where
  assignment : Assignment
  history : List (Nat × Pattern × List Event)
  valid : QuantifiedElements environment context parameter body index elements initial assignment history

def runElements (environment : Environment) (context : Context)
    (parameter : String) (body : Premise)
    (executeBody : ∀ initial, List (PremiseAnswer environment context.quantified body initial)) :
    (index : Nat) → (elements : List Pattern) → (initial : Assignment) →
      List (ElementsAnswer environment context parameter body index elements initial)
  | _, [], initial => [⟨initial, [], .nil⟩]
  | index, element :: elements, initial =>
      let localAssignment := bindParameter parameter (localValue context.bound element) initial
      if checked : checkTypedAssignment environment context.quantified localAssignment then
        (executeBody localAssignment).flatMap fun answer =>
          (runElements environment context parameter body executeBody (index + 1) elements
            initial).map fun rest =>
              ⟨rest.assignment, (index, element, [answer.event]) :: rest.history,
                .cons (checkTypedAssignment_sound checked) answer.valid rest.valid⟩
      else []

def runStep (environment : Environment) (oracle : Oracle environment)
    (call : GeneralPremise.Execution.StepCall environment) :
    List (PremiseAnswer environment call.context call.premise call.initial) :=
  (oracle (call.binders ++ call.context.bound) call.type call.source).flatMap fun child =>
    let request : GeneralScopedMatchMachine.Request :=
      ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
        [], call.binders.length, call.initial, call.targetSchema, child.target⟩
    (FiniteServices.Matcher.answers request).filterMap fun matched =>
      if checked : checkTypedAssignment environment call.context matched.val.assignment then
        some ⟨matched.val.assignment,
          .child call.context.premiseIndex call.context.quantifierDepth child.index
            (call.binders ++ call.context.bound) call.source child.target child.trace matched.val.trace
            child.captured child.completed child.history,
          call.conclude _ _ _ _ _ _ _ _ child.valid matched.property
            (checkTypedAssignment_sound checked)⟩
      else none

def runPremise (environment : Environment) (oracle : Oracle environment)
    (context : Context) (premise : Premise) (initial : Assignment) :
    List (PremiseAnswer environment context premise initial) :=
  match premise with
  | .relationQuery relation arguments =>
      let request : Query.Request := ⟨context, relation, arguments, initial⟩
      (FiniteServices.Provider.answers environment request).map fun answer =>
        ⟨answer.assignment, .query context.premiseIndex context.quantifierDepth
          answer.rowIndex answer.origins, .query answer.valid⟩
  | .freshness condition =>
      match read : freshnessSubject? context.rule context.spec context.bound context.premiseIndex
          context.quantifierDepth initial condition with
      | none => []
      | some (atom, subject) =>
          if checked : Substitution.isFresh atom subject then
            [⟨initial, .freshness context.premiseIndex context.quantifierDepth atom subject,
              .freshness read ((syntactic_freshness_iff atom subject).mp checked)⟩]
          else []
  | .congruence source target =>
      match typed : sourceType? environment.language context.rule source with
      | none => []
      | some type =>
          match interpreted : instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source with
          | none => []
          | some actualSource =>
              runStep environment oracle {
                context := context, premise := .congruence source target,
                initial := initial, binders := [], type := type,
                source := actualSource, targetSchema := target,
                conclude := fun _ _ _ _ _ _ _ _ child matched finalTyped =>
                  .step typed interpreted child matched finalTyped }
  | .scopedStep step =>
      match interpreted : instantiateAt? context.rule context.spec context.bound.length
          (context.site 0) [] step.binders.length initial step.source with
      | none => []
      | some actualSource =>
          runStep environment oracle {
            context := context, premise := .scopedStep step,
            initial := initial, binders := step.binders, type := step.resultType,
            source := actualSource, targetSchema := step.target,
            conclude := fun _ _ _ _ _ _ _ _ child matched finalTyped =>
              .scopedStep interpreted child matched finalTyped }
  | .forAll collection parameter body =>
      match read : finiteCollection? context.bound.length initial collection with
      | none => []
      | some (kind, elements) =>
          (runElements environment context parameter body
            (runPremise environment oracle context.quantified body) 0 elements initial).map fun answer =>
              ⟨answer.assignment,
                .quantified context.premiseIndex context.quantifierDepth kind answer.history,
                .quantified read answer.valid⟩
termination_by sizeOf premise

def runPremises (environment : Environment) (oracle : Oracle environment)
    (context : Context) (premises : List Premise) (initial : Assignment) :
    List (PremisesAnswer environment context premises initial) :=
  match premises with
  | [] => [⟨initial, [], .nil⟩]
  | premise :: premises =>
      (runPremise environment oracle context premise initial).flatMap fun answer =>
        (runPremises environment oracle context.next premises answer.assignment).map fun rest =>
          ⟨rest.assignment, answer.event :: rest.history, .cons answer.valid rest.valid⟩

/-- The shared continuation after a root matcher has produced checked scoped
captures. Matcher backends differ only before this boundary; capture typing,
premises, reflective instantiation and target typing stay on this one path. -/
def finishRootMatch (environment : Environment) (oracle : Oracle environment)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (matched : {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩}) :
    List (RootAnswer environment bound type source) :=
  let context : Context := ⟨index, rule, spec, bound, 0, 0⟩
  if capturedTyped : checkTypedAssignment environment context matched.val.assignment then
    (runPremises environment oracle context rule.premises matched.val.assignment).filterMap fun answer =>
      match converted : reductWith? (ScopedReflectiveExecution.binderOperation
          environment.reflection rule) rule spec bound.length answer.assignment with
      | none => none
      | some target =>
          if targetTyped : checkOpenPatternWellSorted environment.language environment.free bound type target then
            some ⟨index, matched.val.trace, matched.val.assignment, answer.assignment,
              answer.history, target,
              .fire declared specified admitted sourceTyped matched.property
                (checkTypedAssignment_sound capturedTyped) answer.valid converted
                (checkOpenPatternWellSorted_sound targetTyped)⟩
          else none
  else []

def runRoot (environment : Environment) (oracle : Oracle environment)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat) :
    List (RootAnswer environment bound type source) :=
  match declared : environment.language.rewrites[index]? with
  | none => []
  | some rule =>
      match specified : specification? environment index with
      | none => []
      | some spec =>
          if admitted : admittedFor rule spec then
            if sorted : checkOpenPatternWellSorted environment.language environment.free bound type source then
              let request : GeneralScopedMatchMachine.Request :=
                ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
              (FiniteServices.Matcher.answers request).flatMap fun matched =>
                finishRootMatch environment oracle bound type source index rule spec
                  declared specified admitted (checkOpenPatternWellSorted_sound sorted) matched
            else []
          else []

/-- Recursive search uses the same finite authored declaration catalogue at
every depth. Self-recursive LamCong/AppCong declarations are therefore visited.
The generic structural admission check earns a complete depth separately. -/
def roots (environment : Environment) : Nat → Oracle environment
  | 0, _, _, _ => []
  | depth + 1, bound, type, source =>
      (List.range environment.language.rewrites.length).flatMap fun index =>
        runRoot environment (roots environment depth) bound type source index

theorem roots_sound (environment : Environment) (depth : Nat)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : RootAnswer environment bound type source)
    (_member : answer ∈ roots environment depth bound type source) :
    RootFiring environment bound type source answer.index answer.trace answer.captured
      answer.completed answer.history answer.target := answer.valid

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Execution
