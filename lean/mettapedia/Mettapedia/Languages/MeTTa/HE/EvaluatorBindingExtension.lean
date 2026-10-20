import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Evaluator binding-theory extension

Recursive evaluation may add constraints, but it must not forget constraints
already visible at its input.  This module states that property semantically:
every model of an output binding record is also a model of the input record.

A type service supplies the two primitive extension laws used by evaluator
dispatch. The remaining control steps derive extension from the exact
solution theory of specification matching and merging. Concrete service
realizations consume these laws downstream; they are not dependencies of the
evaluator preservation theorem.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Eval.Steps
open Spec.Match.SolutionTheory
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement

/-- `output` presents at least every constraint presented by `input`. -/
def BindingTheoryExtends (input output : Bindings) : Prop :=
  ∀ valuation, TypeBindingSatisfied valuation output →
    TypeBindingSatisfied valuation input

namespace BindingTheoryExtends

@[simp] theorem refl (bindings : Bindings) :
    BindingTheoryExtends bindings bindings := by
  intro _ satisfied
  exact satisfied

theorem trans {first second third : Bindings}
    (left : BindingTheoryExtends first second)
    (right : BindingTheoryExtends second third) :
    BindingTheoryExtends first third := by
  intro valuation satisfied
  exact left valuation (right valuation satisfied)

theorem of_presentationExtension {input output : Bindings}
    {presentation : Spec.Type.Presentation.TypeSubst}
    (extension : PresentationExtensionRel input presentation output) :
    BindingTheoryExtends input output := by
  intro valuation satisfied
  exact (extension valuation).mp satisfied |>.1

end BindingTheoryExtends

/-- The two binding-extension obligations owned by an evaluator type service.
Lookup is absent because it returns types without changing bindings. -/
structure EvalTypeServiceBindingLaws (typing : EvalTypeService) : Prop where
  typeCast : ∀ {protectedScope space atom expectedType input result},
    typing.typeCast protectedScope space atom expectedType input result →
      BindingTheoryExtends input result.2
  candidateScanSuccess : ∀ {scope space expression expectedType input candidates
      policy output},
    typing.candidateScan scope space expression expectedType input candidates
        (.success policy output) →
      BindingTheoryExtends input output

/-- Specification merging conjoins its two input theories, so its output
extends the left input. -/
theorem mergeRel_extends_left {left right output : Bindings}
    (merge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right output) :
    BindingTheoryExtends left output := by
  intro valuation outputSatisfied
  apply (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    valuation left).mpr
  exact ((mergeRel_solution_iff merge
    (fun name => encodeModelAtom (valuation name))).mp
      ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        valuation output).mp outputSatisfied)).1

/-- Specification merging conjoins its two input theories, so its output
also extends the right input. -/
theorem mergeRel_extends_right {left right output : Bindings}
    (merge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right output) :
    BindingTheoryExtends right output := by
  intro valuation outputSatisfied
  apply (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    valuation right).mpr
  exact ((mergeRel_solution_iff merge
    (fun name => encodeModelAtom (valuation name))).mp
      ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        valuation output).mp outputSatisfied)).2

/-- Every surviving primitive candidate contains the incoming constraint
theory, independently of the syntax selected by its materializer. -/
theorem unifyCandidateRel_bindingTheoryExtends
    {target pattern : Atom} {input output : Bindings}
    (candidate : UnifyCandidateRel target pattern input output) :
    BindingTheoryExtends input output := by
  rcases candidate with ⟨_matched, _matching, merged⟩
  intro valuation satisfied
  exact ((merged.solutions valuation).mp satisfied).2

/-- Primitive `unify` either retains the incoming record or selects a merged
record containing it. -/
theorem unifyStep_bindingTheoryExtends
    {target pattern thenBranch elseBranch : Atom}
    {input output : Bindings} {result : Atom}
    (step : UnifyStep target pattern thenBranch elseBranch input result output) :
    BindingTheoryExtends input output := by
  cases step with
  | success success =>
      exact unifyCandidateRel_bindingTheoryExtends success.1
  | noMatch => exact BindingTheoryExtends.refl input

/-- A selected switch branch has the same binding-extension property as its
underlying unify candidate. -/
theorem switchRawRel_bindingTheoryExtends_selected
    {scrutinee : Atom} {branches : List Atom} {input output : Bindings}
    {result : Atom}
    (scan : SwitchRawRel scrutinee input branches (.selected result output)) :
    BindingTheoryExtends input output := by
  generalize outcomeEquation :
      SwitchRawOutcome.selected result output = outcome at scan
  induction scan with
  | nil => cases outcomeEquation
  | malformed _ tail ih => exact ih outcomeEquation
  | hit success =>
      cases outcomeEquation
      exact unifyCandidateRel_bindingTheoryExtends success.1
  | miss _ tail ih => exact ih outcomeEquation

/-- `switch-minimal` either keeps its input or returns the selected unify
candidate's extension. -/
theorem switchStep_bindingTheoryExtends
    {scrutinee result : Atom} {branches : List Atom}
    {input output : Bindings}
    (step : SwitchStep scrutinee branches input result output) :
    BindingTheoryExtends input output := by
  cases step with
  | noMatch => exact BindingTheoryExtends.refl input
  | notReducible scan =>
      exact switchRawRel_bindingTheoryExtends_selected scan
  | selected scan _ =>
      exact switchRawRel_bindingTheoryExtends_selected scan

/-- A selected equation candidate merges the match presentation into the
incoming evaluator theory. -/
theorem equationQueryCandidateRel_bindingTheoryExtends
    {space : Space} {live : List Atom} {query emitted : Atom}
    {input output : Bindings}
    (candidate : EquationQueryCandidateRel
      space live query input emitted output) :
    BindingTheoryExtends input output := by
  rcases candidate with
    ⟨_freshPattern, _freshRhs, _matched, _rule, merged, _observation⟩
  intro valuation satisfied
  exact ((merged.solutions valuation).mp satisfied).2

/-- A successful core-plus-R2 match exposes the incoming theory as the first
conjunct of its exact solution characterization. -/
theorem corePlusR2TypeMatchRel_bindingTheoryExtends
    {left right : Atom} {input output : Bindings}
    (matched : CorePlusR2TypeMatchRel left right input output) :
    BindingTheoryExtends input output := by
  intro valuation satisfied
  exact (matched.solutions valuation).mp satisfied |>.1

/-! ## Mutual evaluator preservation -/

/-- Producer completion suppresses interpretation, not the type service's
binding refinement. Both held values and cast results extend the input. -/
theorem completedNativeReturnRel_bindingTheoryExtends
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {input : BindingFrame} {result : FrameResult} {protectedScope : List String}
    (laws : EvalTypeServiceBindingLaws typing)
    (returned : CompletedNativeReturnRel space typing value expectedType input result
      (protectedScope := protectedScope)) :
    BindingTheoryExtends input result.2 := by
  cases returned with
  | keep => exact BindingTheoryExtends.refl _
  | cast _ cast _ => exact laws.typeCast cast

/-- Every raw evaluator derivation extends its input binding theory. The
mutual induction also covers minimal invocation, function completion, and
continuations, so a full call cannot forget constraints in its emitted body. -/
theorem evalAtomRawRel_bindingTheoryExtends
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {protectedScope : List String}
    {atom expectedType : Atom} {input : BindingFrame} {result : FrameResult}
    {typing : EvalTypeService}
    (laws : EvalTypeServiceBindingLaws typing)
    (derivation : EvalAtomRawRel space dispatch live (typing := typing)
      (protectedScope := protectedScope) atom expectedType input result) :
    BindingTheoryExtends input result.2 := by
  have generalized : typing = typing →
      BindingTheoryExtends input result.2 := by
    apply EvalAtomRawRel.rec
      (motive_1 := fun _space _dispatch _live _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_2 := fun _space _dispatch _live _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_3 := fun _space _dispatch _live _ _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_4 := fun _space _dispatch _live _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_5 := fun _space _dispatch _live _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_6 := fun _space _dispatch _live _ _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_7 := fun _space _dispatch _live _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_8 := fun _space _dispatch _live _ input result _protectedScope currentTyping _caller _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_9 := fun _space _dispatch _live _ input result _protectedScope currentTyping _caller _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_10 := fun _space _dispatch _live _ input result _protectedScope currentTyping _caller _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_11 := fun _space _dispatch _live _ input result _protectedScope currentTyping _caller _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_12 := fun _space _dispatch _live _ input result _protectedScope currentTyping _caller _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (t := derivation)
    all_goals
      intros
      subst_vars
      first
        | exact BindingTheoryExtends.refl _
        | exact laws.typeCast (by assumption)
        | exact unifyCandidateRel_bindingTheoryExtends (by assumption)
        | exact unifyStep_bindingTheoryExtends (by assumption)
        | exact switchStep_bindingTheoryExtends (by assumption)
        | exact mergeRel_extends_right (by assumption)
        | solve_by_elim [rfl]
        | exact BindingTheoryExtends.trans
            (mergeRel_extends_right (by assumption))
            (completedNativeReturnRel_bindingTheoryExtends laws (by assumption))
        | exact BindingTheoryExtends.trans
            (laws.candidateScanSuccess (by assumption))
            (BindingTheoryExtends.trans
              (by solve_by_elim [rfl]) (by solve_by_elim [rfl]))
        | exact BindingTheoryExtends.trans
            (mergeRel_extends_right (by assumption))
            (BindingTheoryExtends.trans
              (by solve_by_elim [rfl]) (by solve_by_elim [rfl]))
        | exact BindingTheoryExtends.trans
            (equationQueryCandidateRel_bindingTheoryExtends (by assumption))
            (BindingTheoryExtends.trans
              (by solve_by_elim [rfl]) (by solve_by_elim [rfl]))
        | exact BindingTheoryExtends.trans
            (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
  exact generalized rfl

/-- Ordinary return handling preserves the reached binding theory, whether
it restores an invocation, stops, or resumes typed evaluation. -/
theorem callReturnRel_bindingTheoryExtends
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {original expectedType value : Atom} {input : BindingFrame} {result : FrameResult}
    {typing : EvalTypeService}
    (laws : EvalTypeServiceBindingLaws typing)
    (returned : CallReturnRel space dispatch live original expectedType value input result
      (typing := typing)) :
    BindingTheoryExtends input result.2 := by
  cases returned <;>
    first
    | exact BindingTheoryExtends.refl _
    | exact evalAtomRawRel_bindingTheoryExtends laws (by assumption)

/-! ## Boundary canaries -/

/-- Positive: the empty binding theory extends itself. -/
example : BindingTheoryExtends Bindings.empty Bindings.empty :=
  BindingTheoryExtends.refl _

private def forgottenBinding : Bindings :=
  ⟨[("x", .symbol "A")], []⟩

/-- Negative: replacing a visible assignment by the empty theory forgets a
constraint and therefore is not an extension. -/
example : ¬BindingTheoryExtends forgottenBinding Bindings.empty := by
  intro extension
  let valuation : String → Atom := fun name =>
    if name = "x" then .symbol "B" else .var name
  have emptySatisfied : TypeBindingSatisfied valuation Bindings.empty := by
    simp [TypeBindingSatisfied, Bindings.empty]
  have forgottenSatisfied := extension valuation emptySatisfied
  have equation := forgottenSatisfied.1 "x" (.symbol "A") (by
    simp [forgottenBinding])
  simp [valuation, applyTypeValuation] at equation

end Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension

namespace Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Eval

theorem published_typeMatch_bindingTheoryExtends {left right : Atom} {input output : Bindings}
    (matched : TypeMatchRel left right input output) : BindingTheoryExtends input output := by
  cases matched <;> first
    | exact BindingTheoryExtends.refl _
    | exact mergeRel_extends_left (by assumption)

theorem published_argumentsApplicable_bindingTheoryExtends
    {space : Space} {arguments domains : List Atom} {input output : Bindings}
    {lookup : TypeLookupRel}
    (applicable : ArgumentsApplicableRel space (lookup := lookup) arguments domains input output) :
    BindingTheoryExtends input output := by
  induction applicable with
  | nil => exact BindingTheoryExtends.refl _
  | cons _ matched _ tail =>
      exact (published_typeMatch_bindingTheoryExtends matched).trans tail

theorem published_applicationSuccess_bindingTheoryExtends
    {space : Space} {expression functionType expectedType : Atom} {input output : Bindings}
    {lookup : TypeLookupRel}
    (applicable : ApplicationSuccessRel space (lookup := lookup) expression functionType expectedType
      input output) :
    BindingTheoryExtends input output := by
  cases applicable with
  | mk _ _ arguments result =>
      exact (published_argumentsApplicable_bindingTheoryExtends arguments).trans
        (published_typeMatch_bindingTheoryExtends result)

/-- The ordinary published service earns the two local extension obligations
from its actual type-match/merge and ordered candidate-scan derivations. -/
theorem publishedTypeService_bindingLaws : EvalTypeServiceBindingLaws storageTypeService := by
  constructor
  · intro scope space atom expected input result cast
    cases cast with
    | success _ _ _ matched => exact published_typeMatch_bindingTheoryExtends matched
    | failure => exact BindingTheoryExtends.refl _
  · intro _ space expression expected input candidates policy output scan
    obtain ⟨candidate, _member, applicable⟩ := scan.success_candidate
    cases applicable with
    | success _ applicable =>
      cases applicable with
      | success path => exact published_applicationSuccess_bindingTheoryExtends path

end Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension
