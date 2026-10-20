import Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments
import Mettapedia.Languages.MeTTa.HE.FirstSuccessRawExecution
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Earned prepared evaluation replies

Empty/error data, Atom demand, intrinsic meta-type demand and variable demand
are source leaves with a uniquely determined independent evaluator result.
The actual recursive source function, retained first-success controller and
independent evaluator all realize that same ordered singleton. Preparation
and endpoint acceptance remain separate judgments.

Typed casts, expression interpretation and external effects are not installed
as assumed soundness fields. Their remaining correspondence obligations are
separate from these constructed replies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type FirstSuccessPreparedArguments
open NativeArgumentControl
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The independently stated source-leaf boundary. It includes arbitrary
nesting and syntax; the expected demand decides whether it is a leaf. -/
def LeafRel (value expected : Atom) : Prop :=
  IsEmptyOrErrorRel value ∨ ∃ metaType, MetaTypeRel value metaType ∧
    (expected = Atom.atomType ∨ expected = metaType ∨ metaType = Atom.variableType)

theorem leaf_gate (value expected : Atom) :
    LeafRel value expected ↔
      isEmptyOrError value = true ∨
        (expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType) = true := by
  simp only [LeafRel, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError,
    Conformance.metaTypeRel_iff_getMetaType, Bool.or_eq_true, beq_iff_eq, or_assoc]
  constructor
  · rintro (failed | ⟨metaType, rfl, passed⟩)
    · exact Or.inl failed
    · exact Or.inr passed
  · rintro (failed | passed)
    · exact Or.inl failed
    · exact Or.inr ⟨_, rfl, passed⟩

theorem leaf_evidence (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (scope : List String)
    (value expected : Atom) (bindings : BindingFrame) (leaf : LeafRel value expected) :
    EvalAtomRawRel space dispatch live (protectedScope := scope) (typing := typing)
      value expected bindings (value, bindings) := by
  by_cases failed : IsEmptyOrErrorRel value
  · exact .emptyOrError value expected bindings failed
  · rcases leaf with failure | ⟨metaType, intrinsic, passed⟩
    · exact (failed failure).elim
    · exact .typePass value expected metaType bindings failed intrinsic passed

theorem leaf_unique {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {scope : List String}
    {value expected : Atom} {bindings : BindingFrame} {result : FrameResult}
    (leaf : LeafRel value expected)
    (earned : EvalAtomRawRel space dispatch live (protectedScope := scope) (typing := typing)
      value expected bindings result) : result = (value, bindings) := by
  cases earned with
  | emptyOrError => rfl
  | typePass => rfl
  | cast _ _ metaType _ _ clean intrinsic rejects _ _ _ =>
      rcases leaf with failure | ⟨otherType, otherIntrinsic, passed⟩
      · exact (clean failure).elim
      · rw [MetaTypeRel.eq otherIntrinsic intrinsic] at passed
        exact (rejects passed).elim
  | interpretSuccess _ _ metaType _ _ clean intrinsic rejects _ _ _ =>
      rcases leaf with failure | ⟨otherType, otherIntrinsic, passed⟩
      · exact (clean failure).elim
      · rw [MetaTypeRel.eq otherIntrinsic intrinsic] at passed
        exact (rejects passed).elim
  | interpretError _ _ metaType _ _ clean intrinsic rejects _ _ _ =>
      rcases leaf with failure | ⟨otherType, otherIntrinsic, passed⟩
      · exact (clean failure).elim
      · rw [MetaTypeRel.eq otherIntrinsic intrinsic] at passed
        exact (rejects passed).elim

theorem source_leaf (space : Space) (source : HE.GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat)
    (leaf : LeafRel value expected) :
    evalAtom space source value expected bindings (fuel + 1) = [(value, bindings)] := by
  rcases (leaf_gate value expected).mp leaf with failed | passed
  · simp only [evalAtom, failed, if_true]
  · simp only [evalAtom, passed, if_true, ite_self]

theorem source_leaf_iff (space : Space) (source : HE.GroundedDispatch)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (scope : List String) (value expected : Atom) (bindings : Bindings) (fuel : Nat)
    (leaf : LeafRel value expected) (result : ResultPair) :
    result ∈ evalAtom space source value expected bindings (fuel + 1) ↔
      EvalAtomRawRel space dispatch live (protectedScope := scope) (typing := typing)
        value expected bindings result := by
  rw [source_leaf space source value expected bindings fuel leaf, List.mem_singleton]
  constructor
  · rintro rfl
    exact leaf_evidence space dispatch live typing scope value expected bindings leaf
  · intro derived
    exact congrArg BindingFrame.rawResult (leaf_unique leaf derived)

theorem retained_leaf (space : Space) (source : HE.GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat)
    (leaf : LeafRel value expected) (live : List Atom) (stack : List RecursiveTasks.Frame)
    (emitted : ResultSet) :
    SilentPath source ⟨space, .work (.atom value expected bindings (fuel + 1) live), stack, emitted⟩
      ⟨space, .returning [(value, bindings)], stack, emitted⟩ := by
  have expanded : FirstSuccessRecursiveStrategy.enter space source
      (.atom value expected bindings (fuel + 1) live) = (.returning [(value, bindings)], []) := by
    rcases (leaf_gate value expected).mp leaf with failed | passed
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, failed, if_true]
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
        passed, if_true, ite_self]
  simpa only [expanded, List.nil_append] using
    enter_request space source (.atom value expected bindings (fuel + 1) live) stack emitted

/-- Preparation constructs the resolved endpoint; actual source evaluation
earns its singleton independently of the external serial checker. -/
theorem prepared_leaf_reply
    {substitution : Spec.Type.Presentation.TypeSubst} (normal : substitution.Normal)
    (argument : TypedApplyState) (policy : NativeArgumentControlPolicy.Policy) (prepareBudget : Nat)
    (imported : argument.env = presentedBindings substitution)
    (domainBudget : BindingComposition.atomDepth (originalDomain argument) + 2 ≤ prepareBudget)
    (argumentBudget : BindingComposition.atomDepth (original argument) + 2 ≤ prepareBudget)
    (space : Space) (source : HE.GroundedDispatch) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (fuel : Nat)
    (leaf : LeafRel (prepareSource argument policy prepareBudget).bound
      (prepareSource argument policy prepareBudget).domain) :
    PreparationRel substitution argument policy (prepareSource argument policy prepareBudget) ∧
    evalAtom space source (prepareSource argument policy prepareBudget).bound
      (prepareSource argument policy prepareBudget).domain argument.env (fuel + 1) =
        [((prepareSource argument policy prepareBudget).bound, argument.env)] ∧
    EvalAtomRawRel space dispatch live (typing := typing)
      (prepareSource argument policy prepareBudget).bound
      (prepareSource argument policy prepareBudget).domain argument.env
      ((prepareSource argument policy prepareBudget).bound, argument.env) :=
  ⟨preparation_sound normal argument policy prepareBudget imported domainBudget argumentBudget,
    source_leaf space source _ _ _ fuel leaf,
    leaf_evidence space dispatch live typing [] _ _ _ leaf⟩

end Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafEvaluation
