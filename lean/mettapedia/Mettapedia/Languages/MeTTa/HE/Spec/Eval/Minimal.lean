import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha

/-!
# Minimal-instruction semantics

The published evaluator uses two host objects that ordinary MeTTa syntax
cannot inspect: the current context space and the binding snapshot stored by
`collapse-bind`.  This module keeps their representation abstract.  Concrete
interpreters choose carriers at the conformance boundary; the semantic rules
depend only on their observable role.

In particular, a collapsed binding set is not encoded as a MeTTa expression.
It is an opaque grounded value, and `superpose-bind` restores it before merging
it with the bindings at the continuation point.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge
open Spec.Eval
open Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

private theorem logical_merge_empty :
    Spec.Bindings.ScopeObservation.LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty := by
  refine ⟨?_, fun name => .var name, ?_⟩
  · simpa [Bindings.empty] using BindingSourceAgreement.refl Bindings.empty
  · simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied, Bindings.empty]

/-- Ordinary embedded calls use exactly the raw minimal invocation followed
by the selected typed return gate, at the actual reached binding frame. -/
theorem ordinary_embedded_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expected : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (nonerror : ¬IsErrorRel atom) (noHost : ¬HostCall dispatch atom)
    (embedded : embeddedInstruction atom = true) :
    CallRel space dispatch live atom expected bindings result (typing := typing) ↔
      ∃ raw, CoreInvocationRel space dispatch (expected :: live)
        atom bindings raw (typing := typing) ∧
        CallReturnRel space dispatch live atom expected raw.1 raw.2 result
          (typing := typing) := by
  constructor
  · intro derived
    cases derived
    all_goals first
      | exact ⟨_, by assumption, by assumption⟩
      | simp_all [NonGroundedCallRel, HostCall]
  · rintro ⟨raw, invoked, returned⟩
    exact .embedded _ _ _ _ _ nonerror noHost embedded invoked returned

/-- With native dispatch excluded, recognized embedded syntax invokes exactly
its minimal execution. Equation fallback cannot introduce another result. -/
theorem raw_embedded_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {atom : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (noHost : ¬HostCall dispatch atom) (embedded : embeddedInstruction atom = true) :
    CoreInvocationRel space dispatch live atom bindings result
        (typing := typing) (caller := caller) ↔
      CoreRunRel space dispatch live atom bindings result
        (typing := typing) (caller := caller) := by
  constructor
  · intro derived
    cases derived
    all_goals first
      | assumption
      | simp_all [HostCall]
  · exact .embedded _ _ _ _ noHost embedded

/-- Successful primitive unification reads the selected template using the
reached frame. Refusal retains the whole incoming frame without renewal. -/
theorem unify_step_exact {space : Space} {dispatch : GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {caller : Option Atom}
    {target pattern yes no : Atom} {incoming : BindingFrame} {result : FrameResult} :
    CoreStepRel space dispatch live
      (.expression [.symbol "unify", target, pattern, yes, no]) incoming result
        (typing := typing) (caller := caller) ↔
      (UnifyCandidateRel target pattern incoming result.2 ∧
        BindingFrame.Update .renew incoming result.2 ∧
        BindingFrame.Materialization result.2 yes result.1) ∨
      (UnifyNoMatchRel target pattern incoming ∧ result = (no, incoming)) := by
  constructor
  · intro step
    generalize sourceEq : (Atom.expression [.symbol "unify", target, pattern, yes, no]) = source at step
    cases step <;> simp_all
    have arity := congrArg List.length sourceEq
    simp only [List.length_cons, List.length_nil] at arity
    omega
  · rintro (⟨matched, updated, read⟩ | ⟨missing, rfl⟩)
    · exact .unifySuccess _ _ _ _ _ _ _ _ matched updated read
    · exact .unifyNoMatch _ _ _ _ _ _ missing

theorem unify_run_exact {space : Space} {dispatch : GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {caller : Option Atom}
    {target pattern yes no : Atom} {incoming : BindingFrame} {result : FrameResult} :
    CoreRunRel space dispatch live
      (.expression [.symbol "unify", target, pattern, yes, no]) incoming result
        (typing := typing) (caller := caller) ↔
      (UnifyCandidateRel target pattern incoming result.2 ∧
        BindingFrame.Update .renew incoming result.2 ∧
        BindingFrame.Materialization result.2 yes result.1) ∨
      (UnifyNoMatchRel target pattern incoming ∧ result = (no, incoming)) := by
  constructor
  · intro run
    cases run with
    | data _ _ _ terminal => simp [embeddedInstruction] at terminal
    | instruction _ _ _ _ _ _ step => exact unify_step_exact.mp step
    | chain _ _ _ _ _ chain => simp [Minimal.IsChain] at chain
  · intro evidence
    exact .instruction _ _ _ _ rfl (by simp [Minimal.IsChain])
      (unify_step_exact.mpr evidence)

/-- A malformed primitive unify call produces its declared structural error
and renderer text, preserving the input frame. -/
theorem unify_bad_arity_step_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {tail : List Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (wrong : tail.length ≠ 4) :
    CoreStepRel space dispatch live (.expression (.symbol "unify" :: tail))
        bindings result (typing := typing) (caller := caller) ↔
      result = (mkErrorMessage (.expression (.symbol "unify" :: tail))
        (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail))), bindings) := by
  constructor
  · intro derived
    generalize sourceEq : (Atom.expression (.symbol "unify" :: tail)) = source at derived
    cases derived <;> simp_all
  · rintro rfl
    exact .unifyBadArity _ _ _ wrong

/-- Minimal execution retains the exact malformed-unify diagnostic. -/
theorem unify_bad_arity_run_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {tail : List Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (wrong : tail.length ≠ 4) :
    CoreRunRel space dispatch live (.expression (.symbol "unify" :: tail))
        bindings result (typing := typing) (caller := caller) ↔
      result = (mkErrorMessage (.expression (.symbol "unify" :: tail))
        (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail))), bindings) := by
  constructor
  · intro derived
    cases derived with
    | data _ _ _ data => simp [embeddedInstruction] at data
    | instruction _ _ _ _ _ _ step => exact (unify_bad_arity_step_exact wrong).mp step
    | chain _ _ _ _ _ chain _ _ =>
      obtain ⟨tail, equal⟩ := chain
      simp at equal
  · rintro rfl
    exact .instruction _ _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨_, equal⟩; simp at equal) (.unifyBadArity _ _ _ wrong)

/-- Ordinary return stops the exact error obtained from malformed unify;
it neither renders it again nor evaluates a replacement result. -/
theorem ordinary_unify_bad_arity_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {expected : Atom} {tail : List Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (noHost : ¬HostCall dispatch (.expression (.symbol "unify" :: tail)))
    (wrong : tail.length ≠ 4) :
    CallRel space dispatch live (.expression (.symbol "unify" :: tail))
        expected bindings result (typing := typing) ↔
      result = (mkErrorMessage (.expression (.symbol "unify" :: tail))
        (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail))), bindings) := by
  rw [ordinary_embedded_exact (by simp [IsErrorRel]) noHost
    (by simp [embeddedInstruction])]
  constructor
  · rintro ⟨raw, invoked, returned⟩
    have ran := (raw_embedded_exact noHost (by simp [embeddedInstruction])).mp invoked
    have equal := (unify_bad_arity_run_exact wrong).mp ran
    subst raw
    exact CallReturnRel.stopped_iff (by
      simp [IsEmptyOrErrorRel, IsErrorRel, mkErrorMessage, Atom.error]) |>.mp returned
  · rintro rfl
    refine ⟨_, (raw_embedded_exact noHost (by simp [embeddedInstruction])).mpr
      ((unify_bad_arity_run_exact wrong).mpr rfl), ?_⟩
    apply CallReturnRel.stopped
    simp [IsEmptyOrErrorRel, IsErrorRel, mkErrorMessage, Atom.error]

/-- Laws needed when an implementation realizes the opaque service.  They are
not fields of the data carrier, so partial or symbolic models can still state
the instruction relation without manufacturing proofs they do not possess. -/
structure ServiceLaws (services : Services) : Prop where
  /-- Distinct binding sets have distinct opaque identities. -/
  bindingPayload_injective : Function.Injective services.bindingPayload
  /-- A context-space handle is never confused with a collapsed binding set. -/
  contextPayload_ne_bindingPayload :
    ∀ space bindings, services.contextPayload space ≠ services.bindingPayload bindings

/-- The representation-only enumeration carrier is shared with full calls. -/
abbrev EvalEnumeration (_dispatch : GroundedDispatch) (_live : List Atom)
    (_typing : EvalTypeService) := Enumeration

/-- The semantic law for an evaluation enumeration.  It must enumerate
exactly the support of `EvalRel`; its order and multiplicity remain explicit
data in the chosen profile rather than being reconstructed from membership.

This separation is necessary because individual `Prop`-valued derivations do
not determine how many operational alternatives produced the same result. -/
structure EvalEnumerationLaws
    {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService}
    (enumeration : EvalEnumeration dispatch live typing) : Prop where
  support_exact :
    ∀ space atom expectedType bindings results,
      enumeration.results space atom expectedType bindings results →
        ∀ result,
          result ∈ results ↔
            EvalRel space dispatch live atom expectedType bindings result
              (typing := typing)

/-- The shared core with this representation/collection package installed. -/
abbrev MinimalStepRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → BindingFrame → FrameResult → (caller : Option Atom := none) → Prop :=
  fun space atom bindings result caller =>
    CoreStepRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing) (caller := caller)

/-- The shared core with this representation/collection package installed. -/
abbrev RawInvocationRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → BindingFrame → FrameResult → (caller : Option Atom := none) → Prop :=
  fun space atom bindings result caller =>
    CoreInvocationRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing) (caller := caller)

/-- The shared core with this representation/collection package installed. -/
abbrev InvocationResultRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → BindingFrame → FrameResult → (caller : Option Atom := none) → Prop :=
  fun space atom bindings result caller =>
    CoreInvocationResultRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing) (caller := caller)

/-- The shared core with this representation/collection package installed. -/
abbrev MinimalRunRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → BindingFrame → FrameResult → (caller : Option Atom := none) → Prop :=
  fun space atom bindings result caller =>
    CoreRunRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing) (caller := caller)

/-- The shared core with this representation/collection package installed. -/
abbrev FunctionBodyRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → BindingFrame → FrameResult → (caller : Option Atom := none) → Prop :=
  fun space atom bindings result caller =>
    CoreFunctionBodyRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing) (caller := caller)


/-- Final Empty results are omitted at the observation/collection boundary.
This does not suppress continuation activation inside the minimal machine. -/
def MinimalResultRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (atom : Atom) (bindings : BindingFrame) (result : FrameResult) : Prop :=
  MinimalRunRel services dispatch live typing enumeration space atom bindings result ∧
    result.1 ≠ Atom.empty

/-- A collapse profile enumerates the surviving minimal results, not the
full ordinary interpretation of the same syntax. Order and multiplicity are
additional profile data; the may relation fixes only support. -/
structure MinimalEnumerationLaws
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) : Prop where
  support_exact :
    ∀ space atom bindings results,
      enumeration.minimalResults space atom bindings results →
        ∀ result, result ∈ results ↔
          MinimalResultRel services dispatch live typing enumeration
            space atom bindings result

/-! ## Captured function-return context -/

theorem functionTerminalResult_return (caller : Option Atom) (value : Atom) :
    functionTerminalResult caller (.expression [.symbol "return", value]) = value := by
  rfl

theorem functionTerminalResult_noReturn (caller : Option Atom) (terminal : Atom)
    (missing : ∀ value, terminal ≠ .expression [.symbol "return", value]) :
    functionTerminalResult caller terminal =
      Atom.error (caller.getD terminal) (.symbol "NoReturn") := by
  unfold functionTerminalResult
  split
  · exact (missing _ rfl).elim
  · rfl

/-- Forgetting a caller can preserve the body and bindings while changing
the complete fault observation. -/
theorem functionTerminalResult_caller_distinguishes
    (left right terminal : Atom) (different : left ≠ right)
    (missing : ∀ value, terminal ≠ .expression [.symbol "return", value]) :
    functionTerminalResult (some left) terminal ≠
      functionTerminalResult (some right) terminal := by
  rw [functionTerminalResult_noReturn _ _ missing,
    functionTerminalResult_noReturn _ _ missing]
  simp only [Option.getD_some, Atom.error, ne_eq, Atom.expression.injEq,
    List.cons.injEq, and_true, true_and]
  exact different

/-! ## Boundary laws and canaries -/

/-- Under lawful services, equal opaque payloads identify the complete binding
sets they carry. -/
theorem bindings_eq_of_payload_eq {services : Services}
    (laws : ServiceLaws services) {left right : Bindings}
    (equal : services.bindingPayload left = services.bindingPayload right) :
    left = right :=
  laws.bindingPayload_injective equal

/-- A lawful enumeration lists precisely the individual semantic results.
The theorem intentionally says nothing about order or multiplicity: those are
the additional operational data carried by `EvalEnumeration.results`. -/
theorem result_mem_iff_evalRel
    {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService}
    {enumeration : EvalEnumeration dispatch live typing}
    (laws : EvalEnumerationLaws enumeration)
    {space : Space} {atom expectedType : Atom} {bindings : Bindings}
    {results : ResultSet}
    (enumerates : enumeration.results space atom expectedType bindings results)
    (result : ResultPair) :
    result ∈ results ↔
      EvalRel space dispatch live atom expectedType bindings result
        (typing := typing) :=
  laws.support_exact space atom expectedType bindings results enumerates result

/-- Positive canary: `context-space` returns the service's opaque handle and
does not change bindings. -/
example (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (bindings : Bindings) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "context-space"]) bindings
      (.grounded (services.contextPayload space), bindings) :=
  .contextSpace space bindings services enumeration rfl

/-- Negative canary: lawful opaque binding payloads cannot identify two
different binding sets. -/
theorem distinct_bindings_have_distinct_payloads {services : Services}
    (laws : ServiceLaws services) {left right : Bindings}
    (different : left ≠ right) :
    services.bindingPayload left ≠ services.bindingPayload right := by
  intro equal
  exact different (bindings_eq_of_payload_eq laws equal)

/-! ## Invocation and continuation boundary laws -/

theorem chain_is_embedded {atom : Atom} (chain : IsChain atom) :
    embeddedInstruction atom = true := by
  obtain ⟨tail, rfl⟩ := chain
  simp [embeddedInstruction]

theorem eval_is_not_chain (atom : Atom) :
    ¬IsChain (.expression [.symbol "eval", atom]) := by
  rintro ⟨tail, equal⟩
  simp at equal

theorem function_is_not_chain (body : Atom) :
    ¬IsChain (.expression [.symbol "function", body]) := by
  rintro ⟨tail, equal⟩
  simp at equal

/-! ## Alpha-invariant minimal dispatch -/

open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.Alpha

/-- Alpha-related function emissions have alpha-related bodies under the
same two injective renamings of their common source. -/
theorem functionBody_of_observedTypeAlpha
    {left right body : Atom} (alpha : ObservedTypeAlphaRel left right)
    (function : left = .expression [.symbol "function", body]) :
    ∃ rightBody, right = .expression [.symbol "function", rightBody] ∧
      ObservedTypeAlphaRel body rightBody := by
  rcases alpha with
    ⟨source, ⟨leftRename, leftInjective, leftEquation⟩,
      ⟨rightRename, rightInjective, rightEquation⟩⟩
  obtain ⟨sourceBody, sourceShape, bodyEquation⟩ :=
    (functionBody_renameTypeVars_iff leftRename source body).mp
      (leftEquation.symm.trans function)
  refine ⟨renameTypeVars rightRename sourceBody, ?_, ?_⟩
  · rw [rightEquation, sourceShape]
    simp [renameTypeVars]
  · exact ⟨sourceBody, ⟨leftRename, leftInjective, bodyEquation⟩,
      ⟨rightRename, rightInjective, rfl⟩⟩

/-- Alpha observations preserve and reflect the exact source function guard. -/
theorem isFunction_of_observedTypeAlpha_iff
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    IsFunction left ↔ IsFunction right := by
  constructor
  · rintro ⟨body, function⟩
    obtain ⟨rightBody, rightFunction, _⟩ :=
      functionBody_of_observedTypeAlpha alpha function
    exact ⟨rightBody, rightFunction⟩
  · rintro ⟨body, function⟩
    obtain ⟨leftBody, leftFunction, _⟩ :=
      functionBody_of_observedTypeAlpha alpha.symm function
    exact ⟨leftBody, leftFunction⟩

/-- Alpha observations preserve every literal symbolic-head guard. -/
theorem symbolicHead_of_observedTypeAlpha_iff
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) (head : String) :
    (∃ tail, left = .expression (.symbol head :: tail)) ↔
      ∃ tail, right = .expression (.symbol head :: tail) := by
  rcases alpha with
    ⟨source, ⟨leftRename, _, rfl⟩, ⟨rightRename, _, rfl⟩⟩
  exact (symbolicHead_renameTypeVars_iff leftRename source head).trans
    (symbolicHead_renameTypeVars_iff rightRename source head).symm

/-- A function-headed expression of any arity stays function-headed under
renaming. Malformed function wrappers are deliberately included here. -/
theorem functionHead_renameTypeVars_iff
    (rename : String → String) (source : Atom) :
    (∃ tail, renameTypeVars rename source = .expression (.symbol "function" :: tail)) ↔
      ∃ tail, source = .expression (.symbol "function" :: tail) :=
  symbolicHead_renameTypeVars_iff rename source "function"

/-- The broader native-entry function-head guard is independently invariant
under the same existing alpha observation relation. -/
theorem functionHead_of_observedTypeAlpha_iff
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    (∃ tail, left = .expression (.symbol "function" :: tail)) ↔
      ∃ tail, right = .expression (.symbol "function" :: tail) :=
  symbolicHead_of_observedTypeAlpha_iff alpha "function"

/-- The separate chain continuation branch is also alpha-invariant. -/
theorem isChain_of_observedTypeAlpha_iff
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    IsChain left ↔ IsChain right :=
  symbolicHead_of_observedTypeAlpha_iff alpha "chain"

/-- Alpha renaming preserves malformed function-headed forms as malformed;
it cannot turn the broader head guard into the exact source function guard. -/
theorem malformedFunctionHead_of_observedTypeAlpha_iff
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    ((∃ tail, left = .expression (.symbol "function" :: tail)) ∧ ¬IsFunction left) ↔
      (∃ tail, right = .expression (.symbol "function" :: tail)) ∧ ¬IsFunction right :=
  and_congr (functionHead_of_observedTypeAlpha_iff alpha)
    (not_congr (isFunction_of_observedTypeAlpha_iff alpha))

/-- An alpha observation preserves both positive and negative embedded
instruction dispatch. -/
theorem embeddedInstruction_of_observedTypeAlpha
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    embeddedInstruction left = embeddedInstruction right := by
  rcases alpha with
    ⟨source, ⟨leftRename, _, rfl⟩, ⟨rightRename, _, rfl⟩⟩
  exact (embeddedInstruction_renameTypeVars leftRename source).trans
    (embeddedInstruction_renameTypeVars rightRename source).symm

private theorem returnBody_renameTypeVars_iff
    (rename : String → String) (source value : Atom) :
    renameTypeVars rename source = .expression [.symbol "return", value] ↔
      ∃ original, source = .expression [.symbol "return", original] ∧
        value = renameTypeVars rename original := by
  constructor
  · intro same
    obtain ⟨tail, shape, tailSame⟩ :=
      (symbolHead_renameTypeVars_iff rename source "return" [value]).mp same
    obtain ⟨original, tailShape, valueSame⟩ := List.map_eq_singleton_iff.mp tailSame.symm
    exact ⟨original, by simpa [tailShape] using shape, valueSame.symm⟩
  · rintro ⟨original, rfl, rfl⟩
    simp [renameTypeVars]

/-- The same saved raw caller gives alpha-related terminal observations.
A captured caller diagnostic remains literally unchanged on both sides. -/
theorem functionTerminalResult_of_observedTypeAlpha (caller : Option Atom)
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    ObservedTypeAlphaRel (functionTerminalResult caller left)
      (functionTerminalResult caller right) := by
  rcases alpha with
    ⟨source, ⟨leftRename, leftInjective, rfl⟩,
      ⟨rightRename, rightInjective, rfl⟩⟩
  by_cases returning : ∃ value, source = .expression [.symbol "return", value]
  · obtain ⟨value, rfl⟩ := returning
    exact ⟨value,
      ⟨leftRename, leftInjective, by simp [renameTypeVars, functionTerminalResult]⟩,
      ⟨rightRename, rightInjective, by simp [renameTypeVars, functionTerminalResult]⟩⟩
  · have missing (rename : String → String) (value : Atom) :
        renameTypeVars rename source ≠ .expression [.symbol "return", value] := by
      intro same
      obtain ⟨original, shape, _⟩ := (returnBody_renameTypeVars_iff _ _ _).mp same
      exact returning ⟨original, shape⟩
    rw [functionTerminalResult_noReturn _ _ (missing leftRename),
      functionTerminalResult_noReturn _ _ (missing rightRename)]
    cases caller with
    | some caller => exact ObservedTypeAlphaRel.refl _
    | none =>
        exact ⟨Atom.error source (.symbol "NoReturn"),
          ⟨leftRename, leftInjective, by simp [renameTypeVars, Atom.error]⟩,
          ⟨rightRename, rightInjective, by simp [renameTypeVars, Atom.error]⟩⟩

/-- An emission outside the exact function guard completes raw, with its
whole binding endpoint unchanged. -/
theorem invocationResult_raw_exact
    {dispatch : GroundedDispatch} {live : List Atom} {typing : EvalTypeService} {caller : Option Atom}
    {space : Space} {atom : Atom} {bindings : BindingFrame} {result : FrameResult}
    (raw : ¬IsFunction atom) :
    CoreInvocationResultRel space dispatch live (caller := caller) atom bindings result (typing := typing) ↔
      result = (atom, bindings) := by
  constructor
  · intro completed
    cases completed with
    | raw => rfl
    | function => exact (raw ⟨_, rfl⟩).elim
  · rintro rfl
    exact .raw space atom bindings raw

/-- At an exact function wrapper, completion is precisely the existing
function-body instruction judgment; no second evaluator is inserted. -/
theorem invocationResult_function_exact
    {dispatch : GroundedDispatch} {live : List Atom} {typing : EvalTypeService} {caller : Option Atom}
    {space : Space} {body : Atom} {bindings : BindingFrame} {result : FrameResult} :
    CoreInvocationResultRel space dispatch live (caller := caller)
        (.expression [.symbol "function", body]) bindings result (typing := typing) ↔
      CoreStepRel space dispatch live (caller := caller)
        (.expression [.symbol "function", body]) bindings result (typing := typing) := by
  constructor
  · intro completed
    cases completed with
    | raw _ _ _ raw => exact (raw ⟨_, rfl⟩).elim
    | function _ _ _ _ step => exact step
  · exact .function space body bindings result

/-- Function completion uses one terminal observer together with the saved
caller. The body runs beneath its own function frame, whose syntax also
belongs to the protected query scope. This reuses the existing body judgment
rather than supplying a second evaluator. -/
theorem function_step_body_terminal_iff
    {dispatch : GroundedDispatch} {live : List Atom} {typing : EvalTypeService}
    {space : Space} {body : Atom} {bindings : BindingFrame} {result : FrameResult}
    {caller : Option Atom} :
    CoreStepRel space dispatch live (.expression [.symbol "function", body]) bindings result
        (typing := typing) (caller := caller) ↔
      (∃ atoms, body = .expression atoms) ∧
      ∃ terminal output,
        CoreFunctionBodyRel space dispatch (.expression [.symbol "function", body] :: live)
          body bindings (terminal, output) (typing := typing)
          (caller := some (.expression [.symbol "function", body])) ∧
        result = (functionTerminalResult caller terminal, output) := by
  constructor
  · intro step
    generalize shape : (Atom.expression [.symbol "function", body]) = atom at step
    cases step with
    | functionReturn _ _ returned _ output expression run =>
        simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at shape
        subst_vars
        exact ⟨expression, .expression [.symbol "return", returned], output, run, rfl⟩
    | functionNoReturn _ _ terminal _ output expression run _ =>
        simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at shape
        subst_vars
        exact ⟨expression, terminal, output, run, rfl⟩
    | _ => simp at shape
  · rintro ⟨expression, terminal, output, run, rfl⟩
    by_cases returning : ∃ value, terminal = .expression [.symbol "return", value]
    · obtain ⟨value, rfl⟩ := returning
      exact .functionReturn space body value bindings output expression run
    · exact .functionNoReturn space body terminal bindings output expression run
        (fun value same => returning ⟨value, same⟩)

/-- A noninstruction body without a return marker yields the captured
caller's diagnostic, or its own terminal when no caller exists. -/
theorem function_data_noReturn
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) (body : Atom) (bindings : Bindings)
    (materialized : Atom)
    (materialization : BindingMaterializationRel bindings body materialized)
    (expression : ∃ atoms, body = .expression atoms)
    (data : embeddedInstruction body = false)
    (terminal : embeddedInstruction materialized = false)
    (missing : ∀ value, materialized ≠ .expression [.symbol "return", value]) :
    CoreStepRel space dispatch live (.expression [.symbol "function", body]) bindings
      (Atom.error (caller.getD materialized) (.symbol "NoReturn"), bindings)
      (typing := typing) (caller := caller) := by
  rw [← functionTerminalResult_noReturn caller materialized missing]
  exact .functionNoReturn space body materialized bindings bindings expression
    (.terminal space body bindings (body, bindings) materialized
      (.data space body bindings data) materialization terminal) missing

/-- Alpha-related presentations of raw data each retain their own syntax and
the same chosen binding endpoint at the completion boundary. -/
theorem invocationResult_raw_of_observedTypeAlpha
    {dispatch : GroundedDispatch} {live : List Atom} {typing : EvalTypeService} {caller : Option Atom}
    {space : Space} {left right : Atom} {bindings : Bindings}
    (alpha : ObservedTypeAlphaRel left right) (raw : ¬IsFunction left) :
    CoreInvocationResultRel space dispatch live (caller := caller) right bindings
      (right, bindings) (typing := typing) :=
  .raw space right bindings
    (fun function => raw ((isFunction_of_observedTypeAlpha_iff alpha).mpr function))

/-- Noninstruction data is never interpreted merely because it looks like
an ordinary call. -/
theorem minimal_data_exact
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings : BindingFrame} {result : FrameResult}
    (data : embeddedInstruction atom = false) :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space atom bindings result ↔
      result = (atom, bindings) := by
  constructor
  · intro run
    cases run with
    | data => rfl
    | instruction _ _ _ _ embedded _ _ => simp [data] at embedded
    | chain _ _ _ _ _ chain _ _ =>
        have embedded := chain_is_embedded chain
        simp [data] at embedded
  · rintro rfl
    exact .data space atom bindings data

/-- Noninstruction alpha siblings are still held data in the minimal run;
this is a shape law and does not transport arbitrary instruction execution. -/
theorem minimal_data_of_observedTypeAlpha
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {left right : Atom} {bindings : BindingFrame} {result : FrameResult}
    (alpha : ObservedTypeAlphaRel left right) (data : embeddedInstruction left = false) :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space right bindings result ↔
      result = (right, bindings) := by
  apply minimal_data_exact
  rw [← embeddedInstruction_of_observedTypeAlpha alpha]
  exact data

/-- The unconfigured shared core also retains noninstructions as raw data. -/
theorem core_run_data_exact
    {dispatch : GroundedDispatch} {live : List Atom} {typing : EvalTypeService}
    {caller : Option Atom} {space : Space} {atom : Atom} {bindings : BindingFrame}
    {result : FrameResult} (data : embeddedInstruction atom = false) :
    CoreRunRel space dispatch live atom bindings result (typing := typing) (caller := caller) ↔
      result = (atom, bindings) := by
  constructor
  · intro run
    cases run with
    | data => rfl
    | instruction _ _ _ _ embedded _ _ => simp [data] at embedded
    | chain _ _ _ _ _ chain _ _ =>
        have embedded := chain_is_embedded chain
        simp [data] at embedded
  · rintro rfl
    exact .data space atom bindings data

/-- A closed noninstruction body has exactly its own terminal and frame.
The same law covers historical and retained finite binding readouts. -/
theorem function_data_body_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {body : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (closed : TypeSubst.typeVars body = [])
    (data : embeddedInstruction body = false) :
    CoreFunctionBodyRel space dispatch live body bindings result
        (typing := typing) (caller := caller) ↔
      BindingFrame.Materialization bindings body body ∧ result = (body, bindings) := by
  constructor
  · intro completed
    cases completed with
    | terminal _ _ _ raw normalized run materialized _ =>
        have same := (core_run_data_exact data).mp run
        subst raw
        have same := materialized.closed_result closed
        subst normalized
        exact ⟨materialized, rfl⟩
    | resume _ _ _ raw normalized _ run materialized embedded _ =>
        have same := (core_run_data_exact data).mp run
        subst raw
        have same := materialized.closed_result closed
        subst normalized
        simp [data] at embedded
  · rintro ⟨materialized, rfl⟩
    exact .terminal space body bindings (body, bindings) body
      (.data space body bindings data) materialized data

/-- A closed data body cannot lose or replace the captured diagnostic origin.
Only a literal return marker bypasses this NoReturn observation. -/
theorem function_data_noReturn_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {body : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (closed : TypeSubst.typeVars body = [])
    (expression : ∃ atoms, body = .expression atoms)
    (data : embeddedInstruction body = false)
    (missing : ∀ value, body ≠ .expression [.symbol "return", value]) :
    CoreStepRel space dispatch live (.expression [.symbol "function", body]) bindings result
        (typing := typing) (caller := caller) ↔
      BindingFrame.Materialization bindings body body ∧
        result = (Atom.error (caller.getD body) (.symbol "NoReturn"), bindings) := by
  rw [function_step_body_terminal_iff]
  constructor
  · rintro ⟨_, terminal, output, run, same⟩
    obtain ⟨materialized, pair⟩ := (function_data_body_exact closed data).mp run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    exact ⟨materialized, by simpa only [functionTerminalResult_noReturn caller _ missing] using same⟩
  · rintro ⟨materialized, rfl⟩
    exact ⟨expression, body, bindings,
      (function_data_body_exact closed data).mpr ⟨materialized, rfl⟩,
      by rw [functionTerminalResult_noReturn caller body missing]⟩

/-- Materialization preserves a literal symbolic head while resolving its
operand with the very same independently constructed presentation. -/
theorem materialization_symbol_head_iff (bindings : Bindings) (head : String)
    (raw normalized : Atom) :
    BindingMaterializationRel bindings (.expression [.symbol head, raw]) normalized ↔
      ∃ value, BindingMaterializationRel bindings raw value ∧
        normalized = .expression [.symbol head, value] :=
  BindingFrame.Materialization.symbol_head_iff (BindingFrame.historical bindings) head raw normalized

/-- A chosen materialization can be reapplied using its own normal
presentation; this does not identify all legal residual presentations. -/
theorem materialization_reapply {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized) :
    BindingMaterializationRel bindings normalized normalized :=
  BindingFrame.Materialization.reapply (frame := BindingFrame.historical bindings) materialized

/-- An immediate return body exposes its independently materialized value.
Its literal return head cannot turn into another embedded instruction. -/
theorem function_return_body_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {returned : Atom}
    {bindings : BindingFrame} {result : FrameResult} :
    CoreFunctionBodyRel space dispatch live
      (.expression [.symbol "return", returned]) bindings result
      (typing := typing) (caller := caller) ↔
      ∃ value, BindingFrame.Materialization bindings returned value ∧
        result = (.expression [.symbol "return", value], bindings) := by
  constructor
  · intro body
    cases body with
    | terminal _ _ _ raw normalized run materialized _ =>
        have same := core_run_data_exact (by simp [embeddedInstruction]) |>.mp run
        subst raw
        obtain ⟨value, valueMaterialized, rfl⟩ :=
          (BindingFrame.Materialization.symbol_head_iff _ _ _ _).mp materialized
        exact ⟨value, valueMaterialized, rfl⟩
    | resume _ _ _ raw normalized _ run materialized embedded _ =>
        have same := core_run_data_exact (by simp [embeddedInstruction]) |>.mp run
        subst raw
        obtain ⟨value, _, rfl⟩ :=
          (BindingFrame.Materialization.symbol_head_iff _ _ _ _).mp materialized
        simp [embeddedInstruction] at embedded
  · rintro ⟨value, materialized, rfl⟩
    exact .terminal space _ bindings (_, bindings) _
      (.data space _ bindings (by simp [embeddedInstruction]))
      ((BindingFrame.Materialization.symbol_head_iff _ _ _ _).mpr ⟨value, materialized, rfl⟩)
      (by simp [embeddedInstruction])

/-- Minimal eval completes precisely the raw operand invocation, with no
ordinary result re-interpretation inserted afterward. Its operand is first
materialized under the independently specified current binding theory. -/
theorem minimal_eval_exact
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings : BindingFrame} {result : FrameResult} :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "eval", atom]) bindings result ↔
    ∃ materialized, BindingFrame.Materialization bindings atom materialized ∧
      RawInvocationRel services dispatch live typing enumeration (caller := caller)
        space materialized bindings result := by
  constructor
  · intro run
    cases run with
    | data _ _ _ data => simp [embeddedInstruction] at data
    | instruction _ _ _ _ _ _ step =>
        generalize sourceEq : (Atom.expression [.symbol "eval", atom]) = source at step
        cases step with
        | eval _ _ materialized _ _ materialization invoke =>
            simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at sourceEq
            subst_vars
            exact ⟨materialized, materialization, invoke⟩
        | _ => simp at sourceEq
    | chain _ _ _ _ _ chain _ _ => exact (eval_is_not_chain atom chain).elim
  · rintro ⟨materialized, materialization, invoke⟩
    exact .instruction space _ bindings result
      (by simp [embeddedInstruction]) (eval_is_not_chain atom)
      (.eval space atom materialized bindings result materialization invoke)

/-- Empty frames preserve the raw operand, deriving the former convenient
invocation law from the general materialization boundary. -/
theorem minimal_eval_empty_exact
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom}
    {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {result : FrameResult} :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "eval", atom]) Bindings.empty result ↔
    RawInvocationRel services dispatch live typing enumeration (caller := caller)
      space atom Bindings.empty result := by
  simp only [minimal_eval_exact, BindingFrame.materialization_historical, BindingMaterializationRel.empty_iff, exists_eq_left]

/-- Executing an embedded eval operand is another minimal dispatch, not
ordinary evaluation of a finished result. -/
theorem nested_eval_of_invocation
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom materialized : Atom} {bindings : BindingFrame} {result : FrameResult}
    (materialization : BindingFrame.Materialization bindings atom materialized)
    (notHost : ¬HostCall dispatch (.expression [.symbol "eval", materialized]))
    (invoke : RawInvocationRel services dispatch live typing enumeration (caller := caller) space
      materialized bindings result) :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "eval", .expression [.symbol "eval", atom]])
      bindings result := by
  apply minimal_eval_exact.mpr
  refine ⟨.expression [.symbol "eval", materialized],
    (BindingFrame.Materialization.symbol_head_iff _ _ _ _).mpr ⟨materialized, materialization, rfl⟩, ?_⟩
  exact .embedded space _ bindings result notHost
    (by simp [embeddedInstruction])
    (minimal_eval_exact.mpr ⟨materialized, BindingFrame.Materialization.reapply materialization, invoke⟩)

/-- Sequential evaluation really invokes the acquired member a second time;
the second invocation sees the first result's refined frame. The chain binder
is substituted locally and does not leak into that ambient frame. -/
theorem sequential_eval
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source operand member materialized : Atom} {name : String}
    {bindings refined : BindingFrame} {result : FrameResult}
    (sourceMaterialization : BindingFrame.Materialization bindings source operand)
    (first : RawInvocationRel services dispatch
      (.expression [.symbol "chain", .expression [.symbol "eval", source],
        .var name, .expression [.symbol "eval", .var name]] :: live)
      typing enumeration
      (caller := some (.expression [.symbol "chain", .expression [.symbol "eval", source],
        .var name, .expression [.symbol "eval", .var name]])) space
      operand bindings (member, refined))
    (memberMaterialization : BindingFrame.Materialization refined member materialized)
    (second : RawInvocationRel services dispatch live typing enumeration (caller := caller) space
      materialized refined result) :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "chain", .expression [.symbol "eval", source],
        .var name, .expression [.symbol "eval", .var name]]) bindings result := by
  apply CoreRunRel.chain space _ bindings
    (.expression [.symbol "eval", materialized], refined) result
  · exact ⟨_, rfl⟩
  · simpa [substituteName] using
      CoreStepRel.chain (dispatch := withHost dispatch services enumeration)
        (live := live) (typing := typing) (caller := caller) space
        (.expression [.symbol "eval", source]) name
        (.expression [.symbol "eval", .var name]) bindings (member, refined) materialized
        (minimal_eval_exact.mpr ⟨operand, sourceMaterialization, first⟩) memberMaterialization
  · exact minimal_eval_exact.mpr
      ⟨materialized, BindingFrame.Materialization.reapply memberMaterialization, second⟩

theorem empty_is_not_observable
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings output : Bindings} :
    ¬MinimalResultRel services dispatch live typing enumeration space
      atom bindings (Atom.empty, output) := by
  rintro ⟨_, notEmpty⟩
  exact notEmpty rfl

/-- The typed ordinary interpreter's Atom guard has an exact singleton
support, independently of how the raw call produced its result. -/
theorem full_atom_expected_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom : Atom} {bindings : BindingFrame}
    {result : FrameResult} :
    EvalRel space dispatch live atom Atom.atomType bindings result
      (typing := typing) ↔ result = (atom, bindings) := by
  have rawExact : ∀ candidate,
      EvalAtomRawRel space dispatch live (typing := typing)
        atom Atom.atomType bindings candidate → candidate = (atom, bindings) := by
    intro candidate raw
    cases raw with
    | emptyOrError => rfl
    | typePass => rfl
    | cast _ _ _ _ _ _ _ doesNotPass _ _ => exact (doesNotPass (Or.inl rfl)).elim
    | interpretSuccess _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
    | interpretError _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
  constructor
  · exact fun evaluated => rawExact result evaluated.1
  · rintro rfl
    constructor
    · by_cases special : IsEmptyOrErrorRel atom
      · exact .emptyOrError atom Atom.atomType bindings special
      · have observedMeta : ∃ metaType, MetaTypeRel atom metaType := by
          cases atom with
          | symbol name => exact ⟨_, .symbol name⟩
          | var name => exact ⟨_, .variable name⟩
          | grounded value => exact ⟨_, .grounded value⟩
          | expression atoms => exact ⟨_, .expression atoms⟩
        obtain ⟨metaType, metaRelation⟩ := observedMeta
        exact .typePass atom Atom.atomType metaType bindings special metaRelation (Or.inl rfl)
    · intro error candidate raw
      simpa [rawExact candidate raw] using error

/-! ## Independent native boundary controls

The native service below emits a callable expression, computes its value,
or emits an empty alternative list. Its outcomes are specified independently
of both evaluator relations. Full interpretation uses the published type
service and one real arrow declaration, not a tailor-made type oracle. -/

private def probeMember : Atom := .expression [.symbol "leaf"]
private def probeValue : Atom := .grounded (.int 3)
private def probeFunction : Atom :=
  .expression [.symbol "function", .expression [.symbol "return", probeMember]]
private def probeArrow : Atom := .expression [.symbol "->", Atom.undefinedType]
private def probeSpace : Space :=
  ⟨[.expression [.symbol ":", .symbol "leaf", probeArrow]]⟩

private def probeDispatch : GroundedDispatch where
  executable := fun operator => operator = .symbol "emit" ∨
    operator = .symbol "leaf" ∨ operator = .symbol "none" ∨
    operator = .symbol "emit-function"
  outcome := fun operator arguments outcome =>
    (operator = .symbol "emit" ∧ arguments = [] ∧
      outcome = .ok [(probeMember, Bindings.empty)]) ∨
    (operator = .symbol "leaf" ∧ arguments = [] ∧
      outcome = .ok [(probeValue, Bindings.empty)]) ∨
    (operator = .symbol "none" ∧ arguments = [] ∧ outcome = .ok []) ∨
    (operator = .symbol "emit-function" ∧ arguments = [] ∧
      outcome = .ok [(probeFunction, Bindings.empty)])

private theorem merge_empty_empty :
    MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) .nil

private theorem empty_frame_satisfiable :
    ∃ valuation : String → Metta.Atom,
      LeaTTaBridge.HEBindingSatisfied valuation Bindings.empty :=
  ⟨fun name => .var name, by simp [LeaTTaBridge.HEBindingSatisfied, Bindings.empty]⟩

private theorem probe_invocation
    {live : List Atom} {caller : Option Atom}
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService)
    {operator emitted : Atom}
    (executable : probeDispatch.executable operator)
    (outcome : probeDispatch.outcome operator []
      (.ok [(emitted, Bindings.empty)]))
    (notFunction : ¬IsFunction emitted) :
    RawInvocationRel services probeDispatch live publishedTypeService enumeration (caller := caller)
      probeSpace (.expression [operator]) Bindings.empty
      (emitted, Bindings.empty) := by
  exact .grounded probeSpace operator [] Bindings.empty Bindings.empty
    [(emitted, Bindings.empty)] (emitted, Bindings.empty)
    (emitted, Bindings.empty) emitted executable rfl outcome (by simp)
    merge_empty_empty (.historical _ _) (BindingMaterializationRel.empty (.symbol "witness")).satisfiable (.raw rfl)
    (.raw probeSpace emitted Bindings.empty notFunction)

private theorem probe_emit_invocation
    {live : List Atom} {caller : Option Atom}
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch live publishedTypeService enumeration (caller := caller)
      probeSpace (.expression [.symbol "emit"]) Bindings.empty
      (probeMember, Bindings.empty) := by
  apply probe_invocation services enumeration
  · exact Or.inl rfl
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rintro ⟨body, equal⟩
    simp [probeMember] at equal

private theorem probe_leaf_invocation
    {live : List Atom} {caller : Option Atom}
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch live publishedTypeService enumeration (caller := caller)
      probeSpace probeMember Bindings.empty (probeValue, Bindings.empty) := by
  apply probe_invocation services enumeration
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · rintro ⟨body, equal⟩
    simp [probeValue] at equal

/-- A native callable-looking result stays raw after minimal eval. -/
theorem native_member_is_raw
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression [.symbol "emit"]])
      Bindings.empty (probeMember, Bindings.empty) :=
  minimal_eval_empty_exact.mpr (probe_emit_invocation services enumeration)

/-- Nesting eval does not reinterpret the already-finished native result. -/
theorem native_member_nested_eval_is_raw
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression
        [.symbol "eval", .expression [.symbol "emit"]]])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply nested_eval_of_invocation (bindings := BindingFrame.historical Bindings.empty)
    (BindingMaterializationRel.empty _)
  · rintro ⟨operator, arguments, equal, executable⟩
    simp only [Atom.expression.injEq, List.cons.injEq] at equal
    rcases equal with ⟨rfl, _⟩
    simp [probeDispatch] at executable
  · exact probe_emit_invocation services enumeration

/-- A chain explicitly evaluating the selected member does compute it. -/
theorem native_member_sequential_eval_computes
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "emit"]],
        .var "member", .expression [.symbol "eval", .var "member"]])
      Bindings.empty (probeValue, Bindings.empty) :=
  sequential_eval (BindingMaterializationRel.empty _)
    (probe_emit_invocation services enumeration) (BindingMaterializationRel.empty _)
    (probe_leaf_invocation services enumeration)

open Spec.Type in
private theorem probe_arrow_matches :
    TypeMatchRel probeArrow probeArrow Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural <;> try simp [probeArrow, Atom.undefinedType, Atom.atomType]
  · apply MatchRel.expression _ semanticLoopFree_empty
    exact .cons (.symSym "->" semanticLoopFree_empty) merge_empty_empty
      (.cons (.symSym "%Undefined%" semanticLoopFree_empty) merge_empty_empty .nil)
  · exact merge_empty_empty

open Spec.Type in
private theorem probe_leaf_types :
    TypesOfRel probeSpace (.symbol "leaf") [probeArrow] :=
  .symbolKnown (.hit .nil) (by simp)

open Spec.Type in
private theorem probe_value_full
    (protectedScope : List String := []) :
    EvalAtomRawRel probeSpace probeDispatch []
      (protectedScope := protectedScope) probeValue Atom.undefinedType
      Bindings.empty (probeValue, Bindings.empty) := by
  apply EvalAtomRawRel.cast probeValue Atom.undefinedType Atom.groundedType
    Bindings.empty (probeValue, Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeValue, Atom.empty]
  · exact .grounded (.int 3)
  · simp [Atom.undefinedType, Atom.atomType, Atom.groundedType, Atom.variableType]
  · exact Or.inr (Or.inl ⟨.int 3, rfl⟩)
  · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
      (actualType := .symbol "Number")
    · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
    · rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .historical _ _

open Spec.Type in
private theorem probe_leaf_full :
    EvalAtomRawRel probeSpace probeDispatch [] probeMember Atom.undefinedType
      Bindings.empty (probeValue, Bindings.empty) := by
  have headEval : EvalAtomRawRel probeSpace probeDispatch [probeArrow, Atom.undefinedType]
      (protectedScope := expectedApplicationScope probeMember Atom.undefinedType)
      (.symbol "leaf") probeArrow Bindings.empty (.symbol "leaf", Bindings.empty) := by
    apply EvalAtomRawRel.cast (.symbol "leaf") probeArrow Atom.symbolType
      Bindings.empty (.symbol "leaf", Bindings.empty)
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .symbol "leaf"
    · simp [probeArrow, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨"leaf", rfl⟩
    · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
        (actualType := probeArrow) probe_leaf_types rfl
      · simp
      · exact probe_arrow_matches
    · exact .historical _ _
  apply EvalAtomRawRel.interpretSuccess probeMember Atom.undefinedType Atom.expressionType
    Bindings.empty (probeValue, Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeMember, Atom.empty]
  · exact .expression [.symbol "leaf"]
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "leaf", [], rfl⟩
  · apply InterpretExpressionRel.functionPath probeMember Atom.undefinedType
      (.symbol "leaf") [] [probeArrow] [probeArrow] ⟨probeArrow, [], Atom.undefinedType, rfl⟩
      Atom.undefinedType Bindings.empty Bindings.empty
      (probeMember, Bindings.empty) (probeValue, Bindings.empty) rfl probe_leaf_types rfl
    · apply FunctionCandidateScanRel.functionSuccess (argumentTypes := [])
        (returnType := Atom.undefinedType) rfl
      exact .success rfl (.success (.mk rfl rfl (.nil _) (.undefinedLeft _ _)))
    · exact .historical _ _
    · simp [Atom.undefinedType, Atom.expressionType]
    · exact .success probeMember probeArrow Atom.undefinedType (.symbol "leaf")
        Atom.undefinedType [] [] Bindings.empty (.symbol "leaf", Bindings.empty)
        (argumentPacket [], Bindings.empty) rfl rfl headEval
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.nil _)
        ⟨[], rfl⟩
    · exact .groundedSuccess probeMember Atom.undefinedType (.symbol "leaf") []
        Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
        (probeValue, Bindings.empty) Bindings.empty probeValue (probeValue, Bindings.empty)
        rfl (Or.inr (Or.inl rfl)) rfl
        (by simp [IsErrorRel, probeMember])
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (by simp) merge_empty_empty (.historical _ _) (.raw rfl)
        (.raw _ _ _ (by rintro ⟨_, equal⟩; simp [probeValue] at equal))
        (.evaluate _ _ _ _ _ (by simp [probeValue, Atom.notReducible])
          (by simp [probeValue, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) probe_value_full)
  · simp [IsErrorRel, probeValue]

/-- The identical native emission is raw under Atom return demand and
computed under Undefined return demand. This exercises the existing full
call relation, independently of the new minimal invocation relation. -/
theorem native_return_demand_discriminates :
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) ∧
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
      Atom.undefinedType Bindings.empty (probeValue, Bindings.empty) ∧
    probeMember ≠ probeValue := by
  have nativeCall : ∀ expected result,
      EvalAtomRawRel probeSpace probeDispatch [] probeMember expected Bindings.empty result →
      CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
        expected Bindings.empty result := by
    intro expected result evaluated
    exact .groundedSuccess _ expected (.symbol "emit") [] Bindings.empty
      [(probeMember, Bindings.empty)] (probeMember, Bindings.empty) result Bindings.empty probeMember
      (probeMember, Bindings.empty)
      rfl (Or.inl rfl) rfl (by simp [IsErrorRel])
      (Or.inl ⟨rfl, rfl, rfl⟩) (by simp) merge_empty_empty (.historical _ _) (.raw rfl)
      (.raw _ _ _ (by rintro ⟨_, equal⟩; simp [probeMember] at equal))
      (.evaluate _ _ _ _ _ (by simp [probeMember, Atom.notReducible])
        (by simp [probeMember, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) evaluated)
  exact ⟨nativeCall _ _ ((full_atom_expected_exact.mpr rfl).1),
    nativeCall _ _ probe_leaf_full, by simp [probeMember, probeValue]⟩

/-- Negative typed-boundary control: Atom demand cannot compute the member
into its native value. This excludes the erroneous recursive continuation,
not merely constructs one allowed raw derivation. -/
theorem atom_demand_cannot_compute_member :
    ¬EvalRel probeSpace probeDispatch [] probeMember Atom.atomType
      Bindings.empty (probeValue, Bindings.empty) := by
  intro evaluated
  have unchanged := full_atom_expected_exact.mp evaluated
  simp [probeMember, probeValue] at unchanged

/-- A function emitted by a native call executes its delimiter before the
caller's return demand. This is the very same completion judgment consumed
by full calls and by raw minimal invocation. -/
private theorem probe_function_completes
    {caller : Option Atom}
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (bindings : Bindings)
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    CoreInvocationResultRel space dispatch live probeFunction bindings
      (probeMember, bindings) (typing := typing) (caller := caller) := by
  apply CoreInvocationResultRel.function
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  · exact .terminal space _ bindings (_, bindings) _
      (.data space _ bindings (by simp [embeddedInstruction]))
      ((BindingMaterializationRel.closed_iff _ _ _ rfl).mpr ⟨rfl, satisfiable⟩)
      (by simp [embeddedInstruction])

/-- Immediate function completion returns an independently materialized value.
Raw open syntax is not assumed to be fixed by arbitrary satisfiable frames. -/
theorem immediate_function_completion_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {returned : Atom} {bindings : BindingFrame}
    {result : FrameResult} :
    CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", returned]])
      bindings result (typing := typing) (caller := caller) ↔
      ∃ value, BindingFrame.Materialization bindings returned value ∧ result = (value, bindings) := by
  rw [invocationResult_function_exact, function_step_body_terminal_iff]
  constructor
  · rintro ⟨_, terminal, output, body, same⟩
    obtain ⟨value, materialized, pair⟩ := function_return_body_exact.mp body
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    exact ⟨value, materialized, same⟩
  · rintro ⟨value, materialized, rfl⟩
    exact ⟨⟨_, rfl⟩, .expression [.symbol "return", value], bindings,
      function_return_body_exact.mpr ⟨value, materialized, rfl⟩, rfl⟩

/-- An empty frame leaves every open return operand unchanged. -/
theorem immediate_function_completion_empty_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {returned : Atom} {result : FrameResult} :
    CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", returned]])
      Bindings.empty result (typing := typing) (caller := caller) ↔ result = (returned, Bindings.empty) := by
  simp only [immediate_function_completion_exact, BindingFrame.materialization_historical, BindingMaterializationRel.empty_iff,
    exists_eq_left, BindingFrame.historicalResult_pair]

/-- Every satisfiable frame earns an immediate completion, while inconsistent
frames cannot bypass materialization through a return delimiter. -/
theorem immediate_function_completion_exists_iff
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (returned : Atom) {caller : Option Atom} (bindings : Bindings) :
    (∃ result, CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", returned]])
      bindings result (typing := typing) (caller := caller)) ↔
      ∃ valuation, TypeBindingSatisfied valuation bindings := by
  constructor
  · rintro ⟨result, completed⟩
    obtain ⟨_, materialized, _⟩ := immediate_function_completion_exact.mp completed
    exact materialized.satisfiable
  · intro satisfiable
    obtain ⟨value, materialized⟩ := BindingMaterializationRel.exists_of_satisfiable satisfiable returned
    exact ⟨(value, bindings), immediate_function_completion_exact.mpr ⟨value, materialized, rfl⟩⟩

/-- Closed return operands remain unchanged, while inconsistent frames still
cannot supply the required materialization. -/
theorem immediate_function_completion_closed_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {returned : Atom} {bindings : Bindings} {result : FrameResult}
    (closed : TypeSubst.typeVars returned = []) :
    CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", returned]])
      bindings result (typing := typing) (caller := caller) ↔
      result = (returned, bindings) ∧
        ∃ valuation, TypeBindingSatisfied valuation bindings := by
  rw [immediate_function_completion_exact]
  constructor
  · rintro ⟨value, materialized, same⟩
    obtain ⟨rfl, model⟩ := (BindingMaterializationRel.closed_iff _ _ _ closed).mp materialized
    exact ⟨same, model⟩
  · rintro ⟨rfl, model⟩
    exact ⟨returned, (BindingMaterializationRel.closed_iff _ _ _ closed).mpr ⟨rfl, model⟩, rfl⟩

/-- Full native calls execute an emitted function before Atom freezes its
returned member; Undefined instead resumes full interpretation of that
member. The function block itself is not the Atom-demand result. -/
theorem native_function_completion_precedes_return_demand :
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) ∧
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
      Atom.undefinedType Bindings.empty (probeValue, Bindings.empty) ∧
    probeFunction ≠ probeMember := by
  have completedCall : ∀ expected result,
      EvalAtomRawRel probeSpace probeDispatch [] probeMember expected Bindings.empty result →
      CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
        expected Bindings.empty result := by
    intro expected result evaluated
    exact .groundedSuccess _ expected (.symbol "emit-function") [] Bindings.empty
      [(probeFunction, Bindings.empty)] (probeFunction, Bindings.empty) result Bindings.empty probeFunction
      (probeMember, Bindings.empty) rfl (Or.inr (Or.inr (Or.inr rfl))) rfl
      (by simp [IsErrorRel])
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) (by simp) merge_empty_empty (.historical _ _) (.raw rfl)
      (probe_function_completes _ _ _ _ _
        (BindingMaterializationRel.empty (.symbol "witness")).satisfiable)
      (.evaluate _ _ _ _ _ (by simp [probeMember, Atom.notReducible])
        (by simp [probeMember, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) evaluated)
  exact ⟨completedCall _ _ ((full_atom_expected_exact.mpr rfl).1),
    completedCall _ _ probe_leaf_full, by simp [probeFunction, probeMember]⟩

/-- Explicit Atom interpretation of the source function is different from
completing a function emitted by an invoked operation. The source is held
verbatim, with its original bindings. -/
theorem source_function_under_atom_demand_is_held :
    EvalRel probeSpace probeDispatch [] probeFunction Atom.atomType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    ¬EvalRel probeSpace probeDispatch [] probeFunction Atom.atomType Bindings.empty
      (probeMember, Bindings.empty) := by
  constructor
  · exact full_atom_expected_exact.mpr rfl
  · intro evaluated
    have unchanged := full_atom_expected_exact.mp evaluated
    simp [probeFunction, probeMember] at unchanged

/-! ## Producer-completed native values

The phase tag belongs to the producer protocol, not to the returned syntax.
These probes test that protocol independently of any particular native
library: they are not a realization proof for an opaque host service.
-/

/-- A completed value at a keep boundary has exactly its original syntax
and frame as support. The cast constructor is excluded, not merely unused. -/
theorem completed_native_keep_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (keep : CompletedNativeKeepRel value expectedType) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      result = (value, bindings) := by
  constructor
  · intro returned
    cases returned with
    | keep => rfl
    | cast notKeep _ => exact (notKeep keep).elim
  · rintro rfl
    exact .keep keep

/-- Undefined demand does not re-enter interpretation of a completed value. -/
theorem completed_native_undefined_exact
    {space : Space} {typing : EvalTypeService} {value : Atom}
    {bindings : BindingFrame} {result : FrameResult} :
    CompletedNativeReturnRel space typing value Atom.undefinedType bindings result ↔
      result = (value, bindings) :=
  completed_native_keep_exact (Or.inr (Or.inl rfl))

/-- Concrete demands outside the keep boundary use precisely the existing
cast judgment, including its refined frame or structured failure result. -/
theorem completed_native_cast_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : Bindings} {result : ResultPair}
    (notKeep : ¬CompletedNativeKeepRel value expectedType) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      typing.typeCast [] space value expectedType bindings result := by
  constructor
  · intro returned
    cases returned with
    | keep keep => exact (notKeep keep).elim
    | cast _ cast => exact cast
  · intro cast
    exact .cast notKeep cast (.historical _ _)

/-- A completed Error remains held even under an incompatible demand. -/
theorem completed_native_error_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : BindingFrame} {result : FrameResult} (error : IsErrorRel value) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      result = (value, bindings) :=
  completed_native_keep_exact (Or.inl (Or.inr error))

private def completedProbeDispatch : GroundedDispatch :=
  { probeDispatch with valueProvenance := fun _ _ => .completed }

/-- The identical function-shaped native payload is held under both Atom
and Undefined when the producer certifies completion. Ordinary emissions
still execute their function delimiter, as the preceding control proves. -/
theorem completed_native_function_stays_data :
    CallRel probeSpace completedProbeDispatch []
      (.expression [.symbol "emit-function"]) Atom.atomType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    CallRel probeSpace completedProbeDispatch []
      (.expression [.symbol "emit-function"]) Atom.undefinedType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    probeFunction ≠ probeMember := by
  have held (expected : Atom) (keep : CompletedNativeKeepRel probeFunction expected) :
      CallRel probeSpace completedProbeDispatch []
        (.expression [.symbol "emit-function"]) expected Bindings.empty
        (probeFunction, Bindings.empty) := by
    exact .groundedCompletedSuccess _ expected (.symbol "emit-function") []
      Bindings.empty [(probeFunction, Bindings.empty)] (probeFunction, Bindings.empty)
      (probeFunction, Bindings.empty) Bindings.empty probeFunction rfl
      (Or.inr (Or.inr (Or.inr rfl))) rfl
      (by simp [IsErrorRel]) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      (by simp) merge_empty_empty (.historical _ _) (.raw rfl) (.keep keep)
  exact ⟨held _ (Or.inr (Or.inr (Or.inl rfl))),
    held _ (Or.inr (Or.inl rfl)), by simp [probeFunction, probeMember]⟩

/-- Raw invocation consumes completed provenance too; an instruction-shaped
payload is not treated as a newly emitted function block. -/
theorem completed_native_raw_function_is_held
    (services : Services)
    (enumeration : EvalEnumeration completedProbeDispatch [] publishedTypeService) :
    MinimalRunRel services completedProbeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression [.symbol "emit-function"]])
      Bindings.empty (probeFunction, Bindings.empty) := by
  apply minimal_eval_empty_exact.mpr
  exact .completedGrounded probeSpace (.symbol "emit-function") []
    Bindings.empty Bindings.empty [(probeFunction, Bindings.empty)]
    (probeFunction, Bindings.empty) probeFunction
    (Or.inr (Or.inr (Or.inr rfl))) rfl
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) (by simp)
    merge_empty_empty (.historical _ _) (BindingMaterializationRel.empty (.symbol "witness")).satisfiable (.raw rfl)

private theorem completed_number_not_keep (expected : Atom)
    (notUndefined : expected ≠ Atom.undefinedType)
    (notAtom : expected ≠ Atom.atomType)
    (notGrounded : expected ≠ Atom.groundedType) :
    ¬CompletedNativeKeepRel probeValue expected := by
  rintro (special | undefined | atom | ⟨metaType, metaRelation, matched | variableMeta⟩)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeValue, Atom.empty] at special
  · exact notUndefined undefined
  · exact notAtom atom
  · cases metaRelation
    exact notGrounded matched
  · cases metaRelation
    simp [Atom.groundedType, Atom.variableType] at variableMeta

open Spec.Type in
/-- A completed number is still checked against Bool and returns the real
published BadType failure; completion does not authorize a failed cast. -/
theorem completed_native_number_rejects_bool :
    CallRel probeSpace completedProbeDispatch [] probeMember (.symbol "Bool")
      Bindings.empty
      (mkError probeValue (.badType (.symbol "Bool") (.symbol "Number")),
        Bindings.empty) := by
  apply CallRel.groundedCompletedSuccess probeMember (.symbol "Bool") (.symbol "leaf")
    [] Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
    _ Bindings.empty probeValue rfl (Or.inr (Or.inl rfl)) rfl
    (by simp [IsErrorRel, probeMember]) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    (by simp) merge_empty_empty (.historical _ _) (.raw rfl)
  refine CompletedNativeReturnRel.cast
    (completed_number_not_keep _ (by decide) (by decide) (by decide)) ?_ (.historical _ _)
  apply TypeCastRel.failure (types := [.symbol "Number"]) (actualType := .symbol "Number")
  · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
  · simp
  · intro candidateType member candidate matched
    simp only [List.mem_singleton] at member
    subst candidateType
    obtain ⟨frame, structural, _⟩ := matched.structural_of_nonWildcard
      (by decide) (by decide) (by decide) (by decide)
    exact symbol_mismatch_not_match (by decide) frame structural

open Spec.Type in
/-- The same completed number can refine an expected type variable through
the existing structural match and binding merge, without evaluator re-entry. -/
theorem completed_native_number_binds_type_variable :
    CallRel probeSpace completedProbeDispatch [] probeMember (.var "T")
      Bindings.empty
      (probeValue, Bindings.empty.assign "T" (.symbol "Number")) := by
  apply CallRel.groundedCompletedSuccess probeMember (.var "T") (.symbol "leaf")
    [] Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
    _ Bindings.empty probeValue rfl (Or.inr (Or.inl rfl)) rfl
    (by simp [IsErrorRel, probeMember]) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    (by simp) merge_empty_empty (.historical _ _) (.raw rfl)
  refine CompletedNativeReturnRel.cast
    (completed_number_not_keep _ (by decide) (by decide) (by decide)) ?_ (.historical _ _)
  apply TypeCastRel.success (types := [.symbol "Number"])
    (earlierTypes := []) (laterTypes := []) (actualType := .symbol "Number")
  · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
  · rfl
  · simp
  · apply TypeMatchRel.structural <;> try decide
    · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro occurrence; cases occurrence))
    · apply MergeRel.mk (order := [.value "T" (.symbol "Number")])
      · decide
      · exact .value (.fresh (by simp [Bindings.classValues, Bindings.lookup, Bindings.empty])) .nil

/-! ## Embedded typed interpretation connection

The shared core admits ordinary non-error interpretation results and exact
Atom/error passthrough. General error-priority completeness requires an
all-alternatives collecting interpreter and is not asserted by this fragment.
-/

/-- A non-error embedded typed result is a public full result, not merely a
raw error candidate. This follows from the independent public success rule. -/
theorem embedded_metta_nonerror_is_full_result
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expectedType : Atom} {bindings : Bindings}
    {result : ResultPair}
    (evaluated : EvalAtomRawRel space dispatch live atom expectedType bindings result
      (typing := typing)) (notError : ¬IsErrorRel result.1) :
    EvalRel space dispatch live atom expectedType bindings result (typing := typing) := by
  exact ⟨evaluated, fun error => (notError error).elim⟩

/-- Empty and syntactic error inputs have exact passthrough support under
every expected type. In particular the embedded error-input rule satisfies
the full public error-priority boundary rather than inventing an error lane. -/
theorem full_special_input_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expectedType : Atom} {bindings : BindingFrame}
    {result : FrameResult} (special : IsEmptyOrErrorRel atom) :
    EvalRel space dispatch live atom expectedType bindings result (typing := typing) ↔
      result = (atom, bindings) := by
  have rawExact : ∀ candidate,
      EvalAtomRawRel space dispatch live atom expectedType bindings candidate
        (typing := typing) → candidate = (atom, bindings) := by
    intro candidate raw
    cases raw <;> first | rfl | contradiction
  constructor
  · exact fun evaluated => rawExact result evaluated.1
  · rintro rfl
    refine ⟨.emptyOrError _ _ _ special, ?_⟩
    intro error candidate raw
    simpa [rawExact candidate raw] using error

/-- Explicit embedded metta with expected Atom holds even an executable
function source. It is not raw invocation completion. -/
theorem embedded_metta_atom_holds_function
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (enumeration : EvalEnumeration dispatch live typing)
    (space context : Space) (body : Atom) (bindings : Bindings) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "metta", .expression [.symbol "function", body], Atom.atomType,
        .grounded (services.contextPayload context)]) bindings
      (.expression [.symbol "function", body], bindings) :=
  .mettaAtom space context _ bindings services enumeration rfl

/-! ## Independent equation and context controls -/

private def noHostDispatch : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False
private def equationProbeSpace : Space :=
  ⟨[.expression [.symbol "=", .symbol "source", probeMember]]⟩

private theorem equation_probe_candidate :
    EquationQueryCandidateRel equationProbeSpace [] (.symbol "source")
      Bindings.empty probeMember Bindings.empty := by
  refine ⟨.symbol "source", probeMember, Bindings.empty, ?_,
    logical_merge_empty, ?_⟩
  · refine ⟨.symbol "source", probeMember, ?_, ?_,
      .symSym "source" semanticLoopFree_empty⟩
    · simp [equationProbeSpace]
    · refine ⟨id, Function.injective_id, .symbol "source",
        .expression (.cons (.symbol "leaf") .nil), ?_⟩
      intro name occurrence
      rcases occurrence with occurrence | occurrence
      · cases occurrence
      · cases occurrence with
        | expression member occurs =>
            simp only [List.mem_singleton] at member
            subst_vars
            cases occurs
  · intros
    rfl

/-- Equation selection also leaves a callable-looking RHS raw. The proof
uses actual hygienic matching and binding merge, not ordinary EvalRel. -/
theorem equation_result_is_raw
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      equationProbeSpace (.expression [.symbol "eval", .symbol "source"])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply minimal_eval_empty_exact.mpr
  apply CoreInvocationRel.equation (merged := BindingFrame.historical Bindings.empty)
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · exact equation_probe_candidate
  · exact .historical _ _
  · exact BindingMaterializationRel.empty _
  · exact .raw _ _ _ (by rintro ⟨body, equal⟩; simp [probeMember] at equal)

private def functionEquationSpace : Space :=
  ⟨[.expression [.symbol "=", .symbol "source-function", probeFunction]]⟩

private theorem function_equation_candidate {live : List Atom} :
    EquationQueryCandidateRel functionEquationSpace live (.symbol "source-function")
      Bindings.empty probeFunction Bindings.empty := by
  refine ⟨.symbol "source-function", probeFunction, Bindings.empty, ?_,
    logical_merge_empty, ?_⟩
  · refine ⟨.symbol "source-function", probeFunction, ?_, ?_,
      .symSym "source-function" semanticLoopFree_empty⟩
    · simp [functionEquationSpace]
    · refine ⟨id, Function.injective_id, .symbol "source-function",
        .expression (.cons (.symbol "function") (.cons
          (.expression (.cons (.symbol "return") (.cons
            (.expression (.cons (.symbol "leaf") .nil)) .nil))) .nil)), ?_⟩
      intro name occurrence
      rcases occurrence with occurrence | occurrence
      · cases occurrence
      · cases occurrence with
        | expression member occurs =>
            simp at member
            rcases member with rfl | rfl
            · cases occurs
            · cases occurs with
              | expression member occurs =>
                  simp at member
                  rcases member with rfl | rfl
                  · cases occurs
                  · cases occurs with
                    | expression member occurs =>
                        simp only [List.mem_singleton] at member
                        subst_vars
                        cases occurs
  · intros
    rfl

/-- A hygienically selected equation RHS function executes before the full
call's Atom demand. Atom demand freezes its returned member, not the emitted
function syntax. The equation, matching and merge witnesses are concrete. -/
theorem equation_function_completion_precedes_atom_demand :
    CallRel functionEquationSpace noHostDispatch [] (.symbol "source-function")
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) := by
  exact .equation _ Atom.atomType probeFunction probeFunction Bindings.empty Bindings.empty
    (probeMember, Bindings.empty) (probeMember, Bindings.empty)
    (by simp [IsErrorRel]) (by simp [NonGroundedCallRel, HostCall, embeddedInstruction, noHostDispatch]) function_equation_candidate
    (.historical _ _) (BindingMaterializationRel.empty _) (probe_function_completes _ _ _ _ _
      (BindingMaterializationRel.empty (.symbol "witness")).satisfiable)
    (.evaluate _ _ _ _ _ (by simp [probeMember, Atom.notReducible])
      (by simp [probeMember, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      ((full_atom_expected_exact.mpr rfl).1))

/-! ## Invocation origin controls -/

namespace InvocationCallerControls

private def sourceCall : Atom := .expression [.symbol "foo"]
private def heldBody : Atom := .expression [.symbol "SomeValue"]
private def emittedFunction : Atom := .expression [.symbol "function", heldBody]
private def sourceSpace : Space :=
  ⟨[.expression [.symbol "=", sourceCall, emittedFunction]]⟩

private theorem sourceClosed (name : String) : ¬AtomOccurs sourceCall name := by
  intro occurs
  cases occurs with
  | expression member child =>
      simp at member
      subst_vars
      cases child

private theorem functionClosed (name : String) : ¬AtomOccurs emittedFunction name := by
  intro occurs
  cases occurs with
  | expression member child =>
      simp at member
      rcases member with rfl | rfl
      · cases child
      · cases child with
        | expression member child =>
            simp at member
            subst_vars
            cases child

private theorem sourceCandidate (live : List Atom) :
    EquationQueryCandidateRel sourceSpace live sourceCall Bindings.empty
      emittedFunction Bindings.empty := by
  refine ⟨sourceCall, emittedFunction, Bindings.empty, ?_, logical_merge_empty, ?_⟩
  · refine ⟨sourceCall, emittedFunction, ?_, ?_, ?_⟩
    · simp [sourceSpace]
    · refine ⟨id, Function.injective_id,
        .expression (.cons (.symbol "foo") .nil),
        .expression (.cons (.symbol "function")
          (.cons (.expression (.cons (.symbol "SomeValue") .nil)) .nil)), ?_⟩
      intro name occurs
      rcases occurs with occurs | occurs
      · exact (sourceClosed name occurs).elim
      · exact (functionClosed name occurs).elim
    · exact .expression (.cons (.symSym "foo" semanticLoopFree_empty) merge_empty_empty .nil)
        semanticLoopFree_empty
  · intros
    rfl

private theorem completed (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (caller : Option Atom) :
    CoreInvocationResultRel space dispatch live emittedFunction Bindings.empty
      (Atom.error (caller.getD heldBody) (.symbol "NoReturn"), Bindings.empty)
      (caller := caller) := by
  apply CoreInvocationResultRel.function
  apply function_data_noReturn space dispatch live publishedTypeService caller heldBody
    Bindings.empty heldBody (BindingMaterializationRel.empty heldBody)
  · exact ⟨_, rfl⟩
  · rfl
  · rfl
  · intro value equal
    simp [heldBody] at equal

/-- Equation lookup installs the assembled call even beneath another caller. -/
theorem raw_equation_keeps_invocation (live : List Atom) (ambient : Option Atom) :
    CoreInvocationRel sourceSpace noHostDispatch live sourceCall Bindings.empty
      (Atom.error sourceCall (.symbol "NoReturn"), Bindings.empty) (caller := ambient) := by
  apply CoreInvocationRel.equation (merged := BindingFrame.historical Bindings.empty)
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · exact sourceCandidate live
  · exact .historical _ _
  · exact BindingMaterializationRel.empty emittedFunction
  · exact completed sourceSpace noHostDispatch live (some sourceCall)

/-- The same saved origin survives the ordinary typed return boundary. -/
theorem typed_equation_keeps_invocation (live : List Atom) (expected : Atom) :
    CallRel sourceSpace noHostDispatch live sourceCall expected Bindings.empty
      (Atom.error sourceCall (.symbol "NoReturn"), Bindings.empty) := by
  apply CallRel.equation (emitted := emittedFunction) (materialized := emittedFunction)
    (merged := BindingFrame.historical Bindings.empty)
    (completed := (Atom.error sourceCall (.symbol "NoReturn"),
      BindingFrame.historical Bindings.empty))
  · simp [sourceCall, IsErrorRel]
  · simp [sourceCall, NonGroundedCallRel, HostCall, embeddedInstruction, noHostDispatch]
  · exact sourceCandidate _
  · exact .historical _ _
  · exact BindingMaterializationRel.empty emittedFunction
  · exact completed sourceSpace noHostDispatch _ (some sourceCall)
  · apply CallReturnRel.stopped
    simp [IsEmptyOrErrorRel, IsErrorRel, Atom.error]

private def hostDispatch : GroundedDispatch where
  executable operator := operator = .symbol "foo"
  outcome operator arguments result :=
    operator = .symbol "foo" ∧ arguments = [] ∧
      result = .ok [(emittedFunction, Bindings.empty)]

/-- An emitted host function captures its actual invocation as well. -/
theorem raw_host_keeps_invocation (live : List Atom) (ambient : Option Atom) :
    CoreInvocationRel Space.empty hostDispatch live sourceCall Bindings.empty
      (Atom.error sourceCall (.symbol "NoReturn"), Bindings.empty) (caller := ambient) := by
  exact .grounded Space.empty (.symbol "foo") [] Bindings.empty Bindings.empty
    [(emittedFunction, Bindings.empty)] (emittedFunction, Bindings.empty)
    (Atom.error sourceCall (.symbol "NoReturn"), Bindings.empty) emittedFunction
    rfl rfl ⟨rfl, rfl, rfl⟩ (by simp) merge_empty_empty (.historical _ _)
    (BindingMaterializationRel.empty heldBody).satisfiable (.raw rfl)
    (completed Space.empty hostDispatch live (some sourceCall))

/-- Full host completion uses the identical saved-call boundary. -/
theorem typed_host_keeps_invocation (live : List Atom) (expected : Atom) :
    CallRel Space.empty hostDispatch live sourceCall expected Bindings.empty
      (Atom.error sourceCall (.symbol "NoReturn"), Bindings.empty) := by
  apply CallRel.groundedSuccess (operator := .symbol "foo") (arguments := [])
    (nativeResults := [(emittedFunction, Bindings.empty)])
    (nativeResult := (emittedFunction, Bindings.empty))
    (merged := BindingFrame.historical Bindings.empty) (emitted := emittedFunction)
    (completed := (Atom.error sourceCall (.symbol "NoReturn"),
      BindingFrame.historical Bindings.empty))
  · rfl
  · rfl
  · rfl
  · simp [IsErrorRel, sourceCall]
  · exact ⟨rfl, rfl, rfl⟩
  · simp
  · exact merge_empty_empty
  · exact .historical _ _
  · exact .raw rfl
  · exact completed Space.empty hostDispatch _ (some sourceCall)
  · apply CallReturnRel.stopped
    simp [IsEmptyOrErrorRel, IsErrorRel, Atom.error]

/-- Embedded function instructions retain their ambient caller; they do not
allocate the ordinary invocation frame introduced by an equation or host. -/
theorem embedded_function_keeps_ambient (live : List Atom) (ambient : Option Atom) :
    CoreInvocationRel sourceSpace noHostDispatch live emittedFunction Bindings.empty
      (Atom.error (ambient.getD heldBody) (.symbol "NoReturn"), Bindings.empty)
      (caller := ambient) := by
  apply CoreInvocationRel.embedded
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · apply CoreRunRel.instruction
    · rfl
    · exact function_is_not_chain heldBody
    · exact invocationResult_function_exact.mp (completed sourceSpace noHostDispatch live ambient)

/-- The former body-origin answer is impossible at the corrected completion
boundary, regardless of the selected finite readout. -/
theorem completion_rejects_body_origin (live : List Atom) (frame : BindingFrame) :
    ¬CoreInvocationResultRel sourceSpace noHostDispatch live emittedFunction frame
      (Atom.error heldBody (.symbol "NoReturn"), frame) (caller := some sourceCall) := by
  intro accepted
  have step := invocationResult_function_exact.mp accepted
  have exactResult := (function_data_noReturn_iff (body := heldBody) rfl ⟨_, rfl⟩ rfl
    (by intro value equal; simp [heldBody] at equal)).mp step
  simp [sourceCall, heldBody, Atom.error] at exactResult

end InvocationCallerControls

/-! ## Ordinary call-return protocol controls -/

namespace CallReturnControls

open Spec.Type

private def sourceCall : Atom := .expression [.symbol "freeze", .grounded (.int 7)]
private def sourceSpace : Space := ⟨[.expression [.symbol "=", sourceCall, Atom.notReducible]]⟩

private theorem sourceClosed (name : String) : ¬AtomOccurs sourceCall name := by
  intro occurs
  cases occurs with
  | expression member child =>
      simp at member
      rcases member with rfl | rfl <;> cases child

private theorem sourceCandidate (live : List Atom) :
    EquationQueryCandidateRel sourceSpace live sourceCall Bindings.empty
      Atom.notReducible Bindings.empty := by
  refine ⟨sourceCall, Atom.notReducible, Bindings.empty, ?_, logical_merge_empty, ?_⟩
  · refine ⟨sourceCall, Atom.notReducible, ?_, ?_, ?_⟩
    · simp [sourceSpace]
    · refine ⟨id, Function.injective_id, ?_, .symbol "NotReducible", ?_⟩
      · exact .expression (.cons (.symbol "freeze") (.cons (.grounded (.int 7)) .nil))
      · intro name occurs
        rcases occurs with left | right
        · exact (sourceClosed name left).elim
        · cases right
    · apply MatchRel.expression
      · exact .cons (.symSym "freeze" semanticLoopFree_empty) merge_empty_empty
          (.cons (.groundedLeftCustom rfl trivial ⟨rfl, rfl⟩ semanticLoopFree_empty)
            merge_empty_empty .nil)
      · exact semanticLoopFree_empty
  · intros
    rfl

private theorem noAnnotations (target : Atom) :
    AnnotationTypesRel target sourceSpace.atoms [] := by
  apply AnnotationTypesRel.skip
  · intro type
    simp
  · exact .nil

private theorem rawSymbol {dispatch : GroundedDispatch} (live : List Atom) (name : String) (bindings : Bindings)
    (notEmpty : name ≠ "Empty") :
    EvalAtomRawRel sourceSpace dispatch live (.symbol name) Atom.undefinedType bindings
      (.symbol name, bindings) := by
  apply EvalAtomRawRel.cast _ _ Atom.symbolType
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
  · exact .symbol name
  · simp [Atom.undefinedType, Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨name, rfl⟩
  · apply TypeCastRel.success (types := [Atom.undefinedType]) (earlierTypes := [])
      (laterTypes := []) (actualType := Atom.undefinedType)
    · exact .symbolUndefined (noAnnotations _)
    · rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .historical _ _

private theorem rawSeven (live : List Atom) :
    EvalAtomRawRel sourceSpace noHostDispatch live (.grounded (.int 7)) Atom.undefinedType
      Bindings.empty (.grounded (.int 7), Bindings.empty) := by
  apply EvalAtomRawRel.cast _ _ Atom.groundedType
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .grounded _
  · simp [Atom.undefinedType, Atom.atomType, Atom.groundedType, Atom.variableType]
  · exact Or.inr (Or.inl ⟨.int 7, rfl⟩)
  · apply TypeCastRel.success (types := [.symbol "Number"]) (earlierTypes := [])
      (laterTypes := []) (actualType := .symbol "Number")
    · exact .groundedKnown (.int 7) (by simp [Atom.undefinedType])
    · rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .historical _ _

/-- Ordinary equation refusal restores the actual assembled invocation. -/
theorem ordinary_equation_refusal_restores_call (live : List Atom) :
    CallRel sourceSpace noHostDispatch live sourceCall Atom.undefinedType Bindings.empty
      (sourceCall, Bindings.empty) := by
  exact .equation sourceCall Atom.undefinedType Atom.notReducible Atom.notReducible
    Bindings.empty Bindings.empty (sourceCall, Bindings.empty)
    (Atom.notReducible, Bindings.empty)
    (by simp [sourceCall, IsErrorRel])
    (by simp [sourceCall, NonGroundedCallRel, HostCall, embeddedInstruction, noHostDispatch])
    (sourceCandidate _) (.historical _ _) (BindingMaterializationRel.empty _)
    (.raw _ _ _ (by simp [IsFunction, Atom.notReducible]))
    (.notReducible _ _ _)

private theorem tupleSource (live : List Atom) :
    InterpretTupleRel sourceSpace noHostDispatch live sourceCall Bindings.empty
      (sourceCall, Bindings.empty) := by
  apply InterpretTupleRel.success (.symbol "freeze") [.grounded (.int 7)] Bindings.empty
    (.symbol "freeze", Bindings.empty) (.expression [.grounded (.int 7)], Bindings.empty)
  · simp
  · exact rawSymbol _ "freeze" Bindings.empty (by decide)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · apply InterpretTupleRel.singleton (.grounded (.int 7)) Bindings.empty
        (.grounded (.int 7), Bindings.empty)
    · exact rawSeven _
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

/-- The concrete untyped equation is restored at the public boundary;
no function annotation is needed to trigger the ordinary return protocol. -/
theorem full_untyped_equation_refusal_restores_call :
    EvalRel sourceSpace noHostDispatch [] sourceCall Atom.undefinedType Bindings.empty
      (sourceCall, Bindings.empty) := by
  constructor
  · apply EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType
    · simp [sourceCall, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .expression _
    · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
    · exact ⟨.symbol "freeze", [.grounded (.int 7)], rfl⟩
    · apply InterpretExpressionRel.tuplePath (operator := .symbol "freeze")
        (arguments := [.grounded (.int 7)]) (rawTypes := [Atom.undefinedType])
        (types := [Atom.undefinedType]) (errors := [])
        (tupleResult := (sourceCall, Bindings.empty))
      · rfl
      · exact TypesOfRel.symbolUndefined (noAnnotations _)
      · rfl
      · exact .nonFunctionExhausted (by simp [FunctionTypeRel, Atom.undefinedType]) .nil
      · exact tupleSource _
      · exact ordinary_equation_refusal_restores_call _
    · simp [IsErrorRel, sourceCall]
  · simp [IsErrorRel, sourceCall]

/-- Direct raw invocation is supposed to retain the protocol atom. -/
theorem raw_equation_keeps_notReducible (live : List Atom) :
    CoreInvocationRel sourceSpace noHostDispatch live sourceCall Bindings.empty
      (Atom.notReducible, Bindings.empty) := by
  apply CoreInvocationRel.equation (merged := BindingFrame.historical Bindings.empty)
  · rintro ⟨_, _, _, impossible⟩
    exact impossible
  · rfl
  · exact sourceCandidate _
  · exact .historical _ _
  · exact BindingMaterializationRel.empty _
  · exact .raw _ _ _ (by simp [IsFunction, Atom.notReducible])

/-- Atom demand is a hold boundary, not ordinary call completion. -/
theorem atom_demand_holds_call :
    EvalRel sourceSpace noHostDispatch [] sourceCall Atom.atomType Bindings.empty
      (sourceCall, Bindings.empty) := full_atom_expected_exact.mpr rfl


private def sentinelHost : GroundedDispatch where
  executable operator := operator = .symbol "sentinel"
  outcome operator arguments result :=
    operator = .symbol "sentinel" ∧ arguments = [] ∧
      result = .ok [(Atom.notReducible, Bindings.empty)]

/-- A raw successful native emission uses the same ordinary refusal gate. -/
theorem ordinary_native_refusal_restores_call :
    CallRel sourceSpace sentinelHost [] (.expression [.symbol "sentinel"])
      Atom.undefinedType Bindings.empty
      (.expression [.symbol "sentinel"], Bindings.empty) := by
  apply CallRel.groundedSuccess (operator := .symbol "sentinel") (arguments := [])
    (nativeResults := [(Atom.notReducible, Bindings.empty)])
    (nativeResult := (Atom.notReducible, Bindings.empty)) (merged := Bindings.empty)
    (emitted := Atom.notReducible) (completed := (Atom.notReducible, Bindings.empty))
  · rfl
  · rfl
  · rfl
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl, rfl⟩
  · simp
  · exact merge_empty_empty
  · exact .historical _ _
  · exact .raw rfl
  · exact .raw _ _ _ (by simp [IsFunction, Atom.notReducible])
  · exact .notReducible _ _ _

private def completedHost : GroundedDispatch :=
  { sentinelHost with valueProvenance := fun _ _ => .completed }

/-- The separately admitted completed-value profile treats this payload as
ready data. Raw HE call-return does not alter that profile. -/
theorem completed_value_profile_keeps_notReducible :
    CallRel sourceSpace completedHost [] (.expression [.symbol "sentinel"])
      Atom.undefinedType Bindings.empty (Atom.notReducible, Bindings.empty) := by
  apply CallRel.groundedCompletedSuccess (operator := .symbol "sentinel") (arguments := [])
    (nativeResults := [(Atom.notReducible, Bindings.empty)])
    (nativeResult := (Atom.notReducible, Bindings.empty)) (merged := Bindings.empty)
    (emitted := Atom.notReducible)
  · rfl
  · rfl
  · rfl
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl, rfl⟩
  · simp
  · exact merge_empty_empty
  · exact .historical _ _
  · exact .raw rfl
  · exact .keep (Or.inr (Or.inl rfl))

/-- The negative control excludes leaking the protocol atom, not merely
constructs a restored alternative. It applies to every reached frame. -/
theorem raw_refusal_cannot_publish_protocol
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {original expectedType : Atom} {bindings : Bindings}
    (notProtocol : original ≠ Atom.notReducible) :
    ¬CallReturnRel space dispatch live original expectedType Atom.notReducible bindings
      (Atom.notReducible, bindings) (typing := typing) := by
  intro returned
  have same := CallReturnRel.notReducible_iff.mp returned
  exact notProtocol (congrArg Prod.fst same).symm

/-- Stopped values are independent of the requested return type. -/
theorem stopped_reply_ignores_return_demand
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} (original expectedType : Atom) (bindings : Bindings) :
    CallReturnRel space dispatch live original expectedType Atom.empty bindings
        (Atom.empty, bindings) (typing := typing) ∧
      CallReturnRel space dispatch live original expectedType
        (.expression [.symbol "Error"]) bindings
        (.expression [.symbol "Error"], bindings) (typing := typing) :=
  ⟨.stopped _ _ _ _ (Or.inl rfl), .stopped _ _ _ _ (Or.inr ⟨[], rfl⟩)⟩

end CallReturnControls

/-- Raw equation invocation and full call completion share the same emitted
function delimiter. Neither requires evaluating its returned member. -/
theorem raw_equation_function_returns_member
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      functionEquationSpace
      (.expression [.symbol "eval", .symbol "source-function"])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply minimal_eval_empty_exact.mpr
  exact .equation _ _ probeFunction probeFunction Bindings.empty Bindings.empty
    (probeMember, Bindings.empty)
    (by rintro ⟨_, _, _, impossible⟩; exact impossible) rfl function_equation_candidate
    (.historical _ _) (BindingMaterializationRel.empty _) (probe_function_completes _ _ _ _ _ (BindingMaterializationRel.empty (.symbol "witness")).satisfiable)

/-- evalc invokes the supplied context, not the caller space; a real rule in
that context supplies the raw result even though the caller has no rules. -/
theorem evalc_uses_supplied_context
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalStepRel services noHostDispatch [] publishedTypeService enumeration
      Space.empty (.expression [.symbol "evalc", .symbol "source",
        .grounded (services.contextPayload equationProbeSpace)])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply CoreStepRel.evalc (services := services) (enumeration := enumeration)
  · rfl
  · exact BindingMaterializationRel.empty _
  apply CoreInvocationRel.equation (merged := BindingFrame.historical Bindings.empty)
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · exact equation_probe_candidate
  · exact .historical _ _
  · exact BindingMaterializationRel.empty _
  · exact .raw _ _ _ (by rintro ⟨body, equal⟩; simp [probeMember] at equal)

/-- In the empty current space, the same ordinary raw query is NotReducible,
which distinguishes context selection from global/default lookup. -/
theorem empty_context_is_not_reducible
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      Space.empty (.expression [.symbol "eval", .symbol "source"])
      Bindings.empty (Atom.notReducible, Bindings.empty) := by
  apply minimal_eval_empty_exact.mpr
  apply CoreInvocationRel.noEquation
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · intro freshPattern freshRhs matched rule
    obtain ⟨lhs, rhs, member, _⟩ := rule
    simp [Space.empty] at member

/-! ## Local binders, ordered alternatives, and the Empty boundary -/

/-- Substitute already materialized occurrences in order without exporting
 the local binder or deduplicating. This data operation supplies no binding
 resolution by itself; the execution adapter requires materialization evidence. -/
def chainActivations (name : String) (template : Atom) (results : ResultSet) : ResultSet :=
  results.map fun result => (substituteName name result.1 template, result.2)

/-- Every independently enumerated source occurrence justifies its concrete
activation by the minimal chain rule. This connects ordered data to the
instruction relation rather than defining one to be the other. -/
theorem chain_activation_is_step
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom}
    {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source : Atom} {bindings : BindingFrame} {selected : FrameResult} {materialized : Atom}
    (name : String) (template : Atom)
    (run : MinimalRunRel services dispatch
      (.expression [.symbol "chain", source, .var name, template] :: live)
      typing enumeration
      (caller := some (.expression [.symbol "chain", source, .var name, template])) space
      source bindings selected)
    (materialization : BindingFrame.Materialization selected.2 selected.1 materialized) :
    MinimalStepRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "chain", source, .var name, template]) bindings
      (substituteName name materialized template, selected.2) :=
  .chain space source name template bindings selected materialized run materialization

theorem chain_activations_append (name : String) (template : Atom)
    (left right : ResultSet) :
    chainActivations name template (left ++ right) =
      chainActivations name template left ++ chainActivations name template right := by
  simp [chainActivations]

theorem chain_activations_preserve_ambient_frames (name : String) (template : Atom)
    (results : ResultSet) :
    (chainActivations name template results).map Prod.snd = results.map Prod.snd := by
  simp [chainActivations, List.map_map]

theorem chain_activations_keep_duplicate_occurrences (name : String) (template : Atom)
    (result : ResultPair) :
    chainActivations name template [result, result] =
      [(substituteName name result.1 template, result.2),
        (substituteName name result.1 template, result.2)] := rfl

/-- The substituted template is data unless it is explicitly an embedded
instruction. Its caller frame contains source refinements, not a new binder. -/
theorem chain_data_template
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom}
    {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source : Atom} {bindings : BindingFrame} {selected : FrameResult} {materialized : Atom}
    (name : String) (template : Atom)
    (run : MinimalRunRel services dispatch
      (.expression [.symbol "chain", source, .var name, template] :: live)
      typing enumeration
      (caller := some (.expression [.symbol "chain", source, .var name, template])) space
      source bindings selected)
    (materialization : BindingFrame.Materialization selected.2 selected.1 materialized)
    (data : embeddedInstruction (substituteName name materialized template) = false) :
    MinimalRunRel services dispatch live typing enumeration (caller := caller) space
      (.expression [.symbol "chain", source, .var name, template]) bindings
      (substituteName name materialized template, selected.2) :=
  .chain space _ bindings _ _ ⟨_, rfl⟩
    (chain_activation_is_step name template run materialization) (.data space _ selected.2 data)

/-- A return-shaped source is locally bound as data; it does not prematurely
return from the surrounding function. -/
theorem return_shaped_chain_source_is_data
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (bindings : Bindings) (value normalized : Atom)
    (materialization : BindingMaterializationRel bindings value normalized) :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "chain", .expression [.symbol "return", value],
        .var "selected", .expression [.symbol "kept", .var "selected"]]) bindings
      (.expression [.symbol "kept", .expression [.symbol "return", normalized]], bindings) := by
  simpa [substituteName] using chain_data_template "selected"
    (.expression [.symbol "kept", .var "selected"])
    (.data space (.expression [.symbol "return", value]) bindings
      (by simp [embeddedInstruction]))
    ((materialization_symbol_head_iff _ _ _ _).mpr ⟨normalized, materialization, rfl⟩)
    (by simp [substituteName, embeddedInstruction])

/-- A chain returns the independently materialized selected value. Reusing
its chosen normal presentation at the return boundary preserves that value;
the pending primitive operands and saved caller syntax remain raw. -/
theorem function_chain_returns_selected_materialized
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source value normalized : Atom} {bindings refined : Bindings}
    (name : String)
    (materialization : BindingMaterializationRel refined value normalized)
    (run :
      let body := Atom.expression [.symbol "chain", source, .var name,
        .expression [.symbol "return", .var name]]
      MinimalRunRel services dispatch (body :: .expression [.symbol "function", body] :: live)
        typing enumeration (caller := some body) space source bindings (value, refined)) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "function", .expression [.symbol "chain", source,
        .var name, .expression [.symbol "return", .var name]]]) bindings
      (normalized, refined) := by
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.terminal space _ bindings
    (.expression [.symbol "return", normalized], refined) _
  · simpa [substituteName] using chain_data_template name
      (.expression [.symbol "return", .var name]) run materialization
      (by simp [substituteName, embeddedInstruction])
  · exact (materialization_symbol_head_iff _ _ _ _).mpr
      ⟨normalized, materialization_reapply materialization, rfl⟩
  · simp [embeddedInstruction]

/-- The former raw-output specialization is valid when the selected value
is explicitly fixed by a legal materialization of its refined frame. -/
theorem function_chain_returns_selected_raw
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source value : Atom} {bindings refined : Bindings}
    (name : String) (fixed : BindingMaterializationRel refined value value)
    (run :
      let body := Atom.expression [.symbol "chain", source, .var name,
        .expression [.symbol "return", .var name]]
      MinimalRunRel services dispatch (body :: .expression [.symbol "function", body] :: live)
        typing enumeration (caller := some body) space source bindings (value, refined)) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "function", .expression [.symbol "chain", source,
        .var name, .expression [.symbol "return", .var name]]]) bindings
      (value, refined) :=
  function_chain_returns_selected_materialized name fixed run

private theorem probe_empty_invocation
    {live : List Atom} {caller : Option Atom}
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch live publishedTypeService enumeration (caller := caller)
      probeSpace (.expression [.symbol "none"]) Bindings.empty (Atom.empty, Bindings.empty) :=
  .groundedEmpty probeSpace (.symbol "none") [] Bindings.empty
    (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

/-- The published minimal continuation can run after an Empty native source.
An independent constant return reaches the function boundary normally. This
positive control prevents confusing minimal chain with a pruning map. -/
theorem minimal_empty_source_can_activate_constant_return
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalStepRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .symbol "reached"]]])
      Bindings.empty (.symbol "reached", Bindings.empty) := by
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.terminal probeSpace _ Bindings.empty
    (.expression [.symbol "return", .symbol "reached"], Bindings.empty) _
  · simpa [substituteName] using chain_data_template "selected"
      (.expression [.symbol "return", .symbol "reached"])
      (minimal_eval_empty_exact.mpr (probe_empty_invocation services enumeration))
      (BindingMaterializationRel.empty _)
      (by simp [substituteName, embeddedInstruction])
  · exact BindingMaterializationRel.empty _
  · simp [embeddedInstruction]

/-- Returning the selected Empty sentinel completes the internal function,
but contributes no public result. This differs from the preceding constant
continuation, which does not return the selected sentinel. -/
theorem minimal_empty_selected_return_is_filtered
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .var "selected"]]])
      Bindings.empty (Atom.empty, Bindings.empty) ∧
    ¬MinimalResultRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .var "selected"]]])
      Bindings.empty (Atom.empty, Bindings.empty) := by
  constructor
  · apply CoreRunRel.instruction
    · simp [embeddedInstruction]
    · exact function_is_not_chain _
    · exact function_chain_returns_selected_raw "selected" (BindingMaterializationRel.empty _)
        (minimal_eval_empty_exact.mpr (probe_empty_invocation services enumeration))
  · exact empty_is_not_observable

/-- Empty final outputs cannot occur in a lawful collapse enumeration even
though internal minimal continuations can receive the sentinel. -/
theorem collapse_enumeration_omits_final_empty
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    {space : Space} {atom : Atom} {bindings : Bindings} {results : ResultSet}
    (enumerates : enumeration.minimalResults space atom bindings results)
    (output : Bindings) : (Atom.empty, output) ∉ results := by
  intro member
  exact empty_is_not_observable
    ((laws.support_exact space atom bindings results enumerates _).mp member)

open Spec.Eval.StateAlgebra

/-- A deliberately effectful body consumer records one activation and emits
its selected atom. This is an independent state service, not an evaluator
definition; the ordered traversal specifies its chronology. -/
private def countActivation (selected : ResultPair) (initial : Nat)
    (results : List Atom) (final : Nat) : Prop :=
  results = [selected.1] ∧ final = initial + 1

private theorem count_activations_final
    {selected : ResultSet} {initial final : Nat} {results : List Atom}
    (run : OrderedStateFlatMapRel countActivation selected initial results final) :
    final = initial + selected.length := by
  induction run with
  | nil => simp
  | @cons head tail initial middle final headResults tailResults step _ inductionHypothesis =>
      rcases step with ⟨_, rfl⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inductionHypothesis

/-- No selected occurrences imply no body effects, independently of the
contents of the held template. This is an enumeration-level statement, not
an assertion that the internal Empty sentinel is no occurrence. -/
theorem no_occurrences_no_body_effect (name : String) (template : Atom)
    (initial final : Nat) (results : List Atom) :
    OrderedStateFlatMapRel countActivation (chainActivations name template [])
      initial results final ↔ results = [] ∧ final = initial :=
  OrderedStateFlatMapRel.nil_iff

/-- Duplicate source occurrences activate an effectful body twice, in
source order, while retaining the independently selected binding frames. -/
theorem duplicate_occurrences_activate_body_twice (selected : ResultPair) :
    OrderedStateFlatMapRel countActivation
      (chainActivations "selected" (.var "selected") [selected, selected])
      0 [selected.1, selected.1] 2 := by
  simp only [chainActivations, List.map_cons, List.map_nil, substituteName]
  apply OrderedStateFlatMapRel.cons (middle := 1)
    (headResults := [selected.1]) (tailResults := [selected.1])
  · exact ⟨rfl, rfl⟩
  · apply OrderedStateFlatMapRel.cons (middle := 2)
      (headResults := [selected.1]) (tailResults := [])
    · exact ⟨rfl, rfl⟩
    · exact .nil 2

/-- Collapsing equal alternatives into one is observationally wrong for an
effectful body even when their returned atoms coincide. -/
theorem duplicate_occurrences_cannot_be_deduplicated (selected : ResultPair)
    (results : List Atom) :
    ¬OrderedStateFlatMapRel countActivation
      (chainActivations "selected" (.var "selected") [selected, selected])
      0 results 1 := by
  intro run
  have final := count_activations_final run
  simp [chainActivations] at final

/-! ## Handler and producer materialization controls -/

private def aliasFrame (value : Atom) : Bindings := ⟨[("pending", value)], []⟩

private theorem alias_materialization (value : Atom)
    (fresh : "pending" ∉ TypeSubst.typeVars value) :
    BindingMaterializationRel (aliasFrame value) (.var "pending") value := by
  simpa [aliasFrame, TypeSubst.apply, TypeSubst.lookup] using
    BindingMaterializationRel.single_assignment "pending" value (.var "pending") fresh

private def aliasFallback : Atom :=
  .expression [.symbol "unify", .symbol "A", .symbol "B", .symbol "unused", .var "pending"]

/-- The primitive fallback itself stays raw; the function handler is the
boundary that subsequently resolves its alias. -/
private theorem alias_fallback_run (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (caller : Option Atom) (value : Atom) :
    CoreRunRel space dispatch live aliasFallback (aliasFrame value)
      (.var "pending", aliasFrame value) (typing := typing) (caller := caller) := by
  apply CoreRunRel.instruction
  · rfl
  · rintro ⟨tail, same⟩
    simp [aliasFallback] at same
  · apply CoreStepRel.unifyNoMatch
    rintro output ⟨matched, structural, _⟩
    exact symbol_mismatch_not_match (by decide) matched structural

/-- A raw primitive result can reveal a return marker only at the actual
function handler's independently licensed materialization boundary. -/
theorem function_alias_exposes_return (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) :
    let returned := Atom.expression [.symbol "return", .symbol "ok"]
    CoreStepRel space dispatch live (.expression [.symbol "function", aliasFallback])
      (aliasFrame returned) (.symbol "ok", aliasFrame returned) (typing := typing) := by
  intro returned
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.terminal space aliasFallback (aliasFrame returned)
    (.var "pending", aliasFrame returned) returned
  · exact alias_fallback_run _ _ _ _ _ _
  · exact alias_materialization returned (by simp [returned, TypeSubst.typeVars, TypeSubst.typeVarsList])
  · rfl

/-- A materialized alias exposing another instruction is resumed. Here that
real cons instruction constructs the eventual return marker. -/
theorem function_alias_exposes_instruction (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) :
    let instruction := Atom.expression
      [.symbol "cons-atom", .symbol "return", .expression [.symbol "ok"]]
    CoreStepRel space dispatch live (.expression [.symbol "function", aliasFallback])
      (aliasFrame instruction) (.symbol "ok", aliasFrame instruction) (typing := typing) := by
  intro instruction
  have materialized := alias_materialization instruction
    (by simp [instruction, TypeSubst.typeVars, TypeSubst.typeVarsList])
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.resume space aliasFallback (aliasFrame instruction)
    (.var "pending", aliasFrame instruction) instruction
  · exact alias_fallback_run _ _ _ _ _ _
  · exact materialized
  · rfl
  apply CoreFunctionBodyRel.terminal space instruction (aliasFrame instruction)
    (.expression [.symbol "return", .symbol "ok"], aliasFrame instruction) _
  · apply CoreRunRel.instruction
    · rfl
    · rintro ⟨tail, same⟩
      simp [instruction] at same
    · exact .consAtom space (.symbol "return") [.symbol "ok"] (aliasFrame instruction)
  · exact (BindingMaterializationRel.closed_iff _ _ _ rfl).mpr ⟨rfl, materialized.satisfiable⟩
  · rfl

/-- A binding for a primitive's pending tail does not authorize eagerly
materializing that raw operand inside the primitive instruction. -/
theorem bound_primitive_input_stays_raw (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) :
    BindingMaterializationRel (aliasFrame (.expression [])) (.var "pending") (.expression []) ∧
      ¬∃ result, CoreStepRel space dispatch live
        (.expression [.symbol "cons-atom", .symbol "a", .var "pending"])
        (aliasFrame (.expression [])) result (typing := typing) := by
  refine ⟨alias_materialization _ (by simp [TypeSubst.typeVars, TypeSubst.typeVarsList]), ?_⟩
  rintro ⟨result, step⟩
  generalize sourceEq :
    (Atom.expression [.symbol "cons-atom", .symbol "a", .var "pending"]) = source at step
  cases step <;> simp at sourceEq

/-- A raw producer retains its alias even when its binding theory can expose
a return. Completion provenance is independent of this binding-mode guard. -/
theorem native_raw_alias_is_not_materialized (dispatch : GroundedDispatch)
    (operator : Atom) (arguments : List Atom)
    (raw : dispatch.bindingMode operator arguments = .raw) :
    let returned := Atom.expression [.symbol "return", .symbol "ok"]
    NativeEmissionRel dispatch operator arguments (aliasFrame returned) (.var "pending") (.var "pending") ∧
      ¬NativeEmissionRel dispatch operator arguments (aliasFrame returned) (.var "pending") returned := by
  intro returned
  refine ⟨.raw raw, ?_⟩
  intro emitted
  have same := (NativeEmissionRel.raw_iff raw).mp emitted
  simp [returned] at same

/-- A materialized producer earns that same exposed return from the actual
single-assignment presentation, without a special callback hook. -/
theorem native_materialized_alias_exposes_return (dispatch : GroundedDispatch)
    (operator : Atom) (arguments : List Atom)
    (materialized : dispatch.bindingMode operator arguments = .materialized) :
    let returned := Atom.expression [.symbol "return", .symbol "ok"]
    NativeEmissionRel dispatch operator arguments (aliasFrame returned) (.var "pending") returned := by
  intro returned
  exact .materialized materialized
    (alias_materialization returned (by simp [returned, TypeSubst.typeVars, TypeSubst.typeVarsList]))

/-! ## Dispatch controls -/

private def residualBody (name : String) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "cons-atom", .var name, .expression []], .var "selected",
    .expression [.symbol "return",
      .expression [.symbol "pair", .var "selected", .var name, .var name]]]

private theorem residual_functions_alpha :
    ObservedTypeAlphaRel
      (.expression [.symbol "function", residualBody "residual"])
      (.expression [.symbol "function", residualBody "fresh#residual"]) := by
  refine ⟨.expression [.symbol "function", residualBody "residual"],
    TypeVariableRenamingOf.refl _, ?_⟩
  refine ⟨Equiv.swap "residual" "fresh#residual", (Equiv.swap _ _).injective, ?_⟩
  simp [residualBody, Equiv.swap_apply_def]

/-- A repeated residual variable changes its spelling at several depths,
while function, chain and embedded dispatch and the body alpha witness stay
intact. The two emitted syntactic presentations are genuinely different. -/
theorem residual_function_alpha_preserves_dispatch :
    ObservedTypeAlphaRel (residualBody "residual") (residualBody "fresh#residual") ∧
    IsFunction (.expression [.symbol "function", residualBody "fresh#residual"]) ∧
    IsChain (residualBody "fresh#residual") ∧
    embeddedInstruction (residualBody "fresh#residual") = true ∧
    (Atom.expression [.symbol "function", residualBody "residual"]) ≠
      Atom.expression [.symbol "function", residualBody "fresh#residual"] := by
  obtain ⟨rightBody, rightFunction, alphaBody⟩ :=
    functionBody_of_observedTypeAlpha residual_functions_alpha rfl
  have bodyEquation : rightBody = residualBody "fresh#residual" := by
    simpa using rightFunction.symm
  subst rightBody
  refine ⟨alphaBody, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · simp [residualBody, embeddedInstruction]
  · simp [residualBody]

/-- Alpha transport cannot relate an unresolved variable to a function,
regardless of the function body's private variables or depth. -/
theorem unresolved_variable_not_alpha_function (name : String) (body : Atom) :
    ¬ObservedTypeAlphaRel (.var name) (.expression [.symbol "function", body]) := by
  intro alpha
  have function := (isFunction_of_observedTypeAlpha_iff alpha).mpr ⟨body, rfl⟩
  simp [IsFunction] at function

/-- Normalizing an assigned function alias can change all three dispatch
observations. It is not a permitted alpha-renaming of the unresolved input. -/
theorem function_alias_materialization_changes_dispatch (body : Atom) :
    let unresolved : Atom := .var "pending"
    let materialized := Spec.Type.Presentation.TypeSubst.apply
      [("pending", .expression [.symbol "function", body])] unresolved
    ¬IsFunction unresolved ∧ IsFunction materialized ∧
      (¬∃ tail, unresolved = .expression (.symbol "function" :: tail)) ∧
      (∃ tail, materialized = .expression (.symbol "function" :: tail)) ∧
      embeddedInstruction unresolved = false ∧ embeddedInstruction materialized = true ∧
      ¬ObservedTypeAlphaRel unresolved materialized := by
  dsimp only
  have normalized : Spec.Type.Presentation.TypeSubst.apply
      [("pending", .expression [.symbol "function", body])] (.var "pending") =
      .expression [.symbol "function", body] := by
    simp [Spec.Type.Presentation.TypeSubst.apply, Spec.Type.Presentation.TypeSubst.lookup]
  rw [normalized]
  exact ⟨by simp [IsFunction], ⟨body, rfl⟩, by simp,
    ⟨[body], rfl⟩, rfl, by simp [embeddedInstruction],
    unresolved_variable_not_alpha_function "pending" body⟩

/-- A malformed two-body wrapper is embedded and function-headed on both
alpha sides, yet neither side satisfies the source's exact function guard. -/
theorem malformed_function_alpha_keeps_guard_distinction :
    ObservedTypeAlphaRel
      (.expression [.symbol "function", .var "residual", .var "residual"])
      (.expression [.symbol "function", .var "fresh#residual", .var "fresh#residual"]) ∧
    (∃ tail, (Atom.expression [.symbol "function", .var "fresh#residual", .var "fresh#residual"]) =
      Atom.expression (.symbol "function" :: tail)) ∧
    ¬IsFunction (.expression [.symbol "function", .var "fresh#residual", .var "fresh#residual"]) ∧
    embeddedInstruction
      (.expression [.symbol "function", .var "fresh#residual", .var "fresh#residual"]) = true := by
  refine ⟨?_, ⟨[.var "fresh#residual", .var "fresh#residual"], rfl⟩, ?_, ?_⟩
  · refine ⟨.expression [.symbol "function", .var "residual", .var "residual"],
      TypeVariableRenamingOf.refl _, ?_⟩
    refine ⟨Equiv.swap "residual" "fresh#residual", (Equiv.swap _ _).injective, ?_⟩
    simp
  · simp [IsFunction]
  · simp [embeddedInstruction]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-! ## Shared residuals and diagnostic-policy controls -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.DiagnosticControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement

private def noForeign : GroundedDispatch where
  executable := fun _=>False
  outcome := fun _ _ _=>False

def source : Atom := .expression [.symbol "unify",.var "a",.symbol "A",.symbol "B"]
def target : Atom := .expression [.symbol "unify",.var "b",.symbol "A",.symbol "B"]
def exchange : Equiv.Perm String := Equiv.swap "a" "b"

theorem source_renames : renameTypeVars exchange source=target := by
  simp [source,target,exchange]

/-- Printed diagnostic text is a symbol payload; ordinary variable renaming
cannot rewrite the spelling already rendered inside that payload. -/
theorem rendered_text_not_equivariant :
    renameTypeVars exchange (mkUnifyBadArityError source) ≠ mkUnifyBadArityError target := by
  change renameTypeVars exchange (Atom.error source (.symbol (unifyBadArityMessage source))) ≠
    Atom.error target (.symbol (unifyBadArityMessage target))
  rw [atom_error,source_renames,atom_symbol]
  decide +kernel

theorem source_call : CallRel Space.empty noForeign [] source Atom.undefinedType Bindings.empty
    (mkUnifyBadArityError source,Bindings.empty) := by
  exact (Minimal.ordinary_unify_bad_arity_exact
    (tail := [.var "a", .symbol "A", .symbol "B"])
    (by simp [Minimal.HostCall, noForeign]) (by decide)).mpr rfl

theorem target_call : CallRel Space.empty noForeign [] target Atom.undefinedType Bindings.empty
    (mkUnifyBadArityError target,Bindings.empty) := by
  exact (Minimal.ordinary_unify_bad_arity_exact
    (tail := [.var "b", .symbol "A", .symbol "B"])
    (by simp [Minimal.HostCall, noForeign]) (by decide)).mpr rfl

/-- Raw text remains observable if a client asks for literal error atoms.
It is not a variable-only alpha observation. -/
theorem target_rejects_renamed_source_text :
    ¬CallRel Space.empty noForeign [] target Atom.undefinedType Bindings.empty
      (renameTypeVars exchange (mkUnifyBadArityError source),Bindings.empty) := by
  intro derived
  have actual := (Minimal.ordinary_unify_bad_arity_exact
    (tail := [.var "b", .symbol "A", .symbol "B"])
    (by simp [Minimal.HostCall, noForeign]) (by decide)).mp derived
  exact rendered_text_not_equivariant (congrArg Prod.fst actual)

/-- Exact source transport uses the named transported renderer rather than
claiming the unchanged text renderer is equivariant. -/
theorem transported_policy_call :
    CallRel Space.empty (dispatch exchange noForeign) [] target Atom.undefinedType Bindings.empty
      (renameTypeVars exchange (mkUnifyBadArityError source),Bindings.empty) := by
  have mapped := (Minimal.ordinary_unify_bad_arity_exact
    (space := Space.empty) (dispatch := dispatch exchange noForeign) (live := [])
    (typing := publishedTypeService) (expected := Atom.undefinedType)
    (tail := [.var "b", .symbol "A", .symbol "B"])
    (bindings := BindingFrame.historical Bindings.empty)
    (by simp [Minimal.HostCall, dispatch, noForeign]) (by decide)).mpr rfl
  change CallRel Space.empty (dispatch exchange noForeign) [] target Atom.undefinedType Bindings.empty
    (mkErrorMessage target ((dispatch exchange noForeign).unifyBadArityMessage target),
      Bindings.empty) at mapped
  rw [←source_renames,malformed_call_error] at mapped
  simpa [source_renames,noForeign,mkUnifyBadArityError] using mapped

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.DiagnosticControls

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Eval.Minimal

private def sourceBody (residual slot : String) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "cons-atom",.var residual,.expression []],.var slot,
    .expression [.symbol "return",.expression [.symbol "pair",.var slot,.var residual]]]

private def outputPair (residual : String) : Atom :=
  .expression [.symbol "pair",.expression [.var residual],.var residual]

/-- The actual source chain retains a shared residual while substituting its
chosen value into the structural destination slot. -/
theorem open_function_source (context : Space) (service : GroundedDispatch)
    (live : List Atom) (types : EvalTypeService) (residual slot : String)
    (distinct : residual ≠ slot) :
    CoreStepRel context service live
      (.expression [.symbol "function",sourceBody residual slot]) Bindings.empty
      (outputPair residual,Bindings.empty) (typing:=types) := by
  apply CoreStepRel.functionReturn
  · exact ⟨_,rfl⟩
  apply CoreFunctionBodyRel.terminal context _ Bindings.empty
    (.expression [.symbol "return",outputPair residual],Bindings.empty) _
  · apply CoreRunRel.chain context _ Bindings.empty
      (.expression [.symbol "return",outputPair residual],Bindings.empty)
    · exact ⟨_,rfl⟩
    · have step := CoreStepRel.chain (dispatch:=service) (typing:=types) (protectedScope:=[])
        (live:=.expression [.symbol "function",sourceBody residual slot]::live)
        (caller:=some (.expression [.symbol "function",sourceBody residual slot]))
        context (.expression [.symbol "cons-atom",.var residual,.expression []]) slot
        (.expression [.symbol "return",.expression [.symbol "pair",.var slot,.var residual]])
        Bindings.empty (.expression [.var residual],Bindings.empty) (.expression [.var residual])
        (.instruction _ _ _ _ (by rfl) (by simp [Minimal.IsChain]) (.consAtom _ _ _ _))
        (BindingMaterializationRel.empty _)
      simpa [sourceBody,outputPair,substituteName,distinct] using step
    · exact .data _ _ _ (by rfl)
  · exact BindingMaterializationRel.empty _
  · rfl

/-- The complete source action renames the destination and both occurrences
of the shared residual together; the reached record is retained exactly. -/
theorem open_function_renamed (context : Space) (service : GroundedDispatch)
    (live : List Atom) (types : EvalTypeService) (p : Equiv.Perm String) :
    CoreStepRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (.expression [.symbol "function",sourceBody (p "residual") (p "slot")]) Bindings.empty
      (outputPair (p "residual"),Bindings.empty) (typing:=typing p types) := by
  have original := open_function_source context service live types "residual" "slot" (by decide)
  simpa [sourceBody, outputPair, frameResult] using core_step p original

/-- A single residual-name action cannot split one shared variable into two
different names. This excludes independent per-component alpha witnesses. -/
theorem shared_residual_cannot_split :
    ¬∃ p : Equiv.Perm String,
      renameTypeVars p (.expression [.symbol "pair",.var "x",.var "x"]) =
        .expression [.symbol "pair",.var "y",.var "z"] := by
  rintro ⟨p,same⟩
  simp only [renameTypeVars,List.map_cons,List.map_nil,Atom.expression.injEq,List.cons.injEq,
    Atom.var.injEq,true_and,and_true] at same
  exact (by decide : "y" ≠ "z") (same.1.symm.trans same.2)

/-- Equal result values at distinct physical positions remain two outputs. -/
theorem duplicate_positions_retained (p : Equiv.Perm String) (value : Atom) (bindings : Bindings) :
    (results p [(value,bindings),(value,bindings)]).length=2 ∧
      (results p [(value,bindings),(value,bindings)])[0]? = some (result p (value,bindings)) ∧
      (results p [(value,bindings),(value,bindings)])[1]? = some (result p (value,bindings)) := by
  simp [results]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.Controls

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.OrdinaryInvocationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal Spec.Eval.Steps Spec.Match.Merge
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

def dispatch : Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

def seven : Atom := .grounded (.int 7)
def returnSeven : Atom := .expression [.symbol "return", seven]
def functionSeven : Atom := .expression [.symbol "function", returnSeven]
def functionArrow : Atom := .expression [.symbol "->", Atom.atomType, Atom.atomType]
def annotatedContext : Space :=
  ⟨[.expression [.symbol ":", .symbol "function", functionArrow]]⟩

theorem annotation_has_no_equation (live : List Atom) (query : Atom)
    (bindings : Bindings) :
    EquationQueryNoMatchRel annotatedContext live query bindings := by
  intro freshPattern freshRhs matched hit
  obtain ⟨rawLhs, rawRhs, stored, _⟩ := hit
  simp [annotatedContext] at stored

/-- Every actual return body retains the complete input frame. -/
theorem immediate_return_step_exact (live : List Atom) (caller : Option Atom)
    (frame : BindingFrame) (result : FrameResult) :
    CoreStepRel annotatedContext dispatch live functionSeven frame result
        (caller := caller) ↔
      BindingFrame.Materialization frame seven seven ∧ result = (seven, frame) := by
  change CoreStepRel annotatedContext dispatch live
    (.expression [.symbol "function", returnSeven]) frame result
      (caller := caller) ↔ _
  rw [function_step_body_terminal_iff]
  constructor
  · rintro ⟨_, terminal, output, body, same⟩
    obtain ⟨value, materialized, pair⟩ := function_return_body_exact.mp body
    have closed : value = seven := materialized.closed_result rfl
    subst value
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    exact ⟨materialized, by simpa only [functionTerminalResult] using same⟩
  · rintro ⟨materialized, rfl⟩
    refine ⟨⟨[.symbol "return", seven], rfl⟩,
      .expression [.symbol "return", seven], frame, ?_, rfl⟩
    exact function_return_body_exact.mpr ⟨seven, materialized, rfl⟩

theorem immediate_return_run_exact (live : List Atom) (caller : Option Atom)
    (frame : BindingFrame) (result : FrameResult) :
    CoreRunRel annotatedContext dispatch live functionSeven frame result
        (caller := caller) ↔
      BindingFrame.Materialization frame seven seven ∧ result = (seven, frame) := by
  constructor
  · intro run
    cases run with
    | data _ _ _ noninstruction =>
      simp [functionSeven, embeddedInstruction] at noninstruction
    | instruction _ _ _ _ _ _ step =>
      exact (immediate_return_step_exact live caller frame result).mp step
    | chain _ _ _ _ _ chain _ _ =>
      simp [functionSeven, Minimal.IsChain] at chain
  · intro result
    apply CoreRunRel.instruction
    · rfl
    · simp [functionSeven, Minimal.IsChain]
    · exact (immediate_return_step_exact live caller frame _).mpr result

theorem selected_empty_certificate : ReadoutCertificate Bindings.empty [] :=
  ReadoutCertificate.of_fold (.nil [])

def selectedEmpty : BindingFrame :=
  .selected Bindings.empty [] selected_empty_certificate

/-- The pure return retains the selected readout, rather than reconstructing
an historical frame from its equal raw rows. -/
theorem selected_function_keeps_exact_frame (live : List Atom) (caller : Option Atom) :
    CoreInvocationRel annotatedContext dispatch live functionSeven selectedEmpty
      (seven, selectedEmpty) (caller := caller) := by
  apply CoreInvocationRel.embedded
  · rintro ⟨operator, arguments, _, executable⟩
    exact executable
  · rfl
  · apply (immediate_return_run_exact live caller selectedEmpty _).mpr
    exact ⟨by change seven = TypeSubst.apply [] seven; simp only [seven, TypeSubst.apply], rfl⟩

theorem selected_frame_is_not_historical :
    selectedEmpty ≠ BindingFrame.historical Bindings.empty := by
  intro same
  cases same

private theorem merge_empty_empty :
    MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) .nil

private theorem function_arrow_matches :
    TypeMatchRel functionArrow functionArrow Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural <;>
    try simp [functionArrow, Atom.undefinedType, Atom.atomType]
  · apply MatchRel.expression _ semanticLoopFree_empty
    exact .cons (.symSym "->" semanticLoopFree_empty) merge_empty_empty
      (.cons (.symSym "Atom" semanticLoopFree_empty) merge_empty_empty
        (.cons (.symSym "Atom" semanticLoopFree_empty) merge_empty_empty .nil))
  · exact merge_empty_empty

private theorem function_types :
    TypesOfRel annotatedContext (.symbol "function") [functionArrow] :=
  .symbolKnown (.hit .nil) (by simp)

private theorem return_seven_type :
    TypeOfRel annotatedContext returnSeven Atom.undefinedType := by
  refine ⟨[Atom.undefinedType], .expressionUndefined ?_, by simp⟩
  exact .skip (by intro type; simp) .nil


private theorem no_host (atom : Atom) : ¬HostCall dispatch atom := by
  rintro ⟨_, _, _, executable⟩
  exact executable

/-- Actual minimal invocation and the ordinary Atom return gate preserve
both the value and the complete reached frame. -/
theorem ordinary_function_at_atom_exact (live : List Atom) (frame : BindingFrame)
    (result : FrameResult) :
    CallRel annotatedContext dispatch live functionSeven Atom.atomType frame result ↔
      frame.Materialization seven seven ∧ result = (seven, frame) := by
  rw [ordinary_embedded_exact (by simp [IsErrorRel, functionSeven])
    (no_host _) (by rfl)]
  constructor
  · rintro ⟨raw, invoked, returned⟩
    have ran := (raw_embedded_exact (no_host _) (by rfl)).mp invoked
    obtain ⟨materialized, rfl⟩ :=
      (immediate_return_run_exact (Atom.atomType :: live) none frame raw).mp ran
    have evaluated := (CallReturnRel.evaluate_iff
      (by simp [seven, Atom.notReducible])
      (by simp [seven, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])).mp returned
    refine ⟨materialized, ?_⟩
    cases evaluated with
    | typePass => rfl
    | emptyOrError _ _ _ stopped =>
        simp [seven, IsEmptyOrErrorRel, IsErrorRel, Atom.empty] at stopped
    | cast _ _ _ _ _ _ _ doesNotPass _ _ => exact (doesNotPass (Or.inl rfl)).elim
    | interpretSuccess _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
    | interpretError _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
  · rintro ⟨materialized, rfl⟩
    refine ⟨(seven, frame),
      (raw_embedded_exact (no_host _) (by rfl)).mpr
        ((immediate_return_run_exact _ none frame _).mpr ⟨materialized, rfl⟩), ?_⟩
    apply CallReturnRel.evaluate
    · simp [seven, Atom.notReducible]
    · simp [seven, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact (full_atom_expected_exact.mpr rfl).1

theorem ordinary_function_returns_seven (live : List Atom) :
    CallRel annotatedContext dispatch live functionSeven Atom.atomType Bindings.empty
      (seven, Bindings.empty) :=
  (ordinary_function_at_atom_exact live _ _).mpr
    ⟨BindingMaterializationRel.empty seven, rfl⟩

/-- The formerly admitted unchanged wrapper is now excluded at its real
selected call demand, even when the initial frame is selected. -/
theorem ordinary_function_cannot_remain_wrapper (live : List Atom)
    (frame output : BindingFrame) :
    ¬CallRel annotatedContext dispatch live functionSeven Atom.atomType frame
      (functionSeven, output) := by
  intro called
  have same := (ordinary_function_at_atom_exact live frame _).mp called |>.2
  have values := congrArg Prod.fst same
  simp [functionSeven, seven] at values

theorem ordinary_function_keeps_selected_frame (live : List Atom) :
    CallRel annotatedContext dispatch live functionSeven Atom.atomType selectedEmpty
      (seven, selectedEmpty) :=
  (ordinary_function_at_atom_exact live selectedEmpty _).mpr
    ⟨by change seven = TypeSubst.apply [] seven; simp only [seven, TypeSubst.apply], rfl⟩

theorem ordinary_function_cannot_erase_selected_frame (live : List Atom) :
    ¬CallRel annotatedContext dispatch live functionSeven Atom.atomType selectedEmpty
      (seven, BindingFrame.historical Bindings.empty) := by
  intro called
  have same := (ordinary_function_at_atom_exact live selectedEmpty _).mp called |>.2
  exact selected_frame_is_not_historical (congrArg Prod.snd same).symm

theorem full_evaluation_returns_seven :
    EvalAtomRawRel annotatedContext dispatch [] functionSeven Atom.undefinedType
      Bindings.empty (seven, Bindings.empty) := by
  have headEval : EvalAtomRawRel annotatedContext dispatch
      [functionArrow, returnSeven, Atom.atomType]
      (protectedScope := expectedApplicationScope functionSeven Atom.undefinedType)
      (.symbol "function") functionArrow Bindings.empty
      (.symbol "function", Bindings.empty) := by
    apply EvalAtomRawRel.cast (.symbol "function") functionArrow Atom.symbolType
      Bindings.empty (.symbol "function", Bindings.empty)
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .symbol "function"
    · simp [functionArrow, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨"function", rfl⟩
    · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
        (actualType := functionArrow) function_types rfl
      · simp
      · exact function_arrow_matches
    · exact .historical _ _
  have argsEval : InterpretArgsRel annotatedContext dispatch
      [.symbol "function", Atom.atomType] [returnSeven] [Atom.atomType] Bindings.empty
      (argumentPacket [returnSeven], Bindings.empty) := by
    apply InterpretArgsRel.success returnSeven [] Atom.atomType [] Bindings.empty
      (returnSeven, Bindings.empty) (argumentPacket [], Bindings.empty)
    · apply EvalAtomRawRel.typePass returnSeven Atom.atomType Atom.expressionType Bindings.empty
      · simp [returnSeven, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · exact .expression [.symbol "return", seven]
      · exact Or.inl rfl
    · exact Or.inr rfl
    · exact .nil _
    · exact ⟨[], rfl⟩
  apply EvalAtomRawRel.interpretSuccess functionSeven Atom.undefinedType Atom.expressionType
    Bindings.empty (seven, Bindings.empty)
  · simp [functionSeven, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .expression [.symbol "function", returnSeven]
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "function", [returnSeven], rfl⟩
  · apply InterpretExpressionRel.functionPath functionSeven Atom.undefinedType
      (.symbol "function") [returnSeven] [functionArrow] [functionArrow]
      ⟨functionArrow, [Atom.atomType], Atom.atomType, rfl⟩ Atom.atomType
      Bindings.empty Bindings.empty (functionSeven, Bindings.empty)
      (seven, Bindings.empty) rfl function_types rfl
    · apply FunctionCandidateScanRel.functionSuccess (argumentTypes := [Atom.atomType])
        (returnType := Atom.atomType) rfl
      exact .success rfl (.success (.mk rfl rfl
        (.cons return_seven_type (.atomLeft _ _) (.nil _)) (.undefinedLeft _ _)))
    · exact .historical _ _
    · simp [Atom.atomType, Atom.expressionType]
    · exact .success functionSeven functionArrow Atom.undefinedType (.symbol "function")
        Atom.atomType [returnSeven] [Atom.atomType] Bindings.empty
        (.symbol "function", Bindings.empty) (argumentPacket [returnSeven], Bindings.empty)
        rfl rfl headEval (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) argsEval
        ⟨[returnSeven], rfl⟩
    · exact ordinary_function_returns_seven []
  · simp [seven, IsErrorRel]

/-- The raw witness survives the public success-priority observation. -/
theorem public_evaluation_returns_seven :
    EvalRel annotatedContext dispatch [] functionSeven Atom.undefinedType
      Bindings.empty (seven, Bindings.empty) := by
  refine ⟨full_evaluation_returns_seven, ?_⟩
  intro impossible
  simp [IsErrorRel, seven] at impossible


def fCall : Atom := .expression [.symbol "f"]
def value : Atom := .symbol "Value"
def fContext : Space := ⟨[.expression [.symbol "=", fCall, value]]⟩
def unifyCall : Atom :=
  .expression [.symbol "unify", .symbol "X", .symbol "X", fCall, .symbol "Fail"]


theorem unify_selects_raw_template :
    UnifyStep (.symbol "X") (.symbol "X") fCall (.symbol "Fail")
      Bindings.empty fCall Bindings.empty := by
  apply UnifyStep.success
  refine ⟨⟨Bindings.empty, .symSym "X" semanticLoopFree_empty, logical_merge_empty⟩, ?_⟩
  · intro valuation _
    rfl


theorem raw_invocation_selects_template (live : List Atom) (caller : Option Atom) :
    CoreInvocationRel fContext dispatch live unifyCall Bindings.empty
      (fCall, Bindings.empty) (caller := caller) := by
  apply CoreInvocationRel.embedded
  · rintro ⟨operator, arguments, _, executable⟩
    exact executable
  · rfl
  · apply CoreRunRel.instruction
    · rfl
    · simp [unifyCall, Minimal.IsChain]
    · apply CoreStepRel.unifySuccess
      · cases unify_selects_raw_template with
        | success selected => exact selected.1
      · exact .historical _ _
      · exact BindingMaterializationRel.empty _


private theorem symbol_types (name : String) :
    TypesOfRel fContext (.symbol name) [Atom.undefinedType] := by
  apply TypesOfRel.symbolUndefined
  exact .skip (by intro type; simp) .nil

theorem symbol_evaluates (live : List Atom) (name : String) :
    EvalAtomRawRel fContext dispatch live (.symbol name) Atom.undefinedType
      Bindings.empty (.symbol name, Bindings.empty) := by
  by_cases empty : name = "Empty"
  · subst name
    exact .emptyOrError _ _ _ (Or.inl rfl)
  apply EvalAtomRawRel.cast (.symbol name) Atom.undefinedType Atom.symbolType
    Bindings.empty (.symbol name, Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, empty]
  · exact .symbol name
  · simp [Atom.undefinedType, Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨name, rfl⟩
  · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
      (actualType := Atom.undefinedType) (symbol_types name) rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .historical _ _

theorem f_query (live : List Atom) :
    EquationQueryCandidateRel fContext live fCall Bindings.empty value Bindings.empty := by
  refine ⟨fCall, value, Bindings.empty, ?_, logical_merge_empty, ?_⟩
  · refine ⟨fCall, value, ?_, ?_, ?_⟩
    · simp [fContext]
    · refine ⟨id, Function.injective_id,
        .expression (.cons (.symbol "f") .nil), .symbol "Value", ?_⟩
      intro name occurs
      rcases occurs with occurs | occurs
      · cases occurs with
        | expression member child =>
          simp at member
          subst_vars
          cases child
      · cases occurs
    · exact .expression (.cons (.symSym "f" semanticLoopFree_empty) merge_empty_empty .nil)
        semanticLoopFree_empty
  · intros
    rfl

theorem f_evaluates (live : List Atom) :
    EvalAtomRawRel fContext dispatch live fCall Atom.undefinedType
      Bindings.empty (value, Bindings.empty) := by
  apply EvalAtomRawRel.interpretSuccess fCall Atom.undefinedType Atom.expressionType
    Bindings.empty (value, Bindings.empty)
  · simp [fCall, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .expression [.symbol "f"]
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "f", [], rfl⟩
  · apply InterpretExpressionRel.tuplePath fCall Atom.undefinedType (.symbol "f") []
      [Atom.undefinedType] [Atom.undefinedType] [] Bindings.empty (fCall, Bindings.empty)
      (value, Bindings.empty) rfl (symbol_types "f") rfl
    · apply FunctionCandidateScanRel.nonFunctionExhausted
      · rintro ⟨argumentTypes, returnType, equation⟩
        simp [FunctionTypeRel, Atom.undefinedType] at equation
      · exact .nil
    · exact .singleton (.symbol "f") Bindings.empty (.symbol "f", Bindings.empty)
        (symbol_evaluates _ "f") (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    · apply CallRel.equation (emitted := value) (materialized := value)
        (merged := BindingFrame.historical Bindings.empty)
        (completed := (value, BindingFrame.historical Bindings.empty))
      · simp [fCall, IsErrorRel]
      · simp [fCall, NonGroundedCallRel, HostCall, embeddedInstruction, dispatch]
      · exact f_query _
      · exact .historical _ _
      · exact BindingMaterializationRel.empty value
      · exact .raw _ _ _ (by rintro ⟨body, equal⟩; simp [value] at equal)
      · apply CallReturnRel.evaluate
        · simp [value, Atom.notReducible]
        · simp [value, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
        · exact symbol_evaluates _ "Value"
  · simp [value, IsErrorRel]

/-- The existing return gate computes the raw selection at Undefined demand. -/
theorem selected_template_computes_at_undefined (live : List Atom) :
    CallReturnRel fContext dispatch live unifyCall Atom.undefinedType fCall Bindings.empty
      (value, Bindings.empty) := by
  apply CallReturnRel.evaluate
  · simp [fCall, Atom.notReducible]
  · simp [fCall, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact f_evaluates live

/-- The same gate holds that exact raw selection under an Atom demand. -/
theorem selected_template_is_held_at_atom (live : List Atom) :
    CallReturnRel fContext dispatch live unifyCall Atom.atomType fCall Bindings.empty
      (fCall, Bindings.empty) := by
  apply CallReturnRel.evaluate
  · simp [fCall, Atom.notReducible]
  · simp [fCall, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · apply EvalAtomRawRel.typePass fCall Atom.atomType Atom.expressionType Bindings.empty
    · simp [fCall, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .expression [.symbol "f"]
    · exact Or.inl rfl


/-- Ordinary unify resumes its selected template under the actual demand. -/
theorem ordinary_unify_computes_template (live : List Atom) :
    CallRel fContext dispatch live unifyCall Atom.undefinedType Bindings.empty
      (value, Bindings.empty) := by
  apply CallRel.embedded (raw := (fCall, Bindings.empty))
  · simp [unifyCall, IsErrorRel]
  · exact no_host _
  · rfl
  · exact raw_invocation_selects_template _ none
  · exact selected_template_computes_at_undefined live

theorem ordinary_unify_holds_template_at_atom (live : List Atom) :
    CallRel fContext dispatch live unifyCall Atom.atomType Bindings.empty
      (fCall, Bindings.empty) := by
  apply CallRel.embedded (raw := (fCall, Bindings.empty))
  · simp [unifyCall, IsErrorRel]
  · exact no_host _
  · rfl
  · exact raw_invocation_selects_template _ none
  · exact selected_template_is_held_at_atom live

/-- Raw invocation retains the template; ordinary invocation computes it. -/
theorem raw_and_ordinary_unify_have_distinct_observations (live : List Atom) :
    CoreInvocationRel fContext dispatch live unifyCall Bindings.empty
      (fCall, Bindings.empty) ∧
    CallRel fContext dispatch live unifyCall Atom.undefinedType Bindings.empty
      (value, Bindings.empty) ∧ fCall ≠ value := by
  exact ⟨raw_invocation_selects_template live none, ordinary_unify_computes_template live,
    by simp [fCall, value]⟩

/-- A library name has no intrinsic switch behavior in an empty equation space. -/
theorem switch_without_library_is_unreduced (live : List Atom) (expected : Atom) :
    CallRel Space.empty dispatch live
      (.expression [.symbol "switch-minimal", .symbol "X", .expression []])
      expected Bindings.empty
      (.expression [.symbol "switch-minimal", .symbol "X", .expression []], Bindings.empty) := by
  apply CallRel.noEquation
  · simp [IsErrorRel]
  · exact ⟨no_host _, by rfl⟩
  · intro lhs rhs matched hit
    obtain ⟨left, right, stored, _⟩ := hit
    simp [Space.empty] at stored

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.OrdinaryInvocationControls

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.UnifyReadoutControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Steps Spec.Match.Merge
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

def dispatch : Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

def outputBindings : Bindings := Bindings.empty.assign "x" (.symbol "B")
def outputTable : TypeSubst := [("x", .symbol "B")]

theorem output_certificate : ReadoutCertificate outputBindings outputTable := by
  apply ReadoutCertificate.of_fold
  simpa [outputBindings, outputTable, Bindings.assign, Bindings.empty,
    Bindings.isBound, Bindings.lookup] using
    single_assignment_presentation "x" (.symbol "B") (by simp [TypeSubst.typeVars])

def initial : BindingFrame := .selected Bindings.empty [] (ReadoutCertificate.of_fold (.nil []))
def reached : BindingFrame := .selected outputBindings outputTable output_certificate
def template : Atom := .expression [.symbol "pair", .var "x", .var "x", .grounded (.string "$x")]
def observed : Atom := .expression [.symbol "pair", .symbol "B", .symbol "B", .grounded (.string "$x")]
def invocation : Atom := .expression [.symbol "unify", .var "x", .symbol "B", template, .symbol "Fail"]

theorem actual_candidate : UnifyCandidateRel (.var "x") (.symbol "B") Bindings.empty outputBindings := by
  have loop : SemanticLoopFree outputBindings :=
    semanticLoopFree_single_assignment (by intro occurs; cases occurs)
  refine ⟨outputBindings, .varNonVar rfl loop, ?_⟩
  apply MergeRel.logicalMerge (.mk (by simp [constraints, Bindings.empty]) .nil)
  exact ⟨fun _ => .symbol "B", by
    simp [outputBindings, Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      Spec.Type.RuntimeRefinement.applyTypeValuation, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup]⟩

/-- One successful source primitive rewrites both pending references through
the same reached table. A string containing the variable's spelling is data. -/
theorem success_reads_both_and_preserves_text (space : Space) (live : List Atom)
    (caller : Option Atom) :
    CoreStepRel space dispatch live invocation initial (observed, reached) (caller := caller) := by
  apply CoreStepRel.unifySuccess
  · exact actual_candidate
  · exact .selected _ _
  · change observed = outputTable.apply template
    simp [observed, outputTable, template, TypeSubst.apply, TypeSubst.lookup]

/-- Matching constraints do not license publishing the unread template. -/
theorem success_cannot_return_unread_template (space : Space) (live : List Atom)
    (caller : Option Atom) :
    ¬CoreStepRel space dispatch live invocation initial (template, reached) (caller := caller) := by
  intro step
  rcases unify_step_exact.mp step with ⟨_, _, read⟩ | ⟨missing, _⟩
  · change template = outputTable.apply template at read
    simp [template, outputTable, TypeSubst.apply, TypeSubst.lookup] at read
  · exact missing _ actual_candidate

theorem mismatch : UnifyNoMatchRel (.symbol "A") (.symbol "C") outputBindings := by
  rintro output ⟨matched, matching, _⟩
  exact symbol_mismatch_not_match (by decide) matched matching

/-- Refusal returns the raw fallback and the identical selected activation,
even though that activation assigns the fallback variable. -/
theorem no_match_retains_raw_fallback_and_frame (space : Space) (live : List Atom)
    (caller : Option Atom) :
    CoreStepRel space dispatch live
      (.expression [.symbol "unify", .symbol "A", .symbol "C", template, .var "x"])
      reached (.var "x", reached) (caller := caller) :=
  .unifyNoMatch _ _ _ _ _ _ mismatch

theorem no_match_cannot_materialize_fallback (space : Space) (live : List Atom)
    (caller : Option Atom) :
    ¬CoreStepRel space dispatch live
      (.expression [.symbol "unify", .symbol "A", .symbol "C", template, .var "x"])
      reached (.symbol "B", reached) (caller := caller) := by
  intro step
  rcases unify_step_exact.mp step with ⟨matched, _⟩ | ⟨_, same⟩
  · exact mismatch _ matched
  · cases same

theorem no_match_cannot_erase_selected_frame (space : Space) (live : List Atom)
    (caller : Option Atom) :
    ¬CoreStepRel space dispatch live
      (.expression [.symbol "unify", .symbol "A", .symbol "C", template, .var "x"])
      reached (.var "x", BindingFrame.historical outputBindings) (caller := caller) := by
  intro step
  rcases unify_step_exact.mp step with ⟨matched, _⟩ | ⟨_, same⟩
  · exact mismatch _ matched
  · have frames := congrArg Prod.snd same
    cases frames

/-- Ordinary invocation consumes the exact primitive readout and preserves
its selected frame through the Atom-demand return gate. -/
theorem ordinary_success_at_atom (space : Space) (live : List Atom) :
    CallRel space dispatch live invocation Atom.atomType initial (observed, reached) := by
  apply CallRel.embedded (raw := (observed, reached))
  · simp [invocation, IsErrorRel]
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · apply CoreInvocationRel.embedded
    · rintro ⟨_, _, _, executable⟩
      exact executable
    · rfl
    · exact .instruction _ _ _ _ rfl (by simp [invocation, Minimal.IsChain])
        (success_reads_both_and_preserves_text space _ none)
  · apply CallReturnRel.evaluate
    · simp [observed, Atom.notReducible]
    · simp [observed, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact (full_atom_expected_exact.mpr rfl).1

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.UnifyReadoutControls

/-! ## Exhausted equation invocation and reached binding readout -/

section
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Steps

/-- No surviving equation candidate restores the complete ordinary invocation
and its reached frame, rather than inventing a successful empty answer. -/
theorem ordinary_all_filtered_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expected : Atom}
    {frame : BindingFrame} {result : FrameResult}
    (nonerror : ¬IsErrorRel atom) (nonGrounded : NonGroundedCallRel dispatch atom)
    (filtered : EquationQueryAllFilteredRel space (expected :: live) atom frame) :
    CallRel space dispatch live atom expected frame result (typing := typing) ↔
      result = (atom, frame) := by
  constructor
  · intro called
    cases called
    all_goals first
      | rfl
      | exact False.elim (filtered.2 _ _ (by assumption))
      | simp_all [NonGroundedCallRel, HostCall]
  · rintro rfl
    exact .allEquationsFiltered _ _ _ nonerror nonGrounded filtered

/-- Raw invocation uses one refusal sentinel after all matches have been
filtered. No completed answer or replacement binding frame is synthesized. -/
theorem raw_all_filtered_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {caller : Option Atom} {atom : Atom}
    {frame : BindingFrame} {result : FrameResult}
    (noHost : ¬HostCall dispatch atom) (notEmbedded : embeddedInstruction atom = false)
    (filtered : EquationQueryAllFilteredRel space live atom frame) :
    CoreInvocationRel space dispatch live atom frame result
        (typing := typing) (caller := caller) ↔
      result = (Atom.notReducible, frame) := by
  constructor
  · intro invoked
    cases invoked
    all_goals first
      | rfl
      | exact False.elim (filtered.2 _ _ (by assumption))
      | simp_all [HostCall]
  · rintro rfl
    exact .allEquationsFiltered _ _ _ noHost notEmbedded filtered

/-- The ordinary return gate restores exactly the saved invocation on raw
refusal, independently of the demanded type and selected readout instance. -/
theorem call_return_not_reducible_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {original expected : Atom}
    {frame : BindingFrame} {result : FrameResult} :
    CallReturnRel space dispatch live original expected Atom.notReducible frame result
        (typing := typing) ↔ result = (original, frame) := by
  constructor
  · intro returned
    cases returned <;> simp_all [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty]
  · rintro rfl
    exact .notReducible _ _ _

/-- Equation calls factor through the same raw invocation and ordinary return
gate as embedded calls. Both exhausted-query cases use the raw refusal
protocol; a successful rule keeps its actual intermediate binding frame. -/
theorem ordinary_equation_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expected : Atom}
    {frame : BindingFrame} {result : FrameResult}
    (nonerror : ¬IsErrorRel atom) (nonGrounded : NonGroundedCallRel dispatch atom) :
    CallRel space dispatch live atom expected frame result (typing := typing) ↔
      ∃ raw, CoreInvocationRel space dispatch (expected :: live)
        atom frame raw (typing := typing) ∧
        CallReturnRel space dispatch live atom expected raw.1 raw.2 result
          (typing := typing) := by
  constructor
  · intro called
    cases called
    all_goals first
      | exact ⟨_, CoreInvocationRel.equation _ _ _ _ _ _ _
          nonGrounded.1 nonGrounded.2 (by assumption) (by assumption)
          (by assumption) (by assumption), by assumption⟩
      | exact ⟨(Atom.notReducible, frame), CoreInvocationRel.noEquation _ _ _
          nonGrounded.1 nonGrounded.2 (by assumption), .notReducible _ _ _⟩
      | exact ⟨(Atom.notReducible, frame), CoreInvocationRel.allEquationsFiltered _ _ _
          nonGrounded.1 nonGrounded.2 (by assumption), .notReducible _ _ _⟩
      | simp_all [NonGroundedCallRel, HostCall]
  · rintro ⟨raw, invoked, returned⟩
    cases invoked
    all_goals first
      | exact CallRel.equation _ _ _ _ _ _ _ _ nonerror nonGrounded
          (by assumption) (by assumption) (by assumption) (by assumption) returned
      | obtain rfl := call_return_not_reducible_exact.mp returned
        exact CallRel.noEquation _ _ _ nonerror nonGrounded (by assumption)
      | obtain rfl := call_return_not_reducible_exact.mp returned
        exact CallRel.allEquationsFiltered _ _ _ nonerror nonGrounded (by assumption)
      | simp_all [NonGroundedCallRel, HostCall]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.EquationFallbackControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Minimal Spec.Eval.Steps Spec.Match.Merge
open Spec.Type
open LeaTTaBridge

def dispatch : Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

def query : Atom := .expression [.symbol "f", .var "x"]
def pattern : Atom := .expression [.symbol "f", .symbol "A"]
def context : Space := ⟨[.expression [.symbol "=", pattern, .symbol "Hit"]]⟩
def caller : Bindings := Bindings.empty.assign "x" (.symbol "B")
def matched : Bindings := Bindings.empty.assign "x" (.symbol "A")

theorem singleton_loop_free (name symbol : String) :
    SemanticLoopFree (Bindings.empty.assign name (.symbol symbol)) :=
  semanticLoopFree_single_assignment (by intro occurs; cases occurs)

theorem singleton_satisfied (symbol : String) :
    HEBindingSatisfied (fun _ => .sym symbol)
      (Bindings.empty.assign "x" (.symbol symbol)) := by
  simp [HEBindingSatisfied, Bindings.assign, Bindings.empty,
    Bindings.isBound, Bindings.lookup, toLeaTTaAtom, applyClassSolution]

private theorem merge_empty (bindings : Bindings) :
    MergeRel equalityGroundedSemantic bindings Bindings.empty bindings :=
  .mk (by simp [constraints, Bindings.empty]) .nil

private theorem merge_singleton (symbol : String) :
    MergeRel equalityGroundedSemantic Bindings.empty
      (Bindings.empty.assign "x" (.symbol symbol))
      (Bindings.empty.assign "x" (.symbol symbol)) := by
  apply MergeRel.mk (order := [.value "x" (.symbol symbol)])
  · simp [constraints, Bindings.assign, Bindings.empty,
      Bindings.isBound, Bindings.lookup]
    rfl
  · exact .value (.fresh (by rfl)) .nil

theorem query_matches : MatchRel equalityGroundedSemantic query pattern matched := by
  apply MatchRel.expression _ (singleton_loop_free "x" "A")
  exact .cons (.symSym "f" semanticLoopFree_empty) (merge_empty _)
    (.cons (.varNonVar rfl (singleton_loop_free "x" "A")) (merge_singleton "A") .nil)

private theorem pattern_is_closed_renaming {rename : String → String} {fresh : Atom}
    (renamed : AlphaRenameAtomRel rename pattern fresh) : fresh = pattern := by
  cases renamed with
  | expression children =>
    cases children with
    | cons head tail =>
      cases head
      cases tail with
      | cons head tail => cases head; cases tail; rfl

theorem selected_rule (live : List Atom) :
    EquationRuleMatchRel context live query caller pattern (.symbol "Hit") matched := by
  refine ⟨pattern, .symbol "Hit", by simp [context], ?_, query_matches⟩
  refine ⟨id, Function.injective_id,
    .expression (.cons (.symbol "f") (.cons (.symbol "A") .nil)), .symbol "Hit", ?_⟩
  intro name occurs
  rcases occurs with occurs | occurs
  · cases occurs with
    | expression member child =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> cases child
  · cases occurs

theorem all_filtered (live : List Atom) :
    EquationQueryAllFilteredRel context live query caller := by
  refine ⟨⟨pattern, .symbol "Hit", matched, selected_rule live⟩, ?_⟩
  rintro emitted output ⟨freshLhs, freshRhs, candidate,
    ⟨rawLhs, rawRhs, stored, alpha, matched⟩,
    merged, _⟩
  obtain ⟨valuation, satisfies⟩ := merged.he_model
  have raw : rawLhs = pattern ∧ rawRhs = .symbol "Hit" := by
    simpa [context] using stored
  rcases raw with ⟨rfl, rfl⟩
  obtain ⟨rename, _, lhs, _, _⟩ := alpha
  have same : freshLhs = pattern := pattern_is_closed_renaming lhs
  subst freshLhs
  have both := (merged.he_solutions valuation).mp satisfies
  have equates := (Spec.Match.SolutionTheory.matchRel_solution_iff matched valuation).mp both.1
  have bound := both.2.1 "x" (.symbol "B") (by
    simp [caller, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup])
  simp only [query, pattern, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution,
    List.map_cons, List.map_nil, Metta.Atom.expr.injEq, List.cons.injEq,
    true_and, and_true] at equates
  simp only [toLeaTTaAtom, applyClassSolution] at bound
  rw [bound] at equates
  simp at equates

/-- Even the nonempty initial match set cannot turn total filtering into
an empty ordinary answer. The complete invocation and selected frame remain. -/
theorem all_filtered_ordinary_returns_invocation (live : List Atom) (expected : Atom) :
    CallRel context dispatch live query expected caller (query, caller) := by
  apply (ordinary_all_filtered_exact (by simp [query, IsErrorRel])
    (by simp [NonGroundedCallRel, HostCall, dispatch, query, embeddedInstruction])
    (all_filtered (expected :: live))).mpr
  rfl

/-- Negative control: the old Empty conclusion is excluded for this
inhabited, satisfiable conflicting-caller example. -/
theorem all_filtered_never_returns_empty (live : List Atom) (expected : Atom) :
    ¬CallRel context dispatch live query expected caller (Atom.empty, caller) := by
  intro returned
  have same := (ordinary_all_filtered_exact (by simp [query, IsErrorRel])
    (by simp [NonGroundedCallRel, HostCall, dispatch, query, embeddedInstruction])
    (all_filtered (expected :: live))).mp returned
  simp [query, Atom.empty] at same

/-- Primitive success reads the template through the actual newly selected
bindings before publishing it to its caller. -/
theorem unify_materializes_selected_bindings (live : List Atom) (origin : Option Atom) :
    CoreStepRel context dispatch live
      (.expression [.symbol "unify", .var "x", .symbol "B", query, .symbol "Fail"])
      Bindings.empty (.expression [.symbol "f", .symbol "B"], caller)
        (caller := origin) := by
  apply CoreStepRel.unifySuccess
  · refine ⟨caller, .varNonVar rfl (singleton_loop_free "x" "B"),
      (merge_empty caller).logicalMerge ?_⟩
    exact ⟨fun _ => .symbol "B", by
      simp [caller, Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
        Spec.Type.RuntimeRefinement.applyTypeValuation, Bindings.assign,
        Bindings.empty, Bindings.isBound, Bindings.lookup]⟩
  · exact .historical _ _
  · simpa [BindingFrame.materialization_historical, caller, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup, query,
      Spec.Type.Presentation.TypeSubst.apply,
      Spec.Type.Presentation.TypeSubst.lookup] using
      (Spec.Type.Presentation.BindingTheory.BindingMaterializationRel.single_assignment
        "x" (.symbol "B") query (by simp [Spec.Type.Presentation.TypeSubst.typeVars]))

def materializedQuery : Atom := .expression [.symbol "f", .symbol "B"]

private theorem materialized_query_has_no_match (live : List Atom) :
    EquationQueryNoMatchRel context live materializedQuery caller := by
  rintro freshPattern freshRhs candidate
    ⟨rawLhs, rawRhs, stored, alpha, matching⟩
  have raw : rawLhs = pattern ∧ rawRhs = .symbol "Hit" := by
    simpa [context] using stored
  rcases raw with ⟨rfl, rfl⟩
  obtain ⟨rename, _, lhs, _, _⟩ := alpha
  have same := pattern_is_closed_renaming lhs
  subst freshPattern
  cases matching with
  | expression children _ =>
    cases children with
    | cons head merge tail =>
      cases tail with
      | cons compared merge tail =>
        exact symbol_mismatch_not_match (by decide : "B" ≠ "A") _ compared

private theorem symbol_types (name : String) :
    TypesOfRel context (.symbol name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (by intro type; simp) .nil)

private theorem symbol_evaluates (live : List Atom) (name : String) :
    EvalAtomRawRel context dispatch live (.symbol name) Atom.undefinedType caller
      (.symbol name, caller) := by
  by_cases empty : name = "Empty"
  · subst name
    exact .emptyOrError _ _ _ (Or.inl rfl)
  apply EvalAtomRawRel.cast (.symbol name) Atom.undefinedType Atom.symbolType
    caller (.symbol name, caller)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, empty]
  · exact .symbol name
  · simp [Atom.undefinedType, Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨name, rfl⟩
  · apply Spec.Type.TypeCastRel.success (earlierTypes := []) (laterTypes := [])
      (actualType := Atom.undefinedType) (symbol_types name) rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .historical _ _

/-- The ordinary continuation evaluates the materialized template. With only
the incompatible `(f A)` rule, the reached `(f B)` remains the answer. -/
theorem materialized_query_evaluates (live : List Atom) :
    EvalAtomRawRel context dispatch live materializedQuery Atom.undefinedType caller
      (materializedQuery, caller) := by
  apply EvalAtomRawRel.interpretSuccess materializedQuery Atom.undefinedType Atom.expressionType
    caller (materializedQuery, caller)
  · simp [materializedQuery, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .expression [.symbol "f", .symbol "B"]
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "f", [.symbol "B"], rfl⟩
  · apply InterpretExpressionRel.tuplePath materializedQuery Atom.undefinedType
      (.symbol "f") [.symbol "B"] [Atom.undefinedType] [Atom.undefinedType] [] caller
      (materializedQuery, caller) (materializedQuery, caller) rfl (symbol_types "f") rfl
    · apply FunctionCandidateScanRel.nonFunctionExhausted
      · rintro ⟨argumentTypes, returnType, equation⟩
        simp [FunctionTypeRel, Atom.undefinedType] at equation
      · exact .nil
    · apply InterpretTupleRel.success (.symbol "f") [.symbol "B"] caller
        (.symbol "f", caller) (.expression [.symbol "B"], caller)
      · simp
      · exact symbol_evaluates _ "f"
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · exact .singleton (.symbol "B") caller (.symbol "B", caller)
          (symbol_evaluates _ "B") (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · apply CallRel.noEquation
      · simp [materializedQuery, IsErrorRel]
      · simp [materializedQuery, NonGroundedCallRel, HostCall, embeddedInstruction, dispatch]
      · exact materialized_query_has_no_match _
  · simp [materializedQuery, IsErrorRel]

/-- From empty bindings, successful unify publishes its readout and the full
ordinary continuation preserves that value under the reached caller record. -/
theorem ordinary_unify_from_empty_materializes_before_call (live : List Atom) :
    CallRel context dispatch live
      (.expression [.symbol "unify", .var "x", .symbol "B", query, .symbol "Fail"])
      Atom.undefinedType Bindings.empty (materializedQuery, caller) := by
  apply CallRel.embedded (raw := (materializedQuery, caller))
  · simp [IsErrorRel]
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · apply CoreInvocationRel.embedded
    · rintro ⟨_, _, _, executable⟩
      exact executable
    · rfl
    · exact .instruction _ _ _ _ rfl (by simp [Minimal.IsChain])
        (unify_materializes_selected_bindings _ none)
  · apply CallReturnRel.evaluate
    · simp [materializedQuery, Atom.notReducible]
    · simp [materializedQuery, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact materialized_query_evaluates _

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.EquationFallbackControls

end
