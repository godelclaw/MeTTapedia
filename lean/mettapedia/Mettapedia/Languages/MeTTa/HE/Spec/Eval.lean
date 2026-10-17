import Mettapedia.Languages.MeTTa.HE.ArgumentResult
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

/-!
# Executable-independent spec evaluator specification

The single mutually recursive, fuel-free rule block carries a complete binding
frame: raw constraints plus either the historical materializer or a certified
finite table shared by every operand in that retained activation. Raw public
calls explicitly inject the historical instance. The judgments share the full typed result
continuation with raw/minimal invocation and function completion. The embedded
`metta` fragment includes Atom demand, syntactic errors, and non-error full
results. General embedded-metta failure-priority completeness is not asserted:
its negative all-alternatives test cannot be placed inside an inductive family.
The type, unify, switch, matcher, merger, alpha-renaming, and
equation-query premises are the independent relations from the preceding
modules.  Grounded operations remain an explicitly parameterized host
relation.

The mutual block presents individual raw results.  `EvalRel` below adds the
published top-level success-priority rule: an error is observable only when no
non-error raw result exists for the same configuration.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.BindingTheory
open Spec.Eval.Steps

/-! ## Retained binding readout -/

/-- Historical materialization remains a distinct exact instance. A selected
readout carries executable finite data and its independent certificate. -/
inductive BindingReadout (bindings : Bindings) : Type where
  | historical
  | selected (table : TypeSubst) (certified : ReadoutCertificate bindings table)

structure BindingFrame where
  bindings : Bindings
  readout : BindingReadout bindings

abbrev FrameResult := Atom × BindingFrame

namespace BindingFrame

open Spec.Type.RuntimeRefinement

def historical (bindings : Bindings) : BindingFrame := ⟨bindings, .historical⟩
def selected (bindings : Bindings) (table : TypeSubst)
    (certified : ReadoutCertificate bindings table) : BindingFrame :=
  ⟨bindings, .selected table certified⟩

theorem selected_congr {left right : Bindings} {first second : TypeSubst}
    {leftCertificate : ReadoutCertificate left first}
    {rightCertificate : ReadoutCertificate right second}
    (rows : left = right) (tables : first = second) :
    selected left first leftCertificate = selected right second rightCertificate := by
  cases rows
  cases tables
  rfl

def rawResult (result : FrameResult) : ResultPair := (result.1, result.2.bindings)
def historicalResult (result : ResultPair) : FrameResult :=
  (result.1, historical result.2)

instance : Coe BindingFrame Bindings := ⟨BindingFrame.bindings⟩
instance : Coe FrameResult ResultPair := ⟨rawResult⟩

/-- Raw public calls retain the historical readout explicitly. A selected
representation is admitted only by supplying its table and certificate. -/
instance : Coe Bindings BindingFrame := ⟨historical⟩
instance : Coe ResultPair FrameResult := ⟨historicalResult⟩

@[simp] theorem historical_bindings (bindings : Bindings) :
    (historical bindings).bindings = bindings := rfl
@[simp] theorem raw_historicalResult (result : ResultPair) :
    rawResult (historicalResult result) = result := by cases result; rfl


theorem historicalResult_injective : Function.Injective historicalResult := by
  intro left right same
  simpa only [raw_historicalResult] using congrArg rawResult same

@[simp] theorem historicalResult_inj {left right : ResultPair} :
    historicalResult left = historicalResult right ↔ left = right :=
  historicalResult_injective.eq_iff

@[simp] theorem historicalResult_pair (value : Atom) (bindings : Bindings) :
    historicalResult (value, bindings) = (value, historical bindings) := rfl

/-- Persistence and real operation re-entry are distinct. A new activation
may reselect its representation even when its raw constraints happen to agree. -/
inductive TransitionKind where
  | retain
  | renew

/-- Renewal evidence is consumed only alongside the actual cast, query or merge
premise in the evaluator. Pure rules retain the whole input frame directly. -/
inductive Update : TransitionKind → BindingFrame → BindingFrame → Prop where
  | same (kind : TransitionKind) (frame : BindingFrame) : Update kind frame frame
  | historical (before after : Bindings) :
      Update .renew (historical before) (historical after)
  | selected {before after : Bindings} {earlier later : TypeSubst}
      (old : ReadoutCertificate before earlier) (next : ReadoutCertificate after later) :
      Update .renew (BindingFrame.selected before earlier old)
        (BindingFrame.selected after later next)

theorem Update.retained_eq {before after : BindingFrame}
    (updated : Update .retain before after) : before = after := by
  cases updated
  rfl

theorem Update.historical_output {before : Bindings} {after : BindingFrame}
    {kind : TransitionKind}
    (updated : Update kind (BindingFrame.historical before) after) :
    after = BindingFrame.historical after.bindings := by
  cases updated <;> rfl

/-- Historical frames cannot acquire a selected representation silently. -/
theorem Update.preserves_historical {before after : BindingFrame} {kind : TransitionKind}
    (updated : Update kind before after)
    (historicalBefore : before = BindingFrame.historical before.bindings) :
    after = BindingFrame.historical after.bindings := by
  rw [historicalBefore] at updated
  exact updated.historical_output

/-- The selected table is shared by all operand reads in this frame. -/
def Materialization (frame : BindingFrame) (raw normalized : Atom) : Prop :=
  match frame.readout with
  | .historical => BindingMaterializationRel frame.bindings raw normalized
  | .selected table _ => normalized = table.apply raw

@[simp] theorem materialization_historical (bindings : Bindings) (raw value : Atom) :
    Materialization (historical bindings) raw value ↔
      BindingMaterializationRel bindings raw value := Iff.rfl

@[simp] theorem materialization_selected (bindings : Bindings) (table : TypeSubst)
    (certified : ReadoutCertificate bindings table) (raw value : Atom) :
    Materialization (selected bindings table certified) raw value ↔
      value = table.apply raw := Iff.rfl

theorem Materialization.output_eq {frame : BindingFrame} {raw left right : Atom}
    (first : Materialization frame raw left) (second : Materialization frame raw right) :
    left = right := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.output_eq first second
  | selected table certified => exact first.trans second.symm

/-- Closed syntax is unchanged by either retained readout profile. -/
theorem Materialization.closed_result {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized)
    (closed : TypeSubst.typeVars raw = []) : normalized = raw := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.closed_result materialized closed
  | selected table certified =>
      change normalized = table.apply raw at materialized
      rw [materialized]
      apply TypeSubst.apply_eq_self_of_variables_not_keys
      intro name member
      simp [closed] at member

/-- Both readout profiles preserve every model of the complete raw record. -/
theorem Materialization.preserves_model {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized) (valuation : String → Atom)
    (satisfied : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation frame.bindings) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation normalized =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation raw := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.preserves_model materialized valuation satisfied
  | selected table certified =>
    change normalized = table.apply raw at materialized
    rw [materialized]
    exact certified.preserves_model valuation satisfied raw

theorem Materialization.of_historical {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized)
    (historicalFrame : frame = historical frame.bindings) :
    BindingMaterializationRel frame.bindings raw normalized := by
  rw [historicalFrame] at materialized
  exact materialized

theorem Update.no_reselect {bindings : Bindings} {old next : TypeSubst}
    (oldCertificate : ReadoutCertificate bindings old)
    (nextCertificate : ReadoutCertificate bindings next) (different : old ≠ next) :
    ¬Update .retain (BindingFrame.selected bindings old oldCertificate)
      (BindingFrame.selected bindings next nextCertificate) := by
  intro updated
  have equal := updated.retained_eq
  cases equal
  exact different rfl

/-- Raw serialization is admitted only for the historical instance until the
host carries the selected representation as part of its saved payload. -/
def Historical (frame : BindingFrame) : Prop := frame = historical frame.bindings


theorem Historical.result {result : FrameResult} (historicalFrame : result.2.Historical) :
    historicalResult (rawResult result) = result := by
  rcases result with ⟨value, frame⟩
  change (value, historical frame.bindings) = (value, frame)
  rw [← historicalFrame]

/-- The same selected readout is reused when a continuation observes its
already materialized operand. -/
theorem Materialization.reapply {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized) :
    frame.Materialization normalized normalized := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    obtain ⟨table, folded, rfl⟩ := materialized
    exact BindingMaterializationRel.reapply_same_presentation folded raw
  | selected table certified =>
    change normalized = table.apply raw at materialized
    change normalized = table.apply normalized
    rw [materialized, certified.absorbs certified (fun _ model => model)]

theorem Materialization.satisfiable {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized) :
    ∃ valuation, TypeBindingSatisfied valuation frame.bindings := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.satisfiable materialized
  | selected table certified => exact certified.satisfiable

/-- Literal instruction heads survive both admitted readout profiles. -/
theorem Materialization.symbol_head_iff (frame : BindingFrame) (head : String)
    (raw normalized : Atom) :
    frame.Materialization (.expression [.symbol head, raw]) normalized ↔
      ∃ value, frame.Materialization raw value ∧
        normalized = .expression [.symbol head, value] := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    constructor
    · rintro ⟨table, folded, same⟩
      exact ⟨table.apply raw, ⟨table, folded, rfl⟩,
        by simpa only [TypeSubst.apply, List.map_cons, List.map_nil] using same⟩
    · rintro ⟨value, ⟨table, folded, rfl⟩, rfl⟩
      exact ⟨table, folded, by simp only [TypeSubst.apply, List.map_cons, List.map_nil]⟩
  | selected table certified =>
    change normalized = table.apply (.expression [.symbol head, raw]) ↔
      ∃ value, value = table.apply raw ∧ normalized = .expression [.symbol head, value]
    simp only [TypeSubst.apply, List.map_cons, List.map_nil, exists_eq_left]

/-- One action renames the entire retained record and finite table together. -/
def rename (permutation : Equiv.Perm String) (frame : BindingFrame) : BindingFrame where
  bindings := Spec.Bindings.ScopeObservation.renameBindings permutation frame.bindings
  readout := match frame.readout with
    | .historical => .historical
    | .selected table certified =>
        .selected (table.renameVars permutation) (certified.rename permutation)

@[simp] theorem rename_bindings (permutation : Equiv.Perm String) (frame : BindingFrame) :
    (rename permutation frame).bindings =
      Spec.Bindings.ScopeObservation.renameBindings permutation frame.bindings := rfl

@[simp] theorem rename_historical (permutation : Equiv.Perm String) (bindings : Bindings) :
    rename permutation (historical bindings) =
      historical (Spec.Bindings.ScopeObservation.renameBindings permutation bindings) := rfl

@[simp] theorem rename_inverse (permutation : Equiv.Perm String) (frame : BindingFrame) :
    rename permutation.symm (rename permutation frame) = frame := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    change historical _ = historical bindings
    apply congrArg historical
    simp
  | selected table certified =>
    apply selected_congr
    · simp
    · simp

@[simp] theorem rename_inverse_reverse (permutation : Equiv.Perm String) (frame : BindingFrame) :
    rename permutation (rename permutation.symm frame) = frame := rename_inverse permutation.symm frame

theorem Historical.rename {frame : BindingFrame} (historicalFrame : frame.Historical)
    (permutation : Equiv.Perm String) : (rename permutation frame).Historical := by
  rw [historicalFrame]
  rfl

theorem Update.rename {kind : TransitionKind} {before after : BindingFrame}
    (updated : Update kind before after) (permutation : Equiv.Perm String) :
    Update kind (rename permutation before) (rename permutation after) := by
  cases updated with
  | same => exact .same _ _
  | historical => exact .historical _ _
  | selected old next => exact .selected (old.rename permutation) (next.rename permutation)

theorem Materialization.rename {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized) (permutation : Equiv.Perm String) :
    (rename permutation frame).Materialization (renameTypeVars permutation raw)
      (renameTypeVars permutation normalized) := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.rename permutation materialized
  | selected table certified =>
    change normalized = table.apply raw at materialized
    change renameTypeVars permutation normalized =
      (table.renameVars permutation).apply (renameTypeVars permutation raw)
    rw [materialized, TypeSubst.apply_renameVars]

end BindingFrame


/-! ## Syntax and host boundaries -/

/-- Intrinsic meta-type, stated relationally. -/
inductive MetaTypeRel : Atom → Atom → Prop where
  | symbol (name : String) :
      MetaTypeRel (.symbol name) Atom.symbolType
  | variable (name : String) :
      MetaTypeRel (.var name) Atom.variableType
  | grounded (value : GroundedValue) :
      MetaTypeRel (.grounded value) Atom.groundedType
  | expression (atoms : List Atom) :
      MetaTypeRel (.expression atoms) Atom.expressionType

/-- Intrinsic meta-types are functional.  Evaluator constructor inversions
use this boundary lemma instead of repeating an atom-constructor case split. -/
theorem MetaTypeRel.eq {atom left right : Atom}
    (leftType : MetaTypeRel atom left) (rightType : MetaTypeRel atom right) :
    left = right := by
  cases leftType <;> cases rightType <;> rfl

/-- Syntactic error atom.  The published `(Error ...)` pattern recognizes
every expression headed by `Error`, independently of its tail shape. -/
def IsErrorRel (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "Error" :: tail)

/-- Empty or syntactic error atom. -/
def IsEmptyOrErrorRel (atom : Atom) : Prop :=
  atom = Atom.empty ∨ IsErrorRel atom

namespace Minimal

/-- Host representations used only by the minimal-instruction layer.  The
carrier contains data; injectivity and other properties are separate laws. -/
structure Services where
  /-- Opaque grounded representation of a complete binding set. -/
  bindingPayload : Bindings → GroundedValue
  /-- Opaque grounded handle for the current context space. -/
  contextPayload : Space → GroundedValue
  /-- Behavior of the internal `call-native` instruction. -/
  nativeCall : Atom → Atom → Atom → Bindings → ResultPair → Prop

/-- An ordered enumeration profile for the fuel-free evaluator.  `EvalRel`
describes which individual results are semantically possible; this relation
separately records the order and multiplicity exposed by `collapse-bind`.

The carrier is relational because the published semantics need not choose one
global scheduler.  A concrete operational profile may nevertheless be
functional. -/
structure Enumeration where
  results : Space → Atom → Atom → Bindings → ResultSet → Prop
  /-- Minimal execution has a different result boundary from full typed
  interpretation. Its semantic law is stated after `MinimalResultRel`. -/
  minimalResults : Space → Atom → Bindings → ResultSet → Prop

/-- Representation and ordered collection services configured at the host boundary. -/
structure HostPackage where
  services : Services
  enumeration : Enumeration

end Minimal

/-- Producer provenance distinguishes an ordinary emission from a value
whose interpretation has already completed. It is not inferred from syntax. -/
inductive NativeValueProvenance where
  | emitted
  | completed
  deriving DecidableEq, Repr

/-- A producer's binding boundary is separate from whether it has already
completed interpretation. Raw delivery retains the authored atom; materialized
delivery resolves its binding equations before dispatching the result. -/
inductive NativeBindingMode where
  | raw
  | materialized
  deriving DecidableEq, Repr

/-- Host-grounded operations are genuinely external to the MeTTa semantics.
The evaluator sees only an executable predicate and a relation of possible
host outcomes. -/
structure GroundedDispatch where
  executable : Atom → Prop
  outcome : Atom → List Atom → GroundedResult → Prop
  /-- Opaque minimal services are optional; core instructions do not require them. -/
  minimal : Option Minimal.HostPackage := none
  /-- The producer's completion boundary, shared by raw and full invocation. -/
  valueProvenance : Atom → List Atom → NativeValueProvenance := fun _ _ => .emitted
  /-- Binding resolution promised by this producer, before its result is read. -/
  bindingMode : Atom → List Atom → NativeBindingMode := fun _ _ => .raw
  /-- Presentation text for malformed primitive calls. The error subject and
  classification remain structural; a renderer may expose variable spelling. -/
  unifyBadArityMessage : Atom → String := HE.unifyBadArityMessage

/-- Native producer provenance is retained separately from materialization. -/
inductive NativeEmissionRel (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (frame : BindingFrame) (raw : Atom) : Atom → Prop where
  | raw : dispatch.bindingMode operator arguments = .raw →
      NativeEmissionRel dispatch operator arguments frame raw raw
  | materialized {value : Atom} :
      dispatch.bindingMode operator arguments = .materialized →
      frame.Materialization raw value →
      NativeEmissionRel dispatch operator arguments frame raw value

theorem NativeEmissionRel.raw_iff {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (mode : dispatch.bindingMode operator arguments = .raw) :
    NativeEmissionRel dispatch operator arguments bindings raw value ↔ value = raw := by
  constructor
  · intro emitted
    cases emitted with
    | raw => rfl
    | materialized opposite _ => simp [mode] at opposite
  · rintro rfl
    exact .raw mode

theorem NativeEmissionRel.materialized_iff {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (mode : dispatch.bindingMode operator arguments = .materialized) :
    NativeEmissionRel dispatch operator arguments bindings raw value ↔
      bindings.Materialization raw value := by
  constructor
  · intro emitted
    cases emitted with
    | raw opposite => simp [mode] at opposite
    | materialized _ resolved => exact resolved
  · exact .materialized mode

/-- The exact producer contract retains the complete binding observation
without allowing it to substitute for the operational result syntax. -/
theorem NativeEmissionRel.preserves_model {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (emitted : NativeEmissionRel dispatch operator arguments bindings raw value)
    (valuation : String → Atom)
    (satisfied : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation value =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation raw := by
  cases emitted with
  | raw => rfl
  | materialized _ resolved => exact resolved.preserves_model valuation satisfied

namespace Minimal

/-- Encode one semantic result in the exact pair shape consumed by
`superpose-bind`. -/
def encodeResult (services : Services) (result : ResultPair) : Atom :=
  .expression [result.1, .grounded (services.bindingPayload result.2)]

/-- Encode an ordered list of results without changing order or multiplicity. -/
def encodeResults (services : Services) (results : ResultSet) : Atom :=
  .expression (results.map (encodeResult services))

/-- Embedded instructions are interpreted by the minimal machine, not by
ordinary argument evaluation. `return` is a function-body delimiter rather
than an executable instruction. -/
def embeddedInstruction : Atom → Bool
  | .expression (.symbol head :: _) =>
      head ∈ ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom",
        "function", "collapse-bind", "superpose-bind", "metta",
        "context-space", "call-native"]
  | _ => false

/-- Observation of a materialized, noninstruction function-body terminal.
The nearest saved caller supplies the NoReturn subject; an outermost function
instead reports its terminal. This boundary does not execute a body or
materialize its syntax. -/
def functionTerminalResult (caller : Option Atom) (terminal : Atom) : Atom :=
  match terminal with
  | .expression [.symbol "return", value] => value
  | _ => Atom.error (caller.getD terminal) (.symbol "NoReturn")


def IsChain (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "chain" :: tail)

def IsFunction (atom : Atom) : Prop :=
  ∃ body, atom = .expression [.symbol "function", body]

def HostCall (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  ∃ operator arguments, atom = .expression (operator :: arguments) ∧
    dispatch.executable operator

/-- Structural substitution of the explicit chain binder. Other caller
variables remain in the carried binding frame. No fixed depth bound is used. -/
def substituteName (name : String) (replacement : Atom) : Atom → Atom
  | .symbol symbol => .symbol symbol
  | .grounded value => .grounded value
  | .var varName => if varName = name then replacement else .var varName
  | .expression atoms => .expression (atoms.map (substituteName name replacement))

/-- Install a concrete minimal host package without changing native dispatch. -/
def withHost (dispatch : GroundedDispatch) (services : Services)
    (enumeration : Enumeration) : GroundedDispatch :=
  { dispatch with minimal := some ⟨services, enumeration⟩ }

end Minimal

/-- The equation-query lane applies only when neither native dispatch nor
minimal instruction dispatch owns the invocation. Authored library operations
use this lane through their actual stored equations. -/
def NonGroundedCallRel (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  ¬Minimal.HostCall dispatch atom ∧ Minimal.embeddedInstruction atom = false

/-! ## Type-service boundary and ordered candidate selection -/

/-- One selected function-type policy.  The proof field keeps the argument
and return projections tied to the same arrow presentation; downstream
consumers never reconstruct them independently. -/
structure SelectedTypePolicy where
  functionType : Atom
  argumentTypes : List Atom
  returnType : Atom
  isFunction : FunctionTypeRel functionType argumentTypes returnType

/-- One candidate's applicability result.  A successful candidate supplies
the exact policy that later evaluation consumes as well as the bindings
produced by the applicability check. -/
inductive SelectedTypeApplicabilityOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | error (errors : List Atom)

/-- Result of the published left-to-right function-candidate scan.  Success
stops the scan immediately and carries one coherent selected policy plus the
bindings produced by applicability.  Exhaustion retains every ordered error
block from every failed function candidate and records whether a non-function
candidate made tuple fallback eligible. -/
inductive FunctionCandidateScanOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

/-- Literal transcription of the candidate loop in `interpret_expression`
(`Specs/he_metta_official_specs.md:172-210`): non-functions enable tuple
fallback, failed functions accumulate errors, and the first applicable
function stops the scan. -/
inductive FunctionCandidateScanRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space)
    (expression expectedType : Atom) (bindings : Bindings) :
    List Atom → FunctionCandidateScanOutcome → Prop where
  | nil :
      FunctionCandidateScanRel applicability space expression expectedType bindings
        [] (.exhausted [] false)
  | nonFunctionSuccess {candidate : Atom} {candidates : List Atom}
      {policy : SelectedTypePolicy} {output : Bindings} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | nonFunctionExhausted {candidate : Atom} {candidates errors : List Atom}
      {tupleEligible : Bool} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.exhausted errors true)
  | functionSuccess {candidate : Atom} {candidates argumentTypes : List Atom}
      {returnType : Atom} {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes returnType →
      applicability space expression candidate expectedType bindings
        (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureThenSuccess
      {candidate : Atom} {candidates argumentTypes : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureExhausted
      {candidate : Atom} {candidates argumentTypes errors : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {tupleEligible : Bool} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates)
        (.exhausted (candidateErrors ++ errors) tupleEligible)

/-! ### Scan boundary algebra -/

/-- Every successful ordered scan is justified by one candidate in the
original list.  Downstream conformance proofs consume this theorem instead of
unfolding the scan recursion. -/
theorem FunctionCandidateScanRel.success_candidate
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.success policy output)) :
    ∃ candidate ∈ candidates,
      applicability space expression candidate expectedType bindings
        (.success policy output) := by
  generalize outcomeEq :
      (.success policy output : FunctionCandidateScanOutcome) = outcome at scan
  revert policy output
  induction scan with
  | nil =>
      intro policy output outcomeEq
      cases outcomeEq
  | nonFunctionSuccess _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | nonFunctionExhausted =>
      intro policy output outcomeEq
      cases outcomeEq
  | functionSuccess _ applicable =>
      intro policy output outcomeEq
      cases outcomeEq
      exact ⟨_, by simp, applicable⟩
  | functionFailureThenSuccess _ _ _ _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | functionFailureExhausted =>
      intro policy output outcomeEq
      cases outcomeEq

/-- An exhausted scan has no successful applicability derivation for any
function candidate in the scanned list.  This is the exact negative boundary
used by tuple fallback and error rules. -/
theorem FunctionCandidateScanRel.exhausted_no_function_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates errors : List Atom} {tupleEligible : Bool}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.exhausted errors tupleEligible)) :
    ∀ candidate ∈ candidates,
      (∃ argumentTypes returnType,
        FunctionTypeRel candidate argumentTypes returnType) →
      ∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output) := by
  generalize outcomeEq :
      (.exhausted errors tupleEligible : FunctionCandidateScanOutcome) =
        outcome at scan
  revert errors tupleEligible
  induction scan with
  | nil =>
      intro errors tupleEligible outcomeEq candidate member
      simp at member
  | nonFunctionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | nonFunctionExhausted notFunction _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact notFunction isFunction
      · exact ih rfl candidate member isFunction policy output applicable

  | functionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureThenSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureExhausted _ noSuccess _ _ _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact noSuccess policy output applicable
      · exact ih rfl candidate member isFunction policy output applicable

/-! ### Generic exact-scan assembly

The concrete runtime bridge supplies one exact classification per candidate.
The two lemmas below are the only place that classification is threaded into
the published left-to-right scan.  Runtime-specific conformance modules never
reimplement the scan induction. -/

/-- Exact evidence for one candidate that did not stop the scan.  A
non-function enables tuple fallback without contributing an error; a failed
function contributes one nonempty ordered error block and includes the
negative success fact required by `FunctionCandidateScanRel`. -/
inductive FunctionCandidateFailureRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) : Atom → (List Atom × Bool) → Prop where
  | nonFunction {candidate : Atom} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate ([], true)
  | functionFailure {candidate : Atom} {argumentTypes : List Atom}
      {candidateReturn : Atom} {errors : List Atom} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output)) →
      applicability space expression candidate expectedType bindings
        (.error errors) →
      errors ≠ [] →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate (errors, false)

/-- Errors contributed by a list of exact failed-candidate summaries, in
source order. -/
def functionCandidateFailureErrors :
    List (List Atom × Bool) → List Atom
  | [] => []
  | (errors, _) :: summaries =>
      errors ++ functionCandidateFailureErrors summaries

/-- The recursive failure readout is exactly row-major flattening of the
per-candidate error blocks. -/
theorem functionCandidateFailureErrors_eq_flatten_map_fst
    (summaries : List (List Atom × Bool)) :
    functionCandidateFailureErrors summaries =
      (summaries.map Prod.fst).flatten := by
  induction summaries with
  | nil => rfl
  | cons summary summaries inductionHypothesis =>
      rcases summary with ⟨errors, eligible⟩
      simp [functionCandidateFailureErrors, inductionHypothesis]

/-- Whether any exact failed-candidate summary enables tuple fallback. -/
def functionCandidateFailureTupleEligible :
    List (List Atom × Bool) → Bool
  | [] => false
  | (_, eligible) :: summaries =>
      eligible || functionCandidateFailureTupleEligible summaries

/-- A pointwise exact failure classification reconstructs the complete
exhausted scan, including error order and tuple eligibility. -/
theorem FunctionCandidateScanRel.of_all_failures
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {summaries : List (List Atom × Bool)}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) candidates summaries) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings candidates
      (.exhausted (functionCandidateFailureErrors summaries)
        (functionCandidateFailureTupleEligible summaries)) := by
  induction failures with
  | nil => exact .nil
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.nonFunctionExhausted
              notFunction ih)
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.functionFailureExhausted
              isFunction noSuccess errors nonempty ih)

/-- Exact failures preceding an already-derived success may be prepended
without reopening the scan proof. -/
theorem FunctionCandidateScanRel.prepend_failures_to_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates tail : List Atom}
    {summaries : List (List Atom × Bool)}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (tailSuccess : FunctionCandidateScanRel applicability space expression
      expectedType bindings tail (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ tail) (.success policy output) := by
  induction failures with
  | nil => simpa using tailSuccess
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa using FunctionCandidateScanRel.nonFunctionSuccess
            notFunction ih
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa using FunctionCandidateScanRel.functionFailureThenSuccess
            isFunction noSuccess errors nonempty ih

/-- Generic first-success assembly: a list of exact failures followed by one
exact successful candidate yields the published ordered-scan result; the
uninspected suffix is intentionally irrelevant. -/
theorem FunctionCandidateScanRel.of_first_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates suffix : List Atom}
    {summaries : List (List Atom × Bool)}
    {candidate : Atom} {argumentTypes : List Atom} {returnType : Atom}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (isFunction : FunctionTypeRel candidate argumentTypes returnType)
    (success : applicability space expression candidate expectedType bindings
      (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ candidate :: suffix)
        (.success policy output) := by
  apply FunctionCandidateScanRel.prepend_failures_to_success failures
  exact FunctionCandidateScanRel.functionSuccess isFunction success

/-- The exact type interface consumed by the six evaluator judgments.  One
service supplies both positive and negative premises; mixing a permissive
positive layer with a different negative candidate set is unrepresentable.

`candidateScan` is deliberately a single ordered relation rather than a bare
applicability predicate: first-success and all-failed outcomes must quantify
over the same exact candidate sequence.

The published instance below is the specification-textual core.  The repaired
runtime instance is defined in the conformance layer from the exact ordered
package relation. -/
structure EvalTypeService where
  typesOf : Space → Atom → List Atom → Prop
  typeCast : List String → Space → Atom → Atom → Bindings → ResultPair → Prop
  instantiateTypes : List String → List Atom → List Atom → Prop :=
    fun _ raw selected => selected = raw
  candidateScan :
    List String → Space → Atom → Atom → Bindings →
      List Atom → FunctionCandidateScanOutcome → Prop

/-- Lift one singular published applicability fact into the block-valued
policy-carrying scan interface.  Error blocks assembled from the complete
published argument/return traversal are supplied by the exact service
instance; this constructor remains the reusable singleton brick. -/
inductive PublishedCandidateApplicabilityRel
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) : SelectedTypeApplicabilityOutcome →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | success {argumentTypes : List Atom} {returnType : Atom}
      {output : Bindings}
      (isFunction : FunctionTypeRel candidate argumentTypes returnType)
      (applicable : ApplicabilityRel space (lookup := lookup) expression candidate expectedType
        bindings (.success output)) :
      PublishedCandidateApplicabilityRel space (lookup := lookup) expression candidate
        expectedType bindings
        (.success ⟨candidate, argumentTypes, returnType, isFunction⟩ output)
  | error {errorAtom : Atom}
      (applicable : ApplicabilityRel space (lookup := lookup) expression candidate expectedType
        bindings (.error errorAtom)) :
      PublishedCandidateApplicabilityRel space (lookup := lookup) expression candidate
        expectedType bindings (.error [errorAtom])

/-- Published-scan success exposes the exact selected arrow and the
spec-threaded applicability bindings.  In particular, the policy witness and
the binding output cannot originate from different candidates. -/
theorem published_scan_success_selected
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      space expression expectedType bindings candidates
        (.success policy output)) :
    policy.functionType ∈ candidates ∧
      ApplicabilityRel space expression policy.functionType expectedType
        bindings (.success output) := by
  obtain ⟨candidate, member, applicable⟩ := scan.success_candidate
  cases applicable with
  | success _ applicability => exact ⟨member, applicability⟩

/-- The published spec type layer, definitionally, as one coherent evaluator
service. -/
def publishedTypeService : EvalTypeService where
  typesOf := TypesOfRel
  typeCast := fun _ => TypeCastRel
  candidateScan := fun _ => FunctionCandidateScanRel PublishedCandidateApplicabilityRel

private def scanFailureType : Atom :=
  .expression [.symbol "->", .symbol "A"]

private def scanSuccessType : Atom :=
  .expression [.symbol "->", .symbol "B"]

private def scanSuccessPolicy : SelectedTypePolicy :=
  ⟨scanSuccessType, [], .symbol "B", rfl⟩

private def scanExpression : Atom :=
  .expression [.symbol "scan-target"]

private def scanFailure : Atom :=
  mkError scanExpression (.badType Atom.undefinedType (.symbol "A"))

private def orderedScanCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
  (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧ outcome = .error [scanFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .success scanSuccessPolicy Bindings.empty)

/-- Positive order canary: a failed first function candidate is recorded and
the second successful candidate is selected. -/
theorem ordered_scan_skips_failed_candidate :
    FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.success scanSuccessPolicy Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanFailure])
  · rfl
  · intro candidatePolicy candidateBindings hsuccess
    simp [orderedScanCanaryApplicability, scanFailureType, scanSuccessType,
      scanSuccessPolicy]
      at hsuccess
  · simp [orderedScanCanaryApplicability]
  · simp
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := []) (returnType := .symbol "B")
        (policy := scanSuccessPolicy) (output := Bindings.empty)
    · rfl
    · exact Or.inr ⟨rfl, rfl⟩

/-- Negative order canary: once the head function candidate succeeds, the
same candidate list cannot be presented as exhausted, so tuple fallback and
all-failed errors are unavailable. -/
theorem ordered_scan_first_success_excludes_exhaustion
    (candidates errors : List Atom) (tupleEligible : Bool) :
    ¬FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      (scanSuccessType :: candidates) (.exhausted errors tupleEligible) := by
  intro hscan
  cases hscan with
  | nonFunctionExhausted hnot _ =>
      exact hnot ⟨[], .symbol "B", rfl⟩
  | functionFailureExhausted _ hnoSuccess _ _ _ =>
      exact hnoSuccess scanSuccessPolicy Bindings.empty (by
        simp [orderedScanCanaryApplicability, scanSuccessPolicy])

private def scanArityFailure : Atom :=
  mkError scanExpression .incorrectNumberOfArguments

private def scanArgumentFailure : Atom :=
  mkError scanExpression
    (.badArgType 1 (.symbol "B") (.symbol "C"))

private def orderedBlockCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
    (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧
    outcome = .error [scanArityFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .error [scanArgumentFailure])

/-- W16 order canary: complete failed-candidate blocks are concatenated in
function-candidate scan order and remain contiguous.  This is the
cross-candidate order observed at the HE reference revision used by the
conformance suite. -/
theorem ordered_scan_concatenates_candidate_error_blocks :
    FunctionCandidateScanRel orderedBlockCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.exhausted [scanArityFailure, scanArgumentFailure] false) := by
  apply FunctionCandidateScanRel.functionFailureExhausted
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanArityFailure])
  · rfl
  · intro policy output success
    simp [orderedBlockCanaryApplicability] at success
  · exact Or.inl ⟨rfl, rfl⟩
  · simp
  · apply FunctionCandidateScanRel.functionFailureExhausted
        (argumentTypes := []) (candidateReturn := .symbol "B")
        (candidateErrors := [scanArgumentFailure])
    · rfl
    · intro policy output success
      simp [orderedBlockCanaryApplicability] at success
    · exact Or.inr ⟨rfl, rfl⟩
    · simp
    · exact .nil

/-! ## Shared full/minimal evaluator judgments -/

/-- Variables of the complete expected application that remain public while
its operator head is evaluated.  A type service may introduce fresh private
names, but none may collide with this enclosing scope. -/
def expectedApplicationScope (expression expectedType : Atom) : List String :=
  (TypeSubst.typeVars expectedType ++ TypeSubst.typeVars expression).eraseDups

/-- Names protected at a typed use: inherited saved scope, live syntax,
complete subject and demand, and every current constraint name. -/
def invocationTypeScope (protectedScope : List String) (live : List Atom)
    (subject expected : Atom) (bindings : Bindings) : List String :=
  protectedScope ++ TypeSubst.typeVarsList (live ++ [subject, expected]) ++
    Spec.Bindings.ScopeObservation.specBindingVars bindings

/-- A scoped query preserves raw lookup as a separate fact and instantiates
its whole ordered result at the actual use site. -/
def scopedTypeLookup (protectedScope : List String) (space : Space) : TypeLookupRel :=
  fun bindings subject expected candidates =>
    ∃ raw, TypesOfRel space subject raw ∧
      ArgumentAlphaVariantsRel (invocationTypeScope protectedScope [] subject expected bindings)
        raw candidates

/-- An explicit scope-aware source service. Raw declaration inspection is
unchanged; casts and applicability use independently freshened query lists.
Its alpha witnesses specify legal local instances, not native fresh-ID text. -/
def scopedTypeService : EvalTypeService where
  typesOf := TypesOfRel
  instantiateTypes := ArgumentAlphaVariantsRel
  typeCast := fun scope space subject expected bindings result =>
    TypeCastRel space subject expected bindings result (lookup := scopedTypeLookup scope space)
  candidateScan := fun scope space expression expected bindings candidates selected =>
    FunctionCandidateScanRel
      (fun context subject candidate demand incoming outcome =>
        PublishedCandidateApplicabilityRel context subject candidate demand incoming outcome
          (lookup := scopedTypeLookup scope context))
      space expression expected bindings candidates selected

/-- Completed values are held for Undefined demand as well as the ordinary
intrinsic passthrough cases. No call or function syntax is activated here. -/
def CompletedNativeKeepRel (value expectedType : Atom) : Prop :=
  IsEmptyOrErrorRel value ∨ expectedType = Atom.undefinedType ∨
    expectedType = Atom.atomType ∨
    ∃ metaType, MetaTypeRel value metaType ∧
      (expectedType = metaType ∨ metaType = Atom.variableType)

/-- The return judgment for producer-completed values. A required cast is
the existing type service, not recursive interpretation of the value. -/
inductive CompletedNativeReturnRel
    (space : Space) (typing : EvalTypeService) (value expectedType : Atom)
    (frame : BindingFrame) : FrameResult →
      (protectedScope : List String := []) → Prop where
  | keep : CompletedNativeKeepRel value expectedType →
      CompletedNativeReturnRel space typing value expectedType frame (protectedScope := protectedScope) (value, frame)
  | cast {result : FrameResult} :
      ¬CompletedNativeKeepRel value expectedType →
      typing.typeCast protectedScope space value expectedType frame.bindings (BindingFrame.rawResult result) →
      BindingFrame.Update .renew frame result.2 →
      CompletedNativeReturnRel space typing value expectedType frame (protectedScope := protectedScope) result


open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

mutual

/-- Evaluate one atom to one raw result. -/
inductive EvalAtomRawRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | emptyOrError (atom expectedType : Atom) (bindings : BindingFrame) :
      IsEmptyOrErrorRel atom →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | typePass (atom expectedType metaType : Atom) (bindings : BindingFrame) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      (expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | cast (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      ((∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) →
      typing.typeCast (invocationTypeScope protectedScope live atom expectedType bindings)
        space atom expectedType bindings result →
      BindingFrame.Update .renew bindings result.2 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result
  | interpretSuccess (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result →
      ¬IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result
  | interpretError (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result →
      IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result

/-- Interpret an expression through a function type, tuple fallback, or
operator-type error. -/
inductive InterpretExpressionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | functionPath (expression expectedType operator : Atom)
      (arguments rawTypes types : List Atom)
      (policy : SelectedTypePolicy) (callType : Atom)
      (bindings applicableBindings : BindingFrame)
      (interpreted callResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.success policy applicableBindings) →
      BindingFrame.Update .renew bindings applicableBindings →
      callType = (if policy.returnType = Atom.expressionType
        then Atom.undefinedType else policy.returnType) →
      InterpretFunctionRel space dispatch (callType :: live) (protectedScope := protectedScope) (typing := typing)
        expression policy.functionType expectedType
          applicableBindings interpreted →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        interpreted.1 callType interpreted.2 callResult →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings callResult
  | tuplePath (expression expectedType operator : Atom)
      (arguments rawTypes types errors : List Atom) (bindings : BindingFrame)
      (tupleResult callResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.exhausted errors true) →
      InterpretTupleRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        expression bindings tupleResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        tupleResult.1 expectedType tupleResult.2 callResult →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings callResult
  | functionError (expression expectedType operator errorAtom : Atom)
      (arguments rawTypes types errors : List Atom) (tupleEligible : Bool)
      (bindings : BindingFrame) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.exhausted errors tupleEligible) →
      errorAtom ∈ errors →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings (errorAtom, bindings)

/-- Evaluate a function head, then its arguments. -/
inductive InterpretFunctionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | headError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings headResult
  | tailError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      (∀ values, tailResult.1 ≠ argumentPacket values) →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings tailResult
  | success (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      (∃ values, tailResult.1 = argumentPacket values) →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings
        (.expression (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Evaluate argument lists left to right. -/
inductive InterpretArgsRel :
    Space → GroundedDispatch → List Atom →
    List Atom → List Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | nil (bindings : BindingFrame) :
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing) [] [] bindings
        (argumentPacket [], bindings)
  | headChangedError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      headResult.1 ≠ argument →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings headResult
  | tailError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult tailResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      (∀ values, tailResult.1 ≠ argumentPacket values) →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings tailResult
  | success (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult tailResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      (∃ values, tailResult.1 = argumentPacket values) →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes) bindings
        (argumentPacket (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Evaluate tuple elements left to right. -/
inductive InterpretTupleRel :
    Space → GroundedDispatch → List Atom →
    Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | nil (bindings : BindingFrame) :
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        Atom.unit bindings (Atom.unit, bindings)
  | singleton (atom : Atom) (bindings : BindingFrame) (result : FrameResult) :
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom Atom.undefinedType bindings result →
      ¬IsEmptyOrErrorRel result.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression [atom]) bindings (.expression [result.1], result.2)
  | singletonError (atom : Atom) (bindings : BindingFrame) (result : FrameResult) :
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom Atom.undefinedType bindings result →
      IsEmptyOrErrorRel result.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression [atom]) bindings result
  | headError (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings headResult
  | tailError (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings tailResult
  | success (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Ordinary call completion interprets the raw invocation protocol before
resuming typed evaluation. `original` is the invocation assembled after
argument evaluation. It is restored on `NotReducible`; stopped values retain
both their syntax and reached bindings. Explicit producer-completed values
use `CompletedNativeReturnRel` instead. -/
inductive CallReturnRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | notReducible (original expectedType : Atom) (bindings : BindingFrame) :
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType Atom.notReducible bindings (original, bindings)
  | stopped (original expectedType value : Atom) (bindings : BindingFrame) :
      IsEmptyOrErrorRel value →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType value bindings (value, bindings)
  | evaluate (original expectedType value : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      value ≠ Atom.notReducible →
      ¬IsEmptyOrErrorRel value →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        value expectedType bindings result →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType value bindings result

/-- Perform one MeTTa call step, completing raw host or equation results
through the ordinary return protocol before recursive typed evaluation.
Invocation completion saves the assembled call as the diagnostic origin. -/
inductive CallRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | errorPassthrough (atom expectedType : Atom) (bindings : BindingFrame) :
      IsErrorRel atom →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | embedded (atom expectedType : Atom) (bindings : BindingFrame)
      (raw result : FrameResult) :
      ¬IsErrorRel atom →
      ¬Minimal.HostCall dispatch atom →
      Minimal.embeddedInstruction atom = true →
      Minimal.CoreInvocationRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        atom bindings raw →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType raw.1 raw.2 result →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings result
  | groundedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame)
      (nativeResults : ResultSet) (nativeResult : ResultPair) (finalResult : FrameResult)
      (merged : BindingFrame) (emitted : Atom) (completed : FrameResult) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationResultRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some atom)
        emitted merged completed →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType completed.1 completed.2 finalResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | groundedCompletedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame)
      (nativeResults : ResultSet) (nativeResult : ResultPair) (finalResult : FrameResult)
      (merged : BindingFrame) (emitted : Atom) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      CompletedNativeReturnRel space typing emitted expectedType merged finalResult
        (protectedScope := invocationTypeScope protectedScope live atom expectedType merged) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | groundedRuntimeError (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) (message : String) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.runtimeError message) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (Atom.error atom (.symbol message), bindings)
  | groundedNoReduce (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .noReduce →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedIncorrectArgument (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .incorrectArgument →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedEmpty (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok []) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)
  | equation (atom expectedType emitted materialized : Atom) (bindings merged : BindingFrame)
      (finalResult completed : FrameResult) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryCandidateRel space (expectedType :: live) atom bindings emitted merged →
      BindingFrame.Update .renew bindings merged →
      BindingFrame.Materialization merged emitted materialized →
      Minimal.CoreInvocationResultRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some atom)
        materialized merged completed →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType completed.1 completed.2 finalResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | noEquation (atom expectedType : Atom) (bindings : BindingFrame) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryNoMatchRel space (expectedType :: live) atom bindings →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | allEquationsFiltered (atom expectedType : Atom) (bindings : BindingFrame) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryAllFilteredRel space (expectedType :: live) atom bindings →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)


/-- One state-free minimal-instruction step.  The context space is read-only;
the state-writing extension is specified separately by `StateAlgebra`.

`live` is the protected equation-query scope threaded by `EvalRel`, not
the equation table. This minimal profile retains the full syntax of entered
chain/function frames in that scope. `caller` names the nearest saved frame
for observable diagnostics; it stays raw when a terminal is materialized.
Backends with placeholder frame syntax or different scope retention need
their own representation adapter. Its `eval` operand invokes one raw
native/equation operation. Full typed interpretation is explicit in the
separate `metta` instruction. -/
inductive Minimal.CoreStepRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) →
      (caller : Option Atom := none) → Prop where
  | eval (space : Space) (atom materialized : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      BindingFrame.Materialization bindings atom materialized →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized bindings result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "eval", atom]) bindings result
  | evalc (space context : Space) (atom materialized : Atom) (bindings : BindingFrame)
      (result : FrameResult) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Materialization bindings atom materialized →
      Minimal.CoreInvocationRel context dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized bindings result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "evalc", atom,
          .grounded (services.contextPayload context)]) bindings result
  | chain (space : Space) (atom : Atom) (name : String) (template : Atom)
      (bindings : BindingFrame) (result : FrameResult) (materialized : Atom) :
      Minimal.CoreRunRel space dispatch
        (.expression [.symbol "chain", atom, .var name, template] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "chain", atom, .var name, template]))
        atom bindings result →
      BindingFrame.Materialization result.2 result.1 materialized →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "chain", atom, .var name, template]) bindings
        (substituteName name materialized template, result.2)
  | unifySuccess (space : Space) (target pattern thenBranch elseBranch result : Atom)
      (bindings output : BindingFrame) :
      UnifyCandidateRel target pattern bindings output →
      BindingFrame.Update .renew bindings output →
      BindingFrame.Materialization output thenBranch result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (result, output)
  | unifyNoMatch (space : Space) (target pattern thenBranch elseBranch : Atom)
      (bindings : BindingFrame) :
      UnifyNoMatchRel target pattern bindings →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (elseBranch, bindings)
  | unifyBadArity (space : Space) (tail : List Atom)
      (bindings : BindingFrame) :
      tail.length ≠ 4 →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (.symbol "unify" :: tail)) bindings
        (mkErrorMessage (.expression (.symbol "unify" :: tail))
          (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail))), bindings)
  | consAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : BindingFrame) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "cons-atom", head, .expression tail]) bindings
        (.expression (head :: tail), bindings)
  | deconsAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : BindingFrame) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "decons-atom", .expression (head :: tail)])
        bindings (.expression [head, .expression tail], bindings)
  | collapseBind (space : Space) (atom : Atom) (bindings : BindingFrame)
      (results : ResultSet) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Historical bindings →
      enumeration.minimalResults space atom bindings results →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "collapse-bind", atom]) bindings
        (encodeResults services results, bindings)
  | superposeBind (space : Space) (results : ResultSet)
      (stored : ResultPair) (bindings merged : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Historical bindings →
      stored ∈ results →
      MergeRel equalityGroundedSemantic stored.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "superpose-bind", encodeResults services results])
        bindings (stored.1, merged)
  | functionReturn (space : Space) (body returned : Atom)
      (bindings output : BindingFrame) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch
        (.expression [.symbol "function", body] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "function", body]))
        body bindings (.expression [.symbol "return", returned], output) →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings (returned, output)
  | functionNoReturn (space : Space) (body result : Atom)
      (bindings output : BindingFrame) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch
        (.expression [.symbol "function", body] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "function", body]))
        body bindings (result, output) →
      (∀ returned, result ≠ .expression [.symbol "return", returned]) →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings
        (functionTerminalResult caller result, output)
  | metta (space context : Space) (atom expectedType : Atom)
      (bindings : BindingFrame) (result : FrameResult)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      EvalAtomRawRel context dispatch live atom expectedType bindings result
        (protectedScope := protectedScope) (typing := typing) →
      ¬IsErrorRel result.1 →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings result
  | mettaAtom (space context : Space) (atom : Atom) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, Atom.atomType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | mettaError (space context : Space) (atom expectedType : Atom) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      IsErrorRel atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | contextSpace (space : Space) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "context-space"]) bindings
        (.grounded (services.contextPayload space), bindings)
  | callNative (space : Space) (name function arguments : Atom)
      (bindings : BindingFrame) (result : ResultPair) (merged : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      services.nativeCall name function arguments bindings result →
      MergeRel equalityGroundedSemantic result.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "call-native", name, function, arguments])
        bindings (result.1, merged)

/-- Raw native/equation invocation: bindings are merged, but the emitted
ordinary atom is not recursively interpreted. An embedded operand is executed
by the minimal machine; an emitted `function` block has its own return frame. -/
inductive Minimal.CoreInvocationRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) →
      (caller : Option Atom := none) → Prop where
  | embedded (space : Space) (atom : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = true →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | grounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : BindingFrame) (results : ResultSet)
      (nativeResult : ResultPair) (result : FrameResult) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      (∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation merged) →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression (operator :: arguments)))
        emitted merged result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings result
  | completedGrounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : BindingFrame) (results : ResultSet)
      (nativeResult : ResultPair) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      (∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation merged) →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings (emitted, merged)
  | groundedEmpty (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.ok []) →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings (Atom.empty, bindings)
  | groundedError (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) (message : String) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.runtimeError message) →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.error (.expression (operator :: arguments)) (.symbol message), bindings)
  | groundedNoReduce (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .noReduce →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | groundedIncorrectArgument (space : Space) (operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .incorrectArgument →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | equation (space : Space) (atom emitted materialized : Atom)
      (bindings merged : BindingFrame) (result : FrameResult) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryCandidateRel space live atom bindings emitted merged →
      BindingFrame.Update .renew bindings merged →
      BindingFrame.Materialization merged emitted materialized →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := some atom)
        materialized merged result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | noEquation (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryNoMatchRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (Atom.notReducible, bindings)
  | allEquationsFiltered (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryAllFilteredRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (Atom.notReducible, bindings)

/-- Completing a raw invocation interprets only an authored `function`
block. Other emitted expressions, including callable-looking data, remain
raw. The invocation rules supply their actual call as the nearest saved
caller; embedded instructions keep their surrounding continuation. This is
independent of the ordinary typed result continuation. -/
inductive Minimal.CoreInvocationResultRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) →
      (caller : Option Atom := none) → Prop where
  | raw (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬IsFunction atom →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (atom, bindings)
  | function (space : Space) (body : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings result →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings result

/-- Completed raw minimal execution. `chain` schedules the substituted
template; other instruction outputs are returned raw. The reference minimal
machine carries Empty and NotReducible through chain as ordinary sentinel
atoms; final observation, not this continuation, removes Empty. -/
inductive Minimal.CoreRunRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) →
      (caller : Option Atom := none) → Prop where
  | data (space : Space) (atom : Atom) (bindings : BindingFrame) :
      embeddedInstruction atom = false →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (atom, bindings)
  | instruction (space : Space) (atom : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      embeddedInstruction atom = true →
      ¬IsChain atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | chain (space : Space) (atom : Atom) (bindings : BindingFrame)
      (selected result : FrameResult) :
      IsChain atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings selected →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        selected.1 selected.2 result →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result

/-- A function body resumes embedded instructions until a noninstruction
terminal is reached. A terminal without `return` produces NoReturn, including
an internal Empty sentinel reached by a valid expression-shaped body. -/
inductive Minimal.CoreFunctionBodyRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) →
      (caller : Option Atom := none) → Prop where
  | terminal (space : Space) (atom : Atom) (bindings : BindingFrame)
      (raw : FrameResult) (materialized : Atom) :
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings raw →
      BindingFrame.Materialization raw.2 raw.1 materialized →
      embeddedInstruction materialized = false →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (materialized, raw.2)
  | resume (space : Space) (atom : Atom) (bindings : BindingFrame)
      (raw : FrameResult) (materialized : Atom) (result : FrameResult) :
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings raw →
      BindingFrame.Materialization raw.2 raw.1 materialized →
      embeddedInstruction materialized = true →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized raw.2 result →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result

end


/-- A raw refusal restores exactly the assembled invocation and the binding
frame reached by that invocation; the protocol atom cannot escape this gate. -/
theorem CallReturnRel.notReducible_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType : Atom}
    {bindings : BindingFrame} {result : FrameResult} :
    CallReturnRel space dispatch live original expectedType Atom.notReducible
      bindings result (protectedScope := protectedScope) (typing := typing) ↔ result = (original, bindings) := by
  constructor
  · intro returned
    cases returned <;>
      simp_all [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty]
  · rintro rfl
    exact .notReducible _ _ _

/-- Empty and error replies stop at ordinary call completion, independently
of the expected type. -/
theorem CallReturnRel.stopped_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType value : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (stopped : IsEmptyOrErrorRel value) :
    CallReturnRel space dispatch live original expectedType value bindings result
      (protectedScope := protectedScope) (typing := typing) ↔ result = (value, bindings) := by
  constructor
  · intro returned
    cases returned <;>
      simp_all [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty]
  · rintro rfl
    exact .stopped _ _ _ _ stopped

/-- Every non-protocol, non-stopped reply resumes the existing raw typed
judgment without changing its scope, demand, or reached frame. -/
theorem CallReturnRel.evaluate_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType value : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (notRefusal : value ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel value) :
    CallReturnRel space dispatch live original expectedType value bindings result
      (protectedScope := protectedScope) (typing := typing) ↔
      EvalAtomRawRel space dispatch live value expectedType bindings result
        (protectedScope := protectedScope) (typing := typing) := by
  constructor
  · intro returned
    cases returned <;> simp_all
  · exact .evaluate _ _ _ _ _ notRefusal notStopped

/-! ## Public success-priority boundary -/

/-- A published evaluator result: raw successes are admitted directly; a raw
error is admitted only if no raw non-error result exists for the same input. -/
def EvalRel
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : BindingFrame) (result : FrameResult)
    (typing : EvalTypeService := publishedTypeService)
    (protectedScope : List String := []) : Prop :=
  EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
      atom expectedType bindings result ∧
    (IsErrorRel result.1 →
      ∀ candidate,
        EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
          atom expectedType bindings candidate →
          IsErrorRel candidate.1)

/-! ## Boundary examples -/

private def noHostDispatch : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- Positive error-shape canary: the published ellipsis permits an empty
tail after the `Error` head. -/
example : IsErrorRel (.expression [.symbol "Error"]) :=
  ⟨[], rfl⟩

/-- Negative error-shape canary: the bare `Error` symbol is data, not an
error expression. -/
example : ¬IsErrorRel (.symbol "Error") := by
  rintro ⟨tail, h⟩
  cases h

/-- Positive: `Empty` passes through unchanged. -/
example : EvalRel Space.empty noHostDispatch []
    Atom.empty Atom.undefinedType Bindings.empty
    (Atom.empty, Bindings.empty) := by
  constructor
  · exact EvalAtomRawRel.emptyOrError _ _ _ (Or.inl rfl)
  · intro herror
    exact (by rcases herror with ⟨tail, h⟩; cases h)

private theorem variablePassRaw (name : String) (expectedType : Atom)
    (protectedScope : List String := []) {live : List Atom} :
    EvalAtomRawRel Space.empty noHostDispatch live
    (.var name) expectedType Bindings.empty
    (.var name, Bindings.empty) protectedScope := by
  apply EvalAtomRawRel.typePass (.var name) expectedType
      Atom.variableType Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.variable name
  · exact Or.inr (Or.inr rfl)

/-- Positive tuple recursion: a singleton tuple retains its wrapper. -/
example : InterpretTupleRel Space.empty noHostDispatch []
    (.expression [.var "x"]) Bindings.empty
    (.expression [.var "x"], Bindings.empty) := by
  apply InterpretTupleRel.singleton (.var "x") Bindings.empty
    (.var "x", Bindings.empty) (variablePassRaw "x" Atom.undefinedType)
  simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

private def unaryWantedType : Atom :=
  .expression [.symbol "->", .symbol "Wanted", .symbol "Wanted"]

private theorem variableArgumentRaw {live : List Atom} :
    InterpretArgsRel Space.empty noHostDispatch live
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (argumentPacket [.var "x"], Bindings.empty) := by
  apply InterpretArgsRel.success
      (.var "x") [] (.symbol "Wanted") [] Bindings.empty
      (.var "x", Bindings.empty) (argumentPacket [], Bindings.empty)
  · exact variablePassRaw "x" (.symbol "Wanted")
  · exact Or.inr rfl
  · exact InterpretArgsRel.nil Bindings.empty
  · exact ⟨[], rfl⟩

/-- Positive function recursion: variables pass the declared unary function
and argument types, producing the interpreted call expression. -/
example : InterpretFunctionRel Space.empty noHostDispatch []
    (.expression [.var "f", .var "x"])
    unaryWantedType (.symbol "Wanted") Bindings.empty
    (.expression [.var "f", .var "x"], Bindings.empty) := by
  apply InterpretFunctionRel.success
      (.expression [.var "f", .var "x"])
      unaryWantedType (.symbol "Wanted") (.var "f")
      (.symbol "Wanted")
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.var "f", Bindings.empty)
      (argumentPacket [.var "x"], Bindings.empty)
  · rfl
  · rfl
  · exact variablePassRaw "f" unaryWantedType
      (expectedApplicationScope
        (.expression [.var "f", .var "x"]) (.symbol "Wanted"))
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact variableArgumentRaw
  · exact ⟨[.var "x"], rfl⟩

/-- Positive type-cast path: an unannotated symbol has `%Undefined%`, which
matches any expected type. -/
example : EvalAtomRawRel Space.empty noHostDispatch []
    (.symbol "x") (.symbol "Wanted") Bindings.empty
    (.symbol "x", Bindings.empty) := by
  apply EvalAtomRawRel.cast
      (.symbol "x") (.symbol "Wanted") Atom.symbolType Bindings.empty
      (.symbol "x", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "x"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"x", rfl⟩
  · apply TypeCastRel.success
        (types := [Atom.undefinedType]) (earlierTypes := [])
        (laterTypes := []) (actualType := Atom.undefinedType)
    · exact TypesOfRel.symbolUndefined AnnotationTypesRel.nil
    · rfl
    · simp
    · exact TypeMatchRel.undefinedRight (.symbol "Wanted") Bindings.empty
  · exact .historical _ _

/-- A raw minimal unify step selects the else atom after a symbol mismatch. -/
example : Minimal.CoreStepRel Space.empty noHostDispatch []
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Bindings.empty (.symbol "else", Bindings.empty) := by
  apply Minimal.CoreStepRel.unifyNoMatch
  intro output hcandidate
  obtain ⟨matched, hmatch, _⟩ := hcandidate
  exact symbol_mismatch_not_match (by decide) matched hmatch

/-- The switch scanner returns Empty on an empty branch list. Ordinary
invocation of the authored switch library is a separate equation boundary. -/
example : SwitchStep (.symbol "a") [] Bindings.empty Atom.empty Bindings.empty :=
  SwitchStep.noMatch SwitchRawRel.nil

/-- Negative equation-query branch: an empty space returns the atom unchanged. -/
example : CallRel Space.empty noHostDispatch []
    (.symbol "unreduced") Atom.undefinedType Bindings.empty
    (.symbol "unreduced", Bindings.empty) := by
  apply CallRel.noEquation
  · rintro ⟨tail, hError⟩
    cases hError
  · simp [NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction]
  · intro freshPattern freshRhs matched hmatch
    obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
    simp [Space.empty] at hmem

private def noReduceDispatch : GroundedDispatch where
  executable := fun operator => operator = .symbol "native"
  outcome := fun operator _ result =>
    operator = .symbol "native" ∧ result = .noReduce

/-- Positive grounded boundary: a host `NoReduce` outcome preserves the call
unchanged without importing an executable dispatcher. -/
example : CallRel Space.empty noReduceDispatch []
    (.expression [.symbol "native", .symbol "argument"])
    Atom.undefinedType Bindings.empty
    (.expression [.symbol "native", .symbol "argument"], Bindings.empty) := by
  apply CallRel.groundedNoReduce
      (.expression [.symbol "native", .symbol "argument"])
      Atom.undefinedType (.symbol "native") [.symbol "argument"]
      Bindings.empty rfl
  · rfl
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

/-! Generic dispatch classifiers used by the source transport below. -/

/-- Renaming variable leaves preserves and reflects every literal symbolic
expression head, without a restriction on its arity. -/
theorem symbolHead_renameTypeVars_iff
    (rename : String → String) (source : Atom) (head : String) (tail : List Atom) :
    renameTypeVars rename source = .expression (.symbol head :: tail) ↔
      ∃ sourceTail, source = .expression (.symbol head :: sourceTail) ∧
        tail = sourceTail.map (renameTypeVars rename) := by
  constructor
  · intro equation
    cases source with
    | symbol | var | grounded => simp [renameTypeVars] at equation
    | expression atoms =>
        simp only [renameTypeVars, Atom.expression.injEq] at equation
        obtain ⟨sourceHead, sourceTail, sourceShape, headEquation, tailEquation⟩ :=
          List.map_eq_cons_iff.mp equation
        have headShape : sourceHead = .symbol head := by
          cases sourceHead <;> simp [renameTypeVars] at headEquation ⊢
          exact headEquation
        subst sourceHead
        exact ⟨sourceTail, congrArg Atom.expression sourceShape, tailEquation.symm⟩
  · rintro ⟨sourceTail, rfl, rfl⟩
    simp [renameTypeVars]

/-- Exact unary function wrappers retain the renamed body, rather than just
the truth of a classification predicate. -/
theorem functionBody_renameTypeVars_iff
    (rename : String → String) (source body : Atom) :
    renameTypeVars rename source = .expression [.symbol "function", body] ↔
      ∃ sourceBody, source = .expression [.symbol "function", sourceBody] ∧
        body = renameTypeVars rename sourceBody := by
  constructor
  · intro equation
    obtain ⟨sourceTail, sourceShape, tailEquation⟩ :=
      (symbolHead_renameTypeVars_iff rename source "function" [body]).mp equation
    obtain ⟨sourceBody, tailShape, bodyEquation⟩ :=
      List.map_eq_singleton_iff.mp tailEquation.symm
    exact ⟨sourceBody, by simpa [tailShape] using sourceShape, bodyEquation.symm⟩
  · rintro ⟨sourceBody, rfl, rfl⟩
    simp [renameTypeVars]

/-- The source's exact-arity function classifier is invariant under variable
renaming. This does not identify it with a function-head test at any arity. -/
theorem isFunction_renameTypeVars_iff (rename : String → String) (source : Atom) :
    IsFunction (renameTypeVars rename source) ↔ IsFunction source := by
  constructor
  · rintro ⟨body, equation⟩
    obtain ⟨sourceBody, sourceShape, _⟩ :=
      (functionBody_renameTypeVars_iff rename source body).mp equation
    exact ⟨sourceBody, sourceShape⟩
  · rintro ⟨body, rfl⟩
    exact ⟨renameTypeVars rename body, by simp [renameTypeVars]⟩

/-- Literal symbolic-head classification, at any arity, is invariant under
variable renaming. -/
theorem symbolicHead_renameTypeVars_iff
    (rename : String → String) (source : Atom) (head : String) :
    (∃ tail, renameTypeVars rename source = .expression (.symbol head :: tail)) ↔
      ∃ tail, source = .expression (.symbol head :: tail) := by
  constructor
  · rintro ⟨tail, equation⟩
    obtain ⟨sourceTail, sourceShape, _⟩ :=
      (symbolHead_renameTypeVars_iff rename source head tail).mp equation
    exact ⟨sourceTail, sourceShape⟩
  · rintro ⟨tail, rfl⟩
    exact ⟨tail.map (renameTypeVars rename), by simp [renameTypeVars]⟩

/-- Minimal instruction dispatch depends on literal heads, never on the
spelling of variable leaves or on a binding model for those variables. -/
theorem embeddedInstruction_renameTypeVars (rename : String → String) (source : Atom) :
    embeddedInstruction (renameTypeVars rename source) = embeddedInstruction source := by
  cases source with
  | symbol | var | grounded => simp [renameTypeVars, embeddedInstruction]
  | expression atoms =>
      cases atoms with
      | nil => simp [renameTypeVars, embeddedInstruction]
      | cons head tail => cases head <;> simp [renameTypeVars, embeddedInstruction]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-! ## Renaming the complete source configuration

These laws simultaneously transport the equation table, live continuation,
binding record, typing service and grounded service. In particular, diagnostic
renderers are transported explicitly: the laws do not assert that an arbitrary
unchanged service or name-rendering policy is equivariant.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

@[simp] theorem error_iff (permutation : Equiv.Perm String) (atom : Atom) :
    IsErrorRel (renameTypeVars permutation atom) ↔ IsErrorRel atom :=
  Minimal.symbolicHead_renameTypeVars_iff permutation atom "Error"

@[simp] theorem stopped_iff (permutation : Equiv.Perm String) (atom : Atom) :
    IsEmptyOrErrorRel (renameTypeVars permutation atom) ↔ IsEmptyOrErrorRel atom := by
  simp only [IsEmptyOrErrorRel, Atom.empty, atom_eq_symbol, error_iff]

@[simp] theorem atom_error (permutation : Equiv.Perm String) (subject message : Atom) :
    renameTypeVars permutation (Atom.error subject message) =
      Atom.error (renameTypeVars permutation subject) (renameTypeVars permutation message) := by
  simp [Atom.error]

@[simp] theorem packet (permutation : Equiv.Perm String) (atoms : List Atom) :
    renameTypeVars permutation (argumentPacket atoms) =
      argumentPacket (atoms.map (renameTypeVars permutation)) := by simp [argumentPacket]

theorem isPacket_iff (permutation : Equiv.Perm String) (atom : Atom) :
    (∃ atoms,renameTypeVars permutation atom=argumentPacket atoms) ↔
      ∃ atoms,atom=argumentPacket atoms := by
  constructor
  · rintro ⟨atoms,same⟩
    refine ⟨atoms.map (renameTypeVars permutation.symm),?_⟩
    simpa only [renameTypeVars_perm_inverse,packet] using congrArg (renameTypeVars permutation.symm) same
  · rintro ⟨atoms,rfl⟩
    exact ⟨_,packet permutation atoms⟩

@[simp] theorem metaType_iff (permutation : Equiv.Perm String) (atom type : Atom) :
    MetaTypeRel (renameTypeVars permutation atom) type ↔ MetaTypeRel atom type := by
  cases atom <;> simp only [atom_symbol, atom_var, atom_grounded, atom_expr] <;>
    constructor <;> intro h <;> cases h <;> constructor

theorem metaType_fixed {atom type : Atom} (h : MetaTypeRel atom type)
    (permutation : Equiv.Perm String) : renameTypeVars permutation type=type := by
  cases h <;> simp [Atom.symbolType,Atom.variableType,Atom.groundedType,Atom.expressionType]

theorem metaType (permutation : Equiv.Perm String) {atom type : Atom}
    (h : MetaTypeRel atom type) :
    MetaTypeRel (renameTypeVars permutation atom) (renameTypeVars permutation type) := by
  rw [metaType_fixed h permutation,metaType_iff]
  exact h

@[simp] theorem functionType_iff (permutation : Equiv.Perm String)
    (type : Atom) (arguments : List Atom) (returned : Atom) :
    FunctionTypeRel (renameTypeVars permutation type)
      (arguments.map (renameTypeVars permutation)) (renameTypeVars permutation returned) ↔
      FunctionTypeRel type arguments returned := by
  unfold FunctionTypeRel
  simpa only [renameTypeVars,List.map_cons,List.map_append,List.map_nil,List.cons_append] using
    (renameTypeVars_perm_injective permutation).eq_iff (a:=type)
      (b:=.expression (.symbol "->" :: arguments ++ [returned]))


private theorem filter_ne (permutation : Equiv.Perm String) (names : List String) (name : String) :
    (names.map permutation).filter (fun candidate=> !(candidate == permutation name)) =
      (names.filter (fun candidate=> !(candidate == name))).map permutation := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first=name
    · subst first
      simp [ih]
    · have mapped : permutation first ≠ permutation name := fun equal=>same (permutation.injective equal)
      simp [same,mapped,ih]

theorem names_eraseDups (permutation : Equiv.Perm String) (names : List String) :
    (names.map permutation).eraseDups = names.eraseDups.map permutation := by
  cases names with
  | nil => rfl
  | cons first rest =>
    rw [List.map_cons,List.eraseDups_cons,List.eraseDups_cons,List.map_cons,filter_ne,
      names_eraseDups]
termination_by names.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem scope (permutation : Equiv.Perm String) (expression expected : Atom) :
    expectedApplicationScope (renameTypeVars permutation expression) (renameTypeVars permutation expected) =
      (expectedApplicationScope expression expected).map permutation := by
  simp only [expectedApplicationScope,typeVars_renameTypeVars,←List.map_append,names_eraseDups]

@[simp] theorem unpack (permutation : Equiv.Perm String) (atom : Atom) :
    unpackArguments (renameTypeVars permutation atom) =
      (unpackArguments atom).map (List.map (renameTypeVars permutation)) := by
  cases h : unpackArguments atom with
  | none =>
    cases found : unpackArguments (renameTypeVars permutation atom) with
    | none => rfl
    | some atoms =>
      obtain ⟨original,rfl⟩ := (isPacket_iff permutation atom).mp
        ⟨atoms,unpackArguments_iff.mp found⟩
      simp at h
  | some atoms =>
    have shape := unpackArguments_iff.mp h
    simp only [shape,packet,unpackArguments_packet,Option.map_some]

@[simp] theorem values (permutation : Equiv.Perm String) (atom : Atom) :
    argumentValues (renameTypeVars permutation atom) =
      (argumentValues atom).map (renameTypeVars permutation) := by
  unfold argumentValues
  rw [unpack]
  cases unpackArguments atom <;> rfl

@[simp] theorem substitute (permutation : Equiv.Perm String) (name : String) (value : Atom) (atom : Atom) :
    renameTypeVars permutation (Minimal.substituteName name value atom) =
      Minimal.substituteName (permutation name) (renameTypeVars permutation value)
        (renameTypeVars permutation atom) := by
  induction atom using Atom.rec
    (motive_2:=fun atoms=>
      (atoms.map (Minimal.substituteName name value)).map (renameTypeVars permutation) =
      (atoms.map (renameTypeVars permutation)).map
        (Minimal.substituteName (permutation name) (renameTypeVars permutation value))) with
  | symbol => simp [Minimal.substituteName]
  | var varName =>
    by_cases same : varName=name
    · subst varName
      simp [Minimal.substituteName]
    · have mapped : permutation varName≠permutation name := fun eq=>same (permutation.injective eq)
      simp [Minimal.substituteName,same,mapped]
  | grounded => simp [Minimal.substituteName]
  | expression atoms ih => simpa [Minimal.substituteName] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

@[simp] theorem chain_iff (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.IsChain (renameTypeVars permutation atom) ↔ Minimal.IsChain atom :=
  Minimal.symbolicHead_renameTypeVars_iff permutation atom "chain"

@[simp] theorem function_iff (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.IsFunction (renameTypeVars permutation atom) ↔ Minimal.IsFunction atom :=
  Minimal.isFunction_renameTypeVars_iff permutation atom

@[simp] theorem embedded (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.embeddedInstruction (renameTypeVars permutation atom) = Minimal.embeddedInstruction atom :=
  Minimal.embeddedInstruction_renameTypeVars permutation atom

@[simp] theorem terminal (permutation : Equiv.Perm String) (caller : Option Atom) (atom : Atom) :
    renameTypeVars permutation (Minimal.functionTerminalResult caller atom) =
      Minimal.functionTerminalResult (caller.map (renameTypeVars permutation)) (renameTypeVars permutation atom) := by
  cases atom with
  | symbol => cases caller <;> simp [Minimal.functionTerminalResult]
  | var => cases caller <;> simp [Minimal.functionTerminalResult]
  | grounded => cases caller <;> simp [Minimal.functionTerminalResult]
  | expression atoms =>
    cases atoms with
    | nil => cases caller <;> simp [Minimal.functionTerminalResult]
    | cons head tail =>
      cases head with
      | symbol tag =>
        cases tail with
        | nil => cases caller <;> simp [Minimal.functionTerminalResult]
        | cons first rest =>
          cases rest with
          | nil => by_cases h : tag="return" <;> cases caller <;> simp [Minimal.functionTerminalResult,h]
          | cons => cases caller <;> simp [Minimal.functionTerminalResult]
      | var => cases caller <;> simp [Minimal.functionTerminalResult]
      | grounded => cases caller <;> simp [Minimal.functionTerminalResult]
      | expression => cases caller <;> simp [Minimal.functionTerminalResult]


@[simp] theorem atoms_equal (permutation : Equiv.Perm String) (left right : Atom) :
    renameTypeVars permutation left=renameTypeVars permutation right ↔ left=right :=
  (renameTypeVars_perm_injective permutation).eq_iff

@[simp] theorem pass_type (permutation : Equiv.Perm String) (expected intrinsic : Atom) :
    (renameTypeVars permutation expected=Atom.atomType ∨
      renameTypeVars permutation expected=renameTypeVars permutation intrinsic ∨
      renameTypeVars permutation intrinsic=Atom.variableType) ↔
      (expected=Atom.atomType ∨ expected=intrinsic ∨ intrinsic=Atom.variableType) := by
  simp only [Atom.atomType,Atom.variableType,atom_eq_symbol,atoms_equal]

theorem cast_shape (permutation : Equiv.Perm String) {atom : Atom}
    (shape : (∃ name,atom=.symbol name) ∨ (∃ value,atom=.grounded value) ∨ atom=Atom.unit) :
    (∃ name,renameTypeVars permutation atom=.symbol name) ∨
      (∃ value,renameTypeVars permutation atom=.grounded value) ∨
      renameTypeVars permutation atom=Atom.unit := by
  rcases shape with ⟨name,rfl⟩ | ⟨value,rfl⟩ | rfl
  · exact Or.inl ⟨name,by simp⟩
  · exact Or.inr (Or.inl ⟨value,by simp⟩)
  · exact Or.inr (Or.inr (by simp [Atom.unit]))

theorem nonempty_expression (permutation : Equiv.Perm String) {atom : Atom}
    (shape : ∃ head tail,atom=.expression (head::tail)) :
    ∃ head tail,renameTypeVars permutation atom=.expression (head::tail) := by
  obtain ⟨head,tail,rfl⟩ := shape
  exact ⟨renameTypeVars permutation head,tail.map (renameTypeVars permutation),by simp⟩

@[simp] theorem not_packet (permutation : Equiv.Perm String) (atom : Atom) :
    (∀ values,renameTypeVars permutation atom≠argumentPacket values) ↔
      ∀ values,atom≠argumentPacket values := by
  simpa only [not_exists] using not_congr (isPacket_iff permutation atom)

@[simp] theorem elements (permutation : Equiv.Perm String) (atom : Atom) :
    (match renameTypeVars permutation atom with | .expression atoms=>atoms | other=>[other]) =
      (match atom with | .expression atoms=>atoms | other=>[other]).map (renameTypeVars permutation) := by
  cases atom <;> simp

@[simp] theorem not_return (permutation : Equiv.Perm String) (atom : Atom) :
    (∀ value,renameTypeVars permutation atom≠.expression [.symbol "return",value]) ↔
      ∀ value,atom≠.expression [.symbol "return",value] := by
  constructor
  · intro missing value same
    apply missing (renameTypeVars permutation value)
    simp [same]
  · intro missing value same
    apply missing (renameTypeVars permutation.symm value)
    simpa using congrArg (renameTypeVars permutation.symm) same

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- One action on a full result preserves its syntax and complete binding rows. -/
def result (permutation : Equiv.Perm String) (source : ResultPair) : ResultPair :=
  (renameTypeVars permutation source.1,renameBindings permutation source.2)

def results (permutation : Equiv.Perm String) (source : ResultSet) : ResultSet :=
  source.map (result permutation)

@[simp] theorem result_inverse (permutation : Equiv.Perm String) (source : ResultPair) :
    result permutation.symm (result permutation source) = source := by
  cases source
  simp [result]

@[simp] theorem result_inverse_reverse (permutation : Equiv.Perm String) (source : ResultPair) :
    result permutation (result permutation.symm source) = source := result_inverse permutation.symm source

@[simp] theorem results_inverse (permutation : Equiv.Perm String) (source : ResultSet) :
    results permutation.symm (results permutation source) = source := by
  simp only [results,List.map_map,Function.comp_def,result_inverse]
  exact List.map_id source

@[simp] theorem results_inverse_reverse (permutation : Equiv.Perm String) (source : ResultSet) :
    results permutation (results permutation.symm source) = source := results_inverse permutation.symm source

/-- The same action carries the retained representation as well as its raw rows. -/
def frameResult (permutation : Equiv.Perm String) (source : FrameResult) : FrameResult :=
  (renameTypeVars permutation source.1, BindingFrame.rename permutation source.2)

@[simp] theorem frameResult_inverse (permutation : Equiv.Perm String) (source : FrameResult) :
    frameResult permutation.symm (frameResult permutation source) = source := by
  cases source
  simp [frameResult]

@[simp] theorem frameResult_inverse_reverse (permutation : Equiv.Perm String) (source : FrameResult) :
    frameResult permutation (frameResult permutation.symm source) = source :=
  frameResult_inverse permutation.symm source

@[simp] theorem frameResult_raw (permutation : Equiv.Perm String) (source : FrameResult) :
    BindingFrame.rawResult (frameResult permutation source) =
      result permutation (BindingFrame.rawResult source) := rfl

/-- Protocol cases and physical result multiplicity are retained. -/
def grounded (permutation : Equiv.Perm String) : GroundedResult → GroundedResult
  | .ok values => .ok (results permutation values)
  | .runtimeError message => .runtimeError message
  | .noReduce => .noReduce
  | .incorrectArgument => .incorrectArgument

@[simp] theorem grounded_inverse (permutation : Equiv.Perm String) (source : GroundedResult) :
    grounded permutation.symm (grounded permutation source) = source := by
  cases source <;> simp [grounded]

/-- The selected argument and return policy is transported as one object. -/
def policy (permutation : Equiv.Perm String) (source : SelectedTypePolicy) : SelectedTypePolicy where
  functionType := renameTypeVars permutation source.functionType
  argumentTypes := source.argumentTypes.map (renameTypeVars permutation)
  returnType := renameTypeVars permutation source.returnType
  isFunction := (functionType_iff permutation _ _ _).mpr source.isFunction

@[simp] theorem policy_inverse (permutation : Equiv.Perm String) (source : SelectedTypePolicy) :
    policy permutation.symm (policy permutation source) = source := by
  cases source
  simp [policy,Function.comp_def]

/-- A failed scan keeps each diagnostic occurrence and the tuple decision. -/
def scanOutcome (permutation : Equiv.Perm String) : FunctionCandidateScanOutcome → FunctionCandidateScanOutcome
  | .success selected bindings => .success (policy permutation selected) (renameBindings permutation bindings)
  | .exhausted errors eligible => .exhausted (errors.map (renameTypeVars permutation)) eligible

@[simp] theorem scanOutcome_inverse (permutation : Equiv.Perm String) (source : FunctionCandidateScanOutcome) :
    scanOutcome permutation.symm (scanOutcome permutation source) = source := by
  cases source <;> simp [scanOutcome,Function.comp_def]

/-- Transport opaque encoders by inverse reindexing of their semantic input.
The grounded payload itself is unchanged by syntactic variable renaming. -/
def services (permutation : Equiv.Perm String) (source : Minimal.Services) : Minimal.Services where
  bindingPayload := fun bindings=>source.bindingPayload (renameBindings permutation.symm bindings)
  contextPayload := fun context=>source.contextPayload (space permutation.symm context)
  nativeCall := fun name function arguments bindings returned=>
    source.nativeCall (renameTypeVars permutation.symm name) (renameTypeVars permutation.symm function)
      (renameTypeVars permutation.symm arguments) (renameBindings permutation.symm bindings)
      (result permutation.symm returned)

def enumeration (permutation : Equiv.Perm String) (source : Minimal.Enumeration) : Minimal.Enumeration where
  results := fun context atom expected bindings returned=>
    source.results (space permutation.symm context) (renameTypeVars permutation.symm atom)
      (renameTypeVars permutation.symm expected) (renameBindings permutation.symm bindings)
      (results permutation.symm returned)
  minimalResults := fun context atom bindings returned=>
    source.minimalResults (space permutation.symm context) (renameTypeVars permutation.symm atom)
      (renameBindings permutation.symm bindings) (results permutation.symm returned)

def host (permutation : Equiv.Perm String) (source : Minimal.HostPackage) : Minimal.HostPackage :=
  ⟨services permutation source.services,enumeration permutation source.enumeration⟩

/-- A transported foreign service is explicit. This construction makes no
claim that an arbitrary unchanged service is insensitive to variable names. -/
def dispatch (permutation : Equiv.Perm String) (source : GroundedDispatch) : GroundedDispatch where
  executable := fun operator=>source.executable (renameTypeVars permutation.symm operator)
  outcome := fun operator arguments returned=>
    source.outcome (renameTypeVars permutation.symm operator)
      (arguments.map (renameTypeVars permutation.symm)) (grounded permutation.symm returned)
  minimal := source.minimal.map (host permutation)
  valueProvenance := fun operator arguments=>source.valueProvenance
    (renameTypeVars permutation.symm operator) (arguments.map (renameTypeVars permutation.symm))
  bindingMode := fun operator arguments=>source.bindingMode
    (renameTypeVars permutation.symm operator) (arguments.map (renameTypeVars permutation.symm))
  unifyBadArityMessage := fun atom=>source.unifyBadArityMessage (renameTypeVars permutation.symm atom)

/-- Type inference, casting and selection retain their actual external
relations; only the simultaneous naming convention changes. -/
def typing (permutation : Equiv.Perm String) (source : EvalTypeService) : EvalTypeService where
  typesOf := fun context atom types=>source.typesOf (space permutation.symm context)
    (renameTypeVars permutation.symm atom) (types.map (renameTypeVars permutation.symm))
  typeCast := fun scope context atom expected bindings returned=>
    source.typeCast (scope.map permutation.symm) (space permutation.symm context)
      (renameTypeVars permutation.symm atom) (renameTypeVars permutation.symm expected)
      (renameBindings permutation.symm bindings) (result permutation.symm returned)
  instantiateTypes := fun scope raw selected =>
    source.instantiateTypes (scope.map permutation.symm)
      (raw.map (renameTypeVars permutation.symm))
      (selected.map (renameTypeVars permutation.symm))
  candidateScan := fun scope context expression expected bindings candidates selected=>
    source.candidateScan (scope.map permutation.symm) (space permutation.symm context) (renameTypeVars permutation.symm expression)
      (renameTypeVars permutation.symm expected) (renameBindings permutation.symm bindings)
      (candidates.map (renameTypeVars permutation.symm)) (scanOutcome permutation.symm selected)

@[simp] theorem typed_types (permutation : Equiv.Perm String) (source : EvalTypeService)
    (context : Space) (atom : Atom) (types : List Atom) :
    (typing permutation source).typesOf (space permutation context)
      (renameTypeVars permutation atom) (types.map (renameTypeVars permutation)) ↔
      source.typesOf context atom types := by simp [typing,Function.comp_def]

@[simp] theorem typed_cast (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (context : Space) (atom expected : Atom) (bindings : Bindings) (returned : ResultPair) :
    (typing permutation source).typeCast (scope.map permutation) (space permutation context)
      (renameTypeVars permutation atom) (renameTypeVars permutation expected)
      (renameBindings permutation bindings) (result permutation returned) ↔
      source.typeCast scope context atom expected bindings returned := by
  simp [typing,List.map_map,Function.comp_def]

@[simp] theorem typed_instances (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (raw selected : List Atom) :
    (typing permutation source).instantiateTypes (scope.map permutation)
      (raw.map (renameTypeVars permutation)) (selected.map (renameTypeVars permutation)) ↔
      source.instantiateTypes scope raw selected := by
  simp [typing, List.map_map, Function.comp_def]

@[simp] theorem typed_scan (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (context : Space) (atom expected : Atom) (bindings : Bindings) (candidates : List Atom)
    (selected : FunctionCandidateScanOutcome) :
    (typing permutation source).candidateScan (scope.map permutation) (space permutation context)
      (renameTypeVars permutation atom) (renameTypeVars permutation expected)
      (renameBindings permutation bindings) (candidates.map (renameTypeVars permutation))
      (scanOutcome permutation selected) ↔
      source.candidateScan scope context atom expected bindings candidates selected := by
  simp [typing,List.map_map,Function.comp_def]

@[simp] theorem dispatch_executable (permutation : Equiv.Perm String) (source : GroundedDispatch) (operator : Atom) :
    (dispatch permutation source).executable (renameTypeVars permutation operator) ↔
      source.executable operator := by simp [dispatch]

@[simp] theorem dispatch_outcome (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) (returned : GroundedResult) :
    (dispatch permutation source).outcome (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) (grounded permutation returned) ↔
      source.outcome operator arguments returned := by simp [dispatch,Function.comp_def]

@[simp] theorem dispatch_provenance (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) :
    (dispatch permutation source).valueProvenance (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) = source.valueProvenance operator arguments := by
  simp [dispatch,Function.comp_def]

@[simp] theorem dispatch_bindingMode (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) :
    (dispatch permutation source).bindingMode (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) = source.bindingMode operator arguments := by
  simp [dispatch,Function.comp_def]

@[simp] theorem encoded_result (permutation : Equiv.Perm String) (source : Minimal.Services) (returned : ResultPair) :
    Minimal.encodeResult (services permutation source) (result permutation returned) =
      renameTypeVars permutation (Minimal.encodeResult source returned) := by
  simp [Minimal.encodeResult,services,result]

@[simp] theorem encoded_results (permutation : Equiv.Perm String) (source : Minimal.Services) (returned : ResultSet) :
    Minimal.encodeResults (services permutation source) (results permutation returned) =
      renameTypeVars permutation (Minimal.encodeResults source returned) := by
  simp [Minimal.encodeResults,results,List.map_map,Function.comp_def]


@[simp] theorem services_inverse (permutation : Equiv.Perm String) (source : Minimal.Services) :
    services permutation.symm (services permutation source) = source := by
  cases source
  simp [services]

@[simp] theorem enumeration_inverse (permutation : Equiv.Perm String) (source : Minimal.Enumeration) :
    enumeration permutation.symm (enumeration permutation source) = source := by
  cases source
  simp [enumeration]

@[simp] theorem host_inverse (permutation : Equiv.Perm String) (source : Minimal.HostPackage) :
    host permutation.symm (host permutation source) = source := by
  cases source
  simp [host]

@[simp] theorem dispatch_inverse (permutation : Equiv.Perm String) (source : GroundedDispatch) :
    dispatch permutation.symm (dispatch permutation source) = source := by
  cases source
  simp [dispatch,Function.comp_def,Option.map_map]

@[simp] theorem typing_inverse (permutation : Equiv.Perm String) (source : EvalTypeService) :
    typing permutation.symm (typing permutation source) = source := by
  cases source
  simp [typing,Function.comp_def,List.map_map]

@[simp] theorem host_call (permutation : Equiv.Perm String) (source : GroundedDispatch) (atom : Atom) :
    Minimal.HostCall (dispatch permutation source) (renameTypeVars permutation atom) ↔
      Minimal.HostCall source atom := by
  cases atom with
  | symbol | var | grounded => simp [Minimal.HostCall]
  | expression atoms =>
    cases atoms with
    | nil => simp [Minimal.HostCall]
    | cons first rest => simp [Minimal.HostCall]

@[simp] theorem nonGrounded_call (permutation : Equiv.Perm String) (source : GroundedDispatch) (atom : Atom) :
    NonGroundedCallRel (dispatch permutation source) (renameTypeVars permutation atom) ↔
      NonGroundedCallRel source atom := by
  simp only [NonGroundedCallRel, host_call, Minimal.embeddedInstruction_renameTypeVars]

@[simp] theorem completed_keep (permutation : Equiv.Perm String) (value expected : Atom) :
    CompletedNativeKeepRel (renameTypeVars permutation value) (renameTypeVars permutation expected) ↔
      CompletedNativeKeepRel value expected := by
  unfold CompletedNativeKeepRel
  simp only [stopped_iff,Atom.undefinedType,Atom.atomType,atom_eq_symbol,metaType_iff]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨intrinsic,isMeta,passes⟩
    refine ⟨intrinsic,isMeta,?_⟩
    rcases passes with same | variableCase
    · exact Or.inl ((renameTypeVars_perm_injective permutation) (same.trans (metaType_fixed isMeta permutation).symm))
    · exact Or.inr variableCase
  · rintro ⟨intrinsic,isMeta,passes⟩
    refine ⟨intrinsic,isMeta,?_⟩
    rcases passes with rfl | variableCase
    · exact Or.inl (metaType_fixed isMeta permutation)
    · exact Or.inr variableCase

theorem completed_return (permutation : Equiv.Perm String)
    {context : Space} {types : EvalTypeService} {value expected : Atom}
    {protectedNames : List String} {bindings : BindingFrame} {returned : FrameResult}
    (derived : CompletedNativeReturnRel context types value expected bindings returned (protectedScope := protectedNames)) :
    CompletedNativeReturnRel (space permutation context) (typing permutation types)
      (renameTypeVars permutation value) (renameTypeVars permutation expected)
      (BindingFrame.rename permutation bindings) (frameResult permutation returned)
      (protectedScope := protectedNames.map permutation) := by
  cases derived with
  | keep keep => exact .keep ((completed_keep permutation value expected).mpr keep)
  | cast notKeep cast updated =>
    exact .cast (by simpa using notKeep) ((typed_cast permutation types protectedNames _ _ _ _ _).mpr cast) (updated.rename permutation)

@[simp] theorem minimal_host (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (provided : Minimal.HostPackage) (same : source.minimal=some provided) :
    (dispatch permutation source).minimal = some (host permutation provided) := by
  simp [dispatch,same]

@[simp] theorem native_call (permutation : Equiv.Perm String) (source : Minimal.Services)
    (name function arguments : Atom) (bindings : Bindings) (returned : ResultPair) :
    (services permutation source).nativeCall (renameTypeVars permutation name)
      (renameTypeVars permutation function) (renameTypeVars permutation arguments)
      (renameBindings permutation bindings) (result permutation returned) ↔
      source.nativeCall name function arguments bindings returned := by simp [services]

@[simp] theorem minimal_enumeration (permutation : Equiv.Perm String) (source : Minimal.Enumeration)
    (context : Space) (atom : Atom) (bindings : Bindings) (returned : ResultSet) :
    (enumeration permutation source).minimalResults (space permutation context)
      (renameTypeVars permutation atom) (renameBindings permutation bindings)
      (results permutation returned) ↔ source.minimalResults context atom bindings returned := by
  simp [enumeration]

@[simp] theorem context_payload (permutation : Equiv.Perm String) (source : Minimal.Services) (context : Space) :
    (services permutation source).contextPayload (space permutation context) = source.contextPayload context := by
  simp [services]


theorem native_emission (permutation : Equiv.Perm String)
    {source : GroundedDispatch} {operator raw value : Atom} {arguments : List Atom} {bindings : BindingFrame}
    (derived : NativeEmissionRel source operator arguments bindings raw value) :
    NativeEmissionRel (dispatch permutation source) (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) (BindingFrame.rename permutation bindings)
      (renameTypeVars permutation raw) (renameTypeVars permutation value) := by
  cases derived with
  | raw mode => exact .raw (by simpa using mode)
  | materialized mode materialized =>
    exact .materialized (by simpa using mode) (materialized.rename permutation)


/-- Rendering is an explicit service; its strings are not variable syntax. -/
@[simp] theorem diagnostic_message (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (atom : Atom) :
    (dispatch permutation source).unifyBadArityMessage (renameTypeVars permutation atom) =
      source.unifyBadArityMessage atom := by simp [dispatch]

theorem malformed_call_error (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (atom : Atom) :
    mkErrorMessage (renameTypeVars permutation atom)
        ((dispatch permutation source).unifyBadArityMessage (renameTypeVars permutation atom)) =
      renameTypeVars permutation (mkErrorMessage atom (source.unifyBadArityMessage atom)) := by
  simp [mkErrorMessage]


theorem type_model (p : Equiv.Perm String) {bindings : Bindings}
    (model : ∃ valuation,TypeBindingSatisfied valuation bindings) :
    ∃ valuation,TypeBindingSatisfied valuation (renameBindings p bindings) := by
  obtain ⟨valuation,satisfied⟩ := model
  refine ⟨valuation ∘ p.symm,(renameBindings_typeBindingSatisfied _ _ _).mpr ?_⟩
  simpa [Function.comp_def] using satisfied

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Eval.Steps Spec.Match.Merge

open Spec.Type.Presentation.ScopeObservation

theorem type_candidate_variant (p : Equiv.Perm String) {scope : List String}
    {original instantiated : Atom}
    (variant : Exact.TypeCandidateAlphaVariantRel scope original instantiated) :
    Exact.TypeCandidateAlphaVariantRel (scope.map p)
      (renameTypeVars p original) (renameTypeVars p instantiated) := by
  obtain ⟨rename, injective, rfl, fresh⟩ := variant
  refine ⟨fun name => p (rename (p.symm name)),
    p.injective.comp (injective.comp p.symm.injective), ?_, ?_⟩
  · simp only [renameTypeVars_comp]
    apply renameTypeVars_congr_on_typeVars
    intro name _
    simp
  · intro name member
    rw [typeVars_renameTypeVars] at member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    simpa using fresh old oldMember

theorem argument_variants (p : Equiv.Perm String) {scope : List String}
    {original instantiated : List Atom}
    (variants : Exact.ArgumentAlphaVariantsRel scope original instantiated) :
    Exact.ArgumentAlphaVariantsRel (scope.map p)
      (original.map (renameTypeVars p)) (instantiated.map (renameTypeVars p)) := by
  induction variants with
  | nil => exact .nil _
  | cons variant _rest ih =>
      exact .cons (type_candidate_variant p variant)
        (by simpa only [List.map_append, typeVars_renameTypeVars] using ih)

@[simp] theorem invocation_scope (p : Equiv.Perm String) (protectedNames : List String)
    (live : List Atom) (subject expected : Atom) (bindings : Bindings) :
    invocationTypeScope (protectedNames.map p) (live.map (renameTypeVars p))
      (renameTypeVars p subject) (renameTypeVars p expected) (renameBindings p bindings) =
      (invocationTypeScope protectedNames live subject expected bindings).map p := by
  simp only [invocationTypeScope, List.map_append, List.map_cons, List.map_nil,
    ← typeVarsList_renameTypeVars, specBindingVars_renameBindings]

mutual

theorem eval_atom (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {protectedNames : List String} {types : EvalTypeService}
    (derived : EvalAtomRawRel context service live atom expected bindings returned
      (protectedScope := protectedNames) (typing := types)) :
    EvalAtomRawRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .emptyOrError atom expected bindings stopped => by exact .emptyOrError _ _ _ (by simpa using stopped)
  | .typePass atom expected intrinsic bindings nonstopped intrinsicType pass => by
    exact .typePass _ _ (renameTypeVars p intrinsic) _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((pass_type p _ _).mpr pass)
  | .cast atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape cast updated => by
    exact .cast _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (cast_shape p shape)
      (by simpa only [invocation_scope, BindingFrame.rename, frameResult_raw] using
        (typed_cast p _ _ _ _ _ _ _).mpr cast) (updated.rename p)
  | .interpretSuccess atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape interpreted nonerror => by
    exact .interpretSuccess _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (nonempty_expression p shape)
      (interpret_expression p interpreted) (by simpa [frameResult] using nonerror)
  | .interpretError atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape interpreted error => by
    exact .interpretError _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (nonempty_expression p shape)
      (interpret_expression p interpreted) (by simpa [frameResult] using error)
termination_by structural derived

theorem interpret_expression (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretExpressionRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretExpressionRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .functionPath expression expected operator arguments rawTypes candidates selected callType bindings applicable interpreted called
      shape inferred instantiated scanned updated callTypeEq functionDerivation callDerivation => by
    refine .functionPath _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p)) (policy p selected) (renameTypeVars p callType)
      _ (BindingFrame.rename p applicable) (frameResult p interpreted) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [shape]
    · exact (typed_types p _ _ _ _).mpr inferred
    · simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated
    · simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned
    · exact updated.rename p
    · by_cases isExpression : selected.returnType = .symbol "Expression"
      <;> simp [policy,callTypeEq,Atom.expressionType,Atom.undefinedType,isExpression]
    · simpa only [List.map_cons,policy] using interpret_function p functionDerivation
    · exact call p callDerivation
  | .tuplePath expression expected operator arguments rawTypes candidates errors bindings tuple called
      shape inferred instantiated scanned tupleDerivation callDerivation => by
    refine .tuplePath _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p)) (errors.map (renameTypeVars p)) _ (frameResult p tuple) _
      (by simp [shape]) ((typed_types p _ _ _ _).mpr inferred)
      (by simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated) ?_ ?_ (call p callDerivation)
    · simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned
    · simpa only [List.map_cons] using interpret_tuple p tupleDerivation
  | .functionError expression expected operator error arguments rawTypes candidates errors eligible bindings
      shape inferred instantiated scanned present => by
    exact .functionError _ _ (renameTypeVars p operator) (renameTypeVars p error)
      (arguments.map (renameTypeVars p)) (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p))
      (errors.map (renameTypeVars p)) eligible _ (by simp [shape])
      ((typed_types p _ _ _ _).mpr inferred)
      (by simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated) (by simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned)
      (List.mem_map.mpr ⟨error,present,rfl⟩)
termination_by structural derived

theorem interpret_function (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {expression functionType expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretFunctionRel context service live expression functionType expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretFunctionRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p expression) (renameTypeVars p functionType) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .headError expression functionType expected operator declaredReturn arguments argumentTypes bindings head
      shape functionShape headDerivation stopped => by
    refine .headError _ _ _ (renameTypeVars p operator) (renameTypeVars p declaredReturn)
      (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p)) _ _
      (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape) ?_ (by simpa [frameResult] using stopped)
    simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation
  | .tailError expression functionType expected operator declaredReturn arguments argumentTypes bindings head tail
      shape functionShape headDerivation nonstopped tailDerivation noPacket => by
    refine .tailError _ _ _ (renameTypeVars p operator) (renameTypeVars p declaredReturn)
      (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p)) _ (frameResult p head) _
      (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape) ?_
      (by simpa [frameResult] using nonstopped) ?_ (by simpa [frameResult] using noPacket)
    · simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation
    · simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation
  | .success expression functionType expected operator declaredReturn arguments argumentTypes bindings head tail
      shape functionShape headDerivation nonstopped tailDerivation packetShape => by
    simpa only [frameResult,atom_expr,List.map_cons,values] using
      InterpretFunctionRel.success (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p expression) (renameTypeVars p functionType) (renameTypeVars p expected)
        (renameTypeVars p operator) (renameTypeVars p declaredReturn)
        (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p))
        (BindingFrame.rename p bindings) (frameResult p head) (frameResult p tail)
        (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape)
        (by simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation)
        (by simpa [frameResult] using nonstopped)
        (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
        ((isPacket_iff p _).mpr packetShape)
termination_by structural derived

theorem interpret_args (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {arguments expected : List Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretArgsRel context service live arguments expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretArgsRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (arguments.map (renameTypeVars p)) (expected.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .nil bindings => by
    simpa [frameResult] using InterpretArgsRel.nil
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (BindingFrame.rename p bindings)
  | .headChangedError argument arguments expected expecteds bindings head headDerivation stopped changed => by
    exact .headChangedError _ _ _ _ _ _
      (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
      (by simpa [frameResult] using stopped) (by simpa [frameResult] using changed)
  | .tailError argument arguments expected expecteds bindings head tail headDerivation eligible tailDerivation noPacket => by
    exact .tailError _ _ _ _ _ (frameResult p head) _
      (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
      (by simpa [frameResult] using eligible)
      (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
      (by simpa [frameResult] using noPacket)
  | .success argument arguments expected expecteds bindings head tail headDerivation eligible tailDerivation packetShape => by
    simpa only [frameResult,packet,List.map_cons,values] using
      InterpretArgsRel.success (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p argument) (arguments.map (renameTypeVars p))
        (renameTypeVars p expected) (expecteds.map (renameTypeVars p))
        (BindingFrame.rename p bindings) (frameResult p head) (frameResult p tail)
        (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
        (by simpa [frameResult] using eligible)
        (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
        ((isPacket_iff p _).mpr packetShape)
termination_by structural derived

theorem interpret_tuple (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {expression : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretTupleRel context service live expression bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretTupleRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p expression) (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .nil bindings => by
    simpa [frameResult,Atom.unit] using InterpretTupleRel.nil
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (BindingFrame.rename p bindings)
  | .singleton atom bindings returned headDerivation nonstopped => by
    simpa [frameResult] using InterpretTupleRel.singleton
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using nonstopped)
  | .singletonError atom bindings returned headDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.singletonError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using stopped)
  | .headError head tail bindings returned nonempty headDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.headError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p returned) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using stopped)
  | .tailError head tail bindings first rest nonempty headDerivation nonstopped tailDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.tailError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p first) (frameResult p rest) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation)
      (by simpa [frameResult] using nonstopped)
      (by simpa [frameResult] using interpret_tuple p tailDerivation) (by simpa [frameResult] using stopped)
  | .success head tail bindings first rest nonempty headDerivation nonstopped tailDerivation restNonstopped => by
    have transported := InterpretTupleRel.success
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p first) (frameResult p rest) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation)
      (by simpa [frameResult] using nonstopped)
      (by simpa [frameResult] using interpret_tuple p tailDerivation) (by simpa [frameResult] using restNonstopped)
    cases valueEq : rest.1 <;> simpa [frameResult,valueEq,renameTypeVars] using transported
termination_by structural derived

theorem call_return (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {original expected value : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : CallReturnRel context service live original expected value bindings returned (protectedScope := protectedNames) (typing := types)) :
    CallReturnRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p original) (renameTypeVars p expected) (renameTypeVars p value)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .notReducible original expected bindings => by
    simpa [frameResult] using CallReturnRel.notReducible
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p original) (renameTypeVars p expected) (BindingFrame.rename p bindings)
  | .stopped original expected value bindings stopped => by exact .stopped _ _ _ _ (by simpa using stopped)
  | .evaluate original expected value bindings returned notNR nonstopped evaluated => by
    exact .evaluate _ _ _ _ _ (by simpa [Atom.notReducible] using notNR)
      (by simpa using nonstopped) (by simpa only [List.map_nil] using eval_atom p evaluated)
termination_by structural derived

theorem call (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : CallRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    CallRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .errorPassthrough atom expected bindings error => by exact .errorPassthrough _ _ _ (by simpa using error)
  | .embedded atom expected bindings raw returned nonerror noHost embedded invoked completed => by
    exact .embedded _ _ _ (frameResult p raw) _
      (by simpa using nonerror) (by simpa using noHost) (by simpa using embedded)
      (by simpa only [List.map_cons, Option.map_none] using core_invocation p invoked)
      (by simpa only [frameResult] using call_return p completed)
  | .groundedSuccess atom expected operator arguments bindings nativeResults nativeResult finalResult merged emitted completed
      shape executable provenance nonerror produced present merge updated emission invoked returned => by
    refine .groundedSuccess _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      _ (results p nativeResults) (result p nativeResult) _ (BindingFrame.rename p merged)
      (renameTypeVars p emitted) (frameResult p completed) (by simp [shape])
      (by simpa using executable) (by simpa using provenance)
      (by simpa using nonerror) ?_ ?_ (merge_rename p merge) (updated.rename p)
      (native_emission p emission) ?_ (call_return p returned)
    · simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced
    · exact List.mem_map.mpr ⟨nativeResult,present,rfl⟩
    · simpa only [List.map_cons,Option.map_some] using core_result p invoked
  | .groundedCompletedSuccess atom expected operator arguments bindings nativeResults nativeResult finalResult merged emitted
      shape executable provenance nonerror produced present merge updated emission returned => by
    refine .groundedCompletedSuccess _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      _ (results p nativeResults) (result p nativeResult) _ (BindingFrame.rename p merged)
      (renameTypeVars p emitted) (by simp [shape]) (by simpa using executable)
      (by simpa using provenance)
      (by simpa using nonerror) ?_ ?_ (merge_rename p merge) (updated.rename p) (native_emission p emission)
      (by simpa only [invocation_scope, BindingFrame.rename] using completed_return p returned)
    · simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced
    · exact List.mem_map.mpr ⟨nativeResult,present,rfl⟩
  | .groundedRuntimeError atom expected operator arguments bindings message shape executable nonerror produced => by
    simpa only [frameResult,atom_error,atom_symbol] using
      CallRel.groundedRuntimeError (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (renameTypeVars p operator)
        (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings) message
        (by simp [shape]) (by simpa using executable)
        (by simpa using nonerror)
        (by simpa only [←dispatch_outcome p service operator arguments (.runtimeError message),grounded] using produced)
  | .groundedNoReduce atom expected operator arguments bindings shape executable nonerror produced => by
    exact .groundedNoReduce _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p)) _
      (by simp [shape]) (by simpa using executable)
      (by simpa using nonerror)
      (by simpa only [←dispatch_outcome p service operator arguments .noReduce,grounded] using produced)
  | .groundedIncorrectArgument atom expected operator arguments bindings shape executable nonerror produced => by
    exact .groundedIncorrectArgument _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p)) _
      (by simp [shape]) (by simpa using executable)
      (by simpa using nonerror)
      (by simpa only [←dispatch_outcome p service operator arguments .incorrectArgument,grounded] using produced)
  | .groundedEmpty atom expected operator arguments bindings shape executable nonerror produced => by
    simpa only [frameResult,atom_empty] using
      CallRel.groundedEmpty (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (renameTypeVars p operator)
        (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
        (by simp [shape]) (by simpa using executable)
        (by simpa using nonerror)
        (by simpa only [←dispatch_outcome p service operator arguments (.ok []),grounded,results,List.map_nil] using produced)
  | .equation atom expected emitted materialized bindings merged finalResult completed
      nonerror nongrounded selected updated materialization invoked returned => by
    exact .equation _ _ (renameTypeVars p emitted) (renameTypeVars p materialized) _
      (BindingFrame.rename p merged) _ (frameResult p completed) (by simpa using nonerror)
      (by simpa using nongrounded) (by simpa only [List.map_cons, BindingFrame.rename] using query_candidate p selected) (updated.rename p)
      (materialization.rename p) (by simpa only [List.map_cons,Option.map_some] using core_result p invoked)
      (call_return p returned)
  | .noEquation atom expected bindings nonerror nongrounded noMatch => by
    exact .noEquation _ _ _ (by simpa using nonerror) (by simpa using nongrounded)
        (by simpa only [List.map_cons, BindingFrame.rename] using query_no_match p noMatch)
  | .allEquationsFiltered atom expected bindings nonerror nongrounded filtered => by
    simpa only [frameResult,atom_empty] using
      CallRel.allEquationsFiltered (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
        (by simpa using nonerror) (by simpa using nongrounded)
        (by simpa only [List.map_cons, BindingFrame.rename] using query_filtered p filtered)
termination_by structural derived

theorem core_step (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreStepRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreStepRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .eval context atom materialized bindings returned materialization invoked => by
    simpa [frameResult] using Minimal.CoreStepRel.eval (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (renameTypeVars p materialized) (BindingFrame.rename p bindings)
      (frameResult p returned) (materialization.rename p) (core_invocation p invoked)
  | .evalc context selected atom materialized bindings returned hostServices hostEnumeration provided materialization invoked => by
    simpa [frameResult] using Minimal.CoreStepRel.evalc (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p materialized)
      (BindingFrame.rename p bindings) (frameResult p returned) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (materialization.rename p) (core_invocation p invoked)
  | .chain context atom name template bindings returned materialized ran materialization => by
    simpa [frameResult,substitute] using Minimal.CoreStepRel.chain (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (p name) (renameTypeVars p template)
      (BindingFrame.rename p bindings) (frameResult p returned) (renameTypeVars p materialized)
      (by simpa using core_run p ran) (materialization.rename p)
  | .unifySuccess context target pattern thenBranch elseBranch emitted bindings output matched updated materialized => by
    simpa [frameResult] using Minimal.CoreStepRel.unifySuccess (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p target) (renameTypeVars p pattern)
      (renameTypeVars p thenBranch) (renameTypeVars p elseBranch) (renameTypeVars p emitted)
      (BindingFrame.rename p bindings) (BindingFrame.rename p output)
      (unify_candidate p matched) (updated.rename p) (materialized.rename p)
  | .unifyNoMatch context target pattern thenBranch elseBranch bindings missing => by
    simpa [frameResult] using Minimal.CoreStepRel.unifyNoMatch (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p target) (renameTypeVars p pattern)
      (renameTypeVars p thenBranch) (renameTypeVars p elseBranch)
      (BindingFrame.rename p bindings) (unify_no_match p missing)
  | .unifyBadArity context tail bindings wrong => by
    simpa only [frameResult, ←malformed_call_error, atom_expr, List.map_cons,
      atom_symbol] using
      Minimal.CoreStepRel.unifyBadArity (dispatch := dispatch p service)
        (live := live.map (renameTypeVars p)) (typing := typing p types)
        (caller := caller.map (renameTypeVars p))
        (space p context) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
        (by simpa using wrong)
  | .consAtom context head tail bindings => by
    simpa [frameResult] using Minimal.CoreStepRel.consAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p head) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
  | .deconsAtom context head tail bindings => by
    simpa [frameResult] using Minimal.CoreStepRel.deconsAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p head) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
  | .collapseBind context atom bindings collected hostServices hostEnumeration provided historicalFrame collectedDerivation => by
    simpa [frameResult] using Minimal.CoreStepRel.collapseBind (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings) (results p collected)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
      (historicalFrame.rename p) ((minimal_enumeration p hostEnumeration _ _ _ _).mpr collectedDerivation)
  | .superposeBind context collected stored bindings merged hostServices hostEnumeration provided historicalFrame present merge updated => by
    simpa [frameResult, result] using Minimal.CoreStepRel.superposeBind (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (results p collected) (result p stored) (BindingFrame.rename p bindings)
      (BindingFrame.rename p merged) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (historicalFrame.rename p)
      (List.mem_map.mpr ⟨stored,present,rfl⟩) (merge_rename p merge) (updated.rename p)
  | .functionReturn context body returned bindings output shaped finished => by
    simpa [frameResult] using Minimal.CoreStepRel.functionReturn (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (renameTypeVars p returned) (BindingFrame.rename p bindings)
      (BindingFrame.rename p output) (by obtain ⟨atoms,rfl⟩:=shaped; exact ⟨atoms.map (renameTypeVars p),atom_expr p atoms⟩)
      (by simpa [frameResult] using core_body p finished)
  | .functionNoReturn context body returned bindings output shaped finished missing => by
    simpa [frameResult,terminal] using Minimal.CoreStepRel.functionNoReturn (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (renameTypeVars p returned) (BindingFrame.rename p bindings)
      (BindingFrame.rename p output) (by obtain ⟨atoms,rfl⟩:=shaped; exact ⟨atoms.map (renameTypeVars p),atom_expr p atoms⟩)
      (by simpa [frameResult] using core_body p finished) ((not_return p _).mpr missing)
  | .metta context selected atom expected bindings returned hostServices hostEnumeration provided evaluated nonerror => by
    simpa [frameResult] using Minimal.CoreStepRel.metta (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (frameResult p returned) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (by simpa only [List.map_nil] using eval_atom p evaluated)
      (by simpa [frameResult] using nonerror)
  | .mettaAtom context selected atom bindings hostServices hostEnumeration provided => by
    simpa [frameResult,Atom.atomType] using Minimal.CoreStepRel.mettaAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
  | .mettaError context selected atom expected bindings hostServices hostEnumeration provided error => by
    simpa [frameResult] using Minimal.CoreStepRel.mettaError (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (by simpa using error)
  | .contextSpace context bindings hostServices hostEnumeration provided => by
    simpa [frameResult] using Minimal.CoreStepRel.contextSpace (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (BindingFrame.rename p bindings) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided)
  | .callNative context name function arguments bindings returned merged hostServices hostEnumeration provided native merge updated => by
    simpa [frameResult, result] using Minimal.CoreStepRel.callNative (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p name) (renameTypeVars p function) (renameTypeVars p arguments)
      (BindingFrame.rename p bindings) (result p returned) (BindingFrame.rename p merged)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
      ((native_call p hostServices _ _ _ _ _).mpr native) (merge_rename p merge) (updated.rename p)
termination_by structural derived

theorem core_invocation (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreInvocationRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .embedded context atom bindings returned nonhost instruction ran => by
    exact .embedded _ _ _ _ (by simpa using nonhost) (by simpa using instruction) (core_run p ran)
  | .grounded context operator arguments bindings merged nativeResults nativeResult returned emitted
      executable provenance produced present merge updated model emission invoked => by
    simpa [frameResult] using Minimal.CoreInvocationRel.grounded (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (BindingFrame.rename p merged) (results p nativeResults)
      (result p nativeResult) (frameResult p returned) (renameTypeVars p emitted)
      (by simpa using executable) (by simpa using provenance)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced)
      (List.mem_map.mpr ⟨nativeResult,present,rfl⟩) (merge_rename p merge) (updated.rename p) (type_model p model)
      (native_emission p emission)
      (by simpa only [Option.map_some, renameTypeVars, List.map_cons] using core_result p invoked)
  | .completedGrounded context operator arguments bindings merged nativeResults nativeResult emitted
      executable provenance produced present merge updated model emission => by
    simpa [frameResult] using Minimal.CoreInvocationRel.completedGrounded (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (BindingFrame.rename p merged) (results p nativeResults)
      (result p nativeResult) (renameTypeVars p emitted)
      (by simpa using executable) (by simpa using provenance)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced)
      (List.mem_map.mpr ⟨nativeResult,present,rfl⟩) (merge_rename p merge) (updated.rename p) (type_model p model)
      (native_emission p emission)
  | .groundedEmpty context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedEmpty (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok []),grounded,results,List.map_nil] using produced)
  | .groundedError context operator arguments bindings message executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedError (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings) message
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments (.runtimeError message),grounded] using produced)
  | .groundedNoReduce context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedNoReduce (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments .noReduce,grounded] using produced)
  | .groundedIncorrectArgument context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedIncorrectArgument (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments .incorrectArgument,grounded] using produced)
  | .equation context atom emitted materialized bindings merged returned nonhost notInstruction selected updated materialization invoked => by
    exact .equation _ _ (renameTypeVars p emitted) (renameTypeVars p materialized) _ (BindingFrame.rename p merged) _
      (by simpa using nonhost) (by simpa using notInstruction) (query_candidate p selected)
      (updated.rename p) (materialization.rename p) (core_result p invoked)
  | .noEquation context atom bindings nonhost notInstruction noMatch => by
    simpa [frameResult] using Minimal.CoreInvocationRel.noEquation (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (by simpa using nonhost) (by simpa using notInstruction) (query_no_match p noMatch)
  | .allEquationsFiltered context atom bindings nonhost notInstruction filtered => by
    simpa [frameResult] using Minimal.CoreInvocationRel.allEquationsFiltered (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (by simpa using nonhost) (by simpa using notInstruction) (query_filtered p filtered)
termination_by structural derived

theorem core_result (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationResultRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreInvocationResultRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .raw context atom bindings nonfunction => by exact .raw _ _ _ (by simpa using nonfunction)
  | .function context body bindings returned stepped => by
    simpa using Minimal.CoreInvocationResultRel.function (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa using core_step p stepped)
termination_by structural derived

theorem core_run (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreRunRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreRunRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .data context atom bindings data => by exact .data _ _ _ (by simpa using data)
  | .instruction context atom bindings returned instruction nonchain stepped => by
    exact .instruction _ _ _ _ (by simpa using instruction) (by simpa using nonchain) (core_step p stepped)
  | .chain context atom bindings selected returned chainShape stepped resumed => by
    exact .chain _ _ _ (frameResult p selected) _ (by simpa using chainShape) (core_step p stepped) (core_run p resumed)
termination_by structural derived

theorem core_body (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreFunctionBodyRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreFunctionBodyRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .terminal context atom bindings raw materialized ran materialization noninstruction => by
    exact .terminal _ _ _ (frameResult p raw) (renameTypeVars p materialized)
      (core_run p ran) (materialization.rename p) (by simpa using noninstruction)
  | .resume context atom bindings raw materialized returned ran materialization instruction resumed => by
    exact .resume _ _ _ (frameResult p raw) (renameTypeVars p materialized) _
      (core_run p ran) (materialization.rename p) (by simpa using instruction) (core_body p resumed)
termination_by structural derived

end

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

/-- The inverse action reflects raw derivations, including their complete
protected scope and reached result record. -/
theorem eval_atom_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {protectedNames : List String} {types : EvalTypeService} :
    EvalAtomRawRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    EvalAtomRawRel context service live atom expected bindings returned
      (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [List.map_map,Function.comp_def] using eval_atom p.symm derived
  · exact eval_atom p

theorem call_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    CallRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    CallRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using call p.symm derived
  · exact call p

theorem call_return_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {original expected value : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    CallReturnRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p original) (renameTypeVars p expected) (renameTypeVars p value)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    CallReturnRel context service live original expected value bindings returned (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using call_return p.symm derived
  · exact call_return p

theorem core_run_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom} :
    Minimal.CoreRunRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) ↔
    Minimal.CoreRunRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller) := by
  constructor
  · intro derived
    simpa [Option.map_map,Function.comp_def,List.map_map] using core_run p.symm derived
  · exact core_run p

theorem core_step_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom} :
    Minimal.CoreStepRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) ↔
    Minimal.CoreStepRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller) := by
  constructor
  · intro derived
    simpa [Option.map_map,Function.comp_def,List.map_map] using core_step p.symm derived
  · exact core_step p

/-- Success priority is transported as well: an error is published only
when all actual raw alternatives are errors on both sides. -/
theorem eval (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : EvalRel context service live atom expected bindings returned types protectedNames) :
    EvalRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (typing p types) (protectedNames.map p) := by
  refine ⟨by simpa using eval_atom p derived.1, ?_⟩
  intro error candidate raw
  have sourceRaw : EvalAtomRawRel context service live atom expected bindings
      (frameResult p.symm candidate) (protectedScope := protectedNames) (typing := types) := by
    simpa [Function.comp_def,List.map_map] using eval_atom p.symm raw
  have sourceError := derived.2 (by simpa [frameResult] using error) _ sourceRaw
  simpa [frameResult] using sourceError

theorem eval_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    EvalRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (typing p types) (protectedNames.map p) ↔
    EvalRel context service live atom expected bindings returned types protectedNames := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using eval p.symm derived
  · exact eval p

/-- Exact physical list positions are retained by the output action. This is
a law of a chosen enumeration, not an enumeration-order requirement on HE. -/
theorem results_position (p : Equiv.Perm String) (produced : ResultSet) (position : Nat) :
    (results p produced)[position]? = produced[position]?.map (result p) := by
  simp only [results,List.getElem?_map]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming


/-! ## Simultaneous renaming of the concrete published type service -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open Spec.Eval.Renaming
open Spec.Match.Merge

theorem AnnotationTypesRel.rename (p : Equiv.Perm String)
    {target : Atom} {atoms types : List Atom}
    (derivation : AnnotationTypesRel target atoms types) :
    AnnotationTypesRel (renameTypeVars p target)
      (atoms.map (renameTypeVars p)) (types.map (renameTypeVars p)) := by
  induction derivation with
  | nil => exact .nil
  | hit _tail ih =>
      simpa only [List.map_cons, atom_expr, atom_symbol, List.map_nil] using
        AnnotationTypesRel.hit ih
  | skip noAnnotation _tail ih =>
      apply AnnotationTypesRel.skip _ ih
      intro type same
      apply noAnnotation (renameTypeVars p.symm type)
      simpa only [atom_expr, List.map_cons, List.map_nil, atom_symbol, renameTypeVars_perm_inverse] using
        congrArg (renameTypeVars p.symm) same

theorem IntrinsicGroundedTypeRel.renamed (p : Equiv.Perm String)
    {value : OSLFCore.GroundedValue} {type : Atom}
    (derivation : IntrinsicGroundedTypeRel value type) :
    IntrinsicGroundedTypeRel value (renameTypeVars p type) := by
  cases derivation <;> simp only [atom_symbol] <;> constructor

theorem TypesOfRel.rename (p : Equiv.Perm String)
    {context : Space} {atom : Atom} {types : List Atom}
    (derivation : TypesOfRel context atom types) :
    TypesOfRel (space p context) (renameTypeVars p atom)
      (types.map (renameTypeVars p)) := by
  cases derivation with
  | «variable» name =>
      simpa only [atom_var, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        TypesOfRel.variable (space p context) (p name)
  | groundedKnown intrinsic notUndefined =>
      simpa only [atom_grounded, List.map_cons, List.map_nil] using
        TypesOfRel.groundedKnown (intrinsic.renamed p)
          (by
            intro same
            exact notUndefined ((atom_eq_symbol p _ _).mp same))
  | groundedUndefined intrinsic =>
      simpa only [atom_grounded, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        TypesOfRel.groundedUndefined (space := space p _) intrinsic
  | symbolKnown annotations nonempty =>
      simp only [atom_symbol]
      apply TypesOfRel.symbolKnown
      · simpa only [space, atom_symbol] using annotations.rename p
      · exact fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  | symbolUndefined annotations =>
      simpa only [atom_symbol, List.map_cons, List.map_nil, Atom.undefinedType] using
        TypesOfRel.symbolUndefined
          (space := space p context)
          (by simpa only [space, atom_symbol, List.map_nil] using annotations.rename p)
  | unit =>
      simpa only [atom_expr, List.map_nil, List.map_cons, Atom.undefinedType, atom_symbol] using
        TypesOfRel.unit (space p context)
  | expressionKnown annotations nonempty =>
      simp only [atom_expr, List.map_cons]
      apply TypesOfRel.expressionKnown
      · simpa only [space, atom_expr, List.map_cons] using annotations.rename p
      · exact fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  | expressionUndefined annotations =>
      simpa only [atom_expr, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        TypesOfRel.expressionUndefined (space := space p context)
          (by simpa only [space, atom_expr, List.map_cons, List.map_nil] using annotations.rename p)

theorem TypesOfRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (atom : Atom) (types : List Atom) :
    TypesOfRel (space p context) (renameTypeVars p atom) (types.map (renameTypeVars p)) ↔
      TypesOfRel context atom types := by
  constructor
  · intro derivation
    simpa only [space_inverse, renameTypeVars_perm_inverse, atoms_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

theorem TypeOfRel.rename (p : Equiv.Perm String)
    {context : Space} {atom type : Atom} (derivation : TypeOfRel context atom type) :
    TypeOfRel (space p context) (renameTypeVars p atom) (renameTypeVars p type) := by
  obtain ⟨types, inferred, member⟩ := derivation
  exact ⟨types.map (renameTypeVars p), inferred.rename p, List.mem_map.mpr ⟨type, member, rfl⟩⟩

theorem TypeMatchRel.rename (p : Equiv.Perm String)
    {left right : Atom} {bindings output : Bindings}
    (derivation : TypeMatchRel left right bindings output) :
    TypeMatchRel (renameTypeVars p left) (renameTypeVars p right)
      (renameBindings p bindings) (renameBindings p output) := by
  cases derivation with
  | undefinedLeft => simpa only [Atom.undefinedType, atom_symbol] using TypeMatchRel.undefinedLeft _ _
  | atomLeft => simpa only [Atom.atomType, atom_symbol] using TypeMatchRel.atomLeft _ _
  | undefinedRight => simpa only [Atom.undefinedType, atom_symbol] using TypeMatchRel.undefinedRight _ _
  | atomRight => simpa only [Atom.atomType, atom_symbol] using TypeMatchRel.atomRight _ _
  | structural leftU leftA rightU rightA matched merged =>
      apply TypeMatchRel.structural
      · exact fun same => leftU ((atom_eq_symbol p _ _).mp same)
      · exact fun same => leftA ((atom_eq_symbol p _ _).mp same)
      · exact fun same => rightU ((atom_eq_symbol p _ _).mp same)
      · exact fun same => rightA ((atom_eq_symbol p _ _).mp same)
      · simpa only [Parameters.rename_equalityGroundedSemantic] using matched.rename p
      · simpa only [Parameters.rename_equalityGroundedSemantic] using merged.rename p

theorem TypeMatchRel.rename_iff (p : Equiv.Perm String) (left right : Atom)
    (bindings output : Bindings) :
    TypeMatchRel (renameTypeVars p left) (renameTypeVars p right)
        (renameBindings p bindings) (renameBindings p output) ↔
      TypeMatchRel left right bindings output := by
  constructor
  · intro derivation
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

@[simp] theorem renamed_badType (p : Equiv.Perm String) (atom expected actual : Atom) :
    renameTypeVars p (mkError atom (.badType expected actual)) =
      mkError (renameTypeVars p atom) (.badType (renameTypeVars p expected) (renameTypeVars p actual)) := by
  simp [mkError, ErrorCode.toAtom]

theorem TypeCastRel.rename (p : Equiv.Perm String)
    {context : Space} {atom expected : Atom} {bindings : Bindings} {returned : ResultPair}
    (derivation : TypeCastRel context atom expected bindings returned) :
    TypeCastRel (space p context) (renameTypeVars p atom) (renameTypeVars p expected)
      (renameBindings p bindings) (result p returned) := by
  cases derivation with
  | success inferred order noEarlier matched =>
      change TypesOfRel _ _ _ at inferred
      apply TypeCastRel.success (inferred.rename p)
      · simpa only [List.map_append, List.map_cons] using congrArg (List.map (renameTypeVars p)) order
      · rintro earlier member candidate matchEarlier
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply noEarlier original originalMember (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using matchEarlier.rename p.symm
      · exact matched.rename p
  | failure inferred actual noMatch =>
      change TypesOfRel _ _ _ at inferred
      simpa only [result, renamed_badType] using TypeCastRel.failure
        (inferred.rename p) (List.mem_map.mpr ⟨_, actual, rfl⟩)
        (by
          rintro candidateType member candidate matchCandidate
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          apply noMatch original originalMember (renameBindings p.symm candidate)
          simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using matchCandidate.rename p.symm)

theorem TypeCastRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (atom expected : Atom) (bindings : Bindings) (returned : ResultPair) :
    TypeCastRel (space p context) (renameTypeVars p atom) (renameTypeVars p expected)
      (renameBindings p bindings) (result p returned) ↔
    TypeCastRel context atom expected bindings returned := by
  constructor
  · intro derivation
    have reversed := derivation.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      result_inverse] using reversed
  · exact fun derivation => derivation.rename p

theorem ArgumentsApplicableRel.rename (p : Equiv.Perm String)
    {context : Space} {arguments expected : List Atom} {bindings output : Bindings}
    (derivation : ArgumentsApplicableRel context arguments expected bindings output) :
    ArgumentsApplicableRel (space p context) (arguments.map (renameTypeVars p))
      (expected.map (renameTypeVars p)) (renameBindings p bindings) (renameBindings p output) := by
  induction arguments generalizing expected bindings output with
  | nil =>
      cases derivation
      exact .nil _
  | cons argument arguments ih =>
      cases derivation with
      | cons typed matched rest =>
          change TypeOfRel context argument _ at typed
          exact .cons (typed.rename p) (matched.rename p) (ih rest)

theorem ApplicationSuccessRel.rename (p : Equiv.Perm String)
    {context : Space} {expression functionType expected : Atom} {bindings output : Bindings}
    (derivation : ApplicationSuccessRel context expression functionType expected bindings output) :
    ApplicationSuccessRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p functionType) (renameTypeVars p expected)
      (renameBindings p bindings) (renameBindings p output) := by
  cases derivation with
  | mk shape function arguments returned =>
      rename_i operator returnType actualArguments argumentTypes afterArguments
      refine .mk (operator := renameTypeVars p operator) ?_ ((functionType_iff p _ _ _).mpr function)
        (arguments.rename p) (returned.rename p)
      simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape

def ApplicabilityOutcome.rename (p : Equiv.Perm String) : ApplicabilityOutcome → ApplicabilityOutcome
  | .success output => .success (renameBindings p output)
  | .error atom => .error (renameTypeVars p atom)

@[simp] theorem ApplicabilityOutcome.rename_inverse (p : Equiv.Perm String)
    (outcome : ApplicabilityOutcome) :
    (outcome.rename p).rename p.symm = outcome := by
  cases outcome <;> simp [ApplicabilityOutcome.rename]

@[simp] theorem renamed_badArgType (p : Equiv.Perm String) (atom : Atom)
    (index : Nat) (expected actual : Atom) :
    renameTypeVars p (mkError atom (.badArgType index expected actual)) =
      mkError (renameTypeVars p atom)
        (.badArgType index (renameTypeVars p expected) (renameTypeVars p actual)) := by
  simp [mkError, ErrorCode.toAtom]

@[simp] theorem renamed_wrongArity (p : Equiv.Perm String) (atom : Atom) :
    renameTypeVars p (mkError atom .incorrectNumberOfArguments) =
      mkError (renameTypeVars p atom) .incorrectNumberOfArguments := by
  simp [mkError, ErrorCode.toAtom]

theorem ApplicabilityRel.rename (p : Equiv.Perm String)
    {context : Space} {expression functionType expected : Atom}
    {bindings : Bindings} {outcome : ApplicabilityOutcome}
    (derivation : ApplicabilityRel context expression functionType expected bindings outcome) :
    ApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p functionType) (renameTypeVars p expected)
      (renameBindings p bindings) (outcome.rename p) := by
  cases derivation with
  | success success => exact .success (success.rename p)
  | wrongArity shape function arity =>
      rename_i operator returnType actualArguments argumentTypes
      simp only [ApplicabilityOutcome.rename, renamed_wrongArity]
      refine .wrongArity (operator := renameTypeVars p operator)
        (arguments := actualArguments.map (renameTypeVars p))
        ?_ ((functionType_iff p _ _ _).mpr function) ?_
      · simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape
      · simpa only [List.length_map] using arity
  | badArgument shape function sameArity arguments typed noMatch noSuccess =>
      rename_i operator returnType argumentsBefore argumentsAfter typesBefore typesAfter
        badArgument expectedArgument actualType beforeBad
      change TypeOfRel context badArgument actualType at typed
      simp only [ApplicabilityOutcome.rename, renamed_badArgType]
      have first : (argumentsBefore.map (renameTypeVars p)).length = argumentsBefore.length :=
        List.length_map _
      rw [← first]
      refine .badArgument (operator := renameTypeVars p operator)
        (returnType := renameTypeVars p returnType)
        (argumentsAfter := argumentsAfter.map (renameTypeVars p))
        (typesAfter := typesAfter.map (renameTypeVars p))
        ?_ ?_ ?_ (arguments.rename p) (typed.rename p) ?_ ?_
      · simpa only [atom_expr, List.map_cons, List.map_append] using
          congrArg (renameTypeVars p) shape
      · simpa only [List.map_append, List.map_cons] using
          (functionType_iff p _ _ _).mpr function
      · simpa only [List.length_map] using sameArity
      · intro candidate matched
        apply noMatch (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
          matched.rename p.symm
      · intro candidate success
        apply noSuccess (renameBindings p.symm candidate)
        have reversed := success.rename p.symm
        rw [space_inverse] at reversed
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using reversed
  | badReturn shape function arguments noMatch noSuccess =>
      rename_i operator returnType actualArguments argumentTypes afterArguments
      simp only [ApplicabilityOutcome.rename, renamed_badType]
      refine .badReturn (operator := renameTypeVars p operator)
        ?_ ((functionType_iff p _ _ _).mpr function) (arguments.rename p) ?_ ?_
      · simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape
      · intro candidate matched
        apply noMatch (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
          matched.rename p.symm
      · intro candidate success
        apply noSuccess (renameBindings p.symm candidate)
        have reversed := success.rename p.symm
        rw [space_inverse] at reversed
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using reversed

end Mettapedia.Languages.MeTTa.HE.Spec.Type

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation Renaming

def SelectedTypeApplicabilityOutcome.rename (p : Equiv.Perm String) :
    SelectedTypeApplicabilityOutcome → SelectedTypeApplicabilityOutcome
  | .success selected bindings => .success (policy p selected) (renameBindings p bindings)
  | .error errors => .error (errors.map (renameTypeVars p))

@[simp] theorem SelectedTypeApplicabilityOutcome.rename_inverse
    (p : Equiv.Perm String) (outcome : SelectedTypeApplicabilityOutcome) :
    (outcome.rename p).rename p.symm = outcome := by
  cases outcome <;> simp [SelectedTypeApplicabilityOutcome.rename, Function.comp_def]

theorem PublishedCandidateApplicabilityRel.rename (p : Equiv.Perm String)
    {context : Space} {expression candidate expected : Atom} {bindings : Bindings}
    {outcome : SelectedTypeApplicabilityOutcome}
    (derivation : PublishedCandidateApplicabilityRel context expression candidate expected bindings outcome) :
    PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
      (outcome.rename p) := by
  cases derivation with
  | success function applicable =>
      exact .success ((functionType_iff p _ _ _).mpr function) (applicable.rename p)
  | error applicable =>
      exact .error (applicable.rename p)

theorem PublishedCandidateApplicabilityRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (expression candidate expected : Atom) (bindings : Bindings)
    (outcome : SelectedTypeApplicabilityOutcome) :
    PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
      (outcome.rename p) ↔
    PublishedCandidateApplicabilityRel context expression candidate expected bindings outcome := by
  constructor
  · intro derivation
    have reversed := derivation.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      SelectedTypeApplicabilityOutcome.rename_inverse] using reversed
  · exact fun derivation => derivation.rename p

theorem FunctionCandidateScanRel.rename (p : Equiv.Perm String)
    {context : Space} {expression expected : Atom} {bindings : Bindings}
    {candidates : List Atom} {selected : FunctionCandidateScanOutcome}
    (derivation : FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      context expression expected bindings candidates selected) :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel (space p context)
      (renameTypeVars p expression) (renameTypeVars p expected) (renameBindings p bindings)
      (candidates.map (renameTypeVars p)) (scanOutcome p selected) := by
  have notFunction {candidate : Atom}
      (original : ¬∃ args returned, FunctionTypeRel candidate args returned) :
      ¬∃ args returned, FunctionTypeRel (renameTypeVars p candidate) args returned := by
    rintro ⟨args, returned, function⟩
    apply original
    refine ⟨args.map (renameTypeVars p.symm), renameTypeVars p.symm returned, ?_⟩
    simpa only [renameTypeVars_perm_inverse] using
      (functionType_iff p.symm _ _ _).mpr function
  have notSuccess {candidate : Atom}
      (original : ∀ candidatePolicy candidateBindings,
        ¬PublishedCandidateApplicabilityRel context expression candidate expected bindings
          (.success candidatePolicy candidateBindings)) :
      ∀ candidatePolicy candidateBindings,
        ¬PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
          (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
          (.success candidatePolicy candidateBindings) := by
    intro candidatePolicy candidateBindings applicable
    apply original (policy p.symm candidatePolicy) (renameBindings p.symm candidateBindings)
    have reversed := applicable.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      SelectedTypeApplicabilityOutcome.rename] using reversed
  induction derivation with
  | nil => exact .nil
  | nonFunctionSuccess absent _tail ih =>
      exact .nonFunctionSuccess (notFunction absent) ih
  | nonFunctionExhausted absent _tail ih =>
      exact .nonFunctionExhausted (notFunction absent) ih
  | functionSuccess function applicable =>
      exact .functionSuccess ((functionType_iff p _ _ _).mpr function) (applicable.rename p)
  | functionFailureThenSuccess function absent failed nonempty _tail ih =>
      exact .functionFailureThenSuccess ((functionType_iff p _ _ _).mpr function)
        (notSuccess absent) (failed.rename p)
        (fun empty => nonempty (List.map_eq_nil_iff.mp empty)) ih
  | functionFailureExhausted function absent failed nonempty _tail ih =>
      simpa only [scanOutcome, List.map_append, List.map_cons] using
        FunctionCandidateScanRel.functionFailureExhausted
          ((functionType_iff p _ _ _).mpr function) (notSuccess absent) (failed.rename p)
          (fun empty => nonempty (List.map_eq_nil_iff.mp empty)) ih

theorem FunctionCandidateScanRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (expression expected : Atom) (bindings : Bindings)
    (candidates : List Atom) (selected : FunctionCandidateScanOutcome) :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel (space p context)
      (renameTypeVars p expression) (renameTypeVars p expected) (renameBindings p bindings)
      (candidates.map (renameTypeVars p)) (scanOutcome p selected) ↔
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      context expression expected bindings candidates selected := by
  constructor
  · intro derivation
    simpa only [rawTypeLookupRel, space_inverse, renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      atoms_inverse, scanOutcome_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

/-- The concrete published service is invariant under simultaneous renaming.
This is a theorem about its independent type judgments, not an assertion about
an arbitrary runtime type service or foreign diagnostic renderer. -/
theorem publishedTypeService_renaming (p : Equiv.Perm String) :
    typing p publishedTypeService = publishedTypeService := by
  unfold typing publishedTypeService
  congr 1
  · funext context atom types
    exact propext (TypesOfRel.rename_iff p.symm context atom types)
  · funext scope context atom expected bindings returned
    exact propext (TypeCastRel.rename_iff p.symm context atom expected bindings returned)
  · funext scope raw selected
    apply propext
    constructor
    · intro same
      exact (List.map_injective_iff.mpr (renameTypeVars_perm_injective p.symm)) same
    · exact congrArg (List.map (renameTypeVars p.symm))
  · funext scope context expression expected bindings candidates selected
    exact propext (FunctionCandidateScanRel.rename_iff p.symm context expression expected bindings candidates selected)

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-! ## Historical readout mode is closed under source execution -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type

/-- A completed native result preserves the historical readout mode through
its actual cast/update, including an unchanged binding record. -/
theorem CompletedNativeReturnRel.preserves_historical
    {space : Space} {typing : EvalTypeService} {protectedScope : List String} {value expected : Atom}
    {frame : BindingFrame} {result : FrameResult}
    (derived : CompletedNativeReturnRel space typing value expected frame result (protectedScope := protectedScope))
    (historical : frame.Historical) : result.2.Historical := by
  cases derived with
  | keep held => exact historical
  | cast required cast updated => exact updated.preserves_historical historical

mutual


theorem EvalAtomRawRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : EvalAtomRawRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .emptyOrError atom expectedType bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .typePass atom expectedType metaType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .cast atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .interpretSuccess atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child4 := InterpretExpressionRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .interpretError atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child4 := InterpretExpressionRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretExpressionRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretExpressionRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .functionPath expression expectedType operator arguments rawTypes types policy callType bindings applicableBindings interpreted callResult h0 h1 instanceTypes h2 h3 h4 h5 h6 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := InterpretFunctionRel.preserves_historical h5 (by solve_by_elim)
    have child6 := CallRel.preserves_historical h6 (by solve_by_elim)
    solve_by_elim
  | .tuplePath expression expectedType operator arguments rawTypes types errors bindings tupleResult callResult h0 h1 instanceTypes h2 h3 h4 => by
    intro historicalFrame
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    have child4 := CallRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .functionError expression expectedType operator errorAtom arguments rawTypes types errors tupleEligible bindings h0 h1 instanceTypes h2 h3 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem InterpretFunctionRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom functionType expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretFunctionRel space dispatch live atom functionType expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .headError expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .tailError expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult tailResult h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    have child4 := InterpretArgsRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .success expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult tailResult h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    have child4 := InterpretArgsRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretArgsRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atoms expected : List Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretArgsRel space dispatch live atoms expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .nil bindings => by
    intro historicalFrame
    solve_by_elim
  | .headChangedError argument arguments expectedType expectedTypes bindings headResult h0 h1 h2 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .tailError argument arguments expectedType expectedTypes bindings headResult tailResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    have child2 := InterpretArgsRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .success argument arguments expectedType expectedTypes bindings headResult tailResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    have child2 := InterpretArgsRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretTupleRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretTupleRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .nil bindings => by
    intro historicalFrame
    solve_by_elim
  | .singleton atom bindings result h0 h1 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .singletonError atom bindings result h0 h1 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .headError head tail bindings headResult h0 h1 h2 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .tailError head tail bindings headResult tailResult h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
  | .success head tail bindings headResult tailResult h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem CallReturnRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {original expected atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : CallReturnRel space dispatch live original expected atom bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .notReducible original expectedType bindings => by
    intro historicalFrame
    solve_by_elim
  | .stopped original expectedType value bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .evaluate original expectedType value bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem CallRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : CallRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .errorPassthrough atom expectedType bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .embedded atom expectedType bindings raw result h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have rawHistorical := Minimal.CoreInvocationRel.preserves_historical h3 historicalFrame
    exact CallReturnRel.preserves_historical h4 rawHistorical
  | .groundedSuccess atom expectedType operator arguments bindings nativeResults nativeResult finalResult merged emitted completed h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    intro historicalFrame
    have historical7 := h7.preserves_historical (by solve_by_elim)
    have child9 := Minimal.CoreInvocationResultRel.preserves_historical h9 (by solve_by_elim)
    have child10 := CallReturnRel.preserves_historical h10 (by solve_by_elim)
    solve_by_elim
  | .groundedCompletedSuccess atom expectedType operator arguments bindings nativeResults nativeResult finalResult merged emitted h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    intro historicalFrame
    have historical7 := h7.preserves_historical (by solve_by_elim)
    have child9 := CompletedNativeReturnRel.preserves_historical h9 (by solve_by_elim)
    solve_by_elim
  | .groundedRuntimeError atom expectedType operator arguments bindings message h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedNoReduce atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedIncorrectArgument atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedEmpty atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .equation atom expectedType emitted materialized bindings merged finalResult completed h0 h1 h2 h3 h4 h5 h6 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := Minimal.CoreInvocationResultRel.preserves_historical h5 (by solve_by_elim)
    have child6 := CallReturnRel.preserves_historical h6 (by solve_by_elim)
    solve_by_elim
  | .noEquation atom expectedType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .allEquationsFiltered atom expectedType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreStepRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreStepRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .eval space atom materialized bindings result h0 h1 => by
    intro historicalFrame
    have child1 := Minimal.CoreInvocationRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .evalc space context atom materialized bindings result services enumeration h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreInvocationRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .chain space atom name template bindings result materialized h0 h1 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .unifySuccess space target pattern thenBranch elseBranch result bindings output h0 h1 h2 => by
    intro historicalFrame
    exact h1.preserves_historical historicalFrame
  | .unifyNoMatch space target pattern thenBranch elseBranch bindings missing => by
    intro historicalFrame
    exact historicalFrame
  | .unifyBadArity space tail bindings wrong => by
    intro historicalFrame
    exact historicalFrame
  | .consAtom space head tail bindings => by
    intro historicalFrame
    solve_by_elim
  | .deconsAtom space head tail bindings => by
    intro historicalFrame
    solve_by_elim
  | .collapseBind space atom bindings results services enumeration h0 _h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .superposeBind space results stored bindings merged services enumeration h0 _h1 h2 h3 h4 => by
    intro historicalFrame
    have historical4 := h4.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .functionReturn space body returned bindings output h0 h1 => by
    intro historicalFrame
    have child1 := Minimal.CoreFunctionBodyRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .functionNoReturn space body result bindings output h0 h1 h2 => by
    intro historicalFrame
    have child1 := Minimal.CoreFunctionBodyRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .metta space context atom expectedType bindings result services enumeration h0 h1 h2 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .mettaAtom space context atom bindings services enumeration h0 => by
    intro historicalFrame
    solve_by_elim
  | .mettaError space context atom expectedType bindings services enumeration h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .contextSpace space bindings services enumeration h0 => by
    intro historicalFrame
    solve_by_elim
  | .callNative space name function arguments bindings result merged services enumeration h0 h1 h2 h3 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreInvocationRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .embedded space atom bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreRunRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .grounded space operator arguments bindings merged results nativeResult result emitted h0 h1 h2 h3 h4 h5 h6 h7 h8 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    have child8 := Minimal.CoreInvocationResultRel.preserves_historical h8 (by solve_by_elim)
    solve_by_elim
  | .completedGrounded space operator arguments bindings merged results nativeResult emitted h0 h1 h2 h3 h4 h5 h6 h7 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .groundedEmpty space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedError space operator arguments bindings message h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedNoReduce space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedIncorrectArgument space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .equation space atom emitted materialized bindings merged result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := Minimal.CoreInvocationResultRel.preserves_historical h5 (by solve_by_elim)
    solve_by_elim
  | .noEquation space atom bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .allEquationsFiltered space atom bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreInvocationResultRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationResultRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .raw space atom bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .function space body bindings result h0 => by
    intro historicalFrame
    have child0 := Minimal.CoreStepRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreRunRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreRunRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .data space atom bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .instruction space atom bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreStepRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .chain space atom bindings selected result h0 h1 h2 => by
    intro historicalFrame
    have child1 := Minimal.CoreStepRel.preserves_historical h1 (by solve_by_elim)
    have child2 := Minimal.CoreRunRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreFunctionBodyRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreFunctionBodyRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .terminal space atom bindings raw materialized h0 h1 h2 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .resume space atom bindings raw materialized result h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    have child3 := Minimal.CoreFunctionBodyRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
termination_by structural derived

end

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.BindingFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open Spec.Type Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory Spec.Type.Presentation.BindingTheory.CurrentStore

/-- Filling an actual open slot reconstructs the independently certified source
frame. The same source materialization relation reads the full old pending tuple
under the renewed table; it does not retain a stale table after a binding write. -/
theorem selected_open_write_renewal {globals : List String}
    {image next : ImageOf ContextualOperand} {raw : RowOf ContextualOperand}
    {payload : ContextualOperand} {atom : Atom} {operands : List ContextualOperand}
    {snapshot : List CurrentStore.Row} {qualified : List Atom} {rank : String → Nat}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (ranked : Ranked rank (assignments snapshot))
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (below : ∀ name ∈ TypeSubst.typeVars atom, rank name < rank (referenceName raw.reference)) :
    let updated := snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))
    ∃ certificate : ReadoutCertificate ⟨assignments updated, []⟩ (normalize (assignments updated)),
      prepareScoped? globals next operands = some (updated, qualified) ∧
      Update .renew
        (selected ⟨assignments snapshot, []⟩ (normalize (assignments snapshot))
          (prepareScoped?_certified prepared ranked))
        (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate) ∧
      ∀ pending : List Atom,
        List.Forall₂
          (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate).Materialization
          (pending.map (normalize (assignments snapshot)).apply)
          (pending.map (normalize (assignments updated)).apply) := by
  dsimp only
  have success := (prepare?_components (prepareScoped?_success prepared)).1
  let certificate := open_write_certified written qualifiedPayload success ranked read unbound below
  refine ⟨certificate, prepareScoped?_write written qualifiedPayload payloadScope prepared,
    Update.selected _ certificate, ?_⟩
  intro pending
  induction pending with
  | nil => exact .nil
  | cons term rest ih =>
    apply List.Forall₂.cons ?_ ih
    change (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply term = _
    exact ((prepareScoped?_certified prepared ranked).absorbs certificate
      (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
      term).symm

/-- The source renewal is earned from the two actual loop checks. No fixed
ordering of variable names, slots, or stored equations is prescribed. -/
theorem selected_open_write_renewal_of_noLoop {globals : List String}
    {image next : ImageOf ContextualOperand} {raw : RowOf ContextualOperand}
    {payload : ContextualOperand} {atom : Atom} {operands : List ContextualOperand}
    {snapshot : List CurrentStore.Row} {qualified : List Atom}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (beforeChecked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false)
    (afterChecked : Bindings.hasLoop
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))), []⟩ = false)
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none) :
    let updated := snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))
    ∃ certificate : ReadoutCertificate ⟨assignments updated, []⟩ (normalize (assignments updated)),
      prepareScoped? globals next operands = some (updated, qualified) ∧
      Update .renew
        (selected ⟨assignments snapshot, []⟩ (normalize (assignments snapshot))
          (prepareScoped?_certified_of_noLoop prepared beforeChecked))
        (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate) ∧
      ∀ pending : List Atom,
        List.Forall₂
          (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate).Materialization
          (pending.map (normalize (assignments snapshot)).apply)
          (pending.map (normalize (assignments updated)).apply) := by
  dsimp only
  have success := (prepare?_components (prepareScoped?_success prepared)).1
  let certificate := write_certified_of_noLoop written qualifiedPayload success afterChecked
  refine ⟨certificate, prepareScoped?_write written qualifiedPayload payloadScope prepared,
    Update.selected _ certificate, ?_⟩
  intro pending
  induction pending with
  | nil => exact .nil
  | cons term rest ih =>
    apply List.Forall₂.cons ?_ ih
    change (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply term = _
    exact ((prepareScoped?_certified_of_noLoop prepared beforeChecked).absorbs certificate
      (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
      term).symm

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.BindingFrame

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteSourceControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.BindingFrame
open WriteControls

def beforeFrame : BindingFrame :=
  selected ⟨assignments beforeRows, []⟩ (normalize (assignments beforeRows))
    (prepareScoped?_certified before_prepared before_ranked)

def afterFrame : BindingFrame :=
  selected ⟨assignments afterRows, []⟩ (normalize (assignments afterRows)) after_certificate

theorem actual_open_write_renews_source_frame : Update .renew beforeFrame afterFrame := by
  obtain ⟨_certificate, _prepared, renewed, _pending⟩ := selected_open_write_renewal
    actual_write payload_qualified payload_scoped before_prepared before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars])
  exact renewed

theorem actual_pending_source_materializations :
    List.Forall₂ afterFrame.Materialization
      (qualified.map (normalize (assignments beforeRows)).apply)
      (qualified.map (normalize (assignments afterRows)).apply) := by
  obtain ⟨_certificate, _prepared, _renewed, pending⟩ := selected_open_write_renewal
    actual_write payload_qualified payload_scoped before_prepared before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars])
  exact pending qualified

theorem changed_binding_is_not_pure_frame_retention : ¬ Update .retain beforeFrame afterFrame := by
  intro retained
  have same := congrArg (fun frame : BindingFrame => frame.bindings.assignments.length)
    retained.retained_eq
  change (assignments beforeRows).length = (assignments afterRows).length at same
  rw [before_assignments, after_assignments] at same
  cases same

theorem actual_before_loop_check : Bindings.hasLoop ⟨assignments beforeRows, []⟩ = false := by
  rw [before_assignments]
  decide +kernel

theorem actual_after_loop_check : Bindings.hasLoop ⟨assignments afterRows, []⟩ = false := by
  rw [after_assignments]
  decide +kernel

theorem actual_loop_checks_renew_source_frame : Update .renew beforeFrame afterFrame := by
  obtain ⟨_certificate, _prepared, renewed, _pending⟩ := selected_open_write_renewal_of_noLoop
    (raw := openRow) (atom := .symbol "A") (snapshot := beforeRows) (qualified := qualified)
    actual_write payload_qualified payload_scoped before_prepared actual_before_loop_check
    actual_after_loop_check target_open.1 target_open.2
  exact renewed

theorem actual_loop_checks_preserve_pending_materializations :
    List.Forall₂ afterFrame.Materialization
      (qualified.map (normalize (assignments beforeRows)).apply)
      (qualified.map (normalize (assignments afterRows)).apply) := by
  obtain ⟨_certificate, _prepared, _renewed, pending⟩ := selected_open_write_renewal_of_noLoop
    (raw := openRow) (atom := .symbol "A") (snapshot := beforeRows) (qualified := qualified)
    actual_write payload_qualified payload_scoped before_prepared actual_before_loop_check
    actual_after_loop_check target_open.1 target_open.2
  exact pending qualified

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteSourceControls
