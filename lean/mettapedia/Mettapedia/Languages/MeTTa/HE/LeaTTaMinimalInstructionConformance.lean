import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlReturn
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlUnify
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingMaterialization
import Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# LeaTTa minimal-instruction carrier and completion conformance

The executable-independent minimal semantics represents a collapsed binding
set by an abstract grounded value.  LeaTTa represents the same object by the
typed `Ground.bindings` carrier.  This module relates those two representations
without choosing the runtime's private spelling in the specification.
Raw and function-result completion reuse the actual interpreter's saved
continuations. Compositional source derivations construct retained native
paths for unification, chains, nested functions and function-body resumption.
Reached binding frames pass between children; selected materializations are
closed, and other operations have explicit admission boundaries.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalInstructionConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Spec.Eval.Minimal
open LeaTTaMinimalControlExecution

/-- Atom correspondence extended by one opaque binding-payload case.  Ordinary
grounded values use the established structural translation; a service payload
is related to the typed runtime carrier through binding-set equivalence. -/
inductive AtomRuntimeRel (services : Services) : Atom → Metta.Atom → Prop where
  | symbol (name : String) :
      AtomRuntimeRel services (.symbol name) (.sym name)
  | variable (name : String) :
      AtomRuntimeRel services (.var name) (.var name)
  | grounded (value : GroundedValue)
      (notPayload : ∀ bindings, value ≠ services.bindingPayload bindings) :
      AtomRuntimeRel services (.grounded value)
        (.gnd (encodeModelGround value))
  | bindingPayload (bindings : Bindings) (runtimeBindings : Metta.Bindings) :
      LeaBindingRelEquiv bindings runtimeBindings →
      AtomRuntimeRel services
        (.grounded (services.bindingPayload bindings))
        (.gnd (.bindings (Metta.Bindings.store runtimeBindings)))
  | expression (atoms : List Atom) (runtimeAtoms : List Metta.Atom) :
      List.Forall₂ (AtomRuntimeRel services) atoms runtimeAtoms →
      AtomRuntimeRel services (.expression atoms) (.expr runtimeAtoms)

/-- A semantic result and a runtime result agree on both the result atom and
the complete binding set. -/
structure ResultRuntimeRel (services : Services)
    (result : ResultPair) (runtimeResult : Metta.Atom × Metta.Bindings) : Prop where
  atom : AtomRuntimeRel services result.1 runtimeResult.1
  bindings : LeaBindingRelEquiv result.2 runtimeResult.2

/-- Runtime encoding used by repaired `collapse-bind`. -/
def encodeRuntimeResult
    (result : Metta.Atom × Metta.Bindings) : Metta.Atom :=
  .expr [result.1, .gnd (.bindings (Metta.Bindings.store result.2))]

/-- One related result pair has related opaque encodings. -/
theorem encodeResult_runtime {services : Services}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (related : ResultRuntimeRel services result runtimeResult) :
    AtomRuntimeRel services (encodeResult services result)
      (encodeRuntimeResult runtimeResult) := by
  apply AtomRuntimeRel.expression
  exact .cons related.atom
    (.cons (.bindingPayload result.2 runtimeResult.2 related.bindings) .nil)

/-- Ordered pointwise result correspondence lifts through the exact
collapse encoding without losing order or multiplicity. -/
theorem encodeResults_runtime {services : Services}
    {results : ResultSet}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    (related : List.Forall₂ (ResultRuntimeRel services) results runtimeResults) :
    AtomRuntimeRel services (encodeResults services results)
      (.expr (runtimeResults.map encodeRuntimeResult)) := by
  apply AtomRuntimeRel.expression
  induction related with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (encodeResult_runtime head) inductionHypothesis

/-- The concrete runtime payload restores the exact runtime binding list
before `superpose-bind` performs its continuation merge. -/
theorem runtime_binding_payload_roundtrip (bindings : Metta.Bindings) :
    Metta.Bindings.restore (Metta.Bindings.store bindings) = bindings :=
  Metta.Bindings.restore_store bindings

/-- A lawful abstract context handle uses the ordinary grounded-value lane:
unlike a collapsed binding set, it requires no runtime-specific constructor. -/
theorem contextPayload_runtime {services : Services}
    (laws : ServiceLaws services) (space : Space) :
    AtomRuntimeRel services
      (.grounded (services.contextPayload space))
      (.gnd (encodeModelGround (services.contextPayload space))) :=
  .grounded _ (laws.contextPayload_ne_bindingPayload space)

/-! ## Positive and negative boundary canaries -/

/-- Positive: empty binding sets are related and therefore have related opaque
payloads. -/
example (services : Services) :
    AtomRuntimeRel services
      (.grounded (services.bindingPayload Bindings.empty))
      (.gnd (.bindings (Metta.Bindings.store []))) :=
  .bindingPayload Bindings.empty [] LeaBindingRelEquiv.empty

/-- Negative: a binding payload cannot satisfy the separation premise of the
ordinary-grounded constructor. -/
theorem binding_payload_is_not_ordinary {services : Services}
    (bindings : Bindings) :
    ¬(∀ candidate,
      services.bindingPayload bindings ≠ services.bindingPayload candidate) := by
  intro separated
  exact separated bindings rfl

/-! ## Emitted raw values and function completion -/

/-- An emitted atom outside the runtime's function-head lane is already a
completed raw result on both sides. Callable-looking ordinary data is not
invoked by this boundary. Native bindings and the saved caller are unchanged. -/
theorem raw_completion_of_not_function_head {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (value : Atom) (bindings : Bindings)
    (previous : Metta.Minimal.Stack) (native : Metta.Bindings)
    (raw : ∀ tail, encodeModelAtom value ≠ .expr (.sym "function" :: tail)) :
    CoreInvocationResultRel space dispatch live value bindings (value, bindings) (typing := typing) (caller := caller) ∧
      Metta.Minimal.evalResult previous (encodeModelAtom value) native =
        Metta.Minimal.finItem previous (encodeModelAtom value) native := by
  constructor
  · apply CoreInvocationResultRel.raw
    rintro ⟨body, rfl⟩
    exact raw [encodeModelAtom body] (by simp only [encodeModelAtom, encodeModelAtoms])
  · exact evalResult_raw_of_not_function_head previous _ native raw

/-- Completion of an arbitrary returning function body composes its
independent body derivation with an actual finite interpreter prefix. The
prefix remains an explicit local execution input: this theorem does not
assume or claim a whole instruction-interpreter correspondence.

The terminal operand may differ structurally from the source return value.
Its observation law and the paired output binding invariant justify native
instantiation at the existing return handler, without replacing the source
operand by the instantiated native result. Queue/results use the actual
driver's final-versus-pending classification, including its Empty policy. -/
theorem function_completion_of_body_prefix {caller : Option Atom}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : Spec.Eval.EvalTypeService} {body returned : Atom}
    {bindings output : Bindings} {environment : Metta.Minimal.MinEnv}
    {previous : Metta.Minimal.Stack} {incoming native : Metta.Bindings}
    {initial final : Metta.Minimal.St} {initialFuel fuel : Nat}
    {nativeOperand : Metta.Atom} {returnScope : List Metta.VarName}
    {retained : List Metta.Minimal.Item}
    (expressionBody : ∃ atoms, body = .expression atoms)
    (source : CoreFunctionBodyRel space dispatch (.expression [.symbol "function", body] :: live)
      body bindings (.expression [.symbol "return", returned], output) (typing := typing)
      (caller := some (.expression [.symbol "function", body])))
    (paired : ScopedEquationQuery.BindingInvariant output native)
    (operand : ∀ valuation, HEBindingSatisfied valuation output →
      applyClassSolution valuation nativeOperand =
        applyClassSolution valuation (encodeModelAtom returned))
    (path : PendingSteps environment
      (initialFuel, initial,
        [Metta.Minimal.evalResult previous
          (encodeModelAtom (.expression [.symbol "function", body])) incoming])
      (fuel + 1, final,
        ⟨{ atom := .expr [.sym "return", nativeOperand], vars := returnScope, fin := true } ::
          { atom := encodeModelAtom (.expression [.symbol "function", body]),
            ret := .function, vars := Metta.Minimal.varsCopy previous } :: previous, native⟩ :: retained))
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, output) (typing := typing) (caller := caller) ∧
    (∀ valuation, HEBindingSatisfied valuation output →
      applyClassSolution valuation (Metta.instantiate native nativeOperand) =
        applyClassSolution valuation (encodeModelAtom returned)) ∧
    Metta.Minimal.interpretFuel environment initialFuel initial
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) incoming :: queued) done =
      Metta.Minimal.interpretFuel environment fuel final
        (([Metta.Minimal.finItem previous (Metta.instantiate native nativeOperand) native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ retained ++ queued)
        ((([Metta.Minimal.finItem previous (Metta.instantiate native nativeOperand) native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  refine ⟨.function space body bindings (returned, output)
    (.functionReturn space body returned bindings output expressionBody source), ?_, ?_⟩
  · intro valuation satisfied
    exact (instantiate_semantically_inert
      ((paired.semantic.solutionTheory valuation).mp satisfied) nativeOperand).trans
      (operand valuation satisfied)
  · exact function_return_after_pending_prefix path queued done

/-! ## Captured caller at the terminal function boundary -/

private theorem caller_target_encoding (caller : Option Atom)
    (previous : Metta.Minimal.Stack) (terminal : Atom)
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom) :
    (match previous with | frame :: _ => frame.atom | [] => encodeModelAtom terminal) =
      encodeModelAtom (caller.getD terminal) := by
  calc
    _ = (previous.head?.map (fun frame => frame.atom)).getD (encodeModelAtom terminal) := by
      cases previous <;> rfl
    _ = _ := by rw [captured]; cases caller <;> rfl

/-- The independent terminal observer uses the actual captured caller, not
the function's own expression. The entry is explicitly materialized. The
native noninstruction guard is local: the runtime's extension surface is not
silently identified with the independent core's instruction classifier. -/
theorem function_terminal_handler_conformance
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (previous : Metta.Minimal.Stack) (scope : List String) (parent : Metta.Atom)
    (native : Metta.Bindings) (caller : Option Atom) (terminal : Atom) (operand : Metta.Atom)
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom)
    (materialized : Metta.instantiate native operand = encodeModelAtom terminal)
    (nativeTerminal : Metta.Minimal.isEmbeddedOp (encodeModelAtom terminal) = false) :
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        ({ atom := parent, ret := .function, vars := scope } :: previous)
        operand native) =
      ([Metta.Minimal.finItem previous (encodeModelAtom (functionTerminalResult caller terminal))
        native], state) := by
  by_cases returning : ∃ value, terminal = .expression [.symbol "return", value]
  · obtain ⟨value, rfl⟩ := returning
    simp only [Metta.Minimal.interpretStack1, Metta.Minimal.finItem, ↓reduceIte,
      materialized, functionTerminalResult_return, encodeModelAtom, encodeModelAtoms]
  · have missing : ∀ value, terminal ≠ .expression [.symbol "return", value] := by
      intro value same
      exact returning ⟨value, same⟩
    have nativeMissing : ∀ value,
        encodeModelAtom terminal ≠ .expr [.sym "return", value] := by
      intro value same
      apply missing (Spec.Match.SolutionTheory.decodeModelAtom value)
      have decoded := congrArg Spec.Match.SolutionTheory.decodeModelAtom same
      simpa only [Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom,
        Spec.Match.SolutionTheory.decodeModelAtom, Spec.Match.SolutionTheory.decodeModelAtoms] using decoded
    rw [functionTerminalResult_noReturn caller terminal missing]
    have target := caller_target_encoding caller previous terminal captured
    simp only [Metta.Minimal.interpretStack1, Metta.Minimal.finItem, ↓reduceIte, materialized,
      nativeTerminal, Bool.false_eq_true, ↓reduceIte]
    cases previous <;>
      exact congrArg (fun subject =>
        ([Metta.Minimal.finItem _ (Metta.Minimal.errAtom subject "NoReturn") native], state))
        target

/-- An independent materialized operand and the actual handler agree up to
residual-variable renaming. The caller stays literal on both sides; an open
binding presentation need not choose the runtime's private representatives. -/
theorem function_materialized_terminal_handler_conformance
    {bindings : Bindings} {native : Metta.Bindings} {raw terminal : Atom}
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (materialization :
      Spec.Type.Presentation.BindingTheory.BindingMaterializationRel bindings raw terminal)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (previous : Metta.Minimal.Stack) (scope : List String) (parent : Metta.Atom)
    (caller : Option Atom)
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom)
    (nativeTerminal : Metta.Minimal.isEmbeddedOp
      (Metta.instantiate native (encodeModelAtom raw)) = false) :
    ∃ observed : Atom,
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
        (functionTerminalResult caller terminal) observed ∧
      Metta.Minimal.interpretStack1 environment fuel state
        (Metta.Minimal.finItem
          ({ atom := parent, ret := .function, vars := scope } :: previous)
          (encodeModelAtom raw) native) =
        ([Metta.Minimal.finItem previous (encodeModelAtom observed) native], state) := by
  let actual := Metta.instantiate native (encodeModelAtom raw)
  let decoded := Spec.Match.SolutionTheory.decodeModelAtom actual
  have image : LeaAtomHEImage actual := instantiate_heImage paired.image _ ⟨raw, rfl⟩
  have encoded : encodeModelAtom decoded = actual :=
    LeaTTaTypeConformance.encodeModelAtom_decodeModelAtom_of_heImage image
  refine ⟨functionTerminalResult caller decoded, ?_, ?_⟩
  · exact functionTerminalResult_of_observedTypeAlpha caller
      (QueryBindingProjection.binding_materialization_alpha paired.semantic materialization)
  · exact function_terminal_handler_conformance environment state fuel previous scope parent
      native caller decoded (encodeModelAtom raw) captured encoded.symm
      (by simpa only [encoded] using nativeTerminal)

/-- At an outermost handler no caller is invented: the terminal itself is
the diagnostic subject. Bindings and all native state remain unchanged. -/
theorem function_outermost_noReturn_conformance
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (scope : List String) (parent : Metta.Atom) (native : Metta.Bindings) (terminal : Atom)
    (missing : ∀ value, terminal ≠ .expression [.symbol "return", value])
    (materialized : Metta.instantiate native (encodeModelAtom terminal) = encodeModelAtom terminal)
    (nativeTerminal : Metta.Minimal.isEmbeddedOp (encodeModelAtom terminal) = false) :
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem [{ atom := parent, ret := .function, vars := scope }]
        (encodeModelAtom terminal) native) =
      ([Metta.Minimal.finItem [] (encodeModelAtom (Atom.error terminal (.symbol "NoReturn")))
        native], state) := by
  simpa only [functionTerminalResult_noReturn none terminal missing, Option.getD_none] using
    function_terminal_handler_conformance environment state fuel [] scope parent native none
      terminal (encodeModelAtom terminal) rfl materialized nativeTerminal

/-- A finite actual body prefix composes with the contextual observer and
the real publication split. Saved alternatives, queued work and prior
results survive a fault just as they survive a successful return. -/
theorem function_terminal_after_pending_prefix
    {environment : Metta.Minimal.MinEnv} {before : PendingState}
    {state : Metta.Minimal.St} {fuel : Nat} {native : Metta.Bindings}
    {parent operand : Metta.Atom} {scope returnScope : List String}
    {previous : Metta.Minimal.Stack} {retained : List Metta.Minimal.Item}
    (caller : Option Atom) (terminal : Atom)
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom)
    (materialized : Metta.instantiate native operand = encodeModelAtom terminal)
    (nativeTerminal : Metta.Minimal.isEmbeddedOp (encodeModelAtom terminal) = false)
    (path : PendingSteps environment before
      (fuel + 1, state,
        ⟨{ atom := operand, vars := returnScope, fin := true } ::
          { atom := parent, ret := .function, vars := scope } :: previous, native⟩ :: retained))
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let completed := Metta.Minimal.finItem previous
      (encodeModelAtom (functionTerminalResult caller terminal)) native
    Metta.Minimal.interpretFuel environment before.1 before.2.1
      (before.2.2 ++ queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([completed].filter (fun result => !Metta.Minimal.isFinal result)) ++ retained ++ queued)
        ((([completed].filter Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro completed
  rw [pendingSteps_replay path queued done]
  simp only [List.cons_append]
  rw [finished_frame_scope_irrelevant environment state native operand returnScope
    { atom := parent, ret := .function, vars := scope } previous (fuel + 1)
    (retained ++ queued) done]
  simpa only [List.append_assoc, completed] using
    FuelConvergenceInterpreter.interpretFuel_succ_of environment fuel state state _
      (retained ++ queued) _ done
      (function_terminal_handler_conformance environment state fuel previous scope parent native
        caller terminal operand captured materialized nativeTerminal)

/-- Independent contextual function completion composes with the actual
terminal prefix for either return or fault. The body derivation and native
prefix are separate inputs: this is the composition law used by a body
correspondence proof, not an assumption that every body already has one. -/
theorem function_terminal_completion_of_body_prefix
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : Spec.Eval.EvalTypeService} {body terminal : Atom}
    {bindings output : Bindings} {caller : Option Atom}
    {environment : Metta.Minimal.MinEnv} {before : PendingState}
    {state : Metta.Minimal.St} {fuel : Nat} {native : Metta.Bindings}
    {operand : Metta.Atom} {scope returnScope : List String}
    {previous : Metta.Minimal.Stack} {retained : List Metta.Minimal.Item}
    (expression : ∃ atoms, body = .expression atoms)
    (source : CoreFunctionBodyRel space dispatch (.expression [.symbol "function", body] :: live)
      body bindings (terminal, output) (typing := typing)
      (caller := some (.expression [.symbol "function", body])))
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom)
    (materialized : Metta.instantiate native operand = encodeModelAtom terminal)
    (nativeTerminal : Metta.Minimal.isEmbeddedOp (encodeModelAtom terminal) = false)
    (path : PendingSteps environment before
      (fuel + 1, state,
        ⟨{ atom := operand, vars := returnScope, fin := true } ::
          { atom := encodeModelAtom (.expression [.symbol "function", body]),
            ret := .function, vars := scope } :: previous, native⟩ :: retained))
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (functionTerminalResult caller terminal, output)
      (typing := typing) (caller := caller) ∧
    (let completed := Metta.Minimal.finItem previous
        (encodeModelAtom (functionTerminalResult caller terminal)) native;
      Metta.Minimal.interpretFuel environment before.1 before.2.1
        (before.2.2 ++ queued) done =
        Metta.Minimal.interpretFuel environment fuel state
          (([completed].filter (fun result => !Metta.Minimal.isFinal result)) ++ retained ++ queued)
          ((([completed].filter Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done)) := by
  constructor
  · exact .function space body bindings _
      (function_step_body_terminal_iff.mpr ⟨expression, terminal, output, source, rfl⟩)
  · exact function_terminal_after_pending_prefix caller terminal captured materialized
      nativeTerminal path queued done

/-- An aliased return marker is classified after materialization. Its open
returned operand survives unchanged and the saved caller is retained. -/
theorem aliased_return_marker_handler
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (scope : List String) (parent : Metta.Atom) :
    let native : Metta.Bindings := [.val "pending" (.expr [.sym "return", .var "free"])]
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        [{ atom := parent, ret := .function, vars := scope }, { atom := .sym "caller" }]
        (.var "pending") native) =
      ([Metta.Minimal.finItem [{ atom := .sym "caller" }] (.var "free") native], state) := by
  intro native
  have materialized : Metta.instantiate native (.var "pending") =
      encodeModelAtom (.expression [.symbol "return", .var "free"]) := by
    exact Metta.instantiate_singleton_val_var_of_not_mem "pending"
      (.expr [.sym "return", .var "free"]) (by simp [Metta.Atom.vars])
  simpa only [functionTerminalResult_return, encodeModelAtom] using
    function_terminal_handler_conformance environment state fuel [{ atom := .sym "caller" }]
      scope parent native (some (.symbol "caller"))
      (.expression [.symbol "return", .var "free"]) (.var "pending") rfl materialized (by rfl)

/-- The terminal is materialized, but the diagnostic's captured caller is
the raw saved frame. Substituting that caller would erase an observable
distinction, even when it uses the very same bound variable. -/
theorem captured_caller_keeps_raw_fault_subject
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (scope : List String) (parent : Metta.Atom) :
    let native : Metta.Bindings := [.val "pending" (.expr [.sym "terminal"])]
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        [{ atom := parent, ret := .function, vars := scope }, { atom := .var "pending" }]
        (.var "pending") native) =
      ([Metta.Minimal.finItem [{ atom := .var "pending" }]
        (Metta.Minimal.errAtom (.var "pending") "NoReturn") native], state) ∧
    Metta.Minimal.errAtom (.var "pending") "NoReturn" ≠
      Metta.Minimal.errAtom (.expr [.sym "terminal"]) "NoReturn" := by
  intro native
  have materialized : Metta.instantiate native (.var "pending") =
      encodeModelAtom (.expression [.symbol "terminal"]) := by
    exact Metta.instantiate_singleton_val_var_of_not_mem "pending" (.expr [.sym "terminal"])
      (by simp [Metta.Atom.vars])
  constructor
  · simpa [functionTerminalResult, Atom.error,
      encodeModelAtom, encodeModelAtoms, Metta.Minimal.errAtom] using
      function_terminal_handler_conformance environment state fuel [{ atom := .var "pending" }]
        scope parent native (some (.var "pending")) (.expression [.symbol "terminal"])
        (.var "pending") rfl materialized (by rfl)
  · simp [Metta.Minimal.errAtom]

/-- The independent HE core and LeaTTa's extended instruction surface are
not the same classifier. A body proof must supply the applicable profile
guard rather than transferring it from syntax alone. -/
theorem embedded_instruction_surfaces_differ :
    embeddedInstruction (.expression [.symbol "call-native"]) = true ∧
    Metta.Minimal.isEmbeddedOp (encodeModelAtom (.expression [.symbol "call-native"])) = false ∧
    embeddedInstruction (.expression [.symbol "get-type"]) = false ∧
    Metta.Minimal.isEmbeddedOp (encodeModelAtom (.expression [.symbol "get-type"])) = true := by
  decide +kernel

/-! ## Primitive instructions at materialized boundaries -/

open _root_.Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open _root_.Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha (ObservedTypeAlphaRel)
open _root_.Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

/-- Every independent minimal unify step constructs the actual interpreter
step with its selected native frame. Success and fallback have the same
complete binding theory and emitted observation as the independent result;
neither raw merge orientation nor private binding spelling is equated. -/
theorem unify_step_complete {caller : Option Atom}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : Spec.Eval.EvalTypeService} {target pattern yes no emitted : Atom}
    {bindings output : Bindings} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (source : CoreStepRel space dispatch live
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings
      (emitted, output) (typing := typing) (caller := caller))
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) :
    ∃ selected value merged,
      Spec.Eval.Steps.UnifyStep target pattern yes no bindings selected output ∧
      (selected = emitted ∨ BindingMaterializationRel output selected emitted) ∧
      Metta.Minimal.interpretStack1 environment fuel state
        ⟨{ atom := encodeModelAtom (.expression [.symbol "unify", target, pattern, yes, no]),
            vars := scope } :: previous, native⟩ =
        ([Metta.Minimal.finItem previous value merged], state) ∧
      LeaBindingSolutionTheoryEquiv output merged ∧
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant merged ∧ LeaBindingsHEImage merged ∧
      ∀ valuation, HEBindingSatisfied valuation output →
        applyClassSolution valuation value = applyClassSolution valuation (encodeModelAtom selected) := by
  obtain ⟨selected, branch, readout⟩ : ∃ selected,
      Spec.Eval.Steps.UnifyStep target pattern yes no bindings selected output ∧
      (selected = emitted ∨ BindingMaterializationRel output selected emitted) := by
    rcases (Spec.Eval.Minimal.unify_step_exact (space := space)
      (dispatch := dispatch) (live := live) (typing := typing) (caller := caller)
      (target := target) (pattern := pattern) (yes := yes) (no := no)
      (incoming := bindings) (result := (emitted, output))).mp source with
      ⟨candidate, _updated, materialized⟩ | ⟨missing, same⟩
    · exact ⟨yes, .success ⟨candidate, fun _ _ => rfl⟩,
        Or.inr materialized⟩
    · have emittedEq : emitted = no :=
        congrArg (fun result : Spec.Eval.FrameResult => result.1) same
      have outputEq : output = bindings := by
        simpa using congrArg
          (fun result : Spec.Eval.FrameResult => result.2.bindings) same
      subst emitted
      subst output
      exact ⟨no, .noMatch missing, Or.inl rfl⟩
  obtain ⟨value, merged, nativeExact, theory, runtime, image, observed⟩ :=
    unifyStep_complete paired branch previous
  refine ⟨selected, value, merged, branch, readout, ?_, theory, runtime, image, observed⟩
  simpa only [encodeModelAtom, encodeModelAtoms, nativeExact] using
    step_unify environment fuel state previous scope (encodeModelAtom target)
      (encodeModelAtom pattern) (encodeModelAtom yes) (encodeModelAtom no) native

/-- Every actual selected unify item has an independent minimal step and a
paired output binding frame. Equal visible values do not identify success
with fallback or replace the carried output frame. -/
theorem unify_step_item_sound (target pattern yes no : Atom)
    {bindings : Bindings} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) {item : Metta.Minimal.Item}
    (member : item ∈ (Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := encodeModelAtom (.expression [.symbol "unify", target, pattern, yes, no]),
          vars := scope } :: previous, native⟩).1) :
    ∃ emitted output value merged,
      item = Metta.Minimal.finItem previous value merged ∧
      Spec.Eval.Steps.UnifyStep target pattern yes no bindings emitted output ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      ∀ valuation, HEBindingSatisfied valuation output →
        applyClassSolution valuation value = applyClassSolution valuation (encodeModelAtom emitted) := by
  have actualMember : item ∈ Metta.Minimal.unifyOp previous (encodeModelAtom target)
      (encodeModelAtom pattern) (encodeModelAtom yes) (encodeModelAtom no) native := by
    simpa only [encodeModelAtom, encodeModelAtoms, step_unify] using member
  obtain ⟨emitted, output, value, merged, same, selected, outputPaired, observed⟩ :=
    unifyOp_item_sound paired previous actualMember
  exact ⟨emitted, output, value, merged, same, selected, outputPaired, observed⟩

/-- The primitive itself preserves every operand exactly. In particular,
open syntax is allowed and no hidden materialization is attributed to the
primitive stack step. -/
theorem cons_atom_step_conformance {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) (native : Metta.Bindings)
    (head : Atom) (tail : List Atom) :
    CoreStepRel space dispatch live
      (.expression [.symbol "cons-atom", head, .expression tail]) bindings
      (.expression (head :: tail), bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := encodeModelAtom (.expression [.symbol "cons-atom", head, .expression tail]),
          vars := scope } :: previous, native⟩ =
      ([Metta.Minimal.finItem previous (encodeModelAtom (.expression (head :: tail))) native], state) := by
  refine ⟨.consAtom space head tail bindings, ?_⟩
  simpa only [encodeModelAtom, encodeModelAtoms] using
    step_cons_atom environment fuel state previous scope (encodeModelAtom head)
      (encodeModelAtoms tail) native

theorem decons_atom_step_conformance {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) (native : Metta.Bindings)
    (head : Atom) (tail : List Atom) :
    CoreStepRel space dispatch live
      (.expression [.symbol "decons-atom", .expression (head :: tail)]) bindings
      (.expression [head, .expression tail], bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := encodeModelAtom (.expression [.symbol "decons-atom", .expression (head :: tail)]),
          vars := scope } :: previous, native⟩ =
      ([Metta.Minimal.finItem previous (encodeModelAtom (.expression [head, .expression tail])) native], state) := by
  refine ⟨.deconsAtom space head tail bindings, ?_⟩
  simpa only [encodeModelAtom, encodeModelAtoms] using
    step_decons_atom environment fuel state previous scope (encodeModelAtom head)
      (encodeModelAtoms tail) native

/-- The paired binding theory earns a normal independent source presentation.
At the explicitly materialized native entry, cons and that source primitive
have alpha-related outputs even with bound and correlated residual variables. -/
theorem cons_atom_materialized_conformance {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) (head : Atom) (tail : List Atom) :
    let instruction := Atom.expression [.symbol "cons-atom", head, .expression tail]
    let returned := Atom.expression (head :: tail)
    ∃ presentation : TypeSubst,
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings) ∧
      CoreStepRel space dispatch live (presentation.apply instruction) bindings
        (presentation.apply returned, bindings) (typing := typing) (caller := caller) ∧
      Metta.Minimal.interpretStack1 environment fuel state
        ⟨{ atom := Metta.instantiate native (encodeModelAtom instruction), vars := scope } :: previous,
          native⟩ =
        ([Metta.Minimal.finItem previous
          (Metta.instantiate native (encodeModelAtom returned)) native], state) ∧
      ObservedTypeAlphaRel (presentation.apply returned)
        (Spec.Match.SolutionTheory.decodeModelAtom
          (Metta.instantiate native (encodeModelAtom returned))) := by
  intro instruction returned
  obtain ⟨presentation, normal, exactTheory, observed⟩ :=
    QueryBindingProjection.exists_normal_materialization paired.semantic
  refine ⟨presentation, normal, exactTheory, ?_, ?_, observed returned⟩
  · simpa only [instruction, returned, TypeSubst.apply, List.map_cons, List.map_nil] using
      (CoreStepRel.consAtom (dispatch := dispatch) (live := live) (typing := typing) (caller := caller)
        space (presentation.apply head) (tail.map presentation.apply) bindings)
  · simp [instruction, returned, encodeModelAtom, encodeModelAtoms, Metta.instantiate,
      Metta.Bindings.resolveAtom, Metta.Minimal.interpretStack1]

/-- Decons requires a syntactic nonempty expression at the independent
primitive boundary. Its elements may be arbitrary open terms; the paired
normal presentation supplies their materialized observation. -/
theorem decons_atom_materialized_conformance {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) (head : Atom) (tail : List Atom) :
    let instruction := Atom.expression [.symbol "decons-atom", .expression (head :: tail)]
    let returned := Atom.expression [head, .expression tail]
    ∃ presentation : TypeSubst,
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings) ∧
      CoreStepRel space dispatch live (presentation.apply instruction) bindings
        (presentation.apply returned, bindings) (typing := typing) (caller := caller) ∧
      Metta.Minimal.interpretStack1 environment fuel state
        ⟨{ atom := Metta.instantiate native (encodeModelAtom instruction), vars := scope } :: previous,
          native⟩ =
        ([Metta.Minimal.finItem previous
          (Metta.instantiate native (encodeModelAtom returned)) native], state) ∧
      ObservedTypeAlphaRel (presentation.apply returned)
        (Spec.Match.SolutionTheory.decodeModelAtom
          (Metta.instantiate native (encodeModelAtom returned))) := by
  intro instruction returned
  obtain ⟨presentation, normal, exactTheory, observed⟩ :=
    QueryBindingProjection.exists_normal_materialization paired.semantic
  refine ⟨presentation, normal, exactTheory, ?_, ?_, observed returned⟩
  · simpa only [instruction, returned, TypeSubst.apply, List.map_cons, List.map_nil] using
      (CoreStepRel.deconsAtom (dispatch := dispatch) (live := live) (typing := typing) (caller := caller)
        space (presentation.apply head) (tail.map presentation.apply) bindings)
  · simp [instruction, returned, encodeModelAtom, encodeModelAtoms, Metta.instantiate,
      Metta.Bindings.resolveAtom, Metta.Minimal.interpretStack1]

/-- A raw primitive result is materialized only by its finished chain
handler. The source presentation and actual result may choose different
residual variable names; their earned alpha relation, paired binding frame
and complete driver suffix connect the two executions. -/
theorem primitive_chain_function_completion {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack) (source returned : Atom)
    (name : String) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (embedded : embeddedInstruction source = true)
    (notChain : ¬IsChain source)
    (sourceStep :
      let template := Atom.expression [.symbol "return", .var name]
      let body := Atom.expression [.symbol "chain", source, .var name, template]
      CoreStepRel space dispatch (body :: .expression [.symbol "function", body] :: live)
        source bindings (returned, bindings) (typing := typing) (caller := some body))
    {normalized : Atom} (materialized : BindingMaterializationRel bindings returned normalized)
    (fuel : Nat)
    (nativeStep : ∀ continuation,
      Metta.Minimal.interpretStack1 environment (fuel + 4) state
        ⟨Metta.Minimal.atomToStack (encodeModelAtom source) continuation, native⟩ =
        ([Metta.Minimal.finItem continuation (encodeModelAtom returned) native], state))
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let template := Atom.expression [.symbol "return", .var name]
    let body := Atom.expression [.symbol "chain", source, .var name, template]
    let actual := Metta.instantiate native (encodeModelAtom returned)
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (normalized, bindings) (typing := typing) (caller := caller) ∧
    ObservedTypeAlphaRel normalized (Spec.Match.SolutionTheory.decodeModelAtom actual) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous actual native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous actual native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro template body actual
  obtain ⟨presentation, fold, rfl⟩ := materialized
  have normalizedResult : BindingMaterializationRel bindings returned (presentation.apply returned) :=
    ⟨presentation, fold, rfl⟩
  have constructed : CoreRunRel space dispatch (body :: .expression [.symbol "function", body] :: live)
      source bindings (returned, bindings) (typing := typing) (caller := some body) :=
    .instruction space source bindings _ embedded notChain sourceStep
  have selected : CoreStepRel space dispatch (.expression [.symbol "function", body] :: live)
      body bindings (.expression [.symbol "return", presentation.apply returned], bindings)
      (typing := typing) (caller := some (.expression [.symbol "function", body])) := by
    simpa [body, template, substituteName] using
      CoreStepRel.chain space source name template bindings (returned, bindings)
        (presentation.apply returned) constructed normalizedResult
  have bodyRun : CoreRunRel space dispatch (.expression [.symbol "function", body] :: live)
      body bindings (.expression [.symbol "return", presentation.apply returned], bindings)
      (typing := typing) (caller := some (.expression [.symbol "function", body])) :=
    .chain space body bindings _ _ ⟨_, rfl⟩ selected
      (.data space _ bindings (by simp [embeddedInstruction]))
  have terminalMaterialized : BindingMaterializationRel bindings
      (.expression [.symbol "return", presentation.apply returned])
      (.expression [.symbol "return", presentation.apply returned]) := by
    simpa only [TypeSubst.apply, List.map_cons, List.map_nil] using
      BindingMaterializationRel.reapply_same_presentation fold
        (.expression [.symbol "return", returned])
  have independent : CoreFunctionBodyRel space dispatch (.expression [.symbol "function", body] :: live)
      body bindings (.expression [.symbol "return", presentation.apply returned], bindings)
      (typing := typing) (caller := some (.expression [.symbol "function", body])) :=
    .terminal space body bindings _ _ bodyRun terminalMaterialized (by simp [embeddedInstruction])
  refine ⟨.function space body bindings _
    (.functionReturn space body _ bindings bindings ⟨_, rfl⟩ independent),
    QueryBindingProjection.binding_materialization_alpha paired.semantic normalizedResult, ?_⟩
  have nativePath := primitive_chain_return_pending_prefix environment state fuel previous
    (encodeModelAtom source) (encodeModelAtom returned) name native nativeStep
  have path : PendingSteps environment
      (fuel + 5, state, [Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", actual], vars := Metta.Minimal.varsCopy previous,
              fin := true } ::
          { atom := encodeModelAtom (.expression [.symbol "function", body]), ret := .function,
            vars := Metta.Minimal.varsCopy previous } :: previous, native⟩]) := by
    simpa only [body, template, actual, encodeModelAtom, encodeModelAtoms] using nativePath
  have idempotent : Metta.instantiate native actual = actual :=
    by
      have inert := LeaTTaBridge.instantiate_semantically_inert
        paired.semantic.runtime.canonical.1 (encodeModelAtom returned)
      simpa only [applyClassSolution_lea_eq_instantiate] using inert
  simpa only [idempotent, List.cons_append, List.nil_append, List.append_nil] using
    function_return_after_pending_prefix path queued done

/-- The stronger exact-value specialization requires independent source
materialization and actual native materialization to fix the chosen result.
The general construction above does not require either fixedness premise. -/
theorem primitive_chain_function_completion_of_fixed {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack) (source returned : Atom)
    (name : String) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (sourceFixed : BindingMaterializationRel bindings (returned) (returned))
    (embedded : embeddedInstruction source = true)
    (notChain : ¬IsChain source)
    (sourceStep :
      let template := Atom.expression [.symbol "return", .var name]
      let body := Atom.expression [.symbol "chain", source, .var name, template]
      CoreStepRel space dispatch (body :: .expression [.symbol "function", body] :: live)
        source bindings (returned, bindings) (typing := typing) (caller := some body))
    (fixed : Metta.instantiate native (encodeModelAtom returned) = encodeModelAtom returned)
    (fuel : Nat)
    (nativeStep : ∀ continuation,
      Metta.Minimal.interpretStack1 environment (fuel + 4) state
        ⟨Metta.Minimal.atomToStack (encodeModelAtom source) continuation, native⟩ =
        ([Metta.Minimal.finItem continuation (encodeModelAtom returned) native], state))
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let template := Atom.expression [.symbol "return", .var name]
    let body := Atom.expression [.symbol "chain", source, .var name, template]
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro template body
  have completed := primitive_chain_function_completion (caller := caller) space dispatch live typing
    environment state previous source returned name bindings native paired embedded notChain
    sourceStep sourceFixed fuel nativeStep queued done
  exact ⟨completed.1, by simpa only [fixed] using completed.2.2⟩

/-- Arbitrary open, fixed cons operands construct a whole function body;
the tail need not be empty and residual variables may remain correlated. -/
theorem cons_chain_function_completion_of_fixed {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack)
    (head : Atom) (tail : List Atom) (name : String) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (sourceFixed : BindingMaterializationRel bindings (.expression (head :: tail)) (.expression (head :: tail)))
    (fixed : Metta.instantiate native (encodeModelAtom (.expression (head :: tail))) =
      encodeModelAtom (.expression (head :: tail))) (fuel : Nat)
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let source := Atom.expression [.symbol "cons-atom", head, .expression tail]
    let template := Atom.expression [.symbol "return", .var name]
    let body := Atom.expression [.symbol "chain", source, .var name, template]
    let returned := Atom.expression (head :: tail)
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro source template body returned
  apply primitive_chain_function_completion_of_fixed space dispatch live typing environment state
    previous source returned name bindings native paired sourceFixed
    (by simp [source, embeddedInstruction])
    (by rintro ⟨rest, impossible⟩; simp [source] at impossible)
    (.consAtom space head tail bindings) fixed fuel _ queued done
  intro continuation
  simp [source, returned, encodeModelAtom, encodeModelAtoms,
    Metta.Minimal.atomToStack, Metta.Minimal.interpretStack1]

/-- The same independent/actual body construction is available for decons
without imposing closedness on any field. -/
theorem decons_chain_function_completion_of_fixed {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack)
    (head : Atom) (tail : List Atom) (name : String) (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (sourceFixed : BindingMaterializationRel bindings (.expression [head, .expression tail]) (.expression [head, .expression tail]))
    (fixed : Metta.instantiate native (encodeModelAtom (.expression [head, .expression tail])) =
      encodeModelAtom (.expression [head, .expression tail])) (fuel : Nat)
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let source := Atom.expression [.symbol "decons-atom", .expression (head :: tail)]
    let template := Atom.expression [.symbol "return", .var name]
    let body := Atom.expression [.symbol "chain", source, .var name, template]
    let returned := Atom.expression [head, .expression tail]
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro source template body returned
  apply primitive_chain_function_completion_of_fixed space dispatch live typing environment state
    previous source returned name bindings native paired sourceFixed
    (by simp [source, embeddedInstruction])
    (by rintro ⟨rest, impossible⟩; simp [source] at impossible)
    (.deconsAtom space head tail bindings) fixed fuel _ queued done
  intro continuation
  simp [source, returned, encodeModelAtom, encodeModelAtoms,
    Metta.Minimal.atomToStack, Metta.Minimal.interpretStack1]

/-- The previous closed empty-tail construction is a consequence of the
open fixed-result theorem. -/
theorem cons_chain_function_completion {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack) (head : Atom) (name : String)
    (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (closed : (encodeModelAtom head).vars = []) (fuel : Nat)
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let source := Atom.expression [.symbol "cons-atom", head, .expression []]
    let template := Atom.expression [.symbol "return", .var name]
    let body := Atom.expression [.symbol "chain", source, .var name, template]
    let returned := Atom.expression [head]
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous
        (encodeModelAtom (.expression [.symbol "function", body])) native :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) native].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  have sourceClosed : TypeSubst.typeVars (.expression [head]) = [] := by
    simpa [TypeSubst.typeVars, TypeSubst.typeVarsList,
      ← Spec.Type.Presentation.encodeModelAtom_vars_eq_typeVars] using closed
  have sourceFixed : BindingMaterializationRel bindings (.expression [head]) (.expression [head]) :=
    (BindingMaterializationRel.closed_iff _ _ _ sourceClosed).mpr
      ⟨rfl, QueryBindingProjection.binding_theory_satisfiable paired.semantic⟩
  exact cons_chain_function_completion_of_fixed space dispatch live typing environment state previous
    head [] name bindings native paired sourceFixed
    (Metta.instantiate_of_closed native _
      (by simp [encodeModelAtom, encodeModelAtoms, Metta.Atom.vars, closed])) fuel queued done

/-! ## Open operands and primitive fault controls -/

private def primitiveControlBindings : Metta.Bindings := [.val "bound" (.sym "answer")]

private theorem primitiveControl_paired :
    ScopedEquationQuery.BindingInvariant
      (QueryBindingProjection.project primitiveControlBindings) primitiveControlBindings := by
  have image : LeaBindingsHEImage primitiveControlBindings := by
    intro key value member
    have same : key = "bound" ∧ value = .sym "answer" := by
      simpa [primitiveControlBindings] using member
    obtain ⟨rfl, rfl⟩ := same
    exact leaAtomHEImage_sym "answer"
  have runtime : LeaTTaSpecConformance.LeaRuntimeBindingInvariant primitiveControlBindings := by
    apply LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty.merge
      (right := primitiveControlBindings)
    · intro key value member
      have same : key = "bound" ∧ value = .sym "answer" := by
        simpa [primitiveControlBindings] using member
      obtain ⟨rfl, rfl⟩ := same
      simp [MettaAtomNoFloat]
    · simp [primitiveControlBindings, Metta.Bindings.empty, Metta.Bindings.merge,
        Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
        Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder, Metta.Bindings.lookupVal,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal]
    · exact Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  exact QueryBindingProjection.paired _ image runtime

/-- A nonempty carried frame binds one input while two occurrences of a
residual variable remain open and correlated in both constructor outputs. -/
theorem open_correlated_materialized_primitive_outputs
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) :
    ScopedEquationQuery.BindingInvariant
      (QueryBindingProjection.project primitiveControlBindings) primitiveControlBindings ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := Metta.instantiate primitiveControlBindings
          (.expr [.sym "cons-atom", .var "bound", .expr [.var "free", .var "free"]]),
          vars := scope } :: previous, primitiveControlBindings⟩ =
      ([Metta.Minimal.finItem previous (.expr [.sym "answer", .var "free", .var "free"])
        primitiveControlBindings], state) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := Metta.instantiate primitiveControlBindings
          (.expr [.sym "decons-atom", .expr [.var "bound", .var "free", .var "free"]]),
          vars := scope } :: previous, primitiveControlBindings⟩ =
      ([Metta.Minimal.finItem previous (.expr [.sym "answer", .expr [.var "free", .var "free"]])
        primitiveControlBindings], state) ∧
    (Metta.Atom.expr [.sym "answer", .var "free", .var "free"]).vars = ["free", "free"] := by
  have materializedCons : Metta.instantiate primitiveControlBindings
      (.expr [.sym "cons-atom", .var "bound", .expr [.var "free", .var "free"]]) =
      .expr [.sym "cons-atom", .sym "answer", .expr [.var "free", .var "free"]] := by
    have bound := Metta.instantiate_singleton_val_var_of_not_mem "bound" (.sym "answer")
      (by simp [Metta.Atom.vars])
    have free := Metta.instantiate_singleton_val_inert "bound" (.sym "answer") (.var "free")
      (by simp [Metta.Atom.vars])
    simp only [primitiveControlBindings, Metta.instantiate, Metta.Bindings.resolveAtom,
      List.map_cons, List.map_nil] at bound free ⊢
    simp only [bound, free]
  have materializedDecons : Metta.instantiate primitiveControlBindings
      (.expr [.sym "decons-atom", .expr [.var "bound", .var "free", .var "free"]]) =
      .expr [.sym "decons-atom", .expr [.sym "answer", .var "free", .var "free"]] := by
    have bound := Metta.instantiate_singleton_val_var_of_not_mem "bound" (.sym "answer")
      (by simp [Metta.Atom.vars])
    have free := Metta.instantiate_singleton_val_inert "bound" (.sym "answer") (.var "free")
      (by simp [Metta.Atom.vars])
    simp only [primitiveControlBindings, Metta.instantiate, Metta.Bindings.resolveAtom,
      List.map_cons, List.map_nil] at bound free ⊢
    simp only [bound, free]
  refine ⟨primitiveControl_paired, ?_, ?_, by simp [Metta.Atom.vars]⟩
  · rw [materializedCons]
    exact step_cons_atom environment fuel state previous scope _ _ _
  · rw [materializedDecons]
    exact step_decons_atom environment fuel state previous scope _ _ _

/-- The general function theorem genuinely admits nonclosed correlated
payloads under a nonempty paired frame, arbitrary callers and queued work. -/
theorem open_correlated_cons_function_completion {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack) (name : String) (fuel : Nat)
    (queued : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let bindings := QueryBindingProjection.project primitiveControlBindings
    let returned := Atom.expression [.symbol "answer", .var "free", .var "free"]
    let source := Atom.expression [.symbol "cons-atom", .symbol "answer",
      .expression [.var "free", .var "free"]]
    let body := Atom.expression [.symbol "chain", source, .var name,
      .expression [.symbol "return", .var name]]
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous (encodeModelAtom (.expression [.symbol "function", body]))
        primitiveControlBindings :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) primitiveControlBindings].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) primitiveControlBindings].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  have sourceFixed : BindingMaterializationRel
      (QueryBindingProjection.project primitiveControlBindings)
      (.expression [.symbol "answer", .var "free", .var "free"])
      (.expression [.symbol "answer", .var "free", .var "free"]) := by
    change BindingMaterializationRel (⟨[("bound", .symbol "answer")], []⟩ : Bindings) _ _
    apply BindingMaterializationRel.of_unassigned_variables
      (single_assignment_presentation "bound" (.symbol "answer") (by simp [TypeSubst.typeVars]))
    intro key member
    simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at member
    subst key
    simp [TypeSubst.keys]
  exact cons_chain_function_completion_of_fixed space dispatch live typing environment state previous
    (.symbol "answer") [.var "free", .var "free"] name _ _ primitiveControl_paired
    sourceFixed
    (Metta.instantiate_singleton_val_inert "bound" (.sym "answer") _
      (by simp [encodeModelAtom, encodeModelAtoms, Metta.Atom.vars])) fuel queued done

/-- A non-fixed primitive result is resolved by the chain handler, then
returned by the enclosing function. The two free occurrences remain shared;
the raw primitive itself still emits the bound variable. -/
theorem open_cons_function_materializes_binding {caller : Option Atom}
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (previous : Metta.Minimal.Stack) (name : String)
    (fuel : Nat) (queued : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings)) :
    let bindings := QueryBindingProjection.project primitiveControlBindings
    let raw := Atom.expression [.var "bound", .var "free", .var "free"]
    let returned := Atom.expression [.symbol "answer", .var "free", .var "free"]
    let source := Atom.expression
      [.symbol "cons-atom", .var "bound", .expression [.var "free", .var "free"]]
    let body := Atom.expression
      [.symbol "chain", source, .var name, .expression [.symbol "return", .var name]]
    ¬Spec.Type.Presentation.BindingTheory.BindingMaterializationRel bindings raw raw ∧
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (returned, bindings) (typing := typing) (caller := caller) ∧
    Metta.Minimal.interpretFuel environment (fuel + 5) state
      (Metta.Minimal.evalResult previous (encodeModelAtom (.expression [.symbol "function", body]))
        primitiveControlBindings :: queued) done =
      Metta.Minimal.interpretFuel environment fuel state
        (([Metta.Minimal.finItem previous (encodeModelAtom returned) primitiveControlBindings].filter
          (fun result => !Metta.Minimal.isFinal result)) ++ queued)
        ((([Metta.Minimal.finItem previous (encodeModelAtom returned) primitiveControlBindings].filter
          Metta.Minimal.isFinal).map Metta.Minimal.finalPair).reverse ++ done) := by
  intro bindings raw returned source body
  have nativeResolved : Metta.instantiate primitiveControlBindings (encodeModelAtom raw) =
      encodeModelAtom returned := by
    have bound := Metta.instantiate_singleton_val_var_of_not_mem "bound" (.sym "answer")
      (by simp [Metta.Atom.vars])
    have free := Metta.instantiate_singleton_val_inert "bound" (.sym "answer") (.var "free")
      (by simp [Metta.Atom.vars])
    simp only [primitiveControlBindings, raw, returned, encodeModelAtom, encodeModelAtoms,
      Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil]
      at bound free ⊢
    simp only [bound, free]
  have materialized : Spec.Type.Presentation.BindingTheory.BindingMaterializationRel
      bindings raw returned := by
    change BindingMaterializationRel
      (⟨[("bound", .symbol "answer")], []⟩ : Bindings) raw returned
    simpa [raw, returned, TypeSubst.apply, TypeSubst.lookup] using
      BindingMaterializationRel.single_assignment "bound" (.symbol "answer") raw
        (by simp [TypeSubst.typeVars])
  have notFixed : ¬BindingMaterializationRel bindings raw raw := by
    intro fixed
    have alpha := QueryBindingProjection.binding_materialization_alpha
      primitiveControl_paired.semantic fixed
    rw [nativeResolved, Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom] at alpha
    have wrong := (symbolicHead_of_observedTypeAlpha_iff alpha "answer").mpr
      ⟨[.var "free", .var "free"], rfl⟩
    obtain ⟨tail, impossible⟩ := wrong
    simp [raw] at impossible
  have completed := primitive_chain_function_completion (caller := caller)
    space dispatch live typing environment state previous source raw name bindings
    primitiveControlBindings primitiveControl_paired (by simp [source, embeddedInstruction])
    (by rintro ⟨rest, impossible⟩; simp [source] at impossible)
    (by exact .consAtom space _ _ bindings) materialized fuel
    (fun continuation => by
      simp [source, raw, encodeModelAtom, encodeModelAtoms,
        Metta.Minimal.atomToStack, Metta.Minimal.interpretStack1]) queued done
  refine ⟨notFixed, completed.1, ?_⟩
  simpa only [nativeResolved] using completed.2.2

/-- Empty deconstruction has a real runtime diagnostic but no constructor in
the current independent primitive judgment. It must not be called a proved
source/native error correspondence. -/
theorem decons_empty_native_fault_without_source_step
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) (native : Metta.Bindings) :
    (∀ result, ¬CoreStepRel space dispatch live
      (.expression [.symbol "decons-atom", .expression []]) bindings result (typing := typing)) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := .expr [.sym "decons-atom", .expr []], vars := scope } :: previous, native⟩ =
      ([Metta.Minimal.finItem previous
        (Metta.Minimal.errAtom (.expr [.sym "decons-atom", .expr []])
          "decons-atom: expected (decons-atom <non-empty-expression>)") native], state) := by
  constructor
  · intro result step
    generalize equation : (Atom.expression [.symbol "decons-atom", .expression []]) = source at step
    cases step <;> simp at equation
  · exact step_decons_atom_invalid environment fuel state previous scope _ native
      (by intro head tail; simp)

/-- A tail alias is invalid at unmaterialized primitive entry, even when its
binding is an expression. Materializing the instruction first succeeds.
The independent raw primitive has no step for that unresolved tail either. -/
theorem cons_tail_alias_needs_materialized_entry
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService)
    (environment : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (previous : Metta.Minimal.Stack) (scope : List String) :
    let bindings : Bindings := ⟨[("tail", .expression [.symbol "b"])], []⟩
    let native : Metta.Bindings := [.val "tail" (.expr [.sym "b"])]
    let instruction := Atom.expression [.symbol "cons-atom", .symbol "a", .var "tail"]
    (∀ result, ¬CoreStepRel space dispatch live instruction bindings result (typing := typing)) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := encodeModelAtom instruction, vars := scope } :: previous, native⟩ =
      ([Metta.Minimal.finItem previous (Metta.Minimal.errAtom (encodeModelAtom instruction)
        "cons-atom: expected (cons-atom <head> <expression>)") native], state) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      ⟨{ atom := Metta.instantiate native (encodeModelAtom instruction), vars := scope } :: previous, native⟩ =
      ([Metta.Minimal.finItem previous (.expr [.sym "a", .sym "b"]) native], state) := by
  intro bindings native instruction
  refine ⟨?_, ?_, ?_⟩
  · intro result step
    generalize equation : instruction = source at step
    cases step <;> simp [instruction] at equation
  · simpa only [instruction, encodeModelAtom, encodeModelAtoms] using
      step_cons_atom_invalid_tail environment fuel state previous scope (.sym "a") (.var "tail")
        native (by intro values; simp)
  · have materialized : Metta.instantiate native (encodeModelAtom instruction) =
        .expr [.sym "cons-atom", .sym "a", .expr [.sym "b"]] := by
      have tail := Metta.instantiate_singleton_val_var_of_not_mem "tail" (.expr [.sym "b"])
        (by simp [Metta.Atom.vars])
      simp only [native, instruction, encodeModelAtom, encodeModelAtoms, Metta.instantiate,
        Metta.Bindings.resolveAtom, List.map_cons, List.map_nil] at tail ⊢
      rw [tail]
    rw [materialized]
    exact step_cons_atom environment fuel state previous scope _ _ _

/-- The independent source and actual function handler both resolve the
open return operand under its carried frame. A raw variable is not the
completed answer when that frame binds it to a symbol. -/
theorem open_return_operand_is_materialized
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat)
    (previous : Metta.Minimal.Stack) :
    let bindings : Bindings := ⟨[("result", .symbol "answer")], []⟩
    LeaBindingSolutionTheoryEquiv bindings [.val "result" (.sym "answer")] ∧
    CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", .var "result"]])
      bindings (.symbol "answer", bindings) (typing := typing) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        ({ atom := .expr [.sym "function", .expr [.sym "return", .var "result"]],
           ret := .function } :: previous)
        (.expr [.sym "return", .var "result"]) [.val "result" (.sym "answer")]) =
      ([Metta.Minimal.finItem previous (.sym "answer") [.val "result" (.sym "answer")]], state) ∧
    (Metta.Atom.var "result") ≠ .sym "answer" := by
  intro bindings
  have image : LeaBindingsHEImage [.val "result" (.sym "answer")] := by
    intro key value member
    have same : key = "result" ∧ value = .sym "answer" := by simpa using member
    obtain ⟨rfl, rfl⟩ := same
    exact leaAtomHEImage_sym "answer"
  have resolved : BindingMaterializationRel bindings (.var "result") (.symbol "answer") := by
    simpa [bindings, TypeSubst.apply, TypeSubst.lookup] using
      BindingMaterializationRel.single_assignment "result" (.symbol "answer") (.var "result")
        (by simp [TypeSubst.typeVars])
  refine ⟨?_, immediate_function_completion_exact.mpr ⟨.symbol "answer", resolved, rfl⟩,
    ?_, by intro impossible; cases impossible⟩
  · simpa [bindings, QueryBindingProjection.project, leaEqualityEdges,
      Spec.Match.SolutionTheory.decodeModelAtom] using
      QueryBindingProjection.solutionTheory [.val "result" (.sym "answer")] image
  ·
    have instantiated : Metta.instantiate [.val "result" (.sym "answer")] (.var "result") =
        .sym "answer" := by
      rw [Metta.instantiate, Metta.Bindings.resolveAtom]
      rfl
    simpa only [instantiated] using step_function_return environment fuel state previous []
      (.expr [.sym "function", .expr [.sym "return", .var "result"]]) (.var "result")
      [.val "result" (.sym "answer")]

/-- Omitting a saved caller changes the diagnostic. The source judgment
now distinguishes those contexts, and the captured case agrees with the
actual nested handler without erasing the error subject. -/
theorem noReturn_error_subjects_differ
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat) :
    let body := Atom.expression [.symbol "terminal"]
    let functionValue := Atom.expression [.symbol "function", body]
    CoreInvocationResultRel space dispatch live functionValue Bindings.empty
      (Atom.error body (.symbol "NoReturn"), Bindings.empty) (typing := typing) ∧
    CoreInvocationResultRel space dispatch live functionValue Bindings.empty
      (Atom.error (.symbol "caller") (.symbol "NoReturn"), Bindings.empty)
      (typing := typing) (caller := some (.symbol "caller")) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        [{ atom := encodeModelAtom functionValue, ret := .function }, { atom := .sym "caller" }]
        (encodeModelAtom body) []) =
      ([Metta.Minimal.finItem [{ atom := .sym "caller" }]
        (Metta.Minimal.errAtom (.sym "caller") "NoReturn") []], state) ∧
    encodeModelAtom (Atom.error body (.symbol "NoReturn")) ≠
      Metta.Minimal.errAtom (.sym "caller") "NoReturn" := by
  intro body functionValue
  have expression : ∃ atoms, body = .expression atoms := ⟨_, rfl⟩
  have data : embeddedInstruction body = false := by simp [body, embeddedInstruction]
  have missing : ∀ value, body ≠ .expression [.symbol "return", value] := by
    intro value
    simp [body]
  refine ⟨.function space body Bindings.empty _
    (function_data_noReturn space dispatch live typing none body Bindings.empty body
      (BindingMaterializationRel.empty body) expression data data missing),
    .function space body Bindings.empty _
    (function_data_noReturn space dispatch live typing (some (.symbol "caller")) body
      Bindings.empty body (BindingMaterializationRel.empty body) expression data data missing), ?_, ?_⟩
  · simpa [functionTerminalResult, functionValue, body, Atom.error,
      encodeModelAtom, encodeModelAtoms, Metta.Minimal.errAtom] using
      function_terminal_handler_conformance environment state fuel [{ atom := .sym "caller" }]
        [] (encodeModelAtom functionValue) [] (some (.symbol "caller")) body
        (encodeModelAtom body) rfl
        (Metta.instantiate_of_closed [] _ (by simp [body, encodeModelAtom, encodeModelAtoms,
          Metta.Atom.vars])) (by rfl)
  · simp [body, Atom.error, encodeModelAtom, encodeModelAtoms, Metta.Minimal.errAtom]

/-- Two nested function faults use two different saved callers. The source
derivation and the actual handlers agree at both boundaries. -/
theorem nested_function_fault_contexts
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) (fuel : Nat) :
    let body := Atom.expression [.symbol "terminal"]
    let inner := Atom.expression [.symbol "function", body]
    let outer := Atom.expression [.symbol "function", inner]
    let innerFault := Atom.error outer (.symbol "NoReturn")
    let result := Atom.error (.symbol "caller") (.symbol "NoReturn")
    let previous : Metta.Minimal.Stack := [{ atom := .sym "caller" }]
    let outerFrame : Metta.Minimal.Frame := { atom := encodeModelAtom outer, ret := .function }
    CoreInvocationResultRel space dispatch live outer Bindings.empty
      (result, Bindings.empty) (typing := typing) (caller := some (.symbol "caller")) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem
        ({ atom := encodeModelAtom inner, ret := .function } :: outerFrame :: previous)
        (encodeModelAtom body) []) =
      ([Metta.Minimal.finItem (outerFrame :: previous) (encodeModelAtom innerFault) []], state) ∧
    Metta.Minimal.interpretStack1 environment fuel state
      (Metta.Minimal.finItem (outerFrame :: previous) (encodeModelAtom innerFault) []) =
      ([Metta.Minimal.finItem previous (encodeModelAtom result) []], state) := by
  intro body inner outer innerFault result previous outerFrame
  have innerStep : CoreStepRel space dispatch (outer :: live) inner Bindings.empty
      (innerFault, Bindings.empty) (typing := typing) (caller := some outer) :=
    function_data_noReturn space dispatch (outer :: live) typing (some outer) body
      Bindings.empty body (BindingMaterializationRel.empty body) ⟨_, rfl⟩
      (by simp [body, embeddedInstruction]) (by simp [body, embeddedInstruction])
      (by intro value; simp [body])
  have innerRun : CoreRunRel space dispatch (outer :: live) inner Bindings.empty
      (innerFault, Bindings.empty) (typing := typing) (caller := some outer) :=
    .instruction space inner Bindings.empty _ (by simp [inner, embeddedInstruction])
      (by rintro ⟨_, same⟩; simp [inner] at same) innerStep
  have bodyRun : CoreFunctionBodyRel space dispatch (outer :: live) inner Bindings.empty
      (innerFault, Bindings.empty) (typing := typing) (caller := some outer) :=
    .terminal space inner Bindings.empty _ _ innerRun
      (BindingMaterializationRel.empty innerFault)
      (by simp [innerFault, Atom.error, embeddedInstruction])
  constructor
  · apply CoreInvocationResultRel.function space inner Bindings.empty _
    apply function_step_body_terminal_iff.mpr
    exact ⟨⟨_, rfl⟩, innerFault, Bindings.empty, bodyRun,
      by simp [result, innerFault, Atom.error, functionTerminalResult]⟩
  constructor
  · simpa [body, inner, outer, innerFault, outerFrame, previous,
      functionTerminalResult, Atom.error, encodeModelAtom, encodeModelAtoms, Metta.Minimal.errAtom] using
      function_terminal_handler_conformance environment state fuel (outerFrame :: previous) []
        (encodeModelAtom inner) [] (some outer) body (encodeModelAtom body) rfl
        (Metta.instantiate_of_closed [] _ (by simp [body, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]))
        (by rfl)
  · simpa [innerFault, result, functionTerminalResult, Atom.error, encodeModelAtom,
      encodeModelAtoms, Metta.Minimal.errAtom] using
      function_terminal_handler_conformance environment state fuel previous []
        (encodeModelAtom outer) [] (some (.symbol "caller")) innerFault
        (encodeModelAtom innerFault) rfl
        (Metta.instantiate_of_closed [] _ (by simp [innerFault, outer, inner, body,
          Atom.error, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars])) (by rfl)

/-- Exact function arity matters: the independent raw constructor holds a
malformed one-token function expression, while the runtime head test routes
it to the malformed-function error path. The guards are not interchangeable. -/
theorem malformed_function_head_routes_differ
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (bindings : Bindings)
    (previous : Metta.Minimal.Stack) (native : Metta.Bindings) :
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function"])
      bindings (.expression [.symbol "function"], bindings) (typing := typing) ∧
    Metta.Minimal.evalResult previous (.expr [.sym "function"]) native =
      Metta.Minimal.finItem previous
        (Metta.Minimal.errAtom (.expr [.sym "function"]) "function: expected (function <expression>)") native ∧
    Metta.Minimal.evalResult previous (.expr [.sym "function"]) native ≠
      Metta.Minimal.finItem previous (.expr [.sym "function"]) native := by
  refine ⟨.raw space _ bindings ?_, ?_, ?_⟩
  · rintro ⟨body, impossible⟩
    simp at impossible
  · simp [Metta.Minimal.evalResult, Metta.Minimal.atomToStack, Metta.Minimal.finItem]
  · intro same
    have atoms := congrArg (fun item => item.stack.map (fun frame => frame.atom)) same
    simp [Metta.Minimal.evalResult, Metta.Minimal.atomToStack, Metta.Minimal.finItem,
      Metta.Minimal.errAtom] at atoms

/-- An ordinary callable-looking expression is finished data at the raw
completion boundary, irrespective of whether another evaluator can call it. -/
theorem callable_looking_raw_result_is_finished (bindings : Metta.Bindings) :
    Metta.Minimal.isFinal
      (Metta.Minimal.evalResult [] (.expr [.sym "callable", .var "argument"]) bindings) = true := by
  rfl


/-! ## Constructed retained function invocations -/

open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory
open LeaTTaTypeConformance
open LeaTTaMinimalControlExecution.Retained
open Metta.Minimal
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private theorem closed_valuation (valuation : String → Atom) (atom : Atom)
    (closed : TypeSubst.typeVars atom = []) : applyTypeValuation valuation atom = atom := by
  rw [applyTypeValuation_eq_subst]
  exact Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ atom
    (by simpa only [TypeSubst.typeVars_eq_vars] using closed)

/-- Closed materializations have no residual representative choice. The exact
native operand follows from the actual binding model, not an execution premise. -/
theorem materialization_closed_native {bindings : Bindings} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    {raw normalized : Atom} (materialized : BindingMaterializationRel bindings raw normalized)
    (closed : TypeSubst.typeVars normalized = []) :
    Metta.instantiate native (encodeModelAtom raw) = encodeModelAtom normalized := by
  have model := specTypeBindingSatisfied_of_heBindingSatisfied
    ((paired.semantic.solutionTheory _).mpr paired.semantic.runtime.canonical.1)
  have observed := materialized.preserves_model _ model
  rw [closed_valuation _ normalized closed] at observed
  rw [← decodeModelAtom_applyClassSolution, applyClassSolution_lea_eq_instantiate] at observed
  have image : LeaAtomHEImage (Metta.instantiate native (encodeModelAtom raw)) :=
    instantiate_heImage paired.image _ ⟨raw, rfl⟩
  exact (encodeModelAtom_decodeModelAtom_of_heImage image).symm.trans
    (congrArg encodeModelAtom observed.symm)

inductive ControlPhase where
  | run
  | body

/-- Local source admission records reached bindings and the structural
possibility of a binding update. Read-only constructors retain exact frames. -/
inductive CoveredControlDerivation :
    Bindings → ControlPhase → Option Atom → Atom → Atom → Bindings → Bool → Prop where
  | data {bindings : Bindings} {caller : Option Atom} (atom : Atom)
      (sourceRaw : embeddedInstruction atom = false)
      (nativeRaw : Metta.Minimal.isEmbeddedOp (encodeModelAtom atom) = false) :
      CoveredControlDerivation bindings .run caller atom atom bindings false
  | cons {bindings : Bindings} {caller : Option Atom} (head : Atom) (tail : List Atom) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "cons-atom", head, .expression tail]) (.expression (head :: tail)) bindings false
  | decons {bindings : Bindings} {caller : Option Atom} (head : Atom) (tail : List Atom) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "decons-atom", .expression (head :: tail)])
        (.expression [head, .expression tail]) bindings false
  | unifySuccess {bindings output : Bindings} {caller : Option Atom}
      (target pattern yes no result : Atom)
      (candidate : Spec.Eval.Steps.UnifyCandidateRel target pattern bindings output)
      (materialized : BindingMaterializationRel output yes result)
      (closed : TypeSubst.typeVars result = [])
      (nonvariable : HEAssignmentsNonVariable output) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "unify", target, pattern, yes, no]) result output true
  | chain {bindings middle output : Bindings} {firstUpdates nextUpdates : Bool}
      {caller : Option Atom} (source raw normalized template result : Atom) (name : String)
      (first : CoveredControlDerivation bindings .run
        (some (.expression [.symbol "chain", source, .var name, template])) source raw middle firstUpdates)
      (materialized : BindingMaterializationRel middle raw normalized)
      (closed : TypeSubst.typeVars normalized = [])
      (next : CoveredControlDerivation middle .run caller
        (substituteName name normalized template) result output nextUpdates) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "chain", source, .var name, template]) result output (firstUpdates || nextUpdates)
  | functionReturn {bindings output : Bindings} {updates : Bool} {caller : Option Atom} (body returned : Atom)
      (expression : ∃ atoms, body = .expression atoms)
      (bodyRun : CoveredControlDerivation bindings .body
        (some (.expression [.symbol "function", body])) body
        (.expression [.symbol "return", returned]) output updates) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "function", body]) returned output updates
  | functionNoReturn {bindings output : Bindings} {updates : Bool} {caller : Option Atom} (body terminal : Atom)
      (expression : ∃ atoms, body = .expression atoms)
      (bodyRun : CoveredControlDerivation bindings .body
        (some (.expression [.symbol "function", body])) body terminal output updates)
      (missing : ∀ value, terminal ≠ .expression [.symbol "return", value]) :
      CoveredControlDerivation bindings .run caller
        (.expression [.symbol "function", body]) (functionTerminalResult caller terminal) output updates
  | terminal {bindings output : Bindings} {updates : Bool} {caller : Option Atom} (source raw normalized : Atom)
      (run : CoveredControlDerivation bindings .run caller source raw output updates)
      (materialized : BindingMaterializationRel output raw normalized)
      (closed : TypeSubst.typeVars normalized = [])
      (sourceTerminal : embeddedInstruction normalized = false)
      (nativeTerminal : Metta.Minimal.isEmbeddedOp (encodeModelAtom normalized) = false) :
      CoveredControlDerivation bindings .body caller source normalized output updates
  | resume {bindings middle output : Bindings} {firstUpdates bodyUpdates : Bool}
      {caller : Option Atom} (source raw normalized result : Atom)
      (run : CoveredControlDerivation bindings .run caller source raw middle firstUpdates)
      (materialized : BindingMaterializationRel middle raw normalized)
      (closed : TypeSubst.typeVars normalized = [])
      (sourceInstruction : embeddedInstruction normalized = true)
      (nativeInstruction : Metta.Minimal.isEmbeddedOp (encodeModelAtom normalized) = true)
      (body : CoveredControlDerivation middle .body caller normalized result output bodyUpdates) :
      CoveredControlDerivation bindings .body caller source result output (firstUpdates || bodyUpdates)

theorem CoveredControlDerivation.sound {bindings output : Bindings} {updates : Bool} {phase : ControlPhase}
    {caller : Option Atom} {source result : Atom}
    (derivation : CoveredControlDerivation bindings phase caller source result output updates)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (typing : Spec.Eval.EvalTypeService) (live : List Atom) :
    match phase with
    | .run => CoreRunRel space dispatch live source bindings (result, output)
        (typing := typing) (caller := caller)
    | .body => CoreFunctionBodyRel space dispatch live source bindings (result, output)
        (typing := typing) (caller := caller) := by
  induction derivation generalizing live with
  | data atom sourceRaw nativeRaw => exact .data space atom _ sourceRaw
  | cons head tail =>
    exact .instruction space _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨rest, impossible⟩; simp at impossible) (.consAtom space head tail _)
  | decons head tail =>
    exact .instruction space _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨rest, impossible⟩; simp at impossible) (.deconsAtom space head tail _)
  | unifySuccess target pattern yes no result candidate materialized closed nonvariable =>
    exact .instruction space _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨rest, impossible⟩; simp at impossible)
      (.unifySuccess space target pattern yes no result _ _ candidate
        (.historical _ _) materialized)
  | chain source raw normalized template result name first materialized closed next ihFirst ihNext =>
    exact .chain space _ _ _ _ ⟨_, rfl⟩
      (.chain space source name template _ (raw, _) normalized
        (ihFirst (_ :: live)) materialized) (ihNext live)
  | functionReturn body returned expression bodyRun ih =>
    exact .instruction space _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨rest, impossible⟩; simp at impossible)
      (.functionReturn space body returned _ _ expression (ih (_ :: live)))
  | functionNoReturn body terminal expression bodyRun missing ih =>
    exact .instruction space _ _ _ (by simp [embeddedInstruction])
      (by rintro ⟨rest, impossible⟩; simp at impossible)
      (.functionNoReturn space body terminal _ _ expression (ih (_ :: live)) missing)
  | terminal source raw normalized run materialized closed sourceTerminal nativeTerminal ih =>
    exact .terminal space source _ (raw, _) normalized (ih live) materialized sourceTerminal
  | resume source raw normalized result run materialized closed sourceInstruction nativeInstruction body ihRun ihBody =>
    exact .resume space source _ (raw, _) normalized (result, _)
      (ihRun live) materialized sourceInstruction (ihBody live)

private def scopedFinished (previous : Stack) (atom : Metta.Atom) (bindings : Metta.Bindings)
    (scope : List String) : Item :=
  ⟨{ atom := atom, fin := true, vars := scope } :: previous, bindings⟩

private theorem scopedFinished_step (environment : MinEnv) (state : St) (fuel : Nat)
    (parent : Frame) (previous : Stack) (atom : Metta.Atom) (bindings : Metta.Bindings)
    (scope : List String) :
    interpretStack1 environment fuel state (scopedFinished (parent :: previous) atom bindings scope) =
      interpretStack1 environment fuel state (finItem (parent :: previous) atom bindings) := by
  simp only [scopedFinished, finItem, interpretStack1, if_true]

private theorem atomToStack_raw (atom : Metta.Atom) (previous : Stack)
    (raw : isEmbeddedOp atom = false) :
    atomToStack atom previous = { atom := atom, vars := varsCopy previous } :: previous := by
  unfold atomToStack
  split <;> try rfl
  all_goals simp_all [isEmbeddedOp]

set_option maxHeartbeats 2000000 in
private theorem raw_step (environment : MinEnv) (state : St) (fuel : Nat)
    (atom : Metta.Atom) (previous : Stack) (bindings : Metta.Bindings)
    (raw : isEmbeddedOp atom = false) :
    interpretStack1 environment fuel state ⟨atomToStack atom previous, bindings⟩ =
      ([scopedFinished previous atom bindings (varsCopy previous)], state) := by
  rw [atomToStack_raw atom previous raw]
  simp only [interpretStack1, Bool.false_eq_true, if_false]
  split <;> try rfl
  all_goals simp_all [isEmbeddedOp, scopedFinished]

private theorem raw_ready (atom : Metta.Atom) (previous : Stack) (bindings : Metta.Bindings)
    (raw : isEmbeddedOp atom = false) :
    stepReady ⟨atomToStack atom previous, bindings⟩ = true := by
  rw [atomToStack_raw atom previous raw]
  simp only [stepReady, Bool.false_or]
  cases atom with
  | expr atoms =>
    cases atoms with
    | nil => rfl
    | cons head tail =>
      cases head with
      | sym name =>
        simp only [isEmbeddedOp, List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.or_eq_false_iff] at raw
        simp_all [nestedBudgetInstruction]
      | _ => rfl
  | _ => rfl

private theorem toLeaTTa_substituteName (name : String) (value atom : Atom) :
    encodeModelAtom (substituteName name value atom) =
      Metta.Subst.apply [(name, encodeModelAtom value)] (encodeModelAtom atom) := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => encodeModelAtoms (atoms.map (substituteName name value)) =
        (encodeModelAtoms atoms).map (Metta.Subst.apply [(name, encodeModelAtom value)])) with
  | symbol symbol => simp [substituteName, encodeModelAtom, Metta.Subst.apply]
  | var varName =>
    by_cases same : varName = name <;> simp [substituteName, Metta.Subst.apply, Metta.Subst.lookup, encodeModelAtom, same]
  | grounded value => simp [substituteName, encodeModelAtom, Metta.Subst.apply]
  | expression atoms ih =>
    simpa only [substituteName, encodeModelAtom, Metta.Subst.apply] using congrArg Metta.Atom.expr ih
  | nil => rfl
  | cons atom atoms first later =>
    exact congrArg₂ List.cons first later

/-- Actual pending-prefix realization retains changed frames and materialized operands. -/
private def ControlRealizes (environment : MinEnv) (state : St) (native : Metta.Bindings)
    (phase : ControlPhase) (caller : Option Atom) (source result : Atom)
    (output : Bindings) (updates : Bool) : Prop :=
  match phase with
  | .run => ∀ (parent : Frame) (previous : Stack),
      some parent.atom = caller.map encodeModelAtom →
      ∃ nativeOutput, ScopedEquationQuery.BindingInvariant output nativeOutput ∧
        (updates = false → nativeOutput = native) ∧ ∀ fuel,
      ∃ initial scope operand, CoveredPendingSteps environment
        (initial, state, [⟨atomToStack (encodeModelAtom source) (parent :: previous), native⟩])
        (fuel, state, [scopedFinished (parent :: previous) operand nativeOutput scope]) ∧
        Metta.instantiate nativeOutput operand = Metta.instantiate nativeOutput (encodeModelAtom result)
  | .body => ∀ (parent : Frame) (previous : Stack),
      some parent.atom = caller.map encodeModelAtom → parent.ret = .function →
      ∃ nativeOutput, ScopedEquationQuery.BindingInvariant output nativeOutput ∧
        (updates = false → nativeOutput = native) ∧ ∀ fuel,
      ∃ initial scope operand, CoveredPendingSteps environment
        (initial, state, [⟨atomToStack (encodeModelAtom source) (parent :: previous), native⟩])
        (fuel, state, [scopedFinished (parent :: previous) operand nativeOutput scope]) ∧
        Metta.instantiate nativeOutput operand = encodeModelAtom result ∧
        isEmbeddedOp (encodeModelAtom result) = false

private theorem CoveredControlDerivation.realizes {bindings output : Bindings} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    {updates : Bool} {phase : ControlPhase} {caller : Option Atom} {source result : Atom}
    (derivation : CoveredControlDerivation bindings phase caller source result output updates)
    (environment : MinEnv) (state : St) :
    ControlRealizes environment state native phase caller source result output updates := by
  induction derivation generalizing native with
  | data atom sourceRaw nativeRaw =>
    intro parent previous captured
    refine ⟨native, paired, fun _ => rfl, ?_⟩
    intro fuel
    refine ⟨fuel + 1, varsCopy (parent :: previous), encodeModelAtom atom, .single ?_, rfl⟩
    exact coveredPendingStep_singleton (raw_ready _ _ _ nativeRaw)
      (raw_step environment state fuel _ _ native nativeRaw) (by rfl)
  | cons head tail =>
    intro parent previous captured
    refine ⟨native, paired, fun _ => rfl, ?_⟩
    intro fuel
    refine ⟨fuel + 1, [], _, .single ?_, rfl⟩
    apply coveredPendingStep_singleton (by rfl) (pending := by rfl)
    simp [encodeModelAtom, encodeModelAtoms, atomToStack, interpretStack1, scopedFinished, finItem]
  | decons head tail =>
    intro parent previous captured
    refine ⟨native, paired, fun _ => rfl, ?_⟩
    intro fuel
    refine ⟨fuel + 1, [], _, .single ?_, rfl⟩
    apply coveredPendingStep_singleton (by rfl) (pending := by rfl)
    simp [encodeModelAtom, encodeModelAtoms, atomToStack, interpretStack1, scopedFinished, finItem]
  | unifySuccess target pattern yes no result candidate materialized closed nonvariable =>
    intro parent previous captured
    let branch : Spec.Eval.Steps.UnifyStep target pattern yes no _ yes _ :=
      .success ⟨candidate, fun _ _ => rfl⟩
    obtain ⟨value, merged, selectedNative, theory, runtime, image, observed⟩ :=
      unifyStep_complete_materialized paired branch (parent :: previous)
    have outputPaired : ScopedEquationQuery.BindingInvariant _ merged :=
      ⟨⟨theory, nonvariable, runtime⟩, image⟩
    have readout : Metta.instantiate merged (encodeModelAtom yes) =
        encodeModelAtom result :=
      materialization_closed_native outputPaired materialized closed
    have resultClosed : Metta.instantiate merged (encodeModelAtom result) =
        encodeModelAtom result := by
      apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness.instantiate_eq_self_of_vars_nil
      simpa only [Spec.Type.Presentation.encodeModelAtom_vars_eq_typeVars] using closed
    refine ⟨merged, outputPaired, by simp, ?_⟩
    intro fuel
    refine ⟨fuel + 1, [], value, .single ?_,
      observed.trans (readout.trans resultClosed.symm)⟩
    apply coveredPendingStep_singleton (by rfl) (pending := by rfl)
    simpa only [encodeModelAtom, encodeModelAtoms, atomToStack, scopedFinished, finItem] using
      (step_unify environment fuel state (parent :: previous) []
        (encodeModelAtom target) (encodeModelAtom pattern) (encodeModelAtom yes) (encodeModelAtom no) native).trans
        (congrArg (fun items => (items, state)) selectedNative)
  | @chain bindings middle output firstUpdates nextUpdates caller source raw normalized template result name
      first materialized closed next ihFirst ihNext =>
    intro parent previous captured
    let chain : Frame :=
      { atom := encodeModelAtom (.expression [.symbol "chain", source, .var name, template])
        ret := .chain
        vars := chainFrameVars (parent :: previous) (encodeModelAtom source) (encodeModelAtom template) }
    obtain ⟨middleNative, middlePaired, firstReadOnly, firstRun⟩ :=
      ihFirst paired chain (parent :: previous) rfl
    obtain ⟨finalNative, finalPaired, nextReadOnly, laterRun⟩ :=
      ihNext middlePaired parent previous captured
    refine ⟨finalNative, finalPaired, ?_, ?_⟩
    · intro readOnly
      obtain ⟨firstPure, nextPure⟩ := Bool.or_eq_false_iff.mp readOnly
      exact (nextReadOnly nextPure).trans (firstReadOnly firstPure)
    intro fuel
    obtain ⟨laterFuel, scope, finalOperand, later, finalObserved⟩ := laterRun fuel
    obtain ⟨initial, rawScope, rawOperand, firstPath, rawObserved⟩ := firstRun (laterFuel + 2)
    have normalizedNative : Metta.instantiate middleNative rawOperand = encodeModelAtom normalized :=
      rawObserved.trans (materialization_closed_native middlePaired materialized closed)
    let middleItem : Item := ⟨{ atom := .expr [.sym "chain", encodeModelAtom normalized, .var name,
        encodeModelAtom template], ret := .chain, vars := chain.vars } :: parent :: previous, middleNative⟩
    have selected : interpretStack1 environment (laterFuel + 1) state
        (scopedFinished (chain :: parent :: previous) rawOperand middleNative rawScope) =
        ([middleItem], state) := by
      rw [scopedFinished_step]
      simpa only [chain, middleItem, encodeModelAtom, encodeModelAtoms, normalizedNative] using
        step_chain_result environment (laterFuel + 1) state (parent :: previous)
          chain.vars (encodeModelAtom source) rawOperand (encodeModelAtom template) name middleNative
    have applied : interpretStack1 environment laterFuel state middleItem =
        ([⟨atomToStack (encodeModelAtom (substituteName name normalized template))
          (parent :: previous), middleNative⟩], state) := by
      simpa only [middleItem, toLeaTTa_substituteName] using
        step_chain_apply environment laterFuel state (parent :: previous) chain.vars
          (encodeModelAtom normalized) (encodeModelAtom template) name middleNative
    refine ⟨initial, scope, finalOperand, ?_, finalObserved⟩
    change CoveredPendingSteps environment
      (initial, state, [⟨atomToStack (encodeModelAtom source) (chain :: parent :: previous), native⟩]) _
    exact firstPath.trans (.head (coveredPendingStep_singleton (by rfl) selected (by rfl))
      (.head (coveredPendingStep_singleton (by rfl) applied (atomToStack_pending _ _ _ _)) later))
  | @functionReturn bindings output updates caller body returned expression bodyRun ih =>
    intro parent previous captured
    let function : Frame :=
      { atom := encodeModelAtom (.expression [.symbol "function", body])
        ret := .function
        vars := varsCopy (parent :: previous) }
    obtain ⟨finalNative, finalPaired, pureFrame, bodyPath⟩ :=
      ih paired function (parent :: previous) rfl rfl
    refine ⟨finalNative, finalPaired, pureFrame, ?_⟩
    intro fuel
    obtain ⟨initial, scope, operand, path, materialized, terminal⟩ := bodyPath (fuel + 1)
    have finished : interpretStack1 environment fuel state
        (scopedFinished (function :: parent :: previous) operand finalNative scope) =
        ([finItem (parent :: previous) (encodeModelAtom returned) finalNative], state) := by
      rw [scopedFinished_step]
      simpa only [function, functionTerminalResult_return] using
        function_terminal_handler_conformance environment state fuel (parent :: previous)
          function.vars function.atom finalNative caller (.expression [.symbol "return", returned]) operand
          (by simpa using captured) materialized terminal
    refine ⟨initial, [], encodeModelAtom returned, ?_, rfl⟩
    obtain ⟨atoms, rfl⟩ := expression
    change CoveredPendingSteps environment
      (initial, state, [⟨atomToStack (encodeModelAtom (.expression atoms))
        (function :: parent :: previous), native⟩]) _
    exact path.tail (coveredPendingStep_singleton (by rfl) finished (by rfl))
  | @functionNoReturn bindings output updates caller body terminal expression bodyRun missing ih =>
    intro parent previous captured
    let function : Frame :=
      { atom := encodeModelAtom (.expression [.symbol "function", body])
        ret := .function
        vars := varsCopy (parent :: previous) }
    obtain ⟨finalNative, finalPaired, pureFrame, bodyPath⟩ :=
      ih paired function (parent :: previous) rfl rfl
    refine ⟨finalNative, finalPaired, pureFrame, ?_⟩
    intro fuel
    obtain ⟨initial, scope, operand, path, materialized, nativeTerminal⟩ := bodyPath (fuel + 1)
    have finished : interpretStack1 environment fuel state
        (scopedFinished (function :: parent :: previous) operand finalNative scope) =
        ([finItem (parent :: previous) (encodeModelAtom (functionTerminalResult caller terminal)) finalNative], state) := by
      rw [scopedFinished_step]
      exact function_terminal_handler_conformance environment state fuel (parent :: previous)
        function.vars function.atom finalNative caller terminal operand
        (by simpa using captured) materialized nativeTerminal
    refine ⟨initial, [], encodeModelAtom (functionTerminalResult caller terminal), ?_, rfl⟩
    obtain ⟨atoms, rfl⟩ := expression
    change CoveredPendingSteps environment
      (initial, state, [⟨atomToStack (encodeModelAtom (.expression atoms))
        (function :: parent :: previous), native⟩]) _
    exact path.tail (coveredPendingStep_singleton (by rfl) finished (by rfl))
  | terminal source raw normalized run materialized closed sourceTerminal nativeTerminal ih =>
    intro parent previous captured isFunction
    obtain ⟨finalNative, finalPaired, pureFrame, runPath⟩ := ih paired parent previous captured
    refine ⟨finalNative, finalPaired, pureFrame, ?_⟩
    intro fuel
    obtain ⟨initial, scope, operand, path, observed⟩ := runPath fuel
    exact ⟨initial, scope, operand, path,
      observed.trans (materialization_closed_native finalPaired materialized closed), nativeTerminal⟩
  | @resume bindings middle output firstUpdates bodyUpdates caller source raw normalized result
      run materialized closed sourceInstruction nativeInstruction body ihRun ihBody =>
    intro parent previous captured isFunction
    obtain ⟨middleNative, middlePaired, firstReadOnly, firstRun⟩ := ihRun paired parent previous captured
    obtain ⟨finalNative, finalPaired, laterReadOnly, laterRun⟩ :=
      ihBody middlePaired parent previous captured isFunction
    refine ⟨finalNative, finalPaired, ?_, ?_⟩
    · intro readOnly
      obtain ⟨firstPure, nextPure⟩ := Bool.or_eq_false_iff.mp readOnly
      exact (laterReadOnly nextPure).trans (firstReadOnly firstPure)
    intro fuel
    obtain ⟨laterFuel, scope, operand, later, observed, terminal⟩ := laterRun fuel
    obtain ⟨initial, rawScope, rawOperand, first, rawObserved⟩ := firstRun (laterFuel + 1)
    have normalizedNative := rawObserved.trans (materialization_closed_native middlePaired materialized closed)
    have resumed : interpretStack1 environment laterFuel state
        (scopedFinished (parent :: previous) rawOperand middleNative rawScope) =
        ([⟨atomToStack (encodeModelAtom normalized) (parent :: previous), middleNative⟩], state) := by
      rw [scopedFinished_step]
      simp only [interpretStack1, finItem, if_true, normalizedNative, isFunction]
      split
      · rename_i returned same
        simp [same, isEmbeddedOp] at nativeInstruction
      · simp [nativeInstruction]
    exact ⟨initial, scope, operand,
      first.trans (.head (coveredPendingStep_singleton (by rfl) resumed (atomToStack_pending _ _ _ _)) later),
      observed, terminal⟩
/-- The admitted body earns an independent invocation judgment, including the
captured-caller diagnostic when it terminates without return. -/
theorem CoveredControlDerivation.invocation_sound {bindings output : Bindings} {updates : Bool} {body terminal : Atom}
    (derivation : CoveredControlDerivation bindings .body
      (some (.expression [.symbol "function", body])) body terminal output updates)
    (expression : ∃ atoms, body = .expression atoms)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (typing : Spec.Eval.EvalTypeService) (live : List Atom) (caller : Option Atom) :
    CoreInvocationResultRel space dispatch live (.expression [.symbol "function", body])
      bindings (functionTerminalResult caller terminal, output) (typing := typing) (caller := caller) := by
  have source := derivation.sound space dispatch typing (.expression [.symbol "function", body] :: live)
  apply CoreInvocationResultRel.function
  by_cases returning : ∃ value, terminal = .expression [.symbol "return", value]
  · obtain ⟨value, rfl⟩ := returning
    rw [functionTerminalResult_return]
    exact .functionReturn space body value bindings output expression source
  · exact .functionNoReturn space body terminal bindings output expression source
      (fun value same => returning ⟨value, same⟩)

/-- A function invocation starts in the actual native wrapper, with its saved
caller, queued work, earlier completions and instruction receipts. -/
def functionConfiguration (depth : Nat) (state : St) (previous : Stack) (body : Atom)
    (native : Metta.Bindings) (queued : List Item)
    (completed : List (Metta.Atom × Metta.Bindings)) (receipts : List Receipt) : Configuration :=
  { depth := depth
    runtime := state
    pending := evalResult previous (encodeModelAtom (.expression [.symbol "function", body])) native :: queued
    completed := completed
    receipts := receipts }

/-- The source derivation constructs the retained regional invocation. A saved
caller remains pending; an outermost result is published by the native final
classification. Earlier answers and all queued occurrences are preserved. -/
theorem CoveredControlDerivation.invocation_retained {bindings output : Bindings} {updates : Bool} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native) {body terminal : Atom}
    (derivation : CoveredControlDerivation bindings .body
      (some (.expression [.symbol "function", body])) body terminal output updates)
    (expression : ∃ atoms, body = .expression atoms)
    (environment : MinEnv) (state : St) (previous : Stack) (caller : Option Atom)
    (captured : previous.head?.map (fun frame => frame.atom) = caller.map encodeModelAtom)
    (fuel : Nat) (queued : List Item) (completed : List (Metta.Atom × Metta.Bindings))
    (receipts : List Receipt) :
    ∃ nativeOutput, ScopedEquationQuery.BindingInvariant output nativeOutput ∧
    (updates = false → nativeOutput = native) ∧
    let result := finItem previous (encodeModelAtom (functionTerminalResult caller terminal)) nativeOutput
    ∃ depth ticks after,
      (machine environment).run ticks
        (functionConfiguration depth state previous body native queued completed receipts) =
        ((finals [result]).filter (fun pair => pair.1 != emptyA), .exhausted after) ∧
      after.depth = fuel ∧ after.runtime = state ∧
      after.pending = [result].filter (fun item => !isFinal item) ++ queued ∧
      after.completed = completed ++ finals [result] ∧
      ∃ added, after.receipts = receipts ++ added ∧
        ∀ receipt ∈ added, Receipt.Valid environment receipt := by
  let function : Frame :=
    { atom := encodeModelAtom (.expression [.symbol "function", body])
      ret := .function
      vars := varsCopy previous }
  obtain ⟨nativeOutput, outputPaired, readOnly, bodyPath⟩ :=
    CoveredControlDerivation.realizes paired derivation environment state function previous rfl rfl
  refine ⟨nativeOutput, outputPaired, readOnly, ?_⟩
  intro result
  obtain ⟨depth, scope, operand, path, materialized, terminalNative⟩ := bodyPath (fuel + 1)
  have initial : ⟨atomToStack (encodeModelAtom body) (function :: previous), native⟩ =
      evalResult previous (encodeModelAtom (.expression [.symbol "function", body])) native := by
    obtain ⟨atoms, rfl⟩ := expression
    rfl
  rw [initial] at path
  obtain ⟨ticks, added, checked, retained⟩ := path.retained queued completed receipts
  let saved := ofPending (fuel + 1, state,
    [scopedFinished (function :: previous) operand nativeOutput scope]) queued completed (receipts ++ added)
  have finished : interpretStack1 environment fuel state
      (scopedFinished (function :: previous) operand nativeOutput scope) = ([result], state) := by
    rw [scopedFinished_step]
    exact function_terminal_handler_conformance environment state fuel previous function.vars function.atom
      nativeOutput caller terminal operand captured materialized terminalNative
  let after := advance environment saved fuel
    (scopedFinished (function :: previous) operand nativeOutput scope) queued
  have last : (machine environment).run 1 saved =
      ((finals [result]).filter (fun pair => pair.1 != emptyA), .exhausted after) := by
    rw [run_succ_ready environment saved _ queued rfl fuel rfl (by rfl) 0]
    simp only [Machine.run, emitted, saved, ofPending, finished, List.append_nil]
    rfl
  refine ⟨depth, ticks + 1, after, ?_, rfl, ?_, ?_, ?_,
    added ++ [⟨state, scopedFinished (function :: previous) operand nativeOutput scope, [result], state⟩], ?_, ?_⟩
  · rw [(machine environment).run_add]
    change (machine environment).continueRun 1
      ((machine environment).run ticks (ofPending
        (depth, state, [evalResult previous (encodeModelAtom (.expression [.symbol "function", body])) native])
        queued completed receipts)) = _
    rw [retained]
    simpa only [Machine.continueRun, List.nil_append] using last
  · simp only [after, advance, saved, ofPending, finished]
  · simp only [after, advance, saved, ofPending, finished]
  · simp only [after, advance, saved, ofPending, finished]
  · simp only [after, advance, saved, ofPending, finished, List.append_assoc]
  · intro receipt member
    rcases List.mem_append.mp member with member | member
    · exact checked receipt member
    · obtain rfl := List.mem_singleton.mp member
      refine ⟨by rfl, ?_⟩
      intro other
      exact (stepReady_independent environment state _ other fuel (by rfl)).trans finished

theorem CoveredControlDerivation.invocation_completed {bindings output : Bindings} {updates : Bool} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native) {body terminal : Atom}
    (derivation : CoveredControlDerivation bindings .body
      (some (.expression [.symbol "function", body])) body terminal output updates)
    (expression : ∃ atoms, body = .expression atoms)
    (environment : MinEnv) (state : St) :
    ∃ nativeOutput, ScopedEquationQuery.BindingInvariant output nativeOutput ∧
    (updates = false → nativeOutput = native) ∧ ∃ depth ticks final,
      (machine environment).run ticks (functionConfiguration depth state [] body native [] [] []) =
        (([(Metta.instantiate nativeOutput (encodeModelAtom (functionTerminalResult none terminal)), nativeOutput)]).filter
          (fun pair => pair.1 != emptyA), .finished final) ∧
      final.runtime = state ∧
      ∀ extra, interpretFuel environment (depth + extra) state
        [evalResult [] (encodeModelAtom (.expression [.symbol "function", body])) native] [] =
        (final.published, state) := by
  obtain ⟨nativeOutput, outputPaired, readOnly, depth, ticks, final, ran, finalDepth, world, pending, completed, history⟩ :=
    derivation.invocation_retained paired expression environment state [] none rfl 0 [] [] []
  have empty : final.pending = [] := by simpa [finItem, isFinal] using pending
  have done : (machine environment).run (ticks + 1)
      (functionConfiguration depth state [] body native [] [] []) =
      (([(Metta.instantiate nativeOutput (encodeModelAtom (functionTerminalResult none terminal)), nativeOutput)]).filter
        (fun pair => pair.1 != emptyA), .finished final) := by
    rw [(machine environment).run_add, ran]
    simp only [Machine.continueRun, empty_finished environment final empty 0, List.append_nil]
    simp only [finals, finItem, isFinal, List.filter_cons, if_true, List.filter_nil, List.map_cons, List.map_nil, finalPair]
  refine ⟨nativeOutput, outputPaired, readOnly, depth, ticks + 1, final, done, world, ?_⟩
  intro extra
  have stable := completed_interpreter_all_depths environment (ticks + 1)
    (functionConfiguration depth state [] body native [] [] []) final _ done extra
  simpa only [functionConfiguration, List.reverse_nil, world] using stable

namespace RetainedControls

private def returned : Atom := .expression [.symbol "return", .symbol "A"]
private def nested : Atom :=
  .expression [.symbol "chain", .expression [.symbol "function", returned], .var "x",
    .expression [.symbol "chain", .expression [.symbol "cons-atom", .var "x", .expression []], .var "ys",
      .expression [.symbol "return", .var "ys"]]]

private theorem closed_materialization (bindings : Bindings)
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings) (atom : Atom)
    (closed : TypeSubst.typeVars atom = []) : BindingMaterializationRel bindings atom atom :=
  (BindingMaterializationRel.closed_iff bindings atom atom closed).mpr ⟨rfl, model⟩

/-- The nested control program is admitted for any satisfiable incoming frame,
including nonempty caller bindings unrelated to its local chain binders. -/
theorem nested_body (bindings : Bindings)
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    CoveredControlDerivation bindings .body (some (.expression [.symbol "function", nested])) nested
      (.expression [.symbol "return", .expression [.symbol "A"]]) bindings false := by
  have returnBody (caller : Option Atom) :
      CoveredControlDerivation bindings .body caller returned returned bindings false :=
    .terminal returned returned returned (.data returned (by rfl) (by rfl))
      (closed_materialization bindings model returned (by rfl)) (by rfl) (by rfl) (by rfl)
  have inner (caller : Option Atom) : CoveredControlDerivation bindings .run caller
      (.expression [.symbol "function", returned]) (.symbol "A") bindings false :=
    .functionReturn returned (.symbol "A") ⟨_, rfl⟩ (returnBody _)
  let final := Atom.expression [.symbol "return", .expression [.symbol "A"]]
  let rest := Atom.expression [.symbol "chain", .expression [.symbol "cons-atom", .symbol "A", .expression []],
    .var "ys", .expression [.symbol "return", .var "ys"]]
  have tail (caller : Option Atom) : CoveredControlDerivation bindings .run caller rest final bindings false := by
    apply CoveredControlDerivation.chain _ (.expression [.symbol "A"]) (.expression [.symbol "A"])
      _ _ "ys" (.cons (.symbol "A") [])
      (closed_materialization bindings model _ (by rfl)) (by rfl)
    simpa [substituteName, final] using
      (CoveredControlDerivation.data (bindings := bindings) (caller := caller) final (by rfl) (by rfl))
  have run : CoveredControlDerivation bindings .run
      (some (.expression [.symbol "function", nested])) nested final bindings false := by
    apply CoveredControlDerivation.chain _ (.symbol "A") (.symbol "A") _ _ "x" (inner _)
      (closed_materialization bindings model _ rfl) rfl
    simpa [substituteName, rest] using tail (some (.expression [.symbol "function", nested]))
  exact .terminal nested final final run (closed_materialization bindings model _ rfl) rfl rfl rfl

/-- Cons constructs an instruction, which the actual function handler resumes;
that instruction in turn constructs the return marker. -/
theorem generated_instruction_body (bindings : Bindings)
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings) (caller : Option Atom) :
    let source := Atom.expression [.symbol "cons-atom", .symbol "cons-atom",
      .expression [.symbol "return", .expression [.symbol "A"]]]
    CoveredControlDerivation bindings .body caller source returned bindings false := by
  intro source
  let generated := Atom.expression [.symbol "cons-atom", .symbol "return", .expression [.symbol "A"]]
  apply CoveredControlDerivation.resume source generated generated returned
    (.cons (.symbol "cons-atom") [.symbol "return", .expression [.symbol "A"]])
    (closed_materialization bindings model _ rfl) rfl rfl rfl
  exact .terminal generated returned returned (.cons (.symbol "return") [.symbol "A"])
    (closed_materialization bindings model _ rfl) rfl rfl rfl

/-- The general source/retained theorem applies to the constructed nested body,
not only a separately hand-evaluated fixture. -/
theorem nested_completed (bindings : Bindings) (native : Metta.Bindings)
    (paired : ScopedEquationQuery.BindingInvariant bindings native)
    (environment : MinEnv) (state : St) :
    ∃ depth ticks final,
      (machine environment).run ticks (functionConfiguration depth state [] nested native [] [] []) =
        ([(.expr [.sym "A"], native)], .finished final) ∧ final.runtime = state := by
  have model := QueryBindingProjection.binding_theory_satisfiable paired.semantic
  obtain ⟨actual, actualPaired, readOnly, depth, ticks, final, ran, world, stable⟩ :=
    (nested_body bindings model).invocation_completed paired ⟨_, rfl⟩ environment state
  have unchanged := readOnly rfl
  subst actual
  refine ⟨depth, ticks, final, ?_, world⟩
  simpa [functionTerminalResult, encodeModelAtom, encodeModelAtoms, Metta.instantiate,
    Metta.Bindings.resolveAtom, emptyA,
    show ((.expr [.sym "A"] : Metta.Atom) != .sym "Empty") = true by decide] using ran

private def environment := MinEnv.ofAtomsGT [] Metta.Builtins.table
private def loaded (depth : Nat) := functionConfiguration depth St.init [] nested [] [] [] []

private def status : Outcome Configuration Configuration Request → String
  | .finished _ => "finished"
  | .exhausted _ => "scheduler"
  | .suspended .interpreterDepth _ => "depth"
  | .suspended .nestedEvaluation _ => "nested"
  | .faulted => "fault"
  | .stuck _ => "stuck"

#guard ((machine environment).run 30 (loaded 30)).1 == [(.expr [.sym "A"], [])]
#guard status ((machine environment).run 30 (loaded 30)).2 == "finished"
#guard status ((machine environment).run 0 (loaded 30)).2 == "scheduler"
#guard status ((machine environment).run 30 (loaded 0)).2 == "depth"
#guard (continueRun environment 30 30 ((machine environment).run 30 (loaded 0))).1 == [(.expr [.sym "A"], [])]

private def emptyBody : Atom := .expression [.symbol "return", .symbol "Empty"]
private def emptyLoaded (depth : Nat) := functionConfiguration depth St.init [] emptyBody [] [] [] []
#guard ((machine environment).run 5 (emptyLoaded 5)).1 == []
#guard status ((machine environment).run 5 (emptyLoaded 5)).2 == "finished"
#guard status ((machine environment).run 5 (emptyLoaded 0)).2 == "depth"

private def nestedRequest : Configuration :=
  ⟨8, St.init, [⟨atomToStack (.expr [.sym "capture", .sym "work"]) [], []⟩], [], []⟩
#guard status ((machine environment).run 8 nestedRequest).2 == "nested"
#guard status (continueRun environment 8 100 ((machine environment).run 8 nestedRequest)).2 == "nested"

/-- Native self-import expansion has its own fixed depth bound. It remains
pending instead of being mistaken for complete dependency loading. -/
private def importRequest : Configuration :=
  ⟨8, St.init, [⟨atomToStack (.expr [.sym "import!", .sym "&self", .sym "module"]) [], []⟩], [], []⟩
#guard status ((machine environment).run 8 importRequest).2 == "nested"

private def duplicate : Configuration :=
  let item := evalResult [] (encodeModelAtom (.expression [.symbol "function", returned])) []
  ⟨8, St.init, [item, item], [], []⟩
#guard ((machine environment).run 2 duplicate).1 == [(.sym "A", [])]
#guard status ((machine environment).run 2 duplicate).2 == "scheduler"
#guard ((machine environment).continueRun 3 ((machine environment).run 2 duplicate)).1 ==
  [(.sym "A", []), (.sym "A", [])]

private def allocate : Configuration :=
  ⟨2, St.init, [⟨atomToStack (.expr [.sym "new-state", .sym "stored"]) [], []⟩], [], []⟩
#guard match ((machine environment).run 1 allocate).2 with
  | .exhausted saved => saved.runtime.counter == 1 && saved.receipts.length == 1 &&
      saved.runtime.world.store[0]? == some (.sym "stored")
  | _ => false
#guard match ((machine environment).continueRun 1 ((machine environment).run 1 allocate)).2 with
  | .finished saved => saved.runtime.counter == 1 && saved.receipts.length == 1 &&
      saved.runtime.world.store[0]? == some (.sym "stored")
  | _ => false

private def guarded : Configuration :=
  ⟨8, St.init, [evalResult [] (.expr [.sym "function",
    .expr [.sym "unify", .sym "same", .sym "same",
      .expr [.sym "return", .sym "chosen"], .expr [.sym "capture", .sym "unselected"]]]) []], [], []⟩
#guard ((machine environment).run 8 guarded).1 == [(.sym "chosen", [])]
#guard status ((machine environment).run 8 guarded).2 == "finished"

private def malformed : Configuration :=
  ⟨2, St.init, [evalResult [] (.expr [.sym "function"]) []], [], []⟩
#guard ((machine environment).run 2 malformed).1 ==
  [(errAtom (.expr [.sym "function"]) "function: expected (function <expression>)", [])]

end RetainedControls


namespace RetainedBindingControls
private def reuseTemplate (name : String) : Atom :=
  .expression [.symbol "cons-atom", .symbol "return",
    .expression [.expression [.symbol "pair", .var name, .var name]]]
private def reuseBody (name : String) : Atom :=
  .expression [.symbol "unify", .var name, .symbol "A", reuseTemplate name,
    .expression [.symbol "return", .symbol "refused"]]
private def reused : Atom := .expression [.symbol "pair", .symbol "A", .symbol "A"]
private def normalizedTemplate : Atom :=
  .expression [.symbol "cons-atom", .symbol "return", .expression [reused]]
private def reuseNested (name : String) : Atom :=
  .expression [.symbol "chain", .expression [.symbol "function", reuseBody name], .var "pair-result",
    .expression [.symbol "return", .var "pair-result"]]

/-- An independent finite unification proof supplies the changed binding
frame used at both occurrences in the following constructor instruction. -/
theorem binding_reuse_body {bindings output : Bindings} (name : String)
    (candidate : Spec.Eval.Steps.UnifyCandidateRel (.var name) (.symbol "A") bindings output)
    (nonvariable : HEAssignmentsNonVariable output) :
    CoveredControlDerivation bindings .body (some (.expression [.symbol "function", reuseBody name]))
      (reuseBody name) (.expression [.symbol "return", reused]) output true := by
  obtain ⟨matched, matching, merging⟩ := candidate
  have satisfiable : ∃ valuation, TypeBindingSatisfied valuation output := merging.2
  have fixed : ∀ valuation, TypeBindingSatisfied valuation output → valuation name = .symbol "A" := by
    intro valuation modelSatisfied
    have split := (merging.solutions valuation).mp modelSatisfied
    have same := (Spec.Match.SolutionTheory.matchRel_solution_iff matching _).mp
      (heBindingSatisfied_of_specTypeBindingSatisfied split.1)
    have decoded := congrArg decodeModelAtom same
    simpa only [HEAtomEquationSatisfied, encodeModelAtom, applyClassSolution,
      decodeModelAtom_encodeModelAtom, decodeModelAtom] using decoded
  have materialized : BindingMaterializationRel output (reuseTemplate name) normalizedTemplate := by
    apply BindingMaterializationRel.of_model_constant satisfiable
    intro valuation sat
    simp only [reuseTemplate, normalizedTemplate, reused, applyTypeValuation, List.map_cons, List.map_nil, fixed valuation sat]
  have closedResult : BindingMaterializationRel output
      (.expression [.symbol "return", reused]) (.expression [.symbol "return", reused]) :=
    (BindingMaterializationRel.closed_iff _ _ _ (by rfl)).mpr ⟨rfl, satisfiable⟩
  have normalizedSelf : BindingMaterializationRel output normalizedTemplate normalizedTemplate :=
    (BindingMaterializationRel.closed_iff _ _ _ (by rfl)).mpr ⟨rfl, satisfiable⟩
  have first : CoveredControlDerivation bindings .run
      (some (.expression [.symbol "function", reuseBody name]))
      (reuseBody name) normalizedTemplate output true := by
    simpa [reuseBody] using
      (CoveredControlDerivation.unifySuccess (.var name) (.symbol "A") (reuseTemplate name)
      (.expression [.symbol "return", .symbol "refused"]) normalizedTemplate
      ⟨matched, matching, merging⟩ materialized (by rfl) nonvariable)
  exact .resume (reuseBody name) normalizedTemplate normalizedTemplate _
    first normalizedSelf (by rfl) (by rfl) (by rfl)
    (.terminal normalizedTemplate _ _ (.cons (.symbol "return") [reused]) closedResult (by rfl) (by rfl) (by rfl))

/-- A nested function carries the changed frame through its captured caller
and a second enclosing continuation. -/
theorem binding_reuse_nested_body {bindings output : Bindings} (name : String)
    (candidate : Spec.Eval.Steps.UnifyCandidateRel (.var name) (.symbol "A") bindings output)
    (nonvariable : HEAssignmentsNonVariable output) :
    CoveredControlDerivation bindings .body (some (.expression [.symbol "function", reuseNested name]))
      (reuseNested name) (.expression [.symbol "return", reused]) output true := by
  have model : ∃ valuation, TypeBindingSatisfied valuation output :=
    candidate.choose_spec.2.2
  have pairMaterialized : BindingMaterializationRel output reused reused :=
    (BindingMaterializationRel.closed_iff _ _ _ (by rfl)).mpr ⟨rfl, model⟩
  have returnedMaterialized : BindingMaterializationRel output
      (.expression [.symbol "return", reused]) (.expression [.symbol "return", reused]) :=
    (BindingMaterializationRel.closed_iff _ _ _ (by rfl)).mpr ⟨rfl, model⟩
  apply CoveredControlDerivation.terminal (reuseNested name) _ _ (materialized := returnedMaterialized)
    (closed := by rfl) (sourceTerminal := by rfl) (nativeTerminal := by rfl)
  apply CoveredControlDerivation.chain _ reused reused _ _ "pair-result"
    (.functionReturn (reuseBody name) reused ⟨_, rfl⟩
      (binding_reuse_body name candidate nonvariable)) pairMaterialized (by rfl)
  simpa [substituteName] using
    (CoveredControlDerivation.data (bindings := output)
      (caller := some (.expression [.symbol "function", reuseNested name]))
      (.expression [.symbol "return", reused]) (by rfl) (by rfl))

/-- The general changed-binding theorem, instantiated by a genuine composed
source derivation. The output frame is the actual reached native record. -/
theorem binding_reuse_nested_completed {bindings output : Bindings} {native : Metta.Bindings}
    (paired : ScopedEquationQuery.BindingInvariant bindings native) (name : String)
    (candidate : Spec.Eval.Steps.UnifyCandidateRel (.var name) (.symbol "A") bindings output)
    (nonvariable : HEAssignmentsNonVariable output)
    (environment : MinEnv) (state : St) :
    ∃ nativeOutput, ScopedEquationQuery.BindingInvariant output nativeOutput ∧
      ∃ depth ticks final,
        (machine environment).run ticks
          (functionConfiguration depth state [] (reuseNested name) native [] [] []) =
          ([(.expr [.sym "pair", .sym "A", .sym "A"], nativeOutput)], .finished final) ∧
        final.runtime = state := by
  obtain ⟨actual, actualPaired, _, depth, ticks, final, ran, world, _⟩ :=
    (binding_reuse_nested_body name candidate nonvariable).invocation_completed
      paired ⟨_, rfl⟩ environment state
  refine ⟨actual, actualPaired, depth, ticks, final, ?_, world⟩
  simpa [functionTerminalResult, reused, encodeModelAtom, encodeModelAtoms, Metta.instantiate,
    Metta.Bindings.resolveAtom, emptyA,
    show ((.expr [.sym "pair", .sym "A", .sym "A"] : Metta.Atom) != .sym "Empty") = true by decide] using ran

private def incoming : Bindings := Bindings.empty.assign "caller" (.symbol "kept")
private def selected : Bindings := Bindings.empty.assign "x" (.symbol "A")
private def reached : Bindings := selected.assign "caller" (.symbol "kept")
private def nativeIncoming : Metta.Bindings := [.val "caller" (.sym "kept")]
private def environment := MinEnv.ofAtomsGT [] Metta.Builtins.table

/-- The composed positive witness obtains its unifier from an actual
independent match and merge, retaining a different caller binding. -/
theorem reuse_candidate : Spec.Eval.Steps.UnifyCandidateRel (.var "x") (.symbol "A") incoming reached := by
  refine ⟨selected, ?_, ?_⟩
  · apply Spec.Match.Merge.MatchRel.varNonVar (by rfl)
    exact Spec.Match.Merge.semanticLoopFree_single_assignment
      (by intro occurs; cases occurs)
  · apply Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
    let valuation : String → Atom :=
      fun name => if name = "x" then .symbol "A" else .symbol "kept"
    refine ⟨valuation, ?_, ?_⟩
    · simp [selected, TypeBindingSatisfied, Bindings.empty, Bindings.assign,
        Bindings.isBound, Bindings.lookup, applyTypeValuation, valuation]
    · simp [incoming, TypeBindingSatisfied, Bindings.empty, Bindings.assign,
        Bindings.isBound, Bindings.lookup, applyTypeValuation, valuation]

private theorem reached_nonvariable : HEAssignmentsNonVariable reached := by
  intro key target member
  have shape : reached.assignments =
      [("x", .symbol "A"), ("caller", .symbol "kept")] := by
    decide +kernel
  rw [shape] at member
  simp at member

private theorem incoming_paired : ScopedEquationQuery.BindingInvariant incoming nativeIncoming := by
  have image : LeaBindingsHEImage nativeIncoming := by
    intro key value member
    have same : key = "caller" ∧ value = .sym "kept" := by simpa [nativeIncoming] using member
    obtain ⟨rfl, rfl⟩ := same
    exact leaAtomHEImage_sym "kept"
  have runtime : LeaTTaSpecConformance.LeaRuntimeBindingInvariant nativeIncoming := by
    apply LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty.merge (right := nativeIncoming)
    · intro key value member
      have same : key = "caller" ∧ value = .sym "kept" := by simpa [nativeIncoming] using member
      obtain ⟨rfl, rfl⟩ := same
      simp [MettaAtomNoFloat]
    · simp [nativeIncoming, Metta.Bindings.empty, Metta.Bindings.merge,
        Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
        Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder, Metta.Bindings.lookupVal,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal]
    · exact Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simpa [incoming, nativeIncoming, QueryBindingProjection.project, Bindings.assign, Bindings.isBound, Bindings.lookup,
    Bindings.empty, List.filterMap_cons, List.filterMap_nil, leaEqualityEdges, decodeModelAtom] using
    QueryBindingProjection.paired nativeIncoming image runtime

theorem reuse_with_caller_completed (environment : MinEnv) (state : St) :
    ∃ nativeOutput, ScopedEquationQuery.BindingInvariant reached nativeOutput ∧
      ∃ depth ticks final,
        (machine environment).run ticks
          (functionConfiguration depth state [] (reuseNested "x") nativeIncoming [] [] []) =
          ([(.expr [.sym "pair", .sym "A", .sym "A"], nativeOutput)], .finished final) ∧
        final.runtime = state :=
  binding_reuse_nested_completed incoming_paired "x" reuse_candidate
    reached_nonvariable environment state

private def loaded := functionConfiguration 30 St.init [] (reuseNested "x") nativeIncoming [] [] []
#guard ((machine environment).run 30 loaded).1 ==
  [(.expr [.sym "pair", .sym "A", .sym "A"], [.val "x" (.sym "A"), .val "caller" (.sym "kept")])]
#guard match ((machine environment).run 30 loaded).2 with
  | .finished final => final.runtime.counter == 0
  | _ => false
#guard ((machine environment).continueRun 30 ((machine environment).run 2 loaded)).1 ==
  ((machine environment).run 32 loaded).1

private def incompatible : Bindings := incoming.assign "x" (.symbol "B")
private def incompatibleNative : Metta.Bindings :=
  [.val "x" (.sym "B"), .val "caller" (.sym "kept")]

/-- A successful pattern match cannot override an incompatible retained
binding; the common-model condition rules out the success branch. -/
theorem incompatible_binding_refuses :
    Spec.Eval.Steps.UnifyNoMatchRel (.var "x") (.symbol "A") incompatible := by
  rintro output ⟨matched, matching, merging⟩
  obtain ⟨valuation, matchedModel, incomingModel⟩ := merging.common_model
  have newValue := (Spec.Match.SolutionTheory.matchRel_solution_iff matching
    (fun name => encodeModelAtom (valuation name))).mp
      (heBindingSatisfied_of_specTypeBindingSatisfied matchedModel)
  have incomingSatisfied := heBindingSatisfied_of_specTypeBindingSatisfied incomingModel
  have oldValue := incomingSatisfied.1 "x" (.symbol "B") (by decide)
  simp only [encodeModelAtom, applyClassSolution] at newValue oldValue
  have impossible := newValue.symm.trans oldValue
  simp at impossible

/-- A residual name cannot be silently replaced by the desired concrete
answer. Independent materialization still observes unconstrained models. -/
theorem residual_template_not_concrete :
    ¬BindingMaterializationRel Bindings.empty (reuseTemplate "x") normalizedTemplate := by
  intro materialized
  have model : TypeBindingSatisfied (fun _ => .symbol "B") Bindings.empty := by
    constructor <;> simp [Bindings.empty]
  have same := materialized.preserves_model _ model
  simp [reuseTemplate, normalizedTemplate, reused, applyTypeValuation] at same

private def refusedLoaded := functionConfiguration 30 St.init [] (reuseNested "x") incompatibleNative [] [] []
#guard ((machine environment).run 30 refusedLoaded).1 == [(.sym "refused", incompatibleNative)]
#guard ((machine environment).run 3 loaded).1 == []
#guard match ((machine environment).run 3 loaded).2 with
  | .exhausted saved => saved.pending.any (fun item => item.bnd.any
      (fun relation => relation == .val "x" (.sym "A")))
  | _ => false


end RetainedBindingControls

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalInstructionConformance

/-! ## Equation-query completion through this module's carriers

These composites use the raw-completion and covered-control laws above, so
they live with them rather than in `LeaTTaScopedQuery`. -/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Match.Merge Spec.Eval.Steps

/-- Actual query soundness composes with the guarded raw completion lane.
No second merge or ordinary evaluation is inserted at this boundary. -/
theorem queryOpItemsOfRule_raw_completion
    {space : Space} {previous : Metta.Minimal.Stack} {query lhs rhs : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs)) :
    ∃ emitted output merged,
      EquationQueryCandidateRel space (liveScope previous) query
        (QueryBindingProjection.project incoming) emitted output ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      ((∀ tail, encodeModelAtom emitted ≠ .expr (.sym "function" :: tail)) →
      ∀ dispatch typing caller,
        Spec.Eval.Minimal.CoreInvocationResultRel space dispatch (liveScope previous)
          emitted output (emitted, output) (typing := typing) (caller := caller) ∧
        item = Metta.Minimal.finItem previous (encodeModelAtom emitted) merged) := by
  obtain ⟨emitted, output, merged, candidate, itemEq, paired, _, _⟩ :=
    queryOpItemsOfRule_sound stored image runtime member
  refine ⟨emitted, output, merged, candidate, paired, ?_⟩
  intro raw dispatch typing caller
  have completed := LeaTTaMinimalInstructionConformance.raw_completion_of_not_function_head
    (caller := caller)
    space dispatch (liveScope previous) typing emitted output previous merged raw
  exact ⟨completed.1, itemEq.trans completed.2⟩

open Metta.Minimal
open LeaTTaMinimalControlExecution LeaTTaMinimalControlExecution.Retained
open LeaTTaMinimalInstructionConformance
open Spec.Eval.Minimal Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory

/-- Source evidence for a scanned occurrence composes with the existing
function-body derivation and actual retained handler. Closed materialization
is the exact-name boundary here; general open results retain their separate
alpha observation rather than being identified with a chosen spelling. -/
theorem queryWork_function_invocation
    {atoms added imported : List Atom} {previous : Stack} {query : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {occurrence : QueryOccurrence}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : occurrence ∈ queryWork previous query incoming counter
      (candidateRules atoms added imported query)) :
    ∃ rawRhs output merged,
      EquationQueryCandidateRel (Space.ofList (atoms ++ added ++ imported))
        (liveScope previous) query (QueryBindingProjection.project incoming) rawRhs output ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      ∀ body terminal finalBindings updates,
        BindingMaterializationRel output rawRhs (.expression [.symbol "function", body]) →
        TypeSubst.typeVars (.expression [.symbol "function", body]) = [] →
        CoveredControlDerivation output .body (some (.expression [.symbol "function", body]))
          body terminal finalBindings updates →
        (∃ entries, body = .expression entries) →
        ∀ environment state outerCaller,
        previous.head?.map (fun frame => frame.atom) = some (encodeModelAtom query) →
        ∀ dispatch typing,
        ¬HostCall dispatch query → embeddedInstruction query = false →
        CoreInvocationRel (Space.ofList (atoms ++ added ++ imported)) dispatch (liveScope previous)
          query (QueryBindingProjection.project incoming)
          (functionTerminalResult (some query) terminal, finalBindings)
          (typing := typing) (caller := outerCaller) ∧
        ∀ fuel queued completed receipts,
        ∃ nativeFinal, ScopedEquationQuery.BindingInvariant finalBindings nativeFinal ∧
        (updates = false → nativeFinal = merged) ∧
        let result := finItem previous
          (encodeModelAtom (functionTerminalResult (some query) terminal)) nativeFinal
        ∃ depth ticks after,
          (machine environment).run ticks
            (⟨depth, state, occurrence.item :: queued, completed, receipts⟩ : Configuration) =
            ((finals [result]).filter (fun pair => pair.1 != emptyA), .exhausted after) ∧
          after.depth = fuel ∧ after.runtime = state ∧
          after.pending = [result].filter (fun item => !isFinal item) ++ queued ∧
          after.completed = completed ++ finals [result] ∧
          ∃ appended, after.receipts = receipts ++ appended ∧
            ∀ receipt ∈ appended, Receipt.Valid environment receipt := by
  obtain ⟨emitted, output, merged, pattern, rawRhs, matched, source, item, _, paired, emittedEq⟩ :=
    queryWork_sound image runtime member
  have candidate : EquationQueryCandidateRel (Space.ofList (atoms ++ added ++ imported))
      (liveScope previous) query (QueryBindingProjection.project incoming) rawRhs output := by
    refine ⟨pattern, rawRhs, matched,
      ⟨occurrence.rule.lhs, occurrence.rule.rhs, List.mem_of_getElem? source.stored, source.selected⟩,
      source.result.1, ?_⟩
    intro valuation satisfied
    rfl
  refine ⟨rawRhs, output, merged, candidate, paired, ?_⟩
  intro body terminal finalBindings updates materialized closed derivation expression
    environment state outerCaller captured dispatch typing notHost ordinary
  constructor
  · exact .equation _ query rawRhs _ _ output _ notHost ordinary candidate
      (.historical _ _) materialized
      (derivation.invocation_sound expression _ dispatch typing
        (liveScope previous) (some query))
  · intro fuel queued completed receipts
    have readout := materialization_closed_native paired materialized closed
    rw [emittedEq, readout, decodeModelAtom_encodeModelAtom] at item
    obtain ⟨nativeFinal, finalPaired, readOnly, depth, ticks, after, ran, depthEq,
      world, pending, done, history⟩ :=
      derivation.invocation_retained paired expression environment state previous
        (some query) captured
        fuel queued completed receipts
    refine ⟨nativeFinal, finalPaired, readOnly, depth, ticks, after, ?_, depthEq, world, pending, done, history⟩
    simpa only [functionConfiguration, ← item] using ran

end Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery
