import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices
import Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServiceWire
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Gradual
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Optional declared-calculus service comparisons in extended HE and PeTTa

The two reserved calls invoke the existing scoped rho packet service and the
original binding-equation packet service. Requests and replies are grounded
strings in the existing exact wire alphabet. The binding-equation service is
fixed to a literal scope and authored declaration header.

HE uses its existing grounded dispatch. PeTTa gains two call transitions on
its existing configuration carrier; every other transition is the original
source evaluator. The extension preserves the store, continuations, input and
output at each native service transition. Argument evaluation remains the
source evaluator's responsibility.

This is an opt-in service extension, not a whole-dialect type embedding or a
qualification of the live Rust or Prolog implementations. Gradual type
compatibility is kept separate from native conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.NativeDialectKernelServices

open Mettapedia.Languages.MeTTa.PrimeComparisons.Rho

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef TypeExpr TypeDecl GrammarRule)
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily (DeclaredAxiom)
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- The two installed services use their existing packet formats. -/
inductive Service where
  | rho
  | bindingEquation
  deriving DecidableEq, Repr

namespace Service

def head : Service → String
  | .rho => "prime:rho"
  | .bindingEquation => "prime:binding-equation"

def readHead : String → Option Service
  | "prime:rho" => some .rho
  | "prime:binding-equation" => some .bindingEquation
  | _ => none

@[simp] theorem readHead_head (service : Service) : readHead service.head = some service := by
  cases service <;> rfl

theorem head_injective : Function.Injective head := by
  intro first second equal
  have same := congrArg readHead equal
  simpa only [readHead_head, Option.some.injEq] using same

end Service

/-- A selected binding profile is admitted through the existing exact
header codec. It authorizes declared constructors and their derived laws,
without importing arbitrary rewrite or conditional-rule authority. -/
def readBindingProfile? (text : String) : Option (Lean.Name × LanguageDef) := do
  let word ← Binary.Text.parse text
  let (scope, header) ← Binary.canonicalDecodeWith Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.profileCodec word
  some (scope, Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.profileLanguage header)

theorem readBindingProfile_encoded (scope : Lean.Name)
    (header : String × List TypeDecl × List GrammarRule) :
    readBindingProfile? (Binary.Text.render (Binary.encodeWith Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.profileCodec
      (scope, header))) = some (scope, Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.profileLanguage header) := by
  simp only [readBindingProfile?, Binary.Text.parse_render, Binary.canonicalDecodeWith_encodeWith,
    Bind.bind, Option.bind]

/-- Whole-packet execution is the existing implementation, with no adapter
substitution, normalization or replacement checker. -/
def run (scope : Lean.Name) (language : LanguageDef) : Service →
    List Binary.Alphabet → Option (List Binary.Alphabet)
  | .rho => ScopedServiceWire.run
  | .bindingEquation => Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.run scope language

/-- The accepted source/native observations are independent of dialect call
execution. Each reply binds its original complete packet. -/
def PacketMeaning (scope : Lean.Name) (language : LanguageDef) :
    Service → List Binary.Alphabet → List Binary.Alphabet → Prop
  | .rho, input, output => ∃ value result,
      ScopedServiceWire.encodeRequest value = input ∧
      ScopedServiceWire.ReplyMeaning value result ∧
      Binary.encodeData (.pair (ScopedServiceWire.packet.put value) result) = output
  | .bindingEquation, input, output => ∃ value result,
      Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.encodeRequest value = input ∧
      Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.ReplyMeaning scope language value result ∧
      Binary.encodeData (.pair (Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.packetCodec.put value) result) = output

theorem run_sound (scope : Lean.Name) (language : LanguageDef) (service : Service)
    (input output : List Binary.Alphabet) (accepted : run scope language service input = some output) :
    PacketMeaning scope language service input output := by
  cases service with
  | rho => exact ScopedServiceWire.run_sound input output accepted
  | bindingEquation =>
      obtain ⟨value, result, inputBound, outputBound, meaning⟩ :=
        Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.run_sound scope language input output accepted
      exact ⟨value, result, inputBound, meaning, outputBound.symm⟩

def textAtom (text : String) : Atom := .grounded (.string text)

/-- Argument arity and grounded string shape are checked before the exact
shared alphabet parser. Malformed or rejected packets produce no answer. -/
def invoke? (scope : Lean.Name) (language : LanguageDef) (service : Service) :
    List Atom → Option Atom
  | [.grounded (.string text)] => do
      let input ← Binary.Text.parse text
      let output ← run scope language service input
      some (textAtom (Binary.Text.render output))
  | _ => none

/-- Independent packet authority plus the literal input and output strings. -/
def ReplyMeaning (scope : Lean.Name) (language : LanguageDef) (service : Service)
    (arguments : List Atom) (reply : Atom) : Prop :=
  ∃ text input output,
    arguments = [textAtom text] ∧ Binary.Text.parse text = some input ∧
    PacketMeaning scope language service input output ∧ reply = textAtom (Binary.Text.render output)

theorem invoke_sound (scope : Lean.Name) (language : LanguageDef) (service : Service)
    (arguments : List Atom) (reply : Atom) (accepted : invoke? scope language service arguments = some reply) :
    ReplyMeaning scope language service arguments reply := by
  cases arguments with
  | nil => cases accepted
  | cons first rest =>
    cases rest with
    | cons _ _ => cases first <;> simp [invoke?] at accepted
    | nil =>
      cases first with
      | symbol _ | var _ | expression _ => cases accepted
      | grounded value =>
        cases value with
        | int _ | bool _ | custom _ _ => cases accepted
        | string text =>
          cases parsed : Binary.Text.parse text with
          | none => simp only [invoke?, parsed, Bind.bind, Option.bind] at accepted; cases accepted
          | some input =>
            cases computed : run scope language service input with
            | none => simp only [invoke?, parsed, computed, Bind.bind, Option.bind] at accepted; cases accepted
            | some output =>
              simp only [invoke?, parsed, computed, Bind.bind, Option.bind, Option.some.injEq] at accepted
              exact ⟨text, input, output, rfl, parsed,
                run_sound scope language service input output computed, accepted.symm⟩

theorem invoke_encoded (scope : Lean.Name) (language : LanguageDef) (service : Service)
    (input output : List Binary.Alphabet) (accepted : run scope language service input = some output) :
    invoke? scope language service [textAtom (Binary.Text.render input)] =
      some (textAtom (Binary.Text.render output)) := by
  simp only [invoke?, textAtom, Binary.Text.parse_render, accepted, Bind.bind, Option.bind]

theorem invoke_render_exact (scope : Lean.Name) (language : LanguageDef) (service : Service)
    (input : List Binary.Alphabet) (reply : Atom) :
    invoke? scope language service [textAtom (Binary.Text.render input)] = some reply ↔
      ∃ output, run scope language service input = some output ∧
        reply = textAtom (Binary.Text.render output) := by
  cases computed : run scope language service input with
  | none => simp [invoke?, textAtom, Binary.Text.parse_render, computed]
  | some output => simp [invoke?, textAtom, Binary.Text.parse_render, computed, eq_comm]

/-- Construct the existing source-faithful request at its literal scoped
native endpoints. The submitted finite law table remains part of the packet. -/
def bindingEquationArguments (scope : Lean.Name) {language : LanguageDef}
    {context : List TypeExpr}
    {sort : TypeExpr}
    (declarations : List (DeclaredAxiom language))
    (first second : Term
      (signatureOf language) context sort)
    (submitted : Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.SubmittedTable.Packet) : List Atom :=
  [textAtom (Binary.Text.render (Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.encodeRequest
    ⟨context, sort, .submittedTableEquation,
      Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.sourceRequest scope declarations first second, submitted⟩))]

/-- The original full collection-equation family is preserved and reflected
at the actual dialect call's submitted-table endpoint, with finite evidence. -/
theorem full_source_iff_invoke (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr}
    {sort : TypeExpr}
    (first second : Term
      (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related
      (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language),
      ∃ submitted : Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.SubmittedTable.Packet, ∃ reply,
      invoke? scope language .bindingEquation
        (bindingEquationArguments scope declarations first second submitted) = some reply := by
  rw [Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.External.full_source_iff_external scope first second]
  constructor
  · rintro ⟨declarations, submitted, output, accepted⟩
    exact ⟨declarations, submitted, _, invoke_encoded scope language .bindingEquation _ output accepted⟩
  · rintro ⟨declarations, submitted, reply, accepted⟩
    obtain ⟨output, computed, _⟩ := (invoke_render_exact scope language .bindingEquation _ reply).mp accepted
    exact ⟨declarations, submitted, output, computed⟩

/-- Both source substitutions leave packet bytes untouched. -/
theorem petta_substitution_text (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (text : String) :
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (textAtom text) = textAtom text := rfl

theorem he_substitution_text (bindings : HE.Bindings) (text : String) (fuel : Nat) :
    bindings.applyFull (textAtom text) fuel = textAtom text := by
  cases fuel <;> rfl

/-- Compatibility with `%Undefined%` is not a native conversion judgment. -/
theorem gradual_not_native_conversion {Head : Type} {arity : Nat}
    (headEquality : Head → Head → Prop) (root : RootComputation Head)
    (encode : Atom → Tm Head arity) :
    ¬(∀ left right,
      Mettapedia.Logic.TheoryModel.Consistent HE.TypeGrounding.Gradual.Concretization {left, right} ↔
        Conv headEquality (encode left) (encode right) root) := by
  exact HE.TypeGrounding.Gradual.no_faithful_transitive_representation
    (fun first second => Conv headEquality first second root)
    (fun first second => Relation.EqvGen.trans _ _ _ first second) encode

/-! ## HE's existing grounded dispatch -/

def heDispatch (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch) :
    HE.GroundedDispatch where
  isExecutable operator := match operator with
    | .symbol head => (Service.readHead head).isSome || base.isExecutable operator
    | _ => base.isExecutable operator
  execute operator arguments := match operator with
    | .symbol head => match Service.readHead head with
      | some service => .ok ((invoke? scope language service arguments).toList.map (fun reply => (reply, HE.Bindings.empty)))
      | none => base.execute operator arguments
    | _ => base.execute operator arguments

theorem he_unknown_executable (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (head : String) (unknown : Service.readHead head = none) :
    (heDispatch scope language base).isExecutable (.symbol head) = base.isExecutable (.symbol head) := by
  simp only [heDispatch, unknown, Option.isSome_none, Bool.false_or]

theorem he_unknown_execute (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (head : String) (arguments : List Atom) (unknown : Service.readHead head = none) :
    (heDispatch scope language base).execute (.symbol head) arguments = base.execute (.symbol head) arguments := by
  simp only [heDispatch, unknown]

theorem he_service_executable (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (service : Service) : (heDispatch scope language base).isExecutable (.symbol service.head) = true := by
  simp only [heDispatch, Service.readHead_head, Option.isSome_some, Bool.true_or]

theorem he_service_execute (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (service : Service) (arguments : List Atom) :
    (heDispatch scope language base).execute (.symbol service.head) arguments =
      .ok ((invoke? scope language service arguments).toList.map (fun reply => (reply, HE.Bindings.empty))) := by
  simp only [heDispatch, Service.readHead_head]

/-- Literal service names do not collide with HE's two call special forms. -/
theorem service_call_guards (service : Service) (arguments : List Atom) :
    HE.isErrorAtom (.expression (.symbol service.head :: arguments)) = false ∧
      service.head ≠ "unify" ∧ service.head ≠ "switch-minimal" := by
  cases service <;> simp [Service.head, HE.isErrorAtom]

/-- The adapter adds no binding assignments. The existing HE merge remains
visible for every caller, including callers whose binding representation has
not been assumed normalized. A caller whose bindings admit no merge receives
HE's native `Empty` reply with its bindings unchanged. -/
theorem he_mettaCall_accepted_merges (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (reply : Atom)
    (bindings : HE.Bindings) (accepted : invoke? scope language service arguments = some reply) (fuel : Nat) :
    HE.mettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType bindings (fuel + 2) =
        if (HE.mergeBindings HE.Bindings.empty bindings (fuel + 1)).isEmpty then
          [(Atom.empty, bindings)]
        else
          (HE.mergeBindings HE.Bindings.empty bindings (fuel + 1)).map (fun merged => (reply, merged)) := by
  obtain ⟨_, _, output, _, _, _, bound⟩ := invoke_sound scope language service arguments reply accepted
  subst reply
  cases merged : HE.mergeBindings HE.Bindings.empty bindings (fuel + 1) with
  | nil =>
    cases service <;>
      simp [HE.mettaCall, HE.invoke, HE.InvocationMode.errorPassthrough, HE.ordinaryCallReturn,
        Service.head, heDispatch, Service.readHead, accepted, merged, HE.isEmptyOrError, HE.isEmptyAtom,
        HE.isErrorAtom, textAtom, Atom.empty, Atom.notReducible]
  | cons first rest =>
    cases service <;>
      simp [HE.mettaCall, HE.invoke, HE.InvocationMode.errorPassthrough, HE.ordinaryCallReturn,
        HE.invocationResult, HE.Bindings.applyFull, Service.head, heDispatch, Service.readHead, accepted,
        merged, HE.evalAtom, HE.isEmptyOrError, HE.isEmptyAtom, HE.isErrorAtom, textAtom, Atom.notReducible,
        List.flatMap_map]
    all_goals exact List.map_eq_flatMap.symm

/-- This is the actual modeled `mettaCall`, including its native binding
merge and recursive evaluation of the returned grounded string. -/
theorem he_mettaCall_accepted (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (reply : Atom)
    (accepted : invoke? scope language service arguments = some reply) (fuel : Nat) :
    HE.mettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType HE.Bindings.empty (fuel + 2) =
        [(reply, HE.Bindings.empty)] := by
  rw [he_mettaCall_accepted_merges scope language base space service arguments reply HE.Bindings.empty accepted fuel]
  simp only [HE.mergeBindings, HE.Bindings.empty, List.foldl_nil, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceIte, List.map_cons, List.map_nil]

/-- A caller assignment that the available fuel cannot merge receives HE's
`Empty` reply, not an empty answer list. -/
theorem he_mettaCall_accepted_unmerged (scope : Lean.Name) (language : LanguageDef)
    (base : HE.GroundedDispatch) (space : HE.Space) (service : Service) (arguments : List Atom)
    (reply : Atom) (accepted : invoke? scope language service arguments = some reply)
    (name : String) (value : Atom) :
    HE.mettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType ⟨[(name, value)], []⟩ 2 =
        [(Atom.empty, ⟨[(name, value)], []⟩)] := by
  have merged := he_mettaCall_accepted_merges scope language base space service arguments reply
    ⟨[(name, value)], []⟩ accepted 0
  simp only [HE.mergeBindings, HE.addVarBinding, List.foldl_cons, List.foldl_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.isEmpty_nil, ↓reduceIte] at merged
  exact merged

theorem he_mettaCall_refused (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (type_ : Atom) (bindings : HE.Bindings)
    (refused : invoke? scope language service arguments = none) (fuel : Nat) :
    HE.mettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) type_ bindings (fuel + 1) = [(Atom.empty, bindings)] := by
  cases service <;>
    simp [HE.mettaCall, HE.invoke, HE.InvocationMode.errorPassthrough, HE.ordinaryCallReturn, HE.isErrorAtom,
      HE.isEmptyOrError, HE.isEmptyAtom, Service.head, heDispatch, Service.readHead, refused, Atom.empty,
      Atom.notReducible]

/-- Accepted service calls also have derivations in the independently stated
HE call judgment, using its original grounded-call and type-pass rules. -/
theorem he_mettaCall_derivation (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (reply : Atom)
    (accepted : invoke? scope language service arguments = some reply) :
    HE.MettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType HE.Bindings.empty
        (reply, HE.Bindings.empty) := by
  have shape : ∃ text, reply = textAtom text := by
    obtain ⟨_, _, output, _, _, _, bound⟩ := invoke_sound scope language service arguments reply accepted
    exact ⟨Binary.Text.render output, bound⟩
  have notError : HE.isEmptyOrError reply = false := by
    obtain ⟨text, rfl⟩ := shape
    rfl
  have notReducible : reply ≠ Atom.notReducible := by
    obtain ⟨text, rfl⟩ := shape
    simp [textAtom, Atom.notReducible]
  refine HE.MettaCall.grounded_ok _ _ _ (.symbol service.head) arguments
    [(reply, HE.Bindings.empty)] (reply, HE.Bindings.empty) HE.Bindings.empty
    (reply, HE.Bindings.empty) 1 rfl (he_service_executable scope language base service)
    ?_ ?_ (service_call_guards service arguments).1 ?_ (by simp) ?_ ?_
  · cases service <;> decide
  · cases service <;> decide
  · rw [he_service_execute, accepted]
    rfl
  · simp [HE.mergeBindings, HE.Bindings.empty]
  · exact HE.OrdinaryCallReturnRel.of_eval notReducible
      (HE.EvalAtom.type_pass reply Atom.atomType HE.Bindings.empty notError (Or.inl rfl))

/-- Successful string replies are preserved and reflected by the actual HE
call. Refusal is the distinct source `Empty` result. -/
theorem he_mettaCall_text_iff (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (text : String) (fuel : Nat) :
    HE.mettaCall space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType HE.Bindings.empty (fuel + 2) =
        [(textAtom text, HE.Bindings.empty)] ↔ invoke? scope language service arguments = some (textAtom text) := by
  cases computed : invoke? scope language service arguments with
  | none =>
      rw [he_mettaCall_refused scope language base space service arguments Atom.atomType HE.Bindings.empty computed (fuel + 1)]
      simp [textAtom, Atom.empty]
  | some reply =>
      rw [he_mettaCall_accepted scope language base space service arguments reply computed fuel]
      simp

/-- Every successful host reply still has the original independent packet
meaning; the empty native binding set supplies no extra hypotheses. -/
theorem he_reply_sound (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (service : Service) (arguments : List Atom) (reply : Atom) (bindings : HE.Bindings)
    (results : HE.ResultSet)
    (returned : (heDispatch scope language base).execute (.symbol service.head) arguments = .ok results)
    (accepted : (reply, bindings) ∈ results) :
    bindings = HE.Bindings.empty ∧ ReplyMeaning scope language service arguments reply := by
  rw [he_service_execute] at returned
  have bound := (HE.GroundedResult.ok.inj returned).symm
  rw [bound] at accepted
  cases computed : invoke? scope language service arguments with
  | none => simp [computed] at accepted
  | some value =>
      simp only [computed, Option.toList_some, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at accepted
      exact ⟨accepted.2, invoke_sound scope language service arguments reply
        (computed.trans (congrArg some accepted.1.symm))⟩

/-- Asking HE for raw `Atom` data intentionally does not run a native call.
This is the source evaluator's existing demand policy. -/
theorem he_raw_call_is_data (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (service : Service) (arguments : List Atom) (bindings : HE.Bindings) (fuel : Nat) :
    HE.evalAtom space (heDispatch scope language base)
      (.expression (.symbol service.head :: arguments)) Atom.atomType bindings (fuel + 1) =
      [(.expression (.symbol service.head :: arguments), bindings)] := by
  cases service <;> simp [HE.evalAtom, HE.isEmptyOrError, HE.isEmptyAtom, HE.isErrorAtom, Service.head]

/-! ## Additive PeTTa transitions on the original configuration -/

/-- Exactly the two newly installed call sites. -/
def peTTaSite : PeTTa.Eval.Control → Bool
  | .evaluate _ (.expression (.symbol head :: _)) => (Service.readHead head).isSome
  | .arguments _ (.function head) [] _ _ => (Service.readHead head).isSome
  | _ => false

def peTTaNativeStep (scope : Lean.Name) (language : LanguageDef) :
    PeTTa.Eval.Configuration → Option PeTTa.Eval.Configuration
  | configuration => match configuration.control with
    | .evaluate bindings (.expression (.symbol head :: arguments)) =>
      match Service.readHead head with
      | some _ => some {configuration with control := .arguments bindings (.function head) arguments [] 0}
      | none => none
    | .arguments _ (.function head) [] values _ =>
      match Service.readHead head with
      | some service => some {configuration with control := .returned (invoke? scope language service values).toList}
      | none => none
    | _ => none

/-- Every unselected configuration uses the existing PeTTa source step. -/
def peTTaStep (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) : Option PeTTa.Eval.Configuration :=
  if peTTaSite configuration.control then peTTaNativeStep scope language configuration
  else PeTTa.Eval.step program configuration

theorem peTTa_fallback (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (outside : peTTaSite configuration.control = false) :
    peTTaStep scope language program configuration = PeTTa.Eval.step program configuration := by
  simp only [peTTaStep, outside, Bool.false_eq_true, ↓reduceIte]

theorem peTTa_enter (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (service : Service) (arguments : List Atom)
    (control : configuration.control = .evaluate bindings (.expression (.symbol service.head :: arguments))) :
    peTTaStep scope language program configuration =
      some {configuration with control := .arguments bindings (.function service.head) arguments [] 0} := by
  simp only [peTTaStep, control, peTTaSite, Service.readHead_head, Option.isSome_some,
    ↓reduceIte, peTTaNativeStep]

theorem peTTa_return (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (service : Service) (values : List Atom) (index : Nat)
    (control : configuration.control = .arguments bindings (.function service.head) [] values index) :
    peTTaStep scope language program configuration =
      some {configuration with control := .returned (invoke? scope language service values).toList} := by
  simp only [peTTaStep, control, peTTaSite, Service.readHead_head, Option.isSome_some,
    ↓reduceIte, peTTaNativeStep]

/-- The original configuration carries the actual accepted singleton reply;
rejected packets return no answers, so they cannot forge this observation. -/
theorem peTTa_return_reply_iff (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (service : Service) (values : List Atom) (index : Nat) (reply : Atom)
    (control : configuration.control = .arguments bindings (.function service.head) [] values index) :
    peTTaStep scope language program configuration = some {configuration with control := .returned [reply]} ↔
      invoke? scope language service values = some reply := by
  rw [peTTa_return scope language program configuration bindings service values index control]
  cases configuration
  cases computed : invoke? scope language service values <;> simp

theorem peTTa_return_reply_sound (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (service : Service) (values : List Atom) (index : Nat) (reply : Atom)
    (control : configuration.control = .arguments bindings (.function service.head) [] values index)
    (accepted : peTTaStep scope language program configuration =
      some {configuration with control := .returned [reply]}) :
    ReplyMeaning scope language service values reply :=
  invoke_sound scope language service values reply
    ((peTTa_return_reply_iff scope language program configuration bindings service values index reply control).mp accepted)

/-- A native service transition changes control only. In particular, it
neither consumes source input nor writes an effect or store entry. -/
theorem peTTa_native_control_only (scope : Lean.Name) (language : LanguageDef)
    (before after : PeTTa.Eval.Configuration)
    (computed : peTTaNativeStep scope language before = some after) :
    ∃ control, after = {before with control} := by
  unfold peTTaNativeStep at computed
  dsimp only at computed
  split at computed
  · split at computed
    · simp only [Option.some.injEq] at computed
      exact ⟨_, computed.symm⟩
    · cases computed
  · split at computed
    · simp only [Option.some.injEq] at computed
      exact ⟨_, computed.symm⟩
    · cases computed
  · cases computed

theorem peTTa_native_preserves_observations (scope : Lean.Name) (language : LanguageDef)
    (before after : PeTTa.Eval.Configuration)
    (computed : peTTaNativeStep scope language before = some after) :
    after.state = before.state ∧ after.frames = before.frames ∧
      after.input = before.input ∧ after.output = before.output := by
  obtain ⟨control, rfl⟩ := peTTa_native_control_only scope language before after computed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Quotation remains the original source operation. A service-looking
payload beneath it is returned as substituted data, without native dispatch. -/
theorem peTTa_quoted_call (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (body : Atom) (control : configuration.control = .evaluate bindings (.expression [.symbol "quote", body])) :
    peTTaStep scope language program configuration =
      some {configuration with control := .returned [Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings body]} := by
  have outside : peTTaSite configuration.control = false := by rw [control]; rfl
  rw [peTTa_fallback scope language program configuration outside]
  simp [PeTTa.Eval.step, control]

/-- The extension retains PeTTa's captured-value inertness. A binding may
contain a service-looking expression, but evaluating its variable returns the
captured value instead of beginning a new call. -/
theorem peTTa_captured_value_is_data (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (control : configuration.control = .evaluate bindings (.var name)) :
    peTTaStep scope language program configuration =
      some {configuration with control := .returned [Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var name)]} := by
  have outside : peTTaSite configuration.control = false := by rw [control]; rfl
  rw [peTTa_fallback scope language program configuration outside]
  simp only [PeTTa.Eval.step, control]

/-- Every source step outside the two explicit service sites is preserved;
reflection there is the original source machine's adequacy theorem. -/
theorem peTTa_outside_iff_source (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (before after : PeTTa.Eval.Configuration) (outside : peTTaSite before.control = false) :
    peTTaStep scope language program before = some after ↔
      PeTTa.DeclarativeSpec.Transition program before after := by
  rw [peTTa_fallback scope language program before outside]
  exact ⟨PeTTa.Eval.step_transition, PeTTa.Eval.transition_step⟩

/-- The actual extended PeTTa machine executes a grounded packet call from
source syntax to its answer. Both original argument policies are covered:
raw data and ordinary evaluation agree on the grounded packet string. The
path stops before consuming the caller's existing continuation. -/
theorem peTTa_packet_call_path (scope : Lean.Name) (language : LanguageDef) (program : PeTTa.SpaceSemantics.Program)
    (configuration : PeTTa.Eval.Configuration) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (service : Service) (text : String) :
    Relation.ReflTransGen (fun before after => peTTaStep scope language program before = some after)
      {configuration with control := .evaluate bindings (.expression [.symbol service.head, textAtom text])}
      {configuration with control := .returned (invoke? scope language service [textAtom text]).toList} := by
  let relation := fun before after => peTTaStep scope language program before = some after
  let start := {configuration with control := PeTTa.Eval.Control.evaluate bindings (.expression [.symbol service.head, textAtom text])}
  let enter := {configuration with control := PeTTa.Eval.Control.arguments bindings (.function service.head) [textAtom text] [] 0}
  let frame := PeTTa.Eval.Frame.argument bindings (.function service.head) [] [] 0
  let demanded := {configuration with control := PeTTa.Eval.Control.evaluate bindings (textAtom text), frames := frame :: configuration.frames}
  let returned := {configuration with control := PeTTa.Eval.Control.returned [textAtom text], frames := frame :: configuration.frames}
  let completed := PeTTa.Eval.Control.arguments bindings (.function service.head) [] [textAtom text] 1
  let scheduled := {configuration with control := PeTTa.Eval.Control.sequence [completed] []}
  let dispatch := {configuration with control := completed, frames := PeTTa.Eval.Frame.sequence [] [] :: configuration.frames}
  let produced := {configuration with control := PeTTa.Eval.Control.returned (invoke? scope language service [textAtom text]).toList, frames := PeTTa.Eval.Frame.sequence [] [] :: configuration.frames}
  let collected := {configuration with control := PeTTa.Eval.Control.sequence [] (invoke? scope language service [textAtom text]).toList}
  have first : peTTaStep scope language program start = some enter :=
    peTTa_enter scope language program start bindings service [textAtom text] rfl
  have argument : Relation.ReflTransGen
      (fun before after => peTTaStep scope language program before = some after) enter returned := by
    by_cases raw : PeTTa.Eval.argumentIsRaw program service.head 0 = true
    · exact .single (by
        simp [peTTaStep, peTTaSite, enter, returned, frame, PeTTa.Eval.step, raw, textAtom,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst])
    · have notRaw : PeTTa.Eval.argumentIsRaw program service.head 0 = false := by
        exact Bool.eq_false_iff.mpr raw
      apply Relation.ReflTransGen.trans (b := demanded)
      · exact .single (by simp [peTTaStep, peTTaSite, enter, demanded, frame, PeTTa.Eval.step, notRaw])
      · exact .single (by simp [peTTaStep, peTTaSite, demanded, returned, PeTTa.Eval.step, textAtom])
  have resume : peTTaStep scope language program returned = some scheduled := by
    simp [peTTaStep, peTTaSite, returned, scheduled, frame, completed, PeTTa.Eval.step]
  have schedule : peTTaStep scope language program scheduled = some dispatch := by
    simp [peTTaStep, peTTaSite, scheduled, dispatch, PeTTa.Eval.step]
  have invoke : peTTaStep scope language program dispatch = some produced :=
    peTTa_return scope language program dispatch bindings service [textAtom text] 1 rfl
  have collect : peTTaStep scope language program produced = some collected := by
    simp [peTTaStep, peTTaSite, produced, collected, PeTTa.Eval.step]
  have finish : peTTaStep scope language program collected =
      some {configuration with control := .returned (invoke? scope language service [textAtom text]).toList} := by
    simp [peTTaStep, peTTaSite, collected, PeTTa.Eval.step]
  have rest : Relation.ReflTransGen
      (fun before after => peTTaStep scope language program before = some after) returned
      {configuration with control := .returned (invoke? scope language service [textAtom text]).toList} := by
    apply Relation.ReflTransGen.head (r := relation) resume
    apply Relation.ReflTransGen.head (r := relation) schedule
    apply Relation.ReflTransGen.head (r := relation) invoke
    apply Relation.ReflTransGen.head (r := relation) collect
    exact .single finish
  exact Relation.ReflTransGen.head (r := relation) first (argument.trans rest)

/-- Preservation and reflection reach HE's actual call result for the full
original source equation family, with the exact submitted request bytes. -/
theorem full_source_iff_he_call (scope : Lean.Name) (language : LanguageDef) (base : HE.GroundedDispatch)
    (space : HE.Space) (fuel : Nat)
    {context : List TypeExpr}
    {sort : TypeExpr}
    (first second : Term
      (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related
      (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language),
      ∃ submitted : Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.SubmittedTable.Packet, ∃ text,
      HE.mettaCall space (heDispatch scope language base)
        (.expression (.symbol Service.bindingEquation.head :: bindingEquationArguments scope declarations first second submitted))
        Atom.atomType HE.Bindings.empty (fuel + 2) = [(textAtom text, HE.Bindings.empty)] := by
  rw [full_source_iff_invoke scope language first second]
  constructor
  · rintro ⟨declarations, submitted, reply, accepted⟩
    obtain ⟨_, _, output, _, _, _, bound⟩ := invoke_sound scope language .bindingEquation
      (bindingEquationArguments scope declarations first second submitted) reply accepted
    refine ⟨declarations, submitted, Binary.Text.render output,
      (he_mettaCall_text_iff scope language base space .bindingEquation _ _ fuel).mpr ?_⟩
    simpa only [bound] using accepted
  · rintro ⟨declarations, submitted, text, accepted⟩
    exact ⟨declarations, submitted, textAtom text,
      (he_mettaCall_text_iff scope language base space .bindingEquation _ text fuel).mp accepted⟩

/-- The same source authority is preserved and reflected by the actual
PeTTa service return. Existing state and continuation fields remain literal. -/
theorem full_source_iff_peTTa_return (scope : Lean.Name) (language : LanguageDef)
    (program : PeTTa.SpaceSemantics.Program) (configuration : PeTTa.Eval.Configuration)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    {context : List TypeExpr}
    {sort : TypeExpr}
    (first second : Term
      (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related
      (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language),
      ∃ submitted : Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices.SubmittedTable.Packet, ∃ reply,
      peTTaStep scope language program
        {configuration with control := (.arguments bindings (.function Service.bindingEquation.head) []
          (bindingEquationArguments scope declarations first second submitted) 1)} =
          some {configuration with control := .returned [reply]} := by
  rw [full_source_iff_invoke scope language first second]
  constructor
  · rintro ⟨declarations, submitted, reply, accepted⟩
    exact ⟨declarations, submitted, reply,
      (peTTa_return_reply_iff scope language program _ bindings .bindingEquation _ 1 reply rfl).mpr accepted⟩
  · rintro ⟨declarations, submitted, reply, accepted⟩
    exact ⟨declarations, submitted, reply,
      (peTTa_return_reply_iff scope language program _ bindings .bindingEquation _ 1 reply rfl).mp accepted⟩

end Mettapedia.Languages.MeTTa.PrimeComparisons.NativeDialectKernelServices
