import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.Languages.GuardedAtomRule.Services
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

/-!
# Actual PeTTa configurations in the native dependent Data fragment

Three existing codecs compose here: the complete source configuration, the
shared physical Pattern wire, and the native scoped Data representation.
Their round trips retain control, bindings, continuations, pending branches,
spaces, cells and I/O. Each encoded configuration has the existing native
formation-sensitive Data judgment and its actual free-algebra meaning.

The operational graph below transports the existing source transitions onto
those native values. It does not insert effectful transitions into dependent
definitional equality. Data admission does not validate a guest proof or make
it a native inhabitant of its represented proposition. Source-to-C execution
correspondence and that stronger proof interpretation remain separate work.
This is a qualified fragment, not adoption of a complete Prime foundation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations

open Presentation
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.LanguageDef

abbrev NativeTerm := Tower.Tm 0

def wire (configuration : Eval.Configuration) (names : List String) : CettaWire.Term :=
  InferenceCettaWire.encodePattern (ConfigurationEncoding.encode configuration names)

def encode (configuration : Eval.Configuration) (names : List String) : NativeTerm :=
  NativeWireData.encode (wire configuration names)

def decode (term : NativeTerm) : Option Eval.Configuration := do
  let value ← NativeWireData.decode term
  let pattern ← InferenceCettaWire.decodePattern value
  ConfigurationEncoding.decode pattern

theorem decode_encode (configuration : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail configuration.state [])
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) :
    decode (encode configuration names) = some configuration := by
  simpa [decode, encode, wire] using
    ConfigurationEncoding.decode_encode configuration names vacant covers

/-- Actual native formation, using the existing declarations and judgment. -/
theorem encode_admitted (configuration : Eval.Configuration) (names : List String) :
    FormationSensitive.Judgment NativeWireData.rules .nil
      (encode configuration names) NativeWireData.dataType :=
  NativeWireData.encode_judgment .nil _

/-- Meaning is the existing total constructor algebra, independently of the
decoder. The semantic carrier is the actual source store, not a dummy model. -/
theorem encode_denotes (configuration : Eval.Configuration) (names : List String) :
    NativeWireDataDenotation.Denotes .nil
      (fun index (_ : Effects.State) => Fin.elim0 index)
      (encode configuration names)
      (fun _ => NativeWireDataDenotation.ofWire (wire configuration names)) :=
  NativeWireDataDenotation.encode_denotes .nil _ _

/-- Equal native encodings cannot splice different valid source endpoints. -/
theorem equal_encodings_same_configuration
    (first second : Eval.Configuration) (firstNames secondNames : List String)
    (firstVacant : NamedSpaces.Store.EmptyTail first.state [])
    (secondVacant : NamedSpaces.Store.EmptyTail second.state [])
    (firstCovers : ∀ name, name ∉ firstNames → first.state.cells name = none)
    (secondCovers : ∀ name, name ∉ secondNames → second.state.cells name = none)
    (same : encode first firstNames = encode second secondNames) : first = second := by
  have decoded := congrArg decode same
  rw [decode_encode first firstNames firstVacant firstCovers,
    decode_encode second secondNames secondVacant secondCovers] at decoded
  exact Option.some.inj decoded

/-- The selected source transition earns its native endpoints. Finite cell
support is updated by the existing source operation, not by a guessed bound. -/
inductive Transition (program : SpaceSemantics.Program) : NativeTerm → NativeTerm → Prop where
  | step {before after : Eval.Configuration} (names : List String)
      (vacant : NamedSpaces.Store.EmptyTail before.state [])
      (covers : ∀ name, name ∉ names → before.state.cells name = none)
      (selected : DeclarativeSpec.Transition program before after) :
      Transition program (encode before names)
        (encode after (ConfigurationEncoding.cellSupportAfter before names))

theorem transition_reflects {program : SpaceSemantics.Program} {source target : NativeTerm}
    (transition : Transition program source target) :
    ∃ before after, decode source = some before ∧ decode target = some after ∧
      DeclarativeSpec.Transition program before after := by
  cases transition with
  | step names vacant covers selected =>
      exact ⟨_, _, decode_encode _ names vacant covers,
        decode_encode _ _ (DeclarativeSpec.transition_empty_tail vacant selected)
          (ConfigurationEncoding.transition_support names covers selected), selected⟩

theorem transition_admits {program : SpaceSemantics.Program} {source target : NativeTerm}
    (transition : Transition program source target) :
    FormationSensitive.Judgment NativeWireData.rules .nil source NativeWireData.dataType ∧
      FormationSensitive.Judgment NativeWireData.rules .nil target NativeWireData.dataType := by
  cases transition
  exact ⟨encode_admitted _ _, encode_admitted _ _⟩

/-- This is the explicit-state operational graph, separate from the native
dependent conversion graph. Its edges are the transported source steps. -/
def theory (program : SpaceSemantics.Program) : Mettapedia.GSLT.GSLT where
  Term := NativeTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition program
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

/-- Every native explicit-state path reflects a real source execution.
The decoder checks the starting endpoint, including its complete store. -/
theorem path_reflects {program : SpaceSemantics.Program} {source target : NativeTerm}
    (path : (theory program).MultiStep source target) (before : Eval.Configuration)
    (decoded : decode source = some before) :
    ∃ after, decode target = some after ∧ (Eval.theory program).MultiStep before after := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (theory program)
    (fun source target _ => ∀ before : Eval.Configuration, decode source = some before →
      ∃ after, decode target = some after ∧ (Eval.theory program).MultiStep before after)
    (fun _ before decoded => ⟨before, decoded, .refl _⟩)
    (fun {_ _ _} selected _ ih before decoded => ?_) source target path before decoded
  ·
      obtain ⟨original, middle, readSource, readMiddle, step⟩ := transition_reflects selected
      have same : original = before := Option.some.inj (readSource.symm.trans decoded)
      subst original
      obtain ⟨after, readAfter, remaining⟩ := ih middle readMiddle
      exact ⟨after, readAfter, .step step remaining⟩

/-- Source paths construct native state paths, with actual evolving cell
support and no guest evaluator supplied as an assumed soundness interface. -/
theorem path_lifts {program : SpaceSemantics.Program}
    {before after : Eval.Configuration} (path : (Eval.theory program).MultiStep before after)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ names → before.state.cells name = none) :
    ∃ finalNames,
      (theory program).MultiStep (encode before names) (encode after finalNames) ∧
      NamedSpaces.Store.EmptyTail after.state [] ∧
      (∀ name, name ∉ finalNames → after.state.cells name = none) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (Eval.theory program)
    (fun before after _ => ∀ names : List String,
      NamedSpaces.Store.EmptyTail before.state [] →
      (∀ name, name ∉ names → before.state.cells name = none) →
      ∃ finalNames, (theory program).MultiStep (encode before names) (encode after finalNames) ∧
        NamedSpaces.Store.EmptyTail after.state [] ∧
        (∀ name, name ∉ finalNames → after.state.cells name = none))
    (fun _ names vacant covers => ⟨names, .refl _, vacant, covers⟩)
    (fun {before _ _} selected _ ih names vacant covers => ?_) before after path names vacant covers
  ·
      have nextVacant := DeclarativeSpec.transition_empty_tail vacant selected
      have nextCovers := ConfigurationEncoding.transition_support names covers selected
      obtain ⟨finalNames, remaining, finalVacant, finalCovers⟩ :=
        ih (ConfigurationEncoding.cellSupportAfter before names) nextVacant nextCovers
      exact ⟨finalNames, .step (.step names vacant covers selected) remaining,
        finalVacant, finalCovers⟩

/-- Missing a required named cell changes a source configuration; typing the
remaining Data is not permission to invent the missing state. -/
theorem distinct_configurations_distinct_encodings
    (first second : Eval.Configuration) (firstNames secondNames : List String)
    (firstVacant : NamedSpaces.Store.EmptyTail first.state [])
    (secondVacant : NamedSpaces.Store.EmptyTail second.state [])
    (firstCovers : ∀ name, name ∉ firstNames → first.state.cells name = none)
    (secondCovers : ∀ name, name ∉ secondNames → second.state.cells name = none)
    (different : first ≠ second) : encode first firstNames ≠ encode second secondNames :=
  fun same => different (equal_encodings_same_configuration first second firstNames secondNames
    firstVacant secondVacant firstCovers secondCovers same)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations



open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations.AtomServices

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation
open MatchedIndexDependentTransport (nativePattern)
open Presentation
open SemanticEvidence SemanticService

/-- Canonical admission composes the existing native Data and Pattern
readers. The equality guard requires the original physical representation. -/
def readPattern (term : NativeTerm) : Option Pattern := do
  let wire ← NativeWireData.decode term
  let pattern ← InferenceCettaWire.decodePattern wire
  if nativePattern pattern = term then some pattern else none

@[simp] theorem readPattern_nativePattern (pattern : Pattern) :
    readPattern (nativePattern pattern) = some pattern := by
  simp only [readPattern, nativePattern, NativeWireData.decode_encode,
    InferenceCettaWire.decodePattern_encodePattern, bind, Option.bind, ↓reduceIte]

@[simp] theorem readPattern_exact (term : NativeTerm) (pattern : Pattern) :
    readPattern term = some pattern ↔ term = nativePattern pattern := by
  constructor
  · intro read
    simp only [readPattern, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨wire, _, actual, _, final⟩ := read
    split at final
    next same => cases Option.some.inj final; exact same.symm
    next => contradiction
  · rintro rfl
    exact readPattern_nativePattern pattern

def readPatterns (terms : List NativeTerm) : Option (List Pattern) := terms.mapM readPattern

@[simp] theorem readPatterns_exact (terms : List NativeTerm) (patterns : List Pattern) :
    readPatterns terms = some patterns ↔ terms = patterns.map (nativePattern (n := 0)) := by
  induction terms generalizing patterns with
  | nil => cases patterns <;> simp [readPatterns]
  | cons term terms ih =>
      cases patterns with
      | nil => simp [readPatterns, List.mapM_cons, Option.bind_eq_some_iff]
      | cons pattern patterns =>
          simp only [readPatterns, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff]
          constructor
          · rintro ⟨head, readHead, tail, readTail, same⟩
            have image := congrArg₂ List.cons ((readPattern_exact _ _).mp readHead)
              ((ih tail).mp readTail)
            rw [← List.map_cons, Option.some.inj same] at image
            exact image
          · intro same
            have fields := List.cons.inj same
            refine ⟨pattern, (readPattern_exact _ _).mpr fields.1,
              patterns, (ih patterns).mpr fields.2, rfl⟩

structure Request where
  relation : String
  arguments : List NativeTerm

def encodeRows (rows : List (List Pattern)) : List (List NativeTerm) :=
  rows.map (List.map (nativePattern (n := 0)))

/-- The target observation retains original native inputs, independent
source primitive authority and every resulting row occurrence. -/
def RowsMeaning (request : Request) (outputs : List (List NativeTerm)) : Prop :=
  ∃ arguments rows,
    request.arguments = arguments.map (nativePattern (n := 0)) ∧
    MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.Source
      request.relation arguments rows ∧ outputs = encodeRows rows

/-- This executes the original Atom primitive after canonical native reading
and the actual declared carrier check. It is separate from native conversion. -/
def run (request : Request) : Option (List (List NativeTerm)) := do
  let arguments ← readPatterns request.arguments
  if (MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.inputPatterns
      request.relation arguments).all
      MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.checkSourceCarrier then do
    let rows ← MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows?
      request.relation arguments
    return encodeRows rows
  else none

@[simp] theorem run_exact (request : Request) (outputs : List (List NativeTerm)) :
    run request = some outputs ↔ RowsMeaning request outputs := by
  constructor
  · intro computed
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
    obtain ⟨arguments, decoded, computed⟩ := computed
    split at computed
    next =>
      simp only [Option.bind_eq_some_iff] at computed
      obtain ⟨rows, computed, same⟩ := computed
      exact ⟨arguments, rows, (readPatterns_exact _ _).mp decoded,
        (MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows_exact _ _ _).mp computed,
        (Option.some.inj same).symm⟩
    next => contradiction
  · rintro ⟨arguments, rows, decoded, source, rfl⟩
    have carrier :=
      MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.source_inputs_carrier source
    have computed :=
      (MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows_exact _ _ _).mpr source
    simp only [run, (readPatterns_exact _ _).mpr decoded, carrier, if_true, computed,
      bind, Option.bind, pure]

/-- Missing native admission or a missing primitive response is unknown;
a completed source no-match remains a successful empty native row table. -/
theorem run_unknown_exact (request : Request) :
    run request = none ↔ ∀ outputs, ¬ RowsMeaning request outputs := by
  constructor
  · intro absent outputs source
    have computed := (run_exact _ _).mpr source
    rw [absent] at computed
    contradiction
  · intro absent
    cases computed : run request with
    | none => rfl
    | some outputs => exact (absent outputs ((run_exact _ _).mp computed)).elim

theorem nativePattern_formed (pattern : Pattern) :
    FormationSensitive.Judgment NativeWireData.rules .nil
      (nativePattern pattern) NativeWireData.dataType :=
  NativeWireData.encode_judgment .nil _

theorem nativePattern_denotes (pattern : Pattern) :
    NativeWireDataDenotation.Denotes .nil
      (fun index (_ : PeTTa.Effects.State) => Fin.elim0 index)
      (nativePattern pattern)
      (fun _ => NativeWireDataDenotation.ofWire (InferenceCettaWire.encodePattern pattern)) :=
  NativeWireDataDenotation.encode_denotes .nil _ _

theorem run_inputs_formed {request : Request} {outputs : List (List NativeTerm)}
    (computed : run request = some outputs) :
    ∀ term ∈ request.arguments,
      FormationSensitive.Judgment NativeWireData.rules .nil term NativeWireData.dataType := by
  obtain ⟨arguments, _, image, _, _⟩ := (run_exact _ _).mp computed
  intro term member
  rw [image] at member
  obtain ⟨pattern, _, rfl⟩ := List.mem_map.mp member
  exact nativePattern_formed pattern

theorem run_outputs_formed {request : Request} {outputs : List (List NativeTerm)}
    (computed : run request = some outputs) :
    ∀ row ∈ outputs, ∀ term ∈ row,
      FormationSensitive.Judgment NativeWireData.rules .nil term NativeWireData.dataType := by
  obtain ⟨_, rows, _, _, rfl⟩ := (run_exact _ _).mp computed
  intro row member term selected
  obtain ⟨patterns, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨pattern, _, rfl⟩ := List.mem_map.mp selected
  exact nativePattern_formed pattern

/-- Admission uses source input syntax and the original substitution wire.
It assumes neither a successful guard nor a supplied primitive response. -/
def Request.Meaning (request : Request) : Prop :=
  ∃ arguments,
    request.arguments = arguments.map (nativePattern (n := 0)) ∧
    MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.Inputs
      request.relation arguments

theorem request_meaning_iff_response (request : Request) :
    request.Meaning ↔ ∃ outputs, RowsMeaning request outputs := by
  constructor
  · rintro ⟨arguments, image, admitted⟩
    obtain ⟨rows, source⟩ :=
      MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.inputs_have_source admitted
    exact ⟨encodeRows rows, arguments, rows, image, source, rfl⟩
  · rintro ⟨_, arguments, _, image, source, _⟩
    exact ⟨arguments, image,
      MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.source_inputs source⟩

/-- The native request is unknown exactly outside the independently admitted
source input forms. Admitted false decisions still return an empty table. -/
theorem run_unknown_iff_not_admitted (request : Request) :
    run request = none ↔ ¬ request.Meaning := by
  rw [run_unknown_exact, request_meaning_iff_response]
  exact not_exists.symm

structure Result where
  request : Request
  outputs : Option (List (List NativeTerm))

def Result.Meaning (result : Result) : Prop :=
  ∃ outputs, result.outputs = some outputs ∧ RowsMeaning result.request outputs

def operation : AdmissionHom (⟨Request, Request.Meaning⟩ : AdmissionObject)
    (⟨Result, Result.Meaning⟩ : AdmissionObject) where
  run request := ⟨request, run request⟩
  preserves request admitted := by
    obtain ⟨arguments, image, admitted⟩ := admitted
    obtain ⟨rows, source⟩ :=
      MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.inputs_have_source admitted
    have meaning : RowsMeaning request (encodeRows rows) := ⟨arguments, rows, image, source, rfl⟩
    exact ⟨encodeRows rows, (run_exact _ _).mpr meaning, meaning⟩

def nativeService : Service.{0, 0} (⟨Result, Result.Meaning⟩ : AdmissionObject) :=
  .nativeOperation (⟨Request, Request.Meaning⟩ : AdmissionObject) operation

/-- Compiling original packet arguments and executing natively agrees with
the original primitive response, including unknown and complete empty tables. -/
theorem run_encoded (relation : String) (arguments : List Pattern) :
    run ⟨relation, arguments.map (nativePattern (n := 0))⟩ =
      (MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows? relation arguments).map encodeRows := by
  cases response : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows? relation arguments with
  | none =>
      simp only [run, (readPatterns_exact _ _).mpr rfl, bind, Option.bind, response, Option.map_none]
      split <;> rfl
  | some rows =>
      have source :=
        (MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows_exact _ _ _).mp response
      exact (run_exact _ _).mpr ⟨arguments, rows, rfl, source, rfl⟩

/-- Original guard inputs are resolved with the source first-match lookup and
single simultaneous substitution before becoming native Data packets. -/
def sourceFreshnessRequest (substitution : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (subject : Mettapedia.Languages.MeTTa.OSLFCore.Atom) : Request :=
  ⟨"metta-atom-fresh-v1", [OSLFCore.Bridge.GroundData.encode
      ((substitution.lookup name).getD (.var name)),
    OSLFCore.Bridge.GroundData.encode
      (Mettapedia.Languages.ProcessCalculi.MORK.applySubst substitution subject)].map
        (nativePattern (n := 0))⟩

theorem sourceFreshnessRequest_admitted
    (substitution : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (subject : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    (sourceFreshnessRequest substitution name subject).Meaning :=
  ⟨_, rfl, .freshness _ _⟩

/-- Native execution agrees with the actual source guard for every binding
environment, including captured names and failed non-name values. -/
theorem run_source_guard (substitution : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (subject : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    run (sourceFreshnessRequest substitution name subject) = some
      (if Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard substitution
          (.freshness name subject) then
        [(sourceFreshnessRequest substitution name subject).arguments] else []) := by
  simp only [sourceFreshnessRequest, run_encoded,
    MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.rows?, ↓reduceIte,
    AtomFreshness.queryRows, AtomFreshness.query_source_guard, Option.map_some]
  cases Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard substitution
    (.freshness name subject) <;> rfl

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations.AtomServices

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations.AtomServices
open MatchedIndexDependentTransport (nativePattern)

/-- This downstream adapter maps an independently specified source request to
native Data packets. The source handler does not depend on this adapter. -/
def fromSource (request : Mettapedia.Languages.GuardedAtomRule.Services.Primitive.Request) : Request :=
  ⟨request.relation, request.arguments.map (nativePattern (n := 0))⟩

/-- Native packet execution agrees with the original source service, including
unavailable responses and completed empty row tables. -/
theorem run_fromSource (request : Mettapedia.Languages.GuardedAtomRule.Services.Primitive.Request) :
    run (fromSource request) =
      (Mettapedia.Languages.GuardedAtomRule.Services.Primitive.run request).map encodeRows := by
  rw [fromSource, run_encoded,
    Mettapedia.Languages.GuardedAtomRule.Services.Primitive.run_rows]

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations.AtomServices
