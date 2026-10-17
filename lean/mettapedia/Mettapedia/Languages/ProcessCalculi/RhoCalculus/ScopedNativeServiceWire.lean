import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices

/-!
# Source-only packets for the intrinsic scoped rho services

The fixed profile is the original two-sort, six-constructor binding signature.
Every request retains its complete source context, sort, terms and evidence.
The source tag distinguishes these packets from declared-calculus comparison
packets. Whole-word decoding checks canonical storage and rejects trailing data.

Equality is the original rhoSourceE closure. Computation uses the original
COMM and process Drop rules in parallel contexts; the separate step-evidence
request also checks source equality before and after that computation.
Admission here checks the intrinsic sorted source syntax. It installs no rules.
No physical execution-time or proof-size bound follows from this wire layer.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServiceWire

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.OSLF.Binding.WireCodec
open ScopedNativeServices

private def bit : Codec Bool := Codec.nat.mapped (fun value => if value then 1 else 0)
  (fun value => match value with | 0 => some false | 1 => some true | _ => none)
  (fun value => by cases value <;> rfl)

private def rawData : Codec Data := ⟨id, some, fun _ => rfl⟩

def stepEvidence (context : Ctx sig) : Codec (StepEvidence context) :=
  (Codec.prod (Codec.prod (sourceTerm context .pr) (sourceTerm context .pr))
    (Codec.prod (Codec.list bit) (Codec.prod rawData rawData))).mapped
    (fun evidence => ((evidence.before, evidence.after),
      (evidence.address, evidence.beforeEquation, evidence.afterEquation)))
    (fun fields => some ⟨fields.1.1, fields.1.2, fields.2.1, fields.2.2.1, fields.2.2.2⟩)
    (fun _ => rfl)

inductive Kind where
  | admission | equation | execution | proposedResult | step
  deriving DecidableEq, Repr

private def putKind : Kind → Nat
  | .admission => 0 | .equation => 1 | .execution => 2
  | .proposedResult => 3 | .step => 4
private def getKind : Nat → Option Kind
  | 0 => some .admission | 1 => some .equation | 2 => some .execution
  | 3 => some .proposedResult | 4 => some .step | _ => none
private def kinds : Codec Kind := Codec.nat.mapped putKind getKind (fun kind => by cases kind <;> rfl)

def Fields (context : Ctx sig) : Kind → Type
  | .admission => Σ sort : Srt, Term sig context sort
  | .equation => Σ sort : Srt, (Term sig context sort × Term sig context sort) × Data
  | .execution => Term sig context .pr × List Bool
  | .proposedResult => (Term sig context .pr × List Bool) × Term sig context .pr
  | .step => (Term sig context .pr × Term sig context .pr) × StepEvidence context

abbrev Packet := Σ context : Ctx sig, Σ kind : Kind, Fields context kind

private def fields (context : Ctx sig) : (kind : Kind) → Codec (Fields context kind)
  | .admission => Codec.sigma sorts (sourceTerm context)
  | .equation => Codec.sigma sorts (fun sort =>
      Codec.prod (Codec.prod (sourceTerm context sort) (sourceTerm context sort)) rawData)
  | .execution => Codec.prod (sourceTerm context .pr) (Codec.list bit)
  | .proposedResult => Codec.prod
      (Codec.prod (sourceTerm context .pr) (Codec.list bit)) (sourceTerm context .pr)
  | .step => Codec.prod (Codec.prod (sourceTerm context .pr) (sourceTerm context .pr))
      (stepEvidence context)

private def payload : Codec Packet :=
  Codec.sigma (Codec.list sorts) (fun context => Codec.sigma kinds (fields context))

def serviceTag : String := "Rho.Scoped.Source.Services.v1"

def packet : Codec Packet where
  put value := .pair (Codec.string.put serviceTag) (payload.put value)
  get
    | .pair header body => if header = Codec.string.put serviceTag then payload.get body else none
    | _ => none
  get_put value := by simp only [ite_true, payload.get_put]

def encodeRequest (value : Packet) : List Binary.Alphabet := Binary.encodeWith packet value

def decodeRequest (word : List Binary.Alphabet) : Option Packet := Binary.canonicalDecodeWith packet word

theorem decodeRequest_encodeRequest (value : Packet) :
    decodeRequest (encodeRequest value) = some value := Binary.canonicalDecodeWith_encodeWith packet value

theorem decodeRequest_exact (word : List Binary.Alphabet) (value : Packet) :
    decodeRequest word = some value ↔ encodeRequest value = word := Binary.canonicalDecodeWith_exact packet word value

theorem request_trailing_refused (value : Packet) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) : decodeRequest (encodeRequest value ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused packet value tail nonempty

def respond? : Packet → Option Data
  | ⟨_, .admission, _⟩ => some (.atom 0)
  | ⟨_, .equation, ⟨_, (first, second), evidence⟩⟩ =>
      if checkEquation evidence first second then some (.atom 0) else none
  | ⟨context, .execution, source, address⟩ =>
      (execute? source address).map (sourceTerm context .pr).put
  | ⟨_, .proposedResult, (source, address), target⟩ =>
      if checkExecution source target address then some (.atom 0) else none
  | ⟨_, .step, (source, target), evidence⟩ =>
      if checkStep source target evidence then some (.atom 0) else none

/-- The semantic authorities are the original source equality and event step;
none is defined by successful wire decoding or checker execution. -/
def ReplyMeaning : Packet → Data → Prop
  | ⟨_, .admission, _⟩, output => output = .atom 0
  | ⟨_, .equation, ⟨_, (first, second), _⟩⟩, output =>
      output = .atom 0 ∧ EqClosure rhoSourceE first second
  | ⟨context, .execution, source, address⟩, output =>
      ∃ target, (sourceTerm context .pr).put target = output ∧
        execute? source address = some target ∧ SourceStep source target
  | ⟨_, .proposedResult, (source, address), target⟩, output =>
      output = .atom 0 ∧ execute? source address = some target ∧ SourceStep source target
  | ⟨_, .step, (source, target), _⟩, output => output = .atom 0 ∧ SourceStep source target

theorem respond_sound (value : Packet) (output : Data)
    (accepted : respond? value = some output) : ReplyMeaning value output := by
  obtain ⟨context, kind, fields⟩ := value
  cases kind with
  | admission => exact (Option.some.inj accepted).symm
  | equation =>
      obtain ⟨sort, ⟨first, second⟩, evidence⟩ := fields
      change (if checkEquation evidence first second then some (.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i checked
        exact ⟨(Option.some.inj accepted).symm, checkEquation_sound evidence first second checked⟩
      · cases accepted
  | execution =>
      obtain ⟨target, computed, encoded⟩ := Option.map_eq_some_iff.mp accepted
      exact ⟨target, encoded, computed, execute?_sound fields.1 target fields.2 computed⟩
  | proposedResult =>
      obtain ⟨⟨source, address⟩, target⟩ := fields
      change (if checkExecution source target address then some (.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i checked
        have computed := (checkExecution_exact source target address).mp checked
        exact ⟨(Option.some.inj accepted).symm, computed, execute?_sound source target address computed⟩
      · cases accepted
  | step =>
      obtain ⟨⟨source, target⟩, evidence⟩ := fields
      change (if checkStep source target evidence then some (.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i checked
        exact ⟨(Option.some.inj accepted).symm, checkStep_sound source target evidence checked⟩
      · cases accepted

theorem equation_coverage {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔ ∃ evidence : Data,
      respond? ⟨context, .equation, ⟨sort, (first, second), evidence⟩⟩ = some (.atom 0) := by
  constructor
  · intro held
    obtain ⟨evidence, checked⟩ := (checkEquation_complete first second).mp held
    exact ⟨evidence, by simp only [respond?, checked]; rfl⟩
  · rintro ⟨evidence, accepted⟩
    exact (respond_sound ⟨context, .equation, ⟨sort, (first, second), evidence⟩⟩ (.atom 0) accepted).2

theorem step_coverage {context : Ctx sig} (first second : Term sig context .pr) :
    SourceStep first second ↔ ∃ evidence : StepEvidence context,
      respond? ⟨context, .step, (first, second), evidence⟩ = some (.atom 0) := by
  constructor
  · intro held
    obtain ⟨evidence, checked⟩ := (checkStep_complete first second).mp held
    exact ⟨evidence, by simp only [respond?, checked]; rfl⟩
  · rintro ⟨evidence, accepted⟩
    exact (respond_sound ⟨context, .step, (first, second), evidence⟩ (.atom 0) accepted).2

/-- A response binds the entire canonical request to its actual output. -/
def encodeReply (value : Packet) (output : Data) : List Binary.Alphabet :=
  Binary.encodeData (.pair (packet.put value) output)

def run (word : List Binary.Alphabet) : Option (List Binary.Alphabet) := do
  let value ← decodeRequest word
  let output ← respond? value
  return encodeReply value output

theorem run_encode (value : Packet) :
    run (encodeRequest value) = (respond? value).map (encodeReply value) := by
  simp only [run, decodeRequest_encodeRequest, Bind.bind, Option.bind]
  cases respond? value <;> rfl

theorem run_sound (word reply : List Binary.Alphabet) (accepted : run word = some reply) :
    ∃ value output, encodeRequest value = word ∧ encodeReply value output = reply ∧ ReplyMeaning value output := by
  unfold run at accepted
  obtain ⟨value, decoded, returned⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨output, checked, returned⟩ := Option.bind_eq_some_iff.mp returned
  exact ⟨value, output, (decodeRequest_exact word value).mp decoded,
    Option.some.inj returned, respond_sound value output checked⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServiceWire
