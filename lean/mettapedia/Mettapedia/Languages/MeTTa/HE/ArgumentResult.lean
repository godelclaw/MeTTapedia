import Mettapedia.Languages.MeTTa.HE.Types

/-!
# HE argument-result packets

The HE interpreter's `interpret_args` protocol returns `(Ok (arguments ...))`
on success. Its callers unpack the tag before constructing an application.
An argument list beginning with `Error` is consequently distinct from an
error returned by the argument computation. These definitions describe that
packet boundary; they do not evaluate any of its payload atoms.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Successful argument data, with the interpreter's explicit `Ok` tag. -/
def argumentPacket (arguments : List Atom) : Atom :=
  .expression [.symbol "Ok", .expression arguments]

/-- Decode only the tagged list representation. -/
def unpackArguments : Atom → Option (List Atom)
  | .expression [.symbol tag, .expression arguments] =>
      if tag = "Ok" then some arguments else none
  | _ => none

/-- Admission of the success packet, before consuming its payload. -/
def argumentsSucceeded (result : Atom) : Bool :=
  (unpackArguments result).isSome

/-- Payload extraction, used only after `argumentsSucceeded` is true.
Malformed inputs are rejected by that guard, not treated as empty arguments. -/
def argumentValues (result : Atom) : List Atom :=
  (unpackArguments result).getD []

@[simp] theorem unpackArguments_packet (arguments : List Atom) :
    unpackArguments (argumentPacket arguments) = some arguments := by
  simp [unpackArguments, argumentPacket]

@[simp] theorem argumentsSucceeded_packet (arguments : List Atom) :
    argumentsSucceeded (argumentPacket arguments) = true := by
  simp [argumentsSucceeded]

@[simp] theorem argumentValues_packet (arguments : List Atom) :
    argumentValues (argumentPacket arguments) = arguments := by
  simp [argumentValues]

theorem unpackArguments_iff {result : Atom} {arguments : List Atom} :
    unpackArguments result = some arguments ↔ result = argumentPacket arguments := by
  cases result with
  | expression atoms =>
      rcases atoms with _ | ⟨head, tail⟩
      · simp [unpackArguments, argumentPacket]
      rcases tail with _ | ⟨payload, tail⟩
      · simp [unpackArguments, argumentPacket]
      rcases tail with _ | ⟨extra, rest⟩
      · cases head <;> cases payload <;> simp [unpackArguments, argumentPacket]
      · simp [unpackArguments, argumentPacket]
  | symbol name => simp [unpackArguments, argumentPacket]
  | var name => simp [unpackArguments, argumentPacket]
  | grounded value => simp [unpackArguments, argumentPacket]

theorem argumentsSucceeded_iff {result : Atom} :
    argumentsSucceeded result = true ↔ ∃ arguments, result = argumentPacket arguments := by
  unfold argumentsSucceeded
  cases decoded : unpackArguments result with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨arguments, rfl⟩
      simp at decoded
  | some arguments =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨arguments, unpackArguments_iff.mp decoded⟩

theorem admitted_argumentValues {result : Atom}
    (admitted : argumentsSucceeded result = true) :
    result = argumentPacket (argumentValues result) := by
  obtain ⟨arguments, rfl⟩ := argumentsSucceeded_iff.mp admitted
  simp

theorem argumentPacket_injective : Function.Injective argumentPacket := by
  intro left right equal
  have decoded := congrArg unpackArguments equal
  simpa using decoded

@[simp] theorem argumentPacket_not_error (arguments : List Atom) :
    isEmptyOrError (argumentPacket arguments) = false := by
  simp [argumentPacket, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]

theorem argumentsSucceeded_false_of_error {result : Atom}
    (failed : isEmptyOrError result = true) : argumentsSucceeded result = false := by
  cases admitted : argumentsSucceeded result with
  | false => rfl
  | true =>
      obtain ⟨arguments, rfl⟩ := argumentsSucceeded_iff.mp admitted
      simp at failed

end Mettapedia.Languages.MeTTa.HE
