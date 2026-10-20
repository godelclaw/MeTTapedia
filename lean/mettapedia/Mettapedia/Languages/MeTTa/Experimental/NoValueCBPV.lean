import Mettapedia.Languages.MeTTa.Experimental.NoValueZoo
import Mettapedia.TypeTheory.ContextualCBPVEquations

/-!
# The thirteen no-value kinds in the CBPV reading

The CBPV reading places each kind of `NoValueZoo` in one of four places:

* **values** of value types, never raised: the unit datum `()`, an empty
  collection, `None`, the datum `Empty`, and the evidence status *neither*;
* **runtime no-values** in the one raise carrier `RuntimeKind × payload`:
  an error value and an inert call;
* **observation fields**, not values: zero answers (an observation with no
  world) and incomplete (a budgeted observer's unfinished frontier);
* **judgments**, not values: undetermined, refuted, a closed type with no
  constructors, an open declared type.

An error raises and propagates through `to`, application and handlers until
a handler for its kind catches it. An inert call raises the `inert` kind with
the retained call as payload. In this reading Prime's default at each call
site is the retention handler, which answers the payload (`retain_inert`), so
an uninterpreted call reads back as itself and an enclosing call that cannot
use it is retained in turn; a strict profile would omit the handler.

**Non-collapse survives.** `encode` places every kind's witness into the
CBPV world (`Witness`): run outcomes as values or raised no-values,
evidence, verdicts and declarations. `decode` reads an encoding back as the
zoo's witness (retention for `inert`, an `Error` atom for `error`), and
`decode ∘ encode` is the zoo's witness (`Kind.decode_encode`). Hence every
zoo observation lifts, and every two kinds stay separated
(`Kind.separated_encoded`).

The runtime encodings are realized by actual CBPV computations over a MeTTa
signature (`raise_error_outcomes`, `raise_inert_outcomes`). A control
observer that drops raised outcomes identifies an error with zero answers
(`dropRaised_collapses`), which is why raised no-values stay in the carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.NoValueCBPV

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.TheoryModel
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.Languages.MeTTa.Experimental.NoValueZoo
open Mettapedia.TypeTheory.ContextualCBPV

/-! ## Placement of the kinds -/

/-- Where a no-value kind lives in the CBPV reading. -/
inductive Placement where
  | value
  | raised
  | observation
  | judgment
  deriving DecidableEq, Repr

/-- The placement of each kind. -/
def placement : NoValueZoo.Kind → Placement
  | .zeroAnswers => .observation
  | .unitDatum => .value
  | .emptyCollection => .value
  | .errorValue => .raised
  | .inertCall => .raised
  | .noneValue => .value
  | .emptyDatum => .value
  | .neither => .value
  | .undetermined => .judgment
  | .incomplete => .observation
  | .refuted => .judgment
  | .closedEmptyType => .judgment
  | .openDeclaredType => .judgment

/-- The kinds of the raise carrier. -/
inductive RuntimeKind where
  | error
  | inert
  deriving DecidableEq, Repr

/-- The zoo kind each raise kind is. -/
def RuntimeKind.toKind : RuntimeKind → NoValueZoo.Kind
  | .error => .errorValue
  | .inert => .inertCall

theorem RuntimeKind.toKind_injective : Function.Injective RuntimeKind.toKind := by
  intro first second equal
  cases first <;> cases second <;> first | rfl | cases equal

/-- Exactly the raise kinds are placed in the raise carrier. -/
theorem placement_raised_iff (kind : NoValueZoo.Kind) :
    placement kind = .raised ↔ ∃ runtime : RuntimeKind, runtime.toKind = kind := by
  constructor
  · intro raised
    cases kind <;> simp [placement] at raised <;>
      first
      | exact ⟨.error, rfl⟩
      | exact ⟨.inert, rfl⟩
  · rintro ⟨runtime, rfl⟩
    cases runtime <;> rfl

/-! ## A MeTTa signature: atoms as the one ground sort -/

inductive Ground where
  | atom
  deriving DecidableEq

/-- No primitives are needed for these controls. -/
inductive NoPrim : Ground → Ground → Type

/-- The CBPV signature over MeTTa atoms. State, requests and payloads are
atoms; the raise kinds are `RuntimeKind`. -/
abbrev mettaSig : Signature where
  Ground := Ground
  Data := fun _ => Pattern
  stateSort := Ground.atom
  intentSort := Ground.atom
  payloadSort := Ground.atom
  Kind := RuntimeKind
  Prim := NoPrim
  evalPrim := fun primitive _ => nomatch primitive

abbrev atomT : VTy mettaSig.Ground := .ground Ground.atom

abbrev quoteAtom {context : List (VTy mettaSig.Ground)} (atom : Pattern) :
    Val mettaSig context atomT :=
  .const (sig := mettaSig) Ground.atom atom

/-- A run outcome: an answer value or a raised no-value. -/
abbrev Outcome := Pattern ⊕ (RuntimeKind × Pattern)

/-- The answers of a closed returner over atoms, from a fixed state. -/
def outcomes (code : Comp mettaSig [] (.ret atomT)) : List Outcome :=
  (runWorlds (CTy.asProgram mettaSig (code.den Env.empty)) (sym "state")).map WorldResult.answer

/-! ## The encoding and its decoding -/

/-- Where a kind's witness lives in the CBPV reading. -/
inductive Witness where
  /-- A run: its subject and its outcomes; no outcome is zero answers. -/
  | run (subject : Pattern) (outcomes : List Outcome)
  /-- An evidence value. -/
  | evidence (status : FourVerdict)
  /-- A judgment's verdict, or a budgeted observer's readout. -/
  | verdict (outcome : Verdict)
  /-- A declaration's status. -/
  | declaration (status : OpenDeclarations.Status String)

/-- The message an `Error` atom carries in the zoo's error witness. -/
def errorMessage : Pattern := sym "empty-list"

/-- Each kind's witness in the CBPV reading. -/
def encode : NoValueZoo.Kind → Witness
  | .zeroAnswers => .run (lookupCall (sym "k2")) []
  | .unitDatum => .run doneNil [.inl unitAtom]
  | .emptyCollection => .run tailOfSingleton [.inl nilAtom]
  | .errorValue => .run checkedHeadNil [.inr (.error, errorMessage)]
  | .inertCall => .run headOfNil [.inr (.inert, headOfNil)]
  | .noneValue => .run headOrNoneNil [.inl noneAtom]
  | .emptyDatum => .run emptyOfNil [.inl emptyAtom]
  | .neither => .evidence (fourOfLanes false false)
  | .undetermined => .verdict (.outsideFragment ())
  | .incomplete => .verdict (.incomplete ())
  | .refuted => .verdict (.refuted ())
  | .closedEmptyType => .declaration (.closed ∅)
  | .openDeclaredType => .declaration (.declared ∅)

/-- Read one outcome as a zoo answer: an error becomes an `Error` atom on its
subject; an inert call is retained as its payload. -/
def decodeOutcome (subject : Pattern) : Outcome → Pattern
  | .inl value => value
  | .inr (.error, message) => .apply "Error" [subject, message]
  | .inr (.inert, payload) => payload

/-- Read a CBPV witness as the zoo's witness. -/
def decode : Witness → NoValueZoo.Witness
  | .run subject outcomes => .answers subject (outcomes.map (decodeOutcome subject) : List Pattern)
  | .evidence status => .evidence status
  | .verdict outcome => .verdict outcome
  | .declaration status => .declaration status

/-- **The encoding is a section of the decoding.** -/
theorem Kind.decode_encode (kind : NoValueZoo.Kind) : decode (encode kind) = kind.witness := by
  cases kind
  · rw [witness_zeroAnswers]; rfl
  · rw [witness_unitDatum]; rfl
  · rw [witness_emptyCollection]; rfl
  · rw [witness_errorValue]; rfl
  · rw [witness_inertCall]; rfl
  · rw [witness_noneValue]; rfl
  · rw [witness_emptyDatum]; rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every zoo observation, read through the decoding. -/
def Kind.encodedObservation (kind : NoValueZoo.Kind) : Witness → Prop :=
  fun witness => kind.observation (decode witness)

/-- **Each lifted observation holds of its own kind's encoding and of no other.** -/
theorem Kind.encodedObservation_iff (kind other : NoValueZoo.Kind) :
    Kind.encodedObservation kind (encode other) ↔ other = kind := by
  unfold Kind.encodedObservation
  rw [Kind.decode_encode]
  exact NoValueZoo.Kind.observation_witness_iff kind other

/-- **Non-collapse survives the carrier encoding.** -/
theorem Kind.separated_encoded {kind other : NoValueZoo.Kind} (different : kind ≠ other) :
    ∃ observe : Witness → Prop, observe (encode kind) ∧ ¬ observe (encode other) :=
  ⟨Kind.encodedObservation kind, (Kind.encodedObservation_iff kind kind).mpr rfl,
    fun holds => different ((Kind.encodedObservation_iff kind other).mp holds).symm⟩

theorem Kind.encode_injective : Function.Injective encode := by
  intro kind other equal
  have holds : Kind.encodedObservation kind (encode other) :=
    equal ▸ (Kind.encodedObservation_iff kind kind).mpr rfl
  exact ((Kind.encodedObservation_iff kind other).mp holds).symm

/-- The two raised kinds differ only by the kind index, not by the carrier:
the same payload under the two kinds is two different outcomes. -/
theorem raised_kinds_apart (payload : Pattern) :
    (Sum.inr (RuntimeKind.error, payload) : Outcome) ≠ Sum.inr (RuntimeKind.inert, payload) := by
  simp

/-! ## The runtime encodings are run outcomes of CBPV computations -/

/-- `raise error "empty-list"`. -/
def raiseError : Comp mettaSig [] (.ret atomT) := .raise .error (quoteAtom errorMessage)

/-- `raise inert (head-of Nil)`: an uninterpreted call. -/
def raiseInert : Comp mettaSig [] (.ret atomT) := .raise .inert (quoteAtom headOfNil)

/-- The retention handler: in this reading, Prime's call-site default for an
uninterpreted call. -/
def retainInert (code : Comp mettaSig [] (.ret atomT)) : Comp mettaSig [] (.ret atomT) :=
  .handle code .inert (.ret (.var .zero)) (.ret (.var .zero))

set_option backward.isDefEq.respectTransparency false in
theorem raise_error_outcomes : outcomes raiseError = [.inr (.error, errorMessage)] := rfl

set_option backward.isDefEq.respectTransparency false in
theorem raise_inert_outcomes : outcomes raiseInert = [.inr (.inert, headOfNil)] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Retention.** The default handler answers the retained call itself. -/
theorem retain_inert : outcomes (retainInert raiseInert) = [.inl headOfNil] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The retention handler does not catch an error: it raises again. -/
theorem retain_does_not_catch_error :
    outcomes (retainInert raiseError) = [.inr (.error, errorMessage)] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An error propagates through `to` and through a forced argument. -/
theorem error_propagates :
    outcomes (Comp.bind raiseError (Comp.ret (quoteAtom (sym "after")))) =
        [.inr (.error, errorMessage)] ∧
      outcomes (Comp.app (Comp.lam (Comp.force (Val.var .zero))) (Val.thunk raiseError)) =
        [.inr (.error, errorMessage)] :=
  ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- A thunked error that is never forced raises nothing. -/
theorem unforced_error_not_raised :
    outcomes (Comp.app (Comp.lam (Comp.ret (quoteAtom (sym "wrapped")))) (Val.thunk raiseError)) =
      [.inl (sym "wrapped")] := rfl

theorem runtime_encodings_realized :
    encode .errorValue = .run checkedHeadNil (outcomes raiseError) ∧
      encode .inertCall = .run headOfNil (outcomes raiseInert) := by
  rw [raise_error_outcomes, raise_inert_outcomes]
  exact ⟨rfl, rfl⟩

/-! ## A collapsing observer -/

/-- An observer that keeps only answered values and drops raised outcomes. -/
def dropRaised : Witness → Witness
  | .run subject outcomes => .run subject (outcomes.filter Sum.isLeft)
  | other => other

/-- **Dropping raised outcomes identifies an error with zero answers** on the
same subject, two kinds the carrier keeps apart. -/
theorem dropRaised_collapses :
    dropRaised (.run checkedHeadNil (outcomes raiseError)) = .run checkedHeadNil [] ∧
      Kind.encodedObservation .errorValue (.run checkedHeadNil (outcomes raiseError)) ∧
      ¬ Kind.encodedObservation .errorValue (dropRaised (.run checkedHeadNil (outcomes raiseError))) := by
  rw [raise_error_outcomes]
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨.apply "Error" [checkedHeadNil, errorMessage], ?_, [checkedHeadNil, errorMessage], rfl⟩
    simp [decodeOutcome]
  · simp [dropRaised, Kind.encodedObservation, decode, NoValueZoo.Kind.observation, ErrorAnswer]

#print axioms placement_raised_iff
#print axioms Kind.decode_encode
#print axioms Kind.separated_encoded
#print axioms Kind.encode_injective
#print axioms retain_inert
#print axioms error_propagates
#print axioms unforced_error_not_raised
#print axioms dropRaised_collapses

end Mettapedia.Languages.MeTTa.Experimental.NoValueCBPV
