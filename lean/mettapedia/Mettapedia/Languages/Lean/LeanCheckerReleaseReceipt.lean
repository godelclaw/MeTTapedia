import Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower

/-!
# Release-bound intake for Lean-family checking services

A Lean export verdict is usable only for the release that produced it.  The
release coordinate includes the complete export stream and import closure,
toolchain and exporter, checker family/revision/mode, semantic profile and
assumptions, and the executable artifact.  This module binds those coordinates
to the four-outcome authority service without treating metadata as a proof.

The generic wrapper recomputes the observed coordinate, checks exact equality
with the expected release, and only then invokes the checker service.  An
invalid coordinate is an operational error.  A different valid coordinate is
inapplicable and therefore declines.  An accepted result carries the exact
release coordinate.  Its semantic authority is inherited solely from the
underlying service's soundness or model-soundness theorem.

The con-leche source pin and result decoder below record the audited external
protocol.  They do not instantiate the external executable, verify a digest,
or claim parity with the official Lean kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.LeanCheckerReleaseReceipt

open Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower
open Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower.Service

universe uInput uOutput uModel

/-! ## Exact release coordinates -/

/-- Lean-family checker implementations remain distinct nodes of the flower. -/
inductive CheckerFamily where
  | officialKernel
  | lean4Lean
  | conLeche
  | lean4Less
deriving Repr, DecidableEq, BEq

/-- A mode is part of the checker identity.  In particular, con-leche's
`verified` and `trusted` executions do not share a receipt. -/
inductive CheckerMode where
  | kernel
  | verified
  | trusted
  | named (name : String)
deriving Repr, DecidableEq, BEq

def CheckerMode.isValid : CheckerMode → Bool
  | .kernel | .verified | .trusted => true
  | .named name => name != ""

/-- Exact source identity for one checker implementation.  This is separate
from the executable digest because one source revision can produce different
artifacts. -/
structure SourceRevisionPin where
  repository : String
  revision : String
deriving Repr, DecidableEq, BEq

def SourceRevisionPin.isValid (pin : SourceRevisionPin) : Bool :=
  pin.repository != "" && pin.revision != ""

/-- Identity of the complete exported input.  The import-closure digest is
kept separate so a root stream cannot silently reuse a receipt after an import
changes. -/
structure ExportStreamPin where
  format : String
  formatVersion : String
  streamDigest : String
  importClosureDigest : String
  declarationCount : Nat
deriving Repr, DecidableEq, BEq

def ExportStreamPin.isValid (pin : ExportStreamPin) : Bool :=
  pin.format != "" && pin.formatVersion != "" &&
  pin.streamDigest != "" && pin.importClosureDigest != ""

/-- The producer toolchain is pinned independently of the checking service. -/
structure ToolchainPin where
  leanRevision : String
  exporterRevision : String
  preludeDigest : String
deriving Repr, DecidableEq, BEq

def ToolchainPin.isValid (pin : ToolchainPin) : Bool :=
  pin.leanRevision != "" && pin.exporterRevision != "" &&
  pin.preludeDigest != ""

/-- The selected logical profile, model assumptions and accelerated-operation
pins are separate semantic coordinates. -/
structure SemanticPin where
  profileDigest : String
  assumptionsDigest : String
  primitivePinsDigest : String
deriving Repr, DecidableEq, BEq

def SemanticPin.isValid (pin : SemanticPin) : Bool :=
  pin.profileDigest != "" && pin.assumptionsDigest != "" &&
  pin.primitivePinsDigest != ""

/-- One exact checker executable and protocol. -/
structure CheckerPin where
  family : CheckerFamily
  source : SourceRevisionPin
  mode : CheckerMode
  protocolVersion : String
  executableDigest : String
deriving Repr, DecidableEq, BEq

def CheckerPin.isValid (pin : CheckerPin) : Bool :=
  pin.source.isValid && pin.mode.isValid &&
  pin.protocolVersion != "" && pin.executableDigest != ""

/-- The complete coordinate to which an accepted release receipt applies. -/
structure ReleasePin where
  stream : ExportStreamPin
  toolchain : ToolchainPin
  checker : CheckerPin
  semantics : SemanticPin
deriving Repr, DecidableEq, BEq

def ReleasePin.isValid (pin : ReleasePin) : Bool :=
  pin.stream.isValid && pin.toolchain.isValid &&
  pin.checker.isValid && pin.semantics.isValid

/-- An accepted output paired with the exact release coordinate.  This data is
authoritative only as the output of `ReleaseBoundService.toService`; parsing a
printed copy does not recreate acceptance. -/
structure ReleaseReceipt (Output : Type uOutput) where
  release : ReleasePin
  output : Output
deriving Repr, DecidableEq

@[simp] theorem releaseReceipt_expected_eq_iff
    {Output : Type uOutput} (expected : ReleasePin) (output : Output)
    (receipt : ReleaseReceipt Output) :
    ({ release := expected, output } : ReleaseReceipt Output) = receipt ↔
      expected = receipt.release ∧ output = receipt.output := by
  cases receipt with
  | mk release payload =>
      constructor
      · intro equal
        cases equal
        exact ⟨rfl, rfl⟩
      · rintro ⟨releaseEqual, outputEqual⟩
        cases releaseEqual
        cases outputEqual
        rfl

/-! ## Release-bound four-outcome service -/

/-- `observe` computes the release coordinate from the actual input and
execution environment.  A concrete adapter owes the correspondence theorem
between this observation and the bytes/process it identifies. -/
structure ReleaseBoundService (Input : Type uInput) (Output : Type uOutput) where
  expected : ReleasePin
  observe : Input → ReleasePin
  checker : Service Input Output

namespace ReleaseBoundService

variable {Input : Type uInput} {Output : Type uOutput} {Model : Type uModel}

/-- Run only at the expected valid release.  Invalid metadata is an error;
valid but different metadata is an unsupported input and therefore declines. -/
def run (bound : ReleaseBoundService Input Output) (input : Input) :
    Outcome (ReleaseReceipt Output) :=
  if bound.expected.isValid then
    let observed := bound.observe input
    if observed.isValid then
      if observed = bound.expected then
        match bound.checker.run input with
        | .accepted output => .accepted ⟨bound.expected, output⟩
        | .rejected => .rejected
        | .declined => .declined
        | .error => .error
      else
        .declined
    else
      .error
  else
    .error

def toService (bound : ReleaseBoundService Input Output) :
    Service Input (ReleaseReceipt Output) :=
  ⟨bound.run⟩

/-- Acceptance is exactly underlying acceptance at the same valid observed
release.  No digest or checker family is forgotten. -/
theorem accepts_iff (bound : ReleaseBoundService Input Output)
    (input : Input) (receipt : ReleaseReceipt Output) :
    bound.toService.Accepts input receipt ↔
      bound.expected.isValid = true ∧
      (bound.observe input).isValid = true ∧
      bound.observe input = bound.expected ∧
      bound.expected = receipt.release ∧
      bound.checker.Accepts input receipt.output := by
  unfold toService run Service.Accepts
  by_cases expectedValid : bound.expected.isValid = true
  · simp only [expectedValid, if_true]
    by_cases observedValid : (bound.observe input).isValid = true
    · simp only [observedValid, if_true]
      by_cases same : bound.observe input = bound.expected
      · simp only [same, if_true, true_and]
        cases bound.checker.run input <;> simp
      · simp [same]
    · simp [observedValid]
  · have expectedFalse : bound.expected.isValid = false :=
      Bool.eq_false_of_not_eq_true expectedValid
    simp [expectedFalse]

/-- Every accepted receipt names the configured release exactly. -/
theorem accepts_exact_release (bound : ReleaseBoundService Input Output)
    {input : Input} {receipt : ReleaseReceipt Output}
    (accepted : bound.toService.Accepts input receipt) :
    receipt.release = bound.expected :=
  ((bound.accepts_iff input receipt).mp accepted |>.2.2.2.1).symm

/-- Forgetting the release wrapper gives a one-way acceptance refinement into
the underlying checker. -/
def acceptanceRefinement (bound : ReleaseBoundService Input Output) :
    AcceptanceRefinement bound.toService bound.checker where
  mapOutput := ReleaseReceipt.output
  preserves := by
    intro input receipt accepted
    exact (bound.accepts_iff input receipt).mp accepted |>.2.2.2.2

/-- Ordinary semantic soundness passes through exact release binding. -/
theorem sound (bound : ReleaseBoundService Input Output)
    {Meaning : Input → Output → Prop}
    (sound : bound.checker.Sound Meaning) :
    bound.toService.Sound
      (fun input receipt =>
        receipt.release = bound.expected ∧ Meaning input receipt.output) := by
  intro input receipt accepted
  exact ⟨bound.accepts_exact_release accepted,
    sound input receipt.output
      (bound.acceptanceRefinement.preserves input receipt accepted)⟩

/-- Model soundness likewise comes only from the underlying service theorem. -/
theorem modelSound (bound : ReleaseBoundService Input Output)
    {Satisfies : Input → Output → Model → Prop}
    (sound : bound.checker.ModelSound Satisfies) :
    bound.toService.ModelSound
      (fun input receipt model =>
        receipt.release = bound.expected ∧
        Satisfies input receipt.output model) := by
  intro input receipt accepted
  obtain ⟨model, realized⟩ := sound input receipt.output
    (bound.acceptanceRefinement.preserves input receipt accepted)
  exact ⟨model, bound.accepts_exact_release accepted, realized⟩

/-- Changing any valid release coordinate makes the existing service
inapplicable rather than turning the changed input into a mathematical
rejection. -/
theorem run_eq_declined_of_valid_mismatch
    (bound : ReleaseBoundService Input Output) (input : Input)
    (expectedValid : bound.expected.isValid = true)
    (observedValid : (bound.observe input).isValid = true)
    (different : bound.observe input ≠ bound.expected) :
    bound.run input = .declined := by
  simp [run, expectedValid, observedValid, different]

/-- A malformed configured release is an operational error and invokes no
checker verdict. -/
theorem run_eq_error_of_invalid_expected
    (bound : ReleaseBoundService Input Output) (input : Input)
    (invalid : bound.expected.isValid = false) :
    bound.run input = .error := by
  simp [run, invalid]

end ReleaseBoundService

/-! ## Pinned con-leche source and result protocol -/

/-- Source revision audited for the con-leche authority edge.  The executable
digest remains a required release-specific input below. -/
def conLecheAuditedSource : SourceRevisionPin :=
  { repository := "https://github.com/leanprover/con-leche"
    revision := "103562ba1c46cee26f134d0435765adcb5d22486" }

theorem conLecheAuditedSource_valid :
    conLecheAuditedSource.isValid = true := by
  rfl

/-- Build the verified con-leche checker coordinate without inventing a
binary identity.  The caller must supply the digest of the actual executable. -/
def conLecheVerifiedChecker (executableDigest : String) : CheckerPin :=
  { family := .conLeche
    source := conLecheAuditedSource
    mode := .verified
    protocolVersion := "ndjson-exit-0-1-2-3"
    executableDigest }

theorem conLecheVerifiedChecker_valid_iff (executableDigest : String) :
    (conLecheVerifiedChecker executableDigest).isValid = true ↔
      executableDigest != "" := by
  simp [conLecheVerifiedChecker, CheckerPin.isValid,
    conLecheAuditedSource_valid, CheckerMode.isValid]

namespace ConLecheProtocol

/-- Result coordinates parsed from one completed external invocation.  The
accepted declaration count is present only on the accepting line. -/
structure RawResult where
  exitCode : Nat
  acceptedDeclarations : Option Nat
deriving Repr, DecidableEq

/-- Decode the pinned four-outcome protocol.  Exit zero without an accepted
count, or a nonzero verdict carrying a count, is malformed and therefore an
error. -/
def decode (result : RawResult) : Outcome Nat :=
  match result.exitCode, result.acceptedDeclarations with
  | 0, some count => .accepted count
  | 1, none => .rejected
  | 2, none => .declined
  | _, _ => .error

@[simp] theorem decode_accepted (count : Nat) :
    decode ⟨0, some count⟩ = .accepted count := rfl

@[simp] theorem decode_rejected :
    decode ⟨1, none⟩ = .rejected := rfl

@[simp] theorem decode_declined :
    decode ⟨2, none⟩ = .declined := rfl

@[simp] theorem decode_driver_error :
    decode ⟨3, none⟩ = .error := rfl

@[simp] theorem decode_abort :
    decode ⟨134, none⟩ = .error := rfl

@[simp] theorem decode_missing_acceptance_count :
    decode ⟨0, none⟩ = .error := rfl

@[simp] theorem decode_count_on_rejection (count : Nat) :
    decode ⟨1, some count⟩ = .error := rfl

end ConLecheProtocol

/-! ## Positive and negative release controls -/

namespace Controls

def verifiedRelease : ReleasePin :=
  { stream :=
      { format := "lean4export-ndjson"
        formatVersion := "fixture-v1"
        streamDigest := "sha256:stream-a"
        importClosureDigest := "sha256:imports-a"
        declarationCount := 3 }
    toolchain :=
      { leanRevision := "lean-fixture-revision"
        exporterRevision := "exporter-fixture-revision"
        preludeDigest := "sha256:prelude-a" }
    checker := conLecheVerifiedChecker "sha256:con-leche-binary-a"
    semantics :=
      { profileDigest := "sha256:lean-profile-a"
        assumptionsDigest := "sha256:set-theory-a"
        primitivePinsDigest := "sha256:nat-pins-a" } }

theorem verifiedRelease_valid : verifiedRelease.isValid = true := by
  rfl

def fixtureChecker : Service Bool Nat where
  run
    | false => .accepted 3
    | true => .rejected

def matchingBound : ReleaseBoundService Bool Nat where
  expected := verifiedRelease
  observe := fun _ => verifiedRelease
  checker := fixtureChecker

theorem matching_release_accepts :
    matchingBound.toService.Accepts false
      { release := verifiedRelease, output := 3 } := by
  rfl

theorem matching_release_retains_rejection :
    matchingBound.run true = .rejected := by
  rfl

def changedStreamRelease : ReleasePin :=
  { verifiedRelease with
    stream :=
      { verifiedRelease.stream with
        streamDigest := "sha256:stream-b" } }

theorem changedStreamRelease_valid : changedStreamRelease.isValid = true := by
  rfl

theorem changed_stream_refused :
    ( { matchingBound with observe := fun _ => changedStreamRelease } ).run false =
      .declined := by
  rfl

def trustedRelease : ReleasePin :=
  { verifiedRelease with
    checker := { verifiedRelease.checker with mode := .trusted } }

theorem trustedRelease_valid : trustedRelease.isValid = true := by
  rfl

theorem trusted_mode_cannot_reuse_verified_receipt :
    ( { matchingBound with observe := fun _ => trustedRelease } ).run false =
      .declined := by
  rfl

def officialKernelRelease : ReleasePin :=
  { verifiedRelease with
    checker :=
      { verifiedRelease.checker with
        family := .officialKernel
        mode := .kernel } }

theorem officialKernelRelease_valid : officialKernelRelease.isValid = true := by
  rfl

theorem checker_family_cannot_reuse_receipt :
    ( { matchingBound with observe := fun _ => officialKernelRelease } ).run false =
      .declined := by
  rfl

def malformedRelease : ReleasePin :=
  { verifiedRelease with
    checker :=
      { verifiedRelease.checker with executableDigest := "" } }

theorem malformed_release_errors :
    ( { matchingBound with expected := malformedRelease } ).run false =
      .error := by
  rfl

def verdicts : List (String × Bool) :=
  [ ("matching verified release accepts",
      decide (matchingBound.run false =
        .accepted { release := verifiedRelease, output := 3 }))
  , ("underlying rejection is retained",
      decide (matchingBound.run true = .rejected))
  , ("changed stream declines",
      decide
        (( { matchingBound with observe := fun _ => changedStreamRelease } ).run false =
          .declined))
  , ("trusted mode cannot reuse verified receipt",
      decide
        (( { matchingBound with observe := fun _ => trustedRelease } ).run false =
          .declined))
  , ("official kernel cannot reuse con-leche receipt",
      decide
        (( { matchingBound with observe := fun _ => officialKernelRelease } ).run false =
          .declined))
  , ("malformed release errors",
      decide
        (( { matchingBound with expected := malformedRelease } ).run false =
          .error))
  , ("protocol accepts exit zero with count",
      decide (ConLecheProtocol.decode ⟨0, some 3⟩ = .accepted 3))
  , ("protocol rejects exit one",
      decide (ConLecheProtocol.decode ⟨1, none⟩ = .rejected))
  , ("protocol declines exit two",
      decide (ConLecheProtocol.decode ⟨2, none⟩ = .declined))
  , ("protocol errors on malformed acceptance",
      decide (ConLecheProtocol.decode ⟨0, none⟩ = .error)) ]

theorem verdicts_all : verdicts.all Prod.snd = true := by
  rfl

end Controls

section AxiomAudit

#print axioms ReleaseBoundService.accepts_iff
#print axioms ReleaseBoundService.accepts_exact_release
#print axioms ReleaseBoundService.acceptanceRefinement
#print axioms ReleaseBoundService.sound
#print axioms ReleaseBoundService.modelSound
#print axioms ReleaseBoundService.run_eq_declined_of_valid_mismatch
#print axioms conLecheVerifiedChecker_valid_iff
#print axioms Controls.verdicts_all

end AxiomAudit

end Mettapedia.Languages.Lean.LeanCheckerReleaseReceipt
