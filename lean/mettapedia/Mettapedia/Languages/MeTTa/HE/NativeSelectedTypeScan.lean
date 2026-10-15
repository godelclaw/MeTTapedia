import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# First-success replay of the native HE function-type scan

The canonical HE dispatch loop scans source-ordered type candidates. Each
visited candidate supplies a classification or applicability reply. The first
successful reply stops scanning; later replies cannot add an overload branch.
Unresolved candidates suspend replay rather than being classified as failures.

The general correspondence uses the existing independent candidate-scan
judgment. Its witness certifies only replies that execution actually visits.
The constructive inverse extracts those replies from any independent scan;
the unvisited suffix remains unresolved. This is a service-reply interface,
not a proof that CeTTa's applicability callback implements that service.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type

inductive Reply where
  | unresolved
  | nonFunction
  | error (errors : List Atom)
  | success (policy : SelectedTypePolicy) (bindings : Bindings)

structure Candidate where
  source : Atom
  reply : Reply

def unresolved (types : List Atom) : List Candidate :=
  types.map fun source => ⟨source, .unresolved⟩

def sourceTypes (candidates : List Candidate) : List Atom := candidates.map Candidate.source

@[simp] theorem sourceTypes_unresolved (types : List Atom) :
    sourceTypes (unresolved types) = types := by
  simp [sourceTypes, unresolved, List.map_map, Function.comp_def]

def noteNonFunction : FunctionCandidateScanOutcome → FunctionCandidateScanOutcome
  | .success policy bindings => .success policy bindings
  | .exhausted errors _ => .exhausted errors true

def noteErrors (before : List Atom) : FunctionCandidateScanOutcome → FunctionCandidateScanOutcome
  | .success policy bindings => .success policy bindings
  | .exhausted errors eligible => .exhausted (before ++ errors) eligible

/-- None means a required service reply has not arrived. A selected candidate
returns immediately, without inspecting the suffix. -/
def scan : List Candidate → Option FunctionCandidateScanOutcome
  | [] => some (.exhausted [] false)
  | ⟨_, .unresolved⟩ :: _ => none
  | ⟨_, .nonFunction⟩ :: rest => noteNonFunction <$> scan rest
  | ⟨_, .error errors⟩ :: rest => noteErrors errors <$> scan rest
  | ⟨_, .success policy bindings⟩ :: _ => some (.success policy bindings)

/-- Independent evidence for the visited reply prefix. Success does not
require certificates for callbacks that were never run. -/
inductive RepliesRel
    (applicability : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop)
    (space : Space) (expression expected : Atom) (incoming : Bindings) :
    List Candidate → FunctionCandidateScanOutcome → Prop where
  | nil : RepliesRel applicability space expression expected incoming [] (.exhausted [] false)
  | nonFunction {candidate : Atom} {rest : List Candidate}
      {result : FunctionCandidateScanOutcome} :
      (¬∃ arguments returned, FunctionTypeRel candidate arguments returned) →
      RepliesRel applicability space expression expected incoming rest result →
      RepliesRel applicability space expression expected incoming
        (⟨candidate, .nonFunction⟩ :: rest) (noteNonFunction result)
  | failed {candidate returned : Atom} {arguments errors : List Atom}
      {rest : List Candidate} {result : FunctionCandidateScanOutcome} :
      FunctionTypeRel candidate arguments returned →
      (∀ policy bindings, ¬applicability space expression candidate expected incoming
        (.success policy bindings)) →
      applicability space expression candidate expected incoming (.error errors) →
      errors ≠ [] →
      RepliesRel applicability space expression expected incoming rest result →
      RepliesRel applicability space expression expected incoming
        (⟨candidate, .error errors⟩ :: rest) (noteErrors errors result)
  | selected {candidate returned : Atom} {arguments : List Atom}
      {policy : SelectedTypePolicy} {bindings : Bindings} {rest : List Candidate} :
      FunctionTypeRel candidate arguments returned →
      applicability space expression candidate expected incoming (.success policy bindings) →
      RepliesRel applicability space expression expected incoming
        (⟨candidate, .success policy bindings⟩ :: rest) (.success policy bindings)

theorem scan_replies
    {applicability : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expected : Atom} {incoming : Bindings}
    {candidates : List Candidate} {result : FunctionCandidateScanOutcome}
    (replies : RepliesRel applicability space expression expected incoming candidates result) :
    scan candidates = some result := by
  induction replies with
  | nil => rfl
  | nonFunction _ _ ih => simp [scan, ih]
  | failed _ _ _ _ _ ih => simp [scan, ih]
  | selected _ _ => rfl

theorem replies_to_specification
    {applicability : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expected : Atom} {incoming : Bindings}
    {candidates : List Candidate} {result : FunctionCandidateScanOutcome}
    (replies : RepliesRel applicability space expression expected incoming candidates result) :
    FunctionCandidateScanRel applicability space expression expected incoming
      (sourceTypes candidates) result := by
  induction replies with
  | nil => exact .nil
  | @nonFunction candidate rest result nonFunction tail ih =>
      cases result with
      | success policy bindings => exact .nonFunctionSuccess nonFunction ih
      | exhausted errors eligible => exact .nonFunctionExhausted nonFunction ih
  | @failed candidate returned arguments errors rest result function noSuccess failed nonempty tail ih =>
      cases result with
      | success policy bindings =>
          exact .functionFailureThenSuccess function noSuccess failed nonempty ih
      | exhausted tailErrors eligible =>
          exact .functionFailureExhausted function noSuccess failed nonempty ih
  | selected function applicable => exact .functionSuccess function applicable

/-- Every independent scan constructs exact visited replies and leaves its
unvisited source suffix intact, with no speculative applicability calls. -/
theorem specification_to_replies
    {applicability : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expected : Atom} {incoming : Bindings}
    {types : List Atom} {result : FunctionCandidateScanOutcome}
    (derivation : FunctionCandidateScanRel applicability space expression expected incoming types result) :
    ∃ candidates, sourceTypes candidates = types ∧
      RepliesRel applicability space expression expected incoming candidates result := by
  induction derivation with
  | nil => exact ⟨[], rfl, .nil⟩
  | @nonFunctionSuccess candidate candidates policy bindings nonFunction tail ih =>
      obtain ⟨replies, source, related⟩ := ih
      exact ⟨⟨candidate, .nonFunction⟩ :: replies,
        congrArg (List.cons candidate) source, .nonFunction nonFunction related⟩
  | @nonFunctionExhausted candidate candidates errors eligible nonFunction tail ih =>
      obtain ⟨replies, source, related⟩ := ih
      exact ⟨⟨candidate, .nonFunction⟩ :: replies,
        congrArg (List.cons candidate) source, .nonFunction nonFunction related⟩
  | @functionSuccess candidate candidates arguments returned policy bindings function applicable =>
      refine ⟨⟨candidate, .success policy bindings⟩ :: unresolved candidates, ?_,
        .selected function applicable⟩
      change candidate :: sourceTypes (unresolved candidates) = candidate :: candidates
      rw [sourceTypes_unresolved]
  | @functionFailureThenSuccess candidate candidates arguments returned errors policy bindings function
        noSuccess failed nonempty tail ih =>
      obtain ⟨replies, source, related⟩ := ih
      exact ⟨⟨candidate, .error errors⟩ :: replies,
        congrArg (List.cons candidate) source, .failed function noSuccess failed nonempty related⟩
  | @functionFailureExhausted candidate candidates arguments tailErrors returned errors eligible function
        noSuccess failed nonempty tail ih =>
      obtain ⟨replies, source, related⟩ := ih
      exact ⟨⟨candidate, .error errors⟩ :: replies,
        congrArg (List.cons candidate) source, .failed function noSuccess failed nonempty related⟩

theorem specification_replay_iff
    {applicability : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expected : Atom} {incoming : Bindings}
    {types : List Atom} {result : FunctionCandidateScanOutcome} :
    FunctionCandidateScanRel applicability space expression expected incoming types result ↔
      ∃ candidates, sourceTypes candidates = types ∧
        RepliesRel applicability space expression expected incoming candidates result ∧
        scan candidates = some result := by
  constructor
  · intro derivation
    obtain ⟨candidates, source, related⟩ := specification_to_replies derivation
    exact ⟨candidates, source, related, scan_replies related⟩
  · rintro ⟨candidates, rfl, related, _⟩
    exact replies_to_specification related

theorem selected_suffix_irrelevant (candidate : Atom) (policy : SelectedTypePolicy)
    (bindings : Bindings) (first second : List Candidate) :
    scan (⟨candidate, .success policy bindings⟩ :: first) =
      scan (⟨candidate, .success policy bindings⟩ :: second) := rfl

theorem unresolved_is_not_exhaustion (candidate : Atom) (rest : List Candidate)
    (errors : List Atom) (eligible : Bool) :
    scan (⟨candidate, .unresolved⟩ :: rest) ≠ some (.exhausted errors eligible) := by
  simp [scan]

end Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan
