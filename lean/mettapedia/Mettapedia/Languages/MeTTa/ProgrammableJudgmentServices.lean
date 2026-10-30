import Mettapedia.Languages.MeTTa.ProgrammableJudgmentTransforms
import Mettapedia.GSLT.Dynamics.ServiceResumption
import Mettapedia.TypeTheory.Authority

/-!
# Interactive proposals for an existing open rule

The request retains the selected source, ordered contexts, conclusion and
rule program. A provider proposes the missing argument proofs, reports a
boundary, or reports an unfinished budget. The continuation independently
checks a proposal and emits a transform intent only on acceptance. Committing
that intent still requires its source and linear resources to be current.

This is one well-founded service episode in the existing resumption model.
The resolved-run theorems are conditional on a reply being supplied; they do
not assert that an arbitrary external provider terminates or is fair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ProgrammableJudgmentServices

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.Dynamics.ServiceResumption
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers (BranchTrace)
open Mettapedia.TypeTheory.AuthorityTheory
open ProgrammableJudgmentTransforms TransformComposition

/-- Concrete data of this service call; no field asserts its conclusion. -/
structure Request where
  ticket : Nat
  source : GSLTSource
  premises : List Pattern
  ambient : List Pattern
  goal : Pattern
  program : RawOpenProof

/-- `ok` carries an untrusted argument vector. The existing sum distinguishes
a provider boundary from unfinished work. Neither is a mathematical negation. -/
abbrev Reply (_ : Request) := Except (String ⊕ Nat) (List RawOpenProof)

/-- Refutation here concerns the supplied argument vector, not existence of
a proof of the requested judgment. -/
abbrev Answer := Outcome (GSLTSource × RawOpenProof) (List RawOpenProof) (Mettapedia.GSLT.LanguageDef.CheckedSource.ValidationError ⊕ String) Nat
abbrev Execution := Resumption Request Reply (Multiset Cell) Answer (Span Cell)

variable [DecidableEq Cell]

def publicationIntent (request : Request) (arguments : List RawOpenProof) (result : RawOpenProof) : Span Cell :=
  (preparation request.source request.ticket request.premises request.ambient request.goal request.program arguments).fuse
    (publication request.source request.ticket request.premises request.ambient request.goal request.program arguments result)

def continueWith (request : Request) (reply : Reply request) : Execution :=
  match reply with
  | .error (.inl boundary) => .pure (.outsideFragment (.inr boundary))
  | .error (.inr budget) => .pure (.incomplete budget)
  | .ok arguments =>
      match request.source.applyOpen request.premises request.ambient request.goal request.program arguments with
      | .error invalid => .pure (.outsideFragment (.inl invalid))
      | .ok none => .pure (.refuted arguments)
      | .ok (some (source, proof)) =>
          .intent (publicationIntent request arguments proof) (.pure (.established (source, proof)))

def program (request : Request) : Execution := .request request (continueWith request)

/-- The unresolved program has the original request at its head. No model
call, success, or publication has been fabricated before a response. -/
theorem program_is_request (request : Request) :
    program request = Resumption.request request (continueWith request) := rfl

theorem incomplete_reply_keeps_budget (request : Request) (budget : Nat) :
    continueWith request (.error (.inr budget)) = .pure (.incomplete budget) := rfl

theorem boundary_reply_keeps_reason (request : Request) (reason : String) :
    continueWith request (.error (.inl reason)) = .pure (.outsideFragment (.inr reason)) := rfl

/-- Every publication intent produced by an arbitrary provider preserves
the evidence invariant. No correctness hypothesis about that provider occurs. -/
theorem continuation_intents_preserve
    (provider : (request : Request) → Reply request) (request : Request) (reply : Reply request)
    (initial : Multiset Cell) (branch : BranchTrace)
    (result : Result Request Reply (Multiset Cell) Answer (Span Cell))
    (returned : result ∈ runWorldsAt provider (continueWith request reply) initial branch)
    (intent : Span Cell) (emitted : intent ∈ result.world.intents)
    (store : Multiset Cell) (valid : StoreValid store) : StoreValid (intent.fire store) := by
  cases reply with
  | error stopped =>
      cases stopped <;> simp [continueWith, runWorldsAt_pure] at returned <;>
        subst result <;> simp at emitted
  | ok arguments =>
      cases checked : request.source.applyOpen request.premises request.ambient request.goal request.program arguments with
      | error problem =>
          simp [continueWith, checked, runWorldsAt_pure] at returned
          subst result
          simp at emitted
      | ok answer =>
          cases answer with
          | none =>
              simp [continueWith, checked, runWorldsAt_pure] at returned
              subst result
              simp at emitted
          | some pair =>
              rcases pair with ⟨source, proof⟩
              have sourceEq := (GSLTSource.applyOpen_exact checked).1
              subst source
              simp [continueWith, checked, runWorldsAt_intent, runWorldsAt_pure,
                Result.prepend] at returned
              subst result
              simp only [List.mem_singleton] at emitted
              subst intent
              exact fused_publication_preserves_validity _ _ _ _ _ _ _ _ store checked valid

/-- The same preservation holds for a completed request episode. Replies
are retained by the existing resumption evaluator. -/
theorem program_intents_preserve
    (provider : (request : Request) → Reply request) (request : Request)
    (initial : Multiset Cell) (branch : BranchTrace)
    (result : Result Request Reply (Multiset Cell) Answer (Span Cell))
    (returned : result ∈ runWorldsAt provider (program request) initial branch)
    (intent : Span Cell) (emitted : intent ∈ result.world.intents)
    (store : Multiset Cell) (valid : StoreValid store) : StoreValid (intent.fire store) := by
  simp only [program, runWorldsAt_request, List.mem_map] at returned
  obtain ⟨continuationResult, returned, same⟩ := returned
  subst result
  exact continuation_intents_preserve provider request (provider request) initial branch
    continuationResult returned intent emitted store valid

/-- An unfinished reply produces no publication intent and does not change
the private store. Its request and response remain visible in the history. -/
theorem unfinished_episode (request : Request) (budget : Nat) (initial : Multiset Cell) :
    runWorlds (fun _ => .error (.inr budget)) (program request) initial =
      [{ world := { branch := [], answer := .incomplete budget, state := initial, intents := [] },
         replies := [⟨request, .error (.inr budget)⟩] }] := by
  simp [runWorlds, program, runWorldsAt_request, continueWith, runWorldsAt_pure, Result.prepend]

#print axioms program_intents_preserve
#print axioms unfinished_episode

end Mettapedia.Languages.MeTTa.ProgrammableJudgmentServices
