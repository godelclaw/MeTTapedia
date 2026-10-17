import Mettapedia.Languages.Megalodon.BorrowedProofCursor

/-!
# Distinguishing local inference refusal from conversion exhaustion

The Boolean row interface decides a bounded relation. This observation retains
the reason a local request has no requirements: missing references, malformed
rule shapes and mismatched types refuse; an unfinished normalization exhausts.
A native service must retain/retry the latter instead of reporting a false
mathematical judgment. Parsing failures are outside this typed row interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.RuleObservation

open MathdataKernel BorrowedProofCursor

inductive Outcome where
  | requirements (premises : List Judgment)
  | refused
  | exhausted
  deriving DecidableEq, Repr

def Outcome.erase : Outcome → Option (List Judgment)
  | .requirements premises => some premises
  | .refused | .exhausted => none

def observe (environment : Environment) (fuel : Nat) (witness : Witness) (conclusion : Judgment) : Outcome :=
  let context := conclusion.context
  let proposition := conclusion.proposition
  match witness with
  | .hyp index => if context.hypotheses[index]? = some proposition then .requirements [] else .refused
  | .known name => match environment.lookupKnown? name with
      | none => .refused
      | some source => match normalize environment fuel source with
          | none => .exhausted
          | some result => if result = proposition then .requirements [] else .refused
  | .termApp argument domain body =>
      if inferTerm environment context.typeDepth context.terms argument ≠ some domain then .refused else
        match deltaNormalize environment fuel argument with
        | none => .exhausted
        | some normalized => match normalize environment fuel (Tm.instantiate normalized body) with
            | none => .exhausted
            | some result => if result = proposition then .requirements [⟨context, .all domain body⟩] else .refused
  | .proofApp domain => .requirements [⟨context, .imp domain proposition⟩, ⟨context, domain⟩]
  | .termLam => match proposition with
      | .all type body => if type.plainWellFormed context.typeDepth then
          .requirements [⟨context.termBinder type, body⟩] else .refused
      | _ => .refused
  | .proofLam source => match proposition with
      | .imp normalized body =>
          if inferTerm environment context.typeDepth context.terms source ≠ some .prop then .refused else
            match normalize environment fuel source with
            | none => .exhausted
            | some result => if result = normalized then
                .requirements [⟨context.proofBinder normalized, body⟩] else .refused
      | _ => .refused
  | .typeApp type body => if Tm.typeInstantiate type body = proposition then
      .requirements [⟨context, .typeAll body⟩] else .refused
  | .typeLam => match proposition with
      | .typeAll body => if context.terms = [] ∧ context.hypotheses = [] then
          .requirements [⟨context.typeBinder, body⟩] else .refused
      | _ => .refused

theorem observe_erases (environment : Environment) (fuel : Nat) (witness : Witness) (conclusion : Judgment) :
    (observe environment fuel witness conclusion).erase = requirements environment fuel witness conclusion := by
  rcases conclusion with ⟨context, proposition⟩
  cases witness with
  | hyp index => simp only [observe, requirements]; split <;> rfl
  | known name =>
      cases found : environment.lookupKnown? name with
      | none => simp [observe, requirements, found, Outcome.erase]
      | some source =>
          cases normalized : normalize environment fuel source with
          | none => simp [observe, requirements, found, normalized, Outcome.erase]
          | some result =>
              by_cases same : result = proposition <;>
                simp [observe, requirements, found, normalized, same, Outcome.erase]
  | termApp argument domain body =>
      by_cases typed : inferTerm environment context.typeDepth context.terms argument = some domain
      · cases unfolded : deltaNormalize environment fuel argument with
        | none => simp [observe, requirements, typed, unfolded, Outcome.erase]
        | some normalized =>
            cases result : normalize environment fuel (Tm.instantiate normalized body) with
            | none => simp [observe, requirements, typed, unfolded, result, Outcome.erase]
            | some actual =>
                by_cases same : actual = proposition <;>
                  simp [observe, requirements, typed, unfolded, result, same, Outcome.erase]
      · simp [observe, requirements, typed, Outcome.erase]
  | proofApp => rfl
  | termLam =>
      cases proposition <;> simp only [observe, requirements]
      all_goals try rfl
      rename_i type body
      by_cases formed : type.plainWellFormed context.typeDepth = true <;> simp [formed, Outcome.erase]
  | proofLam source =>
      cases proposition <;> simp only [observe, requirements, Outcome.erase]
      rename_i normalized body
      by_cases typed : inferTerm environment context.typeDepth context.terms source = some .prop
      · cases result : normalize environment fuel source with
        | none => simp [typed]
        | some actual =>
            by_cases same : actual = normalized <;> simp [typed, same]
      · simp [typed]
  | typeApp type body => simp only [observe, requirements]; split <;> rfl
  | typeLam =>
      cases proposition <;> simp only [observe, requirements]
      all_goals try rfl
      by_cases empty : context.terms = [] ∧ context.hypotheses = [] <;> simp [empty, Outcome.erase]

theorem requirements_iff (environment : Environment) (fuel : Nat) (witness : Witness)
    (conclusion : Judgment) (parents : List Judgment) :
    observe environment fuel witness conclusion = .requirements parents ↔
      requirements environment fuel witness conclusion = some parents := by
  rw [← observe_erases]
  cases observe environment fuel witness conclusion <;> simp [Outcome.erase]

theorem accepted_sound {environment : Environment} {fuel : Nat} {witness : Witness}
    {conclusion : Judgment} {parents : List Judgment}
    (accepted : observe environment fuel witness conclusion = .requirements parents) :
    Rules environment fuel parents conclusion :=
  requirements_sound ((requirements_iff environment fuel witness conclusion parents).mp accepted)

namespace Controls
private def environment : Environment :=
  { terms := [⟨"p", .prop, none⟩, ⟨"alias", .prop, some (.named "p")⟩]
    known := [⟨"proof", .named "alias"⟩] }
private def claim : Judgment := ⟨⟨0, [], []⟩, .named "p"⟩

theorem insufficient_conversion_fuel_is_exhaustion :
    observe environment 0 (.known "proof") claim = .exhausted := by
  simp [observe, environment, Environment.lookupKnown?, lookupKnownList?,
    MathdataKernel.normalize, deltaNormalize, Environment.lookupTerm?, lookupTermList?]

theorem retry_preserves_request_and_accepts :
    observe environment 1 (.known "proof") claim = .requirements [] := by
  simp [observe, environment, claim, Environment.lookupKnown?, lookupKnownList?,
    MathdataKernel.normalize, deltaNormalize, Environment.lookupTerm?, lookupTermList?,
    Tm.normalize, Tm.normalizeOne]

theorem missing_known_is_refusal : observe environment 0 (.known "missing") claim = .refused := by decide
theorem changing_claim_is_refusal :
    observe environment 1 (.known "proof") ⟨⟨0, [], []⟩, .prim 0⟩ = .refused := by
  simp [observe, environment, Environment.lookupKnown?, lookupKnownList?, MathdataKernel.normalize,
    deltaNormalize, Environment.lookupTerm?, lookupTermList?, Tm.normalize, Tm.normalizeOne]
end Controls

end Mettapedia.Languages.Megalodon.RuleObservation
