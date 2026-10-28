import Mettapedia.Machines.CalleeAdmission
import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Callee-owned compilation refusal and input-local fallback

The reference chooses a prepared route from current compilation authority
and this input's readiness. The native adapter first reads exact revisioned
negative evidence, then judges the input and enters the callee. Only a
compilation refusal publishes a negative fact. An input refusal leaves the
owner's cache unchanged and cannot disable another call or caller.

This reuses RevisionedQueryFacts for the cache and CalleeAdmission for the
route. Native stamp completeness, truthful compiler refusal, synchronization
and body execution remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CalleeRefusalScope

open RevisionedQueryFacts CalleeAdmission

variable {Stamp Key Input : Type} [DecidableEq Stamp] [DecidableEq Key]

def facts (compiles : Stamp → Key → Bool) (stamp : Stamp) (key : Key) : List Unit :=
  if compiles stamp key then [] else [()]

def blocked (stamp : Stamp) (key : Key) (cache : Cache Stamp Key Unit) : Bool :=
  lookup stamp key cache == some [()]

theorem blocked_sound (compiles : Stamp → Key → Bool)
    (stamp : Stamp) (key : Key) (cache : Cache Stamp Key Unit)
    (valid : Valid (facts compiles) cache) (refused : blocked stamp key cache = true) :
    compiles stamp key = false := by
  have found : lookup stamp key cache = some [()] := by
    simpa [blocked] using refused
  have exactFact := lookup_sound (facts compiles) cache valid stamp key found
  cases compiled : compiles stamp key with
  | false => rfl
  | true =>
      simp only [facts, compiled, ite_true] at exactFact
      cases exactFact

def reference (compiles : Stamp → Key → Bool) (ready : Input → Bool)
    (stamp : Stamp) (key : Key) (input : Input) : Route Input Key :=
  if ready input && compiles stamp key then .code input key else .cursor

def attempt (compiles : Stamp → Key → Bool) (ready : Input → Bool)
    (stamp : Stamp) (key : Key) (input : Input) (cache : Cache Stamp Key Unit) :
    Route Input Key × Cache Stamp Key Unit :=
  if blocked stamp key cache then (.cursor, cache)
  else if ready input then
    if compiles stamp key then (.code input key, cache)
    else (.cursor, ⟨stamp, key, [()]⟩ :: cache)
  else (.cursor, cache)

theorem route_refines (compiles : Stamp → Key → Bool) (ready : Input → Bool)
    (stamp : Stamp) (key : Key) (input : Input) (cache : Cache Stamp Key Unit)
    (valid : Valid (facts compiles) cache) :
    (attempt compiles ready stamp key input cache).1 =
      reference compiles ready stamp key input := by
  cases refusal : blocked stamp key cache with
  | true =>
      have unavailable := blocked_sound compiles stamp key cache valid refusal
      simp [attempt, reference, refusal, unavailable]
  | false =>
      cases readiness : ready input <;> cases compiled : compiles stamp key <;>
        simp [attempt, reference, refusal, readiness, compiled]

theorem attempt_valid (compiles : Stamp → Key → Bool) (ready : Input → Bool)
    (stamp : Stamp) (key : Key) (input : Input) (cache : Cache Stamp Key Unit)
    (valid : Valid (facts compiles) cache) :
    Valid (facts compiles) (attempt compiles ready stamp key input cache).2 := by
  unfold attempt
  split
  · exact valid
  · split
    · split
      · exact valid
      · rename_i absent inputReady refused
        intro entry member
        rcases List.mem_cons.mp member with rfl | old
        · simp [facts, refused]
        · exact valid entry old
    · exact valid

theorem input_refusal_retains_cache (compiles : Stamp → Key → Bool)
    (ready : Input → Bool) (stamp : Stamp) (key : Key) (input : Input)
    (cache : Cache Stamp Key Unit) (refused : ready input = false) :
    (attempt compiles ready stamp key input cache).2 = cache := by
  cases observed : blocked stamp key cache <;> simp [attempt, observed, refused]

/-- The next call sees precisely the same owner authority after an
input-specific refusal, including when it comes from another cursor. -/
theorem later_input_remains_eligible (compiles : Stamp → Key → Bool)
    (ready : Input → Bool) (stamp : Stamp) (key : Key) (earlier later : Input)
    (cache : Cache Stamp Key Unit) (refused : ready earlier = false)
    (valid : Valid (facts compiles) cache) :
    (attempt compiles ready stamp key later
      (attempt compiles ready stamp key earlier cache).2).1 =
      reference compiles ready stamp key later := by
  rw [input_refusal_retains_cache compiles ready stamp key earlier cache refused]
  exact route_refines compiles ready stamp key later cache valid

namespace Controls

def compiles (revision head : Nat) : Bool := revision != 0 || head != 0

def negative : Cache Nat Nat Unit := [⟨0, 0, [()]⟩]

theorem old_revision_does_not_disable_new_compilation :
    (attempt compiles (fun _ : Nat => true) 1 0 7 negative).1 = .code 7 0 := by
  decide +kernel

theorem unrelated_head_keeps_its_prepared_entry :
    (attempt compiles (fun _ : Nat => true) 0 1 7 negative).1 = .code 7 1 := by
  decide +kernel

theorem stable_refusal_skips_input_admission (ready : Nat → Bool) :
    attempt compiles ready 0 0 7 negative = (.cursor, negative) := by
  rfl

def oldAttempt (enabled ready : Bool) : Route Nat Nat × Bool :=
  if enabled && ready then (.code 7 0, true) else (.cursor, false)

theorem global_input_poison_changes_the_later_route :
    (oldAttempt (oldAttempt true false).2 true).1 = .cursor ∧
    (attempt (fun _ _ : Nat => true) (· != 0) 0 0 7
      (attempt (fun _ _ : Nat => true) (· != 0) 0 0 0 []).2).1 = .code 7 0 := by
  decide +kernel

end Controls
end Mettapedia.Machines.CalleeRefusalScope

#print axioms Mettapedia.Machines.CalleeRefusalScope.blocked_sound
#print axioms Mettapedia.Machines.CalleeRefusalScope.route_refines
#print axioms Mettapedia.Machines.CalleeRefusalScope.attempt_valid
#print axioms Mettapedia.Machines.CalleeRefusalScope.input_refusal_retains_cache
#print axioms Mettapedia.Machines.CalleeRefusalScope.later_input_remains_eligible
#print axioms Mettapedia.Machines.CalleeRefusalScope.Controls.old_revision_does_not_disable_new_compilation
#print axioms Mettapedia.Machines.CalleeRefusalScope.Controls.unrelated_head_keeps_its_prepared_entry
#print axioms Mettapedia.Machines.CalleeRefusalScope.Controls.stable_refusal_skips_input_admission
#print axioms Mettapedia.Machines.CalleeRefusalScope.Controls.global_input_poison_changes_the_later_route
