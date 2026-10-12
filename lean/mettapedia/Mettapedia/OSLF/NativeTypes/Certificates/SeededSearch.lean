import Mettapedia.OSLF.NativeTypes.Certificates.Search

/-!
# Checked finite prefixes of fair certificate search

An ordered finite prefix may contain arbitrary certificate candidates. Each is
checked against the requested independent judgment before it is accepted. The
complete raw-code stream follows the prefix; adding seeds preserves fairness.
A paused cursor retains the position in both phases and conclusive results stop.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch

universe u

variable {P : Presentation.{u}} [Encodable P.Rule]

def candidate (seeds : List (Tree P)) (position : Nat) : Option (Tree P) :=
  if position < seeds.length then seeds[position]? else
    Encodable.decode (α := Tree P) (position - seeds.length)

theorem candidate_at_encoded (seeds : List (Tree P)) (certificate : Tree P) :
    candidate seeds (seeds.length + Encodable.encode certificate) = some certificate := by
  have after : ¬seeds.length + Encodable.encode certificate < seeds.length := by omega
  simp only [candidate, after, if_false, Nat.add_sub_cancel_left, Tree.decode_encode]

variable [DecidableEq P.Judgment]

def step (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P) : Search.State P :=
  match state.found with
  | some _ => state
  | none =>
      match candidate seeds state.cursor with
      | none => ⟨state.cursor + 1, none⟩
      | some certificate =>
          if certificate.check judgment then ⟨state.cursor + 1, some certificate⟩
          else ⟨state.cursor + 1, none⟩

def run (seeds : List (Tree P)) (judgment : P.Judgment) : Nat → Search.State P → Search.State P
  | 0, state => state
  | budget + 1, state => run seeds judgment budget (step seeds judgment state)

def search (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat) : Search.State P :=
  run seeds judgment budget Search.initial

theorem run_add (seeds : List (Tree P)) (judgment : P.Judgment)
    (first second : Nat) (state : Search.State P) :
    run seeds judgment (first + second) state =
      run seeds judgment second (run seeds judgment first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simp only [Nat.succ_add, run, ih]

theorem run_settled (seeds : List (Tree P)) (judgment : P.Judgment)
    (budget : Nat) (state : Search.State P) (certificate : Tree P)
    (settled : state.found = some certificate) : run seeds judgment budget state = state := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa only [run, step, settled] using ih

theorem step_valid (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P)
    (valid : state.Valid judgment) : (step seeds judgment state).Valid judgment := by
  intro certificate found
  cases stored : state.found with
  | some old =>
      have same : state.found = some certificate := by simpa only [step, stored] using found
      exact valid certificate same
  | none =>
      cases decoded : candidate seeds state.cursor with
      | none => simp only [step, stored, decoded] at found; cases found
      | some possible =>
          cases accepted : possible.check judgment with
          | false =>
              simp only [step, stored, decoded, accepted, Bool.false_eq_true, if_false] at found
              cases found
          | true =>
              have same : possible = certificate := by simpa only [step, stored, decoded,
                accepted, if_true, Option.some.injEq] using found
              simpa only [← same] using accepted

theorem run_valid (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat)
    (state : Search.State P) (valid : state.Valid judgment) : (run seeds judgment budget state).Valid judgment := by
  induction budget generalizing state with
  | zero => exact valid
  | succ budget ih => exact ih (step seeds judgment state) (step_valid seeds judgment state valid)

theorem search_sound (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat)
    (certificate : Tree P) (found : (search seeds judgment budget).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate := by
  apply (Tree.check_exact certificate judgment).mp
  exact run_valid seeds judgment budget Search.initial
    (by intro certificate impossible; cases impossible) certificate found

theorem step_cursor (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P)
    (unresolved : state.found = none) : (step seeds judgment state).cursor = state.cursor + 1 := by
  cases decoded : candidate seeds state.cursor with
  | none => simp only [step, unresolved, decoded]
  | some certificate =>
      cases accepted : certificate.check judgment <;>
        simp only [step, unresolved, decoded, accepted, Bool.false_eq_true, if_false, if_true]

theorem step_at_encoded (seeds : List (Tree P)) (judgment : P.Judgment)
    (state : Search.State P) (certificate : Tree P) (unresolved : state.found = none)
    (cursor : state.cursor = seeds.length + Encodable.encode certificate)
    (accepted : certificate.check judgment = true) :
    (step seeds judgment state).found = some certificate := by
  simp only [step, unresolved, cursor, candidate_at_encoded, accepted, if_true]

theorem complete_from (seeds : List (Tree P)) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true)
    (budget : Nat) (state : Search.State P)
    (before : state.cursor ≤ seeds.length + Encodable.encode certificate)
    (sufficient : seeds.length + Encodable.encode certificate < state.cursor + budget) :
    ∃ result, (run seeds judgment budget state).found = some result := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
      cases stored : state.found with
      | some result =>
          exact ⟨result, by rw [run_settled seeds judgment (budget + 1) state result stored]; exact stored⟩
      | none =>
          by_cases atCertificate : state.cursor = seeds.length + Encodable.encode certificate
          · have found := step_at_encoded seeds judgment state certificate stored atCertificate accepted
            exact ⟨certificate, by rw [run, run_settled seeds judgment budget _ certificate found]; exact found⟩
          · have nextCursor := step_cursor seeds judgment state stored
            have nextBefore : (step seeds judgment state).cursor ≤ seeds.length + Encodable.encode certificate := by omega
            have nextSufficient : seeds.length + Encodable.encode certificate <
                (step seeds judgment state).cursor + budget := by omega
            exact ih (step seeds judgment state) nextBefore nextSufficient

def discoveryBound (prefixLength wireBits : Nat) : Nat := prefixLength + Tree.discoveryBound wireBits

theorem discover_within_wire_bound (seeds : List (Tree P)) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true) :
    ∃ result,
      (search seeds judgment (discoveryBound seeds.length (Tree.wireSize certificate))).found = some result := by
  apply complete_from seeds judgment certificate accepted _ Search.initial (Nat.zero_le _)
  have bound := Tree.code_lt_discoveryBound certificate
  change seeds.length + Encodable.encode certificate <
    0 + (seeds.length + Tree.discoveryBound (Tree.wireSize certificate))
  omega

theorem stable_conclusion (seeds : List (Tree P)) (judgment : P.Judgment)
    (budget extra : Nat) (certificate : Tree P)
    (found : (search seeds judgment budget).found = some certificate) :
    search seeds judgment (budget + extra) = search seeds judgment budget :=
  (run_add seeds judgment budget extra Search.initial).trans
    (run_settled seeds judgment extra (search seeds judgment budget) certificate found)

end Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch
