import Mettapedia.OSLF.NativeTypes.Certificates.Coding

/-!
# Fair resumable search for finite native derivation certificates

Natural-number code enumeration is complete by the constructive certificate
codec. A result is emitted only after the original judgment checker accepts it.
Running out of work retains a cursor and asserts no refutation. The discovery
bound depends on the complete encoded bit length, including all rule payloads.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Search

universe u

variable {P : Presentation.{u}} [Encodable P.Rule] [DecidableEq P.Judgment]

structure State (P : Presentation.{u}) where
  cursor : Nat
  found : Option (Tree P)

def initial : State P := ⟨0, none⟩

def step (judgment : P.Judgment) (state : State P) : State P :=
  match state.found with
  | some _ => state
  | none =>
      match Encodable.decode (α := Tree P) state.cursor with
      | none => ⟨state.cursor + 1, none⟩
      | some certificate =>
          if certificate.check judgment then ⟨state.cursor + 1, some certificate⟩
          else ⟨state.cursor + 1, none⟩

def run (judgment : P.Judgment) : Nat → State P → State P
  | 0, state => state
  | budget + 1, state => run judgment budget (step judgment state)

def search (judgment : P.Judgment) (budget : Nat) : State P := run judgment budget initial

theorem run_add (judgment : P.Judgment) (first second : Nat) (state : State P) :
    run judgment (first + second) state = run judgment second (run judgment first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
      simp only [Nat.succ_add, run, ih]

theorem run_settled (judgment : P.Judgment) (budget : Nat) (state : State P)
    (certificate : Tree P) (settled : state.found = some certificate) :
    run judgment budget state = state := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa only [run, step, settled] using ih

def State.Valid (judgment : P.Judgment) (state : State P) : Prop :=
  ∀ certificate, state.found = some certificate → certificate.check judgment = true

theorem step_valid (judgment : P.Judgment) (state : State P)
    (valid : state.Valid judgment) : (step judgment state).Valid judgment := by
  intro certificate found
  cases stored : state.found with
  | some old =>
      have same : state.found = some certificate := by simpa only [step, stored] using found
      exact valid certificate same
  | none =>
      cases decoded : Encodable.decode (α := Tree P) state.cursor with
      | none => simp only [step, stored, decoded] at found; cases found
      | some candidate =>
          cases accepted : candidate.check judgment with
          | false => simp only [step, stored, decoded, accepted, Bool.false_eq_true, if_false] at found; cases found
          | true =>
              have same : candidate = certificate := by simpa only [step, stored, decoded,
                accepted, if_true, Option.some.injEq] using found
              simpa only [← same] using accepted

theorem run_valid (judgment : P.Judgment) (budget : Nat) (state : State P)
    (valid : state.Valid judgment) : (run judgment budget state).Valid judgment := by
  induction budget generalizing state with
  | zero => exact valid
  | succ budget ih => exact ih (step judgment state) (step_valid judgment state valid)

theorem search_sound (judgment : P.Judgment) (budget : Nat) (certificate : Tree P)
    (found : (search judgment budget).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate := by
  apply (Tree.check_exact certificate judgment).mp
  exact run_valid judgment budget initial (by intro certificate impossible; cases impossible)
    certificate found

theorem step_cursor (judgment : P.Judgment) (state : State P)
    (unresolved : state.found = none) : (step judgment state).cursor = state.cursor + 1 := by
  cases decoded : Encodable.decode (α := Tree P) state.cursor with
  | none => simp only [step, unresolved, decoded]
  | some certificate =>
      cases accepted : certificate.check judgment <;>
        simp only [step, unresolved, decoded, accepted, Bool.false_eq_true, if_false, if_true]

theorem step_at_encoded (judgment : P.Judgment) (state : State P) (certificate : Tree P)
    (unresolved : state.found = none) (cursor : state.cursor = Encodable.encode certificate)
    (accepted : certificate.check judgment = true) :
    (step judgment state).found = some certificate := by
  simp only [step, unresolved, cursor, Tree.decode_encode, accepted, if_true]

theorem complete_from (judgment : P.Judgment) (certificate : Tree P)
    (accepted : certificate.check judgment = true) (budget : Nat) (state : State P)
    (before : state.cursor ≤ Encodable.encode certificate)
    (sufficient : Encodable.encode certificate < state.cursor + budget) :
    ∃ result, (run judgment budget state).found = some result := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
      cases stored : state.found with
      | some result => exact ⟨result, by rw [run_settled judgment (budget + 1) state result stored]; exact stored⟩
      | none =>
          by_cases atCertificate : state.cursor = Encodable.encode certificate
          · have found := step_at_encoded judgment state certificate stored atCertificate accepted
            exact ⟨certificate, by rw [run, run_settled judgment budget _ certificate found]; exact found⟩
          · have nextCursor := step_cursor judgment state stored
            have nextBefore : (step judgment state).cursor ≤ Encodable.encode certificate := by omega
            have nextSufficient : Encodable.encode certificate < (step judgment state).cursor + budget := by omega
            exact ih (step judgment state) nextBefore nextSufficient

theorem discover_within_wire_bound (judgment : P.Judgment) (certificate : Tree P)
    (accepted : certificate.check judgment = true) :
    ∃ result, (search judgment (Tree.discoveryBound (Tree.wireSize certificate))).found = some result :=
  complete_from judgment certificate accepted _ initial (Nat.zero_le _)
    (by simpa only [initial, Nat.zero_add] using Tree.code_lt_discoveryBound certificate)

theorem stable_conclusion (judgment : P.Judgment) (budget extra : Nat) (certificate : Tree P)
    (found : (search judgment budget).found = some certificate) :
    search judgment (budget + extra) = search judgment budget := by
  exact (run_add judgment budget extra initial).trans
    (run_settled judgment extra (search judgment budget) certificate found)

end Mettapedia.OSLF.NativeTypes.Certificates.Search
