import Mathlib.Data.List.Basic

/-! # Partial intrinsic dispatch

A registry entry in another language does not authorize an intrinsic here.
An unavailable intrinsic is distinct from a handled call with no answers.
This small dispatch model specifies that distinction; it does not verify a C
implementation or assume correctness of the intrinsic or host interpreter.
-/
set_option autoImplicit false
namespace Mettapedia.Machines.IntrinsicDispatch

variable {Query Answer : Type}

inductive Evaluates (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer) :
    Query → Answer → Prop
  | native {q answers a} : allowed q = true → native q = some answers →
      a ∈ answers → Evaluates allowed native host q a
  | unowned {q a} : allowed q = false → a ∈ host q →
      Evaluates allowed native host q a
  | unavailable {q a} : native q = none → a ∈ host q →
      Evaluates allowed native host q a

def run (allowed : Query → Bool) (native : Query → Option (List Answer))
    (host : Query → List Answer) (q : Query) : List Answer :=
  if allowed q then (native q).getD (host q) else host q

/-- Whole-answer semantics retains occurrences, including an empty handled
call. Declining an implementation is a separate semantic case. -/
inductive Answers (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer) :
    Query → List Answer → Prop
  | native {q xs} : allowed q = true → native q = some xs →
      Answers allowed native host q xs
  | unowned {q} : allowed q = false → Answers allowed native host q (host q)
  | unavailable {q} : native q = none → Answers allowed native host q (host q)

theorem run_eq_iff (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (q : Query) (xs : List Answer) :
    run allowed native host q = xs ↔ Answers allowed native host q xs := by
  constructor
  · intro h
    subst xs
    cases ha : allowed q with
    | false => simpa [run, ha] using Answers.unowned (native := native) (host := host) ha
    | true =>
      cases hn : native q with
      | none => simpa [run, ha, hn] using Answers.unavailable (allowed := allowed) (host := host) hn
      | some ys => simpa [run, ha, hn] using Answers.native (host := host) ha hn
  · intro h
    cases h with
    | native ha hn => simp [run, ha, hn]
    | unowned ha => simp [run, ha]
    | unavailable hn => cases ha : allowed q <;> simp [run, ha, hn]

theorem mem_run_iff (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (q : Query) (a : Answer) :
    a ∈ run allowed native host q ↔ Evaluates allowed native host q a := by
  constructor
  · intro h
    cases ha : allowed q with
    | false => exact .unowned ha (by simpa [run, ha] using h)
    | true =>
      cases hn : native q with
      | none => exact .unavailable hn (by simpa [run, ha, hn] using h)
      | some xs => exact .native ha hn (by simpa [run, ha, hn] using h)
  · intro h
    cases h with
    | native ha hn hm => simpa [run, ha, hn] using hm
    | unowned ha hm => simpa [run, ha] using hm
    | unavailable hn hm => cases ha : allowed q <;> simpa [run, ha, hn] using hm

-- A declined native division may have an ordinary user equation.
example : run (fun _ : Unit => true) (fun _ => none) (fun _ => [5, 5]) () =
    ([5, 5] : List Nat) := rfl

-- A genuine handled failure must not invoke those equations.
example : run (fun _ : Unit => true) (fun _ => some []) (fun _ => [5]) () =
    ([] : List Nat) := rfl

-- Global recognition of a name cannot override this language's ownership.
example : run (fun _ : Unit => false) (fun _ => some [0]) (fun _ => [5]) () ≠
    ([] : List Nat) := by decide

namespace ClosedCalls

/-! A closed worker may omit per-call ownership checks only after its finite
call inventory passes admission. The source below dispatches each occurrence
under its dialect; the worker uses the machine's implementation table directly.
Admission is computed from ownership and availability, not assumed equality of
their results. This pure call-sequence model does not establish C reachability,
effect scheduling, declaration currency or native classifier correspondence. -/

def admitted (allowed : Query → Bool) (native : Query → Option (List Answer))
    (calls : List Query) : Bool :=
  calls.all fun query => allowed query || (native query).isNone

def source (allowed : Query → Bool) (native : Query → Option (List Answer))
    (host : Query → List Answer) : List Query → List Answer
  | [] => []
  | query :: rest => run allowed native host query ++ source allowed native host rest

def worker (native : Query → Option (List Answer))
    (host : Query → List Answer) (calls : List Query) : List Answer :=
  calls.flatMap fun query => (native query).getD (host query)

theorem admitted_call_refines (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (query : Query) (permission : allowed query || (native query).isNone = true) :
    (native query).getD (host query) = run allowed native host query := by
  cases owns : allowed query with
  | true => simp [run, owns]
  | false =>
      cases implementation : native query with
      | none => simp [run, owns]
      | some answers => simp [owns, implementation] at permission

/-- Whole ordered observations are preserved, including duplicates and a
handled empty result. An unowned available native excludes the worker. -/
theorem admitted_worker_refines (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (calls : List Query) (permission : admitted allowed native calls = true) :
    worker native host calls = source allowed native host calls := by
  induction calls with
  | nil => rfl
  | cons query rest ih =>
      have both : (allowed query || (native query).isNone = true) ∧
          admitted allowed native rest = true := by
        simpa [admitted, List.all_cons, Bool.and_eq_true] using permission
      simp only [worker, List.flatMap_cons, source]
      rw [admitted_call_refines allowed native host query both.1]
      exact congrArg (run allowed native host query ++ ·) (ih both.2)

theorem unowned_available_refuses (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (query : Query) (rest : List Query)
    (unowned : allowed query = false) (available : (native query).isSome = true) :
    admitted allowed native (query :: rest) = false := by
  cases implementation : native query with
  | none => simp [implementation] at available
  | some answers => simp [admitted, unowned, implementation]

namespace Controls

def owns (query : Nat) : Bool := query == 0
def implementations : Nat → Option (List Nat)
  | 0 => some [1]
  | 1 => some [2]
  | _ => none
def authored (_query : Nat) : List Nat := [88, 88]

theorem shared_and_ordinary_occurrences :
    admitted owns implementations [0, 0, 2, 2] = true ∧
    worker implementations authored [0, 0, 2, 2] = [1, 1, 88, 88, 88, 88] ∧
    source owns implementations authored [0, 0, 2, 2] = [1, 1, 88, 88, 88, 88] := by
  decide

theorem backend_name_cannot_replace_authored_answers :
    admitted owns implementations [1] = false ∧
    source owns implementations authored [1] = [88, 88] ∧
    worker implementations authored [1] = [2] := by decide

end Controls
end ClosedCalls
end Mettapedia.Machines.IntrinsicDispatch

#print axioms Mettapedia.Machines.IntrinsicDispatch.run_eq_iff
#print axioms Mettapedia.Machines.IntrinsicDispatch.mem_run_iff
#print axioms Mettapedia.Machines.IntrinsicDispatch.ClosedCalls.admitted_call_refines
#print axioms Mettapedia.Machines.IntrinsicDispatch.ClosedCalls.admitted_worker_refines
#print axioms Mettapedia.Machines.IntrinsicDispatch.ClosedCalls.unowned_available_refuses
#print axioms Mettapedia.Machines.IntrinsicDispatch.ClosedCalls.Controls.shared_and_ordinary_occurrences
#print axioms Mettapedia.Machines.IntrinsicDispatch.ClosedCalls.Controls.backend_name_cannot_replace_authored_answers
