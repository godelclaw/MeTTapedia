import Mettapedia.Machines.ReadOnlyQuery

/-!
# Admit a route before preparing its ready arguments

Admission and argument preparation are pure adaptive read programs. The
reference runs both before selecting the result; the refinement runs preparation
only after admission. Admission may itself read a versioned program store.
The answers agree, and a refused route's read certificate loses exactly the
preparation suffix. Accepted routes retain all reads in their original order.

This models adapter preparation of already evaluated values, not evaluation of
source arguments. Effectful evaluation cannot be moved by these results. The
native allocation/ownership and C correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyRouteAdmission

open ReadOnlyQuery

universe u v w x
variable {Key : Type u} {Value : Type v} {Argument : Type w} {Answer : Type x}

def prepareBefore (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) : Program Key Value Answer :=
  bind admission fun allowed =>
    map (fun argument => if allowed then consume argument else fallback) prepare

def admitBefore (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) : Program Key Value Answer :=
  bind admission fun allowed =>
    if allowed then map consume prepare else .pure fallback

theorem preserves_answer (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) :
    (run store (admitBefore admission prepare consume fallback)).answer =
      (run store (prepareBefore admission prepare consume fallback)).answer := by
  simp only [admitBefore, prepareBefore, run_bind]
  cases (run store admission).answer <;> simp [run_map, run]

theorem accepted_reads (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) (accepted : (run store admission).answer = true) :
    (run store (admitBefore admission prepare consume fallback)).reads =
      (run store (prepareBefore admission prepare consume fallback)).reads := by
  simp [admitBefore, prepareBefore, run_bind, run_map, accepted]

theorem refused_reads (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) (refused : (run store admission).answer = false) :
    (run store (admitBefore admission prepare consume fallback)).reads =
      (run store admission).reads ∧
    (run store (prepareBefore admission prepare consume fallback)).reads =
      (run store admission).reads ++ (run store prepare).reads := by
  simp [admitBefore, prepareBefore, run_bind, run_map, run, refused]

/-- The exact removed read suffix, including repeats and negative reads. -/
theorem read_suffix (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) :
    (run store (prepareBefore admission prepare consume fallback)).reads =
      (run store (admitBefore admission prepare consume fallback)).reads ++
        (if (run store admission).answer then [] else (run store prepare).reads) := by
  cases h : (run store admission).answer <;>
    simp [admitBefore, prepareBefore, run_bind, run_map, run, h]

theorem read_cost (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) :
    (run store (admitBefore admission prepare consume fallback)).reads.length ≤
      (run store (prepareBefore admission prepare consume fallback)).reads.length := by
  rw [read_suffix]
  simp only [List.length_append]
  exact Nat.le_add_right _ _

theorem strict_read_saving (store : Key → Value) (admission : Program Key Value Bool)
    (prepare : Program Key Value Argument) (consume : Argument → Answer)
    (fallback : Answer) (refused : (run store admission).answer = false)
    (nonempty : (run store prepare).reads ≠ []) :
    (run store (admitBefore admission prepare consume fallback)).reads.length <
      (run store (prepareBefore admission prepare consume fallback)).reads.length := by
  rw [read_suffix, refused]
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_append]
  have positive : 0 < (run store prepare).reads.length := by
    cases h : (run store prepare).reads with
    | nil => exact False.elim (nonempty h)
    | cons first rest => simp
  exact Nat.lt_add_of_pos_right positive

/-- A concrete preparation reads every requested coordinate in order. -/
def readAll (keys : List Key) : Program Key Value (List Value) :=
  match keys with
  | [] => .pure []
  | key :: rest => .read key fun value => map (value :: ·) (readAll rest)

theorem readAll_certificate (store : Key → Value) (keys : List Key) :
    (run store (readAll keys)).reads = samples store keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih => simp [readAll, run, run_map, samples, ih]

/-- Refusal omits every argument read even for an arbitrarily long sequence. -/
example (store : Nat → Nat) (argumentKeys : List Nat) (refused : store 0 = 0) :
    (run store (admitBefore (.read 0 fun gate => .pure (gate != 0))
      (readAll argumentKeys) List.length 0)).reads = [(0, 0)] := by
  simp [admitBefore, run_bind, run, refused]

/-- The optimization does not omit any argument reads after admission. -/
example (store : Nat → Nat) (argumentKeys : List Nat) (accepted : store 0 ≠ 0) :
    (run store (admitBefore (.read 0 fun gate => .pure (gate != 0))
      (readAll argumentKeys) List.length 0)).reads =
      (0, store 0) :: samples store argumentKeys := by
  simp [admitBefore, run_bind, run, accepted, run_map, readAll_certificate]

end Mettapedia.Machines.ReadOnlyRouteAdmission
