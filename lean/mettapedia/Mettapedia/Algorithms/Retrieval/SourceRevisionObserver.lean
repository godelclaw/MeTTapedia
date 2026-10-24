import Mettapedia.GSLT.Dynamics.PartialRegionPlan

/-!
An all-source revision observer with separate data admission and execution.
The ordinary observation collects every stale row; the optimized loop carries
one Boolean. Unsupported carriers and bounded-native-number cases decline to
the complete ordinary observation. The model covers algorithmic observations,
not pointer ownership, the native resolver, or C execution.
-/

namespace Mettapedia.Algorithms.Retrieval.SourceRevisionObserver

open Mettapedia.GSLT.Dynamics.PartialRegionPlan

variable {Owner : Type}

abbrev Guard (Owner : Type) := Owner × Nat

def eraseRows : List (Option (Guard Owner)) → Option (List (Guard Owner))
  | [] => some []
  | none :: _ => none
  | some row :: rest => (row :: ·) <$> eraseRows rest

/-- Shape/expected-number admission does not read the world. -/
def captureRows (limit : Nat) : List (Option (Guard Owner)) → Option (List (Guard Owner))
  | [] => some []
  | none :: _ => none
  | some row :: rest =>
      if row.2 ≤ limit then (row :: ·) <$> captureRows limit rest else none

/-- Collect the complete stale-row observation, retaining later read errors. -/
def staleRows (read : Owner → Nat) (limit : Nat) :
    List (Guard Owner) → Option (List (Guard Owner))
  | [] => some []
  | row :: rest =>
      if read row.1 ≤ limit then
        (fun stale => if read row.1 = row.2 then stale else row :: stale) <$>
          staleRows read limit rest
      else none

def source (read : Owner → Nat) (limit : Nat) (rows : List (Option (Guard Owner))) :
    Option Bool :=
  (eraseRows rows).bind fun guards => List.isEmpty <$> staleRows read limit guards

/-- A mismatch never skips a later source or its number-range check. -/
def scan (read : Owner → Nat) (limit : Nat) (current : Bool) :
    List (Guard Owner) → Option Bool
  | [] => some current
  | row :: rest =>
      if read row.1 ≤ limit then
        scan read limit (current && decide (read row.1 = row.2)) rest
      else none

theorem captureRows_erases (limit : Nat) (rows : List (Option (Guard Owner)))
    (guards : List (Guard Owner)) (captured : captureRows limit rows = some guards) :
    eraseRows rows = some guards := by
  induction rows generalizing guards with
  | nil => simpa [captureRows, eraseRows] using captured
  | cons row rest ih =>
      cases row with
      | none => simp [captureRows] at captured
      | some row =>
          by_cases fits : row.2 ≤ limit
          · cases tail : captureRows limit rest with
            | none => simp [captureRows, fits, tail] at captured
            | some suffix =>
                simp [captureRows, fits, tail] at captured
                subst guards
                simp [eraseRows, ih suffix tail]
          · simp [captureRows, fits] at captured

theorem scan_eq_stale_observation (read : Owner → Nat) (limit : Nat)
    (guards : List (Guard Owner)) (current : Bool) :
    scan read limit current guards =
      (fun stale => current && stale.isEmpty) <$> staleRows read limit guards := by
  induction guards generalizing current with
  | nil => simp [scan, staleRows]
  | cons row rest ih =>
      by_cases fits : read row.1 ≤ limit
      · by_cases same : read row.1 = row.2 <;>
          cases tail : staleRows read limit rest <;>
            simp [scan, staleRows, fits, same, ih, tail]
      · simp [scan, staleRows, fits]

def attempt (enabled : Bool) (read : Owner → Nat) (limit : Nat)
    (rows : List (Option (Guard Owner))) :
    Attempt (List (Option (Guard Owner))) (Option Bool) :=
  if enabled then
    match captureRows limit rows with
    | none => .declined rows
    | some guards =>
        match scan read limit true guards with
        | none => .declined rows
        | some current => .committed (some current)
  else .declined rows

theorem restores (enabled : Bool) (read : Owner → Nat) (limit : Nat) :
    RestoresOnDecline (attempt enabled read limit) := by
  intro rows restored declined
  cases enabled <;> simp only [attempt, Bool.false_eq_true, ↓reduceIte] at declined
  · exact Attempt.declined.inj declined.symm
  · cases captured : captureRows limit rows with
    | none => simpa [captured] using declined.symm
    | some guards =>
        cases scanned : scan read limit true guards <;>
          simp_all

theorem commits (enabled : Bool) (read : Owner → Nat) (limit : Nat) :
    ExactOnCommit (attempt enabled read limit) (source read limit) := by
  intro rows observed committed
  cases enabled <;> simp only [attempt, Bool.false_eq_true, ↓reduceIte] at committed
  · cases committed
  · cases captured : captureRows limit rows with
    | none => simp [captured] at committed
    | some guards =>
        cases scanned : scan read limit true guards with
        | none => simp [captured, scanned] at committed
        | some current =>
            simp only [captured, scanned, Attempt.committed.injEq] at committed
            subst observed
            have ordinary := scan_eq_stale_observation read limit guards true
            simp only [Bool.true_and] at ordinary
            rw [ordinary] at scanned
            simpa [source, captureRows_erases limit rows guards captured] using scanned.symm

theorem realize_eq_source (enabled : Bool) (read : Owner → Nat) (limit : Nat) :
    realize (attempt enabled read limit) (source read limit) = source read limit :=
  realize_exact _ _ (restores enabled read limit) (commits enabled read limit)

example : scan (fun (_ : Bool) => 1) 8 true [(false, 1), (true, 1)] = some true := by
  decide +kernel

example : scan (fun (_ : Bool) => 1) 8 true [(false, 1), (true, 2)] = some false := by
  decide +kernel

example : attempt true (fun (_ : Bool) => 1) 8 [some (false, 1), none] =
    .declined [some (false, 1), none] := by
  rfl

example : realize (attempt true (fun (_ : Bool) => 1) 8)
    (source (fun (_ : Bool) => 1) 8) [some (false, 9)] = some false := by
  decide +kernel

example : scan (fun key : Bool => if key then 9 else 1) 8 false
    [(false, 1), (true, 1)] = none := by
  decide +kernel

#print axioms realize_eq_source

end Mettapedia.Algorithms.Retrieval.SourceRevisionObserver
