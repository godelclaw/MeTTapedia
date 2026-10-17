import Mathlib.Tactic

/-!
# Reusing the vacancy discovered by an intern probe

The probe checks keys and stops at a matching cell, an empty cell, or the end
of its finite probe sequence. The reference performs a second vacancy scan on
miss; the fused implementation uses the vacancy returned by the first probe.
These distinct executable algorithms agree on an unchanged sequence. A stale
vacancy is not a license to overwrite a newly occupied cell.

This models a table's linear probe sequence, not its native hash, wraparound,
allocation, resizing, or concurrency. A native hint must be invalidated by a
change of table layout or intervening insertion.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.IncrementalConformance.InternProbe

variable {Key Value : Type*} [DecidableEq Key]
abbrev Cells (Key Value : Type*) := List (Option (Key × Value))

def probe (key : Key) : Cells Key Value → Option Value × Option Nat
  | [] => (none, none)
  | none :: _ => (none, some 0)
  | some (stored, value) :: tail =>
      if key = stored then (some value, none)
      else let result := probe key tail
           (result.1, result.2.map Nat.succ)

def firstEmpty : Cells Key Value → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: tail => (firstEmpty tail).map Nat.succ

theorem miss_vacancy (key : Key) (cells : Cells Key Value)
    (miss : (probe key cells).1 = none) :
    (probe key cells).2 = firstEmpty cells := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
      cases cell with
      | none => rfl
      | some pair =>
          rcases pair with ⟨stored, value⟩
          by_cases same : key = stored
          · simp [probe, same] at miss
          · have rest : (probe key tail).1 = none := by
              simpa [probe, same] using miss
            simpa [probe, firstEmpty, same] using
              congrArg (Option.map Nat.succ) (ih rest)

def install (cells : Cells Key Value) (key : Key) (value : Value)
    (vacancy : Option Nat) : Option Value × Cells Key Value :=
  match vacancy with
  | none => (none, cells)
  | some index => (some value, cells.set index (some (key, value)))

def fused (cells : Cells Key Value) (key : Key) (value : Value) :
    Option Value × Cells Key Value :=
  let result := probe key cells
  match result.1 with
  | some old => (some old, cells)
  | none => install cells key value result.2

def twoScans (cells : Cells Key Value) (key : Key) (value : Value) :
    Option Value × Cells Key Value :=
  match (probe key cells).1 with
  | some old => (some old, cells)
  | none => install cells key value (firstEmpty cells)

theorem fused_agrees (cells : Cells Key Value) (key : Key) (value : Value) :
    fused cells key value = twoScans cells key value := by
  cases found : (probe key cells).1 with
  | none => simp [fused, twoScans, found, miss_vacancy key cells found]
  | some old => simp [fused, twoScans, found]

def probeVisits (key : Key) : Cells Key Value → Nat
  | [] => 0
  | none :: _ => 1
  | some (stored, _) :: tail => if key = stored then 1 else 1 + probeVisits key tail

def emptyVisits : Cells Key Value → Nat
  | [] => 0
  | none :: _ => 1
  | some _ :: tail => 1 + emptyVisits tail

def twoScanVisits (cells : Cells Key Value) (key : Key) : Nat :=
  probeVisits key cells + if (probe key cells).1 = none then emptyVisits cells else 0

theorem fused_visits_le (cells : Cells Key Value) (key : Key) :
    probeVisits key cells ≤ twoScanVisits cells key := by
  simp only [twoScanVisits]
  omega

/-- Ordered admission stops at the first exhausted probe, retaining the
canonical identities of the admitted prefix, including repeated requests. -/
def fusedBatch (cells : Cells Key Value) : List (Key × Value) →
    List Value × Cells Key Value × Bool
  | [] => ([], cells, true)
  | (key, value) :: tail =>
      let result := fused cells key value
      match result.1 with
      | none => ([], result.2, false)
      | some id =>
          let rest := fusedBatch result.2 tail
          (id :: rest.1, rest.2)

/-- Reference batch executes the separately stated scalar two-scan procedure
in request order; exhaustion prevents subsequent requests from running. -/
def scalarBatch (cells : Cells Key Value) : List (Key × Value) →
    List Value × Cells Key Value × Bool
  | [] => ([], cells, true)
  | (key, value) :: tail =>
      let result := twoScans cells key value
      match result.1 with
      | none => ([], result.2, false)
      | some id =>
          let rest := scalarBatch result.2 tail
          (id :: rest.1, rest.2)

theorem batch_agrees (requests : List (Key × Value)) (cells : Cells Key Value) :
    fusedBatch cells requests = scalarBatch cells requests := by
  induction requests generalizing cells with
  | nil => rfl
  | cons request tail ih =>
      rcases request with ⟨key, value⟩
      simp only [fusedBatch, scalarBatch, fused_agrees]
      cases (twoScans cells key value).1 <;> simp only [ih]


/-- A finite ordered clause model. Nonempty bodies stand for guarded rules;
calling them may produce rows that mere stored-fact enumeration must omit. -/
structure Clause (Head : Type*) where
  head : Head
  body : List Bool
  deriving DecidableEq

def ruleCount {Head : Type*} : List (Clause Head) → Nat
  | [] => 0
  | c :: rest => (if c.body.isEmpty then 0 else 1) + ruleCount rest

def executeClauses {Head : Type*} : List (Clause Head) → List Head
  | [] => []
  | c :: rest => (if c.body.all id then [c.head] else []) ++ executeClauses rest

def storedFacts {Head : Type*} : List (Clause Head) → List Head
  | [] => []
  | c :: rest => (if c.body.isEmpty then [c.head] else []) ++ storedFacts rest

/-- A zero-rule certificate permits direct ordered fact execution. Duplicate
clauses remain duplicate outputs; predicates with rules need the fallback. -/
theorem execute_facts_only {Head : Type*} (clauses : List (Clause Head))
    (onlyFacts : ruleCount clauses = 0) :
    executeClauses clauses = storedFacts clauses := by
  induction clauses with
  | nil => rfl
  | cons c rest ih =>
      cases c with
      | mk head body =>
          cases body with
          | nil =>
              simp only [ruleCount, List.isEmpty_nil, ite_true, Nat.zero_add] at onlyFacts
              simp [executeClauses, storedFacts, ih onlyFacts]
          | cons first tail =>
              simp [ruleCount] at onlyFacts


namespace Controls

theorem collision_insert :
    fused [some (1, 9), some (2, 8), none] 3 7 =
      (some 7, [some (1, 9), some (2, 8), some (3, 7)]) := by
  decide

theorem existing_identity_preserved :
    fused [some (1, 9), some (2, 8), none] 2 100 =
      (some 8, [some (1, 9), some (2, 8), none]) := by
  decide

theorem collision_miss_saves_scan :
    probeVisits 3 [some (1, 9), some (2, 8), none] <
      twoScanVisits [some (1, 9), some (2, 8), none] 3 := by
  decide

theorem stale_vacancy_overwrites :
    install [some (1, 9)] 2 7 (probe 2 ([none] : Cells Nat Nat)).2 ≠
      twoScans [some (1, 9)] 2 7 := by
  decide

theorem fact_duplicates_retained :
    executeClauses [⟨7, []⟩, ⟨7, []⟩, ⟨3, []⟩] = [7, 7, 3] := by
  decide

theorem executing_rules_is_not_fact_enumeration :
    executeClauses [⟨7, [true]⟩] ≠ storedFacts [⟨7, [true]⟩] := by
  decide

theorem batch_keeps_first_identity :
    fusedBatch ([none, none] : Cells Nat Nat) [(1, 9), (1, 100), (2, 8)] =
      ([9, 9, 8], [some (1, 9), some (2, 8)], true) := by
  decide

theorem batch_exhaustion_keeps_prefix :
    fusedBatch ([none] : Cells Nat Nat) [(1, 9), (2, 8), (1, 100)] =
      ([9], [some (1, 9)], false) := by
  decide

end Controls
end Mettapedia.Machines.IncrementalConformance.InternProbe

namespace Mettapedia.Machines.IncrementalConformance.InternProbe
variable {Key Value : Type*} [DecidableEq Key]

/-- Every successful probe names an actual occurrence in its retained sequence. -/
theorem found_mem (key : Key) (cells : Cells Key Value) (value : Value)
    (found : (probe key cells).1 = some value) : some (key, value) ∈ cells := by
  induction cells with
  | nil => simp [probe] at found
  | cons cell tail ih =>
    cases cell with
    | none => simp [probe] at found
    | some pair =>
      rcases pair with ⟨stored, old⟩
      by_cases same : key = stored
      · simp only [probe, same, ↓reduceIte] at found
        cases Option.some.inj found
        simp [same]
      · have suffix : (probe key tail).1 = some value := by simpa [probe, same] using found
        exact List.mem_cons_of_mem _ (ih suffix)

/-- An initialized prefix with no earlier vacancy reaches its target, unless
an earlier occurrence of the same key has already supplied that same value.
This is an inventory condition, not a premise about the probe result. -/
theorem finds_reachable_member (key : Key) (value : Value) (cells : Cells Key Value)
    (index : Fin cells.length)
    (there : cells[index.val] = some (key, value))
    (occupied : ∀ earlier : Fin cells.length, earlier.val < index.val → cells[earlier.val] ≠ none)
    (coherent : ∀ candidate, some (key, candidate) ∈ cells → candidate = value) :
    (probe key cells).1 = some value := by
  induction cells with
  | nil => exact False.elim (Nat.not_lt_zero _ index.isLt)
  | cons cell tail ih =>
    cases offset : index.val with
    | zero =>
      have cellEq : cell = some (key, value) := by simpa [offset] using there
      simp [cellEq, probe]
    | succ next =>
      have nextRange : next < tail.length := by have := index.isLt; simp only [List.length_cons] at this; omega
      have nonempty : cell ≠ none := occupied ⟨0, by simp⟩ (by change 0 < index.val; omega)
      cases cell with
      | none => exact False.elim (nonempty rfl)
      | some pair =>
        rcases pair with ⟨stored, old⟩
        by_cases same : key = stored
        · have oldEq : old = value := coherent old (by simp [same])
          simp [probe, same, oldEq]
        · have suffixThere : tail[next] = some (key, value) := by simpa [offset] using there
          have suffixOccupied : ∀ earlier : Fin tail.length, earlier.val < next →
              tail[earlier.val] ≠ none := by
            intro earlier before
            exact occupied ⟨earlier.val + 1, by simp⟩
              (by change earlier.val + 1 < index.val; omega)
          have suffixCoherent : ∀ candidate, some (key, candidate) ∈ tail → candidate = value := by
            intro candidate member
            exact coherent candidate (List.mem_cons_of_mem _ member)
          simpa [probe, same] using ih ⟨next, nextRange⟩ suffixThere suffixOccupied suffixCoherent

/-- A finite sequence containing a vacancy cannot exhaust without either
finding the key or retaining that vacancy. -/
theorem stops_if_vacancy (key : Key) (cells : Cells Key Value) (vacancy : none ∈ cells) :
    (probe key cells).1 ≠ none ∨ (probe key cells).2 ≠ none := by
  induction cells with
  | nil => simp at vacancy
  | cons cell tail ih =>
    cases cell with
    | none => simp [probe]
    | some pair =>
      rcases pair with ⟨stored, value⟩
      by_cases same : key = stored
      · simp [probe, same]
      · have rest := ih (by simpa using vacancy)
        simpa [probe, same] using rest

omit [DecidableEq Key] in
/-- A cardinality bound earns an actual vacant cell; it is not a promise
that a future lookup will stop. -/
theorem vacancy_of_count_lt (cells : Cells Key Value)
    (room : cells.countP Option.isSome < cells.length) : none ∈ cells := by
  induction cells with
  | nil => simp at room
  | cons cell tail ih =>
    cases cell with
    | none => simp
    | some pair =>
      have fewer : tail.countP Option.isSome < tail.length := by
        simpa only [List.countP_cons, Option.isSome_some, Bool.true_eq, ↓reduceIte,
          List.length_cons, Nat.add_lt_add_iff_right] using room
      exact List.mem_cons_of_mem _ (ih fewer)

end Mettapedia.Machines.IncrementalConformance.InternProbe
