import Mettapedia.Languages.MeTTa.EquationKernel.Certificate

/-!
# Checking certificates held as atoms of a space

The space form of the checker reads a certificate from facts of a proof
space, `(ek:size name n)`, `(ek:root name r)` and `(ek:row name i row)`, and
records each row's claim in a claim table shared by all invocations. This
module is the model of that implementation.

The table may hold anything when an invocation starts: claims of earlier
invocations under other theories, claims of failed invocations, or entries
written by other code. An invocation therefore
* tags every entry it writes with its own invocation number;
* writes row `i` only after finding no entry for its key, so every entry it
  reads under its key is its own;
* reads a premise only at an index below the current row, and the root only
  below the certificate's size;
* reads each fact and each claim as the unique answer of its query;
* removes the entries of its invocation when it finishes, after success or
  failure.

`spaceCheck_sound`: whatever the table holds, acceptance means that the
certificate read from the facts is accepted by `check`. `spaceCheck_complete`:
from a table without entries of the invocation, a certificate that `check`
accepts is accepted. `spaceCheck_table`: an invocation leaves no entry of its
own number. Together they cover stale names, changed theories, failures and
retries, forward roots and injected entries; the controls at the end replay
each case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)

/-! ## Proof spaces and the claim table -/

/-- The facts of a proof space that the checker queries. Other atoms of the
space match none of its queries. -/
inductive ProofFact where
  | size (name : String) (count : Nat)
  | root (name : String) (index : Nat)
  | row (name : String) (index : Nat) (row : Row)
  deriving DecidableEq, Repr

/-- The answer of a query when it has exactly one. -/
def onlyAnswer {α : Type} : List α → Option α
  | [answer] => some answer
  | _ => none

def readSize (facts : List ProofFact) (name : String) : Option Nat :=
  onlyAnswer (facts.filterMap fun
    | .size key count => if key = name then some count else none
    | _ => none)

def readRoot (facts : List ProofFact) (name : String) : Option Nat :=
  onlyAnswer (facts.filterMap fun
    | .root key index => if key = name then some index else none
    | _ => none)

def readRow (facts : List ProofFact) (name : String) (index : Nat) : Option Row :=
  onlyAnswer (facts.filterMap fun
    | .row key position row => if key = name ∧ position = index then some row else none
    | _ => none)

/-- A claim table entry: invocation number, row index, claim. -/
abbrev TableEntry := Nat × Nat × Claim

def claimsAt (table : List TableEntry) (invocation index : Nat) : List Claim :=
  table.filterMap fun entry =>
    if entry.1 = invocation ∧ entry.2.1 = index then some entry.2.2 else none

/-- A premise is read only below the current row, as the unique entry of its key. -/
def boundedClaim (table : List TableEntry) (invocation current index : Nat) : Option Claim :=
  if index < current then onlyAnswer (claimsAt table invocation index) else none

/-- Check rows `index`, `index + 1`, … while `remaining` rows are left. A row is
written only to an empty key. On refusal the table so far is returned, so that
it can be cleaned. -/
def spaceRun (program : List Atom) (facts : List ProofFact) (name : String) (invocation : Nat) :
    Nat → Nat → List TableEntry → Except (List TableEntry) (List TableEntry)
  | 0, _, table => .ok table
  | remaining + 1, index, table =>
      match readRow facts name index with
      | none => .error table
      | some row =>
          match row.claimBy? program (boundedClaim table invocation index) with
          | none => .error table
          | some claim =>
              if claimsAt table invocation index = [] then
                spaceRun program facts name invocation remaining (index + 1)
                  (table ++ [(invocation, index, claim)])
              else .error table

/-- Remove every entry of an invocation. -/
def cleanup (table : List TableEntry) (invocation : Nat) : List TableEntry :=
  table.filter fun entry => entry.1 ≠ invocation

/-- One invocation: its verdict and the table it leaves. -/
def spaceCheck (program : List Atom) (facts : List ProofFact) (name : String) (claim : Claim)
    (table : List TableEntry) (invocation : Nat) : Bool × List TableEntry :=
  match readSize facts name, readRoot facts name with
  | some size, some root =>
      if root < size then
        match spaceRun program facts name invocation size 0 table with
        | .ok final =>
            (decide (boundedClaim final invocation size root = some claim), cleanup final invocation)
        | .error reached => (false, cleanup reached invocation)
      else (false, table)
  | _, _ => (false, table)

/-! ## The invariant of a run -/

/-- After rows `0 … index-1`, the entries of the invocation are exactly the
claims of the pure checker's table, one per key, after the original entries
of other invocations. -/
structure RunInvariant (table original : List TableEntry) (invocation : Nat) (claims : List Claim) :
    Prop where
  extends_original : ∃ written, table = original ++ written ∧
    ∀ entry ∈ written, entry.1 = invocation
  own : ∀ index, index < claims.length → claimsAt table invocation index = [claims[index]!]
  original_clear : ∀ index, index < claims.length → claimsAt original invocation index = []
  above : ∀ index, claims.length ≤ index → claimsAt table invocation index = claimsAt original invocation index

theorem claimsAt_append (first second : List TableEntry) (invocation index : Nat) :
    claimsAt (first ++ second) invocation index =
      claimsAt first invocation index ++ claimsAt second invocation index := by
  simp [claimsAt, List.filterMap_append]

theorem claimsAt_single (invocation index index' : Nat) (claim : Claim) (other : Nat) :
    claimsAt [(other, index', claim)] invocation index =
      if other = invocation ∧ index' = index then [claim] else [] := by
  simp only [claimsAt, List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp

theorem boundedClaim_of_invariant {table original : List TableEntry} {invocation : Nat}
    {claims : List Claim} (invariant : RunInvariant table original invocation claims) (index : Nat) :
    boundedClaim table invocation claims.length index = claims[index]? := by
  unfold boundedClaim
  split_ifs with below
  · rw [invariant.own index below]
    simp [onlyAnswer, below]
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt below)]

theorem RunInvariant.start (original : List TableEntry) (invocation : Nat) :
    RunInvariant original original invocation [] :=
  ⟨⟨[], by simp, by simp⟩, fun _ bound => absurd bound (Nat.not_lt_zero _), fun _ bound =>
    absurd bound (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem RunInvariant.push {table original : List TableEntry} {invocation : Nat} {claims : List Claim}
    (invariant : RunInvariant table original invocation claims) {claim : Claim}
    (empty : claimsAt table invocation claims.length = []) :
    RunInvariant (table ++ [(invocation, claims.length, claim)]) original invocation (claims ++ [claim]) := by
  obtain ⟨written, extended, tagged⟩ := invariant.extends_original
  refine ⟨⟨written ++ [(invocation, claims.length, claim)], by simp [extended], ?_⟩, ?_, ?_, ?_⟩
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · exact tagged entry old
    · simp at new
      rw [new]
  · intro index bound
    rw [claimsAt_append, claimsAt_single]
    simp only [List.length_append, List.length_singleton] at bound
    rcases Nat.lt_succ_iff_lt_or_eq.mp bound with earlier | here
    · rw [invariant.own index earlier]
      have different : claims.length ≠ index := Nat.ne_of_gt earlier
      simp [different, List.getElem!_eq_getElem?_getD, List.getElem?_append_left earlier]
    · subst here
      rw [empty]
      simp
  · intro index bound
    simp only [List.length_append, List.length_singleton] at bound
    rcases Nat.lt_succ_iff_lt_or_eq.mp bound with earlier | here
    · exact invariant.original_clear index earlier
    · subst here
      rw [← invariant.above claims.length (Nat.le_refl _)]
      exact empty
  · intro index bound
    simp only [List.length_append, List.length_singleton] at bound
    rw [claimsAt_append, claimsAt_single, invariant.above index (by omega)]
    have different : ¬ (claims.length = index) := by omega
    simp [different]

/-! ## Correspondence with the pure checker -/

/-- The rows the facts present for a name, in order, when each is unique. -/
def readRows (facts : List ProofFact) (name : String) : Nat → Nat → Option (List Row)
  | 0, _ => some []
  | remaining + 1, index => do
      let row ← readRow facts name index
      let rest ← readRows facts name remaining (index + 1)
      pure (row :: rest)

/-- A successful run computes exactly the pure checker's table on the rows it
read, whatever the table held before. -/
theorem spaceRun_ok {program : List Atom} {facts : List ProofFact} {name : String} {invocation : Nat}
    {original : List TableEntry} :
    ∀ (remaining : Nat) (claims : List Claim) (table final : List TableEntry),
      RunInvariant table original invocation claims →
      spaceRun program facts name invocation remaining claims.length table = .ok final →
      ∃ rows finalClaims, readRows facts name remaining claims.length = some rows ∧
        checkRows program claims rows = some finalClaims ∧
        RunInvariant final original invocation finalClaims ∧
        finalClaims.length = claims.length + remaining
  | 0, claims, table, final, invariant, run => by
      simp only [spaceRun, Except.ok.injEq] at run
      subst run
      exact ⟨[], claims, rfl, rfl, invariant, by simp⟩
  | remaining + 1, claims, table, final, invariant, run => by
      simp only [spaceRun] at run
      split at run
      · cases run
      · rename_i row found
        split at run
        · cases run
        · rename_i claim computed
          split_ifs at run with empty
          have lookups : ∀ index, boundedClaim table invocation claims.length index = claims[index]? :=
            boundedClaim_of_invariant invariant
          have pure : row.claim? program claims = some claim := by
            rw [Row.claim?_eq_claimBy, ← Row.claimBy?_congr program lookups]
            exact computed
          have next := invariant.push empty (claim := claim)
          have run' : spaceRun program facts name invocation remaining (claims ++ [claim]).length
              (table ++ [(invocation, claims.length, claim)]) = .ok final := by
            simpa using run
          obtain ⟨rows, finalClaims, readOk, checked, finalInvariant, length⟩ :=
            spaceRun_ok remaining (claims ++ [claim]) _ final next run'
          refine ⟨row :: rows, finalClaims, ?_, ?_, finalInvariant, by simp at length ⊢; omega⟩
          · simp only [readRows, found, Option.bind_eq_bind, Option.bind_some]
            simp only [List.length_append, List.length_singleton] at readOk
            rw [readOk]
            rfl
          · simp only [checkRows, pure]
            exact checked

/-- Soundness: whatever the table held, an accepted invocation checked a
certificate, read uniquely from the facts, that the pure checker accepts. -/
theorem spaceCheck_sound {program : List Atom} {facts : List ProofFact} {name : String}
    {claim : Claim} {table : List TableEntry} {invocation : Nat}
    (accepted : (spaceCheck program facts name claim table invocation).1 = true) :
    ∃ size root rows, readSize facts name = some size ∧ readRoot facts name = some root ∧
      readRows facts name size 0 = some rows ∧ check program ⟨rows, root⟩ claim = true := by
  unfold spaceCheck at accepted
  split at accepted
  · rename_i size root sized rooted
    split_ifs at accepted with bounded
    split at accepted
    · rename_i final run
      obtain ⟨rows, finalClaims, readOk, checked, invariant, length⟩ :=
        spaceRun_ok size [] table final (RunInvariant.start table invocation) run
      refine ⟨size, root, rows, sized, rooted, readOk, ?_⟩
      have rootClaim : boundedClaim final invocation size root = some claim := of_decide_eq_true accepted
      have lookups := boundedClaim_of_invariant invariant root
      simp only [List.length_nil, Nat.zero_add] at length
      rw [length] at lookups
      rw [lookups] at rootClaim
      rw [check_eq_checkReference]
      unfold checkReference
      rw [checked]
      exact decide_eq_true rootClaim
    · cases accepted
  · cases accepted

/-- The facts present a certificate under a name: one size, one root, one
row per index below the size. -/
def Presents (facts : List ProofFact) (name : String) (certificate : Certificate) : Prop :=
  readSize facts name = some certificate.rows.length ∧ readRoot facts name = some certificate.root ∧
    readRows facts name certificate.rows.length 0 = some certificate.rows

theorem spaceRun_complete {program : List Atom} {facts : List ProofFact} {name : String}
    {invocation : Nat} {original : List TableEntry} :
    ∀ (rows : List Row) (claims finalClaims : List Claim) (table : List TableEntry),
      RunInvariant table original invocation claims →
      (∀ index, claims.length ≤ index → claimsAt original invocation index = []) →
      readRows facts name rows.length claims.length = some rows →
      checkRows program claims rows = some finalClaims →
      ∃ final, spaceRun program facts name invocation rows.length claims.length table = .ok final ∧
        RunInvariant final original invocation finalClaims
  | [], claims, finalClaims, table, invariant, _, _, checked => by
      simp only [checkRows, Option.some.injEq] at checked
      subst checked
      exact ⟨table, rfl, invariant⟩
  | row :: rows, claims, finalClaims, table, invariant, clear, readOk, checked => by
      simp only [readRows, Option.bind_eq_bind, List.length_cons] at readOk
      obtain ⟨row', found, rest⟩ := Option.bind_eq_some_iff.mp readOk
      obtain ⟨rows', restOk, same⟩ := Option.bind_eq_some_iff.mp rest
      simp only [Option.pure_def, Option.some.injEq, List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      simp only [checkRows] at checked
      split at checked
      · rename_i claim pure
        have lookups : ∀ index, boundedClaim table invocation claims.length index = claims[index]? :=
          boundedClaim_of_invariant invariant
        have computed : row'.claimBy? program (boundedClaim table invocation claims.length) = some claim := by
          rw [Row.claimBy?_congr program lookups, ← Row.claim?_eq_claimBy]
          exact pure
        have empty : claimsAt table invocation claims.length = [] := by
          rw [invariant.above claims.length (Nat.le_refl _)]
          exact clear claims.length (Nat.le_refl _)
        have next := invariant.push empty (claim := claim)
        have restOk' : readRows facts name rows'.length (claims ++ [claim]).length = some rows' := by
          simpa using restOk
        obtain ⟨final, run, finalInvariant⟩ := spaceRun_complete rows' (claims ++ [claim]) finalClaims _ next
          (fun index bound => clear index (by simp at bound; omega)) restOk' checked
        refine ⟨final, ?_, finalInvariant⟩
        simp only [List.length_cons, spaceRun, found, computed, empty, if_true]
        simpa using run
      · cases checked

/-- Completeness: from a table with no entry of the invocation, a presented
certificate that the pure checker accepts is accepted. -/
theorem spaceCheck_complete {program : List Atom} {facts : List ProofFact} {name : String}
    {certificate : Certificate} {claim : Claim} {table : List TableEntry} {invocation : Nat}
    (presents : Presents facts name certificate)
    (fresh : ∀ entry ∈ table, entry.1 ≠ invocation)
    (accepted : check program certificate claim = true) :
    (spaceCheck program facts name claim table invocation).1 = true := by
  obtain ⟨sized, rooted, readOk⟩ := presents
  rw [check_eq_checkReference] at accepted
  unfold checkReference at accepted
  split at accepted
  · rename_i finalClaims checked
    have rootFound : finalClaims[certificate.root]? = some claim := of_decide_eq_true accepted
    have valid := (checkRows_exact _ _ _ _).mp checked
    obtain ⟨claims, same, length⟩ := valid.extends
    simp only [List.nil_append] at same
    subst same
    have bounded : certificate.root < certificate.rows.length := by
      rw [← length]
      exact (List.getElem?_eq_some_iff.mp rootFound).1
    have clear : ∀ index, ([] : List Claim).length ≤ index → claimsAt table invocation index = [] := by
      intro index _
      simp only [claimsAt, List.filterMap_eq_nil_iff]
      intro entry member
      simp [fresh entry member]
    obtain ⟨final, run, invariant⟩ := spaceRun_complete certificate.rows [] finalClaims table
      (RunInvariant.start table invocation) clear readOk checked
    unfold spaceCheck
    simp only [sized, rooted, if_pos bounded]
    simp only [List.length_nil] at run
    rw [run]
    simp only
    apply decide_eq_true
    have lookup := boundedClaim_of_invariant invariant certificate.root
    rw [length] at lookup
    rw [lookup]
    exact rootFound
  · cases accepted

theorem cleanup_clears (table : List TableEntry) (invocation : Nat) :
    ∀ entry ∈ cleanup table invocation, entry.1 ≠ invocation := by
  intro entry member
  simp only [cleanup, List.mem_filter, decide_eq_true_eq] at member
  exact member.2

/-- An invocation leaves no entry of its own number, after success or failure. -/
theorem spaceCheck_table (program : List Atom) (facts : List ProofFact) (name : String) (claim : Claim)
    (table : List TableEntry) (invocation : Nat) (fresh : ∀ entry ∈ table, entry.1 ≠ invocation) :
    ∀ entry ∈ (spaceCheck program facts name claim table invocation).2, entry.1 ≠ invocation := by
  unfold spaceCheck
  split
  · split_ifs
    · split
      · exact cleanup_clears _ _
      · exact cleanup_clears _ _
    · exact fresh
  · exact fresh

/-- A run, refused or not, only appends entries of its own invocation. -/
theorem spaceRun_extends {program : List Atom} {facts : List ProofFact} {name : String}
    {invocation : Nat} :
    ∀ (remaining index : Nat) (table : List TableEntry),
      ∃ written, (∀ entry ∈ written, entry.1 = invocation) ∧
        (spaceRun program facts name invocation remaining index table = .ok (table ++ written) ∨
          spaceRun program facts name invocation remaining index table = .error (table ++ written))
  | 0, _, table => ⟨[], by simp, .inl (by simp [spaceRun])⟩
  | remaining + 1, index, table => by
      simp only [spaceRun]
      split
      · exact ⟨[], by simp, .inr (by simp)⟩
      · split
        · exact ⟨[], by simp, .inr (by simp)⟩
        · rename_i row _ claim _
          split_ifs
          · obtain ⟨written, tagged, outcome⟩ := spaceRun_extends remaining (index + 1)
              (table ++ [(invocation, index, claim)])
            refine ⟨(invocation, index, claim) :: written, ?_, ?_⟩
            · intro entry member
              rcases List.mem_cons.mp member with here | there
              · rw [here]
              · exact tagged entry there
            · simpa using outcome
          · exact ⟨[], by simp, .inr (by simp)⟩

/-- An invocation from a table without entries of its number leaves exactly
the table it found: a failed invocation can be retried, and a later
invocation under another theory sees no claim of this one. -/
theorem spaceCheck_table_restored (program : List Atom) (facts : List ProofFact) (name : String)
    (claim : Claim) (table : List TableEntry) (invocation : Nat)
    (fresh : ∀ entry ∈ table, entry.1 ≠ invocation) :
    (spaceCheck program facts name claim table invocation).2 = table := by
  have restore : ∀ written : List TableEntry, (∀ entry ∈ written, entry.1 = invocation) →
      cleanup (table ++ written) invocation = table := by
    intro written tagged
    simp only [cleanup, List.filter_append]
    rw [List.filter_eq_self.mpr (fun entry member => by simpa using fresh entry member),
      List.filter_eq_nil_iff.mpr (fun entry member => by simpa using tagged entry member)]
    simp
  unfold spaceCheck
  split
  · rename_i size root _ _
    split_ifs
    · obtain ⟨written, tagged, outcome⟩ :=
        spaceRun_extends (program := program) (facts := facts) (name := name) size 0 table
      rcases outcome with ok | refused
      · rw [ok]
        exact restore written tagged
      · rw [refused]
        exact restore written tagged
    · rfl
  · rfl

/-- A retry after any number of earlier invocations, under any theories,
returns the pure checker's verdict on the presented certificate. -/
theorem spaceCheck_retry {program : List Atom} {facts : List ProofFact} {name : String}
    {certificate : Certificate} {claim : Claim} {table : List TableEntry} {invocation : Nat}
    (presents : Presents facts name certificate) (fresh : ∀ entry ∈ table, entry.1 ≠ invocation) :
    (spaceCheck program facts name claim table invocation).1 = check program certificate claim := by
  cases accepted : check program certificate claim with
  | true => exact spaceCheck_complete presents fresh accepted
  | false =>
      cases verdict : (spaceCheck program facts name claim table invocation).1 with
      | false => rfl
      | true =>
          obtain ⟨size, root, rows, sized, rooted, readOk, checked⟩ := spaceCheck_sound verdict
          obtain ⟨sized', rooted', readOk'⟩ := presents
          rw [sized'] at sized
          cases sized
          rw [rooted'] at rooted
          cases rooted
          rw [readOk'] at readOk
          cases readOk
          rw [accepted] at checked
          cases checked

/-! ## The reviewed cases -/

namespace SpaceScenarios

def atomA : Atom := .symbol "A"
def atomB : Atom := .symbol "B"
def equationAB : Atom := Atom.equality atomA atomB

/-- The facts of a certificate under a name. -/
def factsOf (name : String) (certificate : Certificate) : List ProofFact :=
  .size name certificate.rows.length :: .root name certificate.root ::
    certificate.rows.zipIdx.map fun (row, index) => .row name index row

def certificateAB : Certificate := ⟨[.refl atomA, .step 0 ⟨equationAB, 0⟩ [] []], 1⟩

/-- A first invocation accepts and leaves the table empty. -/
example : spaceCheck [equationAB] (factsOf "same-id" certificateAB) "same-id" (atomA, atomB) [] 0 =
    (true, []) := by decide

/-- The reviewed false acceptance: another space, the empty theory, the same
name, size 0 and root 1. Refused, also with the first invocation's claims
left in the table under either number. -/
example : (spaceCheck [] [.size "same-id" 0, .root "same-id" 1] "same-id" (atomA, atomB) [] 1).1 = false := by
  decide
example : (spaceCheck [] [.size "same-id" 0, .root "same-id" 1] "same-id" (atomA, atomB)
    [(0, 0, (atomA, atomA)), (0, 1, (atomA, atomB))] 1).1 = false := by decide
example : (spaceCheck [] [.size "same-id" 0, .root "same-id" 1] "same-id" (atomA, atomB)
    [(0, 0, (atomA, atomA)), (0, 1, (atomA, atomB))] 0).1 = false := by decide

/-- Entries injected under the invocation's own number cause refusal. -/
example : (spaceCheck [] (factsOf "n" ⟨[.refl atomA], 0⟩) "n" (atomA, atomA) [(1, 0, (atomA, atomB))] 1).1 =
    false := by decide
example : (spaceCheck [] (factsOf "n" ⟨[.refl atomA, .trans 0 0], 1⟩) "n" (atomA, atomB)
    [(1, 1, (atomA, atomB))] 1).1 = false := by decide

/-- A root at or past the size, and a premise at or past its row, refuse,
even when an entry for that index exists. -/
example : (spaceCheck [equationAB] (factsOf "n" ⟨[.refl atomA], 1⟩) "n" (atomA, atomA) [] 0).1 = false := by
  decide
example : (spaceCheck [equationAB] (factsOf "n" ⟨[.step 1 ⟨equationAB, 0⟩ [] [], .refl atomA], 0⟩) "n"
    (atomA, atomB) [(0, 1, (atomA, atomA))] 0).1 = false := by decide

/-- Two certificates under one name refuse. -/
example : (spaceCheck [equationAB] (factsOf "n" certificateAB ++ factsOf "n" certificateAB) "n"
    (atomA, atomB) [] 0).1 = false := by decide

/-- A refused invocation leaves the table as it was, and a retry with a
corrected certificate is accepted. -/
example : spaceCheck [equationAB] (factsOf "n" ⟨[.refl atomA, .step 0 ⟨equationAB, 1⟩ [] []], 1⟩) "n"
    (atomA, atomB) [] 0 = (false, []) := by decide
example : (spaceCheck [equationAB] (factsOf "m" certificateAB) "m" (atomA, atomB) [] 1).1 = true := by decide

end SpaceScenarios

end Mettapedia.Languages.MeTTa.EquationKernel
