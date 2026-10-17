import Mettapedia.GSLT.Contracts.RelyGuaranteeClaims
import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Logic.Relation

/-!
# Transaction dependencies as rely–guarantee claims

A speculative computation reads a snapshot of a store of atom occurrences and
records what its result depends on.  At commit the dependencies are validated
against the current store.  This module reads such a dependency set as a
rely–guarantee claim (`claim`):

* its assertion is the set of stores on which every dependency holds;
* its rely is every change that keeps the dependencies valid;
* its guarantee is the transaction's own writes.

Pessimistic concurrency asks the environment's guarantee to lie within this
rely, which is coexistence in the separation algebra of
`Mettapedia.GSLT.Contracts.RelyGuaranteeClaims`.  Optimistic concurrency does
not ask it in advance; it checks the reified claim at commit.  Coexistence
implies that validation succeeds (`valid_of_coexist`); validation can succeed
without coexistence (`optimistic_admits_more`).  So a transaction is not a new
kind of structure: it is a rely checked late.

## Dependencies

`Dep` has three forms: an occurrence holds an atom (`present`), no occurrence
matches a query (`absent`), and the matching occurrences are exactly a given
ordered list (`complete`).  Positive returned atoms alone are not enough.

* Inserting a matching atom invalidates an absence (`absent_insert_iff`) and a
  complete result (`complete_insert_match`), though every atom returned before
  is still present.
* A reader of an absence and an inserter of a matching atom write disjoint
  parts of the store, yet do not coexist (`coexist_inserter_absent_iff`).
* Validating only the returned atoms does not determine a query result
  (`returned_only_not_determines`); a complete-result dependency does
  (`complete_determines_matches`).
* Occurrence identity matters: after one party takes an occurrence, another
  party's dependency on that occurrence fails although a second occurrence of
  the same atom remains (`printed_value_does_not_rescue`).
* A transaction's own write does not invalidate its earlier read, and neither
  does an unrelated insertion; comparing the whole store with the snapshot
  would refuse it (`own_write_retained`).

Validation is sound for a result exactly when the dependency set determines
that result on the stores it admits (`Determines`, `validated_result`); proving
that a dependency language determines the results of every query it is used
for is the substantive obligation of a transaction implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Contracts.RGClaim
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {Atom : Type u}

/-- A store of atom occurrences: occurrence identifiers with their atoms. -/
abbrev Store (Atom : Type u) := List (ℕ × Atom)

/-- **A dependency** recorded by a speculative read. -/
inductive Dep (Atom : Type u) where
  /-- The occurrence holds the atom. -/
  | present (occurrence : ℕ) (atom : Atom)
  /-- No occurrence matches the query. -/
  | absent (query : Atom → Bool)
  /-- The occurrences matching the query are exactly these, in store order. -/
  | complete (query : Atom → Bool) (occurrences : List ℕ)

/-- The occurrences of a store matching a query, in store order. -/
def matching (q : Atom → Bool) (s : Store Atom) : List ℕ :=
  (s.filter fun entry => q entry.2).map Prod.fst

/-- When a dependency holds of a store. -/
def Dep.Holds : Dep Atom → Store Atom → Prop
  | .present occurrence atom, s => (occurrence, atom) ∈ s
  | .absent q, s => ∀ entry ∈ s, q entry.2 = false
  | .complete q occurrences, s => matching q s = occurrences

/-- Every dependency of the set holds. -/
def Valid (D : List (Dep Atom)) (s : Store Atom) : Prop := ∀ d ∈ D, d.Holds s

instance Dep.decidableHolds [DecidableEq Atom] (d : Dep Atom) (s : Store Atom) :
    Decidable (d.Holds s) := by
  cases d with
  | present occurrence atom => exact inferInstanceAs (Decidable ((occurrence, atom) ∈ s))
  | absent q => exact inferInstanceAs (Decidable (∀ entry ∈ s, q entry.2 = false))
  | complete q occurrences => exact inferInstanceAs (Decidable (matching q s = occurrences))

instance decidableValid [DecidableEq Atom] (D : List (Dep Atom)) (s : Store Atom) :
    Decidable (Valid D s) :=
  inferInstanceAs (Decidable (∀ d ∈ D, d.Holds s))

/-- **The dependency claim**: valid stores, the rely that keeps them valid, and
the transaction's own writes as its guarantee. -/
def claim (D : List (Dep Atom)) (own : Store Atom → Store Atom → Prop) : RGClaim (Store Atom) :=
  { assertion := {s | Valid D s}
    rely := fun s s' => Valid D s → Valid D s'
    guarantee := own
    stable := fun _ _ holds relies => relies holds }

/-- Insert a new occurrence at the end of the store. -/
def insertStep (occurrence : ℕ) (atom : Atom) (s s' : Store Atom) : Prop :=
  s' = s ++ [(occurrence, atom)]

/-- A party whose guarantee is inserting occurrences of one atom; it relies on
nothing. -/
def inserter (atom : Atom) : RGClaim (Store Atom) :=
  { assertion := Set.univ
    rely := fun _ _ => True
    guarantee := fun s s' => ∃ occurrence, insertStep occurrence atom s s'
    stable := fun _ _ _ _ => trivial }

/-! ## Insertion against the three dependency forms -/

theorem present_insert {occurrence occurrence' : ℕ} {atom atom' : Atom} {s : Store Atom}
    (holds : (Dep.present occurrence atom).Holds s) :
    (Dep.present occurrence atom).Holds (s ++ [(occurrence', atom')]) :=
  List.mem_append_left _ holds

/-- **Insertion invalidates an absence exactly when the inserted atom
matches.** -/
theorem absent_insert_iff {q : Atom → Bool} {s : Store Atom} (occurrence : ℕ) (atom : Atom)
    (holds : (Dep.absent q).Holds s) :
    (Dep.absent q).Holds (s ++ [(occurrence, atom)]) ↔ q atom = false := by
  constructor
  · intro after
    exact after (occurrence, atom) (by simp)
  · intro unmatched entry member
    rcases List.mem_append.mp member with old | new
    · exact holds entry old
    · rw [List.mem_singleton.mp new]
      exact unmatched

/-- **Inserting a match invalidates a complete result**, although every
occurrence listed in it is still present. -/
theorem complete_insert_match {q : Atom → Bool} {occurrences : List ℕ} {s : Store Atom}
    (occurrence : ℕ) {atom : Atom} (hit : q atom = true)
    (holds : (Dep.complete q occurrences).Holds s) :
    ¬ (Dep.complete q occurrences).Holds (s ++ [(occurrence, atom)]) := by
  intro after
  change matching q (s ++ [(occurrence, atom)]) = occurrences at after
  change matching q s = occurrences at holds
  have grown : matching q (s ++ [(occurrence, atom)]) = matching q s ++ [occurrence] := by
    simp [matching, List.filter_append, hit]
  rw [grown, holds] at after
  have lengths := congrArg List.length after
  simp at lengths

/-- **Disjoint writes do not make independence**: a reader of an absence, which
writes nothing, coexists with an inserter exactly when the inserted atom does
not match. -/
theorem coexist_inserter_absent_iff (q : Atom → Bool) (atom : Atom) :
    inserter atom ## claim [.absent q] (fun s s' => s' = s) ↔ q atom = false := by
  constructor
  · rintro ⟨withinRely, -⟩
    have empty : Valid [.absent q] ([] : Store Atom) := by
      intro d member
      simp only [List.mem_singleton] at member
      subst member
      intro entry impossible
      cases impossible
    have after := withinRely [] [(0, atom)] ⟨0, rfl⟩ empty (.absent q) (by simp)
    exact after (0, atom) (by simp)
  · intro unmatched
    refine ⟨?_, fun _ _ _ => trivial⟩
    rintro s s' ⟨occurrence, rfl⟩ valid d member
    simp only [List.mem_singleton] at member
    subst member
    exact (absent_insert_iff occurrence atom (valid _ (by simp))).mpr unmatched

/-! ## Optimistic validation is a rely checked late -/

/-- **Coexistence implies validation**: if every environment step lies within
a guarantee that coexists with the claim, validation succeeds at commit. -/
theorem valid_of_coexist {D : List (Dep Atom)} {own : Store Atom → Store Atom → Prop}
    {environment : RGClaim (Store Atom)} (coexist : environment ## claim D own)
    {snapshot current : Store Atom}
    (run : Relation.ReflTransGen environment.guarantee snapshot current)
    (valid : Valid D snapshot) : Valid D current := by
  induction run with
  | refl => exact valid
  | tail _ step ih => exact coexist.1 _ _ step ih

/-- A party allowed to insert any atom. -/
def anyInserter : RGClaim (Store Atom) :=
  { assertion := Set.univ
    rely := fun _ _ => True
    guarantee := fun s s' => ∃ occurrence atom, insertStep occurrence atom s s'
    stable := fun _ _ _ _ => trivial }

/-- **Optimistic validation admits more schedules**: a party allowed to insert
any atom does not coexist with an absence, yet a run in which it inserts a
non-matching atom validates. -/
theorem optimistic_admits_more {q : Atom → Bool} {matched unmatched : Atom}
    (isMatch : q matched = true) (noMatch : q unmatched = false) :
    ¬ (anyInserter ## claim [.absent q] (fun s s' => s' = s)) ∧
      Relation.ReflTransGen anyInserter.guarantee ([] : Store Atom) [(0, unmatched)] ∧
      Valid [.absent q] ([(0, unmatched)] : Store Atom) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨withinRely, -⟩
    have empty : Valid [.absent q] ([] : Store Atom) := by
      intro d member
      simp only [List.mem_singleton] at member
      subst member
      intro entry impossible
      cases impossible
    have after := withinRely [] [(0, matched)] ⟨0, matched, rfl⟩ empty (.absent q) (by simp)
    have wrong := after (0, matched) (by simp)
    rw [isMatch] at wrong
    cases wrong
  · exact Relation.ReflTransGen.single ⟨0, unmatched, rfl⟩
  · intro d member
    simp only [List.mem_singleton] at member
    subst member
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    exact noMatch

/-! ## Which dependencies determine a result -/

/-- `D` **determines** `result` at the snapshot: every store admitted by `D`
gives the snapshot's result. -/
def Determines {R : Type v} (D : List (Dep Atom)) (result : Store Atom → R)
    (snapshot : Store Atom) : Prop :=
  ∀ s, Valid D s → result s = result snapshot

/-- **Validated publication**: when the dependencies determine the result and
validation succeeds at commit, the speculative result is the result at the
commit point. -/
theorem validated_result {R : Type v} {D : List (Dep Atom)} {result : Store Atom → R}
    {snapshot current : Store Atom} (determines : Determines D result snapshot)
    (valid : Valid D current) : result current = result snapshot :=
  determines current valid

/-- A complete-result dependency determines the matching occurrences. -/
theorem complete_determines_matches (q : Atom → Bool) (snapshot : Store Atom) :
    Determines [.complete q (matching q snapshot)] (matching q) snapshot := by
  intro s valid
  exact valid (.complete q (matching q snapshot)) (List.mem_singleton_self _)

/-- The naive dependencies of a result: only the returned occurrences are
checked to be present. -/
def returnedDeps (s : Store Atom) (q : Atom → Bool) : List (Dep Atom) :=
  (s.filter fun entry => q entry.2).map fun entry => .present entry.1 entry.2

/-! ## Complete occurrence queries realize adaptive read certificates

An identifier-only result observes less than an ordered list of occurrence
payloads. Complete identifiers together with the corresponding presence claims
determine the full list when an identifier has one payload in the current
store. This is an explicit store integrity condition, not authority inferred
from a printed atom or a hash. The resulting bridge reuses the existing pure
adaptive query interpreter, including its bind and performed-prefix laws.
-/

/-- Full matching rows, retaining occurrence identity, payload and order. -/
def matchingRows (q : Atom → Bool) (s : Store Atom) : Store Atom :=
  s.filter fun entry => q entry.2

@[simp] theorem matchingRows_ids (q : Atom → Bool) (s : Store Atom) :
    (matchingRows q s).map Prod.fst = matching q s := rfl

/-- One identifier cannot denote two different payloads in a store. Repeated
equal rows are still observed with their actual multiplicity. -/
def PayloadConsistent (s : Store Atom) : Prop :=
  ∀ first ∈ s, ∀ second ∈ s, first.1 = second.1 → first.2 = second.2

/-- Capture both the complete ordered identifiers and every returned payload. -/
def rowDependencies (q : Atom → Bool) (rows : Store Atom) : List (Dep Atom) :=
  .complete q (rows.map Prod.fst) :: rows.map fun entry => .present entry.1 entry.2

theorem valid_rowDependencies_iff (q : Atom → Bool) (rows current : Store Atom) :
    Valid (rowDependencies q rows) current ↔
      matching q current = rows.map Prod.fst ∧ ∀ entry ∈ rows, entry ∈ current := by
  constructor
  · intro valid
    refine ⟨valid _ (List.mem_cons_self), ?_⟩
    intro entry member
    exact valid (.present entry.1 entry.2)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  · rintro ⟨complete, present⟩ dependency member
    rcases List.mem_cons.mp member with rfl | member
    · exact complete
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
      exact present entry entryMember

private theorem rows_eq_of_ids_and_members (current : Store Atom)
    (consistent : PayloadConsistent current) (first second : Store Atom)
    (ids : first.map Prod.fst = second.map Prod.fst)
    (firstMembers : ∀ entry ∈ first, entry ∈ current)
    (secondMembers : ∀ entry ∈ second, entry ∈ current) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => simp at ids
  | cons head tail ih =>
      cases second with
      | nil => simp at ids
      | cons head' tail' =>
          simp only [List.map_cons, List.cons.injEq] at ids
          have same : head = head' := Prod.ext ids.1
            (consistent head (firstMembers head (by simp))
              head' (secondMembers head' (by simp)) ids.1)
          subst head'
          exact congrArg (head :: ·) (ih tail' ids.2
            (fun entry member => firstMembers entry (by simp [member]))
            (fun entry member => secondMembers entry (by simp [member])))

theorem valid_rowDependencies_payloads (q : Atom → Bool) (rows current : Store Atom)
    (consistent : PayloadConsistent current)
    (valid : Valid (rowDependencies q rows) current) : matchingRows q current = rows := by
  obtain ⟨complete, present⟩ := (valid_rowDependencies_iff q rows current).mp valid
  exact rows_eq_of_ids_and_members current consistent (matchingRows q current) rows
    complete (fun _ member => List.mem_of_mem_filter member) present

/-- Actual matching rows satisfy their recorded dependency claims. -/
theorem captured_rows_valid (q : Atom → Bool) (current : Store Atom) :
    Valid (rowDependencies q (matchingRows q current)) current := by
  apply (valid_rowDependencies_iff q _ current).mpr
  exact ⟨rfl, fun _ member => List.mem_of_mem_filter member⟩

theorem valid_rowDependencies_iff_matchingRows (q : Atom → Bool) (rows current : Store Atom)
    (consistent : PayloadConsistent current) :
    Valid (rowDependencies q rows) current ↔ matchingRows q current = rows := by
  constructor
  · exact valid_rowDependencies_payloads q rows current consistent
  · intro equal
    rw [← equal]
    exact captured_rows_valid q current

/-- Compile the adaptive interpreter's actual ordered read certificate into
the existing transaction dependency language. -/
def readDependencies
    (reads : Mettapedia.Machines.ReadOnlyQuery.Reads (Atom → Bool) (Store Atom)) :
    List (Dep Atom) := reads.flatMap fun read => rowDependencies read.1 read.2

theorem valid_readDependencies_of_agrees (current : Store Atom)
    (reads : Mettapedia.Machines.ReadOnlyQuery.Reads (Atom → Bool) (Store Atom))
    (agrees : Mettapedia.Machines.ReadOnlyQuery.Agrees
      (fun q => matchingRows q current) reads) : Valid (readDependencies reads) current := by
  intro dependency member
  obtain ⟨read, belongs, contains⟩ := List.mem_flatMap.mp member
  have equal := agrees read belongs
  have valid : Valid (rowDependencies read.1 read.2) current := by
    rw [← equal]
    exact captured_rows_valid read.1 current
  exact valid dependency contains

theorem valid_readDependencies_iff (current : Store Atom)
    (consistent : PayloadConsistent current)
    (reads : Mettapedia.Machines.ReadOnlyQuery.Reads (Atom → Bool) (Store Atom)) :
    Valid (readDependencies reads) current ↔
      Mettapedia.Machines.ReadOnlyQuery.Agrees (fun q => matchingRows q current) reads := by
  constructor
  · intro valid read member
    apply (valid_rowDependencies_iff_matchingRows read.1 read.2 current consistent).mp
    intro dependency belongs
    exact valid dependency (List.mem_flatMap.mpr ⟨read, member, belongs⟩)
  · exact valid_readDependencies_of_agrees current reads

/-- A certificate compiled from an actual run is valid in its captured store.
This uses the interpreter's read semantics, not a guessed dependency list. -/
theorem captured_program_valid {Answer : Type v} (snapshot : Store Atom)
    (program : Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Answer) :
    Valid (readDependencies
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot) program).reads)
      snapshot :=
  valid_readDependencies_of_agrees snapshot _
    (Mettapedia.Machines.ReadOnlyQuery.run_agrees _ program)

theorem readDependencies_append
    (first second : Mettapedia.Machines.ReadOnlyQuery.Reads (Atom → Bool) (Store Atom)) :
    readDependencies (first ++ second) = readDependencies first ++ readDependencies second := by
  exact List.flatMap_append

/-- Transaction validation now supplies the pure-query agreement premise from
an independently defined occurrence store and its concrete dependencies. -/
theorem validated_adaptive_query {Answer : Type v} (snapshot current : Store Atom)
    (program : Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Answer)
    (consistent : PayloadConsistent current)
    (valid : Valid (readDependencies
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot) program).reads)
      current) :
    Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current) program =
      Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot) program :=
  Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees _ _ program
    ((valid_readDependencies_iff current consistent _).mp valid)

/-- The same concrete query certificate serves both disciplines: coexistence
with an actual environment run establishes the commit validation premise,
which preserves the whole adaptive observation. -/
theorem coexisting_environment_preserves_adaptive_query {Answer : Type v}
    (snapshot current : Store Atom)
    (program : Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Answer)
    (own : Store Atom → Store Atom → Prop) (environment : RGClaim (Store Atom))
    (coexist : environment ## claim (readDependencies
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot) program).reads) own)
    (changes : Relation.ReflTransGen environment.guarantee snapshot current)
    (consistent : PayloadConsistent current) :
    Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current) program =
      Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot) program :=
  validated_adaptive_query snapshot current program consistent
    (valid_of_coexist coexist changes (captured_program_valid snapshot program))

/-- The answer-selected continuation contributes its own dependencies in the
same order as the existing sequential query semantics. -/
theorem readDependencies_bind {Answer Other : Type v} (snapshot : Store Atom)
    (program : Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Answer)
    (next : Answer → Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Other) :
    readDependencies (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q snapshot)
      (Mettapedia.Machines.ReadOnlyQuery.bind program next)).reads =
      readDependencies (Mettapedia.Machines.ReadOnlyQuery.run
        (fun q => matchingRows q snapshot) program).reads ++
      readDependencies (Mettapedia.Machines.ReadOnlyQuery.run
        (fun q => matchingRows q snapshot)
        (next (Mettapedia.Machines.ReadOnlyQuery.run
          (fun q => matchingRows q snapshot) program).answer)).reads := by
  rw [Mettapedia.Machines.ReadOnlyQuery.run_bind]
  exact readDependencies_append _ _

/-- Validating concrete dependencies of performed reads licenses the existing
fresh-resumption law. Snapshot continuation remains a different contract. -/
theorem validated_adaptive_resume {Answer : Type v} (snapshot current : Store Atom)
    (steps : Nat)
    (program : Mettapedia.Machines.ReadOnlyQuery.Program (Atom → Bool) (Store Atom) Answer)
    (consistent : PayloadConsistent current)
    (valid : Valid (readDependencies
      (Mettapedia.Machines.ReadOnlyQuery.pausePrefix
        (fun q => matchingRows q snapshot) steps program).1) current) :
    (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current)
      (Mettapedia.Machines.ReadOnlyQuery.pausePrefix
        (fun q => matchingRows q snapshot) steps program).2).answer =
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current) program).answer ∧
    (Mettapedia.Machines.ReadOnlyQuery.pausePrefix
      (fun q => matchingRows q snapshot) steps program).1 ++
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current)
        (Mettapedia.Machines.ReadOnlyQuery.pausePrefix
          (fun q => matchingRows q snapshot) steps program).2).reads =
      (Mettapedia.Machines.ReadOnlyQuery.run (fun q => matchingRows q current) program).reads :=
  Mettapedia.Machines.ReadOnlyQuery.resumed_eq_fresh_of_prefix_agrees _ _ steps program
    ((valid_readDependencies_iff current consistent _).mp valid)

/-! ## Controls -/

/-- Atoms for the controls. -/
inductive Item where
  | target | other | written | unrelated
  deriving DecidableEq, Repr

/-- The query: is this the target atom? -/
def isTarget : Item → Bool
  | .target => true
  | _ => false

/-- **Validating only the returned atoms does not determine the result**: an
insertion of a further match leaves every returned atom present and changes the
matching occurrences. -/
theorem returned_only_not_determines :
    let snapshot : Store Item := [(0, .target), (1, .other)]
    let current : Store Item := snapshot ++ [(2, .target)]
    Valid (returnedDeps snapshot isTarget) current ∧
      matching isTarget current ≠ matching isTarget snapshot ∧
      ¬ Valid [.complete isTarget (matching isTarget snapshot)] current := by
  decide

/-- **The printed value does not rescue a taken occurrence**: after occurrence
`0` is taken, a dependency on it fails, although occurrence `1` still holds the
same atom. -/
theorem printed_value_does_not_rescue :
    let before : Store Item := [(0, .target), (1, .target)]
    let after : Store Item := before.erase (0, .target)
    (Dep.present 0 Item.target).Holds before ∧ ¬ (Dep.present 0 Item.target).Holds after ∧
      ∃ occurrence, (occurrence, Item.target) ∈ after := by
  exact ⟨by decide, by decide, 1, by decide⟩

/-- **Own writes are retained**: a transaction that read occurrence `0`, wrote
occurrence `2`, and saw an unrelated insertion of occurrence `3` still
validates; comparing the whole store with the snapshot would refuse it. -/
theorem own_write_retained :
    let snapshot : Store Item := [(0, .other)]
    let current : Store Item := snapshot ++ [(2, .written)] ++ [(3, .unrelated)]
    Valid [.present 0 Item.other] current ∧ current ≠ snapshot := by
  decide

/-- **An absence is invalidated by an insertion that changes no returned
atom**: the query returned nothing, so the naive dependency set is empty. -/
theorem absence_invalidated :
    let snapshot : Store Item := [(0, .other)]
    let current : Store Item := snapshot ++ [(1, .target)]
    Valid (returnedDeps snapshot isTarget) current ∧
      Valid [.absent isTarget] snapshot ∧ ¬ Valid [.absent isTarget] current := by
  decide

namespace AdaptiveControls

open Mettapedia.Machines.ReadOnlyQuery

/-- The second query is selected by the first answer. -/
def parentThenChild : Program (Item → Bool) (Store Item) (Store Item) :=
  .read isTarget fun parents =>
    if parents.isEmpty then .pure []
    else .read (fun item => item == .other) .pure

/-- Equal printed atoms remain two occurrence rows. An unrelated insertion
preserves the actual parent-selected query path and its complete certificate. -/
theorem unrelated_insert_preserves_adaptive_query :
    let snapshot : Store Item := [(0, .target), (1, .target), (2, .other)]
    let current := snapshot ++ [(3, .unrelated)]
    let observation := run (fun q => matchingRows q snapshot) parentThenChild
    matchingRows isTarget current = [(0, .target), (1, .target)] ∧
    Valid (readDependencies observation.reads) current ∧
    run (fun q => matchingRows q current) parentThenChild = observation := by
  dsimp only
  refine ⟨rfl, by decide, ?_⟩
  exact validated_adaptive_query _ _ parentThenChild (by simp [PayloadConsistent]) (by decide)

/-- The parent result is unchanged; the new child row invalidates the
continuation's complete-result dependency and changes its answer. -/
theorem child_insert_invalidates_adaptive_certificate :
    let snapshot : Store Item := [(0, .target), (1, .other)]
    let current := snapshot ++ [(2, .other)]
    matchingRows isTarget current = matchingRows isTarget snapshot ∧
    ¬ Valid (readDependencies
      (run (fun q => matchingRows q snapshot) parentThenChild).reads) current ∧
    (run (fun q => matchingRows q current) parentThenChild).answer ≠
      (run (fun q => matchingRows q snapshot) parentThenChild).answer := by
  decide

/-- The adaptive child query returned no rows. Its absence still contributes
a dependency, so a later matching insertion cannot reuse the empty answer. -/
theorem empty_child_is_a_dependency :
    let snapshot : Store Item := [(0, .target)]
    let current := snapshot ++ [(1, .other)]
    (run (fun q => matchingRows q snapshot) parentThenChild).answer = [] ∧
    ¬ Valid (readDependencies
      (run (fun q => matchingRows q snapshot) parentThenChild).reads) current := by
  decide

/-- Complete identifiers alone accept a changed payload. The compiled row
certificate rejects it even though the query still returns the same ID. -/
theorem payload_change_needs_presence_claim :
    let snapshot : Store Item := [(0, .target)]
    let current : Store Item := [(0, .other)]
    let query : Item → Bool := fun _ => true
    Valid [.complete query (matching query snapshot)] current ∧
    ¬ Valid (rowDependencies query (matchingRows query snapshot)) current ∧
    matchingRows query current ≠ matchingRows query snapshot := by
  decide

/-- If one ID denotes different payloads, complete IDs and row membership
can agree while ordered payloads differ. Store integrity is essential. -/
theorem ambiguous_identifiers_break_row_validation :
    let snapshot : Store Item := [(0, .target), (0, .other)]
    let current : Store Item := [(0, .other), (0, .target)]
    let query : Item → Bool := fun _ => true
    Valid (rowDependencies query (matchingRows query snapshot)) current ∧
    matchingRows query current ≠ matchingRows query snapshot ∧
    ¬ PayloadConsistent current := by
  refine ⟨by decide, by decide, ?_⟩
  intro consistent
  have impossible := consistent (0, .other) (by simp) (0, .target) (by simp) rfl
  cases impossible

/-- Pausing after the parent read retains its two occurrence rows. A valid
prefix permits a fresh child query against the successor store. -/
theorem validated_prefix_reads_fresh_child :
    let snapshot : Store Item := [(0, .target), (1, .target)]
    let current := snapshot ++ [(2, .other)]
    let paused := pausePrefix (fun q => matchingRows q snapshot) 1 parentThenChild
    Valid (readDependencies paused.1) current ∧
    (run (fun q => matchingRows q current) paused.2).answer = [(2, .other)] ∧
    paused.1 ++ (run (fun q => matchingRows q current) paused.2).reads =
      (run (fun q => matchingRows q current) parentThenChild).reads := by
  dsimp only
  refine ⟨by decide, rfl, ?_⟩
  exact (validated_adaptive_resume _ _ 1 parentThenChild
    (by simp [PayloadConsistent]) (by decide)).2

end AdaptiveControls

/-! ## Axiom audit -/

#print axioms absent_insert_iff
#print axioms complete_insert_match
#print axioms coexist_inserter_absent_iff
#print axioms valid_of_coexist
#print axioms optimistic_admits_more
#print axioms returned_only_not_determines
#print axioms printed_value_does_not_rescue
#print axioms own_write_retained
#print axioms absence_invalidated
#print axioms valid_rowDependencies_payloads
#print axioms valid_readDependencies_iff
#print axioms captured_program_valid
#print axioms validated_adaptive_query
#print axioms coexisting_environment_preserves_adaptive_query
#print axioms readDependencies_bind
#print axioms validated_adaptive_resume
#print axioms AdaptiveControls.unrelated_insert_preserves_adaptive_query
#print axioms AdaptiveControls.child_insert_invalidates_adaptive_certificate
#print axioms AdaptiveControls.empty_child_is_a_dependency
#print axioms AdaptiveControls.payload_change_needs_presence_claim
#print axioms AdaptiveControls.ambiguous_identifiers_break_row_validation
#print axioms AdaptiveControls.validated_prefix_reads_fresh_child

end Mettapedia.GSLT.Contracts.Dependencies
