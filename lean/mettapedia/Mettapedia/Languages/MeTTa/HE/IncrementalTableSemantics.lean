import Mettapedia.Languages.MeTTa.HE.SnapshotPreservation
import Mettapedia.Languages.MeTTa.HE.BindingCacheSoundness
import Mettapedia.Languages.MeTTa.HE.VariantQueryCorrectness
import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.SourceSnapshot

/-!
# Incremental Table Semantics

Specifies correctness conditions for **incremental tabling**: accumulating
answers incrementally while consumers read partial results.

## Key Results

- `TableEntry.Sound` — every answer is a genuine query result
- `addAnswer_sound` — adding genuine answers preserves soundness
- `addAnswer_extends` — monotonicity (no retraction)
- `markComplete_sound` — completion preserves soundness
- `exact_is_sound` — exact tables are sound
- `tableEntry_addAtom_invalidates` — revision invalidation
- `tableEntry_variant_rhs_agree` — legacy variant queries share RHS atoms
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Table entry states -/

/-- Completion state of a table entry. -/
inductive TableStatus where
  | inProgress
  | completed
  deriving DecidableEq, Repr

/-- A table entry: accumulated answers + completion status. -/
structure TableEntry where
  query : Atom
  spaceRevision : Nat
  answers : List (Atom × Bindings)
  status : TableStatus

namespace TableEntry

def init (q : Atom) (rev : Nat) : TableEntry :=
  { query := q, spaceRevision := rev, answers := [], status := .inProgress }

def addAnswer (te : TableEntry) (ans : Atom × Bindings) : TableEntry :=
  match te.status with
  | .inProgress => { te with answers := ans :: te.answers }
  | .completed => te

def markComplete (te : TableEntry) : TableEntry :=
  { te with status := .completed }

theorem addAnswer_query (te : TableEntry) (ans : Atom × Bindings)
    (h : te.status = .inProgress) :
    (te.addAnswer ans).query = te.query := by simp [addAnswer, h]

theorem markComplete_query (te : TableEntry) :
    te.markComplete.query = te.query := rfl

end TableEntry

/-! ## §2: Soundness -/

def isGenuineAnswer (space : Space) (q : Atom) (fuel : Nat)
    (ans : Atom × Bindings) : Prop :=
  ans ∈ queryEquations space q fuel

def TableEntry.Sound (te : TableEntry) (space : Space) (fuel : Nat) : Prop :=
  ∀ ans, ans ∈ te.answers → isGenuineAnswer space te.query fuel ans

theorem TableEntry.init_sound (q : Atom) (rev : Nat) (space : Space) (fuel : Nat) :
    (TableEntry.init q rev).Sound space fuel :=
  fun _ h => by simp [TableEntry.init] at h

theorem TableEntry.addAnswer_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hpartial : te.status = .inProgress)
    (hsound : te.Sound space fuel)
    (ans : Atom × Bindings) (hgenuine : isGenuineAnswer space te.query fuel ans) :
    (te.addAnswer ans).Sound space fuel := by
  intro a hmem
  have hq := te.addAnswer_query ans hpartial
  rw [TableEntry.Sound, hq] at *
  simp [TableEntry.addAnswer, hpartial] at hmem
  rcases hmem with rfl | hmem
  · exact hgenuine
  · exact hsound a hmem

theorem TableEntry.addAnswer_complete_noop (te : TableEntry)
    (hcomplete : te.status = .completed) (ans : Atom × Bindings) :
    te.addAnswer ans = te := by simp [TableEntry.addAnswer, hcomplete]

theorem TableEntry.markComplete_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hsound : te.Sound space fuel) :
    te.markComplete.Sound space fuel := hsound

/-! ## §3: Monotonicity -/

theorem TableEntry.addAnswer_extends (te : TableEntry) (ans : Atom × Bindings)
    (hpartial : te.status = .inProgress) :
    ∀ a, a ∈ te.answers → a ∈ (te.addAnswer ans).answers := by
  intro a ha; simp [TableEntry.addAnswer, hpartial]; exact Or.inr ha

theorem TableEntry.addAnswer_mem_new (te : TableEntry) (ans : Atom × Bindings)
    (hpartial : te.status = .inProgress) :
    ans ∈ (te.addAnswer ans).answers := by
  simp [TableEntry.addAnswer, hpartial]

theorem TableEntry.markComplete_answers (te : TableEntry) :
    te.markComplete.answers = te.answers := rfl

/-! ## §4: Completeness -/

def TableEntry.Exact (te : TableEntry) (space : Space) (fuel : Nat) : Prop :=
  te.answers.Perm (queryEquations space te.query fuel)

theorem TableEntry.exact_is_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hexact : te.Exact space fuel) :
    te.Sound space fuel :=
  fun _ hmem => hexact.mem_iff.mp hmem

def TableEntry.populateExact (rs : RevisionedSpace) (q : Atom) (fuel : Nat) :
    TableEntry :=
  { query := q, spaceRevision := rs.revision,
    answers := queryEquations rs.space q fuel, status := .completed }

/-- Historical simpleMatch-based population model retained only for the legacy
variant-key cache theorem. The repaired public query interface is
`TableEntry.populateExact`. -/
def TableEntry.populateExactLegacy (rs : RevisionedSpace) (q : Atom) (fuel : Nat) :
    TableEntry :=
  { query := q, spaceRevision := rs.revision,
    answers := variantLegacyQueryEquations rs.space q fuel, status := .completed }

theorem TableEntry.populateExact_exact (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    (TableEntry.populateExact rs q fuel).Exact rs.space fuel :=
  List.Perm.refl _

theorem TableEntry.populateExact_valid (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    (TableEntry.populateExact rs q fuel).spaceRevision = rs.revision := rfl

/-! ## §5: Revision invalidation -/

theorem tableEntry_addAtom_invalidates (rs : RevisionedSpace) (a : Atom)
    (te : TableEntry) (hvalid : te.spaceRevision = rs.revision) :
    te.spaceRevision ≠ (rs.addAtom a).revision := by
  simp [RevisionedSpace.addAtom] at *; omega

theorem tableEntry_snapshot_permanent (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    let snap := rs.snapshot
    let te := TableEntry.populateExact ⟨⟨snap.atoms⟩, snap.frozenRevision⟩ q fuel
    te.spaceRevision = snap.frozenRevision := rfl

/-! ## §6: Legacy variant-key compatibility -/

theorem tableEntry_variant_rhs_agree
    (rs : RevisionedSpace) (q₁ q₂ : Atom) (hvar : VariantEquiv q₁ q₂) (fuel : Nat) :
    (TableEntry.populateExactLegacy rs q₁ fuel).answers.map Prod.fst =
    (TableEntry.populateExactLegacy rs q₂ fuel).answers.map Prod.fst :=
  variant_queries_same_rhs rs.space q₁ q₂ hvar fuel

/-! ## §7: Table store -/

structure TableStore where
  entries : List (Atom × TableEntry)

namespace TableStore

def empty : TableStore := ⟨[]⟩

def lookup (ts : TableStore) (q : Atom) : Option TableEntry :=
  ts.entries.find? (fun (k, _) => k == q) |>.map Prod.snd

def upsert (ts : TableStore) (q : Atom) (te : TableEntry) : TableStore :=
  ⟨(q, te) :: ts.entries.filter (fun (k, _) => !(k == q))⟩

end TableStore

/-! ## Conservative complete-read instance

The existing HE table is a query-equation table, not a general evaluator
cache. Its conservative dependency is the complete captured space, including
failed queries. The authority additionally distinguishes source revisions.
Equality checking of this certificate has no constant-cost claim.
-/

namespace TableEntry

open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadCertifiedQueryReuse

/-- A complete space read supports the existing ordered query operation. -/
def queryFamily : Supported.Family RevisionedSpace Nat (Atom × Nat) Unit Space
    (List (Atom × Bindings)) where
  authority := RevisionedSpace.revision
  memory := fun source _ => source.space
  observe := fun source query =>
    ⟨queryEquations source.space query.1 query.2, [((), source.space)]⟩
  certifies := by
    intro source query read present
    simp only [List.mem_singleton] at present
    subst present
    rfl
  stable := by
    intro first second query _ reads
    have sameSpace : second.space = first.space := reads ((), first.space) (by simp)
    exact congrArg (fun space => queryEquations space query.1 query.2) sameSpace

def captureRead (source : RevisionedSpace) (query : Atom) (fuel : Nat) :
    Supported.Captured queryFamily :=
  Supported.capture queryFamily source (query, fuel)

theorem captureRead_recorded (source : RevisionedSpace) (query : Atom) (fuel : Nat) :
    Supported.Recorded queryFamily (captureRead source query fuel).val :=
  (captureRead source query fuel).property

/-- Population in the older table representation and in the shared dependency
interface agree on their complete ordered answer records. -/
theorem captureRead_answers (source : RevisionedSpace) (query : Atom) (fuel : Nat) :
    (captureRead source query fuel).val.value.answer = (populateExact source query fuel).answers := rfl

def reuseRead (current : RevisionedSpace) (query : Atom) (fuel : Nat)
    (entry : Supported.Captured queryFamily) :
    List (Atom × Bindings) × Nat :=
  Supported.reuseCaptured queryFamily current (query, fuel) entry

/-- The validator and the fresh query take different paths. Their ordered
answers coincide for every genuinely captured entry, including absence. -/
theorem reuseRead_exact (old current : RevisionedSpace) (query : Atom) (fuel : Nat) :
    (reuseRead current query fuel (captureRead old query fuel)).1 =
      queryEquations current.space query fuel :=
  Supported.reuseCaptured_exact queryFamily current (query, fuel) (captureRead old query fuel)

theorem unchangedRead_reuses (source : RevisionedSpace) (query : Atom) (fuel : Nat) :
    reuseRead source query fuel (captureRead source query fuel) =
      (queryEquations source.space query fuel, 0) :=
  Supported.unchanged_reuses queryFamily source (query, fuel)

/-- Any revision edit refuses the old authority, independently of its reads. -/
theorem addAtom_recomputes (source : RevisionedSpace) (atom query : Atom) (fuel : Nat) :
    reuseRead (source.addAtom atom) query fuel (captureRead source query fuel) =
      (queryEquations (source.addAtom atom).space query fuel, 1) := by
  have rejected : Supported.admissible queryFamily (source.addAtom atom) (query, fuel)
      (captureRead source query fuel).val = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have same := ((Supported.admissible_iff _ _ _ _).mp accepted).1
    change source.revision = (source.addAtom atom).revision at same
    simp only [RevisionedSpace.addAtom] at same
    omega
  unfold reuseRead Supported.reuseCaptured Supported.reuse
  rw [if_neg (by rw [rejected]; decide)]
  rfl

/-- Retained readers query their captured HE space. Writes alter the current
world without changing that reader's ordered query answers. -/
theorem pinned_queries_exact (snapshot current : Space)
    (steps : List (Mettapedia.Machines.SourceSnapshot.Step Atom (Atom × Nat))) :
    ((Mettapedia.Machines.SourceSnapshot.captured
      (Mettapedia.Machines.SourceSnapshot.pureProvider
        (fun query atoms => queryEquations ⟨atoms⟩ query.1 query.2))
      snapshot.atoms current.atoms steps).2.map (fun reading => (reading.operation, reading.value))) =
    (Mettapedia.Machines.SourceSnapshot.operations steps).map
      (fun query => (query, queryEquations snapshot query.1 query.2)) :=
  Mettapedia.Machines.SourceSnapshot.captured_pure_values _ snapshot.atoms current.atoms steps

end TableEntry

namespace TableReadControls

open Mettapedia.Machines.SourceSnapshot

private def query : Atom := .expression [.symbol "f"]
private def rule : Atom := .expression [.symbol "=", query, .symbol "answer"]
private def changed : Space := Space.ofList [rule]
private def operation : Atom × Nat := (query, 8)
private def provider : Provider Atom (Atom × Nat) (List (Atom × Bindings)) :=
  pureProvider (fun query atoms => queryEquations ⟨atoms⟩ query.1 query.2)

/-- A failed captured query remains empty across a write. Reopening reads
the new equation instead; snapshot retention and cache validation are distinct. -/
theorem pinned_absence_and_reopened_insertion_differ :
    ((captured provider [] [] [.visit operation, .write changed.atoms, .visit operation]).2.map
      (fun reading => reading.value.map Prod.fst)) = [[], []] ∧
    ((reopened provider [] [.visit operation, .write changed.atoms, .visit operation]).2.map
      (fun reading => reading.value.map Prod.fst)) = [[], [.symbol "answer"]] := by decide

/-- The conservative current-world cache refuses that same absent read after
the source revision changes, and returns the fresh ordered answer. -/
theorem absent_read_invalidates_on_matching_insertion :
    (TableEntry.reuseRead ((⟨Space.empty, 0⟩ : RevisionedSpace).addAtom rule) query 8
      (TableEntry.captureRead ⟨Space.empty, 0⟩ query 8)).1.map Prod.fst = [.symbol "answer"] ∧
    (TableEntry.reuseRead ((⟨Space.empty, 0⟩ : RevisionedSpace).addAtom rule) query 8
      (TableEntry.captureRead ⟨Space.empty, 0⟩ query 8)).2 = 1 := by decide

end TableReadControls

end Mettapedia.Languages.MeTTa.HE
