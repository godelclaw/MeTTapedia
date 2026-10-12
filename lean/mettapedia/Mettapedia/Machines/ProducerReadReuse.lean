import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.ConstraintPropagation
import Mathlib.Data.List.Infix

/-!
# Reusing recursive generator rounds through producer reads

A generator may observe different snapshots while its callees discover
answers. Reuse is justified only if every observed answer list remains an
unchanged prefix of the final list. In an append-only computation, matching
lengths establish equality of the complete lists, including order and repeats.
This also covers a read which found no answers.

The operational model below reads successive snapshots; the comparison runs
the same pure adaptive program against one final store. They are distinct
algorithms. Version validation and the previous round's actual merge establish
that a skipped round cannot add support. This does not establish purity for
arbitrary language programs, a native hash-table correspondence, general
recursive completion, or a bound on C instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerReadReuse

open ReadOnlyQuery

universe u v w

variable {Key : Type u} {Value : Type v} {Answer : Type w}

/-- One snapshot per read event; continuations depend on actual read values. -/
def runChanging (stores : Nat → Key → Value) (start : Nat) :
    Program Key Value Answer → Observation Key Value Answer
  | .pure answer => ⟨answer, []⟩
  | .read key next =>
      let value := stores start key
      let rest := runChanging stores (start + 1) (next value)
      ⟨rest.answer, (key, value) :: rest.reads⟩

/-- Agreement retains the entire result and read path, not just support. -/
theorem replay_changing_exact (stores : Nat → Key → Value)
    (final : Key → Value) (start : Nat) (program : Program Key Value Answer)
    (valid : Agrees final (runChanging stores start program).reads) :
    run final program = runChanging stores start program := by
  induction program generalizing start with
  | pure answer => rfl
  | read key next ih =>
      have here : final key = stores start key :=
        valid (key, stores start key) (by simp [runChanging])
      have tail : Agrees final
          (runChanging stores (start + 1) (next (stores start key))).reads := by
        intro observed member
        exact valid observed (by simp [runChanging, member])
      simp only [run, runChanging, here, ih (stores start key) (start + 1) tail]

variable {Item : Type v}

def versions (reads : Reads Key (List Item)) : Reads Key Nat :=
  reads.map fun read => (read.1, read.2.length)

/-- The observed lists may grow, but cannot be replaced or rearranged. -/
def ExtendsReads (final : Key → List Item) (reads : Reads Key (List Item)) : Prop :=
  ∀ read ∈ reads, read.2 <+: final read.1

theorem version_agreement_iff (final : Key → List Item)
    (reads : Reads Key (List Item)) :
    Agrees (fun key => (final key).length) (versions reads) ↔
      ∀ read ∈ reads, (final read.1).length = read.2.length := by
  constructor
  · intro agrees read member
    exact agrees (read.1, read.2.length) (List.mem_map.mpr ⟨read, member, rfl⟩)
  · intro lengths read member
    obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp member
    exact lengths original belongs

/-- Length is a complete change token only under the append-only law. -/
theorem equal_versions_agree (final : Key → List Item)
    (reads : Reads Key (List Item)) (extension : ExtendsReads final reads)
    (valid : checkReads (fun key => (final key).length) (versions reads) = true) :
    Agrees final reads := by
  have lengths := (version_agreement_iff final reads).mp
    ((checkReads_iff _ _).mp valid)
  intro read member
  exact ((extension read member).eq_of_length (lengths read member).symm).symm

theorem version_replay_exact (stores : Nat → Key → List Item)
    (final : Key → List Item) (start : Nat)
    (program : Program Key (List Item) Answer)
    (extension : ExtendsReads final (runChanging stores start program).reads)
    (valid : checkReads (fun key => (final key).length)
      (versions (runChanging stores start program).reads) = true) :
    run final program = runChanging stores start program :=
  replay_changing_exact stores final start program
    (equal_versions_agree final _ extension valid)

/-- A purity license belongs to a particular immutable region snapshot.
Producer versions certify its reads only while that region version is retained.
This does not certify a native mutation counter's snapshot interpretation. -/
theorem region_version_replay_exact {Region Version : Type*}
    (regions : Version → Region) (licensed current : Version)
    (unchanged : current = licensed)
    (program : Region → Program Key (List Item) Answer)
    (stores : Nat → Key → List Item) (final : Key → List Item) (start : Nat)
    (extension : ExtendsReads final
      (runChanging stores start (program (regions licensed))).reads)
    (valid : checkReads (fun key => (final key).length)
      (versions (runChanging stores start (program (regions licensed))).reads) = true) :
    run final (program (regions current)) =
      runChanging stores start (program (regions licensed)) := by
  subst current
  exact version_replay_exact stores final start _ extension valid

/-- Independent callers may materialize fresh views of the same observation. -/
theorem fresh_materialization_exact (stores : Nat → Key → List Item)
    (final : Key → List Item) (start : Nat)
    (program : Program Key (List Item) Answer)
    (extension : ExtendsReads final (runChanging stores start program).reads)
    (valid : checkReads (fun key => (final key).length)
      (versions (runChanging stores start program).reads) = true)
    {Invocation Result : Type*} (materialize : Invocation → Answer → Result)
    (invocation : Invocation) :
    materialize invocation (run final program).answer =
      materialize invocation (runChanging stores start program).answer := by
  rw [version_replay_exact stores final start program extension valid]

/-- The previous round really merged its result before it can be skipped. -/
theorem reusable_round_adds_no_support [DecidableEq Answer]
    (stores : Nat → Key → List Item) (final : Key → List Item) (start : Nat)
    (program : Program Key (List Item) (Finset Answer))
    (before current : Finset Answer)
    (merged : before ∪ (runChanging stores start program).answer ⊆ current)
    (extension : ExtendsReads final (runChanging stores start program).reads)
    (valid : checkReads (fun key => (final key).length)
      (versions (runChanging stores start program).reads) = true) :
    current ∪ (run final program).answer = current := by
  rw [version_replay_exact stores final start program extension valid]
  exact Finset.union_eq_left.mpr (Finset.subset_union_right.trans merged)

/-- A first read and a later different revision cannot both validate. -/
theorem mixed_revision_rejected (final : Key → Nat)
    (key : Key) (first second : Nat) (different : first ≠ second) :
    checkReads final [(key, first), (key, second)] = false := by
  have unequal : ¬ Agrees final [(key, first), (key, second)] := by
    intro valid
    exact different ((valid (key, first) (by simp)).symm.trans
      (valid (key, second) (by simp)))
  cases checked : checkReads final [(key, first), (key, second)] with
  | false => rfl
  | true => exact False.elim (unequal ((checkReads_iff _ _).mp checked))

/-- If a previously empty producer gains an answer, its reader must run again. -/
theorem empty_read_growth_rejected (final : Key → List Item) (key : Key)
    (nonempty : final key ≠ []) :
    checkReads (fun key => (final key).length)
      (versions [(key, ([] : List Item))]) = false := by
  have positive : (final key).length ≠ 0 := by simpa using nonempty
  simp [checkReads, versions, positive]

/-! ## Positive and negative controls -/

def headOrZero : Program Unit (List Nat) Nat :=
  .read () fun answers => .pure (answers.headD 0)

def firstEmpty : Nat → Unit → List Nat := fun _ _ => []
def oneAnswer : Unit → List Nat := fun _ => [7]

def answerFromRegion (region : Nat) : Program Unit (List Nat) Nat :=
  .read () fun _ => .pure region

theorem unchanged_producers_do_not_certify_the_region :
    checkReads (fun _ : Unit => 0)
      (versions (run (fun _ => []) (answerFromRegion 0)).reads) = true ∧
    (run (fun _ => []) (answerFromRegion 0)).answer ≠
      (run (fun _ => []) (answerFromRegion 1)).answer := by decide

theorem absence_is_a_dependency :
    (runChanging firstEmpty 0 headOrZero).answer = 0 ∧
    (run oneAnswer headOrZero).answer = 7 ∧
    checkReads (fun key => (oneAnswer key).length)
      (versions (runChanging firstEmpty 0 headOrZero).reads) = false := by decide

theorem length_alone_does_not_certify_replacement :
    ([1] : List Nat).length = [2].length ∧
    (run (fun _ : Unit => [1]) headOrZero).answer ≠
      (run (fun _ : Unit => [2]) headOrZero).answer := by decide

theorem equal_support_does_not_certify_order_or_multiplicity :
    ([1, 2] : List Nat).toFinset = [2, 1, 1].toFinset ∧
      ([1, 2] : List Nat) ≠ [2, 1, 1] := by decide

def changingPair : Program Bool (List Nat) (List Nat × List Nat) :=
  .read false fun left => .read true fun right => .pure (left, right)

def stableSnapshots : Nat → Bool → List Nat := fun time key =>
  if key then [time] else [3, 3]

theorem changing_unread_snapshots_preserve_the_full_answer :
    run (fun key => if key then [1] else [3, 3]) changingPair =
      runChanging stableSnapshots 0 changingPair := by rfl

def mixedSameProducer : Program Unit (List Nat) (List Nat × List Nat) :=
  .read () fun left => .read () fun right => .pure (left, right)

theorem overwriting_the_first_revision_is_unsound :
    (runChanging (fun time _ => List.replicate time 7) 0 mixedSameProducer).answer =
      ([], [7]) ∧
    (run oneAnswer mixedSameProducer).answer = ([7], [7]) ∧
    checkReads (fun key => (oneAnswer key).length)
      (versions (runChanging (fun time _ => List.replicate time 7)
        0 mixedSameProducer).reads) = false := by decide

#print axioms replay_changing_exact
#print axioms equal_versions_agree
#print axioms version_replay_exact
#print axioms reusable_round_adds_no_support
#print axioms overwriting_the_first_revision_is_unsound

end Mettapedia.Machines.ProducerReadReuse
