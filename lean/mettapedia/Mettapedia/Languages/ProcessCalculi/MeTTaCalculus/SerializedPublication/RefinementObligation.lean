import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication.RevisionValidation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.OptimisticRetries
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave

/-!
# What a fine-grained publication runtime must refine, and where revision validation stops

`RevisionValidation` models publication validated by one revision per space as the commit
protocol over widened proposals. This module states the obligation a fine-grained runtime must
meet instead, and checks the revision protocol and the per-occurrence protocol against it.

## Invalidation rules

A runtime's validation is summarized by an **invalidation rule** `inv d c`: publishing `d` makes an
open attempt of `c` invalid. Two properties matter.

* **Sound** (`SoundFor`): the rule invalidates whatever serializable validation must invalidate
  (`OptimisticRetries.Invalidates` at `Mode.serializable`). Every runtime must be sound; with
  atomic commit steps this is what `CommitProtocol.Run.refines` turns into serializability.
* **Local** (`LocalTo key`): the rule invalidates only for a reason in the attempt's footprint:
  a common take, a take of a kept occurrence, a common fresh identity, or a write inside the
  epoch key of a region the attempt queries. `key` may be coarser than the regions it
  validates (`Covers`, `localTo_mono`), which adds aborts only among commits that touch one key.

## Results

* Serializable validation is sound and local with the finest keys
  (`serializable_soundFor`, `serializable_localTo`). The per-occurrence protocol keeps a ready
  transaction ready across every commit that neither clashes with it nor spoils it
  (`CommitProtocol.ready_commitState`), and that rule is local (`clashOrSpoils_localTo`). Run over
  widened transactions, the same rule becomes "any write" (`widened_clashOrSpoils_iff`).
* **Revision validation invalidates exactly on any write**: an attempt widened by a revision
  check is invalidated by a commit exactly when that commit takes or makes something
  (`widened_invalidates_iff`). The rule is sound (`revision_soundFor`) and local for no choice of
  keys at all (`revision_not_localTo`).
* Locality is what makes writers on distinct channels never abort each other: a local rule never
  invalidates an attempt whose footprint is apart from the committed one (`localTo_apart`).
* **Progress.** A reader of a token beside a writer of unrelated facts is never invalidated
  under serializable validation (`Controls.base_neverInvalidated`), so by
  `OptimisticRetries.never_aborts` it never aborts in any execution. Widened by revision checks,
  every write of the writer invalidates every open attempt of the reader
  (`Controls.widened_reader_invalidated`), which is the schedule of
  `OptimisticRetries.Controls.optimistic_starvation`.
* **Preparation waves are not commit waves.** On the native preparation footprint the resource
  selector admits exactly the first `workers` tasks of the agenda and defers the rest
  (`preparation_selectWave`, from `CeTTaResourceWave.Preparation.enabled_iff`): the maximal
  admitted wave is a prefix cut by the worker credits, and no read, take or write of the tasks
  enters the decision. Carrying the two rival takers of one token, an admitted wave has no
  executable order (`preparation_wave_not_commit_wave`). Serialized revision-validated
  publication then commits at most one writer per snapshot
  (`RevisionValidation.writers_only_last`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

/-! ## Invalidation rules -/

section Rules

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The rule invalidates at least what serializable validation must invalidate. -/
def SoundFor (label : O → R) (inv : Commit O R → Commit O R → Prop) : Prop :=
  ∀ d c, Liveness.Invalidates label Mode.serializable d c → inv d c

/-- The rule invalidates only for a reason inside the attempt's footprint, reading each queried
region through its epoch key. -/
def LocalTo (label : O → R) (key : (R → Bool) → R → Bool)
    (inv : Commit O R → Commit O R → Prop) : Prop :=
  ∀ d c, inv d c → ¬ Disjoint d.taken c.taken ∨ ¬ Disjoint d.taken c.kept ∨
    ¬ Disjoint d.made c.made ∨ ∃ read ∈ c.queries, ∃ o ∈ d.taken ∪ d.made, key read.region (label o) = true

/-- An epoch key contains each region it validates. -/
def Covers (key : (R → Bool) → R → Bool) : Prop :=
  ∀ region x, region x = true → key region x = true

/-- **Serializable validation is sound**, trivially. -/
theorem serializable_soundFor (label : O → R) :
    SoundFor label (Liveness.Invalidates label Mode.serializable) := fun _ _ invalid => invalid

/-- **Serializable validation is local with the finest keys.** -/
theorem serializable_localTo (label : O → R) :
    LocalTo label id (Liveness.Invalidates label Mode.serializable) := by
  intro d c invalid
  rcases invalid with ⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, o, written, inRegion⟩
  · exact Or.inl takes
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, inRegion⟩))

/-- A coarser key keeps a local rule local. -/
theorem localTo_mono {label : O → R} {key key' : (R → Bool) → R → Bool}
    (coarser : ∀ region x, key region x = true → key' region x = true)
    {inv : Commit O R → Commit O R → Prop} (local_ : LocalTo label key inv) :
    LocalTo label key' inv := by
  intro d c invalid
  rcases local_ d c invalid with takes | keeps | made | ⟨read, member, o, written, inKey⟩
  · exact Or.inl takes
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inl made))
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, coarser _ _ inKey⟩))

/-- Every key that covers its regions keeps serializable validation local. -/
theorem serializable_localTo_of_covers (label : O → R) {key : (R → Bool) → R → Bool}
    (covers : Covers key) : LocalTo label key (Liveness.Invalidates label Mode.serializable) :=
  localTo_mono (fun region x inRegion => covers region x inRegion) (serializable_localTo label)

/-- **A local rule never invalidates an attempt apart from the committed footprint**: one that
shares no take, keeps nothing taken, shares no fresh identity and queries no key the
commit writes into. Writers on distinct channels, with channels as keys, never abort each
other. -/
theorem localTo_apart {label : O → R} {key : (R → Bool) → R → Bool}
    {inv : Commit O R → Commit O R → Prop} (local_ : LocalTo label key inv) {d c : Commit O R}
    (takes : Disjoint d.taken c.taken) (keeps : Disjoint d.taken c.kept)
    (made : Disjoint d.made c.made)
    (keysApart : ∀ read ∈ c.queries, ∀ o ∈ d.taken ∪ d.made, key read.region (label o) = false) :
    ¬ inv d c := by
  intro invalid
  rcases local_ d c invalid with clash | spoiled | fresh | ⟨read, member, o, written, inKey⟩
  · exact clash takes
  · exact spoiled keeps
  · exact fresh made
  · rw [keysApart read member o written] at inKey
    exact absurd inKey (by decide)

/-- **An attempt widened by a revision check is invalidated by a commit exactly when that commit
takes or makes something.** -/
theorem widened_invalidates_iff {label : O → R} {snapshot : Finset O} {d c : Commit O R} :
    Liveness.Invalidates label Mode.serializable d (widen snapshot c) ↔ WritesSomething d := by
  constructor
  · rintro (⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, o, written, _⟩)
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp takes
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp keeps
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · exact ⟨o, written⟩
  · rintro ⟨o, written⟩
    exact Or.inr (Or.inr ⟨by simp [Mode.serializable], revisionQuery snapshot, List.mem_cons_self,
      o, written, rfl⟩)

/-- **The per-occurrence protocol's rule is local with the finest keys.** A ready transaction of
`CommitProtocol` stays ready across every commit that neither clashes with it nor spoils it
(`CommitProtocol.ready_commitState`); that rule is local. -/
theorem clashOrSpoils_localTo (label : O → R) :
    LocalTo label id (fun d c => Clash d c ∨ Spoils label d c) := by
  intro d c invalid
  rcases invalid with (takes | made) | (keeps | ⟨read, member, o, written, inRegion⟩)
  · exact Or.inl takes
  · exact Or.inr (Or.inr (Or.inl made))
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, inRegion⟩))

/-- **The same rule on widened transactions is any write.** Run over proposals widened by a
revision check, the per-occurrence protocol keeps a ready transaction ready across a commit
exactly when that commit writes nothing. -/
theorem widened_clashOrSpoils_iff {label : O → R} {snapshot : Finset O} {d c : Commit O R} :
    Clash d (widen snapshot c) ∨ Spoils label d (widen snapshot c) ↔ WritesSomething d := by
  constructor
  · rintro ((takes | made) | (keeps | ⟨_, _, o, written, _⟩))
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp takes
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp made
      exact ⟨o, Finset.mem_union_right _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp keeps
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · exact ⟨o, written⟩
  · intro writes
    exact Or.inr (spoils_widen_of_writes writes)

/-- The invalidation rule of revision validation, on the base commits: any write. -/
def revisionRule (d _c : Commit O R) : Prop := WritesSomething d

/-- **Revision validation is sound.** -/
theorem revision_soundFor (label : O → R) : SoundFor label (revisionRule (O := O) (R := R)) := by
  intro d c invalid
  have widened : Liveness.Invalidates label Mode.serializable d (widen ∅ c) := by
    rcases invalid with ⟨member, takes⟩ | ⟨member, keeps⟩ | ⟨member, read, inQueries, o, written, inRegion⟩
    · exact Or.inl ⟨member, takes⟩
    · exact Or.inr (Or.inl ⟨member, keeps⟩)
    · exact Or.inr (Or.inr ⟨member, read, List.mem_cons_of_mem _ inQueries, o, written, inRegion⟩)
  exact widened_invalidates_iff.mp widened

end Rules

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls (Atom)

/-- A reader of the token, emitting a fresh output. -/
def readToken : Commit ℕ Atom := OccurrenceCommits.Controls.reader

/-- A writer of one unrelated fresh fact. -/
def writeFact (n : ℕ) : Commit ℕ Atom := ⟨∅, ∅, {n}, []⟩

/-- **Revision validation is local for no choice of epoch keys**: a write of an unrelated fact
invalidates a reader with which it shares nothing. -/
theorem revision_not_localTo (key : (Atom → Bool) → Atom → Bool) :
    ¬ LocalTo lab key (revisionRule (O := ℕ) (R := Atom)) := by
  intro local_
  rcases local_ (writeFact 10) readToken ⟨10, by simp [writeFact]⟩ with
    takes | keeps | made | ⟨read, member, _⟩
  · exact takes (by simp [writeFact])
  · exact keeps (by simp [writeFact])
  · exact made (by simp [writeFact, readToken, OccurrenceCommits.Controls.reader])
  · simp [readToken, OccurrenceCommits.Controls.reader] at member

/-- The reader is a one-shot transaction; the writer is persistent and may write any fact at an
identity from `10` on. -/
def baseProgram : Liveness.Program Bool ℕ Atom where
  rows := fun t => match t with
    | true => {readToken}
    | false => {c | ∃ n, 10 ≤ n ∧ c = writeFact n}
  persistent := fun t => match t with
    | true => false
    | false => true

/-- The same program with every row widened by a revision check at any snapshot. -/
def widenedProgram : Liveness.Program Bool ℕ Atom where
  rows := fun t => {c | ∃ snapshot base, base ∈ baseProgram.rows t ∧ c = widen snapshot base}
  persistent := baseProgram.persistent

/-- **Positive control.** Under serializable validation no row of the reader-writer program
invalidates another, so by `OptimisticRetries.never_aborts` no execution ever aborts. -/
theorem base_neverInvalidated : Liveness.NeverInvalidated lab Mode.serializable baseProgram := by
  intro t t' d c rowD rowC invalid
  have dWrites : d.taken = ∅ ∧ d.made.Nonempty ∨ d = readToken := by
    cases t with
    | true =>
        right
        simpa [baseProgram] using rowD
    | false =>
        left
        obtain ⟨n, _, rfl⟩ := rowD
        exact ⟨rfl, ⟨n, by simp [writeFact]⟩⟩
  have cQueries : c.queries = [] ∧ c.taken = ∅ := by
    cases t' with
    | true =>
        have : c = readToken := by simpa [baseProgram] using rowC
        subst this
        simp [readToken, OccurrenceCommits.Controls.reader]
    | false =>
        obtain ⟨n, _, rfl⟩ := rowC
        simp [writeFact]
  rcases invalid with ⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, _⟩
  · exact takes (by rw [cQueries.2]; simp)
  · rcases dWrites with ⟨noTake, _⟩ | same
    · exact keeps (by rw [noTake]; simp)
    · subst same
      exact keeps (by simp [readToken, OccurrenceCommits.Controls.reader])
  · rw [cQueries.1] at member
    simp at member

/-- **Negative control.** Widened by revision checks, a write of the writer invalidates an open
attempt of the reader, at every snapshot: under the optimistic semantics the reader's attempt
turns invalid at each of the writer's commits. -/
theorem widened_reader_invalidated (snapshot snapshot' : Finset ℕ) (n : ℕ) (_ : 10 ≤ n) :
    Liveness.Invalidates lab Mode.serializable (widen snapshot' (writeFact n))
        (widen snapshot readToken) ∧
      Liveness.invalidate lab Mode.serializable (widen snapshot' (writeFact n))
        (Liveness.Phase.active (widen snapshot readToken) true) =
        Liveness.Phase.active (widen snapshot readToken) false ∧
      ¬ Liveness.NeverInvalidated lab Mode.serializable widenedProgram := by
  have invalid : Liveness.Invalidates lab Mode.serializable (widen snapshot' (writeFact n))
      (widen snapshot readToken) :=
    widened_invalidates_iff.mpr ⟨n, by simp [writeFact]⟩
  refine ⟨invalid, ?_, ?_⟩
  · simp [Liveness.invalidate, invalid]
  · intro never
    exact never false true (widen snapshot' (writeFact n)) (widen snapshot readToken)
      ⟨snapshot', writeFact n, ⟨n, by assumption, rfl⟩, rfl⟩
      ⟨snapshot, readToken, by simp [baseProgram], rfl⟩ invalid

/-- A taker writes; a reader that makes nothing writes nothing. -/
theorem writesSomething_controls :
    WritesSomething takeFirst ∧ ¬ WritesSomething (Commit.keepOne 0 : Commit ℕ Atom) := by
  refine ⟨⟨0, by simp [takeFirst]⟩, ?_⟩
  rintro ⟨o, written⟩
  simp at written

/-- **A rule that never invalidates is not sound**: serializable validation invalidates the second
of two takers of one token. -/
theorem never_not_soundFor : ¬ SoundFor lab (fun _ _ : Commit ℕ Atom => False) := fun sound =>
  sound takeFirst takeFirst (Or.inl ⟨by simp [Mode.serializable], by simp [takeFirst]⟩)

/-- Revision validation is sound at the controls' labels, as serializable validation is. -/
theorem soundFor_instances :
    SoundFor lab (Liveness.Invalidates lab Mode.serializable) ∧
      SoundFor lab (revisionRule (O := ℕ) (R := Atom)) :=
  ⟨serializable_soundFor lab, revision_soundFor lab⟩

/-- Serializable validation is local with the finest keys, at the controls' labels. -/
theorem serializable_local_instance : LocalTo lab id (Liveness.Invalidates lab Mode.serializable) :=
  serializable_localTo lab

/-- The identity key covers every region; the empty key covers none that holds anything. -/
theorem covers_controls :
    Covers (R := Atom) id ∧ ¬ Covers (R := Atom) (fun _ _ => false) := by
  refine ⟨fun _ _ inRegion => inRegion, fun covers => ?_⟩
  have := covers (fun _ => true) Atom.tok rfl
  simp at this

end Controls

/-! ## Preparation waves are not commit waves -/

section Preparation

open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls (Atom)

/-- The commits the two prepared tasks of the control carry: the two rival takers of one
token. -/
def taskCommit : BitVec 64 → Commit ℕ Atom
  | 1 => OccurrenceCommits.Controls.taker
  | _ => OccurrenceCommits.Controls.taker₂

/-- Once the worker credits are used up, the selector defers every further task. -/
theorem preparation_full_defers (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) (done : List (BitVec 64))
    (full : workers ≤ done.length) :
    ∀ rest : List (BitVec 64),
      (Preparation.system owner instanceId revision).selectWaveAux
          (Preparation.supply owner instanceId revision catalogue workers)
          (Preparation.entries owner instanceId revision done)
          (Preparation.entries owner instanceId revision rest) =
        ([], Preparation.entries owner instanceId revision rest)
  | [] => by
      simp [Preparation.entries, Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux]
  | x :: rest => by
      have refused : ¬ (Preparation.system owner instanceId revision).StepEnables
          (Preparation.supply owner instanceId revision catalogue workers)
          ((Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] : List _) : Multiset _) := by
        have appended : Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] =
            Preparation.entries owner instanceId revision (done ++ [x]) := by
          simp [Preparation.entries]
        rw [appended, Preparation.enabled_iff]
        rintro ⟨_, tooMany⟩
        simp at tooMany
        omega
      change (Preparation.system owner instanceId revision).selectWaveAux _ _
          (Preparation.entry owner instanceId revision x ::
            Preparation.entries owner instanceId revision rest) = _
      rw [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux, if_neg refused,
        preparation_full_defers owner instanceId revision catalogue workers done full rest]
      rfl

/-- The scan of the selector over a preparation catalogue, from any prefix already selected. -/
theorem preparation_selectWaveAux (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) :
    ∀ (rest done : List (BitVec 64)), done ++ rest = catalogue → done.length ≤ workers →
      (Preparation.system owner instanceId revision).selectWaveAux
          (Preparation.supply owner instanceId revision catalogue workers)
          (Preparation.entries owner instanceId revision done)
          (Preparation.entries owner instanceId revision rest) =
        (Preparation.entries owner instanceId revision (rest.take (workers - done.length)),
          Preparation.entries owner instanceId revision (rest.drop (workers - done.length)))
  | [], _, _, _ => by
      simp [Preparation.entries, Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux]
  | x :: rest, done, whole, bound => by
      by_cases room : done.length < workers
      · have prefixLe : ((done ++ [x] : List (BitVec 64)) : Multiset (BitVec 64)) ≤ catalogue := by
          rw [← whole]
          exact Multiset.coe_le.mpr
            ((List.Sublist.append_left (List.singleton_sublist.mpr List.mem_cons_self) done).subperm)
        have appended : Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] =
            Preparation.entries owner instanceId revision (done ++ [x]) := by
          simp [Preparation.entries]
        have admitted : (Preparation.system owner instanceId revision).StepEnables
            (Preparation.supply owner instanceId revision catalogue workers)
            ((Preparation.entries owner instanceId revision done ++
              [Preparation.entry owner instanceId revision x] : List _) : Multiset _) := by
          rw [appended, Preparation.enabled_iff]
          exact ⟨prefixLe, by simp; omega⟩
        have later := preparation_selectWaveAux owner instanceId revision catalogue workers rest
          (done ++ [x]) (by simpa using whole) (by simp; omega)
        rw [← appended] at later
        obtain ⟨k, hk⟩ : ∃ k, workers - done.length = k + 1 := ⟨workers - done.length - 1, by omega⟩
        have hk' : workers - (done ++ [x]).length = k := by simp; omega
        rw [hk'] at later
        change (Preparation.system owner instanceId revision).selectWaveAux _ _
            (Preparation.entry owner instanceId revision x ::
              Preparation.entries owner instanceId revision rest) = _
        rw [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux, if_pos admitted,
          later, hk]
        rfl
      · have full : done.length = workers := by omega
        have deferred := preparation_full_defers owner instanceId revision catalogue workers done
          (by omega) (x :: rest)
        rw [deferred, full]
        simp [Preparation.entries]

/-- **The maximal admitted preparation wave is the first `workers` tasks of the agenda.** The
selector, run on the native preparation footprint, admits exactly the prefix of the catalogue
that fits the worker credits and defers the rest; nothing about the tasks' reads, takes or
writes enters the decision. -/
theorem preparation_selectWave (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) :
    (Preparation.system owner instanceId revision).selectWave
        (Preparation.supply owner instanceId revision catalogue workers)
        (Preparation.entries owner instanceId revision catalogue) =
      (Preparation.entries owner instanceId revision (catalogue.take workers),
        Preparation.entries owner instanceId revision (catalogue.drop workers)) := by
  have := preparation_selectWaveAux owner instanceId revision catalogue workers catalogue []
    (by simp) (by simp)
  simpa [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWave,
    Preparation.entries] using this

/-- **A preparation wave is not a commit wave.** The native preparation footprint admits tasks
`1` and `2` together on two worker credits; carrying the two rival takers of one token, their
commits have no executable order at the snapshot where both were matched. -/
theorem preparation_wave_not_commit_wave :
    (Preparation.system 7 9 11).StepEnables (Preparation.supply 7 9 11 [1, 2] 2)
        (Preparation.entries 7 9 11 [1, 2]) ∧
      (∀ c ∈ [1, 2].map taskCommit, Enabled OccurrenceCommits.Controls.label {0} c) ∧
      ¬ ∃ l, l.Perm ([1, 2].map taskCommit) ∧ Executable OccurrenceCommits.Controls.label {0} l := by
  refine ⟨Preparation.occurrence_and_shared_read_controls.1, ?_, ?_⟩
  · simpa [taskCommit] using OccurrenceCommits.Controls.takers_enabled
  · simpa [taskCommit] using OccurrenceCommits.Controls.takers_batch_no_order

end Preparation

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication
