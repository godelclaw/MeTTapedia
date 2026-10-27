import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.OnceLinearPrograms

/-!
# Binary sessions as once-linear commit programs

A binary session type is the sequence of directions in which one endpoint uses a channel, and the
other endpoint must use it in the dual sequence. Propositions as sessions reads these types as
linear propositions and their processes as proofs, with communication as cut elimination. This
module gives the interpretation of session-typed processes in the commit basis and proves what it
preserves.

## The encoding

A **configuration** (`Config`) has processes, each a sequence of actions (send or receive on a
channel), and assigns each channel its two endpoints. Each action becomes one commit
(`commitOf`), in continuation-passing form:

* the process's program counter is a linear occurrence `pc p i`, taken by its `i`-th action, which
  makes `pc p (i + 1)`;
* the `k`-th message on channel `c` is the occurrence `msg c k`: the endpoint whose `k`-th action on
  `c` sends makes it, the endpoint whose `k`-th action on `c` receives takes it. The index plays the
  role of the fresh continuation name of the continuation-passing encoding of sessions into the
  linear π-calculus: each name is used once, by one sender and one receiver.

## Session typing is once-linearity

A configuration is **well typed** (`WellTyped`) when each channel has two distinct endpoints among
the processes, every action on a channel is performed by one of its endpoints, and the second
endpoint's sequence of directions on each channel is the dual of the first's.

* **Well-typed configurations encode to once-linear programs** (`encode_onceLinear`): duality is
  exactly what makes every message have one producer and one consumer, and every consumer's message
  supplied. So the theorems of once-linear programs apply: **a well-typed configuration is deadlock
  free exactly when its feeding relation is acyclic, exactly when it has priorities**
  (`encode_deadlockFree_iff_prioritized`).
* **One session between two processes never deadlocks** (`single_session_deadlockFree`): when two
  processes communicate only over one channel with dual types, priorities `2 (i + 1)` for sends and
  `2 (i + 1) + 1` for receives, at the `i`-th action, increase along feeding.

## What typing per channel does not give

* **Crossed channels deadlock** (`Controls.crossedChannels_deadlock`): two processes linked by two channels,
  each well typed, where each first receives on the channel the other sends on later. The tree
  discipline of the cut rule, which forbids two channels between the same pair, excludes it.
* **Two channels in matching order complete** (`Controls.alignedChannels_deadlockFree`): the same pair of
  processes and channels with the actions aligned has priorities. So the tree discipline is
  sufficient, not necessary; priorities are exact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-- A direction of use of a channel. -/
inductive Dir where
  | send
  | recv
  deriving DecidableEq, Repr

/-- The dual direction. -/
def Dir.flip : Dir → Dir
  | .send => .recv
  | .recv => .send

@[simp] theorem Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl

theorem Dir.flip_ne (d : Dir) : d.flip ≠ d := by cases d <;> decide

variable {ι : Type} [DecidableEq ι] {Ch : Type} [DecidableEq Ch]

/-! ## Session positions -/

/-- The directions of a sequence of actions on one channel: its session type at that channel. -/
def dirs (l : List (Ch × Dir)) (c : Ch) : List Dir := (l.filter fun a => decide (a.1 = c)).map Prod.snd

/-- One action with its position in its process and its index in its channel's session. -/
structure Entry (Ch : Type) where
  pos : ℕ
  ch : Ch
  dir : Dir
  idx : ℕ
  deriving DecidableEq

/-- The actions of a sequence, annotated with positions from `i₀` and session indices counted from
`cnt`. -/
def annotate : List (Ch × Dir) → (Ch → ℕ) → ℕ → List (Entry Ch)
  | [], _, _ => []
  | a :: rest, cnt, i₀ => ⟨i₀, a.1, a.2, cnt a.1⟩ :: annotate rest (Function.update cnt a.1 (cnt a.1 + 1)) (i₀ + 1)

theorem pos_mem_annotate : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {e : Entry Ch},
    e ∈ annotate l cnt i₀ → i₀ ≤ e.pos ∧ e.pos < i₀ + l.length
  | [], _, _, _, member => by simp [annotate] at member
  | a :: rest, cnt, i₀, e, member => by
      simp only [annotate, List.mem_cons] at member
      rcases member with rfl | inRest
      · simp
      · have := pos_mem_annotate inRest
        simp only [List.length_cons]
        omega

theorem idx_mem_annotate : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {e : Entry Ch},
    e ∈ annotate l cnt i₀ → cnt e.ch ≤ e.idx
  | [], _, _, _, member => by simp [annotate] at member
  | a :: rest, cnt, i₀, e, member => by
      simp only [annotate, List.mem_cons] at member
      rcases member with rfl | inRest
      · simp
      · have := idx_mem_annotate inRest
        by_cases same : e.ch = a.1
        · rw [same, Function.update_self] at this
          rw [same]
          omega
        · rw [Function.update_of_ne same] at this
          exact this

theorem action_mem_annotate : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {e : Entry Ch},
    e ∈ annotate l cnt i₀ → (e.ch, e.dir) ∈ l
  | [], _, _, _, member => by simp [annotate] at member
  | a :: rest, cnt, i₀, e, member => by
      simp only [annotate, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (action_mem_annotate inRest)

/-- Entries are determined by their position. -/
theorem eq_of_pos_eq : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {e e' : Entry Ch},
    e ∈ annotate l cnt i₀ → e' ∈ annotate l cnt i₀ → e.pos = e'.pos → e = e'
  | [], _, _, _, _, member, _, _ => by simp [annotate] at member
  | a :: rest, cnt, i₀, e, e', member, member', same => by
      simp only [annotate, List.mem_cons] at member member'
      rcases member with rfl | inRest <;> rcases member' with rfl | inRest'
      · rfl
      · have := (pos_mem_annotate inRest').1
        simp only at same
        omega
      · have := (pos_mem_annotate inRest).1
        simp only at same
        omega
      · exact eq_of_pos_eq inRest inRest' same

/-- Entries are determined by their channel and session index. -/
theorem eq_of_idx_eq : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {e e' : Entry Ch},
    e ∈ annotate l cnt i₀ → e' ∈ annotate l cnt i₀ → e.ch = e'.ch → e.idx = e'.idx → e = e'
  | [], _, _, _, _, member, _, _, _ => by simp [annotate] at member
  | a :: rest, cnt, i₀, e, e', member, member', sameCh, sameIdx => by
      simp only [annotate, List.mem_cons] at member member'
      rcases member with rfl | inRest <;> rcases member' with rfl | inRest'
      · rfl
      · have := idx_mem_annotate inRest'
        simp only at sameCh sameIdx
        rw [← sameCh, Function.update_self] at this
        omega
      · have := idx_mem_annotate inRest
        simp only at sameCh sameIdx
        rw [sameCh, Function.update_self] at this
        omega
      · exact eq_of_idx_eq inRest inRest' sameCh sameIdx

/-- Every position of the sequence has an entry. -/
theorem exists_entry_at_pos : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ j : ℕ}, j < l.length →
    ∃ e ∈ annotate l cnt i₀, e.pos = i₀ + j
  | [], _, _, _, lt => by simp at lt
  | a :: rest, cnt, i₀, j, lt => by
      cases j with
      | zero => exact ⟨_, List.mem_cons_self, by simp⟩
      | succ j =>
          obtain ⟨e, member, pos⟩ := exists_entry_at_pos (l := rest)
            (cnt := Function.update cnt a.1 (cnt a.1 + 1)) (i₀ := i₀ + 1) (j := j)
            (by simp only [List.length_cons] at lt; omega)
          exact ⟨e, List.mem_cons_of_mem _ member, by rw [pos]; omega⟩

/-- **Entries on a channel are the session type at that channel.** -/
theorem exists_entry_iff : ∀ {l : List (Ch × Dir)} {cnt : Ch → ℕ} {i₀ : ℕ} {c : Ch} {k : ℕ} {d : Dir},
    (∃ e ∈ annotate l cnt i₀, e.ch = c ∧ e.idx = k ∧ e.dir = d) ↔
      cnt c ≤ k ∧ (dirs l c)[k - cnt c]? = some d
  | [], cnt, i₀, c, k, d => by simp [annotate, dirs]
  | a :: rest, cnt, i₀, c, k, d => by
      have ih := exists_entry_iff (l := rest) (cnt := Function.update cnt a.1 (cnt a.1 + 1))
        (i₀ := i₀ + 1) (c := c) (k := k) (d := d)
      by_cases same : a.1 = c
      · subst same
        have dirsEq : dirs (a :: rest) a.1 = a.2 :: dirs rest a.1 := by simp [dirs]
        rw [Function.update_self] at ih
        simp only [annotate, List.mem_cons, exists_eq_or_imp, dirsEq]
        rw [ih]
        constructor
        · rintro (⟨-, rfl, rfl⟩ | ⟨le, get⟩)
          · simp
          · refine ⟨by omega, ?_⟩
            have : k - cnt a.1 = (k - (cnt a.1 + 1)) + 1 := by omega
            rw [this]
            simpa using get
        · rintro ⟨le, get⟩
          by_cases atHead : k = cnt a.1
          · subst atHead
            left
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at get
            simp [get]
          · right
            refine ⟨by omega, ?_⟩
            have : k - cnt a.1 = (k - (cnt a.1 + 1)) + 1 := by omega
            rw [this] at get
            simpa using get
      · have dirsEq : dirs (a :: rest) c = dirs rest c := by simp [dirs, same]
        rw [Function.update_of_ne (Ne.symm same)] at ih
        simp only [annotate, List.mem_cons, exists_eq_or_imp, dirsEq, same, false_and, false_or]
        exact ih

/-- The entries of a whole sequence. -/
def entries (l : List (Ch × Dir)) : List (Entry Ch) := annotate l (fun _ => 0) 0

theorem exists_entry_iff_dirs {l : List (Ch × Dir)} {c : Ch} {k : ℕ} {d : Dir} :
    (∃ e ∈ entries l, e.ch = c ∧ e.idx = k ∧ e.dir = d) ↔ (dirs l c)[k]? = some d := by
  rw [entries, exists_entry_iff]
  simp

theorem entries_nodup : ∀ (l : List (Ch × Dir)) (cnt : Ch → ℕ) (i₀ : ℕ), (annotate l cnt i₀).Nodup
  | [], _, _ => List.nodup_nil
  | a :: rest, cnt, i₀ => by
      refine List.nodup_cons.mpr ⟨fun member => ?_, entries_nodup rest _ _⟩
      have := (pos_mem_annotate member).1
      simp at this

/-! ## Configurations and their encoding -/

/-- A configuration of session processes. -/
structure Config (ι Ch : Type) where
  procs : List ι
  prog : ι → List (Ch × Dir)
  ends : Ch → ι × ι

/-- **A well-typed configuration**: two distinct endpoints per channel, actions only by
endpoints, and dual session types at the two endpoints. -/
structure WellTyped (C : Config ι Ch) : Prop where
  nodup : C.procs.Nodup
  distinct : ∀ c, (C.ends c).1 ≠ (C.ends c).2
  first_mem : ∀ c, (C.ends c).1 ∈ C.procs
  second_mem : ∀ c, (C.ends c).2 ∈ C.procs
  owned : ∀ p ∈ C.procs, ∀ a ∈ C.prog p, p = (C.ends a.1).1 ∨ p = (C.ends a.1).2
  dual : ∀ c, dirs (C.prog (C.ends c).2) c = (dirs (C.prog (C.ends c).1) c).map Dir.flip

/-- The occurrences of an encoded configuration. -/
inductive SOcc (ι Ch : Type) where
  | pc (p : ι) (i : ℕ)
  | msg (c : Ch) (k : ℕ)
  deriving DecidableEq

/-- **The commit of one action.** -/
def commitOf (p : ι) (e : Entry Ch) : Commit (SOcc ι Ch) Unit :=
  ⟨{.pc p e.pos} ∪ (if e.dir = .recv then {.msg e.ch e.idx} else ∅), ∅,
    {.pc p (e.pos + 1)} ∪ (if e.dir = .send then {.msg e.ch e.idx} else ∅), []⟩

/-- The encoded program: one commit per action of each process. -/
def program (C : Config ι Ch) : List (Commit (SOcc ι Ch) Unit) :=
  C.procs.flatMap fun p => (entries (C.prog p)).map (commitOf p)

/-- The initial store: every process at its first action. -/
def initial (C : Config ι Ch) : Finset (SOcc ι Ch) := (C.procs.map fun p => SOcc.pc p 0).toFinset

theorem mem_program {C : Config ι Ch} {c : Commit (SOcc ι Ch) Unit} :
    c ∈ program C ↔ ∃ p ∈ C.procs, ∃ e ∈ entries (C.prog p), c = commitOf p e := by
  simp only [program, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, inP, e, inE, rfl⟩
    exact ⟨p, inP, e, inE, rfl⟩
  · rintro ⟨p, inP, e, inE, rfl⟩
    exact ⟨p, inP, e, inE, rfl⟩

theorem pc_mem_taken (p : ι) (e : Entry Ch) : SOcc.pc p e.pos ∈ (commitOf p e).taken := by
  simp [commitOf]

theorem mem_taken_iff {p : ι} {e : Entry Ch} {o : SOcc ι Ch} :
    o ∈ (commitOf p e).taken ↔ o = .pc p e.pos ∨ (e.dir = .recv ∧ o = .msg e.ch e.idx) := by
  simp only [commitOf]
  by_cases h : e.dir = .recv <;> simp [h]

theorem mem_made_iff {p : ι} {e : Entry Ch} {o : SOcc ι Ch} :
    o ∈ (commitOf p e).made ↔ o = .pc p (e.pos + 1) ∨ (e.dir = .send ∧ o = .msg e.ch e.idx) := by
  simp only [commitOf]
  by_cases h : e.dir = .send <;> simp [h]

theorem commitOf_inj {C : Config ι Ch} {p p' : ι} {e e' : Entry Ch} (inE : e ∈ entries (C.prog p))
    (inE' : e' ∈ entries (C.prog p')) (same : commitOf p e = commitOf p' e') : p = p' ∧ e = e' := by
  have member : SOcc.pc p e.pos ∈ (commitOf p' e').taken := same ▸ pc_mem_taken p e
  rcases mem_taken_iff.mp member with eq | ⟨-, eq⟩
  · simp only [SOcc.pc.injEq] at eq
    obtain ⟨rfl, posEq⟩ := eq
    exact ⟨rfl, eq_of_pos_eq inE inE' posEq⟩
  · cases eq

section Typed

variable {C : Config ι Ch}

omit [DecidableEq ι] in
/-- Duality, read at one session index. -/
theorem session_dual (typed : WellTyped C) {c : Ch} {k : ℕ} {d : Dir} :
    (dirs (C.prog (C.ends c).2) c)[k]? = some d.flip ↔ (dirs (C.prog (C.ends c).1) c)[k]? = some d := by
  rw [typed.dual, List.getElem?_map]
  cases h : (dirs (C.prog (C.ends c).1) c)[k]? with
  | none => simp
  | some d' =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro flipEq
        have := congrArg Dir.flip flipEq
        simpa using this
      · rintro rfl
        rfl

omit [DecidableEq ι] in
/-- In a well-typed configuration, two different processes that act at one session index of one
channel act in opposite directions. -/
theorem opposite_of_typed (typed : WellTyped C) {p q : ι} (inP : p ∈ C.procs) (inQ : q ∈ C.procs)
    (different : p ≠ q) {e e' : Entry Ch} (inE : e ∈ entries (C.prog p)) (inE' : e' ∈ entries (C.prog q))
    (sameCh : e.ch = e'.ch) (sameIdx : e.idx = e'.idx) : e'.dir = e.dir.flip := by
  have endsP := typed.owned p inP _ (action_mem_annotate inE)
  have endsQ := typed.owned q inQ _ (action_mem_annotate inE')
  rw [← sameCh] at endsQ
  have getP : (dirs (C.prog p) e.ch)[e.idx]? = some e.dir :=
    exists_entry_iff_dirs.mp ⟨e, inE, rfl, rfl, rfl⟩
  have getQ : (dirs (C.prog q) e.ch)[e.idx]? = some e'.dir :=
    exists_entry_iff_dirs.mp ⟨e', inE', sameCh.symm, sameIdx.symm, rfl⟩
  rcases endsP with hp | hp <;> rcases endsQ with hq | hq
  · exact absurd (hp.trans hq.symm) different
  · rw [hp] at getP
    rw [hq] at getQ
    have := (session_dual typed (d := e.dir)).mpr getP
    rw [getQ] at this
    exact Option.some.inj this
  · rw [hp] at getP
    rw [hq] at getQ
    have := (session_dual typed (d := e'.dir)).mpr getQ
    rw [getP] at this
    have flip := congrArg Dir.flip (Option.some.inj this)
    simp only [Dir.flip_flip] at flip
    exact flip.symm
  · exact absurd (hp.trans hq.symm) different

/-- **Session typing is once-linearity**: a well-typed configuration encodes to a once-linear
program. -/
theorem encode_onceLinear (typed : WellTyped C) : OnceLinear (program C) (initial C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinct actions give distinct commits
    rw [program, List.nodup_flatMap]
    refine ⟨fun p _ => (entries_nodup _ _ _).map_on fun e inE e' inE' same =>
        (commitOf_inj inE inE' same).2, ?_⟩
    refine typed.nodup.imp_of_mem fun {p q} _ _ different => ?_
    intro c inP inQ
    obtain ⟨e, inE, rfl⟩ := List.mem_map.mp inP
    obtain ⟨e', inE', same⟩ := List.mem_map.mp inQ
    exact different (commitOf_inj inE' inE same).1.symm
  · intro c member
    obtain ⟨p, -, e, -, rfl⟩ := mem_program.mp member
    rfl
  · intro c inC d inD different
    obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp inC
    obtain ⟨q, inQ, e', inE', rfl⟩ := mem_program.mp inD
    refine Finset.disjoint_left.mpr fun o takenP takenQ => ?_
    rcases mem_taken_iff.mp takenP with eqP | ⟨recvP, eqP⟩ <;>
      rcases mem_taken_iff.mp takenQ with eqQ | ⟨recvQ, eqQ⟩ <;> subst eqP <;>
      simp only [SOcc.pc.injEq, SOcc.msg.injEq, reduceCtorEq] at eqQ
    · obtain ⟨rfl, posEq⟩ := eqQ
      exact different (by rw [eq_of_pos_eq inE inE' posEq])
    · obtain ⟨chEq, idxEq⟩ := eqQ
      by_cases same : p = q
      · subst same
        exact different (by rw [eq_of_idx_eq inE inE' chEq idxEq])
      · have := opposite_of_typed typed inP inQ same inE inE' chEq idxEq
        rw [recvP, recvQ] at this
        exact absurd this (by decide)
  · intro c inC d _
    obtain ⟨p, -, e, -, rfl⟩ := mem_program.mp inC
    simp [commitOf]
  · intro c inC d inD different
    obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp inC
    obtain ⟨q, inQ, e', inE', rfl⟩ := mem_program.mp inD
    refine Finset.disjoint_left.mpr fun o madeP madeQ => ?_
    rcases mem_made_iff.mp madeP with eqP | ⟨sendP, eqP⟩ <;>
      rcases mem_made_iff.mp madeQ with eqQ | ⟨sendQ, eqQ⟩ <;> subst eqP <;>
      simp only [SOcc.pc.injEq, SOcc.msg.injEq, reduceCtorEq] at eqQ
    · obtain ⟨rfl, posEq⟩ := eqQ
      exact different (by rw [eq_of_pos_eq inE inE' (by omega)])
    · obtain ⟨chEq, idxEq⟩ := eqQ
      by_cases same : p = q
      · subst same
        exact different (by rw [eq_of_idx_eq inE inE' chEq idxEq])
      · have := opposite_of_typed typed inP inQ same inE inE' chEq idxEq
        rw [sendP, sendQ] at this
        exact absurd this (by decide)
  · intro c inC
    obtain ⟨p, -, e, -, rfl⟩ := mem_program.mp inC
    refine Finset.disjoint_left.mpr fun o made inInitial => ?_
    simp only [initial, List.mem_toFinset, List.mem_map] at inInitial
    obtain ⟨q, -, rfl⟩ := inInitial
    rcases mem_made_iff.mp made with eq | ⟨-, eq⟩
    · simp only [SOcc.pc.injEq] at eq
      omega
    · cases eq
  · intro c inC o used
    obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp inC
    have takenO : o ∈ (commitOf p e).taken := by simpa [commitOf] using used
    rcases mem_taken_iff.mp takenO with rfl | ⟨recv, rfl⟩
    · cases hpos : e.pos with
      | zero =>
          left
          simp only [initial, List.mem_toFinset, List.mem_map]
          exact ⟨p, inP, rfl⟩
      | succ j =>
          right
          have bound := (pos_mem_annotate inE).2
          obtain ⟨e', inE', pos'⟩ := exists_entry_at_pos (l := C.prog p) (cnt := fun _ => 0)
            (i₀ := 0) (j := j) (by omega)
          refine ⟨commitOf p e', mem_program.mpr ⟨p, inP, e', inE', rfl⟩, ?_⟩
          rw [mem_made_iff]
          left
          rw [pos']
          simp
    · right
      have endsP := typed.owned p inP _ (action_mem_annotate inE)
      have getP : (dirs (C.prog p) e.ch)[e.idx]? = some .recv :=
        exists_entry_iff_dirs.mp ⟨e, inE, rfl, rfl, recv⟩
      -- the other endpoint sends at the same index
      have other : ∃ q ∈ C.procs, (dirs (C.prog q) e.ch)[e.idx]? = some .send := by
        rcases endsP with hp | hp
        · refine ⟨_, typed.second_mem e.ch, ?_⟩
          rw [hp] at getP
          exact (session_dual typed (d := .recv)).mpr getP
        · refine ⟨_, typed.first_mem e.ch, ?_⟩
          rw [hp] at getP
          exact (session_dual typed (d := .send)).mp getP
      obtain ⟨q, inQ, getQ⟩ := other
      obtain ⟨e', inE', chEq, idxEq, sendEq⟩ := exists_entry_iff_dirs.mpr getQ
      refine ⟨commitOf q e', mem_program.mpr ⟨q, inQ, e', inE', rfl⟩, ?_⟩
      rw [mem_made_iff, chEq, idxEq]
      exact Or.inr ⟨sendEq, rfl⟩

/-- **A well-typed configuration is deadlock free exactly when it has priorities.** -/
theorem encode_deadlockFree_iff_prioritized (typed : WellTyped C) :
    DeadlockFree (fun _ => ()) (program C) (initial C) ↔ ∃ prio, Prioritized (program C) prio :=
  deadlockFree_iff_prioritized (encode_onceLinear typed)

end Typed

/-! ## One session between two processes -/

section Single

/-- The position read off a commit: the largest program-counter index it makes. -/
def pcIndex : SOcc ι Ch → ℕ
  | .pc _ i => i
  | .msg _ _ => 0

/-- **The priority of a commit** of a single session: twice the next position, plus one for a
receive. -/
def sessionPrio (c : Commit (SOcc ι Ch) Unit) : ℕ :=
  2 * c.made.sup pcIndex + (if c.taken.card = 2 then 1 else 0)

theorem sup_pcIndex (p : ι) (e : Entry Ch) : (commitOf p e).made.sup pcIndex = e.pos + 1 := by
  unfold commitOf
  split_ifs <;> simp [Finset.sup_insert, pcIndex]

theorem taken_card (p : ι) (e : Entry Ch) :
    (commitOf p e).taken.card = if e.dir = .recv then 2 else 1 := by
  unfold commitOf
  split_ifs with h <;> simp [Finset.card_insert_of_notMem]

theorem sessionPrio_commitOf (p : ι) (e : Entry Ch) :
    sessionPrio (commitOf p e) = 2 * (e.pos + 1) + (if e.dir = .recv then 1 else 0) := by
  unfold sessionPrio
  rw [sup_pcIndex, taken_card]
  split_ifs <;> simp_all

/-- When every action of a sequence is on one channel, the session index is the position. -/
theorem idx_eq_pos_of_single : ∀ {l : List (Ch × Dir)} {c : Ch} {cnt : Ch → ℕ} {i₀ : ℕ},
    (∀ a ∈ l, a.1 = c) → cnt c = i₀ → ∀ e ∈ annotate l cnt i₀, e.ch = c ∧ e.idx = e.pos
  | [], _, _, _, _, _, e, member => by simp [annotate] at member
  | a :: rest, c, cnt, i₀, onC, count, e, member => by
      simp only [annotate, List.mem_cons] at member
      have headC := onC a List.mem_cons_self
      rcases member with rfl | inRest
      · simp [headC, count]
      · refine idx_eq_pos_of_single (fun b inB => onC b (List.mem_cons_of_mem _ inB)) ?_ e inRest
        rw [headC, Function.update_self, count]

/-- **One session between two processes never deadlocks**: a well-typed configuration of two
processes using only one channel has priorities. Typing leaves only the channel's two endpoints with
actions. -/
theorem single_session_deadlockFree {C : Config ι Ch} (typed : WellTyped C) (c : Ch)
    (onC : ∀ p ∈ C.procs, ∀ a ∈ C.prog p, a.1 = c) :
    DeadlockFree (fun _ => ()) (program C) (initial C) := by
  refine (encode_deadlockFree_iff_prioritized typed).mpr ⟨sessionPrio, ?_⟩
  rintro d d' ⟨inD, inD', o, made, used⟩
  obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp inD
  obtain ⟨q, inQ, e', inE', rfl⟩ := mem_program.mp inD'
  have singleP := idx_eq_pos_of_single (onC p inP) rfl e inE
  have singleQ := idx_eq_pos_of_single (onC q inQ) rfl e' inE'
  have takenO : o ∈ (commitOf q e').taken := by simpa [commitOf] using used
  rw [sessionPrio_commitOf, sessionPrio_commitOf]
  rcases mem_made_iff.mp made with rfl | ⟨send, rfl⟩
  · rcases mem_taken_iff.mp takenO with eq | ⟨-, eq⟩
    · simp only [SOcc.pc.injEq] at eq
      obtain ⟨-, posEq⟩ := eq
      rw [← posEq]
      split_ifs <;> omega
    · cases eq
  · rcases mem_taken_iff.mp takenO with eq | ⟨recv, eq⟩
    · cases eq
    · simp only [SOcc.msg.injEq] at eq
      obtain ⟨-, idxEq⟩ := eq
      rw [send, recv]
      simp only [reduceCtorEq, if_false, if_true, add_zero]
      have : e.pos = e'.pos := by rw [← singleP.2, ← singleQ.2, idxEq]
      omega

end Single

/-! ## Controls -/

namespace Controls

/-- Two processes. -/
inductive Proc where
  | P | Q
  deriving DecidableEq, Repr

/-- Two channels. -/
inductive Chan where
  | a | b
  deriving DecidableEq, Repr

open Proc Chan

/-- Both channels join `P` and `Q`. -/
def bothEnds : Chan → Proc × Proc := fun _ => (P, Q)

/-- **Crossed**: `P` receives on `a` then sends on `b`; `Q` receives on `b` then sends on `a`. -/
def crossed : Config Proc Chan where
  procs := [P, Q]
  prog
    | P => [(a, .recv), (b, .send)]
    | Q => [(b, .recv), (a, .send)]
  ends := bothEnds

/-- **Aligned**: `P` sends on `a` then receives on `b`; `Q` receives on `a` then sends on `b`. -/
def aligned : Config Proc Chan where
  procs := [P, Q]
  prog
    | P => [(a, .send), (b, .recv)]
    | Q => [(a, .recv), (b, .send)]
  ends := bothEnds

theorem typed_of (C : Config Proc Chan) (procsEq : C.procs = [P, Q]) (endsEq : C.ends = bothEnds)
    (dualA : dirs (C.prog Q) a = (dirs (C.prog P) a).map Dir.flip)
    (dualB : dirs (C.prog Q) b = (dirs (C.prog P) b).map Dir.flip) : WellTyped C where
  nodup := by rw [procsEq]; decide
  distinct c := by rw [endsEq]; cases c <;> decide
  first_mem c := by rw [endsEq, procsEq]; simp [bothEnds]
  second_mem c := by rw [endsEq, procsEq]; simp [bothEnds]
  owned p inP x _ := by
    rw [endsEq]
    rw [procsEq] at inP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inP
    rcases inP with rfl | rfl <;> simp [bothEnds]
  dual c := by
    rw [endsEq]
    cases c
    · exact dualA
    · exact dualB

theorem crossed_typed : WellTyped crossed := typed_of crossed rfl rfl (by decide) (by decide)

theorem aligned_typed : WellTyped aligned := typed_of aligned rfl rfl (by decide) (by decide)

/-- **Crossed channels deadlock**: nothing is enabled at the start, though neither process has
finished. -/
theorem crossedChannels_deadlock :
    Maximal (fun _ => ()) (program crossed) (initial crossed) [] ∧ (program crossed).length = 4 ∧
      ¬ DeadlockFree (fun _ => ()) (program crossed) (initial crossed) := by
  have maximal : Maximal (fun _ => ()) (program crossed) (initial crossed) [] := by
    intro c member _ enabled
    obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp member
    simp only [crossed, List.mem_cons, List.not_mem_nil, or_false] at inP
    rcases inP with rfl | rfl <;>
      simp only [crossed, entries, annotate, List.mem_cons, List.not_mem_nil, or_false] at inE <;>
      rcases inE with rfl | rfl
    · exact absurd (enabled.taken_subset (mem_taken_iff.mpr (Or.inr ⟨rfl, rfl⟩))) (by decide)
    · exact absurd (enabled.taken_subset (pc_mem_taken _ _)) (by decide)
    · exact absurd (enabled.taken_subset (mem_taken_iff.mpr (Or.inr ⟨rfl, rfl⟩))) (by decide)
    · exact absurd (enabled.taken_subset (pc_mem_taken _ _)) (by decide)
  refine ⟨maximal, by decide, fun free => ?_⟩
  have := free [] ⟨.nil _, List.nodup_nil, by simp⟩ maximal _ (mem_program.mpr ⟨P, by simp [crossed],
    ⟨0, a, .recv, 0⟩, by simp [crossed, entries, annotate], rfl⟩)
  simp at this

/-- The priorities of the aligned configuration: `P`'s send, `Q`'s receive, `Q`'s send, `P`'s
receive. -/
def alignedPrio (c : Commit (SOcc Proc Chan) Unit) : ℕ :=
  if SOcc.pc P 0 ∈ c.taken then 0 else if SOcc.pc Q 0 ∈ c.taken then 1
  else if SOcc.pc Q 1 ∈ c.taken then 2 else 3

/-- **Two channels in matching order complete**: the aligned configuration has priorities. -/
theorem alignedChannels_deadlockFree : DeadlockFree (fun _ => ()) (program aligned) (initial aligned) := by
  refine (encode_deadlockFree_iff_prioritized aligned_typed).mpr ⟨alignedPrio, ?_⟩
  rintro d d' ⟨inD, inD', o, made, used⟩
  obtain ⟨p, inP, e, inE, rfl⟩ := mem_program.mp inD
  obtain ⟨q, inQ, e', inE', rfl⟩ := mem_program.mp inD'
  simp only [aligned, List.mem_cons, List.not_mem_nil, or_false] at inP inQ
  rcases inP with rfl | rfl <;> rcases inQ with rfl | rfl <;>
    simp only [aligned, entries, annotate, List.mem_cons, List.not_mem_nil, or_false] at inE inE' <;>
    rcases inE with rfl | rfl <;> rcases inE' with rfl | rfl <;>
    revert o made used <;> decide

/-- A configuration in which both ends of every channel are process `P`. -/
def selfChannel : Config Proc Chan := ⟨[P, Q], fun _ => [], fun _ => (P, P)⟩

/-- **Well typed, negative**: a channel needs two distinct endpoints. (`crossed_typed` and
`aligned_typed` are positive controls.) -/
theorem selfChannel_not_typed : ¬ WellTyped selfChannel := fun typed => typed.distinct a rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
