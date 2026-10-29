import Mathlib.Logic.Function.Basic

/-!
# Custody under crashes: synced before acknowledged

RFC 5321 §6.1: a receiver that answers `250` to `DATA` accepts responsibility
for the message and must not lose it because the host later crashes. Maildir
(maildir(5), "How a message is delivered") delivers in steps: create
`tmp/time.pid.host`, write the message checking `write`, `fsync` and `close`,
then link it into `new/`; at that instant the message is delivered. fsync(2)
adds what a crash may still undo: `fsync` on a file makes its data and metadata
durable, but not the entry in the directory that holds it, which needs an
`fsync` of the directory.

The model: two directories, `tmp` and `new`, whose entries name inodes, and
inodes with contents. Each entry and each content has a visible value and a
durable one. Writing, creating, linking and unlinking change the visible
values; `fsyncFile` makes an inode's content durable, `fsyncDir` a
directory's entries. A crash keeps, for each entry and each content that is
not durable, either its visible value or its durable one, as an adversary
chooses. A created file exists, empty, in both.

The theorems:
- `acked_survives`: a delivery that syncs the file, links it, and syncs `new`
  before it acknowledges, followed by any operations on other names and inodes,
  recovers the message whole from every crash.
- Mutants: without the directory sync, a crash after the acknowledgement can
  lose the message (`no_dir_sync_loses`); without the file sync, it can leave
  the message empty (`no_file_sync_empties`).

Not modelled: torn writes within a file (content is replaced whole), the
order in which a file system writes unsynced data, NFS, and the 24-hour
timer.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Custody

/-- The two directories of a maildir that delivery uses. -/
inductive Dir
  | tmp
  | new
deriving DecidableEq, Repr

/-- A directory entry. -/
abbrev Key := Dir × String

/-- Inodes. -/
abbrev Inode := Nat

/-- Visible and durable directory entries and contents. -/
structure FS where
  entry : Key → Option Inode
  durEntry : Key → Option Inode
  content : Inode → Option String
  durContent : Inode → Option String

/-- The operations of a delivery. -/
inductive Op
  | create (k : Key) (i : Inode)
  | write (i : Inode) (data : String)
  | fsyncFile (i : Inode)
  | link (src dst : Key)
  | unlink (k : Key)
  | fsyncDir (d : Dir)
  | ack

/-- One operation. -/
def FS.apply (s : FS) : Op → FS
  | .create k i => { s with entry := Function.update s.entry k (some i),
                            content := Function.update s.content i (some ""),
                            durContent := Function.update s.durContent i (some "") }
  | .write i data => { s with content := Function.update s.content i (some data) }
  | .fsyncFile i => { s with durContent := Function.update s.durContent i (s.content i) }
  | .link src dst => { s with entry := Function.update s.entry dst (s.entry src) }
  | .unlink k => { s with entry := Function.update s.entry k none }
  | .fsyncDir d => { s with durEntry := fun k => if k.1 = d then s.entry k else s.durEntry k }
  | .ack => s

/-- Operations in order. -/
def FS.run (s : FS) (ops : List Op) : FS := ops.foldl FS.apply s

/-- What the adversary lets reach the disk of what was not synced. -/
structure Crash where
  keepEntry : Key → Bool
  keepContent : Inode → Bool

/-- The state recovered after a crash. -/
def FS.recover (s : FS) (c : Crash) : Key → Option String := fun k =>
  match (if c.keepEntry k then s.entry k else s.durEntry k) with
  | none => none
  | some i => if c.keepContent i then s.content i else s.durContent i

/-- Delivery of `data` as `n`, with inode `i`, as maildir(5) and fsync(2) have it. -/
def deliver (n : String) (i : Inode) (data : String) : List Op :=
  [.create (.tmp, n) i, .write i data, .fsyncFile i, .link (.tmp, n) (.new, n), .fsyncDir .new, .ack]

/-- An operation that leaves the name `n` in `new` and the inode `i` alone. -/
def Apart (n : String) (i : Inode) : Op → Prop
  | .create k j => k ≠ (.new, n) ∧ j ≠ i
  | .write j _ => j ≠ i
  | .fsyncFile _ => True
  | .link _ dst => dst ≠ (.new, n)
  | .unlink k => k ≠ (.new, n)
  | .fsyncDir _ => True
  | .ack => True

/-- The message is in `new`, visibly and durably, whole. -/
def Synced (s : FS) (n : String) (i : Inode) (data : String) : Prop :=
  s.entry (.new, n) = some i ∧ s.durEntry (.new, n) = some i ∧ s.content i = some data ∧
    s.durContent i = some data

theorem synced_apply {s : FS} {n : String} {i : Inode} {data : String} (h : Synced s n i data)
    {op : Op} (ha : Apart n i op) : Synced (s.apply op) n i data := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases op with
  | create k j =>
    obtain ⟨hk, hj⟩ := ha
    exact ⟨by simp [FS.apply, Function.update_of_ne hk.symm, h1], h2,
      by simp [FS.apply, Function.update_of_ne hj.symm, h3],
      by simp [FS.apply, Function.update_of_ne hj.symm, h4]⟩
  | write j d =>
    exact ⟨h1, h2, by simp [FS.apply, Function.update_of_ne (Ne.symm ha), h3], h4⟩
  | fsyncFile j =>
    refine ⟨h1, h2, h3, ?_⟩
    by_cases hj : i = j
    · subst hj; simp [FS.apply, h3]
    · simp [FS.apply, Function.update_of_ne hj, h4]
  | link src dst => exact ⟨by simp [FS.apply, Function.update_of_ne (Ne.symm ha), h1], h2, h3, h4⟩
  | unlink k => exact ⟨by simp [FS.apply, Function.update_of_ne (Ne.symm ha), h1], h2, h3, h4⟩
  | fsyncDir d =>
    refine ⟨h1, ?_, h3, h4⟩
    by_cases hd : Dir.new = d
    · simp only [FS.apply]; rw [if_pos hd]; exact h1
    · simp only [FS.apply]; rw [if_neg hd]; exact h2
  | ack => exact ⟨h1, h2, h3, h4⟩

theorem synced_run {s : FS} {n : String} {i : Inode} {data : String} (h : Synced s n i data) :
    ∀ (ops : List Op), (∀ op ∈ ops, Apart n i op) → Synced (s.run ops) n i data
  | [], _ => h
  | op :: ops, ha => synced_run (synced_apply h (ha op (by simp))) ops (fun o ho => ha o (by simp [ho]))

/-- Synced mail is recovered whole from every crash. -/
theorem synced_recover {s : FS} {n : String} {i : Inode} {data : String} (h : Synced s n i data)
    (c : Crash) : s.recover c (.new, n) = some data := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FS.recover
  split
  · next he => split at he <;> simp_all
  · next j he =>
    have : j = i := by split at he <;> simp_all
    subst this
    split <;> assumption

theorem deliver_synced (s : FS) (n : String) (i : Inode) (data : String) :
    Synced (s.run (deliver n i data)) n i data := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [FS.run, deliver, FS.apply, Function.update]

/-- **Acknowledged means kept**: after a delivery that syncs file and directory
before it acknowledges, and any operations on other names and inodes, every
crash recovers the message whole. -/
theorem acked_survives (s : FS) (n : String) (i : Inode) (data : String) (later : List Op)
    (ha : ∀ op ∈ later, Apart n i op) (c : Crash) :
    ((s.run (deliver n i data)).run later).recover c (.new, n) = some data :=
  synced_recover (synced_run (deliver_synced s n i data) later ha) c

/-! ## Examples and mutants -/

/-- An empty maildir. -/
def empty : FS := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none⟩

/-- A crash that keeps nothing it was not made to keep. -/
def worst : Crash := ⟨fun _ => false, fun _ => false⟩

/-- A second delivery after the first, then the worst crash: both survive. The
hypotheses of `acked_survives` meet. -/
example : (∀ op ∈ deliver "b" 2 "second", Apart "a" 1 op) ∧
    ((empty.run (deliver "a" 1 "first")).run (deliver "b" 2 "second")).recover worst (.new, "a") =
      some "first" :=
  ⟨by simp [deliver, Apart], acked_survives _ _ _ _ _ (by simp [deliver, Apart]) _⟩

/-- Delivery without the directory sync. -/
def deliverNoDirSync (n : String) (i : Inode) (data : String) : List Op :=
  [.create (.tmp, n) i, .write i data, .fsyncFile i, .link (.tmp, n) (.new, n), .ack]

/-- Delivery without the file sync. -/
def deliverNoFileSync (n : String) (i : Inode) (data : String) : List Op :=
  [.create (.tmp, n) i, .write i data, .link (.tmp, n) (.new, n), .fsyncDir .new, .ack]

/-- Without the directory sync, a crash after the acknowledgement loses the
message. -/
theorem no_dir_sync_loses : (empty.run (deliverNoDirSync "a" 1 "first")).recover worst (.new, "a") = none := by
  simp [FS.run, deliverNoDirSync, FS.apply, FS.recover, worst, empty]

/-- Without the file sync, a crash after the acknowledgement leaves the message
empty; a luckier crash keeps it. -/
theorem no_file_sync_empties :
    (empty.run (deliverNoFileSync "a" 1 "first")).recover worst (.new, "a") = some "" ∧
    (empty.run (deliverNoFileSync "a" 1 "first")).recover ⟨fun _ => false, fun _ => true⟩ (.new, "a") =
      some "first" := by
  constructor <;> simp [FS.run, deliverNoFileSync, FS.apply, FS.recover, worst, empty, Function.update]

end Mettapedia.Protocols.Mail.Custody
