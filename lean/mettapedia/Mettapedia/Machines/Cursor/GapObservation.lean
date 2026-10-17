import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Option.Basic
import Mathlib.Data.Finset.Option

/-!
# Gap observations on trie cursors

A space of keys is read through a trie: a key is a path of bytes, and a
cursor at node `q` (a path) sees the child bytes `c` such that some key
extends `q ++ [c]`.  An **absence read** asks that no key lie in the region
below a path `p`.  Its dependency is not a set of keys that were read: it is a
region that must stay empty.

* **A missing edge certifies absence** (`regionEmpty_of_nodeGap`): a gap
  `[lo, hi)` among the child bytes at node `q` empties every region below
  `q ++ c :: rest` for `c` in the gap.
* **Seek returns its own footprint** (`nodeGap_seekChild`): seeking the least
  child byte at least `lo` returns `hi` and certifies the gap `[lo, hi)`.
* **Footprint locality** (`seekChild_eq_of_footprint`): in any other space with
  the same gap and, when `hi` is a byte, the same child `hi`, the seek returns
  the same answer.  Validating a cursor computation therefore needs its
  negative observations as well as its positive ones.
* **Phantoms** (`Controls.phantom`): two spaces that agree on every key a seek
  read positively can disagree on the absence it certified.  An inserted key
  inside the gap is invisible to a footprint of positive reads.
* **Footprint locality for adaptive cursor programs**
  (`SeekProgram.run_eq_of_valid`): a program chooses each seek from the answers
  of the earlier ones.  Its footprint lists every seek with its answer; a
  space in which every recorded gap holds and every recorded child is present
  makes the program take the same seeks, receive the same answers and return
  the same result.  The footprint is valid in the space it was taken from
  (`SeekProgram.valid_self`).  One datatype therefore serves as the read set of
  a transaction, the dependency of a cache entry and the evidence a checker
  revalidates.

These are the negative footprints that serializable absence needs: an
absence decided at a frontier stays decided, and a concurrent commit must
validate the gap, as predicate locks (Eswaran, Gray, Lorie and Traiger) and
node-version validation of range scans (Silo) do for databases.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.GapObservation

universe u

variable {β : Type u}

/-- No key of the space lies in the region below `p`. -/
def RegionEmpty (space : Finset (List β)) (p : List β) : Prop :=
  ∀ key ∈ space, ¬ p <+: key

/-- A gap at node `q`: no child byte in `[lo, hi)`. -/
def NodeGap [Preorder β] (space : Finset (List β)) (q : List β) (lo : β) (hi : WithTop β) :
    Prop :=
  ∀ key ∈ space, ∀ c : β, lo ≤ c → (c : WithTop β) < hi → ¬ (q ++ [c]) <+: key

theorem prefix_of_append_cons {q rest : List β} {c : β} {key : List β}
    (h : q ++ c :: rest <+: key) : q ++ [c] <+: key :=
  List.IsPrefix.trans ⟨rest, by simp⟩ h

/-- **A missing edge certifies absence** below it. -/
theorem regionEmpty_of_nodeGap [Preorder β] {space : Finset (List β)} {q : List β} {lo : β}
    {hi : WithTop β} (gap : NodeGap space q lo hi) {c : β} (above : lo ≤ c)
    (below : (c : WithTop β) < hi) (rest : List β) :
    RegionEmpty space (q ++ c :: rest) :=
  fun key member inRegion => gap key member c above below (prefix_of_append_cons inRegion)

/-- An insertion outside the region preserves absence. -/
theorem regionEmpty_insert {space : Finset (List β)} {p key : List β} [DecidableEq β]
    (empty : RegionEmpty space p) (outside : ¬ p <+: key) :
    RegionEmpty (insert key space) p := by
  intro other member
  rcases Finset.mem_insert.1 member with rfl | old
  · exact outside
  · exact empty other old

/-- An insertion inside the region breaks absence. -/
theorem not_regionEmpty_insert {space : Finset (List β)} {p key : List β} [DecidableEq β]
    (inside : p <+: key) : ¬ RegionEmpty (insert key space) p :=
  fun empty => empty key (Finset.mem_insert_self key space) inside

/-! ## Seeking a child byte -/

section Seek

variable [DecidableEq β]

/-- The byte after the path `q` in `key`, when `q` is a proper prefix. -/
def byteAfter (q key : List β) : Option β :=
  if q <+: key then key[q.length]? else none

theorem byteAfter_eq_some_iff {q key : List β} {c : β} :
    byteAfter q key = some c ↔ q ++ [c] <+: key := by
  unfold byteAfter
  constructor
  · intro h
    split_ifs at h with isPrefix
    obtain ⟨tail, rfl⟩ := isPrefix
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at h
    cases tail with
    | nil => simp at h
    | cons head tail =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨tail, by simp⟩
  · intro h
    have isPrefix : q <+: key := List.IsPrefix.trans ⟨[c], rfl⟩ h
    rw [if_pos isPrefix]
    obtain ⟨tail, rfl⟩ := h
    simp

/-- The child bytes at node `q`. -/
def childBytes (space : Finset (List β)) (q : List β) : Finset β :=
  space.biUnion fun key => (byteAfter q key).toFinset

theorem mem_childBytes {space : Finset (List β)} {q : List β} {c : β} :
    c ∈ childBytes space q ↔ ∃ key ∈ space, q ++ [c] <+: key := by
  simp [childBytes, Option.mem_toFinset, byteAfter_eq_some_iff]

variable [LinearOrder β]

/-- **Seek**: the least child byte at node `q` that is at least `lo`, or `⊤`. -/
def seekChild (space : Finset (List β)) (q : List β) (lo : β) : WithTop β :=
  ((childBytes space q).filter fun c => lo ≤ c).min

/-- **A seek certifies the gap it skipped.** -/
theorem nodeGap_seekChild (space : Finset (List β)) (q : List β) (lo : β) :
    NodeGap space q lo (seekChild space q lo) := by
  intro key member c above below inRegion
  have child : c ∈ (childBytes space q).filter fun c => lo ≤ c :=
    Finset.mem_filter.2 ⟨mem_childBytes.2 ⟨key, member, inRegion⟩, above⟩
  exact (lt_irrefl _) (below.trans_le (Finset.min_le child))

/-- The answer of a seek, when it is a byte, is a child. -/
theorem seekChild_mem {space : Finset (List β)} {q : List β} {lo c : β}
    (found : seekChild space q lo = c) : c ∈ childBytes space q ∧ lo ≤ c := by
  have := Finset.mem_of_min found
  exact Finset.mem_filter.1 this

/-- **Footprint locality of a seek**: the gap and the positive child read
determine its answer in every space. -/
theorem seekChild_eq_of_footprint {space : Finset (List β)} {q : List β} {lo : β}
    {hi : WithTop β} (gap : NodeGap space q lo hi)
    (child : ∀ c : β, hi = c → c ∈ childBytes space q ∧ lo ≤ c) :
    seekChild space q lo = hi := by
  apply le_antisymm
  · cases hi with
    | top => exact le_top
    | coe c =>
        obtain ⟨isChild, above⟩ := child c rfl
        exact Finset.min_le (Finset.mem_filter.2 ⟨isChild, above⟩)
  · cases found : seekChild space q lo with
    | top => exact le_top
    | coe c =>
        obtain ⟨isChild, above⟩ := seekChild_mem found
        obtain ⟨key, member, inRegion⟩ := mem_childBytes.1 isChild
        by_contra notLe
        exact gap key member c above (lt_of_not_ge notLe) inRegion

/-- A seek that lands strictly beyond `c` certifies the absence of every key
below `q ++ c :: rest`. -/
theorem regionEmpty_of_seek {space : Finset (List β)} {q : List β} {c : β}
    (beyond : (c : WithTop β) < seekChild space q c) (rest : List β) :
    RegionEmpty space (q ++ c :: rest) :=
  regionEmpty_of_nodeGap (nodeGap_seekChild space q c) le_rfl beyond rest

/-! ## Adaptive cursor programs -/

/-- A cursor program: seek at a node and continue with the answer, or stop. -/
inductive SeekProgram (β : Type u) (Result : Type*)
  | done (result : Result)
  | seek (node : List β) (lo : β) (next : WithTop β → SeekProgram β Result)

namespace SeekProgram

variable {Result : Type*}

/-- Run a program on a space. -/
def run (space : Finset (List β)) : SeekProgram β Result → Result
  | done result => result
  | seek node lo next => (next (seekChild space node lo)).run space

/-- The seeks a run makes, with their answers. -/
def footprint (space : Finset (List β)) : SeekProgram β Result → List (List β × β × WithTop β)
  | done _ => []
  | seek node lo next =>
      (node, lo, seekChild space node lo) :: (next (seekChild space node lo)).footprint space

/-- A recorded seek is valid in a space when its gap holds there and its answer,
when a byte, is a child there. -/
def ObservationValid (space : Finset (List β)) (observation : List β × β × WithTop β) : Prop :=
  NodeGap space observation.1 observation.2.1 observation.2.2 ∧
    ∀ c : β, observation.2.2 = c → c ∈ childBytes space observation.1 ∧ observation.2.1 ≤ c

/-- **Footprint locality**: a space validating the footprint replays the run. -/
theorem run_eq_of_valid {space other : Finset (List β)} :
    ∀ program : SeekProgram β Result,
      (∀ observation ∈ program.footprint space, ObservationValid other observation) →
        program.run other = program.run space ∧ program.footprint other = program.footprint space
  | done _, _ => ⟨rfl, rfl⟩
  | seek node lo next, valid => by
      have head := valid _ List.mem_cons_self
      have same : seekChild other node lo = seekChild space node lo :=
        seekChild_eq_of_footprint head.1 head.2
      have rest := run_eq_of_valid (next (seekChild space node lo))
        fun observation member => valid observation (List.mem_cons_of_mem _ member)
      simp only [run, footprint, same]
      exact ⟨rest.1, congrArg _ rest.2⟩

/-- **A footprint is valid where it was taken.** -/
theorem valid_self (space : Finset (List β)) :
    ∀ program : SeekProgram β Result,
      ∀ observation ∈ program.footprint space, ObservationValid space observation
  | done _, _, member => by simp [footprint] at member
  | seek node lo next, observation, member => by
      rcases List.mem_cons.1 member with rfl | later
      · exact ⟨nodeGap_seekChild space node lo, fun c found => seekChild_mem found⟩
      · exact valid_self space (next (seekChild space node lo)) observation later

end SeekProgram

end Seek

/-! ## Controls -/

namespace Controls

/-- `{[2]}`: one key. -/
def before : Finset (List ℕ) := {[2]}

/-- `{[1], [2]}`: a key inserted inside the gap. -/
def after : Finset (List ℕ) := {[1], [2]}

theorem childBytes_before : childBytes before [] = {2} := by
  ext c
  simp [mem_childBytes, before]

theorem childBytes_after : childBytes after [] = {1, 2} := by
  ext c
  simp [mem_childBytes, after]

theorem seek_before : seekChild before [] 1 = (2 : ℕ) := by
  simp [seekChild, childBytes_before, Finset.filter_singleton]

/-- **Phantom**: the positive read (the child `2` at the root) agrees in both
spaces, the gap `[1, 2)` certified absence below `[1]` in the first, and the
inserted key `[1]` breaks it without touching any key that was read. -/
theorem phantom :
    (2 ∈ childBytes before [] ∧ 2 ∈ childBytes after []) ∧
      RegionEmpty before [1] ∧ ¬ RegionEmpty after [1] ∧ ¬ NodeGap after [] 1 (2 : ℕ) := by
  refine ⟨⟨by simp [childBytes_before], by simp [childBytes_after]⟩, ?_, ?_, ?_⟩
  · have := regionEmpty_of_nodeGap (nodeGap_seekChild before [] 1) le_rfl
      (by rw [seek_before]; exact WithTop.coe_lt_coe.2 (by decide)) []
    simpa using this
  · intro empty
    exact empty [1] (by simp [after]) (List.prefix_refl _)
  · intro gap
    exact gap [1] (by simp [after]) 1 le_rfl (WithTop.coe_lt_coe.2 (by decide))
      (List.prefix_refl _)

theorem seek_after : seekChild after [] 1 = (1 : ℕ) := by
  simp [seekChild, childBytes_after, Finset.filter_insert, Finset.filter_singleton]

/-- An absence probe: is anything below `[1]`?  It answers `true` (absent) when
the seek from `1` at the root lands beyond `1`. -/
def absenceProbe : SeekProgram ℕ Bool :=
  .seek [] 1 fun answer => .done (decide (((1 : ℕ) : WithTop ℕ) < answer))

/-- **The probe's footprint is what protects its answer**: absent before, present
after, and the footprint taken before is not valid after. -/
theorem probe_controls :
    absenceProbe.run before = true ∧ absenceProbe.run after = false ∧
      ¬ ∀ observation ∈ absenceProbe.footprint before,
        SeekProgram.ObservationValid after observation := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [absenceProbe, SeekProgram.run, seek_before]
    decide
  · simp only [absenceProbe, SeekProgram.run, seek_after]
    decide
  · intro valid
    have := (SeekProgram.run_eq_of_valid absenceProbe valid).1
    simp only [absenceProbe, SeekProgram.run, seek_before, seek_after] at this
    exact absurd this (by decide)

end Controls

end Mettapedia.Machines.Cursor.GapObservation
