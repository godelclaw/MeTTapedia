import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback

/-!
# A growing store of class-prefixed frame identities

`CeTTaFrameWriteback.NativeFrames` reads the runtime's 32-bit frame identity: a
handle and a generation, spelled in one of four classes chosen by a prefix of
leading one bits, a later class having more handles and fewer generations per
handle. This module models the store that issues those identities
(`frame_identity_acquire`, `cetta_frame_identity_retain`,
`cetta_frame_identity_release`):

* cells are allocated a segment of `2 ^ 16` at a time, when the segment's first
  handle is issued, and handles are issued in order from one;
* a released handle joins the releasing thread's cache of at most 64 free
  handles, or the shared free list; a mint takes from the cache, then from the
  shared list, and only then issues a new handle;
* each mint of a handle raises its generation by one, and releasing the last
  reference of a handle at its class's largest generation retires it;
* a refused acquisition is counted, unless it is quiet.

Main results:
* `stale_forever_g`: an identity whose incarnation has ended is refused by
  retain and release in every later store, across segment growth and reuse;
* `acquired_fresh`, `grown_handle_fresh`: every mint spells an identity never
  issued before, including a handle of a newly allocated segment;
* `class_lifetime`, `class_serves_exactly`: a handle serves its class's
  generations once each and then retires for good;
* `acquire_none_iff`: an acquisition is refused exactly when every handle under
  the limit has been issued and each one is referenced or retired;
* `take?_none_iff_census`, `census_in_use`, `census_headroom`: equivalently,
  when the thread's cache is empty and the census headroom is zero; the
  census's in-use count is the referenced handles plus this thread's cache, and
  its headroom is what the limit leaves after them and the retired handles.

It is the growing counterpart of `MetavariableFrameStore.Shared`, whose
allocator has one generation bound over a fixed array of cells. Each operation
is one atomic transition, and the model follows one thread's cache. It is the sequential protocol: it does not verify the runtime's atomics,
memory orders, or the caches of other threads, and it gives references no
upper bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStoreGrowth

open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames

/-! ## The store -/

/-- Cells per segment. -/
def segmentCells : Nat := 2 ^ 16

/-- The segment holding a handle's cell. -/
def segmentOf (handle : Nat) : Nat := handle / segmentCells

/-- Free handles a thread keeps for itself. -/
def cacheCapacity : Nat := 64

/-- A handle's generation, that of its current or last incarnation (zero before
the first), and its reference count. A cell never written is all zero. -/
structure Cell where
  generation : Nat
  references : Nat
  deriving DecidableEq, Repr

/-- `cells` is read only inside allocated `segments`; `next` is the next handle
to issue and handles `1 .. limit - 1` may be issued; `shared` and `cache` are
the shared free list and one thread's cache, most recent release first. -/
structure Store where
  cells : Nat → Cell
  segments : List Nat
  next : Nat
  limit : Nat
  shared : List Nat
  cache : List Nat
  retired : Nat
  exhaustions : Nat

/-- No handle issued yet. -/
def Store.empty (limit : Nat) : Store :=
  ⟨fun _ => ⟨0, 0⟩, [], 1, limit, [], [], 0, 0⟩

/-- The store at process start: every class may be issued. -/
def Store.initial : Store := Store.empty handleLimit

/-- `cetta_frame_identity_limit_handles count` at process start. -/
def Store.limited (count : Nat) : Store :=
  Store.empty (if handleLimit - 1 ≤ count then handleLimit else count + 1)

/-- `frame_identity_cell`: none for handle zero, a handle beyond every class, or
one whose segment was never allocated. -/
def Store.cell? (s : Store) (handle : Nat) : Option Cell :=
  if 0 < handle ∧ handle < handleLimit ∧ segmentOf handle ∈ s.segments then
    some (s.cells handle)
  else none

/-- The handle an acquisition takes and the store without it: the cache, then
the shared list, then a new handle, whose segment is allocated if it has none.
`room` says whether that allocation succeeds. -/
def Store.pick? (s : Store) (room : Bool) : Option (Store × Nat) :=
  match s.cache with
  | handle :: rest => some ({ s with cache := rest }, handle)
  | [] =>
    match s.shared with
    | handle :: rest => some ({ s with shared := rest }, handle)
    | [] =>
      if s.next < s.limit then
        if segmentOf s.next ∈ s.segments then
          some ({ s with next := s.next + 1 }, s.next)
        else if room then
          some ({ s with next := s.next + 1, segments := segmentOf s.next :: s.segments },
            s.next)
        else none
      else none

/-- A mint: one reference at the handle's next generation. -/
def Store.mint (s : Store) (handle : Nat) : Store × Token :=
  ({ s with
      cells := Function.update s.cells handle ⟨(s.cells handle).generation + 1, 1⟩ },
    ⟨handle, (s.cells handle).generation + 1⟩)

/-- A successful acquisition: the store after it and the minted token, whose
identity is `encode token`. -/
def Store.take? (s : Store) (room : Bool) : Option (Store × Token) :=
  (s.pick? room).map fun picked => picked.1.mint picked.2

/-- `cetta_frame_identity_acquire` when `counted`, else its quiet variant. A
refusal changes only the refusal count, and only when counted. -/
def Store.acquire (s : Store) (room counted : Bool) : Store × Option Token :=
  match s.take? room with
  | some (after, token) => (after, some token)
  | none => ({ s with exhaustions := s.exhaustions + if counted then 1 else 0 }, none)

/-- `cetta_frame_identity_retain`: the identity must spell a live incarnation. -/
def Store.retain? (s : Store) (identity : BitVec 64) : Option Store :=
  (decode? identity).bind fun token =>
    (s.cell? token.handle).bind fun cell =>
      if cell.generation = token.generation ∧ 0 < cell.references then
        some { s with
          cells := Function.update s.cells token.handle ⟨cell.generation, cell.references + 1⟩ }
      else none

/-- After its last release a handle retires at its largest generation; otherwise
it joins the cache, or the shared list when the cache is full. -/
def Store.idle (s : Store) (handle generation : Nat) : Store :=
  if generation = generationMax handle then { s with retired := s.retired + 1 }
  else if s.cache.length < cacheCapacity then { s with cache := handle :: s.cache }
  else { s with shared := handle :: s.shared }

/-- `cetta_frame_identity_release`; none where the runtime aborts. -/
def Store.release? (s : Store) (identity : BitVec 64) : Option Store :=
  (decode? identity).bind fun token =>
    (s.cell? token.handle).bind fun cell =>
      if cell.generation = token.generation ∧ 0 < cell.references then
        let dropped := { s with
          cells := Function.update s.cells token.handle ⟨cell.generation, cell.references - 1⟩ }
        some (if cell.references = 1 then dropped.idle token.handle token.generation
          else dropped)
      else none

/-- A thread's exit returns its cache to the shared list. -/
def Store.returnCache (s : Store) : Store :=
  { s with shared := s.cache.reverse ++ s.shared, cache := [] }

/-- `cetta_frame_identity_test_issue_from`, present only in test builds: new
handles are issued from `handle` on, and the skipped ones are never issued. -/
def Store.issueFrom (s : Store) (handle : Nat) : Store :=
  if s.next < handle ∧ handle < handleLimit then { s with next := handle } else s

/-- One operation of the runtime. -/
inductive Step : Store → Store → Prop
  | acquire (s : Store) (room counted : Bool) : Step s (s.acquire room counted).1
  | retain {s after : Store} {identity : BitVec 64} :
      s.retain? identity = some after → Step s after
  | release {s after : Store} {identity : BitVec 64} :
      s.release? identity = some after → Step s after
  | returnCache (s : Store) : Step s s.returnCache

/-- An operation of a test build, which may also skip handles. -/
inductive TestStep : Store → Store → Prop
  | step {s after : Store} : Step s after → TestStep s after
  | issueFrom (s : Store) (handle : Nat) : TestStep s (s.issueFrom handle)

/-! ## Incarnations -/

/-- The token's generation is one its handle has reached: it has been minted. -/
def Minted (s : Store) (token : Token) : Prop :=
  0 < token.generation ∧ token.generation ≤ (s.cells token.handle).generation

/-- The token is its handle's current incarnation and holds a reference. -/
def Live (s : Store) (token : Token) : Prop :=
  (s.cells token.handle).generation = token.generation ∧
    0 < (s.cells token.handle).references

/-- Minted, and its incarnation is over. -/
def Ended (s : Store) (token : Token) : Prop := Minted s token ∧ ¬ Live s token

/-- Generations spent and no reference held. -/
def Retired (s : Store) (handle : Nat) : Prop :=
  (s.cells handle).generation = generationMax handle ∧ (s.cells handle).references = 0

instance (s : Store) (token : Token) : Decidable (Minted s token) := by
  unfold Minted; infer_instance

instance (s : Store) (token : Token) : Decidable (Live s token) := by
  unfold Live; infer_instance

instance (s : Store) (token : Token) : Decidable (Ended s token) := by
  unfold Ended; infer_instance

instance (s : Store) (handle : Nat) : Decidable (Retired s handle) := by
  unfold Retired; infer_instance


theorem generationMax_ge_two (handle : Nat) : 2 ≤ generationMax handle := by
  unfold generationMax; split_ifs <;> decide

/-! ## Operations as cell updates -/

/-- The three ways an acquisition takes a handle: from the head of the cache or
of the shared list, or by issuing the next handle. Only the last may allocate a
segment, and then only the next handle's. -/
theorem pick?_eq_some {s b : Store} {room : Bool} {handle : Nat}
    (picked : s.pick? room = some (b, handle)) :
    b.cells = s.cells ∧ b.limit = s.limit ∧ b.retired = s.retired ∧
      b.exhaustions = s.exhaustions ∧
      ((s.cache ++ s.shared = handle :: (b.cache ++ b.shared) ∧
          b.cache.length ≤ s.cache.length ∧ b.next = s.next ∧ b.segments = s.segments) ∨
        (s.cache = [] ∧ s.shared = [] ∧ handle = s.next ∧ s.next < s.limit ∧
          b.cache = [] ∧ b.shared = [] ∧ b.next = s.next + 1 ∧
          segmentOf s.next ∈ b.segments ∧ (∀ x ∈ s.segments, x ∈ b.segments) ∧
          (b.segments ≠ s.segments → segmentOf s.next ∉ s.segments))) := by
  unfold Store.pick? at picked
  cases hc : s.cache with
  | cons c cs =>
    simp only [hc, Option.some.injEq, Prod.mk.injEq] at picked
    obtain ⟨rfl, rfl⟩ := picked
    exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨by simp, by simp, rfl, rfl⟩⟩
  | nil =>
    cases hs : s.shared with
    | cons d ds =>
      simp only [hc, hs, Option.some.injEq, Prod.mk.injEq] at picked
      obtain ⟨rfl, rfl⟩ := picked
      exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨by simp, by simp, rfl, rfl⟩⟩
    | nil =>
      simp only [hc, hs] at picked
      split_ifs at picked with hlim hseg hroom
      · simp only [Option.some.injEq, Prod.mk.injEq] at picked
        obtain ⟨rfl, rfl⟩ := picked
        exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl, hlim, rfl, rfl, rfl, hseg,
          fun _ hx => hx, fun h => absurd rfl h⟩⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at picked
        obtain ⟨rfl, rfl⟩ := picked
        exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl, hlim, rfl, rfl, rfl,
          List.mem_cons_self .., fun _ hx => List.mem_cons_of_mem _ hx, fun _ => hseg⟩⟩

/-- A mint raises the taken handle's generation by one and holds one reference;
no other cell changes. -/
theorem take?_eq_some {s after : Store} {room : Bool} {token : Token}
    (taken : s.take? room = some (after, token)) :
    ∃ b, s.pick? room = some (b, token.handle) ∧
      token.generation = (s.cells token.handle).generation + 1 ∧
      after = { b with
        cells := Function.update s.cells token.handle (Cell.mk token.generation 1) } := by
  unfold Store.take? at taken
  obtain ⟨⟨b, handle⟩, picked, minted⟩ := Option.map_eq_some_iff.mp taken
  have cells := (pick?_eq_some picked).1
  simp only [Store.mint, Prod.mk.injEq] at minted
  obtain ⟨rfl, rfl⟩ := minted
  exact ⟨b, picked, by simp [cells], by simp [cells]⟩

theorem take?_cells {s after : Store} {room : Bool} {token : Token}
    (taken : s.take? room = some (after, token)) :
    token.generation = (s.cells token.handle).generation + 1 ∧
      after.cells = Function.update s.cells token.handle (Cell.mk token.generation 1) := by
  obtain ⟨_, _, generation, rfl⟩ := take?_eq_some taken
  exact ⟨generation, rfl⟩

theorem acquire_cells (s : Store) (room counted : Bool) :
    (s.acquire room counted).1.cells = s.cells ∨
      ∃ token, (s.acquire room counted).2 = some token ∧
        s.take? room = some ((s.acquire room counted).1, token) := by
  unfold Store.acquire
  rcases taken : s.take? room with _ | ⟨after, token⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨token, rfl, rfl⟩

private theorem cell?_eq_some {s : Store} {handle : Nat} {cell : Cell}
    (found : s.cell? handle = some cell) :
    0 < handle ∧ handle < handleLimit ∧ segmentOf handle ∈ s.segments ∧
      cell = s.cells handle := by
  unfold Store.cell? at found
  split_ifs at found with inside
  · exact ⟨inside.1, inside.2.1, inside.2.2, (Option.some.inj found).symm⟩

/-- Retain succeeds exactly on a live incarnation in an allocated segment, and
adds one reference. -/
theorem retain?_eq_some {s after : Store} {identity : BitVec 64}
    (retained : s.retain? identity = some after) :
    ∃ token, decode? identity = some token ∧ segmentOf token.handle ∈ s.segments ∧
      Live s token ∧
      after = { s with
        cells := Function.update s.cells token.handle
          (Cell.mk token.generation ((s.cells token.handle).references + 1)) } := by
  unfold Store.retain? at retained
  rcases decoded : decode? identity with _ | token
  · simp [decoded] at retained
  · simp only [decoded, Option.bind_some] at retained
    rcases found : s.cell? token.handle with _ | cell
    · simp [found] at retained
    · simp only [found, Option.bind_some] at retained
      obtain ⟨_, _, segment, rfl⟩ := cell?_eq_some found
      split_ifs at retained with live
      · refine ⟨token, rfl, segment, live, ?_⟩
        rw [← Option.some.inj retained, live.1]

/-- The store after a release removes one reference from a live incarnation. -/
def Store.dropped (s : Store) (token : Token) : Store :=
  { s with
    cells := Function.update s.cells token.handle
      (Cell.mk token.generation ((s.cells token.handle).references - 1)) }

/-- Release succeeds exactly on a live incarnation in an allocated segment. It
removes one reference, and after the last one the handle goes idle. -/
theorem release?_eq_some {s after : Store} {identity : BitVec 64}
    (released : s.release? identity = some after) :
    ∃ token, decode? identity = some token ∧ segmentOf token.handle ∈ s.segments ∧
      Live s token ∧
      after = (if (s.cells token.handle).references = 1 then
        (s.dropped token).idle token.handle token.generation else s.dropped token) := by
  unfold Store.release? at released
  rcases decoded : decode? identity with _ | token
  · simp [decoded] at released
  · simp only [decoded, Option.bind_some] at released
    rcases found : s.cell? token.handle with _ | cell
    · simp [found] at released
    · simp only [found, Option.bind_some] at released
      obtain ⟨_, _, segment, rfl⟩ := cell?_eq_some found
      split_ifs at released with live last
      · refine ⟨token, rfl, segment, live, ?_⟩
        rw [← Option.some.inj released, Store.dropped, live.1, if_pos last]
      · refine ⟨token, rfl, segment, live, ?_⟩
        rw [← Option.some.inj released, Store.dropped, live.1, if_neg last]

theorem release?_frame {s after : Store} {identity : BitVec 64}
    (released : s.release? identity = some after) :
    after.next = s.next ∧ after.limit = s.limit ∧ after.segments = s.segments := by
  obtain ⟨token, _, _, _, rfl⟩ := release?_eq_some released
  unfold Store.idle Store.dropped
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem idle_cells (s : Store) (handle generation : Nat) :
    (s.idle handle generation).cells = s.cells := by
  unfold Store.idle; split_ifs <;> rfl

theorem release?_cells {s after : Store} {identity : BitVec 64}
    (released : s.release? identity = some after) :
    ∃ token, decode? identity = some token ∧ Live s token ∧
      after.cells = Function.update s.cells token.handle
        (Cell.mk token.generation ((s.cells token.handle).references - 1)) := by
  obtain ⟨token, decoded, _, live, rfl⟩ := release?_eq_some released
  refine ⟨token, decoded, live, ?_⟩
  split_ifs <;> simp [idle_cells, Store.dropped]

/-! ## Ended incarnations stay refused -/

/-- A one-cell update that cannot revive `token`: it keeps the token's
generation reached, and makes it current and referenced only if it already was. -/
private theorem ended_of_update {s after : Store} {token : Token} {handle : Nat} {cell : Cell}
    (cells : after.cells = Function.update s.cells handle cell) (ended : Ended s token)
    (keeps : token.handle = handle →
      token.generation ≤ cell.generation ∧
        (cell.generation = token.generation → 0 < cell.references → Live s token)) :
    Ended after token := by
  obtain ⟨⟨positive, reached⟩, notLive⟩ := ended
  by_cases here : token.handle = handle
  · obtain ⟨reach, revive⟩ := keeps here
    refine ⟨⟨positive, ?_⟩, fun live => notLive (revive ?_ ?_)⟩
    · rw [cells, here, Function.update_self]; exact reach
    · have := live.1; rw [cells, here, Function.update_self] at this; exact this
    · have := live.2; rw [cells, here, Function.update_self] at this; exact this
  · refine ⟨⟨positive, ?_⟩, fun live => notLive ?_⟩
    · rw [cells, Function.update_of_ne here]; exact reached
    · unfold Live at live ⊢; rw [cells, Function.update_of_ne here] at live; exact live

/-- An ended incarnation stays ended: generations never decrease, and the only
change to an idle cell at that generation is a mint, which moves past it. -/
theorem Step.ended {s after : Store} {token : Token} (step : Step s after)
    (ended : Ended s token) : Ended after token := by
  cases step with
  | acquire room counted =>
    rcases acquire_cells s room counted with same | ⟨fresh, _, taken⟩
    · refine ended_of_update (handle := 0) (cell := s.cells 0) ?_ ended ?_
      · rw [same, Function.update_eq_self]
      · intro here
        exact ⟨by rw [← here]; exact ended.1.2, fun _ _ => by
          by_contra notLive; exact ended.2 (by
            unfold Live; rw [here]; exact ⟨by assumption, by assumption⟩)⟩
    · obtain ⟨generation, cells⟩ := take?_cells taken
      refine ended_of_update cells ended fun here => ⟨?_, fun same => ?_⟩
      · have := ended.1.2; rw [here] at this; dsimp only; omega
      · have := ended.1.2; rw [here] at this; dsimp only at same; omega
  | retain retained =>
    obtain ⟨other, _, _, live, rfl⟩ := retain?_eq_some retained
    refine ended_of_update rfl ended fun here => ⟨?_, fun same _ => ?_⟩
    · have := ended.1.2; rw [here, live.1] at this; exact this
    · dsimp only at same
      exact ⟨by rw [here, live.1, same], by rw [here]; exact live.2⟩
  | release released =>
    obtain ⟨other, _, live, cells⟩ := release?_cells released
    refine ended_of_update cells ended fun here => ⟨?_, fun same _ => ?_⟩
    · have := ended.1.2; rw [here, live.1] at this; exact this
    · dsimp only at same
      exact ⟨by rw [here, live.1, same], by rw [here]; exact live.2⟩
  | returnCache => exact ended

theorem TestStep.ended {s after : Store} {token : Token} (step : TestStep s after)
    (ended : Ended s token) : Ended after token := by
  cases step with
  | step step => exact step.ended ended
  | issueFrom handle =>
    unfold Store.issueFrom
    split_ifs
    · exact ended
    · exact ended

theorem retain?_live {s after : Store} {identity : BitVec 64} {token : Token}
    (spelled : decode? identity = some token) (retained : s.retain? identity = some after) :
    Live s token := by
  obtain ⟨found, decoded, _, live, _⟩ := retain?_eq_some retained
  rw [spelled] at decoded
  cases Option.some.inj decoded
  exact live

theorem release?_live {s after : Store} {identity : BitVec 64} {token : Token}
    (spelled : decode? identity = some token) (released : s.release? identity = some after) :
    Live s token := by
  obtain ⟨found, decoded, _, live, _⟩ := release?_eq_some released
  rw [spelled] at decoded
  cases Option.some.inj decoded
  exact live

/-- A stale identity, one whose incarnation has ended, is refused by retain and
release in every later store, whatever segments are allocated or handles reused
in between. -/
theorem stale_forever_g {s after : Store} {token : Token} (ended : Ended s token)
    (trace : Relation.ReflTransGen TestStep s after) {identity : BitVec 64}
    (spelled : decode? identity = some token) :
    Ended after token ∧ after.retain? identity = none ∧ after.release? identity = none := by
  have stays : Ended after token := by
    induction trace with
    | refl => exact ended
    | tail _ step ih => exact step.ended ih
  refine ⟨stays, ?_, ?_⟩
  · rcases retained : after.retain? identity with _ | next
    · rfl
    · exact absurd (retain?_live spelled retained) stays.2
  · rcases released : after.release? identity with _ | next
    · rfl
    · exact absurd (release?_live spelled released) stays.2

/-- A strictly older generation of a reached handle has ended. -/
theorem older_generation_ended {s : Store} {token : Token} (positive : 0 < token.generation)
    (older : token.generation < (s.cells token.handle).generation) : Ended s token :=
  ⟨⟨positive, Nat.le_of_lt older⟩, fun live => Nat.ne_of_lt older live.1.symm⟩

/-- Releasing the last reference ends the incarnation. -/
theorem final_release_ends {s after : Store} {identity : BitVec 64} {token : Token}
    (spelled : decode? identity = some token) (last : (s.cells token.handle).references = 1)
    (released : s.release? identity = some after) : Ended after token := by
  obtain ⟨found, decoded, live, cells⟩ := release?_cells released
  rw [spelled] at decoded
  cases Option.some.inj decoded
  have positive := (decoded_representable spelled).2.2.1
  refine ⟨⟨positive, by rw [cells, Function.update_self]⟩, ?_⟩
  unfold Live
  rw [cells, Function.update_self]
  dsimp only
  omega

/-- The last release ends authority for good, across growth and reuse. -/
theorem final_release_never_revives_g {s released after : Store} {identity : BitVec 64}
    {token : Token} (spelled : decode? identity = some token)
    (last : (s.cells token.handle).references = 1)
    (success : s.release? identity = some released)
    (trace : Relation.ReflTransGen TestStep released after) :
    after.retain? identity = none ∧ after.release? identity = none :=
  (stale_forever_g (final_release_ends spelled last success) trace spelled).2


/-! ## The invariant of reachable stores -/

/-- Handles beyond `next` and handle zero were never written; generations stay
within their class; a referenced handle has been minted, and a minted one has
its segment. The free lists hold, without repetition, exactly the minted handles
that are idle below their class's largest generation. -/
structure WellFormed (s : Store) : Prop where
  limit_le : s.limit ≤ handleLimit
  next_pos : 0 < s.next
  next_le : s.next ≤ handleLimit
  zero : s.cells 0 = ⟨0, 0⟩
  fresh : ∀ handle, s.next ≤ handle → s.cells handle = ⟨0, 0⟩
  bounded : ∀ handle, (s.cells handle).generation ≤ generationMax handle
  referenced : ∀ handle, 0 < (s.cells handle).references → 0 < (s.cells handle).generation
  allocated : ∀ handle, 0 < (s.cells handle).generation → segmentOf handle ∈ s.segments
  listed : ∀ handle ∈ s.cache ++ s.shared,
    0 < (s.cells handle).generation ∧ (s.cells handle).generation < generationMax handle ∧
      (s.cells handle).references = 0
  complete : ∀ handle, 0 < (s.cells handle).generation → (s.cells handle).references = 0 →
    (s.cells handle).generation < generationMax handle → handle ∈ s.cache ++ s.shared
  nodup : (s.cache ++ s.shared).Nodup
  cache_le : s.cache.length ≤ cacheCapacity

theorem WellFormed.issued_bounds {s : Store} (valid : WellFormed s) {handle : Nat}
    (issued : 0 < (s.cells handle).generation) : 0 < handle ∧ handle < s.next := by
  constructor
  · rcases Nat.eq_zero_or_pos handle with rfl | positive
    · rw [valid.zero] at issued; exact absurd issued (Nat.lt_irrefl 0)
    · exact positive
  · by_contra late
    rw [valid.fresh handle (Nat.le_of_not_lt late)] at issued
    exact absurd issued (Nat.lt_irrefl 0)

theorem WellFormed.minted_representable {s : Store} (valid : WellFormed s) {token : Token}
    (minted : Minted s token) : Representable token := by
  have issued : 0 < (s.cells token.handle).generation := Nat.lt_of_lt_of_le minted.1 minted.2
  obtain ⟨positive, early⟩ := valid.issued_bounds issued
  exact ⟨positive, Nat.lt_of_lt_of_le early valid.next_le, minted.1,
    Nat.le_trans minted.2 (valid.bounded token.handle)⟩

theorem empty_wellFormed {limit : Nat} (bounded : limit ≤ handleLimit) :
    WellFormed (Store.empty limit) where
  limit_le := bounded
  next_pos := Nat.one_pos
  next_le := by unfold handleLimit; simp [Store.empty]
  zero := rfl
  fresh := fun _ _ => rfl
  bounded := fun _ => Nat.zero_le _
  referenced := fun _ h => absurd h (Nat.lt_irrefl 0)
  allocated := fun _ h => absurd h (Nat.lt_irrefl 0)
  listed := fun _ h => by simp [Store.empty] at h
  complete := fun _ h => absurd h (Nat.lt_irrefl 0)
  nodup := List.nodup_nil
  cache_le := Nat.zero_le _

private theorem update_cases {f : Nat → Cell} {handle : Nat} {cell : Cell}
    (P : Nat → Cell → Prop) (here : P handle cell) (other : ∀ h, h ≠ handle → P h (f h)) :
    ∀ h, P h (Function.update f handle cell h) := by
  intro h
  by_cases same : h = handle
  · subst same; rw [Function.update_self]; exact here
  · rw [Function.update_of_ne same]; exact other h same

/-- Minting a handle taken from a free list keeps the invariant. -/
private theorem mint_reuse_wellFormed {s b : Store} {handle : Nat} (valid : WellFormed s)
    (cells : b.cells = s.cells) (limit : b.limit = s.limit) (next : b.next = s.next)
    (segments : b.segments = s.segments)
    (lists : s.cache ++ s.shared = handle :: (b.cache ++ b.shared))
    (shorter : b.cache.length ≤ s.cache.length) : WellFormed (b.mint handle).1 := by
  have member : handle ∈ s.cache ++ s.shared := by rw [lists]; exact List.mem_cons_self ..
  obtain ⟨issued, below, _⟩ := valid.listed handle member
  obtain ⟨positive, early⟩ := valid.issued_bounds issued
  have nodup := valid.nodup
  rw [lists] at nodup
  obtain ⟨notTail, tailNodup⟩ := List.nodup_cons.mp nodup
  have tail : ∀ h ∈ b.cache ++ b.shared, h ∈ s.cache ++ s.shared ∧ h ≠ handle := by
    intro h member'
    refine ⟨by rw [lists]; exact List.mem_cons_of_mem _ member', ?_⟩
    rintro rfl; exact notTail member'
  simp only [Store.mint, cells]
  refine ⟨by rw [limit]; exact valid.limit_le, by rw [next]; exact valid.next_pos,
    by rw [next]; exact valid.next_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, tailNodup,
    Nat.le_trans shorter valid.cache_le⟩ <;> dsimp only
  · rw [Function.update_of_ne (Nat.ne_of_lt positive)]; exact valid.zero
  · intro h late
    rw [next] at late
    rw [Function.update_of_ne (show h ≠ handle by omega)]; exact valid.fresh h late
  · refine update_cases (fun h cell => cell.generation ≤ generationMax h) ?_ ?_
    · exact below
    · exact fun h _ => valid.bounded h
  · refine update_cases (fun _ cell => 0 < cell.references → 0 < cell.generation) ?_ ?_
    · exact fun _ => Nat.succ_pos _
    · exact fun h _ => valid.referenced h
  · rw [segments]
    refine update_cases (fun h cell => 0 < cell.generation → segmentOf h ∈ s.segments) ?_ ?_
    · exact fun _ => valid.allocated handle issued
    · exact fun h _ => valid.allocated h
  · intro h member'
    obtain ⟨old, distinct⟩ := tail h member'
    rw [Function.update_of_ne distinct]; exact valid.listed h old
  · refine update_cases (fun h cell => 0 < cell.generation → cell.references = 0 →
      cell.generation < generationMax h → h ∈ b.cache ++ b.shared) ?_ ?_
    · intro _ zero; exact absurd zero Nat.one_ne_zero
    · intro h distinct issued' idle' below'
      have old := valid.complete h issued' idle' below'
      rw [lists] at old
      rcases List.mem_cons.mp old with same | rest
      · exact absurd same distinct
      · exact rest

/-- Minting the next handle keeps the invariant. -/
private theorem mint_fresh_wellFormed {s b : Store} (valid : WellFormed s)
    (cells : b.cells = s.cells) (limit : b.limit = s.limit) (next : b.next = s.next + 1)
    (cache : b.cache = s.cache) (shared : b.shared = s.shared)
    (segments : ∀ x ∈ s.segments, x ∈ b.segments) (own : segmentOf s.next ∈ b.segments)
    (room : s.next < s.limit) : WellFormed (b.mint s.next).1 := by
  have untouched := valid.fresh s.next (Nat.le_refl _)
  simp only [Store.mint, cells, untouched]
  refine ⟨by rw [limit]; exact valid.limit_le, by rw [next]; exact Nat.succ_pos _,
    by rw [next]; have := valid.limit_le; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only
  · rw [Function.update_of_ne (Nat.ne_of_lt valid.next_pos)]; exact valid.zero
  · intro h late
    rw [next] at late
    rw [Function.update_of_ne (show h ≠ s.next by omega)]
    exact valid.fresh h (Nat.le_of_succ_le late)
  · refine update_cases (fun h cell => cell.generation ≤ generationMax h) ?_ ?_
    · have := generationMax_ge_two s.next; dsimp only; omega
    · exact fun h _ => valid.bounded h
  · refine update_cases (fun _ cell => 0 < cell.references → 0 < cell.generation) ?_ ?_
    · exact fun _ => Nat.one_pos
    · exact fun h _ => valid.referenced h
  · refine update_cases (fun h cell => 0 < cell.generation → segmentOf h ∈ b.segments) ?_ ?_
    · exact fun _ => own
    · exact fun h _ issued => segments _ (valid.allocated h issued)
  · intro h member
    rw [cache, shared] at member
    obtain ⟨issued, below, idle⟩ := valid.listed h member
    have distinct : h ≠ s.next := Nat.ne_of_lt (valid.issued_bounds issued).2
    rw [Function.update_of_ne distinct]
    exact ⟨issued, below, idle⟩
  · rw [cache, shared]
    refine update_cases (fun h cell => 0 < cell.generation → cell.references = 0 →
      cell.generation < generationMax h → h ∈ s.cache ++ s.shared) ?_ ?_
    · intro _ zero; exact absurd zero Nat.one_ne_zero
    · exact fun h _ => valid.complete h
  · rw [cache, shared]; exact valid.nodup
  · rw [cache]; exact valid.cache_le

theorem take?_wellFormed {s after : Store} {room : Bool} {token : Token}
    (valid : WellFormed s) (taken : s.take? room = some (after, token)) :
    WellFormed after := by
  unfold Store.take? at taken
  obtain ⟨⟨b, handle⟩, picked, minted⟩ := Option.map_eq_some_iff.mp taken
  obtain ⟨cells, limit, _, _, reuse | grow⟩ := pick?_eq_some picked
  · obtain ⟨lists, shorter, next, segments⟩ := reuse
    have := mint_reuse_wellFormed valid cells limit next segments lists shorter
    rw [minted] at this
    exact this
  · obtain ⟨cache, shared, rfl, room, cache', shared', next, own, segments, _⟩ := grow
    have := mint_fresh_wellFormed valid cells limit next (by rw [cache', cache])
      (by rw [shared', shared]) segments own room
    rw [minted] at this
    exact this

theorem acquire_wellFormed {s : Store} (valid : WellFormed s) (room counted : Bool) :
    WellFormed (s.acquire room counted).1 := by
  unfold Store.acquire
  rcases taken : s.take? room with _ | ⟨after, token⟩
  · exact { valid with }
  · exact take?_wellFormed valid taken

theorem retain_wellFormed {s after : Store} {identity : BitVec 64} (valid : WellFormed s)
    (retained : s.retain? identity = some after) : WellFormed after := by
  obtain ⟨token, _, _, live, rfl⟩ := retain?_eq_some retained
  have issued := valid.referenced token.handle live.2
  have unlisted : token.handle ∉ s.cache ++ s.shared := fun member =>
    Nat.ne_of_gt live.2 (valid.listed token.handle member).2.2
  obtain ⟨positive, early⟩ := valid.issued_bounds issued
  refine ⟨valid.limit_le, valid.next_pos, valid.next_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    valid.nodup, valid.cache_le⟩
  · dsimp only; rw [Function.update_of_ne (Nat.ne_of_lt positive)]; exact valid.zero
  · intro h late
    dsimp only at late ⊢
    rw [Function.update_of_ne (show h ≠ token.handle by omega)]; exact valid.fresh h late
  · refine update_cases (fun h cell => cell.generation ≤ generationMax h) ?_ ?_
    · rw [← live.1]; exact valid.bounded token.handle
    · exact fun h _ => valid.bounded h
  · refine update_cases (fun _ cell => 0 < cell.references → 0 < cell.generation) ?_ ?_
    · exact fun _ => by rw [← live.1]; exact issued
    · exact fun h _ => valid.referenced h
  · refine update_cases (fun h cell => 0 < cell.generation → segmentOf h ∈ s.segments) ?_ ?_
    · exact fun _ => valid.allocated token.handle issued
    · exact fun h _ => valid.allocated h
  · intro h member
    have distinct : h ≠ token.handle := by rintro rfl; exact unlisted member
    dsimp only; rw [Function.update_of_ne distinct]; exact valid.listed h member
  · refine update_cases (fun h cell => 0 < cell.generation → cell.references = 0 →
      cell.generation < generationMax h → h ∈ s.cache ++ s.shared) ?_ ?_
    · intro _ zero; exact absurd zero (Nat.succ_ne_zero _)
    · exact fun h _ => valid.complete h

theorem release_wellFormed {s after : Store} {identity : BitVec 64} (valid : WellFormed s)
    (released : s.release? identity = some after) : WellFormed after := by
  obtain ⟨token, decoded, _, live, rfl⟩ := release?_eq_some released
  have representable := decoded_representable decoded
  have issued := valid.referenced token.handle live.2
  have unlisted : token.handle ∉ s.cache ++ s.shared := fun member =>
    Nat.ne_of_gt live.2 (valid.listed token.handle member).2.2
  obtain ⟨positive, early⟩ := valid.issued_bounds issued
  have generation := live.1
  -- the dropped store, before the handle goes idle
  have dropped : WellFormed (s.dropped token) ∨ (s.cells token.handle).references = 1 := by
    by_cases last : (s.cells token.handle).references = 1
    · exact Or.inr last
    · left
      refine ⟨valid.limit_le, valid.next_pos, valid.next_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        valid.nodup, valid.cache_le⟩
      · simp only [Store.dropped]; rw [Function.update_of_ne (Nat.ne_of_lt positive)]
        exact valid.zero
      · intro h late
        simp only [Store.dropped] at late ⊢
        rw [Function.update_of_ne (show h ≠ token.handle by omega)]; exact valid.fresh h late
      · simp only [Store.dropped]
        refine update_cases (fun h cell => cell.generation ≤ generationMax h) ?_ ?_
        · rw [← generation]; exact valid.bounded token.handle
        · exact fun h _ => valid.bounded h
      · simp only [Store.dropped]
        refine update_cases (fun _ cell => 0 < cell.references → 0 < cell.generation) ?_ ?_
        · exact fun _ => by rw [← generation]; exact issued
        · exact fun h _ => valid.referenced h
      · simp only [Store.dropped]
        refine update_cases (fun h cell => 0 < cell.generation → segmentOf h ∈ s.segments) ?_ ?_
        · exact fun _ => valid.allocated token.handle issued
        · exact fun h _ => valid.allocated h
      · intro h member
        have distinct : h ≠ token.handle := by rintro rfl; exact unlisted member
        simp only [Store.dropped]; rw [Function.update_of_ne distinct]
        exact valid.listed h member
      · simp only [Store.dropped]
        refine update_cases (fun h cell => 0 < cell.generation → cell.references = 0 →
          cell.generation < generationMax h → h ∈ s.cache ++ s.shared) ?_ ?_
        · intro _ zero; have := live.2; dsimp only at zero; omega
        · exact fun h _ => valid.complete h
  split_ifs with last
  · -- the last reference: the handle retires or joins a free list
    have common : ∀ (cache shared : List Nat) (retired : Nat),
        (token.handle ∈ cache ++ shared ↔
          token.generation < generationMax token.handle) →
        (∀ h ∈ cache ++ shared, h ≠ token.handle → h ∈ s.cache ++ s.shared) →
        (∀ h ∈ s.cache ++ s.shared, h ∈ cache ++ shared) →
        (cache ++ shared).Nodup → cache.length ≤ cacheCapacity →
        WellFormed { (s.dropped token) with
          cache := cache, shared := shared, retired := retired } := by
      intro cache shared retired present back forth nodup short
      refine ⟨valid.limit_le, valid.next_pos, valid.next_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        nodup, short⟩
      · simp only [Store.dropped]; rw [Function.update_of_ne (Nat.ne_of_lt positive)]
        exact valid.zero
      · intro h late
        simp only [Store.dropped] at late ⊢
        rw [Function.update_of_ne (show h ≠ token.handle by omega)]; exact valid.fresh h late
      · simp only [Store.dropped]
        refine update_cases (fun h cell => cell.generation ≤ generationMax h) ?_ ?_
        · rw [← generation]; exact valid.bounded token.handle
        · exact fun h _ => valid.bounded h
      · simp only [Store.dropped]
        refine update_cases (fun _ cell => 0 < cell.references → 0 < cell.generation) ?_ ?_
        · exact fun _ => by rw [← generation]; exact issued
        · exact fun h _ => valid.referenced h
      · simp only [Store.dropped]
        refine update_cases (fun h cell => 0 < cell.generation → segmentOf h ∈ s.segments) ?_ ?_
        · exact fun _ => valid.allocated token.handle issued
        · exact fun h _ => valid.allocated h
      · intro h member
        simp only [Store.dropped]
        by_cases same : h = token.handle
        · subst same
          rw [Function.update_self]
          exact ⟨representable.2.2.1, present.mp member, by dsimp only; omega⟩
        · rw [Function.update_of_ne same]
          exact valid.listed h (back h member same)
      · simp only [Store.dropped]
        refine update_cases (fun h cell => 0 < cell.generation → cell.references = 0 →
          cell.generation < generationMax h → h ∈ cache ++ shared) ?_ ?_
        · intro _ _ below; exact present.mpr below
        · exact fun h _ issued' idle' below' => forth h (valid.complete h issued' idle' below')
    have notOld : token.handle ∉ s.cache ++ s.shared := unlisted
    unfold Store.idle
    split_ifs with spent roomy
    · have := common s.cache s.shared (s.retired + 1)
        ⟨fun member => absurd member notOld, fun below => absurd spent (Nat.ne_of_lt below)⟩
        (fun h member _ => member) (fun h member => member) valid.nodup valid.cache_le
      exact this
    · have below : token.generation < generationMax token.handle :=
        Nat.lt_of_le_of_ne (by rw [← generation]; exact valid.bounded token.handle) spent
      have := common (token.handle :: s.cache) s.shared s.retired
        ⟨fun _ => below, fun _ => List.mem_cons_self ..⟩
        (fun h member distinct => by
          rcases List.mem_append.mp member with inCache | inShared
          · rcases List.mem_cons.mp inCache with same | rest
            · exact absurd same distinct
            · exact List.mem_append_left _ rest
          · exact List.mem_append_right _ inShared)
        (fun h member => by
          rcases List.mem_append.mp member with inCache | inShared
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ inCache)
          · exact List.mem_append_right _ inShared)
        (by rw [List.cons_append]; exact List.nodup_cons.mpr ⟨notOld, valid.nodup⟩)
        (by simp only [List.length_cons]; simp only [Store.dropped] at roomy; omega)
      exact this
    · have below : token.generation < generationMax token.handle :=
        Nat.lt_of_le_of_ne (by rw [← generation]; exact valid.bounded token.handle) spent
      have := common s.cache (token.handle :: s.shared) s.retired
        ⟨fun _ => below, fun _ => List.mem_append_right _ (List.mem_cons_self ..)⟩
        (fun h member distinct => by
          rcases List.mem_append.mp member with inCache | inShared
          · exact List.mem_append_left _ inCache
          · rcases List.mem_cons.mp inShared with same | rest
            · exact absurd same distinct
            · exact List.mem_append_right _ rest)
        (fun h member => by
          rcases List.mem_append.mp member with inCache | inShared
          · exact List.mem_append_left _ inCache
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ inShared))
        (List.nodup_middle.mpr (List.nodup_cons.mpr ⟨notOld, valid.nodup⟩))
        valid.cache_le
      exact this
  · rcases dropped with dropped | last'
    · exact dropped
    · exact absurd last' last

theorem returnCache_wellFormed {s : Store} (valid : WellFormed s) :
    WellFormed s.returnCache := by
  have same : ∀ h, h ∈ s.returnCache.cache ++ s.returnCache.shared ↔ h ∈ s.cache ++ s.shared := by
    intro h; simp [Store.returnCache, List.mem_append, or_comm]
  refine ⟨valid.limit_le, valid.next_pos, valid.next_le, valid.zero, valid.fresh,
    valid.bounded, valid.referenced, valid.allocated, ?_, ?_, ?_, ?_⟩
  · exact fun h member => valid.listed h ((same h).mp member)
  · exact fun h issued idle below => (same h).mpr (valid.complete h issued idle below)
  · simp only [Store.returnCache, List.nil_append]
    exact ((List.reverse_perm s.cache).append_right s.shared).nodup_iff.mpr valid.nodup
  · simp [Store.returnCache]

theorem issueFrom_wellFormed {s : Store} (valid : WellFormed s) (handle : Nat) :
    WellFormed (s.issueFrom handle) := by
  unfold Store.issueFrom
  split_ifs with skip
  · exact { valid with
      next_pos := by dsimp only; have := valid.next_pos; omega
      next_le := by dsimp only; omega
      fresh := fun h late => valid.fresh h (by dsimp only at late; omega) }
  · exact valid

theorem Step.wellFormed {s after : Store} (step : Step s after) (valid : WellFormed s) :
    WellFormed after := by
  cases step with
  | acquire room counted => exact acquire_wellFormed valid room counted
  | retain retained => exact retain_wellFormed valid retained
  | release released => exact release_wellFormed valid released
  | returnCache => exact returnCache_wellFormed valid

theorem TestStep.wellFormed {s after : Store} (step : TestStep s after) (valid : WellFormed s) :
    WellFormed after := by
  cases step with
  | step step => exact step.wellFormed valid
  | issueFrom handle => exact issueFrom_wellFormed valid handle

/-- Stores reachable from process start, in production or in a test build. -/
inductive Reachable : Store → Prop
  | empty {limit : Nat} : limit ≤ handleLimit → Reachable (Store.empty limit)
  | step {s after : Store} : Reachable s → TestStep s after → Reachable after

theorem Reachable.wellFormed {s : Store} (reach : Reachable s) : WellFormed s := by
  induction reach with
  | empty bounded => exact empty_wellFormed bounded
  | step _ step ih => exact step.wellFormed ih

theorem wellFormed_trace {s after : Store} (valid : WellFormed s)
    (trace : Relation.ReflTransGen TestStep s after) : WellFormed after := by
  induction trace with
  | refl => exact valid
  | tail _ step ih => exact step.wellFormed ih


/-! ## Every mint spells a new identity -/

/-- A taken handle holds no reference and has a generation left in its class,
so the runtime's checks before a mint never abort. -/
theorem take?_available {s after : Store} {room : Bool} {token : Token} (valid : WellFormed s)
    (taken : s.take? room = some (after, token)) :
    (s.cells token.handle).references = 0 ∧
      (s.cells token.handle).generation < generationMax token.handle ∧
      0 < token.handle ∧ token.handle < handleLimit := by
  obtain ⟨b, picked, _, _⟩ := take?_eq_some taken
  obtain ⟨_, _, _, _, reuse | grow⟩ := pick?_eq_some picked
  · have member : token.handle ∈ s.cache ++ s.shared := by
      rw [reuse.1]; exact List.mem_cons_self ..
    obtain ⟨issued, below, idle⟩ := valid.listed token.handle member
    obtain ⟨positive, early⟩ := valid.issued_bounds issued
    exact ⟨idle, below, positive, Nat.lt_of_lt_of_le early valid.next_le⟩
  · obtain ⟨_, _, same, room, _⟩ := grow
    rw [same, valid.fresh s.next (Nat.le_refl _)]
    exact ⟨rfl, Nat.lt_of_lt_of_le (by decide) (generationMax_ge_two s.next), valid.next_pos,
      Nat.lt_of_lt_of_le room valid.limit_le⟩

/-- Every acquisition mints an incarnation not minted before, at a generation
its class allows, and spells an identity different from every one issued
before. -/
theorem acquired_fresh {s after : Store} {room : Bool} {token : Token} (valid : WellFormed s)
    (taken : s.take? room = some (after, token)) :
    Representable token ∧ ¬ Minted s token ∧ Minted after token ∧ Live after token ∧
      (∀ old, Minted s old → Minted after old) ∧
      (∀ old, Minted s old → encode old ≠ encode token) := by
  obtain ⟨generation, cells⟩ := take?_cells taken
  obtain ⟨_, below, positive, inside⟩ := take?_available valid taken
  have representable : Representable token :=
    ⟨positive, inside, by omega, by omega⟩
  have unminted : ¬ Minted s token := fun minted => by have := minted.2; omega
  refine ⟨representable, unminted, ⟨by omega, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [cells, Function.update_self]
  · rw [cells, Function.update_self]
  · rw [cells, Function.update_self]; exact Nat.one_pos
  · intro old minted
    refine ⟨minted.1, ?_⟩
    by_cases here : old.handle = token.handle
    · rw [cells, here, Function.update_self]; have := minted.2; rw [here] at this; dsimp only
      omega
    · rw [cells, Function.update_of_ne here]; exact minted.2
  · intro old minted same
    exact unminted (encode_injective (valid.minted_representable minted) representable same ▸
      minted)

/-- A handle issued for the first time is minted at generation one; no identity
of it was issued before. -/
theorem issued_handle_fresh {s after : Store} {room : Bool} {token : Token}
    (valid : WellFormed s) (taken : s.take? room = some (after, token))
    (issued : after.next ≠ s.next) :
    token = ⟨s.next, 1⟩ ∧ after.next = s.next + 1 ∧
      (∀ generation, ¬ Minted s ⟨s.next, generation⟩) := by
  obtain ⟨b, picked, generation, rfl⟩ := take?_eq_some taken
  obtain ⟨_, _, _, _, reuse | grow⟩ := pick?_eq_some picked
  · exact absurd reuse.2.2.1 issued
  · obtain ⟨_, _, same, _, _, _, next, _⟩ := grow
    have untouched := valid.fresh s.next (Nat.le_refl _)
    refine ⟨?_, next, fun g minted => ?_⟩
    · rw [same, untouched] at generation
      cases token
      dsimp only at same generation ⊢
      rw [same, generation]
    · have bound : g ≤ (s.cells s.next).generation := minted.2
      have positive : 0 < g := minted.1
      rw [untouched] at bound
      exact absurd bound (by dsimp only; omega)

/-- A handle issued from a newly allocated segment spells an identity never
issued before: no handle of that segment had been minted, and the spelling
differs from every identity issued before. -/
theorem grown_handle_fresh {s after : Store} {room : Bool} {token : Token}
    (valid : WellFormed s) (taken : s.take? room = some (after, token))
    (grew : after.segments ≠ s.segments) :
    token = ⟨s.next, 1⟩ ∧ after.next = s.next + 1 ∧ segmentOf s.next ∉ s.segments ∧
      segmentOf token.handle ∈ after.segments ∧
      (∀ old, Minted s old → segmentOf old.handle ≠ segmentOf token.handle) ∧
      (∀ old, Minted s old → encode old ≠ encode token) := by
  obtain ⟨b, picked, generation, rfl⟩ := take?_eq_some taken
  obtain ⟨_, _, _, _, reuse | grow⟩ := pick?_eq_some picked
  · exact absurd reuse.2.2.2 grew
  · obtain ⟨_, _, same, _, _, _, next, own, _, newSegment⟩ := grow
    have notOld := newSegment grew
    have untouched := valid.fresh s.next (Nat.le_refl _)
    have tokenEq : token = ⟨s.next, 1⟩ := by
      rw [same, untouched] at generation
      cases token
      dsimp only at same generation ⊢
      rw [same, generation]
    refine ⟨tokenEq, next, notOld, by rw [same]; exact own, ?_,
      (acquired_fresh valid taken).2.2.2.2.2⟩
    intro old minted segment
    have issued : 0 < (s.cells old.handle).generation := Nat.lt_of_lt_of_le minted.1 minted.2
    have := valid.allocated old.handle issued
    rw [segment, same] at this
    exact notOld this

/-! ## Class lifetimes -/

/-- The class of a handle, as its spelling's prefix records. -/
def handleClass (handle : Nat) : Fin 4 :=
  if handle < classOneFirst then 0
  else if handle < classTwoFirst then 1
  else if handle < classThreeFirst then 2 else 3

/-- The generations a handle of each class serves. -/
def classGenerations : Fin 4 → Nat
  | 0 => 2046
  | 1 => 62
  | 2 => 6
  | 3 => 2

/-- The first handle of each class. -/
def classFirst : Fin 4 → Nat
  | 0 => 1
  | 1 => classOneFirst
  | 2 => classTwoFirst
  | 3 => classThreeFirst

theorem generationMax_eq_class (handle : Nat) :
    generationMax handle = classGenerations (handleClass handle) := by
  unfold generationMax handleClass; split_ifs <;> rfl

theorem classFirst_class (c : Fin 4) : handleClass (classFirst c) = c := by
  fin_cases c <;> decide

theorem classFirst_bounds (c : Fin 4) : 0 < classFirst c ∧ classFirst c < handleLimit := by
  fin_cases c <;> decide

/-- A handle a mint takes is never a retired one. -/
theorem take?_not_retired {s after : Store} {room : Bool} {token : Token} {handle : Nat}
    (valid : WellFormed s) (retired : Retired s handle)
    (taken : s.take? room = some (after, token)) : token.handle ≠ handle := by
  rintro rfl
  have := (take?_available valid taken).2.1
  rw [retired.1] at this
  exact Nat.lt_irrefl _ this

/-- No operation changes a retired handle's cell. -/
theorem TestStep.retired_cell {s after : Store} {handle : Nat} (step : TestStep s after)
    (valid : WellFormed s) (retired : Retired s handle) : after.cells handle = s.cells handle := by
  cases step with
  | step step =>
    cases step with
    | acquire room counted =>
      rcases acquire_cells s room counted with same | ⟨token, _, taken⟩
      · rw [same]
      · rw [(take?_cells taken).2, Function.update_of_ne
          (Ne.symm (take?_not_retired valid retired taken))]
    | retain retained =>
      obtain ⟨token, _, _, live, rfl⟩ := retain?_eq_some retained
      have distinct : handle ≠ token.handle := by
        rintro rfl; have := live.2; rw [retired.2] at this; exact Nat.lt_irrefl 0 this
      exact Function.update_of_ne distinct _ _
    | release released =>
      obtain ⟨token, _, live, cells⟩ := release?_cells released
      have distinct : handle ≠ token.handle := by
        rintro rfl; have := live.2; rw [retired.2] at this; exact Nat.lt_irrefl 0 this
      rw [cells, Function.update_of_ne distinct]
    | returnCache => rfl
  | issueFrom h =>
    unfold Store.issueFrom; split_ifs <;> rfl

/-- Retirement is permanent: a retired handle's cell never changes again, and
no later acquisition takes it. -/
theorem retirement_permanent_g {s after : Store} {handle : Nat} (valid : WellFormed s)
    (retired : Retired s handle) (trace : Relation.ReflTransGen TestStep s after) :
    after.cells handle = s.cells handle ∧ Retired after handle ∧
      ∀ room later token, after.take? room = some (later, token) → token.handle ≠ handle := by
  have kept : WellFormed after ∧ after.cells handle = s.cells handle := by
    induction trace with
    | refl => exact ⟨valid, rfl⟩
    | @tail b c _ step ih =>
      obtain ⟨middle, same⟩ := ih
      have stillRetired : Retired b handle := by unfold Retired; rw [same]; exact retired
      exact ⟨step.wellFormed middle, (step.retired_cell middle stillRetired).trans same⟩
  have stillRetired : Retired after handle := by unfold Retired; rw [kept.2]; exact retired
  exact ⟨kept.2, stillRetired, fun room later token taken =>
    take?_not_retired kept.1 stillRetired taken⟩

/-- A handle of class `c` serves the generations `1 .. classGenerations c`: the
identities issued for it are exactly its generations reached so far, never more
than its class allows; while it is idle below that bound it stays on a free
list, so a later mint can take it; and once its last generation has ended it is
retired, its cell frozen, and never taken again. -/
theorem class_lifetime {s : Store} (valid : WellFormed s) (handle : Nat) :
    (∀ generation, Minted s ⟨handle, generation⟩ ↔
        0 < generation ∧ generation ≤ (s.cells handle).generation) ∧
      (s.cells handle).generation ≤ classGenerations (handleClass handle) ∧
      (0 < (s.cells handle).generation → (s.cells handle).references = 0 →
        (s.cells handle).generation < classGenerations (handleClass handle) →
        handle ∈ s.cache ++ s.shared) ∧
      (Retired s handle ↔ (s.cells handle).generation = classGenerations (handleClass handle) ∧
        (s.cells handle).references = 0) ∧
      (Retired s handle → ∀ after, Relation.ReflTransGen TestStep s after →
        after.cells handle = s.cells handle ∧
          ∀ room later token, after.take? room = some (later, token) → token.handle ≠ handle) := by
  refine ⟨fun _ => Iff.rfl, ?_, ?_, ?_, ?_⟩
  · rw [← generationMax_eq_class]; exact valid.bounded handle
  · rw [← generationMax_eq_class]; exact valid.complete handle
  · unfold Retired; rw [generationMax_eq_class]
  · intro retired after trace
    obtain ⟨same, _, never⟩ := retirement_permanent_g valid retired trace
    exact ⟨same, never⟩

/-! ## A handle's whole lifetime -/

/-- Acquire an identity and release it at once. -/
def Store.cycle (s : Store) : Store :=
  match s.take? true with
  | some (after, token) => (after.release? (encode token)).getD after
  | none => s

theorem cycle_reachable {s : Store} (reach : Reachable s) : Reachable s.cycle := by
  unfold Store.cycle
  rcases taken : s.take? true with _ | ⟨after, token⟩
  · exact reach
  · dsimp only
    have acquired : (s.acquire true true).1 = after := by
      simp [Store.acquire, taken]
    have first : Reachable after := acquired ▸ reach.step (.step (.acquire s true true))
    rcases released : after.release? (encode token) with _ | last
    · exact first
    · exact first.step (.step (.release released))

/-- The shape of a store just before the `n + 1`-st mint of `handle` in a cycle
run: the handle is idle at generation `n`, and the next mint takes it. -/
private structure CycleShape (s : Store) (handle n : Nat) : Prop where
  cell : s.cells handle = ⟨n, 0⟩
  below : n < generationMax handle
  positive : 0 < handle
  inside : handle < handleLimit
  shared : s.shared = []
  source : (n = 0 ∧ s.cache = [] ∧ s.next = handle ∧ handle < s.limit) ∨
    (0 < n ∧ s.cache = [handle] ∧ segmentOf handle ∈ s.segments)

private theorem cycle_step {s : Store} {handle n : Nat} (shape : CycleShape s handle n) :
    (∃ later, s.take? true = some (later, ⟨handle, n + 1⟩)) ∧
      s.cycle.cells handle = ⟨n + 1, 0⟩ ∧ s.cycle.shared = [] ∧
      segmentOf handle ∈ s.cycle.segments ∧
      s.cycle.cache = (if n + 1 = generationMax handle then [] else [handle]) := by
  -- the mint
  have taken : ∃ b, s.pick? true = some (b, handle) ∧ b.cache = [] ∧ b.shared = [] ∧
      segmentOf handle ∈ b.segments ∧ b.cells = s.cells := by
    rcases shape.source with ⟨_, cache, next, room⟩ | ⟨_, cache, segment⟩
    · subst next
      unfold Store.pick?
      rw [cache, shape.shared]
      dsimp only
      rw [if_pos room]
      by_cases allocated : segmentOf s.next ∈ s.segments
      · rw [if_pos allocated]
        exact ⟨_, rfl, rfl, rfl, allocated, rfl⟩
      · rw [if_neg allocated, if_pos rfl]
        exact ⟨_, rfl, rfl, rfl, List.mem_cons_self .., rfl⟩
    · unfold Store.pick?
      rw [cache]
      exact ⟨_, rfl, rfl, shape.shared, segment, rfl⟩
  obtain ⟨b, picked, cache, shared, segment, cells⟩ := taken
  have minted : s.take? true = some ((b.mint handle).1, ⟨handle, n + 1⟩) := by
    simp only [Store.take?, picked, Option.map_some, Store.mint, cells, shape.cell]
  refine ⟨⟨_, minted⟩, ?_⟩
  have representable : Representable ⟨handle, n + 1⟩ :=
    ⟨shape.positive, shape.inside, Nat.succ_pos _, shape.below⟩
  have afterCell : (b.mint handle).1.cells handle = ⟨n + 1, 1⟩ := by
    simp [Store.mint, cells, shape.cell]
  have found : (b.mint handle).1.cell? handle = some ⟨n + 1, 1⟩ := by
    unfold Store.cell?
    rw [if_pos ⟨shape.positive, shape.inside, segment⟩, afterCell]
  have release : (b.mint handle).1.release? (encode ⟨handle, n + 1⟩) =
      some (((b.mint handle).1.dropped ⟨handle, n + 1⟩).idle handle (n + 1)) := by
    unfold Store.release?
    rw [decode_encode representable]
    simp only [Option.bind_some]
    rw [found]
    simp [Store.dropped, afterCell]
  have cycled : s.cycle = ((b.mint handle).1.dropped ⟨handle, n + 1⟩).idle handle (n + 1) := by
    unfold Store.cycle
    rw [minted]
    dsimp only
    rw [release]
    rfl
  have roomy : ((b.mint handle).1.dropped ⟨handle, n + 1⟩).cache.length < cacheCapacity := by
    simp [Store.dropped, Store.mint, cache, cacheCapacity]
  rw [cycled]
  unfold Store.idle
  by_cases spent : n + 1 = generationMax handle
  · rw [if_pos spent, if_pos spent]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Store.dropped, Store.mint, cells, shape.cell, shared, segment, cache]
  · rw [if_neg spent, if_neg spent, if_pos roomy]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Store.dropped, Store.mint, cells, shape.cell, shared, segment, cache]

private theorem cycle_iterate {s : Store} {handle : Nat} (start : CycleShape s handle 0) :
    ∀ n, n < generationMax handle →
      CycleShape (Store.cycle^[n] s) handle n ∧
        ∃ later, (Store.cycle^[n] s).take? true = some (later, ⟨handle, n + 1⟩) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨start, (cycle_step start).1⟩
  | succ n ih =>
    intro bound
    obtain ⟨shape, _⟩ := ih (Nat.lt_of_succ_lt bound)
    obtain ⟨_, cell, shared, segment, cache⟩ := cycle_step shape
    have notSpent : n + 1 ≠ generationMax handle := Nat.ne_of_lt bound
    rw [if_neg notSpent] at cache
    have next : CycleShape (Store.cycle^[n + 1] s) handle (n + 1) := by
      rw [Function.iterate_succ_apply']
      exact ⟨cell, bound, shape.positive, shape.inside, shared,
        Or.inr ⟨Nat.succ_pos _, cache, segment⟩⟩
    exact ⟨next, (cycle_step next).1⟩

/-- The run of a handle's whole lifetime: started at the first handle of class
`c`, repeatedly acquiring an identity and releasing it mints that handle at the
generations `1 .. classGenerations c`, once each, without retiring it; after
the last of them it is retired, and no later acquisition, in any continuation,
takes it. -/
theorem class_serves_exactly (c : Fin 4) :
    Reachable (Store.initial.issueFrom (classFirst c)) ∧
      handleClass (classFirst c) = c ∧
      (∀ n, n < classGenerations c →
        (∃ later, (Store.cycle^[n] (Store.initial.issueFrom (classFirst c))).take? true =
          some (later, ⟨classFirst c, n + 1⟩)) ∧
        ¬ Retired (Store.cycle^[n] (Store.initial.issueFrom (classFirst c))) (classFirst c)) ∧
      Retired (Store.cycle^[classGenerations c] (Store.initial.issueFrom (classFirst c)))
        (classFirst c) ∧
      ∀ after, Relation.ReflTransGen TestStep
          (Store.cycle^[classGenerations c] (Store.initial.issueFrom (classFirst c))) after →
        ∀ room later token, after.take? room = some (later, token) →
          token.handle ≠ classFirst c := by
  have reach : Reachable (Store.initial.issueFrom (classFirst c)) :=
    (Reachable.empty (Nat.le_refl _)).step (.issueFrom _ _)
  have maxEq : generationMax (classFirst c) = classGenerations c := by
    rw [generationMax_eq_class, classFirst_class]
  obtain ⟨positive, inside⟩ := classFirst_bounds c
  have start : CycleShape (Store.initial.issueFrom (classFirst c)) (classFirst c) 0 := by
    have nextEq : (Store.initial.issueFrom (classFirst c)).next = classFirst c := by
      unfold Store.issueFrom
      split_ifs with skip
      · rfl
      · simp only [Store.initial, Store.empty] at skip ⊢
        omega
    refine ⟨?_, by rw [maxEq]; fin_cases c <;> decide, positive, inside, ?_, Or.inl ⟨rfl, ?_,
      nextEq, ?_⟩⟩
    · unfold Store.issueFrom; split_ifs <;> rfl
    · unfold Store.issueFrom; split_ifs <;> rfl
    · unfold Store.issueFrom; split_ifs <;> rfl
    · have : (Store.initial.issueFrom (classFirst c)).limit = handleLimit := by
        unfold Store.issueFrom; split_ifs <;> rfl
      rw [this]; exact inside
  have iterates := cycle_iterate start
  have lastIndex : classGenerations c - 1 < generationMax (classFirst c) := by
    rw [maxEq]; fin_cases c <;> decide
  obtain ⟨lastShape, _⟩ := iterates _ lastIndex
  obtain ⟨_, lastCell, _, _, _⟩ := cycle_step lastShape
  have succEq : classGenerations c - 1 + 1 = classGenerations c := by
    fin_cases c <;> decide
  have finalCell : (Store.cycle^[classGenerations c] (Store.initial.issueFrom (classFirst c))).cells
      (classFirst c) = ⟨classGenerations c, 0⟩ := by
    conv_lhs => rw [← succEq, Function.iterate_succ_apply']
    rw [lastCell, succEq]
  have retired : Retired (Store.cycle^[classGenerations c] (Store.initial.issueFrom (classFirst c)))
      (classFirst c) := by
    unfold Retired; rw [finalCell, maxEq]; exact ⟨rfl, rfl⟩
  have finalReach : ∀ n, Reachable (Store.cycle^[n] (Store.initial.issueFrom (classFirst c))) := by
    intro n
    induction n with
    | zero => exact reach
    | succ n ih => rw [Function.iterate_succ_apply']; exact cycle_reachable ih
  refine ⟨reach, classFirst_class c, ?_, retired, ?_⟩
  · intro n bound
    obtain ⟨shape, mint⟩ := iterates n (by rw [maxEq]; exact bound)
    refine ⟨mint, fun spent => ?_⟩
    have := spent.1
    rw [shape.cell, maxEq] at this
    dsimp only at this
    omega
  · intro after trace room later token taken
    exact (retirement_permanent_g (finalReach _).wellFormed retired trace).2.2 room later token
      taken

/-! ## When an acquisition is refused -/

/-- A refusal: nothing free in this thread's cache or the shared list, and no
new handle can be issued, either past the limit or for want of a segment. -/
theorem take?_none_iff (s : Store) (room : Bool) :
    s.take? room = none ↔ s.cache = [] ∧ s.shared = [] ∧
      (s.limit ≤ s.next ∨ (segmentOf s.next ∉ s.segments ∧ room = false)) := by
  unfold Store.take? Store.pick?
  cases s.cache with
  | cons c cs => simp
  | nil =>
    cases s.shared with
    | cons d ds => simp
    | nil =>
      by_cases below : s.next < s.limit
      · by_cases allocated : segmentOf s.next ∈ s.segments
        · simp [below, allocated]
        · cases room <;> simp [below, allocated]
      · simp [below]; omega

theorem acquire_none_iff_take (s : Store) (room counted : Bool) :
    (s.acquire room counted).2 = none ↔ s.take? room = none := by
  unfold Store.acquire
  rcases s.take? room with _ | ⟨after, token⟩ <;> simp

/-- A refusal changes the store only by counting itself, and only when the
acquisition is counted; a success leaves the count alone. -/
theorem acquire_counts (s : Store) (room counted : Bool) :
    (s.acquire room counted).1.exhaustions =
      s.exhaustions + if (s.acquire room counted).2 = none ∧ counted then 1 else 0 := by
  unfold Store.acquire
  rcases taken : s.take? room with _ | ⟨after, token⟩
  · cases counted <;> simp
  · obtain ⟨b, picked, _, rfl⟩ := take?_eq_some taken
    have := (pick?_eq_some picked).2.2.2.1
    simp [this]

/-- Every handle below `next` has been issued: no test hook skipped any. -/
def Contiguous (s : Store) : Prop :=
  ∀ handle, 0 < handle → handle < s.next → 0 < (s.cells handle).generation

theorem Step.contiguous {s after : Store} (step : Step s after) (valid : WellFormed s)
    (contiguous : Contiguous s) : Contiguous after := by
  cases step with
  | acquire room counted =>
    unfold Store.acquire
    rcases taken : s.take? room with _ | ⟨after, token⟩
    · exact contiguous
    · intro h positive early
      dsimp only
      obtain ⟨b, picked, generation, rfl⟩ := take?_eq_some taken
      obtain ⟨_, _, _, _, reuse | grow⟩ := pick?_eq_some picked
      · dsimp only at early ⊢
        rw [reuse.2.2.1] at early
        by_cases same : h = token.handle
        · rw [same, Function.update_self]; show 0 < token.generation; omega
        · rw [Function.update_of_ne same]; exact contiguous h positive early
      · obtain ⟨_, _, handleEq, _, _, _, next, _⟩ := grow
        dsimp only at early ⊢
        rw [next] at early
        by_cases same : h = token.handle
        · rw [same, Function.update_self]; show 0 < token.generation; omega
        · rw [Function.update_of_ne same]
          exact contiguous h positive (by rw [handleEq] at same; omega)
  | retain retained =>
    obtain ⟨token, _, _, live, rfl⟩ := retain?_eq_some retained
    intro h positive early
    dsimp only at early ⊢
    by_cases same : h = token.handle
    · rw [same, Function.update_self]; dsimp only; rw [← live.1]
      exact valid.referenced token.handle live.2
    · rw [Function.update_of_ne same]; exact contiguous h positive early
  | release released =>
    obtain ⟨token, decoded, live, cells⟩ := release?_cells released
    intro h positive early
    rw [(release?_frame released).1] at early
    rw [cells]
    by_cases same : h = token.handle
    · rw [same, Function.update_self]; dsimp only; rw [← live.1]
      exact valid.referenced token.handle live.2
    · rw [Function.update_of_ne same]; exact contiguous h positive early
  | returnCache => exact contiguous

/-- Stores reachable from process start in a production build. -/
inductive Produced : Store → Prop
  | empty {limit : Nat} : limit ≤ handleLimit → Produced (Store.empty limit)
  | step {s after : Store} : Produced s → Step s after → Produced after

theorem Produced.reachable {s : Store} (produced : Produced s) : Reachable s := by
  induction produced with
  | empty bounded => exact .empty bounded
  | step _ step ih => exact ih.step (.step step)

theorem Produced.contiguous {s : Store} (produced : Produced s) : Contiguous s := by
  induction produced with
  | empty bounded =>
    intro h positive early
    simp only [Store.empty] at early
    omega
  | step before step ih => exact step.contiguous before.reachable.wellFormed ih

/-- An acquisition, with memory for any segment it needs, is refused exactly
when every handle under the limit has been issued and each issued handle is
referenced or retired: none is free. -/
theorem acquire_none_iff {s : Store} (valid : WellFormed s) (contiguous : Contiguous s)
    (counted : Bool) :
    (s.acquire true counted).2 = none ↔
      (∀ handle, 0 < handle → handle < s.limit → 0 < (s.cells handle).generation) ∧
        ∀ handle, 0 < (s.cells handle).generation →
          0 < (s.cells handle).references ∨ Retired s handle := by
  rw [acquire_none_iff_take, take?_none_iff]
  simp only [Bool.true_eq_false, and_false, or_false]
  constructor
  · rintro ⟨cache, shared, limit⟩
    refine ⟨fun h positive below => contiguous h positive (by omega), fun h issued => ?_⟩
    by_cases held : 0 < (s.cells h).references
    · exact Or.inl held
    · right
      have idle : (s.cells h).references = 0 := by omega
      refine ⟨?_, idle⟩
      by_contra spent
      have below : (s.cells h).generation < generationMax h :=
        Nat.lt_of_le_of_ne (valid.bounded h) spent
      have := valid.complete h issued idle below
      rw [cache, shared] at this
      exact absurd this List.not_mem_nil
  · rintro ⟨issued, full⟩
    have noneFree : ∀ h, h ∉ s.cache ++ s.shared := by
      intro h member
      obtain ⟨positive, below, idle⟩ := valid.listed h member
      rcases full h positive with held | retired
      · omega
      · rw [retired.1] at below; exact Nat.lt_irrefl _ below
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun h member =>
        noneFree h (List.mem_append_left _ member),
      List.eq_nil_iff_forall_not_mem.mpr fun h member =>
        noneFree h (List.mem_append_right _ member), ?_⟩
    by_contra early
    have := issued s.next valid.next_pos (by omega)
    rw [valid.fresh s.next (Nat.le_refl _)] at this
    exact Nat.lt_irrefl 0 this


/-! ## The census -/

/-- `CettaFrameIdentityCensus`: the limit, the handles issued, those on the
shared free list, and those retired. -/
structure Census where
  limit : Nat
  issued : Nat
  free : Nat
  retired : Nat
  deriving DecidableEq, Repr

/-- `cetta_frame_identity_census`; the handles issued are counted by the last
one issued. -/
def Store.census (s : Store) : Census := ⟨s.limit, s.next - 1, s.shared.length, s.retired⟩

/-- `cetta_frame_identity_census_in_use`. -/
def Census.inUse (c : Census) : Nat := c.issued - (c.free + c.retired)

/-- `cetta_frame_identity_census_headroom`. -/
def Census.headroom (c : Census) : Nat := (c.limit - 1 - c.issued) + c.free

/-- A mint with memory for its segment is refused exactly when the thread's
cache is empty and the census headroom is zero. -/
theorem take?_none_iff_census {s : Store} (valid : WellFormed s) :
    s.take? true = none ↔ s.cache = [] ∧ s.census.headroom = 0 := by
  rw [take?_none_iff]
  simp only [Store.census, Census.headroom, Bool.true_eq_false, and_false, or_false]
  have := valid.next_pos
  constructor
  · rintro ⟨cache, shared, limit⟩
    refine ⟨cache, ?_⟩
    rw [shared, List.length_nil]
    omega
  · rintro ⟨cache, zero⟩
    have empty : s.shared.length = 0 := by omega
    exact ⟨cache, List.eq_nil_of_length_eq_zero empty, by omega⟩

/-- The retired count is the number of retired handles. -/
def RetiredCounted (s : Store) : Prop :=
  s.retired = ((Finset.range s.next).filter (Retired s)).card

/-- The handles holding a reference. -/
def Store.held (s : Store) : Finset Nat :=
  (Finset.range s.next).filter fun handle => 0 < (s.cells handle).references

private theorem filter_range_congr {n : Nat} {P Q : Nat → Prop} [DecidablePred P]
    [DecidablePred Q] (same : ∀ h, h < n → (P h ↔ Q h)) :
    (Finset.range n).filter P = (Finset.range n).filter Q :=
  Finset.filter_congr fun h member => same h (Finset.mem_range.mp member)

private theorem filter_range_extend {n m : Nat} {P : Nat → Prop} [DecidablePred P]
    (le : n ≤ m) (outside : ∀ h, n ≤ h → h < m → ¬ P h) :
    (Finset.range m).filter P = (Finset.range n).filter P := by
  ext h
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨below, holds⟩
    exact ⟨by by_contra late; exact outside h (by omega) below holds, holds⟩
  · rintro ⟨below, holds⟩
    exact ⟨by omega, holds⟩

private theorem filter_range_insert {n : Nat} {P Q : Nat → Prop} [DecidablePred P]
    [DecidablePred Q] {handle : Nat} (inside : handle < n) (before : ¬ P handle)
    (after : Q handle) (same : ∀ h, h ≠ handle → (P h ↔ Q h)) :
    ((Finset.range n).filter Q).card = ((Finset.range n).filter P).card + 1 := by
  have grown : (Finset.range n).filter Q = insert handle ((Finset.range n).filter P) := by
    ext h
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    by_cases here : h = handle
    · subst here; simp [inside, after]
    · simp [here, same h here]
  rw [grown, Finset.card_insert_of_notMem (by simp [before])]

private theorem retired_update {s : Store} {handle h : Nat} {cell : Cell} (distinct : h ≠ handle) :
    Retired { s with cells := Function.update s.cells handle cell } h ↔ Retired s h := by
  unfold Retired; dsimp only; rw [Function.update_of_ne distinct]

theorem TestStep.retiredCounted {s after : Store} (step : TestStep s after) (valid : WellFormed s)
    (counted : RetiredCounted s) : RetiredCounted after := by
  cases step with
  | step step =>
    cases step with
    | acquire room counted' =>
      unfold Store.acquire
      rcases taken : s.take? room with _ | ⟨after, token⟩
      · exact counted
      · dsimp only
        obtain ⟨_, _, positive, inside⟩ := take?_available valid taken
        have spare := (take?_available valid taken).2.1
        obtain ⟨b, picked, generation, rfl⟩ := take?_eq_some taken
        obtain ⟨_, _, retired, _, reuse | grow⟩ := pick?_eq_some picked
        · unfold RetiredCounted
          dsimp only
          rw [retired, reuse.2.2.1, counted]
          congr 1
          apply filter_range_congr
          intro h _
          by_cases here : h = token.handle
          · subst here
            unfold Retired
            dsimp only
            rw [Function.update_self]
            constructor
            · rintro ⟨spent, _⟩; exact absurd spent (Nat.ne_of_lt spare)
            · rintro ⟨_, zero⟩; exact absurd zero Nat.one_ne_zero
          · exact (retired_update here).symm
        · obtain ⟨_, _, handleEq, _, _, _, next, _⟩ := grow
          unfold RetiredCounted
          dsimp only
          rw [retired, next, counted, filter_range_extend (Nat.le_succ _)]
          · congr 1
            apply filter_range_congr
            intro h below
            have here : h ≠ token.handle := by omega
            exact (retired_update here).symm
          · intro h low high
            have here : h = token.handle := by omega
            subst here
            unfold Retired
            dsimp only
            rw [Function.update_self]
            rintro ⟨_, zero⟩
            exact absurd zero Nat.one_ne_zero
    | retain retained =>
      obtain ⟨token, _, _, live, rfl⟩ := retain?_eq_some retained
      unfold RetiredCounted
      dsimp only
      rw [counted]
      congr 1
      apply filter_range_congr
      intro h _
      by_cases here : h = token.handle
      · subst here
        unfold Retired
        dsimp only
        rw [Function.update_self]
        constructor
        · rintro ⟨_, zero⟩; exact absurd live.2 (by omega)
        · rintro ⟨_, zero⟩; exact absurd zero (Nat.succ_ne_zero _)
      · exact (retired_update here).symm
    | release released =>
      obtain ⟨token, _, _, live, rfl⟩ := release?_eq_some released
      have issued := valid.referenced token.handle live.2
      have early := (valid.issued_bounds issued).2
      have before : ¬ Retired s token.handle := fun retired => by
        have := live.2; rw [retired.2] at this; exact Nat.lt_irrefl 0 this
      split_ifs with last
      · unfold Store.idle
        split_ifs with spent
        · unfold RetiredCounted
          dsimp only [Store.dropped]
          rw [counted]
          symm
          apply filter_range_insert early before
          · unfold Retired
            dsimp only
            rw [Function.update_self]
            exact ⟨spent, by dsimp only; omega⟩
          · intro h here
            exact (retired_update here).symm
        all_goals
          unfold RetiredCounted
          dsimp only [Store.dropped]
          rw [counted]
          congr 1
          apply filter_range_congr
          intro h _
          by_cases here : h = token.handle
          · subst here
            unfold Retired
            dsimp only
            rw [Function.update_self]
            constructor
            · intro retired; exact absurd retired before
            · rintro ⟨same, _⟩; exact absurd same spent
          · exact (retired_update here).symm
      · unfold RetiredCounted
        dsimp only [Store.dropped]
        rw [counted]
        congr 1
        apply filter_range_congr
        intro h _
        by_cases here : h = token.handle
        · subst here
          unfold Retired
          dsimp only
          rw [Function.update_self]
          constructor
          · intro retired; exact absurd retired before
          · rintro ⟨_, zero⟩; have := live.2; dsimp only at zero; omega
        · exact (retired_update here).symm
    | returnCache => exact counted
  | issueFrom handle =>
    unfold Store.issueFrom
    split_ifs with skip
    · unfold RetiredCounted
      dsimp only
      rw [filter_range_extend (Nat.le_of_lt skip.1)]
      · exact counted
      · intro h low _ retired
        unfold Retired at retired
        rw [valid.fresh h low] at retired
        have := generationMax_ge_two h
        dsimp only at retired
        omega
    · exact counted

theorem Reachable.retiredCounted {s : Store} (reach : Reachable s) : RetiredCounted s := by
  induction reach with
  | empty _ => rfl
  | step before step ih => exact step.retiredCounted before.wellFormed ih

/-- Every handle issued is referenced, free in this thread's cache or on the
shared list, or retired, and exactly one of these. -/
theorem census_partition {s : Store} (valid : WellFormed s) (contiguous : Contiguous s)
    (counted : RetiredCounted s) :
    s.next - 1 = s.held.card + s.cache.length + s.shared.length + s.retired := by
  let issued := (Finset.range s.next).filter fun h => 0 < (s.cells h).generation
  have issuedCard : issued.card = s.next - 1 := by
    have : issued = Finset.Ico 1 s.next := by
      ext h
      simp only [issued, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨below, positive⟩
        exact ⟨(valid.issued_bounds positive).1, below⟩
      · rintro ⟨low, below⟩
        exact ⟨below, contiguous h low below⟩
    rw [this, Nat.card_Ico]
  have split₁ := Finset.card_filter_add_card_filter_not (s := issued)
    (fun h => 0 < (s.cells h).references)
  set idle := issued.filter fun h => ¬ 0 < (s.cells h).references with idleDef
  have heldEq : issued.filter (fun h => 0 < (s.cells h).references) = s.held := by
    ext h
    simp only [issued, Store.held, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨below, _⟩, held⟩; exact ⟨below, held⟩
    · rintro ⟨below, held⟩; exact ⟨⟨below, valid.referenced h held⟩, held⟩
  have split₂ := Finset.card_filter_add_card_filter_not (s := idle)
    (fun h => (s.cells h).generation < generationMax h)
  have freeEq : idle.filter (fun h => (s.cells h).generation < generationMax h) =
      (s.cache ++ s.shared).toFinset := by
    ext h
    simp only [idle, issued, Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    constructor
    · rintro ⟨⟨⟨_, positive⟩, unheld⟩, below⟩
      exact valid.complete h positive (by omega) below
    · intro member
      obtain ⟨positive, below, zero⟩ := valid.listed h member
      exact ⟨⟨⟨(valid.issued_bounds positive).2, positive⟩, by omega⟩, below⟩
  have retiredEq : idle.filter (fun h => ¬ (s.cells h).generation < generationMax h) =
      (Finset.range s.next).filter (Retired s) := by
    ext h
    simp only [idle, issued, Finset.mem_filter, Finset.mem_range, Retired]
    constructor
    · rintro ⟨⟨⟨below, _⟩, unheld⟩, spent⟩
      exact ⟨below, by have := valid.bounded h; omega, by omega⟩
    · rintro ⟨below, spent, zero⟩
      have := generationMax_ge_two h
      exact ⟨⟨⟨below, by omega⟩, by omega⟩, by omega⟩
  have freeCard : (s.cache ++ s.shared).toFinset.card = s.cache.length + s.shared.length := by
    rw [List.toFinset_card_of_nodup valid.nodup, List.length_append]
  rw [heldEq] at split₁
  rw [freeEq, retiredEq, freeCard, ← counted] at split₂
  omega

/-- The census's handles in use are exactly the referenced handles and this
thread's cache. -/
theorem census_in_use {s : Store} (valid : WellFormed s) (contiguous : Contiguous s)
    (counted : RetiredCounted s) : s.census.inUse = s.held.card + s.cache.length := by
  have := census_partition valid contiguous counted
  simp only [Store.census, Census.inUse]
  omega

/-- With no handle issued beyond the limit, the census headroom is what the limit
leaves after the handles in use and the retired ones. -/
theorem census_headroom {s : Store} (valid : WellFormed s) (contiguous : Contiguous s)
    (counted : RetiredCounted s) (within : s.next ≤ s.limit) :
    s.census.headroom = s.limit - 1 - (s.census.inUse + s.census.retired) := by
  have partition := census_partition valid contiguous counted
  have := valid.next_pos
  simp only [Store.census, Census.headroom, Census.inUse]
  omega

/-! ## Controls -/

namespace Controls

/-- The store after one successful acquisition, keeping its identity live. -/
def afterMint (s : Store) : Store := ((s.take? true).map Prod.fst).getD s

/-- The first mint at process start is handle one at generation one, spelled
`0x00100001`. -/
theorem first_mint :
    (Store.initial.take? true).map Prod.snd = some ⟨1, 1⟩ ∧
      encode ⟨1, 1⟩ = 0x00100001 := by decide

/-- A released handle is reused from the cache at its next generation. -/
theorem reuse_raises_generation :
    Store.initial.cycle.cache = [1] ∧
      (Store.initial.cycle.take? true).map Prod.snd = some ⟨1, 2⟩ := by decide

/-- After reuse the old spelling is refused and the new one accepted. -/
theorem stale_spelling_refused :
    ((afterMint Store.initial.cycle).retain? (encode ⟨1, 1⟩)).isNone = true ∧
      ((afterMint Store.initial.cycle).release? (encode ⟨1, 1⟩)).isNone = true ∧
      ((afterMint Store.initial.cycle).retain? (encode ⟨1, 2⟩)).isSome = true := by decide

/-- The handle after a segment boundary allocates a new segment. Without memory
for it, the acquisition is refused although handles remain under the limit. -/
theorem growth_allocates_segment :
    (afterMint (Store.initial.issueFrom (segmentCells - 1))).segments = [0] ∧
      ((afterMint (Store.initial.issueFrom (segmentCells - 1))).take? true).map Prod.snd =
        some ⟨segmentCells, 1⟩ ∧
      ((afterMint (Store.initial.issueFrom (segmentCells - 1))).take? true).map
        (fun taken => taken.1.segments) = some [1, 0] ∧
      ((afterMint (Store.initial.issueFrom (segmentCells - 1))).take? false).isNone = true := by
  decide

/-- A class-three handle serves two generations, then retires; the next mint
takes another handle. -/
theorem class_three_retires :
    ((Store.initial.issueFrom classThreeFirst).take? true).map Prod.snd =
        some ⟨classThreeFirst, 1⟩ ∧
      ((Store.initial.issueFrom classThreeFirst).cycle.take? true).map Prod.snd =
        some ⟨classThreeFirst, 2⟩ ∧
      Retired (Store.initial.issueFrom classThreeFirst).cycle.cycle classThreeFirst ∧
      (Store.initial.issueFrom classThreeFirst).cycle.cycle.retired = 1 ∧
      ((Store.initial.issueFrom classThreeFirst).cycle.cycle.take? true).map Prod.snd =
        some ⟨classThreeFirst + 1, 1⟩ := by decide

/-- With one handle allowed and held, an acquisition is refused; a counted
refusal is recorded, a quiet one is not. -/
theorem exhaustion_counted_or_quiet :
    ((afterMint (Store.limited 1)).acquire true true).2 = none ∧
      ((afterMint (Store.limited 1)).acquire true true).1.exhaustions = 1 ∧
      ((afterMint (Store.limited 1)).acquire true false).1.exhaustions = 0 := by decide

/-- The contiguity premise of `acquire_none_iff` is needed: after a test build
skips handles one and two, an acquisition is refused although handle one, under
the limit, was never issued. -/
theorem skipped_handles_refuse_unissued :
    ((afterMint ((Store.limited 3).issueFrom 3)).acquire true true).2 = none ∧
      ((afterMint ((Store.limited 3).issueFrom 3)).cells 1).generation = 0 ∧
      1 < (afterMint ((Store.limited 3).issueFrom 3)).limit ∧
      ¬ Contiguous (afterMint ((Store.limited 3).issueFrom 3)) := by
  refine ⟨by decide, by decide, by decide, fun contiguous => ?_⟩
  have := contiguous 1 (by decide) (by decide)
  revert this
  decide

/-- A store outside the invariant: handle one waits in the cache at generation
2063, beyond its class's 2046, while handle `2 ^ 20 + 1` is live. -/
def overrun : Store :=
  { Store.initial with
    cells := Function.update (Function.update (fun _ => ⟨0, 0⟩) 1 ⟨2063, 0⟩)
      (classOneFirst + 1) ⟨1, 1⟩
    cache := [1]
    next := classOneFirst + 2
    segments := [16, 0] }

/-- The generation bound is what keeps spellings apart: outside it, a mint of
handle one at generation 2064 spells exactly the live class-one identity of
handle `2 ^ 20 + 1`. -/
theorem unbounded_generation_aliases :
    ¬ WellFormed overrun ∧
      (overrun.take? true).map Prod.snd = some ⟨1, 2064⟩ ∧
      Live overrun ⟨classOneFirst + 1, 1⟩ ∧
      encode ⟨1, 2064⟩ = encode ⟨classOneFirst + 1, 1⟩ := by
  refine ⟨fun valid => ?_, by decide, by decide, by decide⟩
  have := valid.bounded 1
  revert this
  decide

end Controls


end Mettapedia.Languages.MeTTa.MetavariableFrameStoreGrowth
