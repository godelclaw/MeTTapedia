import Mettapedia.Machines.ArenaHeldResources
import Mettapedia.Languages.MeTTa.MetavariableFrameStoreGrowth

/-!
# Reclaiming the frame identities of dead structure

A node that refers to a frame identity holds it in the arena that allocated the
node (`ArenaHeldResources`), and each hold is one reference of the identity in
the frame store (`MetavariableFrameStoreGrowth`). A copying collection copies
the nodes it can reach into a fresh arena and frees the arenas it collected; an
identity left with no hold is released, and the runtime releases its last
reference.

* `collect_safe`: a collection releases no identity that a reachable node
  refers to: each stays held, by the copy, and unreleased; whatever the
  collection releases, no reachable node refers to.
* `collect_reclaims`: after a collection of every generation, the only holds
  left are those of reachable nodes, and every candidate none of them refers to
  is released.
* `fresh_after_collect`: releasing an identity once per reference ends its
  incarnation; the store then never accepts it again, and reissues its handle
  only at a higher generation.

The two models share the discipline that each hold is one reference; this
module proves each side, not that the runtime's counts follow the holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameReclamation

open Mettapedia.Machines.ArenaHeldResources
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)
open Mettapedia.Languages.MeTTa.MetavariableFrameStoreGrowth
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames
  (decode? decoded_representable encode)

variable {ArenaId : Type} [DecidableEq ArenaId]

/-! ## A copying collection -/

/-- Copy the reachable nodes into `destination`. -/
def copyAll (s : State ArenaId Token) (destination : ArenaId) (nodes : List (List Token)) :
    State ArenaId Token :=
  nodes.foldl (fun current node => alloc current destination node) s

/-- Free every collected arena, releasing the candidates left without a hold. -/
noncomputable def freeAll (s : State ArenaId Token) (collected : List ArenaId)
    (candidates : Finset Token) : State ArenaId Token :=
  collected.foldl (fun current arena => reset current arena 0 candidates) s

/-- Copy what is reachable, then free the collected arenas. -/
noncomputable def collect (s : State ArenaId Token) (destination : ArenaId)
    (reachable : List (List Token)) (collected : List ArenaId) (candidates : Finset Token) :
    State ArenaId Token :=
  freeAll (copyAll s destination reachable) collected candidates

theorem copyAll_arenas (s : State ArenaId Token) (destination : ArenaId)
    (nodes : List (List Token)) (arena : ArenaId) :
    (copyAll s destination nodes).arenas arena =
      if arena = destination then s.arenas destination ++ nodes else s.arenas arena := by
  induction nodes generalizing s with
  | nil => split_ifs with same <;> simp [copyAll, same]
  | cons node rest ih =>
    simp only [copyAll, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases same : arena = destination
    · subst same; simp [alloc]
    · simp [alloc, same]

theorem copyAll_released (s : State ArenaId Token) (destination : ArenaId)
    (nodes : List (List Token)) : (copyAll s destination nodes).released = s.released := by
  induction nodes generalizing s with
  | nil => rfl
  | cons node rest ih =>
    simp only [copyAll, List.foldl_cons] at ih ⊢
    rw [ih]
    rfl

theorem copyAll_inv {s : State ArenaId Token} (inv : Inv s) (destination : ArenaId)
    {nodes : List (List Token)} (unreleased : ∀ node ∈ nodes, ∀ r ∈ node, r ∉ s.released) :
    Inv (copyAll s destination nodes) := by
  induction nodes generalizing s with
  | nil => exact inv
  | cons node rest ih =>
    simp only [copyAll, List.foldl_cons] at ih ⊢
    apply ih (inv_alloc inv destination node (unreleased node (List.mem_cons_self ..)))
    intro other member r refers
    exact unreleased other (List.mem_cons_of_mem _ member) r refers

theorem freeAll_arenas (s : State ArenaId Token) (collected : List ArenaId)
    (candidates : Finset Token) (arena : ArenaId) :
    (freeAll s collected candidates).arenas arena =
      if arena ∈ collected then [] else s.arenas arena := by
  classical
  induction collected generalizing s with
  | nil => simp [freeAll]
  | cons first rest ih =>
    simp only [freeAll, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases later : arena ∈ rest
    · simp [later]
    · by_cases same : arena = first
      · subst same; simp [reset, later]
      · simp [reset, later, same]

theorem freeAll_inv {s : State ArenaId Token} (inv : Inv s) (collected : List ArenaId)
    (candidates : Finset Token) : Inv (freeAll s collected candidates) := by
  induction collected generalizing s with
  | nil => exact inv
  | cons first rest ih =>
    simp only [freeAll, List.foldl_cons] at ih ⊢
    exact ih (inv_reset inv first 0 candidates)

theorem freeAll_released_mono (s : State ArenaId Token) (collected : List ArenaId)
    (candidates : Finset Token) : s.released ⊆ (freeAll s collected candidates).released := by
  classical
  induction collected generalizing s with
  | nil => exact fun _ member => member
  | cons first rest ih =>
    simp only [freeAll, List.foldl_cons] at ih ⊢
    intro r member
    apply ih
    simp only [reset, Finset.mem_union]
    exact Or.inl member

/-- Holds are only removed by freeing. -/
private theorem held_of_freeAll {s : State ArenaId Token} {collected : List ArenaId}
    {candidates : Finset Token} {r : Token} (held : Held (freeAll s collected candidates) r) :
    Held s r := by
  obtain ⟨arena, node, member, refers⟩ := held
  rw [freeAll_arenas] at member
  split_ifs at member
  · cases member
  · exact ⟨arena, node, member, refers⟩

/-- A resource is released by freeing only when no hold is left on it. -/
theorem freeAll_released_unheld {s : State ArenaId Token} {collected : List ArenaId}
    {candidates : Finset Token} {r : Token}
    (released : r ∈ (freeAll s collected candidates).released) (fresh : r ∉ s.released) :
    ¬ Held (freeAll s collected candidates) r := by
  classical
  induction collected generalizing s with
  | nil => exact absurd released fresh
  | cons first rest ih =>
    simp only [freeAll, List.foldl_cons] at released ih ⊢
    by_cases before : r ∈ (reset s first 0 candidates).released
    · intro held
      have earlier : Held (reset s first 0 candidates) r := held_of_freeAll held
      simp only [reset, Finset.mem_union, Finset.mem_filter] at before
      rcases before with old | ⟨_, unheld⟩
      · exact fresh old
      · exact unheld earlier
    · exact ih released before

/-- Freeing at least one arena releases every candidate left without a hold. -/
theorem freeAll_releases {s : State ArenaId Token} {collected : List ArenaId}
    (nonempty : collected ≠ []) {candidates : Finset Token} {r : Token} (candidate : r ∈ candidates)
    (unheld : ¬ Held (freeAll s collected candidates) r) :
    r ∈ (freeAll s collected candidates).released := by
  classical
  induction collected generalizing s with
  | nil => exact absurd rfl nonempty
  | cons first rest ih =>
    simp only [freeAll, List.foldl_cons] at unheld ih ⊢
    cases rest with
    | nil =>
      simp only [List.foldl_nil] at unheld ⊢
      exact reset_releases s first 0 candidates candidate unheld
    | cons second more =>
      exact ih (List.cons_ne_nil _ _) unheld

/-! ## Safety and reclamation -/

/-- A collection releases no identity a reachable node refers to: each stays held,
by its copy, and unreleased; and whatever it releases, no reachable node refers
to. -/
theorem collect_safe {s : State ArenaId Token} (inv : Inv s) {destination : ArenaId}
    {reachable : List (List Token)} {collected : List ArenaId} (candidates : Finset Token)
    (unreleased : ∀ node ∈ reachable, ∀ r ∈ node, r ∉ s.released)
    (kept : destination ∉ collected) :
    Inv (collect s destination reachable collected candidates) ∧
      (∀ node ∈ reachable, ∀ r ∈ node,
        Held (collect s destination reachable collected candidates) r ∧
          r ∉ (collect s destination reachable collected candidates).released) ∧
      ∀ r ∈ (collect s destination reachable collected candidates).released, r ∉ s.released →
        ∀ node ∈ reachable, r ∉ node := by
  have copiedInv := copyAll_inv inv destination unreleased
  have finalInv := freeAll_inv copiedInv collected candidates
  have copies : ∀ node ∈ reachable,
      node ∈ (collect s destination reachable collected candidates).arenas destination := by
    intro node member
    unfold collect
    rw [freeAll_arenas, if_neg kept, copyAll_arenas, if_pos rfl]
    exact List.mem_append_right _ member
  refine ⟨finalInv, fun node member r refers => ?_, fun r released fresh node member refers => ?_⟩
  · exact ⟨⟨destination, node, copies node member, refers⟩,
      finalInv destination node (copies node member) r refers⟩
  · have unheld := freeAll_released_unheld (s := copyAll s destination reachable) released
      (by rw [copyAll_released]; exact fresh)
    exact unheld ⟨destination, node, copies node member, refers⟩

/-- After a collection of every generation into a fresh arena, the holds left
are exactly those of reachable nodes, and every candidate none of them refers to
is released: no unreachable hold remains. -/
theorem collect_reclaims (s : State ArenaId Token) {destination : ArenaId}
    {reachable : List (List Token)} {collected : List ArenaId} (candidates : Finset Token)
    (kept : destination ∉ collected) (every : ∀ arena, arena ≠ destination → arena ∈ collected)
    (fresh : s.arenas destination = []) (nonempty : collected ≠ []) :
    (∀ r, Held (collect s destination reachable collected candidates) r ↔
        ∃ node ∈ reachable, r ∈ node) ∧
      ∀ r ∈ candidates, (∀ node ∈ reachable, r ∉ node) →
        r ∈ (collect s destination reachable collected candidates).released := by
  have arenas : ∀ arena, (collect s destination reachable collected candidates).arenas arena =
      if arena = destination then reachable else [] := by
    intro arena
    unfold collect
    rw [freeAll_arenas, copyAll_arenas]
    by_cases same : arena = destination
    · subst same; simp [kept, fresh]
    · simp [every arena same, same]
  have holds : ∀ r, Held (collect s destination reachable collected candidates) r ↔
      ∃ node ∈ reachable, r ∈ node := by
    intro r
    constructor
    · rintro ⟨arena, node, member, refers⟩
      rw [arenas] at member
      split_ifs at member
      · exact ⟨node, member, refers⟩
      · cases member
    · rintro ⟨node, member, refers⟩
      exact ⟨destination, node, by rw [arenas, if_pos rfl]; exact member, refers⟩
  refine ⟨holds, fun r candidate unreferenced => ?_⟩
  apply freeAll_releases nonempty candidate
  intro held
  obtain ⟨node, member, refers⟩ := (holds r).mp held
  exact unreferenced node member refers

/-! ## Released identities come back only as new incarnations -/

/-- Release an identity the given number of times. -/
def releaseTimes (identity : BitVec 64) : Nat → Store → Option Store
  | 0, s => some s
  | n + 1, s => (s.release? identity).bind (releaseTimes identity n)

/-- A live identity released once per reference ends its incarnation. -/
theorem release_all {identity : BitVec 64} {token : Token} (spelled : decode? identity = some token) :
    ∀ (n : Nat) (s : Store), Live s token → segmentOf token.handle ∈ s.segments →
      (s.cells token.handle).references = n + 1 →
      ∃ after, releaseTimes identity (n + 1) s = some after ∧ Ended after token ∧
        Relation.ReflTransGen TestStep s after := by
  have representable := decoded_representable spelled
  intro n
  induction n with
  | zero =>
    intro s live segment last
    have found : s.cell? token.handle = some (s.cells token.handle) := by
      unfold Store.cell?
      rw [if_pos ⟨representable.1, representable.2.1, segment⟩]
    have current : (s.cells token.handle).generation = token.generation ∧
        0 < (s.cells token.handle).references := live
    have released : ∃ after, s.release? identity = some after := by
      unfold Store.release?
      rw [spelled, Option.bind_some, found, Option.bind_some, if_pos current]
      exact ⟨_, rfl⟩
    obtain ⟨after, release⟩ := released
    refine ⟨after, by simp [releaseTimes, release], final_release_ends spelled last release,
      Relation.ReflTransGen.single (.step (.release release))⟩
  | succ n ih =>
    intro s live segment count
    have found : s.cell? token.handle = some (s.cells token.handle) := by
      unfold Store.cell?
      rw [if_pos ⟨representable.1, representable.2.1, segment⟩]
    have current : (s.cells token.handle).generation = token.generation ∧
        0 < (s.cells token.handle).references := live
    have released : ∃ middle, s.release? identity = some middle := by
      unfold Store.release?
      rw [spelled, Option.bind_some, found, Option.bind_some, if_pos current]
      exact ⟨_, rfl⟩
    obtain ⟨middle, release⟩ := released
    obtain ⟨other, decoded, _, cells⟩ := release?_cells release
    rw [spelled] at decoded
    cases Option.some.inj decoded
    have middleLive : Live middle token := by
      unfold Live
      rw [cells, Function.update_self]
      exact ⟨rfl, by dsimp only; omega⟩
    have middleSegment : segmentOf token.handle ∈ middle.segments := by
      rw [(release?_frame release).2.2]; exact segment
    have middleCount : (middle.cells token.handle).references = n + 1 := by
      rw [cells, Function.update_self]; dsimp only; omega
    obtain ⟨after, rest, ended, trace⟩ := ih middle middleLive middleSegment middleCount
    refine ⟨after, ?_, ended,
      Relation.ReflTransGen.head (.step (.release release)) trace⟩
    simp only [releaseTimes, release, Option.bind_some]
    exact rest

/-- Once a live identity has been released once per reference, as when a
collection drops its last holds, the store never accepts it again and reissues
its handle only at a higher generation. -/
theorem fresh_after_collect {s : Store} (valid : WellFormed s) {identity : BitVec 64}
    {token : Token} (spelled : decode? identity = some token) (live : Live s token) :
    ∃ after, releaseTimes identity (s.cells token.handle).references s = some after ∧
      ∀ later, Relation.ReflTransGen TestStep after later →
        later.retain? identity = none ∧ later.release? identity = none ∧
          ∀ room next reissued, later.take? room = some (next, reissued) →
            reissued.handle = token.handle → token.generation < reissued.generation := by
  have issued := valid.referenced token.handle live.2
  have segment := valid.allocated token.handle issued
  obtain ⟨n, count⟩ : ∃ n, (s.cells token.handle).references = n + 1 :=
    ⟨(s.cells token.handle).references - 1, by have := live.2; omega⟩
  obtain ⟨after, released, ended, _⟩ := release_all spelled n s live segment count
  refine ⟨after, by rw [count]; exact released, fun later trace => ?_⟩
  obtain ⟨stillEnded, refusedRetain, refusedRelease⟩ := stale_forever_g ended trace spelled
  refine ⟨refusedRetain, refusedRelease, fun room next reissued taken same => ?_⟩
  obtain ⟨generation, _⟩ := take?_cells taken
  have reached := stillEnded.1.2
  rw [← same] at reached
  omega

/-! ## Controls -/

namespace Controls

/-- A nursery, an older generation, and the fresh arena a collection copies
into. -/
inductive Arena
  | nursery
  | tenured
  | fresh
  deriving DecidableEq

/-- A reachable identity and a dead one in the nursery, and a dead identity
promoted to the older generation. -/
noncomputable def heap : State Arena Token :=
  ⟨fun arena => match arena with
    | .nursery => [[⟨1, 1⟩], [⟨2, 1⟩]]
    | .tenured => [[⟨3, 1⟩]]
    | .fresh => [], ∅⟩

def candidates : Finset Token := {⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩}

private theorem heap_inv : Inv heap := by
  intro arena node member r _
  simp [heap]

/-- Collecting every generation keeps the reachable identity and releases both
dead ones. -/
theorem every_generation_reclaims :
    Held (collect heap .fresh [[⟨1, 1⟩]] [.nursery, .tenured] candidates) ⟨1, 1⟩ ∧
      (⟨1, 1⟩ : Token) ∉
        (collect heap .fresh [[⟨1, 1⟩]] [.nursery, .tenured] candidates).released ∧
      (⟨2, 1⟩ : Token) ∈
        (collect heap .fresh [[⟨1, 1⟩]] [.nursery, .tenured] candidates).released ∧
      (⟨3, 1⟩ : Token) ∈
        (collect heap .fresh [[⟨1, 1⟩]] [.nursery, .tenured] candidates).released := by
  have safe := collect_safe heap_inv (destination := .fresh) (reachable := [[⟨1, 1⟩]])
    (collected := [.nursery, .tenured]) candidates (by simp [heap]) (by decide)
  have reclaim := collect_reclaims heap (destination := .fresh) (reachable := [[⟨1, 1⟩]])
    (collected := [.nursery, .tenured]) candidates (by decide)
    (fun arena distinct => by cases arena <;> simp_all) rfl (by simp)
  exact ⟨(safe.2.1 [⟨1, 1⟩] (by simp) ⟨1, 1⟩ (by simp)).1,
    (safe.2.1 [⟨1, 1⟩] (by simp) ⟨1, 1⟩ (by simp)).2,
    reclaim.2 ⟨2, 1⟩ (by simp [candidates]) (by simp),
    reclaim.2 ⟨3, 1⟩ (by simp [candidates]) (by simp)⟩

/-- Collecting the nursery alone leaves the promoted dead identity held: only a
collection of every generation reclaims it. -/
theorem nursery_alone_keeps_promoted_garbage :
    Held (collect heap .fresh [[⟨1, 1⟩]] [.nursery] candidates) ⟨3, 1⟩ ∧
      (⟨3, 1⟩ : Token) ∉ (collect heap .fresh [[⟨1, 1⟩]] [.nursery] candidates).released ∧
      (⟨2, 1⟩ : Token) ∈ (collect heap .fresh [[⟨1, 1⟩]] [.nursery] candidates).released := by
  have safe := collect_safe heap_inv (destination := .fresh) (reachable := [[⟨1, 1⟩]])
    (collected := [.nursery]) candidates (by simp [heap]) (by decide)
  have tenured : [⟨3, 1⟩] ∈
      (collect heap .fresh [[⟨1, 1⟩]] [.nursery] candidates).arenas .tenured := by
    unfold collect
    rw [freeAll_arenas, if_neg (by decide), copyAll_arenas, if_neg (by decide)]
    simp [heap]
  have held : Held (collect heap .fresh [[⟨1, 1⟩]] [.nursery] candidates) ⟨3, 1⟩ :=
    ⟨.tenured, [⟨3, 1⟩], tenured, by simp⟩
  refine ⟨held, safe.1 _ _ tenured _ (by simp), ?_⟩
  apply freeAll_releases (by simp) (by simp [candidates])
  rintro ⟨arena, node, member, refers⟩
  rw [freeAll_arenas, copyAll_arenas] at member
  cases arena <;> simp [heap] at member <;> subst member <;> simp at refers

/-- Freeing the arena the copies went to releases a reachable identity. -/
theorem freeing_the_copies_is_unsafe :
    (⟨1, 1⟩ : Token) ∈
      (collect heap .nursery [[⟨1, 1⟩]] [.nursery, .tenured] candidates).released := by
  apply freeAll_releases (by simp) (by simp [candidates])
  rintro ⟨arena, node, member, refers⟩
  rw [freeAll_arenas, copyAll_arenas] at member
  cases arena <;> simp [heap] at member

/-- A released handle is reissued at its next generation, and its old spelling
is refused. -/
theorem reissued_higher :
    (Store.initial.cycle.take? true).map Prod.snd = some ⟨1, 2⟩ ∧
      (Store.initial.cycle.retain? (encode ⟨1, 1⟩)).isNone = true := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.MetavariableFrameReclamation
