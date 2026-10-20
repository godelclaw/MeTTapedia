import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Basic

/-!
# Resources held by arena allocations

A runtime keeps nodes in arenas.  An arena is a log of allocations, oldest
first; resetting it to a mark truncates the log, and freeing it truncates it
to nothing.  Some nodes refer to a *resource* outside the arenas, such as a
foreign object.  Each allocation that refers to a resource registers a *hold*
on it in the same arena at the same moment, so the holds of an arena are the
resources its log refers to, and a truncation drops a node together with its
hold.  A resource is released when a truncation leaves no hold on it.

This module proves the two sides of that discipline.
- **Safety** (`inv_alloc`, `inv_reset`): no allocation still in a log refers
  to a released resource.  An allocation may refer only to a resource that is
  not released, which a runtime meets by copying a node it can still reach.
- **Reclamation** (`reset_releases`): a resource that a truncation leaves
  with no hold is released at that truncation.
- **Exactness** (`held_iff_count_pos`): a count of the holds, the runtime's
  representation, is positive exactly when some allocation refers to the
  resource.

Liveness of the *nodes* is the arenas' own discipline (a node's children live
in its arena, an older generation, or storage never released; see
`Machines.Cursor.GenerationalSharing`); this module adds only that the
resources a live node refers to stay unreleased.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ArenaHeldResources

variable {ArenaId Resource : Type} [DecidableEq ArenaId] [DecidableEq Resource]

/-- An arena's allocations, oldest first: each lists the resources its node
refers to directly. -/
abbrev Log (Resource : Type) := List (List Resource)

structure State (ArenaId Resource : Type) where
  arenas : ArenaId → Log Resource
  released : Finset Resource

/-- Some allocation, in some arena, refers to `r`. -/
def Held (s : State ArenaId Resource) (r : Resource) : Prop :=
  ∃ a, ∃ e ∈ s.arenas a, r ∈ e

/-- Safety: no allocation refers to a released resource. -/
def Inv (s : State ArenaId Resource) : Prop :=
  ∀ a, ∀ e ∈ s.arenas a, ∀ r ∈ e, r ∉ s.released

/-- Allocate a node in arena `a` referring to the resources `e`. -/
def alloc (s : State ArenaId Resource) (a : ArenaId) (e : List Resource) :
    State ArenaId Resource :=
  { s with arenas := Function.update s.arenas a (s.arenas a ++ [e]) }

/-- Truncate arena `a` to its first `k` allocations; the resources that are
held before and not after are released. -/
noncomputable def reset (s : State ArenaId Resource) (a : ArenaId) (k : Nat)
    (candidates : Finset Resource) : State ArenaId Resource := by
  classical
  let arenas := Function.update s.arenas a ((s.arenas a).take k)
  exact { arenas := arenas,
          released := s.released ∪
            candidates.filter (fun r => ¬ ∃ b, ∃ e ∈ arenas b, r ∈ e) }

omit [DecidableEq ArenaId] [DecidableEq Resource] in
theorem held_of_mem {s : State ArenaId Resource} {a : ArenaId}
    {e : List Resource} (member : e ∈ s.arenas a) {r : Resource}
    (refers : r ∈ e) : Held s r :=
  ⟨a, e, member, refers⟩

omit [DecidableEq Resource] in
theorem mem_update_arenas {s : State ArenaId Resource} {a b : ArenaId}
    {log : Log Resource} {e : List Resource}
    (member : e ∈ Function.update s.arenas a log b) :
    (b = a ∧ e ∈ log) ∨ (b ≠ a ∧ e ∈ s.arenas b) := by
  by_cases same : b = a
  · subst same
    simp only [Function.update_self] at member
    exact Or.inl ⟨rfl, member⟩
  · rw [Function.update_of_ne same] at member
    exact Or.inr ⟨same, member⟩

omit [DecidableEq Resource] in
/-- Safety survives an allocation that refers only to unreleased resources. -/
theorem inv_alloc {s : State ArenaId Resource} (inv : Inv s) (a : ArenaId)
    (e : List Resource) (fresh : ∀ r ∈ e, r ∉ s.released) :
    Inv (alloc s a e) := by
  intro b e' member r refers
  rcases mem_update_arenas member with ⟨rfl, inLog⟩ | ⟨_, inOld⟩
  · rcases List.mem_append.mp inLog with old | new
    · exact inv b e' old r refers
    · have : e' = e := by simpa using new
      subst this
      exact fresh r refers
  · exact inv b e' inOld r refers

/-- Safety survives a truncation: what remains was not released before, and
what the truncation releases is held by nothing that remains. -/
theorem inv_reset {s : State ArenaId Resource} (inv : Inv s) (a : ArenaId)
    (k : Nat) (candidates : Finset Resource) :
    Inv (reset s a k candidates) := by
  classical
  intro b e member r refers
  simp only [reset, Finset.mem_union, Finset.mem_filter, not_or, not_and,
    not_not]
  have remained : e ∈ s.arenas b := by
    rcases mem_update_arenas member with ⟨rfl, inLog⟩ | ⟨_, inOld⟩
    · exact List.mem_of_mem_take inLog
    · exact inOld
  refine ⟨inv b e remained r refers, fun _ => ⟨b, e, member, refers⟩⟩

/-- Reclamation: a candidate that the truncation leaves with no hold is
released by it. -/
theorem reset_releases (s : State ArenaId Resource) (a : ArenaId) (k : Nat)
    (candidates : Finset Resource) {r : Resource} (candidate : r ∈ candidates)
    (unheld : ¬ Held (reset s a k candidates) r) :
    r ∈ (reset s a k candidates).released := by
  classical
  simp only [reset, Finset.mem_union, Finset.mem_filter]
  exact Or.inr ⟨candidate, unheld⟩

/-- The holds on `r` in one log. -/
def logHolds (log : Log Resource) (r : Resource) : Nat :=
  (log.map (fun e => e.count r)).sum

/-- A log holds `r` exactly when one of its allocations refers to it. -/
theorem logHolds_pos_iff (log : Log Resource) (r : Resource) :
    0 < logHolds log r ↔ ∃ e ∈ log, r ∈ e := by
  induction log with
  | nil => simp [logHolds]
  | cons head tail ih =>
      simp only [logHolds, List.map_cons, List.sum_cons] at ih ⊢
      constructor
      · intro positive
        by_cases here : 0 < head.count r
        · exact ⟨head, List.mem_cons_self .., List.count_pos_iff.mp here⟩
        · have rest : 0 < (tail.map fun e => e.count r).sum := by omega
          obtain ⟨e, member, refers⟩ := ih.mp rest
          exact ⟨e, List.mem_cons_of_mem _ member, refers⟩
      · rintro ⟨e, member, refers⟩
        rcases List.mem_cons.mp member with rfl | later
        · have := List.count_pos_iff.mpr refers
          omega
        · have := ih.mpr ⟨e, later, refers⟩
          omega

/-- The runtime counts holds over the arenas in use; the count is positive
exactly when some allocation in them refers to the resource. -/
theorem held_iff_count_pos (s : State ArenaId Resource) (inUse : Finset ArenaId)
    (outside : ∀ a ∉ inUse, s.arenas a = []) (r : Resource) :
    Held s r ↔ 0 < ∑ a ∈ inUse, logHolds (s.arenas a) r := by
  constructor
  · rintro ⟨a, e, member, refers⟩
    have used : a ∈ inUse := by
      by_contra absent
      rw [outside a absent] at member
      cases member
    have positive : 0 < logHolds (s.arenas a) r :=
      (logHolds_pos_iff _ r).mpr ⟨e, member, refers⟩
    exact lt_of_lt_of_le positive
      (Finset.single_le_sum (f := fun b => logHolds (s.arenas b) r)
        (fun b _ => Nat.zero_le _) used)
  · intro positive
    by_contra unheld
    have none : ∀ a ∈ inUse, logHolds (s.arenas a) r = 0 := by
      intro a _
      by_contra nonzero
      obtain ⟨e, member, refers⟩ :=
        (logHolds_pos_iff _ r).mp (Nat.pos_of_ne_zero nonzero)
      exact unheld ⟨a, e, member, refers⟩
    rw [Finset.sum_eq_zero none] at positive
    exact Nat.lt_irrefl 0 positive


/-! A returned image may retain only host-qualified resources that its actual
source-arena family holds. Surface classification does not remove a node's resource
requirements. This finite sequential capture uses the existing allocation log;
its temporary suffix is rolled back with the same reset operation. -/
namespace Capture

/-- Host shareability is an explicit lifetime qualification, not execution
permission. A source-family hold and unreleased status are checked from actual state. -/
def qualified (s : State ArenaId Resource) (sources : Finset ArenaId)
    (shareable : Resource → Bool) (node : List Resource) : Bool :=
  node.all fun r => shareable r &&
    (decide (∃ owner ∈ sources, 0 < logHolds (s.arenas owner) r) && decide (r ∉ s.released))

omit [DecidableEq ArenaId] in
theorem qualified_iff (s : State ArenaId Resource) (sources : Finset ArenaId)
    (shareable : Resource → Bool) (node : List Resource) :
    qualified s sources shareable node = true ↔
      ∀ r ∈ node, shareable r = true ∧
        (∃ owner ∈ sources, 0 < logHolds (s.arenas owner) r) ∧ r ∉ s.released := by
  simp [qualified, Bool.and_eq_true]

private theorem qualified_alloc (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (entry node : List Resource) (distinct : receiver ∉ sources) :
    qualified (alloc s receiver entry) sources shareable node =
      qualified s sources shareable node := by
  have owners (r : Resource) :
      (∃ owner ∈ sources, 0 < logHolds ((alloc s receiver entry).arenas owner) r) ↔
        ∃ owner ∈ sources, 0 < logHolds (s.arenas owner) r := by
    constructor <;> rintro ⟨owner, member, held⟩
    all_goals
      have separate : owner ≠ receiver := by
        intro same
        exact distinct (same ▸ member)
      refine ⟨owner, member, ?_⟩
      simpa only [alloc, Function.update_of_ne separate] using held
  apply Bool.eq_iff_iff.mpr
  simp only [qualified_iff, owners]
  rfl

/-- A checked fold retains its actual staged allocation state on refusal.
Only the enclosing capture publishes success or rolls back that suffix. -/
def attempt (sources : Finset ArenaId) (receiver : ArenaId) (shareable : Resource → Bool) :
    State ArenaId Resource → Log Resource → Bool × State ArenaId Resource
  | s, [] => (true, s)
  | s, node :: rest =>
      if qualified s sources shareable node then
        attempt sources receiver shareable (alloc s receiver node) rest
      else (false, s)

/-- Prefixes occur only in the proof: no runtime journal is returned. -/
theorem attempt_prefix (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (distinct : receiver ∉ sources) :
    ∃ copied suffix, nodes = copied ++ suffix ∧
      (attempt sources receiver shareable s nodes).2.arenas receiver = s.arenas receiver ++ copied ∧
      (∀ other, other ≠ receiver →
        (attempt sources receiver shareable s nodes).2.arenas other = s.arenas other) ∧
      (attempt sources receiver shareable s nodes).2.released = s.released ∧
      (∀ node ∈ copied, qualified s sources shareable node = true) ∧
      ((attempt sources receiver shareable s nodes).1 = true → copied = nodes) := by
  induction nodes generalizing s with
  | nil =>
      exact ⟨[], [], rfl, by simp [attempt], fun _ _ => rfl, rfl,
        by simp, fun _ => rfl⟩
  | cons node rest ih =>
      cases checked : qualified s sources shareable node with
      | false =>
          simp only [attempt, checked, Bool.false_eq_true, ↓reduceIte]
          refine ⟨[], node :: rest, ?_⟩
          simp
      | true =>
          simp only [attempt, checked, ↓reduceIte]
          obtain ⟨copied, suffix, partition, log, frame, released, allowed, complete⟩ :=
            ih (alloc s receiver node)
          refine ⟨node :: copied, suffix, ?_, ?_, ?_, released, ?_, ?_⟩
          · simpa using congrArg (List.cons node) partition
          · simpa [alloc, List.append_assoc] using log
          · intro other separate
            rw [frame other separate]
            simp only [alloc, Function.update_of_ne separate]
          · intro entry member
            rcases List.mem_cons.mp member with rfl | later
            · exact checked
            · simpa only [qualified_alloc s sources receiver shareable node entry distinct]
                using allowed entry later
          · intro done
            rw [complete done]

theorem attempt_admitted (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (distinct : receiver ∉ sources) :
    (attempt sources receiver shareable s nodes).1 =
      nodes.all (qualified s sources shareable) := by
  induction nodes generalizing s with
  | nil => rfl
  | cons node rest ih =>
      have same : qualified (alloc s receiver node) sources shareable =
          qualified s sources shareable := by
        funext entry
        exact qualified_alloc s sources receiver shareable node entry distinct
      cases checked : qualified s sources shareable node <;>
        simp only [attempt, checked, Bool.false_eq_true, ↓reduceIte, List.all_cons,
          Bool.false_and, Bool.true_and]
      rw [ih, same]

omit [DecidableEq ArenaId] [DecidableEq Resource] in
private theorem state_ext {s t : State ArenaId Resource}
    (arenas : s.arenas = t.arenas) (released : s.released = t.released) : s = t := by
  cases s
  cases t
  cases arenas
  cases released
  rfl

/-- Every temporary hold still has its original source-family hold at rollback.
Reset therefore restores the whole original state, including released resources. -/
theorem attempt_rollback (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (distinct : receiver ∉ sources) :
    let staged := (attempt sources receiver shareable s nodes).2
    reset staged receiver (s.arenas receiver).length
      (((staged.arenas receiver).drop (s.arenas receiver).length).flatten.toFinset) = s := by
  classical
  obtain ⟨copied, suffix, _, log, frame, released, allowed, _⟩ :=
    attempt_prefix s sources receiver shareable nodes distinct
  let staged := (attempt sources receiver shareable s nodes).2
  let candidates := ((staged.arenas receiver).drop (s.arenas receiver).length).flatten.toFinset
  have dropped : (staged.arenas receiver).drop (s.arenas receiver).length = copied := by
    rw [log]
    simp
  have arenas : (reset staged receiver (s.arenas receiver).length candidates).arenas = s.arenas := by
    funext other
    by_cases same : other = receiver
    · subst other
      simp only [reset, Function.update_self]
      change ((attempt sources receiver shareable s nodes).2.arenas receiver).take
        (s.arenas receiver).length = s.arenas receiver
      rw [log]
      simp
    · simpa only [reset, Function.update_of_ne same] using frame other same
  have held : ∀ r ∈ candidates,
      Held (reset staged receiver (s.arenas receiver).length candidates) r := by
    intro r member
    have listed : r ∈ copied.flatten := by
      simpa only [candidates, dropped, List.mem_toFinset] using member
    obtain ⟨node, inPrefix, refers⟩ := List.mem_flatten.mp listed
    obtain ⟨owner, _, heldByOwner⟩ :=
      ((qualified_iff s sources shareable node).mp (allowed node inPrefix) r refers).2.1
    obtain ⟨entry, inSource, sourceRef⟩ := (logHolds_pos_iff (s.arenas owner) r).mp heldByOwner
    refine ⟨owner, entry, ?_, sourceRef⟩
    rw [congrFun arenas owner]
    exact inSource
  have noNew : candidates.filter
      (fun r => ¬ Held (reset staged receiver (s.arenas receiver).length candidates) r) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r member unheld
    exact unheld (held r member)
  apply state_ext arenas
  change staged.released ∪ candidates.filter
    (fun r => ¬ Held (reset staged receiver (s.arenas receiver).length candidates) r) = s.released
  rw [noNew, Finset.union_empty]
  exact released

/-- The source family excludes the independent receiver. A failed attempt
publishes nothing and resets its temporary suffix. The finite attempt/check is
executable; this wrapper reuses the noncomputable global-hold reset semantics. -/
noncomputable def capture (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) : Bool × State ArenaId Resource :=
  if receiver ∈ sources then (false, s)
  else
    let result := attempt sources receiver shareable s nodes
    if result.1 then result
    else (false, reset result.2 receiver (s.arenas receiver).length
      (((result.2.arenas receiver).drop (s.arenas receiver).length).flatten.toFinset))

theorem admitted_iff (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) :
    (capture s sources receiver shareable nodes).1 = true ↔
      receiver ∉ sources ∧ nodes.all (qualified s sources shareable) = true := by
  by_cases sameArena : receiver ∈ sources
  · simp [capture, sameArena]
  · have checked := attempt_admitted s sources receiver shareable nodes sameArena
    cases completed : (attempt sources receiver shareable s nodes).1 <;>
      simp [capture, sameArena, completed, ← checked]

theorem failed_rollback (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource)
    (failed : (capture s sources receiver shareable nodes).1 = false) :
    (capture s sources receiver shareable nodes).2 = s := by
  by_cases sameArena : receiver ∈ sources
  · simp [capture, sameArena]
  · cases completed : (attempt sources receiver shareable s nodes).1 with
    | true => simp [capture, sameArena, completed] at failed
    | false =>
        simp only [capture, sameArena, ↓reduceIte, completed, Bool.false_eq_true]
        exact attempt_rollback s sources receiver shareable nodes sameArena

private theorem successful_state (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources receiver shareable nodes).1 = true) :
    (capture s sources receiver shareable nodes).2 = (attempt sources receiver shareable s nodes).2 := by
  obtain ⟨distinct, checked⟩ := (admitted_iff s sources receiver shareable nodes).mp admitted
  have completed : (attempt sources receiver shareable s nodes).1 = true := by
    rw [attempt_admitted s sources receiver shareable nodes distinct]
    exact checked
  simp [capture, distinct, completed]

private theorem attempt_inv (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (inv : Inv s) :
    Inv (attempt sources receiver shareable s nodes).2 := by
  induction nodes generalizing s with
  | nil => exact inv
  | cons node rest ih =>
      cases checked : qualified s sources shareable node with
      | false => simpa only [attempt, checked, Bool.false_eq_true, ↓reduceIte] using inv
      | true =>
          simp only [attempt, checked, ↓reduceIte]
          apply ih
          apply inv_alloc inv
          intro r member
          exact ((qualified_iff s sources shareable node).mp checked r member).2.2

theorem inv_capture (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (inv : Inv s) :
    Inv (capture s sources receiver shareable nodes).2 := by
  cases admitted : (capture s sources receiver shareable nodes).1 with
  | false => rw [failed_rollback s sources receiver shareable nodes admitted]; exact inv
  | true =>
      rw [successful_state s sources receiver shareable nodes admitted]
      exact attempt_inv s sources receiver shareable nodes inv

theorem admitted_log (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources receiver shareable nodes).1 = true) :
    (capture s sources receiver shareable nodes).2.arenas receiver = s.arenas receiver ++ nodes := by
  have distinct := ((admitted_iff s sources receiver shareable nodes).mp admitted).1
  obtain ⟨_, _, _, log, _, _, _, complete⟩ :=
    attempt_prefix s sources receiver shareable nodes distinct
  have done : (attempt sources receiver shareable s nodes).1 = true := by
    rw [attempt_admitted s sources receiver shareable nodes distinct]
    exact ((admitted_iff s sources receiver shareable nodes).mp admitted).2
  rw [successful_state s sources receiver shareable nodes admitted, log, complete done]

theorem frame (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) (other : ArenaId)
    (separate : other ≠ receiver) :
    (capture s sources receiver shareable nodes).2.arenas other = s.arenas other := by
  cases admitted : (capture s sources receiver shareable nodes).1 with
  | false => rw [failed_rollback s sources receiver shareable nodes admitted]
  | true =>
      have distinct := ((admitted_iff s sources receiver shareable nodes).mp admitted).1
      obtain ⟨_, _, _, _, frames, _⟩ := attempt_prefix s sources receiver shareable nodes distinct
      rw [successful_state s sources receiver shareable nodes admitted]
      exact frames other separate

theorem released_unchanged (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) :
    (capture s sources receiver shareable nodes).2.released = s.released := by
  cases admitted : (capture s sources receiver shareable nodes).1 with
  | false => rw [failed_rollback s sources receiver shareable nodes admitted]
  | true =>
      have distinct := ((admitted_iff s sources receiver shareable nodes).mp admitted).1
      obtain ⟨_, _, _, _, _, released, _⟩ := attempt_prefix s sources receiver shareable nodes distinct
      rw [successful_state s sources receiver shareable nodes admitted]
      exact released

/-- Cancelling a capture while its sources still hold the resources restores
its exact pre-capture state. -/
theorem cancel (s : State ArenaId Resource) (sources : Finset ArenaId) (receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources receiver shareable nodes).1 = true) :
    let result := (capture s sources receiver shareable nodes).2
    reset result receiver (s.arenas receiver).length
      (((result.arenas receiver).drop (s.arenas receiver).length).flatten.toFinset) = s := by
  have distinct := ((admitted_iff s sources receiver shareable nodes).mp admitted).1
  dsimp only
  rw [successful_state s sources receiver shareable nodes admitted]
  exact attempt_rollback s sources receiver shareable nodes distinct


/-- One source arena is precisely the singleton-family profile. -/
theorem singleton_admitted_iff (s : State ArenaId Resource) (source receiver : ArenaId)
    (shareable : Resource → Bool) (nodes : Log Resource) :
    (capture s {source} receiver shareable nodes).1 = true ↔
      receiver ≠ source ∧ ∀ node ∈ nodes, ∀ r ∈ node,
        shareable r = true ∧ 0 < logHolds (s.arenas source) r ∧ r ∉ s.released := by
  simp [admitted_iff, List.all_eq_true, qualified_iff]

private theorem qualified_after_capture (s : State ArenaId Resource)
    (sources : Finset ArenaId) (receiver : ArenaId) (shareable : Resource → Bool)
    (nodes : Log Resource) (distinct : receiver ∉ sources) (node : List Resource) :
    qualified (capture s sources receiver shareable nodes).2 sources shareable node =
      qualified s sources shareable node := by
  have owners (r : Resource) :
      (∃ owner ∈ sources,
        0 < logHolds ((capture s sources receiver shareable nodes).2.arenas owner) r) ↔
      ∃ owner ∈ sources, 0 < logHolds (s.arenas owner) r := by
    constructor <;> rintro ⟨owner, member, held⟩
    all_goals
      have separate : owner ≠ receiver := by
        intro same
        exact distinct (same ▸ member)
      refine ⟨owner, member, ?_⟩
      simpa only [frame s sources receiver shareable nodes owner separate] using held
  apply Bool.eq_iff_iff.mpr
  simp only [qualified_iff, owners, released_unchanged]

/-- A second independently held receiver retains the same resource identities.
It does not remove or overwrite the first receiver's allocations. -/
theorem independent_receivers (s : State ArenaId Resource) (sources : Finset ArenaId)
    (first second : ArenaId) (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources first shareable nodes).1 = true)
    (outside : second ∉ sources) (separate : first ≠ second) :
    let firstImage := (capture s sources first shareable nodes).2
    let secondImage := capture firstImage sources second shareable nodes
    secondImage.1 = true ∧
      secondImage.2.arenas first = s.arenas first ++ nodes ∧
      secondImage.2.arenas second = s.arenas second ++ nodes := by
  obtain ⟨distinct, allowed⟩ := (admitted_iff s sources first shareable nodes).mp admitted
  let firstImage := (capture s sources first shareable nodes).2
  have same : qualified firstImage sources shareable = qualified s sources shareable := by
    funext node
    exact qualified_after_capture s sources first shareable nodes distinct node
  have again : (capture firstImage sources second shareable nodes).1 = true := by
    apply (admitted_iff firstImage sources second shareable nodes).mpr
    exact ⟨outside, by simpa only [same] using allowed⟩
  refine ⟨again, ?_, ?_⟩
  · rw [frame firstImage sources second shareable nodes first separate]
    exact admitted_log s sources first shareable nodes admitted
  · rw [admitted_log firstImage sources second shareable nodes again]
    rw [frame s sources first shareable nodes second (Ne.symm separate)]

private theorem reset_frame (s : State ArenaId Resource) (arena other : ArenaId)
    (mark : Nat) (candidates : Finset Resource) (separate : other ≠ arena) :
    (reset s arena mark candidates).arenas other = s.arenas other := by
  classical
  simp only [reset, Function.update_of_ne separate]

private theorem resets_arenas (s : State ArenaId Resource) (retired : List ArenaId)
    (candidates : Finset Resource) (arena : ArenaId) :
    (retired.foldl (fun current owner => reset current owner 0 candidates) s).arenas arena =
      if arena ∈ retired then [] else s.arenas arena := by
  classical
  induction retired generalizing s with
  | nil => simp
  | cons owner rest ih =>
      rw [List.foldl_cons, ih]
      by_cases later : arena ∈ rest
      · simp [later]
      · by_cases same : arena = owner <;> simp [reset, later, same]

private theorem resets_inv (s : State ArenaId Resource) (retired : List ArenaId)
    (candidates : Finset Resource) (inv : Inv s) :
    Inv (retired.foldl (fun current owner => reset current owner 0 candidates) s) := by
  induction retired generalizing s with
  | nil => exact inv
  | cons owner rest ih => exact ih _ (inv_reset inv owner 0 candidates)

/-- Source-family retirement and independent receiver cancellation use the
same resets. Every still-held receiver keeps its entire log and required holds. -/
theorem retirements_safe (s : State ArenaId Resource) (sources : Finset ArenaId)
    (receiver : ArenaId) (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources receiver shareable nodes).1 = true) (inv : Inv s)
    (retired : List ArenaId) (candidates : Finset Resource)
    (separate : ∀ owner ∈ retired, owner ≠ receiver) :
    let result := retired.foldl (fun current owner => reset current owner 0 candidates)
      (capture s sources receiver shareable nodes).2
    result.arenas receiver = s.arenas receiver ++ nodes ∧ Inv result ∧
      ∀ r ∈ nodes.flatten, Held result r ∧ r ∉ result.released := by
  have absent : receiver ∉ retired := fun member => separate receiver member rfl
  have log := resets_arenas (capture s sources receiver shareable nodes).2 retired candidates receiver
  rw [if_neg absent, admitted_log s sources receiver shareable nodes admitted] at log
  have safe := resets_inv (capture s sources receiver shareable nodes).2 retired candidates
    (inv_capture s sources receiver shareable nodes inv)
  refine ⟨log, safe, ?_⟩
  intro r member
  obtain ⟨node, listed, refers⟩ := List.mem_flatten.mp member
  have retained : node ∈
      (retired.foldl (fun current owner => reset current owner 0 candidates)
        (capture s sources receiver shareable nodes).2).arenas receiver := by
    rw [log]
    exact List.mem_append.mpr (Or.inr listed)
  exact ⟨held_of_mem retained refers, safe receiver node retained r refers⟩

/-- Retire the other holders of the required resources, leaving unrelated
live frames intact. Releasing the final receiver reclaims each listed resource;
none was reclaimed while that receiver still held it. -/
theorem final_release (s : State ArenaId Resource) (sources : Finset ArenaId)
    (receiver : ArenaId) (shareable : Resource → Bool) (nodes : Log Resource)
    (admitted : (capture s sources receiver shareable nodes).1 = true) (inv : Inv s)
    (retired : List ArenaId) (candidates : Finset Resource)
    (separate : ∀ owner ∈ retired, owner ≠ receiver)
    (disjoint : ∀ owner, owner ≠ receiver → owner ∉ retired →
      ∀ r ∈ nodes.flatten, logHolds (s.arenas owner) r = 0) :
    let before := retired.foldl (fun current owner => reset current owner 0 candidates)
      (capture s sources receiver shareable nodes).2
    let after := reset before receiver 0 nodes.flatten.toFinset
    (∀ owner, owner ≠ receiver → owner ∉ retired → after.arenas owner = s.arenas owner) ∧
      ∀ r ∈ nodes.flatten, Held before r ∧ r ∉ before.released ∧
        ¬ Held after r ∧ r ∈ after.released := by
  classical
  dsimp only
  obtain ⟨_, _, safe⟩ := retirements_safe s sources receiver shareable nodes admitted inv
    retired candidates separate
  let before := retired.foldl (fun current owner => reset current owner 0 candidates)
    (capture s sources receiver shareable nodes).2
  let after := reset before receiver 0 nodes.flatten.toFinset
  have stable (owner : ArenaId) (different : owner ≠ receiver) (retained : owner ∉ retired) :
      after.arenas owner = s.arenas owner := by
    change (reset before receiver 0 nodes.flatten.toFinset).arenas owner = s.arenas owner
    rw [reset_frame before receiver owner 0 nodes.flatten.toFinset different]
    change (retired.foldl (fun current owner => reset current owner 0 candidates)
      (capture s sources receiver shareable nodes).2).arenas owner = s.arenas owner
    rw [resets_arenas, if_neg retained, frame s sources receiver shareable nodes owner different]
  have unheld (r : Resource) (required : r ∈ nodes.flatten) : ¬ Held after r := by
    rintro ⟨owner, node, member, refers⟩
    by_cases same : owner = receiver
    · subst owner
      have empty : after.arenas receiver = [] := by simp [after, reset]
      rw [empty] at member
      cases member
    · by_cases gone : owner ∈ retired
      · have empty : after.arenas owner = [] := by
          change (reset before receiver 0 nodes.flatten.toFinset).arenas owner = []
          rw [reset_frame before receiver owner 0 nodes.flatten.toFinset same]
          change (retired.foldl (fun current owner => reset current owner 0 candidates)
            (capture s sources receiver shareable nodes).2).arenas owner = []
          rw [resets_arenas, if_pos gone]
        rw [empty] at member
        cases member
      · have positive : 0 < logHolds (s.arenas owner) r := by
          apply (logHolds_pos_iff (s.arenas owner) r).mpr
          exact ⟨node, by simpa only [stable owner same gone] using member, refers⟩
        rw [disjoint owner same gone r required] at positive
        exact Nat.lt_irrefl 0 positive
  refine ⟨stable, ?_⟩
  intro r member
  exact ⟨(safe r member).1, (safe r member).2, unheld r member,
    reset_releases before receiver 0 nodes.flatten.toFinset
      (List.mem_toFinset.mpr member) (unheld r member)⟩

#print axioms qualified_iff
#print axioms attempt_prefix
#print axioms attempt_admitted
#print axioms attempt_rollback
#print axioms admitted_iff
#print axioms failed_rollback
#print axioms inv_capture
#print axioms admitted_log
#print axioms frame
#print axioms released_unchanged
#print axioms cancel
#print axioms singleton_admitted_iff
#print axioms independent_receivers
#print axioms retirements_safe
#print axioms final_release


namespace Controls

def seed : State Nat Nat :=
  ⟨fun arena => if arena = 0 then [[11]] else if arena = 3 then [[12]]
    else if arena = 4 then [[77]] else [], ∅⟩

def family : Finset Nat := {0, 3}
def nodes : Log Nat := [[11, 12], [11]]
def allow : Nat → Bool := fun _ => true
def looksScalar (resource : Nat) : Bool := resource == 11

private theorem seed_inv : Inv seed := by
  intro _ _ _ _ _
  simp [seed]

/-- Surface appearance cannot replace a real resource requirement with none. -/
theorem scalar_classification_keeps_the_required_hold :
    looksScalar 11 = true ∧
    (capture seed family 1 (fun _ => false) [[11]]).1 = false ∧
    (capture seed family 1 (fun _ => false) []).1 = true ∧
    (capture seed family 1 allow [[11]]).1 = true ∧
    (capture seed family 1 allow [[11]]).2.arenas 1 = [[11]] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact admitted_log seed family 1 allow [[11]] rfl

theorem missing_unique_or_receiver_owner_is_refused :
    (capture seed {3} 1 allow [[11]]).1 = false ∧
    (capture seed family 1 (fun resource => resource != 12) [[12]]).1 = false ∧
    (capture seed family 0 allow [[11]]).1 = false :=
  ⟨rfl, rfl, rfl⟩

def withFrame := alloc seed 1 [99]
def mixed : Nat → Bool := fun resource => resource != 12

/-- The first node really acquired a temporary hold before the later refusal.
Rollback preserves the pre-existing receiver prefix and every other arena. -/
theorem late_failure_rolls_back_the_actual_temporary_suffix :
    (attempt family 1 mixed withFrame [[11], [12]]).1 = false ∧
    (attempt family 1 mixed withFrame [[11], [12]]).2.arenas 1 = [[99], [11]] ∧
    (capture withFrame family 1 mixed [[11], [12]]).1 = false ∧
    (capture withFrame family 1 mixed [[11], [12]]).2 = withFrame ∧
    (capture withFrame family 1 mixed [[11], [12]]).2.arenas 4 = [[77]] := by
  have rolled := failed_rollback withFrame family 1 mixed [[11], [12]] rfl
  exact ⟨rfl, rfl, rfl, rolled, by rw [rolled]; rfl⟩

noncomputable def firstImage := (capture seed family 1 allow nodes).2
noncomputable def secondImage := (capture firstImage family 2 allow nodes).2
noncomputable def beforeFinal :=
  [0, 3, 1].foldl (fun current owner => reset current owner 0 nodes.flatten.toFinset) secondImage
noncomputable def afterFinal := reset beforeFinal 2 0 nodes.flatten.toFinset

private theorem second_admitted : (capture firstImage family 2 allow nodes).1 = true :=
  (independent_receivers seed family 1 2 allow nodes rfl (by decide) (by decide)).1

private theorem before_separate : ∀ owner ∈ ([0, 3, 1] : List Nat), owner ≠ 2 := by
  intro owner member
  simp at member
  rcases member with rfl | rfl | rfl <;> decide

private theorem first_disjoint : ∀ owner : Nat, owner ≠ 2 →
    owner ∉ ([0, 3, 1] : List Nat) → ∀ r ∈ nodes.flatten,
      logHolds (firstImage.arenas owner) r = 0 := by
  intro owner _ retained r required
  have zero : owner ≠ 0 := by intro same; subst owner; exact retained (by simp)
  have three : owner ≠ 3 := by intro same; subst owner; exact retained (by simp)
  have one : owner ≠ 1 := by intro same; subst owner; exact retained (by simp)
  change logHolds ((capture seed family 1 allow nodes).2.arenas owner) r = 0
  rw [frame seed family 1 allow nodes owner one]
  simp [nodes] at required
  rcases required with rfl | rfl | rfl
  all_goals by_cases unrelated : owner = 4 <;> simp [seed, zero, three, unrelated, logHolds]

theorem two_receivers_survive_family_retirement_and_cancel_independently :
    (capture firstImage family 2 allow nodes).1 = true ∧
    secondImage.arenas 1 = nodes ∧
    beforeFinal.arenas 0 = [] ∧ beforeFinal.arenas 3 = [] ∧ beforeFinal.arenas 1 = [] ∧
    beforeFinal.arenas 2 = nodes ∧
    afterFinal.arenas 4 = [[77]] ∧ Held afterFinal 77 ∧ 77 ∉ afterFinal.released ∧
    ∀ r ∈ nodes.flatten, Held beforeFinal r ∧ r ∉ beforeFinal.released ∧
      ¬ Held afterFinal r ∧ r ∈ afterFinal.released := by
  have firstInv := inv_capture seed family 1 allow nodes seed_inv
  have last := final_release firstImage family 2 allow nodes second_admitted firstInv
    [0, 3, 1] nodes.flatten.toFinset before_separate first_disjoint
  have kept := (retirements_safe firstImage family 2 allow nodes second_admitted firstInv
    [0, 3, 1] nodes.flatten.toFinset before_separate).1
  have originalEmpty : firstImage.arenas 2 = [] := by
    change (capture seed family 1 allow nodes).2.arenas 2 = []
    rw [frame seed family 1 allow nodes 2 (by decide)]
    rfl
  rw [originalEmpty, List.nil_append] at kept
  have unrelatedLog : afterFinal.arenas 4 = [[77]] := by
    calc
      afterFinal.arenas 4 = firstImage.arenas 4 := last.1 4 (by decide) (by decide)
      _ = [[77]] := by
        change (capture seed family 1 allow nodes).2.arenas 4 = [[77]]
        rw [frame seed family 1 allow nodes 4 (by decide)]
        rfl
  have unrelatedNode : [77] ∈ afterFinal.arenas 4 := by rw [unrelatedLog]; simp
  have afterInv : Inv afterFinal := inv_reset
    (resets_inv secondImage [0, 3, 1] nodes.flatten.toFinset
      (inv_capture firstImage family 2 allow nodes firstInv)) 2 0 nodes.flatten.toFinset
  have emptied (owner : Nat) (listed : owner ∈ ([0, 3, 1] : List Nat)) :
      beforeFinal.arenas owner = [] := by
    have raw := resets_arenas secondImage [0, 3, 1] nodes.flatten.toFinset owner
    rw [if_pos listed] at raw
    exact raw
  refine ⟨second_admitted, ?_, emptied 0 (by decide), emptied 3 (by decide),
    emptied 1 (by decide), kept, unrelatedLog,
    held_of_mem unrelatedNode (by simp), afterInv 4 [77] unrelatedNode 77 (by simp), last.2⟩
  exact (independent_receivers seed family 1 2 allow nodes rfl (by decide) (by decide)).2.1

#print axioms scalar_classification_keeps_the_required_hold
#print axioms missing_unique_or_receiver_owner_is_refused
#print axioms late_failure_rolls_back_the_actual_temporary_suffix
#print axioms two_receivers_survive_family_retirement_and_cancel_independently

end Controls

-- The capture proof reuses these existing safety and reclamation laws.
#print axioms inv_alloc
#print axioms inv_reset
#print axioms reset_releases
#print axioms logHolds_pos_iff

end Capture

end Mettapedia.Machines.ArenaHeldResources
