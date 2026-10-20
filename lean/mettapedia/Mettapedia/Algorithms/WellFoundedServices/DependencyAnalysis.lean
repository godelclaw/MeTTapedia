import Mettapedia.Algorithms.WellFoundedServices.MeasuredLoop
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Relation
import Mathlib.Data.List.Forall2
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Iterate
import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation
import Mettapedia.Machines.ResumableRegion

/-!
# Dependency analysis over a finite catalogue

A catalogue lists its items and, for each item, the items it depends on. Four
services, each a measured loop or a measured recursion:

* `Catalogue.affected`: the items affected by a change, found by a reverse
  sweep; `mem_affected` says they are exactly the items that depend, directly
  or not, on a changed item. Variant: the number of catalogue items not yet
  seen.
* `Catalogue.schedule`: parallel rebuild waves (Kahn's algorithm) or a blocked
  set. `schedule_spec`: the waves list every target once, no item depends on
  itself, on an item of its own wave or on a later one; a blocked set is a
  nonempty set of targets each of which depends on a member. Variant: the
  number of pending targets.
* `Catalogue.findCycle`: an explicit dependency cycle through a blocked set,
  found by walking inside it until an item repeats (`findCycle_spec`).
  Variant: the number of members of the set not yet visited.
  `Catalogue.cycle?` finds a cycle among the catalogue items exactly when one
  exists (`cycle?_isSome_iff`).
* `Catalogue.Acyclic.recOrder`: recursion over the dependency relation itself,
  from an acyclicity certificate (a rebuild order of the whole catalogue): the
  value at an item is computed from the values at its dependencies. The
  certificate makes every item accessible (`Acyclic.accCode`).

The bounded `OccurrenceGraph` service is specified by the same independent
dependency-fold judgment. It retains its ordered DFS cursor, memo and
analysis expense across resumptions, and proves soundness of successful
bound readouts. Native memory and source-coverage adapters are separate.

Each loop also runs through the accessibility route (`affectedAcc`,
`scheduleAcc`, `Acyclic.recAcc`), and the two versions agree for every inert
recursor.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Relation Mettapedia.Order

universe u v w

/-- A catalogue of items, each listing the items it depends on. -/
structure Catalogue (α : Type u) where
  items : List α
  deps : α → List α

/-- The segment of a reversed walk from its head down to the first occurrence
of `y`, in walk order. -/
def cycleAt {α : Type u} [DecidableEq α] (y : α) : List α → List α
  | [] => []
  | a :: l => if a = y then [a] else cycleAt y l ++ [a]

/-- A strictly stronger filter keeps strictly fewer elements. -/
theorem length_filter_lt {α : Type u} {l : List α} {p q : α → Bool}
    (hpq : ∀ x, p x = true → q x = true) {z : α} (hz : z ∈ l) (hq : q z = true)
    (hp : p z = false) : (l.filter p).length < (l.filter q).length := by
  have e : l.filter p = (l.filter q).filter p := by
    rw [List.filter_filter]
    congr 1
    funext x
    cases h : p x
    · rfl
    · simp [hpq x h]
  rw [e, List.length_filter_lt_length_iff_exists]
  exact ⟨z, List.mem_filter.2 ⟨hz, hq⟩, by simp [hp]⟩

theorem transGen_of_isChain {α : Type u} {R : α → α → Prop} :
    ∀ {a b : α} {rest : List α}, List.IsChain R (a :: rest ++ [b]) → TransGen R a b
  | _, _, [], h => .single (List.isChain_pair.1 h)
  | _, _, _ :: _, h => by
      rw [List.cons_append, List.cons_append, List.isChain_cons_cons] at h
      exact .head h.1 (transGen_of_isChain (by simpa using h.2))

/-- Appending one element to a chain. -/
theorem isChain_append_singleton {α : Type u} {R : α → α → Prop} {b : α} :
    ∀ {l : List α}, List.IsChain R l → (∀ x ∈ l.getLast?, R x b) → List.IsChain R (l ++ [b])
  | [], _, _ => List.isChain_singleton b
  | [a], _, h => List.isChain_pair.2 (h a rfl)
  | _ :: _ :: _, hc, h => by
      rw [List.cons_append, List.cons_append]
      exact List.isChain_cons_cons.2 ⟨(List.isChain_cons_cons.1 hc).1,
        by rw [← List.cons_append]; exact isChain_append_singleton (List.isChain_cons_cons.1 hc).2 h⟩

/-- The first occurrence of each element, in order. -/
def firstOccurrences {α : Type u} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (firstOccurrences xs).filter fun y => decide (y ≠ x)

theorem mem_firstOccurrences {α : Type u} [DecidableEq α] {x : α} :
    ∀ {l : List α}, x ∈ firstOccurrences l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
      rw [firstOccurrences, List.mem_cons, List.mem_cons, List.mem_filter, mem_firstOccurrences]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact .inl h
        · exact .inr h
      · intro h
        by_cases hx : x = a
        · exact .inl hx
        · exact .inr ⟨h.resolve_left hx, decide_eq_true hx⟩

theorem nodup_firstOccurrences {α : Type u} [DecidableEq α] :
    ∀ l : List α, (firstOccurrences l).Nodup
  | [] => List.nodup_nil
  | _ :: l => List.nodup_cons.2
      ⟨fun h => of_decide_eq_true (List.mem_filter.1 h).2 rfl,
        (nodup_firstOccurrences l).filter _⟩

namespace Catalogue

variable {α : Type u} [DecidableEq α] (c : Catalogue α)

/-- The catalogue item `x` lists `y` among its dependencies. -/
def Uses (x y : α) : Prop := x ∈ c.items ∧ y ∈ c.deps x

/-! ## Affected items -/

/-- The state of a reverse sweep: the items found so far, and those found in
the last round. -/
structure Sweep (α : Type u) where
  seen : List α
  frontier : List α

/-- Catalogue items outside `seen` that list a frontier item among their
dependencies. -/
def fresh (s : Sweep α) : List α :=
  c.items.filter fun x => decide (x ∉ s.seen ∧ ∃ y ∈ s.frontier, y ∈ c.deps x)

theorem mem_fresh {s : Sweep α} {x : α} :
    x ∈ c.fresh s ↔ x ∈ c.items ∧ x ∉ s.seen ∧ ∃ y ∈ s.frontier, y ∈ c.deps x := by
  simp only [fresh, List.mem_filter, decide_eq_true_eq]

/-- The number of catalogue items outside `seen`. -/
def unseen (seen : List α) : ℕ := (c.items.filter fun x => decide (x ∉ seen)).length

theorem unseen_lt {s : Sweep α} (h : c.fresh s ≠ []) :
    c.unseen (s.seen ++ c.fresh s) < c.unseen s.seen := by
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hzi, hzs, -⟩ := c.mem_fresh.1 hz
  refine length_filter_lt (fun x hx => ?_) hzi (by simpa using hzs) (by simp [hz])
  simp only [decide_eq_true_eq, List.mem_append, not_or] at hx ⊢
  exact hx.1

/-- One round of the reverse sweep. -/
def sweep : MeasuredLoop (Sweep α) (List α) where
  measure s := c.unseen s.seen
  step s :=
    if h : c.fresh s = [] then .inr s.seen
    else .inl ⟨⟨s.seen ++ c.fresh s, c.fresh s⟩, c.unseen_lt h⟩

/-- **Affected items**: the changed items and everything that depends on one
of them, directly or not. -/
def affected (changed : List α) : List α := c.sweep.run ⟨changed, changed⟩

/-- The same service through the accessibility route. -/
def affectedAcc (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) : List α :=
  c.sweep.loopAcc I ⟨changed, changed⟩

theorem affectedAcc_eq (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) : c.affectedAcc I changed = c.affected changed :=
  c.sweep.loopAcc_eq_run I _

theorem sweep_inl {s s' : Sweep α} {hs : c.sweep.measure s' < c.sweep.measure s}
    (e : c.sweep.step s = .inl ⟨s', hs⟩) : s' = ⟨s.seen ++ c.fresh s, c.fresh s⟩ := by
  simp only [sweep] at e
  by_cases h : c.fresh s = []
  · rw [dif_pos h] at e; cases e
  · rw [dif_neg h] at e
    exact (congrArg Subtype.val (Sum.inl.inj e)).symm

theorem sweep_inr {s : Sweep α} {b : List α} (e : c.sweep.step s = .inr b) :
    c.fresh s = [] ∧ b = s.seen := by
  simp only [sweep] at e
  by_cases h : c.fresh s = []
  · rw [dif_pos h] at e
    simp only [Sum.inr.injEq] at e
    exact ⟨h, e.symm⟩
  · rw [dif_neg h] at e; cases e

/-- The invariant of the sweep from `changed`. -/
structure SweepInv (changed : List α) (s : Sweep α) : Prop where
  changed_seen : ∀ y ∈ changed, y ∈ s.seen
  seen_reach : ∀ x ∈ s.seen, ∃ y ∈ changed, ReflTransGen c.Uses x y
  frontier_seen : ∀ x ∈ s.frontier, x ∈ s.seen
  closed : ∀ x z, c.Uses x z → z ∈ s.seen → z ∉ s.frontier → x ∈ s.seen

omit [DecidableEq α] in
theorem sweepInv_start (changed : List α) : c.SweepInv changed ⟨changed, changed⟩ where
  changed_seen _ h := h
  seen_reach x h := ⟨x, h, .refl⟩
  frontier_seen _ h := h
  closed _ _ _ hz hf := absurd hz hf

theorem sweepInv_step {changed : List α} {s : Sweep α} (inv : c.SweepInv changed s) :
    c.SweepInv changed ⟨s.seen ++ c.fresh s, c.fresh s⟩ where
  changed_seen y h := List.mem_append_left _ (inv.changed_seen y h)
  seen_reach x h := by
    rcases List.mem_append.1 h with h | h
    · exact inv.seen_reach x h
    · obtain ⟨hx, -, y, hy, hd⟩ := c.mem_fresh.1 h
      obtain ⟨w, hw, r⟩ := inv.seen_reach y (inv.frontier_seen y hy)
      exact ⟨w, hw, .head ⟨hx, hd⟩ r⟩
  frontier_seen _ h := List.mem_append_right _ h
  closed x z hu hz hf := by
    have hz' : z ∈ s.seen := by
      rcases List.mem_append.1 hz with h | h
      · exact h
      · exact absurd h hf
    by_cases hzf : z ∈ s.frontier
    · by_cases hx : x ∈ s.seen
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (c.mem_fresh.2 ⟨hu.1, hx, z, hzf, hu.2⟩)
    · exact List.mem_append_left _ (inv.closed x z hu hz' hzf)

theorem sweepInv_stop {changed : List α} {s : Sweep α} (inv : c.SweepInv changed s)
    (h : c.fresh s = []) (x : α) : x ∈ s.seen ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y := by
  refine ⟨inv.seen_reach x, ?_⟩
  rintro ⟨y, hy, r⟩
  have closed : ∀ a b, c.Uses a b → b ∈ s.seen → a ∈ s.seen := by
    intro a b hu hb
    by_cases hbf : b ∈ s.frontier
    · by_cases ha : a ∈ s.seen
      · exact ha
      · have : a ∈ c.fresh s := c.mem_fresh.2 ⟨hu.1, ha, b, hbf, hu.2⟩
        rw [h] at this
        exact absurd this List.not_mem_nil
    · exact inv.closed a b hu hb hbf
  induction r using ReflTransGen.head_induction_on with
  | refl => exact inv.changed_seen y hy
  | head hu _ ih => exact closed _ _ hu ih

/-- **Affected = reverse-reachable.** -/
theorem mem_affected (changed : List α) (x : α) :
    x ∈ c.affected changed ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y :=
  c.sweep.run_induction (c.SweepInv changed)
    (fun r => ∀ x, x ∈ r ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y)
    (fun _ _ _ inv e => c.sweep_inl e ▸ c.sweepInv_step inv)
    (fun _ _ inv e => (c.sweep_inr e).2 ▸ c.sweepInv_stop inv (c.sweep_inr e).1)
    _ (c.sweepInv_start changed) x

/-- The same characterization through the accessibility route, proved from
the unfolding alone. -/
theorem mem_affectedAcc
    (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) (x : α) :
    x ∈ c.affectedAcc I changed ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y :=
  c.sweep.loopAcc_induction I (c.SweepInv changed)
    (fun r => ∀ x, x ∈ r ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y)
    (fun _ _ _ inv e => c.sweep_inl e ▸ c.sweepInv_step inv)
    (fun _ _ inv e => (c.sweep_inr e).2 ▸ c.sweepInv_stop inv (c.sweep_inr e).1)
    _ (c.sweepInv_start changed) x

/-! ## Rebuild schedule -/

/-- The result of scheduling: parallel rebuild waves, or a blocked set. -/
inductive Schedule (α : Type u) where
  | waves (layers : List (List α))
  | blocked (items : List α)
  deriving DecidableEq, Repr

/-- The state of Kahn's algorithm: the waves so far and the pending targets. -/
structure Plan (α : Type u) where
  layers : List (List α)
  remaining : List α

/-- Pending items none of whose dependencies is pending. -/
def ready (remaining : List α) : List α :=
  remaining.filter fun x => decide (∀ y ∈ c.deps x, y ∉ remaining)

theorem mem_ready {remaining : List α} {x : α} :
    x ∈ c.ready remaining ↔ x ∈ remaining ∧ ∀ y ∈ c.deps x, y ∉ remaining := by
  simp only [ready, List.mem_filter, decide_eq_true_eq]

theorem remaining_lt {remaining : List α} (h : c.ready remaining ≠ []) :
    (remaining.filter fun x => decide (x ∉ c.ready remaining)).length < remaining.length := by
  rw [List.length_filter_lt_length_iff_exists]
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨z, (c.mem_ready.1 hz).1, by simpa using hz⟩

/-- One round of Kahn's algorithm: emit the ready items as a wave. -/
def kahn : MeasuredLoop (Plan α) (Schedule α) where
  measure p := p.remaining.length
  step p :=
    if p.remaining = [] then .inr (.waves p.layers)
    else if h : c.ready p.remaining = [] then .inr (.blocked p.remaining)
    else .inl ⟨⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩, c.remaining_lt h⟩

/-- **Rebuild schedule** for a list of targets. -/
def schedule (target : List α) : Schedule α := c.kahn.run ⟨[], firstOccurrences target⟩

/-- The same service through the accessibility route. -/
def scheduleAcc (I : InertRecursor.{u + 1, u + 1} fun y x => c.kahn.measure y < c.kahn.measure x)
    (target : List α) : Schedule α :=
  c.kahn.loopAcc I ⟨[], firstOccurrences target⟩

theorem scheduleAcc_eq (I : InertRecursor.{u + 1, u + 1} fun y x => c.kahn.measure y < c.kahn.measure x)
    (target : List α) : c.scheduleAcc I target = c.schedule target :=
  c.kahn.loopAcc_eq_run I _

/-- `order` lists each item once, and no item depends on itself or on a later
item. -/
structure Respects (order : List α) : Prop where
  nodup : order.Nodup
  pairwise : order.Pairwise fun a b => b ∉ c.deps a
  irrefl : ∀ x ∈ order, x ∉ c.deps x

/-- A blocked set: nonempty, and each member depends on a member. -/
structure Blocked (B : List α) : Prop where
  ne_nil : B ≠ []
  closed : ∀ x ∈ B, ∃ y ∈ c.deps x, y ∈ B

/-- What a schedule for `target` guarantees. -/
def ScheduleSpec (target : List α) : Schedule α → Prop
  | .waves layers =>
      (∀ x, x ∈ layers.flatten ↔ x ∈ target) ∧ c.Respects layers.flatten ∧ ∀ w ∈ layers, w ≠ []
  | .blocked B => c.Blocked B ∧ ∀ x ∈ B, x ∈ target

/-- The invariant of Kahn's algorithm for `target`. -/
structure PlanInv (target : List α) (p : Plan α) : Prop where
  cover : ∀ x, x ∈ target ↔ x ∈ p.layers.flatten ∨ x ∈ p.remaining
  disjoint : ∀ x ∈ p.layers.flatten, x ∉ p.remaining
  nodup_done : p.layers.flatten.Nodup
  nodup_remaining : p.remaining.Nodup
  pairwise : p.layers.flatten.Pairwise fun a b => b ∉ c.deps a
  irrefl : ∀ x ∈ p.layers.flatten, x ∉ c.deps x
  settled : ∀ x ∈ p.layers.flatten, ∀ y ∈ c.deps x, y ∉ p.remaining
  nonempty : ∀ w ∈ p.layers, w ≠ []

theorem planInv_start (target : List α) : c.PlanInv target ⟨[], firstOccurrences target⟩ where
  cover _ := ⟨fun h => .inr (mem_firstOccurrences.2 h),
    fun h => h.elim (fun h => absurd h List.not_mem_nil) mem_firstOccurrences.1⟩
  disjoint _ h := absurd h List.not_mem_nil
  nodup_done := List.nodup_nil
  nodup_remaining := nodup_firstOccurrences target
  pairwise := List.Pairwise.nil
  irrefl _ h := absurd h List.not_mem_nil
  settled _ h := absurd h List.not_mem_nil
  nonempty _ h := absurd h List.not_mem_nil

theorem planInv_step {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h : c.ready p.remaining ≠ []) :
    c.PlanInv target ⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩ := by
  have hY : ∀ {x}, x ∈ c.ready p.remaining → x ∈ p.remaining := fun hx => (c.mem_ready.1 hx).1
  have hR' : ∀ {x}, x ∈ p.remaining.filter (fun x => decide (x ∉ c.ready p.remaining)) ↔
      x ∈ p.remaining ∧ x ∉ c.ready p.remaining := by
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
  have hF : (p.layers ++ [c.ready p.remaining]).flatten = p.layers.flatten ++ c.ready p.remaining := by
    simp
  refine
    { cover := fun x => ?_, disjoint := fun x hx => ?_, nodup_done := ?_,
      nodup_remaining := inv.nodup_remaining.filter _, pairwise := ?_,
      irrefl := fun x hx => ?_, settled := fun x hx y hy => ?_, nonempty := fun w hw => ?_ } <;>
    dsimp only at * <;> simp only [hF] at *
  · rw [inv.cover x, List.mem_append, hR']
    constructor
    · rintro (hx | hx)
      · exact .inl (.inl hx)
      · by_cases hy : x ∈ c.ready p.remaining
        · exact .inl (.inr hy)
        · exact .inr ⟨hx, hy⟩
    · rintro ((hx | hx) | hx)
      · exact .inl hx
      · exact .inr (hY hx)
      · exact .inr hx.1
  · rw [hR']
    rcases List.mem_append.1 hx with hx | hx
    · exact fun h' => inv.disjoint x hx h'.1
    · exact fun h' => h'.2 hx
  · refine List.nodup_append.2 ⟨inv.nodup_done, inv.nodup_remaining.filter _, ?_⟩
    rintro a ha b hb rfl
    exact inv.disjoint a ha (hY hb)
  · refine List.pairwise_append.2 ⟨inv.pairwise, ?_, ?_⟩
    · exact List.pairwise_of_forall_mem_list fun a ha b hb hd =>
        (c.mem_ready.1 ha).2 b hd (hY hb)
    · exact fun a ha b hb hd => inv.settled a ha b hd (hY hb)
  · rcases List.mem_append.1 hx with hx | hx
    · exact inv.irrefl x hx
    · exact fun hd => (c.mem_ready.1 hx).2 x hd (hY hx)
  · rw [hR']
    rcases List.mem_append.1 hx with hx | hx
    · exact fun h' => inv.settled x hx y hy h'.1
    · exact fun h' => (c.mem_ready.1 hx).2 y hy h'.1
  · rcases List.mem_append.1 hw with hw | hw
    · exact inv.nonempty w hw
    · rw [List.mem_singleton.1 hw]; exact h

omit [DecidableEq α] in
theorem planInv_waves {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h : p.remaining = []) : c.ScheduleSpec target (.waves p.layers) :=
  ⟨fun x => by rw [inv.cover x, h]; simp, ⟨inv.nodup_done, inv.pairwise, inv.irrefl⟩, inv.nonempty⟩

theorem planInv_blocked {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h0 : p.remaining ≠ []) (h : c.ready p.remaining = []) :
    c.ScheduleSpec target (.blocked p.remaining) := by
  refine ⟨⟨h0, fun x hx => ?_⟩, fun x hx => (inv.cover x).2 (.inr hx)⟩
  refine Decidable.byContradiction fun hn => ?_
  have hx' : x ∈ c.ready p.remaining :=
    c.mem_ready.2 ⟨hx, fun y hy hyR => hn ⟨y, hy, hyR⟩⟩
  rw [h] at hx'
  exact List.not_mem_nil hx'

theorem kahn_inl {p p' : Plan α} {hs : c.kahn.measure p' < c.kahn.measure p}
    (e : c.kahn.step p = .inl ⟨p', hs⟩) :
    c.ready p.remaining ≠ [] ∧ p' = ⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩ := by
  simp only [kahn] at e
  by_cases h0 : p.remaining = []
  · rw [if_pos h0] at e; cases e
  · rw [if_neg h0] at e
    by_cases h : c.ready p.remaining = []
    · rw [dif_pos h] at e; cases e
    · rw [dif_neg h] at e
      exact ⟨h, (congrArg Subtype.val (Sum.inl.inj e)).symm⟩

theorem kahn_inr {target : List α} {p : Plan α} {b : Schedule α} (inv : c.PlanInv target p)
    (e : c.kahn.step p = .inr b) : c.ScheduleSpec target b := by
  simp only [kahn] at e
  by_cases h0 : p.remaining = []
  · rw [if_pos h0] at e
    simp only [Sum.inr.injEq] at e
    exact e ▸ c.planInv_waves inv h0
  · rw [if_neg h0] at e
    by_cases h : c.ready p.remaining = []
    · rw [dif_pos h] at e
      simp only [Sum.inr.injEq] at e
      exact e ▸ c.planInv_blocked inv h0 h
    · rw [dif_neg h] at e; cases e

/-- **The schedule is correct.** -/
theorem schedule_spec (target : List α) : c.ScheduleSpec target (c.schedule target) :=
  c.kahn.run_induction (c.PlanInv target) (c.ScheduleSpec target)
    (fun _ _ _ inv e => (c.kahn_inl e).2 ▸ c.planInv_step inv (c.kahn_inl e).1)
    (fun _ _ inv e => c.kahn_inr inv e) _ (c.planInv_start target)

/-! ## Orders and cycles -/

/-- A closed walk along dependencies. -/
def IsCycle (w : List α) : Prop :=
  ∃ a rest, w = a :: rest ∧ List.IsChain c.Uses (a :: rest ++ [a])

/-- The measure given by a rebuild order: one more than the position, and zero
outside the catalogue. -/
def orderMeasure (order : List α) (x : α) : ℕ :=
  if x ∈ c.items then order.idxOf x + 1 else 0

section

variable {c}

omit [DecidableEq α] in
theorem IsCycle.transGen {w : List α} (h : c.IsCycle w) : ∃ a, TransGen c.Uses a a := by
  obtain ⟨a, rest, -, hc⟩ := h
  exact ⟨a, transGen_of_isChain hc⟩

/-- In a respecting order, a dependency comes first. -/
theorem Respects.idxOf_lt {order : List α} (h : c.Respects order) {x y : α} (hx : x ∈ order)
    (hy : y ∈ order) (hd : y ∈ c.deps x) : order.idxOf y < order.idxOf x := by
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  rcases lt_trichotomy (order.idxOf y) (order.idxOf x) with hlt | heq | hgt
  · exact hlt
  · have ey : order[order.idxOf y]? = some y :=
      (List.getElem?_eq_getElem hy').trans (congrArg some (List.getElem_idxOf hy'))
    have ex : order[order.idxOf x]? = some x :=
      (List.getElem?_eq_getElem hx').trans (congrArg some (List.getElem_idxOf hx'))
    rw [heq, ex] at ey
    cases ey
    exact absurd hd (h.irrefl _ hx)
  · have := List.pairwise_iff_getElem.1 h.pairwise _ _ hx' hy' hgt
    rw [List.getElem_idxOf, List.getElem_idxOf] at this
    exact absurd hd this

theorem Respects.orderMeasure_lt {order : List α} (h : c.Respects order)
    (hcov : ∀ x ∈ c.items, x ∈ order) {x y : α} (hu : c.Uses x y) :
    c.orderMeasure order y < c.orderMeasure order x := by
  unfold orderMeasure
  rw [if_pos hu.1]
  by_cases hy : y ∈ c.items
  · rw [if_pos hy]
    exact Nat.succ_lt_succ (h.idxOf_lt (hcov x hu.1) (hcov y hy) hu.2)
  · rw [if_neg hy]
    exact Nat.succ_pos _

/-- A respecting order of the whole catalogue excludes dependency cycles. -/
theorem Respects.acyclic {order : List α} (h : c.Respects order)
    (hcov : ∀ x ∈ c.items, x ∈ order) (a : α) : ¬ TransGen c.Uses a a := by
  intro t
  have key : ∀ {x y}, TransGen c.Uses x y → c.orderMeasure order y < c.orderMeasure order x := by
    intro x y t
    induction t with
    | single hu => exact h.orderMeasure_lt hcov hu
    | tail _ hu ih => exact lt_trans (h.orderMeasure_lt hcov hu) ih
  exact lt_irrefl _ (key t)

/-- A blocked set inside a respecting order is impossible. -/
theorem Blocked.not_respects {B order : List α} (hB : c.Blocked B) (h : c.Respects order)
    (hsub : ∀ x ∈ B, x ∈ order) : False := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hB.ne_nil
  have key : ∀ n, ∀ x ∈ B, order.idxOf x < n → False := by
    intro n
    induction n with
    | zero => intro x _ hn; exact Nat.not_lt_zero _ hn
    | succ n ih =>
        intro x hx hn
        obtain ⟨y, hy, hyB⟩ := hB.closed x hx
        exact ih y hyB (Nat.lt_of_lt_of_le (h.idxOf_lt (hsub x hx) (hsub y hyB) hy)
          (Nat.le_of_lt_succ hn))
  exact key _ x hx (Nat.lt_succ_self _)

end

/-! ## Finding a cycle -/

/-- The first member of `B` among the dependencies of `x`. -/
def nextIn (B : List α) (x : α) : Option α := (c.deps x).find? fun y => decide (y ∈ B)

theorem nextIn_spec {B : List α} {x y : α} (h : c.nextIn B x = some y) :
    y ∈ c.deps x ∧ y ∈ B :=
  ⟨List.mem_of_find?_eq_some (p := fun y => decide (y ∈ B)) h,
    of_decide_eq_true (List.find?_some (p := fun y => decide (y ∈ B)) (l := c.deps x) h)⟩

theorem nextIn_ne_none {B : List α} {x y : α} (hy : y ∈ c.deps x) (hyB : y ∈ B) :
    c.nextIn B x ≠ none := fun h =>
  (List.find?_eq_none (p := fun y => decide (y ∈ B)) (l := c.deps x)).1 h y hy (decide_eq_true hyB)

/-- One step of the walk inside `B`: follow the first dependency in `B`, and
close the cycle when an item repeats. The path is kept reversed. -/
def walkStep (B : List α) : (path : List α) →
    {p : List α // (B.filter fun x => decide (x ∉ p)).length <
      (B.filter fun x => decide (x ∉ path)).length} ⊕ List α
  | [] => .inr []
  | x :: rest =>
      match h : c.nextIn B x with
      | none => .inr []
      | some y =>
          if hy : y ∈ x :: rest then .inr (cycleAt y (x :: rest))
          else .inl ⟨y :: x :: rest, length_filter_lt (fun z hz => by
              simp only [decide_eq_true_eq, List.mem_cons, not_or] at hz ⊢
              exact ⟨hz.2.1, hz.2.2⟩)
            (c.nextIn_spec h).2 (by simpa using hy) (by simp)⟩

/-- The walk as a measured loop. -/
def walk (B : List α) : MeasuredLoop (List α) (List α) where
  measure path := (B.filter fun x => decide (x ∉ path)).length
  step := c.walkStep B

/-- **A cycle through a blocked set.** -/
def findCycle (B : List α) : List α :=
  match B with
  | [] => []
  | x :: _ => (c.walk B).run [x]

/-- The invariant of the walk: a nonempty reversed walk inside `B`. -/
structure WalkInv (B path : List α) : Prop where
  ne_nil : path ≠ []
  sub : ∀ x ∈ path, x ∈ B
  chain : List.IsChain (fun a b => c.Uses b a) path

omit [DecidableEq α] in
theorem walkInv_start {B : List α} {x : α} (hx : x ∈ B) : c.WalkInv B [x] where
  ne_nil := List.cons_ne_nil _ _
  sub z h := by rw [List.mem_singleton.1 h]; exact hx
  chain := List.isChain_singleton _

theorem cycleAt_spec {y : α} :
    ∀ {path : List α}, List.IsChain (fun a b => c.Uses b a) path → y ∈ path →
      ∃ rest, cycleAt y path = y :: rest ∧ List.IsChain c.Uses (cycleAt y path) ∧
        (cycleAt y path).getLast? = path.head? ∧ ∀ z ∈ cycleAt y path, z ∈ path
  | [], _, hy => absurd hy List.not_mem_nil
  | a :: l, hc, hy => by
      by_cases ha : a = y
      · subst ha
        have e : cycleAt a (a :: l) = [a] := by simp [cycleAt]
        rw [e]
        refine ⟨[], rfl, List.isChain_singleton _, by simp, ?_⟩
        intro z hz
        rw [List.mem_singleton.1 hz]
        exact List.mem_cons_self
      · have hyl : y ∈ l := (List.mem_cons.1 hy).resolve_left (Ne.symm ha)
        obtain ⟨b, l', rfl⟩ : ∃ b l', l = b :: l' :=
          List.exists_cons_of_ne_nil (List.ne_nil_of_mem hyl)
        have hab : c.Uses b a := (List.isChain_cons_cons.1 hc).1
        obtain ⟨rest, e, hch, hlast, hmem⟩ := cycleAt_spec (List.isChain_cons_cons.1 hc).2 hyl
        have e' : cycleAt y (a :: b :: l') = cycleAt y (b :: l') ++ [a] := by
          simp only [cycleAt, if_neg ha]
        rw [e']
        refine ⟨rest ++ [a], by rw [e]; rfl, ?_, ?_, ?_⟩
        · refine isChain_append_singleton hch fun u hu => ?_
          rw [hlast, List.head?_cons, Option.mem_some_iff] at hu
          rw [← hu]
          exact hab
        · rw [List.getLast?_append, List.getLast?_singleton, List.head?_cons]
          rfl
        · intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · exact List.mem_cons_of_mem _ (hmem z hz)
          · rw [List.mem_singleton.1 hz]
            exact List.mem_cons_self

theorem walk_inl {B path path' : List α}
    {hs : (c.walk B).measure path' < (c.walk B).measure path}
    (hBI : ∀ x ∈ B, x ∈ c.items) (inv : c.WalkInv B path)
    (e : (c.walk B).step path = .inl ⟨path', hs⟩) : c.WalkInv B path' := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil inv.ne_nil
  simp only [walk, walkStep] at e
  split at e
  · cases e
  · rename_i y h
    by_cases hy : y ∈ x :: rest
    · rw [dif_pos hy] at e; cases e
    · rw [dif_neg hy] at e
      have e' := congrArg Subtype.val (Sum.inl.inj e)
      dsimp only at e'
      subst e'
      obtain ⟨hd, hyB⟩ := c.nextIn_spec h
      refine ⟨List.cons_ne_nil _ _, fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hyB
        · exact inv.sub z hz
      · exact List.isChain_cons_cons.2 ⟨⟨hBI x (inv.sub x List.mem_cons_self), hd⟩, inv.chain⟩

theorem walk_inr {B path w : List α} (hB : c.Blocked B) (hBI : ∀ x ∈ B, x ∈ c.items)
    (inv : c.WalkInv B path) (e : (c.walk B).step path = .inr w) :
    c.IsCycle w ∧ ∀ z ∈ w, z ∈ B := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil inv.ne_nil
  simp only [walk, walkStep] at e
  split at e
  · rename_i h
    obtain ⟨y, hy, hyB⟩ := hB.closed x (inv.sub x List.mem_cons_self)
    exact absurd h (c.nextIn_ne_none hy hyB)
  · rename_i y h
    by_cases hy : y ∈ x :: rest
    · rw [dif_pos hy] at e
      have e' := Sum.inr.inj e
      subst e'
      obtain ⟨hd, -⟩ := c.nextIn_spec h
      obtain ⟨rest', e, hch, hlast, hmem⟩ := c.cycleAt_spec inv.chain hy
      refine ⟨⟨y, rest', e, ?_⟩, fun z hz => inv.sub z (hmem z hz)⟩
      rw [← e]
      refine isChain_append_singleton hch fun u hu => ?_
      rw [hlast, List.head?_cons, Option.mem_some_iff] at hu
      rw [← hu]
      exact ⟨hBI x (inv.sub x List.mem_cons_self), hd⟩
    · rw [dif_neg hy] at e; cases e

/-- **The cycle found through a blocked set is a cycle inside it.** -/
theorem findCycle_spec {B : List α} (hB : c.Blocked B) (hBI : ∀ x ∈ B, x ∈ c.items) :
    c.IsCycle (c.findCycle B) ∧ ∀ z ∈ c.findCycle B, z ∈ B := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hB.ne_nil
  exact (c.walk _).run_induction (c.WalkInv (x :: rest))
    (fun w => c.IsCycle w ∧ ∀ z ∈ w, z ∈ x :: rest)
    (fun _ _ _ inv e => c.walk_inl hBI inv e) (fun _ _ inv e => c.walk_inr hB hBI inv e)
    _ (c.walkInv_start List.mem_cons_self)

/-- **Cycle detection** over the whole catalogue. -/
def cycle? : Option (List α) :=
  match c.schedule c.items with
  | .waves _ => none
  | .blocked B => some (c.findCycle B)

theorem cycle?_sound {w : List α} (h : c.cycle? = some w) :
    c.IsCycle w ∧ ∀ z ∈ w, z ∈ c.items := by
  unfold cycle? at h
  have spec := c.schedule_spec c.items
  split at h
  · cases h
  · rename_i B hs
    cases h
    rw [hs] at spec
    obtain ⟨hB, hsub⟩ := spec
    obtain ⟨hc, hm⟩ := c.findCycle_spec hB hsub
    exact ⟨hc, fun z hz => hsub z (hm z hz)⟩

theorem cycle?_none (h : c.cycle? = none) (a : α) : ¬ TransGen c.Uses a a := by
  unfold cycle? at h
  have spec := c.schedule_spec c.items
  split at h
  · rename_i ws hs
    rw [hs] at spec
    obtain ⟨hcov, hresp, -⟩ := spec
    exact hresp.acyclic (fun x hx => (hcov x).2 hx) a
  · cases h

/-- **Cycle detection is sound and complete.** -/
theorem cycle?_isSome_iff : c.cycle?.isSome ↔ ∃ a, TransGen c.Uses a a := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
    exact (c.cycle?_sound hw).1.transGen
  · rintro ⟨a, t⟩
    cases hc : c.cycle? with
    | none => exact absurd t (c.cycle?_none hc a)
    | some w => rfl

/-! ## Recursion over dependencies -/

/-- An acyclicity certificate: a rebuild order of the whole catalogue. -/
structure Acyclic where
  order : List α
  respects : c.Respects order
  covers : ∀ x ∈ c.items, x ∈ order

/-- The certificate from the schedule of the whole catalogue, when there is
one. -/
def acyclic? : Option c.Acyclic :=
  match h : c.schedule c.items with
  | .waves ws =>
      have spec : c.ScheduleSpec c.items (.waves ws) := h ▸ c.schedule_spec c.items
      some ⟨ws.flatten, spec.2.1, fun x hx => (spec.1 x).2 hx⟩
  | .blocked _ => none

theorem acyclic?_isSome_iff : c.acyclic?.isSome ↔ ∀ a, ¬ TransGen c.Uses a a := by
  constructor
  · intro h a
    obtain ⟨A, -⟩ := Option.isSome_iff_exists.1 h
    exact A.respects.acyclic A.covers a
  · intro h
    have hc : c.cycle? = none := by
      cases hc : c.cycle? with
      | none => rfl
      | some w =>
          obtain ⟨a, t⟩ := (c.cycle?_sound hc).1.transGen
          exact absurd t (h a)
    unfold cycle? at hc
    unfold acyclic?
    split
    · rfl
    · rename_i B hs
      rw [hs] at hc
      cases hc

namespace Acyclic

variable {c}

/-- **Every item is accessible** for the dependency relation of an acyclic
catalogue. -/
theorem accCode (A : c.Acyclic) (x : α) : AccCode (fun y x => c.Uses x y) x :=
  (accCode_measure (c.orderMeasure A.order) x).mono fun _ _ hu =>
    A.respects.orderMeasure_lt A.covers hu

/-- **Measure-based recursion over dependencies**, with the rebuild order as
the measure. -/
def recOrder (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (x : α) : C x :=
  recMeasure (c.orderMeasure A.order)
    (fun x ih => F x fun y hy => ih y (A.respects.orderMeasure_lt A.covers hy)) x

theorem recOrder_eq (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (x : α) : A.recOrder F x = F x fun y _ => A.recOrder F y :=
  recMeasure_eq _ _ x

/-- **Recursion over dependencies through the accessibility route.** -/
def recAcc (A : c.Acyclic) (I : InertRecursor.{u + 1, v} fun y x => c.Uses x y) {C : α → Sort v}
    (F : ∀ x, (∀ y, c.Uses x y → C y) → C x) (x : α) : C x :=
  I.recursor F x (A.accCode x)

/-- **Agreement.** -/
theorem recAcc_eq (A : c.Acyclic) (I : InertRecursor.{u + 1, v} fun y x => c.Uses x y)
    {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x) (x : α) :
    A.recAcc I F x = A.recOrder F x :=
  I.rec_eq_of_fix F (A.recOrder F) (A.recOrder_eq F) _

/-- **Uniqueness**: every function satisfying the recursion equation is the
recursion. -/
theorem eq_recOrder (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (g : ∀ x, C x) (hg : ∀ x, g x = F x fun y _ => g y) (x : α) : g x = A.recOrder F x := by
  rw [← A.recAcc_eq (InertRecursor.ofAcc _) F x]
  exact ((InertRecursor.ofAcc _).rec_eq_of_fix F g hg _).symm

/-- **Locality**: two recursions agree on a set closed under dependencies on
which their steps agree. -/
theorem recOrder_congr (A : c.Acyclic) {C : α → Sort v}
    (F₁ F₂ : ∀ x, (∀ y, c.Uses x y → C y) → C x) (S : α → Prop)
    (hS : ∀ x y, S x → c.Uses x y → S y)
    (hF : ∀ x, S x → ∀ k₁ k₂ : ∀ y, c.Uses x y → C y, (∀ y h, k₁ y h = k₂ y h) →
      F₁ x k₁ = F₂ x k₂) (x : α) (hx : S x) : A.recOrder F₁ x = A.recOrder F₂ x := by
  induction acc_of_accCode (A.accCode x) with
  | intro x _ ih =>
      rw [A.recOrder_eq F₁, A.recOrder_eq F₂]
      exact hF x hx _ _ fun y h => ih y h (hS x y hx h)

end Acyclic

/-! ## Folds over dependencies -/

/-- One step of a dependency fold: combine an item with the values at its
dependencies, in the order the catalogue lists them. -/
def foldStep {β : Type v} (f : α → List β → β) (x : α) (k : ∀ y, c.Uses x y → β) : β :=
  if hx : x ∈ c.items then f x ((c.deps x).attach.map fun y => k y.1 ⟨hx, y.2⟩) else f x []

/-- **A dependency fold**: the value at an item combines the item with the
values at its dependencies. Derivation keys, critical-path lengths and
transitive input lists are instances. -/
def depFold (A : c.Acyclic) {β : Type v} (f : α → List β → β) : α → β :=
  A.recOrder (c.foldStep f)

/-- The same fold through the accessibility route. -/
def depFoldAcc (A : c.Acyclic) (I : InertRecursor.{u + 1, v + 1} fun y x => c.Uses x y)
    {β : Type v} (f : α → List β → β) : α → β :=
  A.recAcc I (c.foldStep f)

theorem depFoldAcc_eq (A : c.Acyclic) (I : InertRecursor.{u + 1, v + 1} fun y x => c.Uses x y)
    {β : Type v} (f : α → List β → β) (x : α) : c.depFoldAcc A I f x = c.depFold A f x :=
  A.recAcc_eq I _ x

/-- The equation of a dependency fold. -/
theorem depFold_eq (A : c.Acyclic) {β : Type v} (f : α → List β → β) (x : α) :
    c.depFold A f x = f x (if x ∈ c.items then (c.deps x).map (c.depFold A f) else []) := by
  rw [depFold, Acyclic.recOrder_eq]
  unfold foldStep
  by_cases hx : x ∈ c.items
  · rw [dif_pos hx, if_pos hx]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val (c.deps x), List.map_map]
    rfl
  · rw [dif_neg hx, if_neg hx]

/-- Interpret a dependency fold through an algebra morphism, retaining the
listed dependency occurrences and their order. -/
theorem depFold_map (A : c.Acyclic) {β : Type v} {γ : Type w}
    (combine : α → List β → β) (combine' : α → List γ → γ)
    (project : β → γ)
    (hom : ∀ item values, project (combine item values) =
      combine' item (values.map project)) (item : α) :
    project (c.depFold A combine item) = c.depFold A combine' item := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
      rw [c.depFold_eq A combine item, c.depFold_eq A combine' item, hom]
      by_cases admitted : item ∈ c.items
      · simp only [if_pos admitted, List.map_map]
        congr 1
        exact List.map_congr_left fun child member => ih child ⟨admitted, member⟩
      · simp only [if_neg admitted, List.map_nil]


/-- An algebra that preserves a property yields that property for every
computed dependency fold, including items outside the catalogue. -/
theorem depFold_preserves (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (property : β → Prop)
    (closed : ∀ item values, (∀ value ∈ values, property value) → property (combine item values))
    (item : α) : property (c.depFold A combine item) := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
      rw [c.depFold_eq A combine item]
      apply closed
      by_cases admitted : item ∈ c.items
      · simp only [if_pos admitted]
        intro value member
        obtain ⟨child, included, rfl⟩ := List.mem_map.mp member
        exact ih child ⟨admitted, included⟩
      · simp only [if_neg admitted, List.not_mem_nil, false_implies, implies_true]

/-- **Incremental rebuild is sound.** If a fold changes only at changed items,
its values outside the affected set do not change. -/
theorem depFold_eq_of_not_affected (A : c.Acyclic) {β : Type v} (f₁ f₂ : α → List β → β)
    (changed : List α) (hf : ∀ x, x ∉ changed → f₁ x = f₂ x) {x : α}
    (hx : x ∉ c.affected changed) : c.depFold A f₁ x = c.depFold A f₂ x := by
  refine A.recOrder_congr _ _ (fun x => x ∉ c.affected changed) ?_ ?_ x hx
  · intro x y hx hu hy
    obtain ⟨z, hz, r⟩ := (c.mem_affected changed y).1 hy
    exact hx ((c.mem_affected changed x).2 ⟨z, hz, .head hu r⟩)
  · intro x hx k₁ k₂ hk
    have hxc : x ∉ changed := fun h => hx ((c.mem_affected changed x).2 ⟨x, h, .refl⟩)
    unfold foldStep
    rw [hf x hxc]
    split
    · congr 1
      exact List.map_congr_left fun y _ => hk _ _
    · rfl

/-! ## Independent derivations of dependency-fold values -/

/-- A catalogue is closed when every dependency of an admitted item is also
admitted. A missing item cannot silently be treated as a leaf. -/
def DependencyClosed : Prop := ∀ x ∈ c.items, ∀ y ∈ c.deps x, y ∈ c.items

/-- Independent evaluation by the listed dependencies. The premise retains
their order and multiplicity; the computed fold is not a premise. -/
inductive FoldDerivation {β : Type v} (combine : α → List β → β) : α → β → Prop where
  | node {item : α} {values : List β}
      (admitted : item ∈ c.items)
      (children : List.Forall₂ (FoldDerivation combine) (c.deps item) values) :
      FoldDerivation combine item (combine item values)

/-- Forget the fold's values, retaining its admission test and every ordered
dependency. This is the independent finite-success judgment used by the
completed structural-observation cache. -/
def observationGraph :
    Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Graph α :=
  fun item => ⟨decide (item ∈ c.items), c.deps item, true⟩

/-- A dependency derivation supplies a finite successful structural
observation. No global acyclicity certificate is assumed. -/
theorem FoldDerivation.accepted {β : Type v} {combine : α → List β → β}
    {item : α} {value : β} (derived : c.FoldDerivation combine item value) :
    Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      c.observationGraph item := by
  induction derived using FoldDerivation.rec
      (motive_2 := fun dependencies _ _ => ∀ child ∈ dependencies,
        Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
          c.observationGraph child) with
  | node admitted _ children =>
      exact .exit _ (by simpa [observationGraph] using admitted) children
  | nil => contradiction
  | @cons child _ rest _ _ _ first remaining =>
      rename_i selected member
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using first
      · exact remaining selected member

/-- Every dependency below a finite fold derivation is accessible, even if
the catalogue contains cycles elsewhere. -/
theorem FoldDerivation.accessible {β : Type v} {combine : α → List β → β}
    {item : α} {value : β} (derived : c.FoldDerivation combine item value) :
    Acc (fun child parent => child ∈ c.deps parent) item :=
  derived.accepted.accessible

/-- A finite observation propagates down every reachable dependency. -/
theorem FoldDerivation.accepted_of_reachable {β : Type v} {combine : α → List β → β}
    {item node : α} {value : β} (derived : c.FoldDerivation combine item value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ c.deps parent) item node) :
    Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      c.observationGraph node := by
  induction reachable with
  | refl => exact derived.accepted
  | tail _ edge ih => exact ih.child edge

/-- A successful finite fold rules out a cycle anywhere below its root,
without rejecting unrelated cyclic catalogue components. -/
theorem FoldDerivation.no_reachable_cycle {β : Type v} {combine : α → List β → β}
    {item node : α} {value : β} (derived : c.FoldDerivation combine item value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ c.deps parent) item node) :
    ¬ Relation.TransGen (fun child parent => child ∈ c.deps parent) node node :=
  (FoldDerivation.accepted_of_reachable c derived reachable).no_cycle

/-- Every independently derived value agrees with the existing executable
fold. The proof follows the catalogue's established accessibility relation. -/
theorem FoldDerivation.value_eq_depFold (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (item : α) :
    ∀ value, c.FoldDerivation combine item value → value = c.depFold A combine item := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
    intro value derived
    cases derived with
    | node admitted children =>
      have values : ∀ {dependencies values},
          List.Forall₂ (c.FoldDerivation combine) dependencies values →
          (∀ child ∈ dependencies, child ∈ c.deps item) →
          values = dependencies.map (c.depFold A combine) := by
        intro dependencies values derivations
        induction derivations with
        | nil => intro _; rfl
        | @cons child value rest values derivation remaining inductionHypothesis =>
          intro included
          rw [List.map_cons, ih child ⟨admitted, included child List.mem_cons_self⟩ value derivation,
            inductionHypothesis (fun other member => included other (List.mem_cons_of_mem _ member))]
      rw [values children (fun _ member => member), c.depFold_eq A combine item,
        if_pos admitted]

/-- A closed acyclic catalogue derives the executable fold's value at every
admitted item, by the independent judgment. -/
theorem depFold_has_derivation (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (closed : c.DependencyClosed) (item : α)
    (admitted : item ∈ c.items) :
    c.FoldDerivation combine item (c.depFold A combine item) := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
    rw [c.depFold_eq A combine item, if_pos admitted]
    apply FoldDerivation.node admitted
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro child member
    exact ih child ⟨admitted, member⟩ (closed item admitted child member)

theorem foldDerivation_iff (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (closed : c.DependencyClosed)
    (item : α) (admitted : item ∈ c.items) (value : β) :
    c.FoldDerivation combine item value ↔ value = c.depFold A combine item := by
  constructor
  · exact FoldDerivation.value_eq_depFold c A combine item value
  · intro equal
    rw [equal]
    exact c.depFold_has_derivation A combine closed item admitted

/-- Total occurrence work unfolds each dependency occurrence. Memoizing a
child fold does not remove a repeated child's contribution from the sum. -/
abbrev unfoldingWork (A : c.Acyclic) (localWork : α → Nat) : α → Nat :=
  c.depFold A (fun item childWork => localWork item + childWork.sum)

theorem unfoldingWork_eq (A : c.Acyclic) (localWork : α → Nat)
    (item : α) (admitted : item ∈ c.items) :
    c.unfoldingWork A localWork item =
      localWork item + ((c.deps item).map (c.unfoldingWork A localWork)).sum := by
  exact (c.depFold_eq A (fun item childWork => localWork item + childWork.sum) item).trans
    (by rw [if_pos admitted])

end Catalogue

/-! ## Bounded traversal of physical occurrence rows

The traversal stores a completed child's value once, while adding that value
for every distinct referring row. Its independent specification is the
catalogue's existing `FoldDerivation`, not the traversal's own cache.
Source coverage, terminal inertness, and the lifetime of a native graph are
separate adapter obligations. -/

namespace OccurrenceGraph

structure Row where
  physical : Nat
  successor : Option Nat
  deriving DecidableEq, Repr

structure Graph where
  nodes : List (List Row)
  deriving DecidableEq, Repr

def Graph.rows (graph : Graph) (node : Nat) : List Row :=
  (graph.nodes[node]?).getD []

def Graph.catalogue (graph : Graph) : Catalogue Nat where
  items := List.range graph.nodes.length
  deps node := (graph.rows node).filterMap Row.successor

def Graph.combine (graph : Graph) (node : Nat) (children : List Nat) : Nat :=
  (graph.rows node).length + children.sum

open Mettapedia.Algebra

/-- Local equation occurrences plus the independent dependency values.
The second coordinate is source dependency depth. It becomes an execution
span only under a separately established independence/realization contract. -/
def Graph.sourceCombine (graph : Graph) (node : Nat) (children : List WorkSpan) : WorkSpan :=
  WorkSpan.sequential
    ⟨(graph.rows node).length, if (graph.rows node).isEmpty then 0 else 1⟩
    (WorkSpan.parallelAll children)

/-- Scalar depth interpretation, independent of the paired fold. Empty
nodes have depth zero; every applicable equation contributes one layer. -/
def Graph.depthCombine (graph : Graph) (node : Nat) (children : List Nat) : Nat :=
  (if (graph.rows node).isEmpty then 0 else 1) + children.foldr max 0

/-- Interpret the existing occurrence catalogue once in the work/depth algebra. -/
def Graph.sourceValuation (graph : Graph) (acyclic : graph.catalogue.Acyclic) : Nat → WorkSpan :=
  graph.catalogue.depFold acyclic graph.sourceCombine

def Graph.dependencyDepth (graph : Graph) (acyclic : graph.catalogue.Acyclic) : Nat → Nat :=
  graph.catalogue.depFold acyclic graph.depthCombine

@[simp] theorem Graph.sourceCombine_work (graph : Graph) (node : Nat) (children : List WorkSpan) :
    (graph.sourceCombine node children).work = graph.combine node (children.map WorkSpan.work) := by
  simp only [sourceCombine, WorkSpan.sequential, WorkSpan.parallelAll_work, combine]

@[simp] theorem Graph.sourceCombine_depth (graph : Graph) (node : Nat) (children : List WorkSpan) :
    (graph.sourceCombine node children).span = graph.depthCombine node (children.map WorkSpan.span) := by
  simp only [sourceCombine, WorkSpan.sequential, WorkSpan.parallelAll_span, depthCombine]

/-- The paired interpretation counts every referring occurrence, even when
an analyzer memoizes a shared successor. -/
theorem Graph.sourceValuation_work (graph : Graph) (acyclic : graph.catalogue.Acyclic) (node : Nat) :
    (graph.sourceValuation acyclic node).work =
      graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node := by
  exact graph.catalogue.depFold_map acyclic graph.sourceCombine graph.combine WorkSpan.work
    (fun item values => graph.sourceCombine_work item values) node

theorem Graph.sourceValuation_depth (graph : Graph) (acyclic : graph.catalogue.Acyclic) (node : Nat) :
    (graph.sourceValuation acyclic node).span = graph.dependencyDepth acyclic node := by
  exact graph.catalogue.depFold_map acyclic graph.sourceCombine graph.depthCombine WorkSpan.span
    (fun item values => graph.sourceCombine_depth item values) node

theorem Graph.sourceValuation_eq (graph : Graph) (acyclic : graph.catalogue.Acyclic) (node : Nat)
    (admitted : node ∈ graph.catalogue.items) :
    graph.sourceValuation acyclic node = graph.sourceCombine node
      ((graph.catalogue.deps node).map (graph.sourceValuation acyclic)) := by
  change graph.catalogue.depFold acyclic graph.sourceCombine node =
    graph.sourceCombine node ((graph.catalogue.deps node).map
      (graph.catalogue.depFold acyclic graph.sourceCombine))
  rw [graph.catalogue.depFold_eq, if_pos admitted]

theorem Graph.dependencyDepth_eq (graph : Graph) (acyclic : graph.catalogue.Acyclic) (node : Nat)
    (admitted : node ∈ graph.catalogue.items) :
    graph.dependencyDepth acyclic node = graph.depthCombine node
      ((graph.catalogue.deps node).map (graph.dependencyDepth acyclic)) := by
  change graph.catalogue.depFold acyclic graph.depthCombine node =
    graph.depthCombine node ((graph.catalogue.deps node).map
      (graph.catalogue.depFold acyclic graph.depthCombine))
  rw [graph.catalogue.depFold_eq, if_pos admitted]

/-- A closed source catalogue independently derives the paired result;
the computed cache is not an assumption of this judgment. -/
theorem Graph.sourceValuation_derives (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (closed : graph.catalogue.DependencyClosed) (node : Nat)
    (admitted : node ∈ graph.catalogue.items) :
    graph.catalogue.FoldDerivation graph.sourceCombine node (graph.sourceValuation acyclic node) :=
  graph.catalogue.depFold_has_derivation acyclic graph.sourceCombine closed node admitted

private theorem parallelAll_depth_le_work (children : List WorkSpan)
    (within : ∀ child ∈ children, child.span ≤ child.work) :
    (WorkSpan.parallelAll children).span ≤ (WorkSpan.parallelAll children).work := by
  induction children with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      change max head.span (WorkSpan.parallelAll tail).span ≤
        head.work + (WorkSpan.parallelAll tail).work
      apply max_le
      · exact (within head List.mem_cons_self).trans (Nat.le_add_right _ _)
      · exact (ih (fun child member => within child (List.mem_cons_of_mem _ member))).trans
          (Nat.le_add_left _ _)

theorem Graph.sourceCombine_depth_le_work (graph : Graph) (node : Nat) (children : List WorkSpan)
    (within : ∀ child ∈ children, child.span ≤ child.work) :
    (graph.sourceCombine node children).span ≤ (graph.sourceCombine node children).work := by
  have localBound : (if (graph.rows node).isEmpty then 0 else 1) ≤ (graph.rows node).length := by
    cases rows : graph.rows node <;> simp
  exact Nat.add_le_add localBound (parallelAll_depth_le_work children within)

theorem Graph.dependencyDepth_le_unfoldingWork (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (node : Nat) : graph.dependencyDepth acyclic node ≤
      graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node := by
  have bound := graph.catalogue.depFold_preserves acyclic graph.sourceCombine
    (fun value => value.span ≤ value.work)
    (fun item values within => graph.sourceCombine_depth_le_work item values within) node
  change (graph.sourceValuation acyclic node).span ≤
    (graph.sourceValuation acyclic node).work at bound
  rw [graph.sourceValuation_depth, graph.sourceValuation_work] at bound
  exact bound

/-- One physical occurrence row. A terminal row is the unit `⟨1, 1⟩`. A
successor occurrence sequences that unit before the child valuation.
Duplicate successors stay in order; they are not deduplicated. -/
def Row.workDepth (row : Row) : Option WorkSpan → WorkSpan
  | none => ⟨1, 1⟩
  | some value =>
    match row.successor with
    | none => ⟨1, 1⟩
    | some _ => WorkSpan.sequential ⟨1, 1⟩ value

/-- Consume successor valuations in row order. A terminal row takes none. -/
def rowAccounts : List Row → List WorkSpan → List WorkSpan
  | [], _ => []
  | row :: rows, children =>
    match row.successor with
    | none => row.workDepth none :: rowAccounts rows children
    | some _ =>
      match children with
      | [] => row.workDepth none :: rowAccounts rows []
      | child :: rest => row.workDepth (some child) :: rowAccounts rows rest

/-- The number of successor occurrences, with multiplicity. -/
def successorCount (rows : List Row) : Nat :=
  (rows.filterMap Row.successor).length

/-- Ordered row aggregate. Its `span` is source dependency depth of these
rows, not a live worker schedule. `WorkSpan.parallelAll` combines the
alternative occurrence rows. -/
def prefixFold (rows : List Row) (children : List WorkSpan) : WorkSpan :=
  WorkSpan.parallelAll (rowAccounts rows children)

private theorem max_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  rcases Nat.le_total b c with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.add_le_add_left h a)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.add_le_add_left h a)]

private theorem rowAccounts_work (rows : List Row) (children : List WorkSpan) :
    ((rowAccounts rows children).map WorkSpan.work).sum =
      rows.length + ((children.take (successorCount rows)).map WorkSpan.work).sum := by
  induction rows generalizing children with
  | nil => simp [rowAccounts, successorCount]
  | cons row rows ih =>
    cases row with
    | mk _ successor =>
      cases successor with
      | none =>
        simp only [rowAccounts, Row.workDepth, successorCount, List.filterMap_cons,
          List.map_cons, List.sum_cons, List.length_cons, ih]
        omega
      | some _ =>
        cases children with
        | nil =>
          simp only [rowAccounts, Row.workDepth, successorCount, List.filterMap_cons,
            List.map_cons, List.sum_cons, List.length_cons, List.take_nil, List.map_nil,
            List.sum_nil, ih]
          omega
        | cons child children =>
          simp only [rowAccounts, Row.workDepth, WorkSpan.sequential, successorCount,
            List.filterMap_cons, List.map_cons, List.sum_cons, List.length_cons,
            List.take_succ_cons, ih]
          omega

private theorem rowAccounts_terminal (physical : Nat) (rows : List Row)
    (children : List WorkSpan) :
    rowAccounts (⟨physical, none⟩ :: rows) children = ⟨1, 1⟩ :: rowAccounts rows children := rfl

private theorem rowAccounts_linked (physical index : Nat) (rows : List Row)
    (child : WorkSpan) (children : List WorkSpan) :
    rowAccounts (⟨physical, some index⟩ :: rows) (child :: children) =
      WorkSpan.sequential ⟨1, 1⟩ child :: rowAccounts rows children := rfl

private theorem successorCount_terminal (physical : Nat) (rows : List Row) :
    successorCount (⟨physical, none⟩ :: rows) = successorCount rows := by
  simp [successorCount]

private theorem successorCount_linked (physical index : Nat) (rows : List Row) :
    successorCount (⟨physical, some index⟩ :: rows) = successorCount rows + 1 := by
  simp [successorCount, List.length_cons]

private theorem layer_nil : (if ([] : List Row).isEmpty then (0 : Nat) else 1) = 0 := by
  rw [List.isEmpty_nil]; rfl

private theorem layer_cons (row : Row) (rows : List Row) :
    (if (row :: rows).isEmpty then (0 : Nat) else 1) = 1 := by
  rw [List.isEmpty_cons]; rfl

private theorem rowAccounts_span (rows : List Row) (children : List WorkSpan)
    (aligned : children.length = successorCount rows) :
    ((rowAccounts rows children).map WorkSpan.span).foldr max 0 =
      (if rows.isEmpty then 0 else 1) +
        ((children.map WorkSpan.span).foldr max 0) := by
  induction rows generalizing children with
  | nil =>
    rw [layer_nil, rowAccounts]
    cases children with
    | nil => simp
    | cons _ _ => simp [successorCount, List.length_cons] at aligned
  | cons row rows ih =>
    rw [layer_cons]
    cases row with
    | mk physical successor =>
      cases successor with
      | none =>
        have alignedTail : children.length = successorCount rows := by
          simpa only [successorCount_terminal] using aligned
        rw [rowAccounts_terminal, List.map_cons, List.foldr_cons, ih children alignedTail]
        cases rows with
        | nil =>
          rw [layer_nil]
          cases children with
          | nil =>
            simp only [List.map_nil, List.foldr_nil]
            rw [Nat.max_eq_left (Nat.zero_le _)]
          | cons _ _ => simp [successorCount] at alignedTail
        | cons _ _ =>
          rw [layer_cons, Nat.max_eq_right (Nat.le_add_right 1 _)]
      | some index =>
        cases children with
        | nil =>
          simp only [successorCount_linked, List.length_nil] at aligned
          omega
        | cons child children =>
          have alignedTail : children.length = successorCount rows := by
            simpa only [successorCount_linked, List.length_cons, Nat.succ_inj] using aligned
          rw [rowAccounts_linked, List.map_cons, List.foldr_cons, ih children alignedTail]
          change max (1 + child.span)
            ((if rows.isEmpty then 0 else 1) +
              (List.map WorkSpan.span children).foldr max 0) =
            1 + (List.map WorkSpan.span (child :: children)).foldr max 0
          cases rows with
          | nil =>
            rw [layer_nil]
            cases children with
            | nil =>
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
              rw [Nat.max_eq_left (Nat.zero_le _), Nat.max_eq_left (Nat.zero_le _)]
            | cons _ _ => simp [successorCount, List.length_cons] at alignedTail
          | cons _ _ =>
            rw [layer_cons, List.map_cons, List.foldr_cons, max_add_left]

/-- A complete node’s ordered row accounts are the paired source combine.
Successor multiplicity is retained: `children` has one entry per successor
occurrence, not one entry per distinct child. -/
theorem prefixFold_eq_sourceCombine (graph : Graph) (node : Nat) (children : List WorkSpan)
    (aligned : children.length = successorCount (graph.rows node)) :
    prefixFold (graph.rows node) children = graph.sourceCombine node children := by
  ext
  · rw [prefixFold, WorkSpan.parallelAll_work, rowAccounts_work, ← aligned, List.take_length,
      Graph.sourceCombine_work, Graph.combine]
  · rw [prefixFold, WorkSpan.parallelAll_span,
      rowAccounts_span (graph.rows node) children aligned, Graph.sourceCombine_depth,
      Graph.depthCombine]

/-- The same row aggregate is the independent source valuation. Its work is
`unfoldingWork` and its span is `dependencyDepth`, because those are the
projections of `sourceValuation`. -/
theorem prefixFold_sourceValuation (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (node : Nat) (admitted : node ∈ graph.catalogue.items) :
    prefixFold (graph.rows node)
        ((graph.catalogue.deps node).map (graph.sourceValuation acyclic)) =
      graph.sourceValuation acyclic node := by
  have aligned :
      ((graph.catalogue.deps node).map (graph.sourceValuation acyclic)).length =
        successorCount (graph.rows node) := by
    simp only [Graph.catalogue, successorCount, List.length_map]
  rw [prefixFold_eq_sourceCombine graph node _ aligned]
  exact (graph.sourceValuation_eq acyclic node admitted).symm

/-- Retained readout. `.unfolding` is the scalar runner's work sum.
`.depth` is source dependency depth alone. `.pair` keeps both coordinates
of one `WorkSpan` aggregate. -/
inductive Metric where
  | unfolding
  | depth
  | pair
  deriving DecidableEq, Repr

/-- One occurrence account joined into the retained cursor.
`.unfolding` adds work and leaves the depth cursor unchanged, which is the
scalar addition. `.pair` is `WorkSpan.parallel` with that account.
`.depth` keeps the running source-depth maximum in the work coordinate.
A finished node is still `prefixFold`, read by `prefixFold_sourceValuation`. -/
@[reducible] def metricCombine (metric : Metric) (accumulated account : WorkSpan) : WorkSpan :=
  match metric with
  | .unfolding => ⟨accumulated.work + account.work, accumulated.span⟩
  | .depth => ⟨max accumulated.work account.span, accumulated.span⟩
  | .pair => ⟨accumulated.work + account.work, max accumulated.span account.span⟩

theorem metricCombine_unfolding (accumulated account : WorkSpan) :
    metricCombine .unfolding accumulated account =
      ⟨accumulated.work + account.work, accumulated.span⟩ := rfl

theorem metricCombine_depth (accumulated account : WorkSpan) :
    metricCombine .depth accumulated account =
      ⟨max accumulated.work account.span, accumulated.span⟩ := rfl

theorem metricCombine_pair (accumulated account : WorkSpan) :
    metricCombine .pair accumulated account =
      ⟨accumulated.work + account.work, max accumulated.span account.span⟩ := rfl

/-- Appending one occurrence account is `WorkSpan.parallel`. The unfolding
projection adds that account's work and does not read its span. -/
theorem metricCombine_oneRow (accounts : List WorkSpan) (account : WorkSpan) :
    metricCombine .pair (WorkSpan.parallelAll accounts) account =
      WorkSpan.parallelAll (accounts ++ [account]) ∧
      (metricCombine .unfolding (WorkSpan.parallelAll accounts) account).work =
        (WorkSpan.parallelAll (accounts ++ [account])).work := by
  have extended :
      WorkSpan.parallelAll (accounts ++ [account]) =
        WorkSpan.parallel (WorkSpan.parallelAll accounts) account := by
    rw [WorkSpan.parallelAll_append, WorkSpan.parallelAll_cons, WorkSpan.parallelAll_nil,
      WorkSpan.parallel_zero_right]
  refine ⟨?_, ?_⟩
  · rw [extended]
    ext <;> simp [WorkSpan.parallel]
  · rw [extended, metricCombine_unfolding]
    simp [WorkSpan.parallel]

/-- The retained cursor advances one account of a `prefixFold` aggregate.
The finished aggregate is the `prefixFold_sourceValuation` specification. -/
theorem metricCombine_prefixFold (rows : List Row) (children : List WorkSpan)
    (account : WorkSpan) :
    metricCombine .pair (prefixFold rows children) account =
      WorkSpan.parallelAll (rowAccounts rows children ++ [account]) ∧
      (metricCombine .unfolding (prefixFold rows children) account).work =
        (prefixFold rows children).work + account.work := by
  have one := metricCombine_oneRow (rowAccounts rows children) account
  refine ⟨?_, ?_⟩
  · rw [prefixFold]
    exact one.1
  · rw [metricCombine_unfolding]

abbrev Graph.Derived (graph : Graph) : Nat → Nat → Prop :=
  graph.catalogue.FoldDerivation graph.combine

inductive RowValue (graph : Graph) : Row → Nat → Prop where
  | terminal (physical : Nat) : RowValue graph ⟨physical, none⟩ 1
  | linked (physical child value : Nat) (derived : graph.Derived child value) :
      RowValue graph ⟨physical, some child⟩ (1 + value)

/-- Ordered row contributions yield ordered child derivations. Terminal rows
still contribute one, and repeated references are not deduplicated. -/
theorem rows_derive (graph : Graph) {rows : List Row} {values : List Nat}
    (derived : List.Forall₂ (RowValue graph) rows values) :
    ∃ children,
      List.Forall₂ graph.Derived (rows.filterMap Row.successor) children ∧
        values.sum = rows.length + children.sum := by
  induction derived with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons row value rows values rowDerived remaining ih =>
    obtain ⟨children, childDerived, total⟩ := ih
    cases rowDerived with
    | terminal physical =>
      refine ⟨children, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using childDerived
      · simp only [List.sum_cons, List.length_cons]
        omega
    | linked physical child value derived =>
      refine ⟨value :: children, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using
          List.Forall₂.cons derived childDerived
      · simp only [List.sum_cons, List.length_cons]
        omega

structure Frame where
  node : Nat
  row : Nat := 0
  total : Nat := 0
  depth : Nat := 0
  deriving DecidableEq, Repr

/-- Work and source-depth coordinates carried by one unfinished frame. -/
def Frame.cursor (frame : Frame) : WorkSpan :=
  ⟨frame.total, frame.depth⟩

/-- Accept one occurrence account. `.unfolding` is the scalar row step. -/
def Frame.advanceBy (frame : Frame) (metric : Metric) (account : WorkSpan) : Frame :=
  let joined := metricCombine metric frame.cursor account
  { frame with row := frame.row + 1, total := joined.work, depth := joined.span }

theorem Frame.advanceBy_unfolding (frame : Frame) (account : WorkSpan) :
    frame.advanceBy .unfolding account =
      { frame with row := frame.row + 1, total := frame.total + account.work } := rfl

theorem Frame.cursor_advanceBy (frame : Frame) (metric : Metric) (account : WorkSpan) :
    (frame.advanceBy metric account).cursor = metricCombine metric frame.cursor account := rfl

theorem Frame.advanceBy_prefixFold (frame : Frame) (rows : List Row) (children : List WorkSpan)
    (account : WorkSpan) (aligned : frame.cursor = prefixFold rows children) :
    (frame.advanceBy .pair account).cursor =
      WorkSpan.parallelAll (rowAccounts rows children ++ [account]) := by
  rw [Frame.cursor_advanceBy, aligned]
  exact (metricCombine_prefixFold rows children account).1

/-- A fresh frame has an empty cursor. Push and initialization use it. -/
@[reducible] def freshFrame (node : Nat) : Frame := { node := node }

theorem freshFrame_cursor (node : Nat) : (freshFrame node).cursor = ⟨0, 0⟩ := rfl

theorem Frame.advanceBy_node (frame : Frame) (metric : Metric) (account : WorkSpan) :
    (frame.advanceBy metric account).node = frame.node := rfl

/-- Source-depth coordinate of one linked row. `.unfolding` ignores it. -/
@[reducible] def rowSpan (metric : Metric) (childDepth : Nat) : Nat :=
  match metric with
  | .unfolding => 1
  | .depth => 1
  | .pair => 1 + childDepth

inductive Color where
  | fresh | active | done
  deriving DecidableEq, Repr

inductive Status where
  | pending | bound | cycle | invalid | overflow
  deriving DecidableEq, Repr

structure State where
  root : Nat
  capacity : Nat
  stack : List Frame
  colors : Nat → Color
  memo : Nat → Nat
  ticks : Nat := 0
  indexVisits : Nat := 0
  status : Status := .pending
  depthMemo : Nat → Nat := fun _ => 0

def init (graph : Graph) (root : Nat) : Option State :=
  if root < graph.nodes.length then
    some {
      root := root
      capacity := graph.nodes.length
      stack := [freshFrame root]
      colors := Function.update (fun _ => .fresh) root .active
      memo := fun _ => 0 }
  else none

theorem init_root (graph : Graph) (root : Nat) (state : State)
    (issued : init graph root = some state) : state.root = root := by
  unfold init at issued
  split at issued
  · cases issued; rfl
  · contradiction

def fail (state : State) (status : Status) : State :=
  { state with status }

def finish (state : State) (frame : Frame) (rest : List Frame) : State :=
  { state with
    stack := rest
    colors := Function.update state.colors frame.node .done
    memo := Function.update state.memo frame.node frame.total
    depthMemo := Function.update state.depthMemo frame.node frame.depth
    status := if rest.isEmpty then .bound else .pending }

def push (state : State) (child : Nat) : State :=
  { state with
    stack := freshFrame child :: state.stack
    colors := Function.update state.colors child .active }

def advance (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) : State :=
  { state with
    stack := { frame with row := frame.row + 1, total := frame.total + contribution } :: rest }

theorem advance_unfolding (state : State) (frame : Frame) (rest : List Frame)
    (account : WorkSpan) :
    advance state frame rest account.work =
      { state with stack := frame.advanceBy .unfolding account :: rest } := rfl

/-- `.unfolding` is definitionally `maximum < total + contribution`. -/
@[reducible] def rowOverflow (metric : Metric) (maximum : Nat) (frame : Frame)
    (contribution span : Nat) : Prop :=
  match metric with
  | .unfolding => maximum < frame.total + contribution
  | .depth => maximum < max frame.total contribution
  | .pair => maximum < frame.total + contribution ∨ maximum < max frame.depth span

instance (metric : Metric) (maximum : Nat) (frame : Frame) (contribution span : Nat) :
    Decidable (rowOverflow metric maximum frame contribution span) := by
  unfold rowOverflow
  cases metric <;> infer_instance

/-- `.unfolding` is definitionally `advance` by the work contribution. -/
@[reducible] def commitRow (metric : Metric) (state : State) (frame : Frame) (rest : List Frame)
    (contribution span : Nat) : State :=
  match metric with
  | .unfolding => advance state frame rest contribution
  | .depth =>
      { state with stack := frame.advanceBy .depth ⟨contribution, contribution⟩ :: rest }
  | .pair =>
      { state with stack := frame.advanceBy .pair ⟨contribution, span⟩ :: rest }

/-- One row. `.unfolding` keeps the scalar overflow test and `advance`.
`.depth` keeps the running maximum. `.pair` joins both coordinates. -/
def addRow (maximum : Nat) (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) (metric : Metric := .unfolding) (span : Nat := 1) : State :=
  if rowOverflow metric maximum frame contribution span then fail state .overflow
  else commitRow metric state frame rest contribution span

/-- The scalar control order of the native graph service. Array access and
counter charging have their own memory and account interpretations.
`metric` defaults to `.unfolding`, the existing work sum. -/
def step (graph : Graph) (maximum : Nat) (state : State)
    (metric : Metric := .unfolding) : State :=
  if state.status ≠ .pending then state
  else if state.capacity ≠ graph.nodes.length ∨ state.stack = [] ∨ state.ticks = maximum then
    fail state .invalid
  else
    let paid := { state with ticks := state.ticks + 1 }
    match state.stack with
    | [] => fail paid .invalid
    | frame :: rest =>
      let rows := graph.rows frame.node
      if frame.row = rows.length then finish paid frame rest
      else match rows[frame.row]? with
      | none => fail paid .invalid
      | some row =>
        if row.physical = 0 ∨ (row.successor.any fun child => graph.nodes.length ≤ child) then
          fail paid .invalid
        else
          let previous := rows.take frame.row
          match previous.findIdx? (fun earlier => earlier.physical == row.physical) with
          | some index => fail { paid with indexVisits := paid.indexVisits + index + 1 } .invalid
          | none =>
            let scanned := { paid with indexVisits := paid.indexVisits + frame.row }
            match row.successor with
            | none => addRow maximum scanned frame rest 1 metric
            | some child =>
              match state.colors child with
              | .active => fail scanned .cycle
              | .fresh =>
                if state.stack.length = state.capacity then fail scanned .invalid
                else push scanned child
              | .done =>
                if state.memo child = maximum then fail scanned .overflow
                else addRow maximum scanned frame rest (1 + state.memo child) metric
                  (rowSpan metric (state.depthMemo child))

/-- A bounded call retains the full DFS stack, memo and accounting cursor.
The metric is last so `run graph maximum fuel state` stays the scalar runner. -/
def run (graph : Graph) (maximum fuel : Nat) (state : State)
    (metric : Metric := .unfolding) : State :=
  match fuel with
  | 0 => state
  | fuel + 1 => run graph maximum fuel (step graph maximum state metric) metric

theorem run_zero (graph : Graph) (maximum : Nat) (state : State) (metric : Metric) :
    run graph maximum 0 state metric = state := rfl

theorem run_split (graph : Graph) (maximum fuel : Nat) (state : State) (metric : Metric) :
    run graph maximum (fuel + 1) state metric =
      run graph maximum fuel (step graph maximum state metric) metric := rfl

def bound? (state : State) : Option Nat :=
  if state.status = .bound then some (state.memo state.root) else none

/-- Both coordinates after `finish` has stored the root cursor. -/
def boundPair? (state : State) : Option WorkSpan :=
  if state.status = .bound then some ⟨state.memo state.root, state.depthMemo state.root⟩ else none

def Rooted (root : Nat) : List Frame → Prop
  | [] => True
  | [frame] => frame.node = root
  | _ :: second :: rest => Rooted root (second :: rest)

def Graph.FrameDerived (graph : Graph) (maximum : Nat) (frame : Frame) : Prop :=
  frame.node < graph.nodes.length ∧ frame.row ≤ (graph.rows frame.node).length ∧
    frame.total ≤ maximum ∧
      ∃ values, List.Forall₂ (RowValue graph) ((graph.rows frame.node).take frame.row) values ∧
        frame.total = values.sum

structure Valid (graph : Graph) (maximum : Nat) (state : State) : Prop where
  frames : ∀ frame ∈ state.stack, graph.FrameDerived maximum frame
  ticksWithin : state.ticks ≤ maximum
  cached : ∀ node, state.colors node = .done →
    graph.Derived node (state.memo node) ∧ state.memo node ≤ maximum
  rooted : Rooted state.root state.stack
  completed : state.status = .bound → state.colors state.root = .done
  stackUnique : (state.stack.map Frame.node).Nodup
  stackActive : ∀ frame ∈ state.stack, state.colors frame.node = .active

theorem frame_zero (graph : Graph) (maximum node : Nat)
    (admitted : node < graph.nodes.length) :
    graph.FrameDerived maximum { node := node } := by
  exact ⟨admitted, Nat.zero_le _, Nat.zero_le _, [], by simp, rfl⟩

theorem frame_complete (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDerived maximum frame)
    (finished : frame.row = (graph.rows frame.node).length) :
    graph.Derived frame.node frame.total := by
  obtain ⟨admitted, _, _, values, rows, total⟩ := valid
  rw [finished, List.take_length] at rows
  obtain ⟨children, derived, sum⟩ := rows_derive graph rows
  rw [total, sum]
  exact Catalogue.FoldDerivation.node (by simpa [Graph.catalogue] using admitted) derived

theorem frame_advance (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDerived maximum frame)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution)
    (within : frame.total + contribution ≤ maximum) :
    graph.FrameDerived maximum
      { frame with row := frame.row + 1, total := frame.total + contribution } := by
  obtain ⟨admitted, _, _, values, rows, total⟩ := valid
  change frame.node < graph.nodes.length ∧ frame.row + 1 ≤ (graph.rows frame.node).length ∧
    frame.total + contribution ≤ maximum ∧ _
  refine ⟨admitted, by omega, within, values ++ [contribution], ?_, ?_⟩
  · rw [List.take_succ_eq_append_getElem available]
    exact List.rel_append rows (.cons derived .nil)
  · simp only [List.sum_append, List.sum_singleton, total]

theorem run_add (graph : Graph) (maximum first second : Nat) (state : State) :
    run graph maximum (first + second) state =
      run graph maximum second (run graph maximum first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run_zero]
  | succ first ih => simpa only [Nat.succ_add, run_split] using ih (step graph maximum state)

theorem Valid.withCounters {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (ticks visits : Nat) (within : ticks ≤ maximum) :
    Valid graph maximum { state with ticks := ticks, indexVisits := visits } :=
  ⟨valid.frames, within, valid.cached, valid.rooted, valid.completed,
    valid.stackUnique, valid.stackActive⟩

theorem Valid.fail {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (status : Status) (notBound : status ≠ .bound) :
    Valid graph maximum (OccurrenceGraph.fail state status) := by
  refine ⟨valid.frames, valid.ticksWithin, valid.cached, valid.rooted, ?_,
    valid.stackUnique, valid.stackActive⟩
  intro completed
  exact False.elim (notBound completed)

theorem Rooted.tail (root : Nat) (frame : Frame) (rest : List Frame)
    (rooted : Rooted root (frame :: rest)) : Rooted root rest := by
  cases rest with
  | nil => trivial
  | cons second rest => exact rooted

theorem init_valid (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) : Valid graph maximum state := by
  unfold init at issued
  split at issued
  · rename_i admitted
    cases issued
    refine ⟨?_, Nat.zero_le _, ?_, rfl, ?_, ?_, ?_⟩
    · intro frame member
      have equal : frame = { node := root } := List.mem_singleton.1 member
      subst frame
      exact frame_zero graph maximum root admitted
    · intro node done
      simp only [Function.update_apply] at done
      split at done <;> contradiction
    · intro completed
      cases completed
    · simp
    · intro frame member
      have equal : frame = freshFrame root := List.mem_singleton.mp member
      subst frame
      simp [freshFrame]
  · contradiction

theorem Valid.finish {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (finished : frame.row = (graph.rows frame.node).length) :
    Valid graph maximum (OccurrenceGraph.finish state frame rest) := by
  have frameValid := valid.frames frame (by simp [stack])
  have unique : frame.node ∉ rest.map Frame.node ∧ (rest.map Frame.node).Nodup := by
    simpa only [stack, List.map_cons, List.nodup_cons] using valid.stackUnique
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_, unique.2, ?_⟩
  · intro other member
    exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · intro node done
    by_cases equal : node = frame.node
    · subst node
      simpa only [OccurrenceGraph.finish, Function.update_self] using
        And.intro (frame_complete graph maximum frame frameValid finished) frameValid.2.2.1
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using done
      simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using valid.cached node previous
  · exact Rooted.tail state.root frame rest (by simpa only [stack] using valid.rooted)
  · intro completed
    cases rest with
    | nil =>
      have root : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp only [OccurrenceGraph.finish, ← root, Function.update_self]
    | cons second rest => simp [OccurrenceGraph.finish] at completed
  · intro other member
    have different : other.node ≠ frame.node := by
      intro equal
      exact unique.1 (List.mem_map.mpr ⟨other, member, equal⟩)
    simpa only [OccurrenceGraph.finish, Function.update_of_ne different] using
      valid.stackActive other (by simp only [stack, List.mem_cons]; exact Or.inr member)

theorem Valid.push {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (child : Nat)
    (admitted : child < graph.nodes.length) (nonempty : state.stack ≠ [])
    (pending : state.status = .pending) (fresh : state.colors child = .fresh) :
    Valid graph maximum (OccurrenceGraph.push state child) := by
  have unvisited : child ∉ state.stack.map Frame.node := by
    intro member
    obtain ⟨frame, member, equal⟩ := List.mem_map.mp member
    have active := valid.stackActive frame member
    rw [equal, fresh] at active
    contradiction
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_, ?_, ?_⟩
  · intro frame member
    rcases List.mem_cons.1 member with equal | member
    · subst frame
      exact frame_zero graph maximum child admitted
    · exact valid.frames frame member
  · intro node done
    by_cases equal : node = child
    · subst node
      simp [OccurrenceGraph.push] at done
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.push, Function.update_of_ne equal] using done
      exact valid.cached node previous
  · cases stack : state.stack with
    | nil => exact False.elim (nonempty stack)
    | cons frame rest => simpa only [OccurrenceGraph.push, stack, Rooted] using valid.rooted
  · intro completed
    simp [OccurrenceGraph.push, pending] at completed
  · simpa only [OccurrenceGraph.push, List.map_cons, freshFrame, List.nodup_cons] using
      And.intro unvisited valid.stackUnique
  · intro frame member
    rcases List.mem_cons.mp member with equal | member
    · subst frame
      simp [OccurrenceGraph.push, freshFrame]
    · have different : frame.node ≠ child := by
        intro equal
        exact unvisited (List.mem_map.mpr ⟨frame, member, equal⟩)
      simpa only [OccurrenceGraph.push, Function.update_of_ne different] using
        valid.stackActive frame member

theorem Valid.advance {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution)
    (within : frame.total + contribution ≤ maximum) :
    Valid graph maximum (OccurrenceGraph.advance state frame rest contribution) := by
  refine ⟨?_, valid.ticksWithin, valid.cached, ?_, valid.completed, ?_, ?_⟩
  · intro other member
    rcases List.mem_cons.1 member with equal | member
    · subst other
      exact frame_advance graph maximum frame (valid.frames frame (by simp [stack]))
        available contribution derived within
    · exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · cases rest with
    | nil => simpa only [OccurrenceGraph.advance, stack, Rooted] using valid.rooted
    | cons second rest => simpa only [OccurrenceGraph.advance, stack, Rooted] using valid.rooted
  · simpa only [OccurrenceGraph.advance, List.map_cons, stack] using valid.stackUnique
  · intro other member
    rcases List.mem_cons.mp member with equal | member
    · subst other
      exact valid.stackActive frame (by simp [stack])
    · exact valid.stackActive other (by simp only [stack, List.mem_cons]; exact Or.inr member)

theorem Valid.addRow {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution) :
    Valid graph maximum (OccurrenceGraph.addRow maximum state frame rest contribution) := by
  unfold OccurrenceGraph.addRow
  dsimp only [rowOverflow, commitRow]
  split
  · exact valid.fail .overflow (by decide)
  · rename_i within
    exact valid.advance frame rest stack available contribution derived (by omega)

theorem addRow_guard_eq (maximum total contribution : Nat) (within : total ≤ maximum) :
    (maximum < total + contribution) ↔ (maximum - total < contribution) := by omega

theorem RowValue.of_terminal (graph : Graph) (row : Row)
    (terminal : row.successor = none) : RowValue graph row 1 := by
  cases row with
  | mk physical successor =>
    change successor = none at terminal
    subst successor
    exact RowValue.terminal physical

theorem RowValue.of_linked (graph : Graph) (row : Row) (child value : Nat)
    (linked : row.successor = some child) (derived : graph.Derived child value) :
    RowValue graph row (1 + value) := by
  cases row with
  | mk physical successor =>
    change successor = some child at linked
    subst successor
    exact RowValue.linked physical child value derived

/-- Every scalar traversal transition preserves independently justified
completed entries and the full ordered prefix of every unfinished frame. -/
theorem step_valid (graph : Graph) (maximum : Nat) (state : State)
    (valid : Valid graph maximum state) : Valid graph maximum (step graph maximum state) := by
  unfold step
  split
  · exact valid
  · rename_i isPending
    have pending : state.status = .pending := by
      by_cases equal : state.status = .pending
      · exact equal
      · exact False.elim (isPending equal)
    split
    · exact valid.fail .invalid (by decide)
    · rename_i admitted
      have beforeLimit : state.ticks ≠ maximum := fun equal =>
        admitted (Or.inr (Or.inr equal))
      let paid : State := { state with ticks := state.ticks + 1 }
      have paidValid : Valid graph maximum paid :=
        valid.withCounters (state.ticks + 1) state.indexVisits (by
          have := valid.ticksWithin
          omega)
      cases stack : state.stack with
      | nil =>
        simp only
        simpa only [paid, stack] using paidValid.fail .invalid (by decide)
      | cons frame rest =>
        simp only
        split
        · rename_i finished
          exact paidValid.finish frame rest stack finished
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none =>
            simp only
            simpa only [paid, stack] using paidValid.fail .invalid (by decide)
          | some row =>
            simp only
            obtain ⟨available, rowEqual⟩ := List.getElem?_eq_some_iff.1 found
            split
            · simpa only [paid, stack] using paidValid.fail .invalid (by decide)
            · rename_i rowValid
              cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index =>
                simp only
                simpa only [paid, stack] using
                  (paidValid.withCounters paid.ticks (paid.indexVisits + index + 1)
                    paidValid.ticksWithin).fail .invalid (by decide)
              | none =>
                simp only
                let scanned : State := { paid with indexVisits := paid.indexVisits + frame.row }
                have scannedValid : Valid graph maximum scanned :=
                  paidValid.withCounters paid.ticks (paid.indexVisits + frame.row)
                    paidValid.ticksWithin
                cases successor : row.successor with
                | none =>
                  simp only
                  have derived : RowValue graph (graph.rows frame.node)[frame.row] 1 := by
                    rw [rowEqual]
                    exact RowValue.of_terminal graph row successor
                  simpa only [scanned, paid, stack] using
                    scannedValid.addRow frame rest stack available 1 derived
                | some child =>
                  simp only
                  have childAdmitted : child < graph.nodes.length := by
                    have excluded : ¬graph.nodes.length ≤ child := by
                      intro outside
                      apply rowValid
                      exact Or.inr (by simp [successor, outside])
                    omega
                  cases color : state.colors child with
                  | active =>
                    simp only
                    simpa only [scanned, paid, stack] using scannedValid.fail .cycle (by decide)
                  | fresh =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using scannedValid.fail .invalid (by decide)
                    · simpa only [scanned, paid, stack] using
                        scannedValid.push child childAdmitted (by simp [scanned, paid, stack]) pending color
                  | done =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using scannedValid.fail .overflow (by decide)
                    · have derived : RowValue graph (graph.rows frame.node)[frame.row]
                          (1 + state.memo child) := by
                        rw [rowEqual]
                        exact RowValue.of_linked graph row child (state.memo child) successor
                          (valid.cached child color).1
                      simpa only [scanned, paid, stack] using
                        scannedValid.addRow frame rest stack available (1 + state.memo child) derived

theorem run_valid (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : Valid graph maximum state) :
    Valid graph maximum (run graph maximum fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih (step graph maximum state) (step_valid graph maximum state valid)

/-- A reported bound has a derivation independent of the DFS memo, including
every listed dependency occurrence, and fits the selected scalar range. -/
theorem bound_derived (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (valid : Valid graph maximum state) (reported : bound? state = some value) :
    graph.Derived state.root value ∧ value ≤ maximum := by
  unfold bound? at reported
  split at reported
  · rename_i completed
    cases reported
    exact valid.cached state.root (valid.completed completed)
  · contradiction

/-- The completed-node cache retains independently certified finite
observations. Reusing a completed child is justified by its derivation,
not merely by an earlier encounter or an active mark. -/
theorem Valid.cached_accepted {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (node : Nat) (completed : state.colors node = .done) :
    Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      graph.catalogue.observationGraph node :=
  (valid.cached node completed).1.accepted

/-- Successful reporting certifies accessibility of the actual dependency
graph. Acyclicity is a conclusion about the observed root, not an input
certificate to the DFS. -/
theorem bound_accessible (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (valid : Valid graph maximum state) (reported : bound? state = some value) :
    Acc (fun child parent => child ∈ graph.catalogue.deps parent) state.root :=
  (bound_derived graph maximum state value valid reported).1.accessible

theorem bound_no_reachable_cycle (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (valid : Valid graph maximum state) (reported : bound? state = some value) (node : Nat)
    (reachable : Relation.ReflTransGen
      (fun parent child => child ∈ graph.catalogue.deps parent) state.root node) :
    ¬ Relation.TransGen (fun child parent => child ∈ graph.catalogue.deps parent) node node :=
  Catalogue.FoldDerivation.no_reachable_cycle graph.catalogue
    (bound_derived graph maximum state value valid reported).1 reachable

theorem bound_unfoldingWork (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (acyclic : graph.catalogue.Acyclic) (valid : Valid graph maximum state)
    (reported : bound? state = some value) :
    value = graph.catalogue.unfoldingWork acyclic (fun node => (graph.rows node).length)
      state.root ∧ value ≤ maximum := by
  obtain ⟨derived, within⟩ := bound_derived graph maximum state value valid reported
  exact ⟨Catalogue.FoldDerivation.value_eq_depFold graph.catalogue acyclic graph.combine
    state.root value derived, within⟩

theorem step_root (graph : Graph) (maximum : Nat) (memory : State) :
    (step graph maximum memory).root = memory.root := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · dsimp only
      cases stack : memory.stack with
      | nil => rfl
      | cons frame rest =>
        simp only
        split
        · rfl
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none => rfl
          | some row =>
            simp only
            split
            · rfl
            · cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index => rfl
              | none =>
                simp only
                cases successor : row.successor with
                | none => simp only; unfold addRow; dsimp only [rowOverflow, commitRow]; split <;> rfl
                | some child =>
                  simp only
                  cases color : memory.colors child with
                  | active => rfl
                  | fresh => simp only; split <;> rfl
                  | done =>
                    simp only
                    split
                    · rfl
                    · unfold addRow; dsimp only [rowOverflow, commitRow]; split <;> rfl
theorem run_root (graph : Graph) (maximum fuel : Nat) (state : State) :
    (run graph maximum fuel state).root = state.root := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run_split, ih, step_root]

theorem initialized_run_bound (graph : Graph) (maximum root fuel : Nat) (state : State)
    (issued : init graph root = some state) (value : Nat) (acyclic : graph.catalogue.Acyclic)
    (reported : bound? (run graph maximum fuel state) = some value) :
    value = graph.catalogue.unfoldingWork acyclic (fun node => (graph.rows node).length)
      root ∧ value ≤ maximum := by
  have rooted := init_root graph root state issued
  have result := bound_unfoldingWork graph maximum (run graph maximum fuel state) value
    acyclic (run_valid graph maximum fuel state (init_valid graph maximum root state issued)) reported
  simpa only [run_root, rooted] using result

/-- The initialized, retained DFS cannot report a finite observation of a
root with a reachable cycle. All completed-cache reuse is covered by
`run_valid`; insufficient fuel is not a successful report. -/
theorem initialized_run_no_reachable_cycle (graph : Graph) (maximum root fuel : Nat)
    (state : State) (issued : init graph root = some state) (value node : Nat)
    (reported : bound? (run graph maximum fuel state) = some value)
    (reachable : Relation.ReflTransGen
      (fun parent child => child ∈ graph.catalogue.deps parent) root node) :
    ¬ Relation.TransGen (fun child parent => child ∈ graph.catalogue.deps parent) node node := by
  have rooted := init_root graph root state issued
  apply bound_no_reachable_cycle graph maximum (run graph maximum fuel state) value
    (run_valid graph maximum fuel state (init_valid graph maximum root state issued)) reported node
  simpa only [run_root, rooted] using reachable

/-- A reachable cycle can never receive a successful bound at any allowance.
This says neither that every insufficient run detects it nor that an
arbitrary malformed input state is a valid initialized traversal. -/
theorem initialized_reachable_cycle_no_bound (graph : Graph) (maximum root fuel : Nat)
    (state : State) (issued : init graph root = some state) (node : Nat)
    (reachable : Relation.ReflTransGen
      (fun parent child => child ∈ graph.catalogue.deps parent) root node)
    (cycle : Relation.TransGen (fun child parent => child ∈ graph.catalogue.deps parent) node node) :
    bound? (run graph maximum fuel state) = none := by
  cases reported : bound? (run graph maximum fuel state) with
  | none => rfl
  | some value =>
      exact False.elim (initialized_run_no_reachable_cycle graph maximum root fuel state
        issued value node reported reachable cycle)

theorem addRow_unfolding (maximum : Nat) (state : State) (frame : Frame) (rest : List Frame)
    (contribution span : Nat) :
    addRow maximum state frame rest contribution .unfolding span =
      (if maximum < frame.total + contribution then fail state .overflow
        else advance state frame rest contribution) := by
  unfold addRow
  rfl

/-- Left-to-right pair steps are `parallelAll`, by the one-row law. -/
theorem foldl_pair_cursor (frame : Frame) (done accounts : List WorkSpan)
    (base : frame.cursor = WorkSpan.parallelAll done) :
    (accounts.foldl (fun frame account => frame.advanceBy .pair account) frame).cursor =
      WorkSpan.parallelAll (done ++ accounts) := by
  induction accounts generalizing frame done with
  | nil =>
    rw [List.foldl_nil, List.append_nil]
    exact base
  | cons account accounts ih =>
    rw [List.foldl_cons, ← List.singleton_append, ← List.append_assoc]
    refine ih (frame.advanceBy .pair account) (done ++ [account]) ?_
    rw [Frame.cursor_advanceBy, base]
    exact (metricCombine_oneRow done account).1

theorem foldl_pair_node (frame : Frame) (accounts : List WorkSpan) :
    (accounts.foldl (fun frame account => frame.advanceBy .pair account) frame).node =
      frame.node := by
  induction accounts generalizing frame with
  | nil => rfl
  | cons account accounts ih =>
    rw [List.foldl_cons, ih, Frame.advanceBy_node]

theorem fresh_prefixFold (node : Nat) (rows : List Row) (children : List WorkSpan) :
    ((rowAccounts rows children).foldl (fun frame account => frame.advanceBy .pair account)
        (freshFrame node)).cursor =
      prefixFold rows children := by
  have base : (freshFrame node).cursor = WorkSpan.parallelAll ([] : List WorkSpan) := by
    rw [freshFrame_cursor, WorkSpan.parallelAll_nil]
    ext <;> simp [WorkSpan.zero_work, WorkSpan.zero_span]
  have folded := foldl_pair_cursor (freshFrame node) [] (rowAccounts rows children) base
  rw [List.nil_append] at folded
  rw [prefixFold, folded]

theorem boundPair_finish (state : State) (frame : Frame) (same : frame.node = state.root) :
    boundPair? (finish state frame []) = some frame.cursor := by
  simp [boundPair?, finish, Frame.cursor, Function.update_self, same, List.isEmpty_nil]

theorem step_bound_stuck (graph : Graph) (maximum : Nat) (state : State) (metric : Metric)
    (bound : state.status = .bound) :
    step graph maximum state metric = state := by
  unfold step
  simp [bound]

theorem run_bound_stable (graph : Graph) (maximum fuel : Nat) (state : State) (metric : Metric)
    (bound : state.status = .bound) :
    run graph maximum fuel state metric = state := by
  induction fuel generalizing state with
  | zero => rw [run_zero]
  | succ fuel ih =>
    rw [run_split, step_bound_stuck graph maximum state metric bound]
    exact ih state bound

/-- Pair row steps from a fresh frame finish at `prefixFold`. Further fuel
does not change a bound state. The complete successor list is
`sourceValuation` by `prefixFold_sourceValuation`. -/
theorem finished_run_sourceValuation (graph : Graph) (maximum fuel : Nat)
    (acyclic : graph.catalogue.Acyclic) (node : Nat)
    (admitted : node ∈ graph.catalogue.items) (state : State)
    (rootEq : state.root = node) :
    let accounts := rowAccounts (graph.rows node)
      ((graph.catalogue.deps node).map (graph.sourceValuation acyclic))
    let frame := accounts.foldl (fun frame account => frame.advanceBy .pair account)
      (freshFrame node)
    boundPair? (run graph maximum fuel (finish state frame []) .pair) =
      some (graph.sourceValuation acyclic node) := by
  intro accounts frame
  have cursor : frame.cursor = prefixFold (graph.rows node)
      ((graph.catalogue.deps node).map (graph.sourceValuation acyclic)) :=
    fresh_prefixFold node (graph.rows node)
      ((graph.catalogue.deps node).map (graph.sourceValuation acyclic))
  have same : frame.node = state.root := by
    rw [foldl_pair_node, freshFrame, rootEq]
  have stored : boundPair? (finish state frame []) = some frame.cursor :=
    boundPair_finish state frame same
  have stable := run_bound_stable graph maximum fuel (finish state frame []) .pair
    (by simp [finish, List.isEmpty_nil])
  rw [stable, stored, cursor, prefixFold_sourceValuation graph acyclic node admitted]

/-- One physical row in the pair cursor. A linked row sequences the unit
before the cached child valuation. Duplicate successors are not collapsed. -/
inductive RowPair (graph : Graph) : Row → WorkSpan → Prop where
  | terminal (physical : Nat) : RowPair graph ⟨physical, none⟩ ⟨1, 1⟩
  | linked (physical child : Nat) (value : WorkSpan)
      (derived : graph.catalogue.FoldDerivation graph.sourceCombine child value) :
      RowPair graph ⟨physical, some child⟩ (WorkSpan.sequential ⟨1, 1⟩ value)

theorem RowPair.of_terminal (graph : Graph) (row : Row) (terminal : row.successor = none) :
    RowPair graph row ⟨1, 1⟩ := by
  cases row with
  | mk physical successor =>
    cases successor with
    | none => exact RowPair.terminal physical
    | some _ => cases terminal

theorem RowPair.of_linked (graph : Graph) (row : Row) (child : Nat) (value : WorkSpan)
    (linked : row.successor = some child)
    (derived : graph.catalogue.FoldDerivation graph.sourceCombine child value) :
    RowPair graph row (WorkSpan.sequential ⟨1, 1⟩ value) := by
  cases row with
  | mk physical successor =>
    cases successor with
    | none => cases linked
    | some index =>
      cases linked
      exact RowPair.linked physical child value derived

/-- The ordered accounts are exactly `rowAccounts`, so `parallelAll` is `prefixFold`. -/
theorem rows_pair (graph : Graph) {rows : List Row} {values : List WorkSpan}
    (derived : List.Forall₂ (RowPair graph) rows values) :
    ∃ children,
      List.Forall₂ (graph.catalogue.FoldDerivation graph.sourceCombine)
        (rows.filterMap Row.successor) children ∧
      children.length = successorCount rows ∧
      values = rowAccounts rows children := by
  induction derived with
  | nil => exact ⟨[], .nil, rfl, rfl⟩
  | @cons row value rows values rowDerived remaining ih =>
    obtain ⟨children, childDerived, aligned, accounts⟩ := ih
    cases rowDerived with
    | terminal physical =>
      refine ⟨children, ?_, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using childDerived
      · rw [successorCount_terminal]
        exact aligned
      · rw [accounts, rowAccounts_terminal]
    | linked physical child childValue derivedChild =>
      refine ⟨childValue :: children, ?_, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using
          List.Forall₂.cons derivedChild childDerived
      · rw [successorCount_linked, List.length_cons, aligned]
      · rw [accounts, rowAccounts_linked]

/-- Unfinished pair frame: the cursor is the parallel aggregate of the rows
already accepted, and that aggregate is the `prefixFold` specification. -/
def Graph.FramePaired (graph : Graph) (maximum : Nat) (frame : Frame) : Prop :=
  frame.node < graph.nodes.length ∧ frame.row ≤ (graph.rows frame.node).length ∧
    frame.total ≤ maximum ∧ frame.depth ≤ frame.total ∧
      ∃ values, List.Forall₂ (RowPair graph) ((graph.rows frame.node).take frame.row) values ∧
        frame.cursor = WorkSpan.parallelAll values

theorem frame_pair_zero (graph : Graph) (maximum node : Nat)
    (admitted : node < graph.nodes.length) :
    graph.FramePaired maximum (freshFrame node) := by
  exact ⟨admitted, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, [], by simp, by
    rw [freshFrame_cursor, WorkSpan.parallelAll_nil]
    ext <;> simp [WorkSpan.zero_work, WorkSpan.zero_span]⟩

theorem frame_pair_complete (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FramePaired maximum frame)
    (finished : frame.row = (graph.rows frame.node).length) :
    graph.catalogue.FoldDerivation graph.sourceCombine frame.node frame.cursor ∧
      frame.depth ≤ frame.total ∧ frame.total ≤ maximum := by
  obtain ⟨admitted, _, within, depthLe, values, paired, cursor⟩ := valid
  rw [finished, List.take_length] at paired
  obtain ⟨children, derived, aligned, accounts⟩ := rows_pair graph paired
  have spec : frame.cursor = graph.sourceCombine frame.node children := by
    rw [cursor, accounts]
    change prefixFold (graph.rows frame.node) children = graph.sourceCombine frame.node children
    exact prefixFold_eq_sourceCombine graph frame.node children aligned
  refine ⟨?_, depthLe, within⟩
  rw [spec]
  exact Catalogue.FoldDerivation.node (by simpa [Graph.catalogue] using admitted) derived

theorem frame_pair_advance (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FramePaired maximum frame)
    (available : frame.row < (graph.rows frame.node).length) (contribution span : Nat)
    (derived : RowPair graph (graph.rows frame.node)[frame.row] ⟨contribution, span⟩)
    (spanLe : span ≤ contribution) (within : frame.total + contribution ≤ maximum) :
    graph.FramePaired maximum (frame.advanceBy .pair ⟨contribution, span⟩) := by
  obtain ⟨admitted, _, _, depthLe, values, paired, cursor⟩ := valid
  refine ⟨admitted, ?_, ?_, ?_, values ++ [⟨contribution, span⟩], ?_, ?_⟩
  · have rowEq : (frame.advanceBy .pair ⟨contribution, span⟩).row = frame.row + 1 := rfl
    rw [rowEq, Frame.advanceBy_node]
    omega
  · have totalEq : (frame.advanceBy .pair ⟨contribution, span⟩).total =
        frame.total + contribution := by
      simp [Frame.advanceBy, Frame.cursor]
    rw [totalEq]
    exact within
  · have totalEq : (frame.advanceBy .pair ⟨contribution, span⟩).total =
        frame.total + contribution := by
      simp [Frame.advanceBy, Frame.cursor]
    have depthEq : (frame.advanceBy .pair ⟨contribution, span⟩).depth = max frame.depth span := by
      simp [Frame.advanceBy, Frame.cursor]
    rw [depthEq, totalEq]
    exact max_le (depthLe.trans (Nat.le_add_right _ _)) (spanLe.trans (Nat.le_add_left _ _))
  · have rowEq : (frame.advanceBy .pair ⟨contribution, span⟩).row = frame.row + 1 := rfl
    rw [rowEq, Frame.advanceBy_node, List.take_succ_eq_append_getElem available]
    exact List.rel_append paired (.cons derived .nil)
  · rw [Frame.cursor_advanceBy, cursor]
    exact (metricCombine_oneRow values ⟨contribution, span⟩).1

structure PairValid (graph : Graph) (maximum : Nat) (state : State) : Prop where
  frames : ∀ frame ∈ state.stack, graph.FramePaired maximum frame
  ticksWithin : state.ticks ≤ maximum
  cached : ∀ node, state.colors node = .done →
    graph.catalogue.FoldDerivation graph.sourceCombine node
        ⟨state.memo node, state.depthMemo node⟩ ∧
      state.memo node ≤ maximum ∧ state.depthMemo node ≤ state.memo node
  rooted : Rooted state.root state.stack
  completed : state.status = .bound → state.colors state.root = .done

theorem PairValid.withCounters {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (ticks visits : Nat) (within : ticks ≤ maximum) :
    PairValid graph maximum { state with ticks := ticks, indexVisits := visits } :=
  ⟨valid.frames, within, valid.cached, valid.rooted, valid.completed⟩

theorem PairValid.fail {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (status : Status) (notBound : status ≠ .bound) :
    PairValid graph maximum (fail state status) := by
  refine ⟨valid.frames, valid.ticksWithin, valid.cached, valid.rooted, ?_⟩
  intro completed
  exact False.elim (notBound completed)

theorem init_pairValid (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) : PairValid graph maximum state := by
  unfold init at issued
  split at issued
  · rename_i admitted
    cases issued
    refine ⟨?_, Nat.zero_le _, ?_, rfl, ?_⟩
    · intro frame member
      have equal : frame = freshFrame root := List.mem_singleton.1 member
      subst frame
      exact frame_pair_zero graph maximum root admitted
    · intro node done
      simp only [Function.update_apply] at done
      split at done <;> contradiction
    · intro completed
      cases completed
  · contradiction

theorem PairValid.finish {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (finished : frame.row = (graph.rows frame.node).length) :
    PairValid graph maximum (OccurrenceGraph.finish state frame rest) := by
  have frameValid := valid.frames frame (by simp [stack])
  have complete := frame_pair_complete graph maximum frame frameValid finished
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro other member
    exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · intro node done
    by_cases equal : node = frame.node
    · subst node
      have memoEq : (OccurrenceGraph.finish state frame rest).memo frame.node = frame.total := by
        simp [OccurrenceGraph.finish, Function.update_self]
      have depthEq : (OccurrenceGraph.finish state frame rest).depthMemo frame.node =
          frame.depth := by
        simp [OccurrenceGraph.finish, Function.update_self]
      rw [memoEq, depthEq]
      exact ⟨complete.1, complete.2.2, complete.2.1⟩
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using done
      simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using
        valid.cached node previous
  · exact Rooted.tail state.root frame rest (by simpa only [stack] using valid.rooted)
  · intro completed
    cases rest with
    | nil =>
      have root : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp only [OccurrenceGraph.finish, ← root, Function.update_self]
    | cons second rest => simp [OccurrenceGraph.finish] at completed

theorem PairValid.push {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (child : Nat)
    (admitted : child < graph.nodes.length) (nonempty : state.stack ≠ [])
    (pending : state.status = .pending) :
    PairValid graph maximum (OccurrenceGraph.push state child) := by
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro frame member
    rcases List.mem_cons.1 member with equal | member
    · subst frame
      exact frame_pair_zero graph maximum child admitted
    · exact valid.frames frame member
  · intro node done
    by_cases equal : node = child
    · subst node
      simp [OccurrenceGraph.push] at done
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.push, Function.update_of_ne equal] using done
      exact valid.cached node previous
  · cases stack : state.stack with
    | nil => exact False.elim (nonempty stack)
    | cons frame rest => simpa only [OccurrenceGraph.push, stack, Rooted] using valid.rooted
  · intro completed
    simp [OccurrenceGraph.push, pending] at completed

theorem PairValid.commit {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution span : Nat)
    (spanLe : span ≤ contribution)
    (derived : RowPair graph (graph.rows frame.node)[frame.row] ⟨contribution, span⟩)
    (within : frame.total + contribution ≤ maximum) :
    PairValid graph maximum
      { state with stack := frame.advanceBy .pair ⟨contribution, span⟩ :: rest } := by
  refine ⟨?_, valid.ticksWithin, valid.cached, ?_, valid.completed⟩
  · intro other member
    rcases List.mem_cons.1 member with equal | member
    · subst other
      exact frame_pair_advance graph maximum frame (valid.frames frame (by simp [stack]))
        available contribution span derived spanLe within
    · exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · cases rest with
    | nil =>
      have rooted : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp [Frame.advanceBy, Rooted, rooted]
    | cons second tail =>
      simpa [Frame.advanceBy, stack, Rooted] using valid.rooted

theorem PairValid.addRow {graph : Graph} {maximum : Nat} {state : State}
    (valid : PairValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution span : Nat)
    (spanLe : span ≤ contribution)
    (derived : RowPair graph (graph.rows frame.node)[frame.row] ⟨contribution, span⟩) :
    PairValid graph maximum (addRow maximum state frame rest contribution .pair span) := by
  unfold OccurrenceGraph.addRow
  dsimp only [rowOverflow, commitRow]
  split
  · exact valid.fail .overflow (by decide)
  · rename_i safe
    have within : frame.total + contribution ≤ maximum := by
      have notWork : ¬ maximum < frame.total + contribution := fun exceeded =>
        safe (Or.inl exceeded)
      omega
    exact valid.commit frame rest stack available contribution span spanLe derived within

theorem step_root_metric (graph : Graph) (maximum : Nat) (memory : State) (metric : Metric) :
    (step graph maximum memory metric).root = memory.root := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · dsimp only
      cases stack : memory.stack with
      | nil => rfl
      | cons frame rest =>
        simp only
        split
        · rfl
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none => rfl
          | some row =>
            simp only
            split
            · rfl
            · cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index => rfl
              | none =>
                simp only
                cases successor : row.successor with
                | none =>
                  simp only
                  cases metric <;>
                    unfold addRow <;>
                    dsimp only [rowOverflow, commitRow] <;>
                    split <;> rfl
                | some child =>
                  simp only
                  cases color : memory.colors child with
                  | active => rfl
                  | fresh => simp only; split <;> rfl
                  | done =>
                    simp only
                    split
                    · rfl
                    · cases metric <;>
                        unfold addRow <;>
                        dsimp only [rowOverflow, commitRow] <;>
                        split <;> rfl

theorem step_root_pair (graph : Graph) (maximum : Nat) (memory : State) :
    (step graph maximum memory .pair).root = memory.root :=
  step_root_metric graph maximum memory .pair

/-- Metric-independent DFS control. Pair and depth supply only the row commit. -/
theorem step_preserve (graph : Graph) (maximum : Nat) (metric : Metric) (V : State → Prop)
    (preserveFail : ∀ state status, status ≠ .bound → V state → V (fail state status))
    (ticksWithin : ∀ state, V state → state.ticks ≤ maximum)
    (preserveCounters : ∀ state ticks visits, ticks ≤ maximum → V state →
      V { state with ticks := ticks, indexVisits := visits })
    (preserveFinish : ∀ state frame rest, state.stack = frame :: rest →
      frame.row = (graph.rows frame.node).length → V state → V (finish state frame rest))
    (preservePush : ∀ state child, child < graph.nodes.length → state.stack ≠ [] →
      state.status = .pending → V state → V (push state child))
    (preserveTerminal : ∀ (state : State) (frame : Frame) (rest : List Frame) (row : Row)
      (_stack : state.stack = frame :: rest)
      (available : frame.row < (graph.rows frame.node).length),
      (graph.rows frame.node)[frame.row] = row → row.successor = none → V state →
      V (addRow maximum state frame rest 1 metric))
    (preserveLinked : ∀ (state : State) (frame : Frame) (rest : List Frame) (row : Row)
      (child : Nat) (_stack : state.stack = frame :: rest)
      (available : frame.row < (graph.rows frame.node).length),
      (graph.rows frame.node)[frame.row] = row → row.successor = some child →
      state.colors child = .done → state.memo child ≠ maximum → V state →
      V (addRow maximum state frame rest (1 + state.memo child) metric
        (rowSpan metric (state.depthMemo child))))
    (state : State) (valid : V state) : V (step graph maximum state metric) := by
  unfold step
  split
  · exact valid
  · rename_i isPending
    have pending : state.status = .pending := by
      by_cases equal : state.status = .pending
      · exact equal
      · exact False.elim (isPending equal)
    split
    · exact preserveFail state .invalid (by decide) valid
    · rename_i admitted
      have beforeLimit : state.ticks ≠ maximum := fun equal =>
        admitted (Or.inr (Or.inr equal))
      let paid : State := { state with ticks := state.ticks + 1 }
      have paidValid : V paid :=
        preserveCounters state (state.ticks + 1) state.indexVisits (by
          have := ticksWithin state valid
          omega) valid
      cases stack : state.stack with
      | nil =>
        simp only
        simpa only [paid, stack] using preserveFail paid .invalid (by decide) paidValid
      | cons frame rest =>
        simp only
        split
        · rename_i finished
          exact preserveFinish paid frame rest stack finished paidValid
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none =>
            simp only
            simpa only [paid, stack] using preserveFail paid .invalid (by decide) paidValid
          | some row =>
            simp only
            obtain ⟨available, rowEqual⟩ := List.getElem?_eq_some_iff.1 found
            split
            · simpa only [paid, stack] using preserveFail paid .invalid (by decide) paidValid
            · rename_i rowValid
              cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index =>
                simp only
                simpa only [paid, stack] using
                  preserveFail { paid with indexVisits := paid.indexVisits + index + 1 } .invalid
                    (by decide)
                    (preserveCounters paid paid.ticks (paid.indexVisits + index + 1)
                      (ticksWithin paid paidValid) paidValid)
              | none =>
                simp only
                let scanned : State := { paid with indexVisits := paid.indexVisits + frame.row }
                have scannedValid : V scanned :=
                  preserveCounters paid paid.ticks (paid.indexVisits + frame.row)
                    (ticksWithin paid paidValid) paidValid
                cases successor : row.successor with
                | none =>
                  simp only
                  simpa only [scanned, paid, stack] using
                    preserveTerminal scanned frame rest row stack available rowEqual successor
                      scannedValid
                | some child =>
                  simp only
                  have childAdmitted : child < graph.nodes.length := by
                    have excluded : ¬ graph.nodes.length ≤ child := by
                      intro outside
                      apply rowValid
                      exact Or.inr (by simp [successor, outside])
                    omega
                  cases color : state.colors child with
                  | active =>
                    simp only
                    simpa only [scanned, paid, stack] using
                      preserveFail scanned .cycle (by decide) scannedValid
                  | fresh =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using
                        preserveFail scanned .invalid (by decide) scannedValid
                    · simpa only [scanned, paid, stack] using
                        preservePush scanned child childAdmitted
                          (by simp [scanned, paid, stack]) pending scannedValid
                  | done =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using
                        preserveFail scanned .overflow (by decide) scannedValid
                    · rename_i notMaximum
                      simpa only [scanned, paid, stack] using
                        preserveLinked scanned frame rest row child stack available rowEqual
                          successor color notMaximum scannedValid

/-- Each pair transition preserves the prefix cursor and the finished
`sourceCombine` memo. The scalar runner is the default metric, untouched. -/
theorem step_pairValid (graph : Graph) (maximum : Nat) (state : State)
    (valid : PairValid graph maximum state) :
    PairValid graph maximum (step graph maximum state .pair) := by
  refine step_preserve graph maximum .pair (PairValid graph maximum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ state valid
  · intro state status notBound valid
    exact valid.fail status notBound
  · intro state valid
    exact valid.ticksWithin
  · intro state ticks visits within valid
    exact valid.withCounters ticks visits within
  · intro state frame rest stack finished valid
    exact valid.finish frame rest stack finished
  · intro state child admitted nonempty pending valid
    exact valid.push child admitted nonempty pending
  · intro state frame rest row stack available rowEqual terminal valid
    have derived : RowPair graph (graph.rows frame.node)[frame.row] ⟨1, 1⟩ := by
      rw [rowEqual]
      exact RowPair.of_terminal graph row terminal
    exact valid.addRow frame rest stack available 1 1 (Nat.le_refl _) derived
  · intro state frame rest row child stack available rowEqual linked color _notMaximum valid
    have cached := valid.cached child color
    have derived : RowPair graph (graph.rows frame.node)[frame.row]
        ⟨1 + state.memo child, 1 + state.depthMemo child⟩ := by
      rw [rowEqual]
      exact RowPair.of_linked graph row child ⟨state.memo child, state.depthMemo child⟩
        linked cached.1
    exact valid.addRow frame rest stack available (1 + state.memo child)
      (1 + state.depthMemo child) (Nat.add_le_add_left cached.2.2 1) derived

theorem run_pairValid (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : PairValid graph maximum state) :
    PairValid graph maximum (run graph maximum fuel state .pair) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    exact ih (step graph maximum state .pair) (step_pairValid graph maximum state valid)

theorem run_root_pair (graph : Graph) (maximum fuel : Nat) (state : State) :
    (run graph maximum fuel state .pair).root = state.root := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run_split, ih, step_root_pair]

/-- A bound pair run is the independent source valuation. The cache is a
consequence of the preserved prefix invariant, not an assumed final fold. -/
theorem bound_sourceValuation (graph : Graph) (maximum : Nat) (state : State) (value : WorkSpan)
    (acyclic : graph.catalogue.Acyclic) (valid : PairValid graph maximum state)
    (reported : boundPair? state = some value) :
    value = graph.sourceValuation acyclic state.root ∧
      value.span ≤ value.work ∧ value.work ≤ maximum := by
  unfold boundPair? at reported
  split at reported
  · rename_i completed
    cases reported
    obtain ⟨derived, within, depthLe⟩ :=
      valid.cached state.root (valid.completed completed)
    have eq := Catalogue.FoldDerivation.value_eq_depFold graph.catalogue acyclic
      graph.sourceCombine state.root ⟨state.memo state.root, state.depthMemo state.root⟩ derived
    refine ⟨?_, depthLe, within⟩
    have spec : graph.sourceValuation acyclic state.root =
        graph.catalogue.depFold acyclic graph.sourceCombine state.root := rfl
    rw [spec]
    exact eq
  · contradiction

theorem initialized_run_sourceValuation (graph : Graph) (maximum root fuel : Nat) (state : State)
    (issued : init graph root = some state) (value : WorkSpan) (acyclic : graph.catalogue.Acyclic)
    (reported : boundPair? (run graph maximum fuel state .pair) = some value) :
    value = graph.sourceValuation acyclic root ∧
      value.span ≤ value.work ∧ value.work ≤ maximum := by
  have rootEq : state.root = root := by
    unfold init at issued
    split at issued
    · cases issued
      rfl
    · contradiction
  have result := bound_sourceValuation graph maximum (run graph maximum fuel state .pair) value
    acyclic (run_pairValid graph maximum fuel state (init_pairValid graph maximum root state issued))
    reported
  simpa only [run_root_pair, rootEq] using result

/-- Source dependency depth is the span projection of that same bound pair. -/
theorem initialized_run_dependencyDepth (graph : Graph) (maximum root fuel : Nat) (state : State)
    (issued : init graph root = some state) (value : WorkSpan) (acyclic : graph.catalogue.Acyclic)
    (reported : boundPair? (run graph maximum fuel state .pair) = some value) :
    value.span = graph.dependencyDepth acyclic root ∧
      value = graph.sourceValuation acyclic root ∧
      value.span ≤ value.work ∧ value.work ≤ maximum := by
  obtain ⟨eq, spanLe, within⟩ :=
    initialized_run_sourceValuation graph maximum root fuel state issued value acyclic reported
  refine ⟨?_, eq, spanLe, within⟩
  rw [eq]
  exact graph.sourceValuation_depth acyclic root

private theorem span_of_depth (children : List Nat) :
    ((children.map (fun n => (⟨0, n⟩ : WorkSpan))).map WorkSpan.span) = children := by
  induction children with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, List.map_cons, ih]

/-- Span aggregate of the shared row accounts. This is `depthCombine` once the
child list is aligned with the successor occurrences. -/
theorem depthAccounts_fold (rows : List Row) (children : List Nat)
    (aligned : children.length = successorCount rows) :
    ((rowAccounts rows (children.map (fun n => (⟨0, n⟩ : WorkSpan)))).map WorkSpan.span).foldr
        max 0 =
      (if rows.isEmpty then 0 else 1) + children.foldr max 0 := by
  have packed : (children.map (fun n => (⟨0, n⟩ : WorkSpan))).length =
      successorCount rows := by
    rw [List.length_map, aligned]
  rw [rowAccounts_span rows (children.map (fun n => (⟨0, n⟩ : WorkSpan))) packed,
    span_of_depth]

private theorem foldr_max_snoc (values : List Nat) (contribution : Nat) :
    (values ++ [contribution]).foldr max 0 = max (values.foldr max 0) contribution := by
  induction values with
  | nil =>
    rw [List.nil_append, List.foldr_cons, List.foldr_nil]
    exact Nat.max_comm contribution 0
  | cons head tail ih =>
    rw [List.cons_append, List.foldr_cons, ih, List.foldr_cons]
    exact (Nat.max_assoc head (tail.foldr max 0) contribution).symm

/-- One depth contribution. A terminal occurrence is one layer. A linked
occurrence is one layer beyond the cached child depth. Duplicate successors
stay distinct. -/
inductive RowDepth (graph : Graph) : Row → Nat → Prop where
  | terminal (physical : Nat) : RowDepth graph ⟨physical, none⟩ 1
  | linked (physical child depth : Nat)
      (derived : graph.catalogue.FoldDerivation graph.depthCombine child depth) :
      RowDepth graph ⟨physical, some child⟩ (1 + depth)

theorem RowDepth.of_terminal (graph : Graph) (row : Row) (terminal : row.successor = none) :
    RowDepth graph row 1 := by
  cases row with
  | mk physical successor =>
    cases successor with
    | none => exact RowDepth.terminal physical
    | some _ => cases terminal

theorem RowDepth.of_linked (graph : Graph) (row : Row) (child depth : Nat)
    (linked : row.successor = some child)
    (derived : graph.catalogue.FoldDerivation graph.depthCombine child depth) :
    RowDepth graph row (1 + depth) := by
  cases row with
  | mk physical successor =>
    cases successor with
    | none => cases linked
    | some index =>
      cases linked
      exact RowDepth.linked physical child depth derived

/-- Accepted depth contributions are the spans of the shared row accounts. -/
theorem rows_depth (graph : Graph) {rows : List Row} {values : List Nat}
    (derived : List.Forall₂ (RowDepth graph) rows values) :
    ∃ children,
      List.Forall₂ (graph.catalogue.FoldDerivation graph.depthCombine)
        (rows.filterMap Row.successor) children ∧
      children.length = successorCount rows ∧
      values = (rowAccounts rows (children.map (fun n => (⟨0, n⟩ : WorkSpan)))).map
        WorkSpan.span := by
  induction derived with
  | nil => exact ⟨[], .nil, rfl, rfl⟩
  | @cons row value rows values rowDerived remaining ih =>
    obtain ⟨children, childDerived, aligned, accounts⟩ := ih
    cases rowDerived with
    | terminal physical =>
      refine ⟨children, ?_, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using childDerived
      · rw [successorCount_terminal]
        exact aligned
      · rw [accounts, rowAccounts_terminal]
        rfl
    | linked physical child depth derivedChild =>
      refine ⟨depth :: children, ?_, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using
          List.Forall₂.cons derivedChild childDerived
      · rw [successorCount_linked, List.length_cons, aligned]
      · rw [List.map_cons, accounts, rowAccounts_linked]
        rfl

/-- The depth cursor stores the running maximum of the accepted row spans.
It is not the paired work sum, so it can stay inside a ceiling that rejects
that sum. -/
def Graph.FrameDepth (graph : Graph) (maximum : Nat) (frame : Frame) : Prop :=
  frame.node < graph.nodes.length ∧ frame.row ≤ (graph.rows frame.node).length ∧
    frame.total ≤ maximum ∧
      ∃ values, List.Forall₂ (RowDepth graph) ((graph.rows frame.node).take frame.row) values ∧
        frame.total = values.foldr max 0

theorem frame_depth_zero (graph : Graph) (maximum node : Nat)
    (admitted : node < graph.nodes.length) :
    graph.FrameDepth maximum (freshFrame node) := by
  exact ⟨admitted, Nat.zero_le _, Nat.zero_le _, [], by simp, rfl⟩

theorem frame_depth_complete (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDepth maximum frame)
    (finished : frame.row = (graph.rows frame.node).length) :
    graph.catalogue.FoldDerivation graph.depthCombine frame.node frame.total ∧
      frame.total ≤ maximum := by
  obtain ⟨admitted, _, within, values, paired, aggregated⟩ := valid
  rw [finished, List.take_length] at paired
  obtain ⟨children, derived, aligned, accounts⟩ := rows_depth graph paired
  have combined : frame.total = graph.depthCombine frame.node children := by
    rw [aggregated, accounts]
    exact depthAccounts_fold (graph.rows frame.node) children aligned
  refine ⟨?_, within⟩
  rw [combined]
  exact Catalogue.FoldDerivation.node (by simpa [Graph.catalogue] using admitted) derived

theorem frame_depth_advance (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDepth maximum frame)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowDepth graph (graph.rows frame.node)[frame.row] contribution)
    (within : max frame.total contribution ≤ maximum) :
    graph.FrameDepth maximum (frame.advanceBy .depth ⟨contribution, contribution⟩) := by
  obtain ⟨admitted, _, _, values, paired, aggregated⟩ := valid
  have rowEq : (frame.advanceBy .depth ⟨contribution, contribution⟩).row = frame.row + 1 := rfl
  have totalEq : (frame.advanceBy .depth ⟨contribution, contribution⟩).total =
      max frame.total contribution := by
    simp [Frame.advanceBy, Frame.cursor]
  refine ⟨admitted, ?_, ?_, values ++ [contribution], ?_, ?_⟩
  · rw [rowEq, Frame.advanceBy_node]
    omega
  · rw [totalEq]
    exact within
  · rw [rowEq, Frame.advanceBy_node, List.take_succ_eq_append_getElem available]
    exact List.rel_append paired (.cons derived .nil)
  · rw [totalEq, aggregated]
    exact (foldr_max_snoc values contribution).symm

structure DepthValid (graph : Graph) (maximum : Nat) (state : State) : Prop where
  frames : ∀ frame ∈ state.stack, graph.FrameDepth maximum frame
  ticksWithin : state.ticks ≤ maximum
  cached : ∀ node, state.colors node = .done →
    graph.catalogue.FoldDerivation graph.depthCombine node (state.memo node) ∧
      state.memo node ≤ maximum
  rooted : Rooted state.root state.stack
  completed : state.status = .bound → state.colors state.root = .done

theorem DepthValid.withCounters {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (ticks visits : Nat) (within : ticks ≤ maximum) :
    DepthValid graph maximum { state with ticks := ticks, indexVisits := visits } :=
  ⟨valid.frames, within, valid.cached, valid.rooted, valid.completed⟩

theorem DepthValid.fail {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (status : Status) (notBound : status ≠ .bound) :
    DepthValid graph maximum (fail state status) := by
  refine ⟨valid.frames, valid.ticksWithin, valid.cached, valid.rooted, ?_⟩
  intro completed
  exact False.elim (notBound completed)

theorem init_depthValid (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) : DepthValid graph maximum state := by
  unfold init at issued
  split at issued
  · rename_i admitted
    cases issued
    refine ⟨?_, Nat.zero_le _, ?_, rfl, ?_⟩
    · intro frame member
      have equal : frame = freshFrame root := List.mem_singleton.1 member
      subst frame
      exact frame_depth_zero graph maximum root admitted
    · intro node done
      simp only [Function.update_apply] at done
      split at done <;> contradiction
    · intro completed
      cases completed
  · contradiction

theorem DepthValid.finish {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (finished : frame.row = (graph.rows frame.node).length) :
    DepthValid graph maximum (OccurrenceGraph.finish state frame rest) := by
  have frameValid := valid.frames frame (by simp [stack])
  have complete := frame_depth_complete graph maximum frame frameValid finished
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro other member
    exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · intro node done
    by_cases equal : node = frame.node
    · subst node
      have memoEq : (OccurrenceGraph.finish state frame rest).memo frame.node = frame.total := by
        simp [OccurrenceGraph.finish, Function.update_self]
      rw [memoEq]
      exact ⟨complete.1, complete.2⟩
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using done
      simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using
        valid.cached node previous
  · exact Rooted.tail state.root frame rest (by simpa only [stack] using valid.rooted)
  · intro completed
    cases rest with
    | nil =>
      have root : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp only [OccurrenceGraph.finish, ← root, Function.update_self]
    | cons second rest => simp [OccurrenceGraph.finish] at completed

theorem DepthValid.push {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (child : Nat)
    (admitted : child < graph.nodes.length) (nonempty : state.stack ≠ [])
    (pending : state.status = .pending) :
    DepthValid graph maximum (OccurrenceGraph.push state child) := by
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro frame member
    rcases List.mem_cons.1 member with equal | member
    · subst frame
      exact frame_depth_zero graph maximum child admitted
    · exact valid.frames frame member
  · intro node done
    by_cases equal : node = child
    · subst node
      simp [OccurrenceGraph.push] at done
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.push, Function.update_of_ne equal] using done
      exact valid.cached node previous
  · cases stack : state.stack with
    | nil => exact False.elim (nonempty stack)
    | cons frame rest => simpa only [OccurrenceGraph.push, stack, Rooted] using valid.rooted
  · intro completed
    simp [OccurrenceGraph.push, pending] at completed

theorem DepthValid.commit {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowDepth graph (graph.rows frame.node)[frame.row] contribution)
    (within : max frame.total contribution ≤ maximum) :
    DepthValid graph maximum
      { state with stack := frame.advanceBy .depth ⟨contribution, contribution⟩ :: rest } := by
  refine ⟨?_, valid.ticksWithin, valid.cached, ?_, valid.completed⟩
  · intro other member
    rcases List.mem_cons.1 member with equal | member
    · subst other
      exact frame_depth_advance graph maximum frame (valid.frames frame (by simp [stack]))
        available contribution derived within
    · exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · cases rest with
    | nil =>
      have rooted : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp [Frame.advanceBy, Rooted, rooted]
    | cons second tail =>
      simpa [Frame.advanceBy, stack, Rooted] using valid.rooted

theorem DepthValid.addRow {graph : Graph} {maximum : Nat} {state : State}
    (valid : DepthValid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution _span : Nat)
    (derived : RowDepth graph (graph.rows frame.node)[frame.row] contribution) :
    DepthValid graph maximum
      (addRow maximum state frame rest contribution .depth _span) := by
  unfold OccurrenceGraph.addRow
  dsimp only [rowOverflow, commitRow]
  split
  · exact valid.fail .overflow (by decide)
  · rename_i safe
    have within : max frame.total contribution ≤ maximum := by omega
    exact valid.commit frame rest stack available contribution derived within

theorem step_depthValid (graph : Graph) (maximum : Nat) (state : State)
    (valid : DepthValid graph maximum state) :
    DepthValid graph maximum (step graph maximum state .depth) := by
  refine step_preserve graph maximum .depth (DepthValid graph maximum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ state valid
  · intro state status notBound valid
    exact valid.fail status notBound
  · intro state valid
    exact valid.ticksWithin
  · intro state ticks visits within valid
    exact valid.withCounters ticks visits within
  · intro state frame rest stack finished valid
    exact valid.finish frame rest stack finished
  · intro state child admitted nonempty pending valid
    exact valid.push child admitted nonempty pending
  · intro state frame rest row stack available rowEqual terminal valid
    have derived : RowDepth graph (graph.rows frame.node)[frame.row] 1 := by
      rw [rowEqual]
      exact RowDepth.of_terminal graph row terminal
    exact valid.addRow frame rest stack available 1 1 derived
  · intro state frame rest row child stack available rowEqual linked color _notMaximum valid
    have cached := valid.cached child color
    have derived : RowDepth graph (graph.rows frame.node)[frame.row]
        (1 + state.memo child) := by
      rw [rowEqual]
      exact RowDepth.of_linked graph row child (state.memo child) linked cached.1
    exact valid.addRow frame rest stack available (1 + state.memo child)
      (rowSpan .depth (state.depthMemo child)) derived

theorem run_depthValid (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : DepthValid graph maximum state) :
    DepthValid graph maximum (run graph maximum fuel state .depth) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    exact ih (step graph maximum state .depth) (step_depthValid graph maximum state valid)

theorem run_root_metric (graph : Graph) (maximum fuel : Nat) (state : State) (metric : Metric) :
    (run graph maximum fuel state metric).root = state.root := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run_split, ih, step_root_metric]

/-- A bound depth run is `dependencyDepth`. The memo is the preserved running
maximum, not the span of a paired run that may have overflowed. -/
theorem bound_dependencyDepth (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (acyclic : graph.catalogue.Acyclic) (valid : DepthValid graph maximum state)
    (reported : bound? state = some value) :
    value = graph.dependencyDepth acyclic state.root ∧ value ≤ maximum := by
  unfold bound? at reported
  split at reported
  · rename_i completed
    cases reported
    obtain ⟨derived, within⟩ := valid.cached state.root (valid.completed completed)
    have eq := Catalogue.FoldDerivation.value_eq_depFold graph.catalogue acyclic
      graph.depthCombine state.root (state.memo state.root) derived
    refine ⟨?_, within⟩
    have spec : graph.dependencyDepth acyclic state.root =
        graph.catalogue.depFold acyclic graph.depthCombine state.root := rfl
    rw [spec]
    exact eq
  · contradiction

theorem initialized_run_depth (graph : Graph) (maximum root fuel : Nat) (state : State)
    (issued : init graph root = some state) (value : Nat) (acyclic : graph.catalogue.Acyclic)
    (reported : bound? (run graph maximum fuel state .depth) = some value) :
    value = graph.dependencyDepth acyclic root ∧ value ≤ maximum := by
  have rootEq : state.root = root := by
    unfold init at issued
    split at issued
    · cases issued
      rfl
    · contradiction
  have result := bound_dependencyDepth graph maximum (run graph maximum fuel state .depth) value
    acyclic (run_depthValid graph maximum fuel state (init_depthValid graph maximum root state issued))
    reported
  rw [run_root_metric graph maximum fuel state .depth, rootEq] at result
  exact result

/-! Concrete depth-only runs. The ceiling is also the step allowance, so the
separating example needs several successor rows: each adds the child work in
one step, while depth keeps the maximum layer. -/

def depthChainGraph : Graph :=
  ⟨[[⟨1, some 1⟩], [⟨1, none⟩]]⟩

def depthChainInitial : State :=
  (init depthChainGraph 0).get (by decide)

def depthChainCertificate : depthChainGraph.catalogue.Acyclic :=
  depthChainGraph.catalogue.acyclic?.get (by decide)

private theorem depthChain_dependencyDepth :
    depthChainGraph.dependencyDepth depthChainCertificate 0 = 2 := by
  have leaf : depthChainGraph.dependencyDepth depthChainCertificate 1 = 1 := by
    rw [Graph.dependencyDepth_eq depthChainGraph depthChainCertificate 1 (by decide)]
    rfl
  rw [Graph.dependencyDepth_eq depthChainGraph depthChainCertificate 0 (by decide)]
  change depthChainGraph.depthCombine 0
      [depthChainGraph.dependencyDepth depthChainCertificate 1] = 2
  simp only [leaf]
  rfl

/-- A successor chain binds depth two through the depth runner. -/
theorem depth_chain_reports_dependencyDepth :
    bound? (run depthChainGraph 5 5 depthChainInitial .depth) =
      some (depthChainGraph.dependencyDepth depthChainCertificate 0) ∧
    depthChainGraph.dependencyDepth depthChainCertificate 0 = 2 := by
  have reported : bound? (run depthChainGraph 5 5 depthChainInitial .depth) = some 2 := by decide
  have sound := initialized_run_depth depthChainGraph 5 0 5 depthChainInitial (by rfl) 2
    depthChainCertificate reported
  refine ⟨?_, depthChain_dependencyDepth⟩
  rw [← sound.1]
  exact reported

def depthFanGraph : Graph :=
  ⟨[[⟨1, some 1⟩, ⟨2, some 1⟩, ⟨3, some 1⟩, ⟨4, some 1⟩, ⟨5, some 1⟩],
    [⟨1, none⟩]]⟩

def depthFanInitial : State :=
  (init depthFanGraph 0).get (by decide)

def depthFanCertificate : depthFanGraph.catalogue.Acyclic :=
  depthFanGraph.catalogue.acyclic?.get (by decide)

private theorem depthFan_dependencyDepth :
    depthFanGraph.dependencyDepth depthFanCertificate 0 = 2 := by
  have leaf : depthFanGraph.dependencyDepth depthFanCertificate 1 = 1 := by
    rw [Graph.dependencyDepth_eq depthFanGraph depthFanCertificate 1 (by decide)]
    rfl
  rw [Graph.dependencyDepth_eq depthFanGraph depthFanCertificate 0 (by decide)]
  change depthFanGraph.depthCombine 0
      [depthFanGraph.dependencyDepth depthFanCertificate 1,
       depthFanGraph.dependencyDepth depthFanCertificate 1,
       depthFanGraph.dependencyDepth depthFanCertificate 1,
       depthFanGraph.dependencyDepth depthFanCertificate 1,
       depthFanGraph.dependencyDepth depthFanCertificate 1] = 2
  simp only [leaf]
  rfl

/-- Five referring rows make activation work overflow at ceiling nine.
The depth runner still binds dependency depth two. Pair overflows on the
same work sum. -/
theorem depth_fan_binds_when_work_overflows :
    bound? (run depthFanGraph 9 9 depthFanInitial .depth) =
      some (depthFanGraph.dependencyDepth depthFanCertificate 0) ∧
    depthFanGraph.dependencyDepth depthFanCertificate 0 = 2 ∧
    (run depthFanGraph 9 9 depthFanInitial .unfolding).status = .overflow ∧
    bound? (run depthFanGraph 9 9 depthFanInitial .unfolding) = none ∧
    (run depthFanGraph 9 9 depthFanInitial .pair).status = .overflow ∧
    bound? (run depthFanGraph 9 9 depthFanInitial .pair) = none := by
  have reported : bound? (run depthFanGraph 9 9 depthFanInitial .depth) = some 2 := by decide
  have sound := initialized_run_depth depthFanGraph 9 0 9 depthFanInitial (by rfl) 2
    depthFanCertificate reported
  refine ⟨?_, depthFan_dependencyDepth, by decide, by decide, by decide, by decide⟩
  rw [← sound.1]
  exact reported

/-! ## Retained finite-graph observations and attempted work

The machine below is the existing DFS with its terminal statuses exposed as
`none`. Its state retains the ordered child cursor, active/completed marks,
memo, and paid counters. A dispatch still performs a bulk duplicate-row scan;
the scan-aware price below does not silently count that scan as one operation.
Native row lookup, hash-table work, allocation and resizing need separate
prices and a correspondence to these observations.
-/

open Mettapedia.Machines

theorem step_of_stopped (graph : Graph) (maximum : Nat) (state : State)
    (stopped : state.status ≠ .pending) (metric : Metric := .unfolding) :
    step graph maximum state metric = state := by
  simp only [step, if_pos stopped]

theorem run_of_stopped (graph : Graph) (maximum fuel : Nat) (state : State)
    (stopped : state.status ≠ .pending) (metric : Metric := .unfolding) :
    run graph maximum fuel state metric = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step_of_stopped graph maximum state stopped metric] using ih

/-- The maintained DFS as a resumable operation. No alternative graph
traversal or journal is introduced. -/
abbrev sliceMachine (graph : Graph) (maximum : Nat) : MachineCore State where
  State := State
  load := id
  step state := if state.status = .pending then some (step graph maximum state) else none

/-- Slicing the operation retains exactly the original DFS state, including
completed sharing, the unfinished child coordinate and both paid counters. -/
theorem sliceMachine_run (graph : Graph) (maximum fuel : Nat) (state : State) :
    (MachineCore.runSlice (sliceMachine graph maximum) fuel state).1 =
      run graph maximum fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases pending : state.status = .pending
      · simpa only [MachineCore.runSlice, sliceMachine, if_pos pending, run] using
          ih (step graph maximum state)
      · simp only [MachineCore.runSlice, sliceMachine, if_neg pending]
        exact (run_of_stopped graph maximum (fuel + 1) state pending).symm

open scoped BigOperators

/-- Every not-yet-entered node reserves its rows, its entry, and its exit.
This mathematical potential is independent of the tick ceiling and returned
unfolding value. It is not state that a native service must maintain. -/
def freshPotential (graph : Graph) (colors : Nat → Color) : Nat :=
  ∑ node ∈ Finset.range graph.nodes.length,
    if colors node = .fresh then (graph.rows node).length + 2 else 0

/-- A fresh child reserves its own complete future work; an active frame
reserves only its unfinished rows and exit. Completed DAG children reserve
neither. All three coordinates are already present in the retained DFS. -/
def structuralRank (graph : Graph) (state : State) : Nat :=
  freshPotential graph state.colors +
    (state.stack.map (fun frame => (graph.rows frame.node).length - frame.row + 1)).sum

theorem freshPotential_update_nonfresh (graph : Graph) (colors : Nat → Color) (node : Nat)
    (color : Color) (before : colors node ≠ .fresh) (after : color ≠ .fresh) :
    freshPotential graph (Function.update colors node color) = freshPotential graph colors := by
  apply Finset.sum_congr rfl
  intro selected _
  by_cases same : selected = node
  · subst selected
    simp [before, after]
  · simp only [Function.update_of_ne same]

theorem freshPotential_activate (graph : Graph) (colors : Nat → Color) (child : Nat)
    (admitted : child < graph.nodes.length) (fresh : colors child = .fresh) :
    freshPotential graph colors =
      freshPotential graph (Function.update colors child .active) + (graph.rows child).length + 2 := by
  let weight := fun node => if colors node = .fresh then (graph.rows node).length + 2 else 0
  have member : child ∈ Finset.range graph.nodes.length := Finset.mem_range.mpr admitted
  have before := Finset.sum_update_of_mem member weight (weight child)
  simp only [Function.update_eq_self] at before
  have changed : (fun node =>
      if Function.update colors child .active node = .fresh then (graph.rows node).length + 2 else 0) =
        Function.update weight child 0 := by
    funext node
    by_cases same : node = child
    · subst node
      simp
    · simp only [Function.update_of_ne same, weight]
  unfold freshPotential
  rw [changed, Finset.sum_update_of_mem member weight 0]
  change (∑ node ∈ Finset.range graph.nodes.length, weight node) = _
  have own : weight child = (graph.rows child).length + 2 := by simp [weight, fresh]
  omega

theorem structuralRank_push (graph : Graph) (state : State) (child : Nat)
    (admitted : child < graph.nodes.length) (fresh : state.colors child = .fresh) :
    structuralRank graph (push state child) + 1 = structuralRank graph state := by
  have reserved := freshPotential_activate graph state.colors child admitted fresh
  dsimp only [structuralRank, push, freshFrame]
  simp only [List.map_cons, List.sum_cons]
  omega

theorem structuralRank_finish (graph : Graph) (maximum : Nat) (state : State)
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest) (finished : frame.row = (graph.rows frame.node).length) :
    structuralRank graph (finish state frame rest) + 1 = structuralRank graph state := by
  have active := valid.stackActive frame (by simp [stack])
  have kept := freshPotential_update_nonfresh graph state.colors frame.node .done
    (by rw [active]; decide) (by decide)
  dsimp only [structuralRank, finish]
  rw [kept, stack, List.map_cons, List.sum_cons, finished, Nat.sub_self]
  omega

theorem structuralRank_advance (graph : Graph) (state : State) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest) (available : frame.row < (graph.rows frame.node).length)
    (contribution : Nat) :
    structuralRank graph (advance state frame rest contribution) + 1 = structuralRank graph state := by
  dsimp only [structuralRank, advance]
  simp only [stack, List.map_cons, List.sum_cons]
  omega

theorem structuralRank_addRow (graph : Graph) (maximum : Nat) (state : State)
    (frame : Frame) (rest : List Frame) (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (pending : (addRow maximum state frame rest contribution).status = .pending) :
    structuralRank graph (addRow maximum state frame rest contribution) + 1 =
      structuralRank graph state := by
  unfold addRow at pending ⊢
  dsimp only [rowOverflow, commitRow] at pending ⊢
  split_ifs at pending ⊢
  · contradiction
  · exact structuralRank_advance graph state frame rest stack available contribution

theorem addRow_ticks (maximum : Nat) (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) : (addRow maximum state frame rest contribution).ticks = state.ticks := by
  unfold addRow
  split <;> rfl

/-- Every continuation of the actual DFS consumes one unit of structural
potential. Fresh-color admission is essential: re-entering a completed or
active node would not consume a fresh node's reservation. Rejections and
administrative stops are not identified with successful completion. -/
theorem step_continuation_exact (graph : Graph) (maximum : Nat) (state : State)
    (valid : Valid graph maximum state)
    (continues : (step graph maximum state).status = .pending) :
    (step graph maximum state).ticks = state.ticks + 1 ∧
      structuralRank graph (step graph maximum state) + 1 = structuralRank graph state := by
  unfold step at continues ⊢
  by_cases stopped : state.status ≠ .pending
  · simp only [if_pos stopped] at continues
    exact False.elim (stopped continues)
  · simp only [if_neg stopped] at continues ⊢
    by_cases refused : state.capacity ≠ graph.nodes.length ∨ state.stack = [] ∨ state.ticks = maximum
    · simp [refused, fail] at continues
    · simp only [if_neg refused] at continues ⊢
      let paid : State := { state with ticks := state.ticks + 1 }
      have paidValid : Valid graph maximum paid :=
        valid.withCounters (state.ticks + 1) state.indexVisits (by
          have := valid.ticksWithin
          have before : state.ticks ≠ maximum := fun equal => refused (Or.inr (Or.inr equal))
          omega)
      cases stack : state.stack with
      | nil => simp [stack, fail] at continues
      | cons frame rest =>
        simp only [stack] at continues
        simp only
        by_cases finished : frame.row = (graph.rows frame.node).length
        · simp only [if_pos finished]
          have progress := structuralRank_finish graph maximum paid paidValid frame rest stack finished
          have same : structuralRank graph paid = structuralRank graph state := rfl
          rw [same] at progress
          exact ⟨rfl, by simpa only [paid, stack] using progress⟩
        · simp only [if_neg finished] at continues ⊢
          cases found : (graph.rows frame.node)[frame.row]? with
          | none => simp [found, fail] at continues
          | some row =>
            simp only [found] at continues
            simp only
            obtain ⟨available, rowEqual⟩ := List.getElem?_eq_some_iff.mp found
            by_cases badRow : row.physical = 0 ∨
                (row.successor.any fun child => graph.nodes.length ≤ child)
            · simp [badRow, fail] at continues
            · simp only [if_neg badRow] at continues ⊢
              cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index => simp [visited, fail] at continues
              | none =>
                simp only [visited] at continues
                simp only
                let scanned : State := { paid with indexVisits := paid.indexVisits + frame.row }
                have same : structuralRank graph scanned = structuralRank graph state := rfl
                cases successor : row.successor with
                | none =>
                  simp only [successor] at continues
                  simp only
                  have after : (addRow maximum scanned frame rest 1).status = .pending := by
                    simpa only [scanned, paid, stack] using continues
                  have progress := structuralRank_addRow graph maximum scanned frame rest stack available 1 after
                  rw [same] at progress
                  exact ⟨by simp only [addRow_ticks],
                    by simpa only [scanned, paid, stack] using progress⟩
                | some child =>
                  simp only [successor] at continues
                  simp only
                  have childAdmitted : child < graph.nodes.length := by
                    have outside : ¬ graph.nodes.length ≤ child := by
                      intro beyond
                      exact badRow (Or.inr (by simp [successor, beyond]))
                    omega
                  cases color : state.colors child with
                  | active => simp [color, fail] at continues
                  | fresh =>
                    simp only [color] at continues
                    simp only
                    by_cases full : (frame :: rest).length = state.capacity
                    · simp [full, fail] at continues
                    · simp only [if_neg full] at continues ⊢
                      have progress := structuralRank_push graph scanned child childAdmitted color
                      rw [same] at progress
                      exact ⟨rfl, by simpa only [scanned, paid, stack] using progress⟩
                  | done =>
                    simp only [color] at continues
                    simp only
                    by_cases overflow : state.memo child = maximum
                    · simp [overflow, fail] at continues
                    · simp only [if_neg overflow] at continues ⊢
                      have after : (addRow maximum scanned frame rest (1 + state.memo child)).status =
                          .pending := by simpa only [scanned, paid, stack] using continues
                      have progress := structuralRank_addRow graph maximum scanned frame rest stack available
                        (1 + state.memo child) after
                      rw [same] at progress
                      exact ⟨by simp only [addRow_ticks],
                        by simpa only [scanned, paid, stack] using progress⟩

theorem step_structuralRank_lt (graph : Graph) (maximum : Nat) (state : State)
    (valid : Valid graph maximum state)
    (continues : (step graph maximum state).status = .pending) :
    structuralRank graph (step graph maximum state) < structuralRank graph state :=
  Nat.lt_of_succ_le (step_continuation_exact graph maximum state valid continues).2.le

/-- Every still-pending run keeps its initial structural work reserve. The
clock ceiling cannot create the decrease proved above. -/
theorem run_pending_reserve (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : Valid graph maximum state) (pending : (run graph maximum fuel state).status = .pending) :
    (run graph maximum fuel state).ticks + structuralRank graph (run graph maximum fuel state) =
      state.ticks + structuralRank graph state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have nextPending : (step graph maximum state).status = .pending := by
        by_contra stopped
        rw [run, run_of_stopped graph maximum fuel _ stopped] at pending
        exact stopped pending
      have progress := step_continuation_exact graph maximum state valid nextPending
      have later := ih (step graph maximum state) (step_valid graph maximum state valid) pending
      change (run graph maximum fuel (step graph maximum state)).ticks +
        structuralRank graph (run graph maximum fuel (step graph maximum state)) = _
      omega

/-- Explicit reserve admission rules out the administrative tick-ceiling
guard at every pending state, independently of whether that state will
eventually accept, detect a cycle, or refuse malformed input. -/
theorem pending_below_administrative_ceiling (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : Valid graph maximum state) (headroom : state.ticks + structuralRank graph state < maximum)
    (pending : (run graph maximum fuel state).status = .pending) :
    (run graph maximum fuel state).ticks < maximum := by
  have reserved := run_pending_reserve graph maximum fuel state valid pending
  omega

/-- A structural allowance forces a returned status even on cyclic or
malformed finite catalogues. The returned status must still be inspected:
`.cycle`, `.invalid` and `.overflow` are not accepted finite observations. -/
theorem run_stops_with_structural_allowance (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : Valid graph maximum state) (enough : structuralRank graph state < fuel) :
    (run graph maximum fuel state).status ≠ .pending := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [run]
      by_cases continues : (step graph maximum state).status = .pending
      · have decreases := step_structuralRank_lt graph maximum state valid continues
        exact ih (step graph maximum state) (step_valid graph maximum state valid) (by omega)
      · rw [run_of_stopped graph maximum fuel _ continues]
        exact continues

theorem initialized_run_stops (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) :
    (run graph maximum (structuralRank graph state + 1) state).status ≠ .pending :=
  run_stops_with_structural_allowance graph maximum _ state (init_valid graph maximum root state issued)
    (Nat.lt_succ_self _)

/-- This finite ceiling is computed from the retained graph's structural
reserve, independently of the possibly much larger unfolded-value range.
It excludes the tick-limit guard while the query is pending. An unfolding
overflow still has its own explicit refusal status. -/
theorem initialized_structural_ceiling (graph : Graph) (root : Nat) (state : State)
    (issued : init graph root = some state) (fuel : Nat)
    (pending : (run graph (state.ticks + structuralRank graph state + 1) fuel state).status = .pending) :
    (run graph (state.ticks + structuralRank graph state + 1) fuel state).ticks <
      state.ticks + structuralRank graph state + 1 :=
  pending_below_administrative_ceiling graph _ fuel state (init_valid graph _ root state issued)
    (Nat.lt_succ_self _) pending

theorem sliceMachine_final_with_structural_allowance (graph : Graph) (maximum : Nat)
    (state : State) (valid : Valid graph maximum state) :
    (sliceMachine graph maximum).step
      (MachineCore.runSlice (sliceMachine graph maximum) (structuralRank graph state + 1) state).1 = none := by
  have stopped := run_stops_with_structural_allowance graph maximum
    (structuralRank graph state + 1) state valid (Nat.lt_succ_self _)
  simp only [sliceMachine_run, sliceMachine, if_neg stopped]

/-- The structural allowance produces an inspected verdict. Only `.bound`
provides a finite-success certificate; the cycle, invalid-input/administrative
and overflow outcomes remain separate refusals. -/
theorem initialized_run_verdict (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) :
    let result := run graph maximum (structuralRank graph state + 1) state
    (∃ value, bound? result = some value ∧
      Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
        graph.catalogue.observationGraph root) ∨
      result.status = .cycle ∨ result.status = .invalid ∨ result.status = .overflow := by
  dsimp only
  have valid := run_valid graph maximum (structuralRank graph state + 1) state
    (init_valid graph maximum root state issued)
  have stopped := initialized_run_stops graph maximum root state issued
  cases verdict : (run graph maximum (structuralRank graph state + 1) state).status with
  | pending => exact False.elim (stopped verdict)
  | bound =>
      left
      let value := (run graph maximum (structuralRank graph state + 1) state).memo
        (run graph maximum (structuralRank graph state + 1) state).root
      have reported : bound? (run graph maximum (structuralRank graph state + 1) state) = some value := by
        simp only [bound?, if_pos verdict, value]
      have accepted := (bound_derived graph maximum _ value valid reported).1.accepted
      exact ⟨value, reported, by simpa only [run_root, init_root graph root state issued] using accepted⟩
  | cycle => exact Or.inr (Or.inl rfl)
  | invalid => exact Or.inr (Or.inr (Or.inl rfl))
  | overflow => exact Or.inr (Or.inr (Or.inr rfl))

theorem addRow_indexVisits (maximum : Nat) (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) (metric : Metric) (span : Nat) :
    (addRow maximum state frame rest contribution metric span).indexVisits = state.indexVisits := by
  unfold addRow
  split
  · rfl
  · cases metric <;> rfl

/-- Actual prefix-scan charges are monotone and bounded by the admitted row
width. This follows the real duplicate-search branches, including an early
duplicate rejection; it does not assume a cost bound for a whole dispatch. -/
theorem step_indexVisits_bounds (graph : Graph) (maximum : Nat) (state : State)
    (width : Nat) (rowWidth : ∀ node, (graph.rows node).length ≤ width)
    (metric : Metric := .unfolding) :
    state.indexVisits ≤ (step graph maximum state metric).indexVisits ∧
      (step graph maximum state metric).indexVisits ≤ state.indexVisits + width := by
  unfold step
  split
  · exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · split
    · exact ⟨le_rfl, Nat.le_add_right _ _⟩
    · dsimp only
      cases stack : state.stack with
      | nil => exact ⟨le_rfl, Nat.le_add_right _ _⟩
      | cons frame rest =>
        simp only
        split
        · exact ⟨le_rfl, Nat.le_add_right _ _⟩
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none => exact ⟨le_rfl, Nat.le_add_right _ _⟩
          | some row =>
            simp only
            split
            · exact ⟨le_rfl, Nat.le_add_right _ _⟩
            · have available := (List.getElem?_eq_some_iff.mp found).1
              have within := rowWidth frame.node
              cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index =>
                  have indexBound := (List.findIdx?_eq_some_iff_findIdx_eq.mp visited).1
                  have prefixBound := List.length_take_le frame.row (graph.rows frame.node)
                  simp only [fail]
                  exact ⟨by omega, by omega⟩
              | none =>
                  simp only
                  cases successor : row.successor with
                  | none =>
                      simp only [addRow_indexVisits]
                      exact ⟨by omega, by omega⟩
                  | some child =>
                      simp only
                      cases color : state.colors child with
                      | active =>
                          simp only [fail]
                          exact ⟨by omega, by omega⟩
                      | fresh =>
                          simp only
                          split <;> exact ⟨by simp [fail, push], by dsimp only [fail, push]; omega⟩
                      | done =>
                          simp only
                          split
                          · exact ⟨by simp [fail], by dsimp only [fail]; omega⟩
                          · simp only [addRow_indexVisits]
                            exact ⟨by omega, by omega⟩

/-- Scan comparisons actually charged by this DFS call, not the logical
number of dependency occurrences represented by its returned bound. -/
def scanWork (graph : Graph) (maximum : Nat) (state : State) : Nat :=
  (step graph maximum state).indexVisits - state.indexVisits

theorem scanWork_le (graph : Graph) (maximum : Nat) (state : State) (width : Nat)
    (rowWidth : ∀ node, (graph.rows node).length ≤ width) :
    scanWork graph maximum state ≤ width := by
  have charged := step_indexVisits_bounds graph maximum state width rowWidth
  unfold scanWork
  omega

theorem scanWork_of_stopped (graph : Graph) (maximum : Nat) (state : State)
    (stopped : state.status ≠ .pending) : scanWork graph maximum state = 0 := by
  simp only [scanWork, step_of_stopped graph maximum state stopped, Nat.sub_self]

/-- A finite graph always supplies a row-width contract; clients may use a
tighter independently established bound. -/
theorem Graph.rows_length_le_total (graph : Graph) (node : Nat) :
    (graph.rows node).length ≤ (graph.nodes.map List.length).sum := by
  unfold Graph.rows
  cases row : graph.nodes[node]? with
  | none => simp
  | some rows =>
      have member := List.mem_of_getElem? row
      have lengthMember : rows.length ∈ graph.nodes.map List.length := List.mem_map.mpr ⟨rows, member, rfl⟩
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ lengthMember

/-- The existing run account of the retained operation reads exactly the
increase in its scan counter. Splitting does not replay a paid prefix. -/
theorem scan_account_exact (graph : Graph) (maximum fuel : Nat) (state : State) :
    state.indexVisits + MachineCore.sliceCost (sliceMachine graph maximum)
      (scanWork graph maximum) fuel state = (run graph maximum fuel state).indexVisits := by
  induction fuel generalizing state with
  | zero => simp only [MachineCore.sliceCost_zero, Nat.add_zero, run_zero]
  | succ fuel ih =>
      by_cases pending : state.status = .pending
      · have later := ih (step graph maximum state)
        have monotone := (step_indexVisits_bounds graph maximum state
          (graph.nodes.map List.length).sum graph.rows_length_le_total).1
        simp only [MachineCore.sliceCost_succ, sliceMachine, if_pos pending, run]
        change state.indexVisits +
          (scanWork graph maximum state + MachineCore.sliceCost (sliceMachine graph maximum)
            (scanWork graph maximum) fuel (step graph maximum state)) = _
        unfold scanWork at *
        omega
      · simp only [MachineCore.sliceCost_succ, sliceMachine, if_neg pending, Nat.add_zero]
        rw [run_of_stopped graph maximum (fuel + 1) state pending]

/-- Terminal probes perform no row scan. They are nevertheless real attempted
calls and can carry a nonzero fixed price. -/
theorem attempted_scan_account_exact (graph : Graph) (maximum fuel : Nat) (state : State) :
    state.indexVisits + MachineCore.Attempts.cost (sliceMachine graph maximum)
      (scanWork graph maximum) fuel state = (run graph maximum fuel state).indexVisits := by
  rw [MachineCore.Attempts.cost_exact]
  by_cases early : (MachineCore.runSlice (sliceMachine graph maximum) fuel state).2 < fuel
  · have final := MachineCore.runSlice_under_budget_final (sliceMachine graph maximum) fuel state early
    have stopped : (MachineCore.runSlice (sliceMachine graph maximum) fuel state).1.status ≠ .pending := by
      simpa only [sliceMachine, ite_eq_right_iff, Option.some_ne_none, imp_false] using final
    rw [if_pos early, scanWork_of_stopped graph maximum _ stopped, Nat.add_zero]
    exact scan_account_exact graph maximum fuel state
  · rw [if_neg early, Nat.add_zero]
    exact scan_account_exact graph maximum fuel state

/-- A scan-aware price for an actual attempt. Fixed service work, memory
access and representation costs belong in declared component prices; this
construction does not assert that a native call has constant duration. -/
def callPrice {Cost : Type*} [AddMonoid Cost] (graph : Graph) (maximum : Nat)
    (fixed scan : Cost) (state : State) : Cost :=
  fixed + scanWork graph maximum state • scan

theorem callPrice_le {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (graph : Graph) (maximum width : Nat)
    (rowWidth : ∀ node, (graph.rows node).length ≤ width) (fixed scan : Cost)
    (scanNonnegative : 0 ≤ scan) (state : State) :
    callPrice graph maximum fixed scan state ≤ fixed + width • scan :=
  add_le_add_right (nsmul_le_nsmul_left scanNonnegative
    (scanWork_le graph maximum state width rowWidth)) fixed

/-- Attempted-operation prices, including early terminal checks, compose
through the maintained `RunAccount`. The bound is derived from the actual
row-scan branches and an explicit price for each component operation. -/
theorem attempted_cost_le {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (graph : Graph) (maximum width : Nat)
    (rowWidth : ∀ node, (graph.rows node).length ≤ width) (fixed scan : Cost)
    (fixedNonnegative : 0 ≤ fixed) (scanNonnegative : 0 ≤ scan) (fuel : Nat) (state : State) :
    MachineCore.Attempts.cost (sliceMachine graph maximum)
      (callPrice graph maximum fixed scan) fuel state ≤ fuel • (fixed + width • scan) :=
  MachineCore.Attempts.cost_le (sliceMachine graph maximum) _ _
    (add_nonneg fixedNonnegative (nsmul_nonneg scanNonnegative width))
    (callPrice_le graph maximum width rowWidth fixed scan scanNonnegative) fuel state

/-- The shared child is completed once, before the unfinished parent is
resumed. Every referring row still contributes to the independent unfolding
value; the retained scan counter records the parent-prefix comparisons. -/
theorem shared_dag_retains_completed_child :
    (run depthFanGraph 100 3 depthFanInitial).stack = [freshFrame 0] ∧
    (run depthFanGraph 100 3 depthFanInitial).colors 0 = .active ∧
    (run depthFanGraph 100 3 depthFanInitial).colors 1 = .done ∧
    (run depthFanGraph 100 3 depthFanInitial).memo 1 = 1 ∧
    run depthFanGraph 100 9 depthFanInitial =
      run depthFanGraph 100 6 (run depthFanGraph 100 3 depthFanInitial) ∧
    bound? (run depthFanGraph 100 9 depthFanInitial) = some 10 ∧
    (run depthFanGraph 100 9 depthFanInitial).ticks = 9 ∧
    (run depthFanGraph 100 9 depthFanInitial).indexVisits = 10 := by
  refine ⟨by decide, by decide, by decide, by decide,
    run_add depthFanGraph 100 3 6 depthFanInitial, by decide, by decide, by decide⟩

/-- The paid scan account is an observation of the real resumed DFS, not an
unfolding tree or a count of returned answers. -/
theorem shared_dag_scan_account :
    MachineCore.sliceCost (sliceMachine depthFanGraph 100)
      (scanWork depthFanGraph 100) 9 depthFanInitial = 10 ∧
    MachineCore.Attempts.cost (sliceMachine depthFanGraph 100)
      (scanWork depthFanGraph 100) 12 depthFanInitial = 10 := by
  have scans := scan_account_exact depthFanGraph 100 9 depthFanInitial
  have attempts := attempted_scan_account_exact depthFanGraph 100 12 depthFanInitial
  have first : (run depthFanGraph 100 9 depthFanInitial).indexVisits = 10 := by decide
  have later : (run depthFanGraph 100 12 depthFanInitial).indexVisits = 10 := by decide
  simpa only [first, later, show depthFanInitial.indexVisits = 0 from rfl, Nat.zero_add]
    using And.intro scans attempts

/-- Sharing consumes a finite structural reserve without unfolding the
shared child repeatedly. Rank is not the prefix-scan work account. -/
theorem shared_dag_structural_reserve :
    structuralRank depthFanGraph depthFanInitial = 9 ∧
    structuralRank depthFanGraph (run depthFanGraph 100 3 depthFanInitial) = 6 ∧
    structuralRank depthFanGraph (run depthFanGraph 100 9 depthFanInitial) = 0 ∧
    (run depthFanGraph 100 7 depthFanInitial).ticks +
      structuralRank depthFanGraph (run depthFanGraph 100 7 depthFanInitial) = 9 := by
  decide

/-- Tick or capacity refusal is not a proof of a cyclic or otherwise
non-finite source. A genuine success at a sufficient allowance supplies
the independent acceptance certificate for the same source. -/
theorem administrative_refusals_do_not_disprove_finiteness :
    (step depthFanGraph 0 depthFanInitial).status = .invalid ∧
    (step depthFanGraph 100 { depthFanInitial with capacity := 0 }).status = .invalid ∧
    Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      depthFanGraph.catalogue.observationGraph 0 := by
  refine ⟨by decide, by decide, ?_⟩
  have valid := run_valid depthFanGraph 100 9 depthFanInitial
    (init_valid depthFanGraph 100 0 depthFanInitial (by rfl))
  have accepted := (bound_derived depthFanGraph 100 _ 10 valid (by decide)).1.accepted
  simpa only [run_root, show depthFanInitial.root = 0 from rfl] using accepted

private def unknownReferenceGraph : Graph := ⟨[[⟨1, some 1⟩]]⟩

private def unknownReferenceInitial : State := (init unknownReferenceGraph 0).get (by decide)

/-- An out-of-catalogue successor is refused as input, rather than silently
treated as a leaf. This is distinct from the administrative refusal above. -/
theorem unknown_reference_refused :
    (run unknownReferenceGraph 10 1 unknownReferenceInitial).status = .invalid ∧
    ¬ Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      unknownReferenceGraph.catalogue.observationGraph 0 := by
  refine ⟨by decide, ?_⟩
  intro accepted
  have member : 1 ∈ unknownReferenceGraph.catalogue.deps 0 := by decide
  have child := accepted.child member
  have admitted := child.localOk
  simp [Catalogue.observationGraph, Graph.catalogue, unknownReferenceGraph] at admitted

/-- A single DFS dispatch can perform several prefix comparisons. Charging
only the dispatch would omit actual work already present in this service. -/
theorem one_dispatch_scans_a_prefix :
    let state := run depthFanGraph 100 7 depthFanInitial
    (step depthFanGraph 100 state).ticks = state.ticks + 1 ∧
      scanWork depthFanGraph 100 state = 4 ∧
      MachineCore.Attempts.cost (sliceMachine depthFanGraph 100)
        (callPrice depthFanGraph 100 (1 : Nat) 7) 1 state = 29 := by
  dsimp only
  refine ⟨by decide, by decide, ?_⟩
  rw [MachineCore.Attempts.cost_exact, MachineCore.sliceCost_succ]
  simp only [MachineCore.runSlice, sliceMachine]
  decide

/-- A finite observed component remains acceptable when an unrelated
component is cyclic. Global catalogue acyclicity is not required. -/
theorem unrelated_cycle_does_not_refuse_leaf :
    let graph : Graph := ⟨[[⟨1, none⟩], [⟨1, some 1⟩]]⟩
    let state := (init graph 0).get (by decide)
    bound? (run graph 10 3 state) = some 1 ∧ 1 ∈ graph.catalogue.deps 1 := by
  decide

def rawCycleGraph : Graph := ⟨[[⟨1, some 0⟩]]⟩

def rawCycleInitial : State := (init rawCycleGraph 0).get (by decide)

/-- A real back-edge is refused. Zero allowance retains the active frontier
and has no verdict; it must not be confused with either refusal or success. -/
theorem raw_cycle_refused_and_zero_incomplete :
    (run rawCycleGraph 10 1 rawCycleInitial).status = .cycle ∧
    bound? (run rawCycleGraph 10 1 rawCycleInitial) = none ∧
    (run rawCycleGraph 10 0 rawCycleInitial).status = .pending ∧
    bound? (run rawCycleGraph 10 0 rawCycleInitial) = none ∧
    (MachineCore.Attempts.trace (sliceMachine rawCycleGraph 10) 0 rawCycleInitial) = [] ∧
    ¬ Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation.Accepted
      rawCycleGraph.catalogue.observationGraph 0 := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, ?_⟩
  intro accepted
  apply accepted.no_cycle
  apply Relation.TransGen.single
  change 0 ∈ rawCycleGraph.catalogue.deps 0
  decide

/-- No scan comparisons occur after the cycle verdict, but an attempted
terminal check has a nonzero fixed price. Dispatch and scan counts alone
therefore do not price the producer callback. -/
theorem terminal_probe_has_price_without_scan :
    scanWork rawCycleGraph 10 (run rawCycleGraph 10 1 rawCycleInitial) = 0 ∧
    MachineCore.Attempts.cost (sliceMachine rawCycleGraph 10)
      (callPrice rawCycleGraph 10 (3 : Nat) 7) 1
      (run rawCycleGraph 10 1 rawCycleInitial) = 3 := by
  have stopped : (run rawCycleGraph 10 1 rawCycleInitial).status ≠ .pending := by decide
  refine ⟨scanWork_of_stopped rawCycleGraph 10 _ stopped, ?_⟩
  rw [MachineCore.Attempts.cost_exact]
  simp [MachineCore.sliceCost_of_final, MachineCore.runSlice, sliceMachine, stopped,
    callPrice, scanWork_of_stopped rawCycleGraph 10 _ stopped]

#print axioms Catalogue.FoldDerivation.accepted
#print axioms Catalogue.FoldDerivation.accessible
#print axioms Catalogue.FoldDerivation.no_reachable_cycle
#print axioms Valid.cached_accepted
#print axioms bound_accessible
#print axioms initialized_run_no_reachable_cycle
#print axioms initialized_reachable_cycle_no_bound
#print axioms sliceMachine_run
#print axioms init_valid
#print axioms step_valid
#print axioms structuralRank_push
#print axioms structuralRank_finish
#print axioms structuralRank_advance
#print axioms step_continuation_exact
#print axioms run_pending_reserve
#print axioms pending_below_administrative_ceiling
#print axioms run_stops_with_structural_allowance
#print axioms initialized_run_stops
#print axioms initialized_structural_ceiling
#print axioms sliceMachine_final_with_structural_allowance
#print axioms initialized_run_verdict
#print axioms step_indexVisits_bounds
#print axioms scan_account_exact
#print axioms attempted_scan_account_exact
#print axioms callPrice_le
#print axioms attempted_cost_le
#print axioms shared_dag_retains_completed_child
#print axioms shared_dag_scan_account
#print axioms shared_dag_structural_reserve
#print axioms administrative_refusals_do_not_disprove_finiteness
#print axioms unknown_reference_refused
#print axioms one_dispatch_scans_a_prefix
#print axioms unrelated_cycle_does_not_refuse_leaf
#print axioms raw_cycle_refused_and_zero_incomplete
#print axioms terminal_probe_has_price_without_scan

/-! ## Admission valuation and source frontier

`admissionValuation` interprets admitted rows by the existing dependency
fold. It does not execute them. The source frontier does: a pending list
of graph nodes and the number of matched rows already paid. Expanding the
head node adds that node's row count once, including a row whose answer
list is empty, and appends every linked successor occurrence. Repeated
child nodes stay repeated. The frontier stores the number, not an
admission log. Resumption is iteration of expansion, and an empty
pending list is a fixed point. `recorded` is the optional `List.iterate`
word of that same expansion; it is not frontier state. The native
compiled correspondence is a separate service boundary; this frontier
does not measure a worker schedule, and dependency depth is not that
span. -/

/-- One retained matched occurrence. `answers` is the returned collection. -/
structure MatchedAdmission where
  physical : Nat
  successor : Option Nat
  answers : List Nat
  deriving DecidableEq, Repr

def MatchedAdmission.occurrence (admission : MatchedAdmission) : Row :=
  ⟨admission.physical, admission.successor⟩

def rowAdmission (answersAt : Row → List Nat) (row : Row) : MatchedAdmission where
  physical := row.physical
  successor := row.successor
  answers := answersAt row

def rowAdmissions (rows : List Row) (answersAt : Row → List Nat) : List MatchedAdmission :=
  rows.map (rowAdmission answersAt)

theorem rowAdmissions_occurrence (rows : List Row) (answersAt : Row → List Nat) :
    (rowAdmissions rows answersAt).map MatchedAdmission.occurrence = rows := by
  rw [rowAdmissions, List.map_map]
  change rows.map id = rows
  exact List.map_id rows

/-- Returned answers, counted separately from admission work. -/
def returnedAnswerCount (admissions : List MatchedAdmission) : Nat :=
  (admissions.map (fun admission => admission.answers.length)).sum

/-- Row-aggregate reading of admitted occurrences. This is not a frontier step. -/
def admissionAggregate (admissions : List MatchedAdmission) (children : List WorkSpan) : WorkSpan :=
  prefixFold (admissions.map MatchedAdmission.occurrence) children

def Graph.admittedRows (graph : Graph) (answersAt : Row → List Nat) (node : Nat) :
    List MatchedAdmission :=
  rowAdmissions (graph.rows node) answersAt

def Graph.admissionCombine (graph : Graph) (answersAt : Row → List Nat)
    (node : Nat) (children : List WorkSpan) : WorkSpan :=
  admissionAggregate (graph.admittedRows answersAt node) children

/-- Dependency-fold reading of admitted rows. The answer annotation is an
input, not a summand. This is a valuation, not a frontier execution. -/
def Graph.admissionValuation (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (answersAt : Row → List Nat) : Nat → WorkSpan :=
  graph.catalogue.depFold acyclic (graph.admissionCombine answersAt)

theorem Graph.admissionCombine_eq_sourceCombine (graph : Graph) (answersAt : Row → List Nat)
    (node : Nat) (children : List WorkSpan)
    (aligned : children.length = successorCount (graph.rows node)) :
    graph.admissionCombine answersAt node children = graph.sourceCombine node children := by
  unfold Graph.admissionCombine admissionAggregate Graph.admittedRows
  rw [rowAdmissions_occurrence]
  exact prefixFold_eq_sourceCombine graph node children aligned

theorem Graph.admissionValuation_eq_sourceValuation (graph : Graph)
    (acyclic : graph.catalogue.Acyclic) (answersAt : Row → List Nat) (node : Nat) :
    graph.admissionValuation acyclic answersAt node = graph.sourceValuation acyclic node := by
  induction acc_of_accCode (acyclic.accCode node) with
  | intro node _ ih =>
    unfold Graph.admissionValuation Graph.sourceValuation
    rw [graph.catalogue.depFold_eq acyclic (graph.admissionCombine answersAt) node,
      graph.catalogue.depFold_eq acyclic graph.sourceCombine node]
    by_cases admitted : node ∈ graph.catalogue.items
    · rw [if_pos admitted, if_pos admitted]
      have children :
          (graph.catalogue.deps node).map
              (graph.catalogue.depFold acyclic (graph.admissionCombine answersAt)) =
            (graph.catalogue.deps node).map
              (graph.catalogue.depFold acyclic graph.sourceCombine) :=
        List.map_congr_left fun child member => by
          have step := ih child ⟨admitted, member⟩
          unfold Graph.admissionValuation Graph.sourceValuation at step
          exact step
      rw [children]
      have aligned :
          ((graph.catalogue.deps node).map
              (graph.catalogue.depFold acyclic graph.sourceCombine)).length =
            successorCount (graph.rows node) := by
        simp only [Graph.catalogue, successorCount, List.length_map]
      exact graph.admissionCombine_eq_sourceCombine answersAt node
        ((graph.catalogue.deps node).map
          (graph.catalogue.depFold acyclic graph.sourceCombine)) aligned
    · rw [if_neg admitted, if_neg admitted]
      have emptyRows : graph.rows node = [] := by
        unfold Graph.rows
        cases found : graph.nodes[node]? with
        | none => rfl
        | some rows =>
          obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
          have member : node ∈ graph.catalogue.items := by
            simp only [Graph.catalogue, List.mem_range]
            exact inside
          exact False.elim (admitted member)
      have aligned : ([] : List WorkSpan).length = successorCount (graph.rows node) := by
        rw [emptyRows]
        rfl
      exact graph.admissionCombine_eq_sourceCombine answersAt node [] aligned

theorem Graph.admissionValuation_work (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (answersAt : Row → List Nat) (node : Nat) :
    (graph.admissionValuation acyclic answersAt node).work =
      graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node := by
  rw [graph.admissionValuation_eq_sourceValuation acyclic answersAt node,
    graph.sourceValuation_work]

theorem Graph.admissionValuation_ignores_answers (graph : Graph)
    (acyclic : graph.catalogue.Acyclic) (first second : Row → List Nat) (node : Nat) :
    graph.admissionValuation acyclic first node = graph.admissionValuation acyclic second node := by
  rw [graph.admissionValuation_eq_sourceValuation acyclic first node,
    graph.admissionValuation_eq_sourceValuation acyclic second node]

/-- Sum of unfolding work over a pending node list. Multiplicity is kept. -/
def pendingWork (graph : Graph) (acyclic : graph.catalogue.Acyclic) (pending : List Nat) : Nat :=
  (pending.map (graph.catalogue.unfoldingWork acyclic
    (fun item => (graph.rows item).length))).sum

private theorem pendingWork_cons (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (node : Nat) (rest : List Nat) :
    pendingWork graph acyclic (node :: rest) =
      graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node +
        pendingWork graph acyclic rest := by
  simp [pendingWork, List.map_cons, List.sum_cons]

private theorem pendingWork_append (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (left right : List Nat) :
    pendingWork graph acyclic (left ++ right) =
      pendingWork graph acyclic left + pendingWork graph acyclic right := by
  induction left with
  | nil => simp [pendingWork]
  | cons head tail ih =>
    rw [List.cons_append, pendingWork_cons, pendingWork_cons, ih]
    omega

private theorem rows_of_outside (graph : Graph) {node : Nat}
    (outside : node ∉ graph.catalogue.items) : graph.rows node = [] := by
  unfold Graph.rows
  cases found : graph.nodes[node]? with
  | none => rfl
  | some rows =>
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
    have member : node ∈ graph.catalogue.items := by
      simp only [Graph.catalogue, List.mem_range]
      exact inside
    exact False.elim (outside member)

private theorem unfoldingWork_outside (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    {node : Nat} (outside : node ∉ graph.catalogue.items) :
    graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node = 0 := by
  have rows := rows_of_outside graph outside
  have eq := graph.catalogue.depFold_eq acyclic
    (fun item childWork => (graph.rows item).length + childWork.sum) node
  rw [if_neg outside] at eq
  simp [rows] at eq
  exact eq

private theorem deps_of_outside (graph : Graph) {node : Nat}
    (outside : node ∉ graph.catalogue.items) : graph.catalogue.deps node = [] := by
  simp [Graph.catalogue, rows_of_outside graph outside]

/-- Charging one node's matched rows and queueing its successor occurrences
is that node's unfolding work. -/
theorem pendingCharge_eq_unfolding (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (node : Nat) :
    (graph.rows node).length + pendingWork graph acyclic (graph.catalogue.deps node) =
      graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) node := by
  by_cases admitted : node ∈ graph.catalogue.items
  · rw [graph.catalogue.unfoldingWork_eq acyclic (fun item => (graph.rows item).length)
      node admitted]
    simp [pendingWork]
  · rw [rows_of_outside graph admitted, deps_of_outside graph admitted,
      unfoldingWork_outside graph acyclic admitted]
    simp [pendingWork]

/-- Pending graph nodes and the number of matched rows already paid.
This is the source algorithm: it stores a count, not an admission log. -/
structure SourceFrontier where
  paid : Nat
  pending : List Nat
  deriving DecidableEq, Repr

namespace SourceFrontier

def start (root : Nat) : SourceFrontier where
  paid := 0
  pending := [root]

/-- Expand the first pending node. Each matched row is charged once, by
row count. Every linked successor occurrence is retained, including a
repeated child. The count does not read returned answers. -/
def expand (graph : Graph) (frontier : SourceFrontier) : SourceFrontier :=
  match frontier.pending with
  | [] => frontier
  | node :: rest =>
    { paid := frontier.paid + (graph.rows node).length
      pending := rest ++ graph.catalogue.deps node }

def resume (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) : SourceFrontier :=
  match fuel with
  | 0 => frontier
  | fuel + 1 =>
    if frontier.pending.isEmpty then frontier
    else (frontier.expand graph).resume graph fuel

def accounts (frontier : SourceFrontier) (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source : Nat) : Prop :=
  frontier.paid + pendingWork graph acyclic frontier.pending = source

theorem start_accounts (graph : Graph) (acyclic : graph.catalogue.Acyclic) (root : Nat) :
    (start root).accounts graph acyclic
      (graph.catalogue.unfoldingWork acyclic (fun item => (graph.rows item).length) root) := by
  simp [start, accounts, pendingWork, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem expand_accounts (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source) :
    (frontier.expand graph).accounts graph acyclic source := by
  unfold expand accounts
  unfold accounts at balanced
  cases pending : frontier.pending with
  | nil => exact balanced
  | cons node rest =>
    rw [pending, pendingWork_cons] at balanced
    dsimp
    rw [pendingWork_append]
    have charge := pendingCharge_eq_unfolding graph acyclic node
    omega

theorem resume_accounts (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source) :
    (frontier.resume graph fuel).accounts graph acyclic source := by
  induction fuel generalizing frontier with
  | zero =>
    unfold resume
    exact balanced
  | succ fuel ih =>
    unfold resume
    split
    · exact balanced
    · exact ih (frontier.expand graph)
        (frontier.expand_accounts graph acyclic source balanced)

theorem completed_paid (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source)
    (done : (frontier.resume graph fuel).pending = []) :
    (frontier.resume graph fuel).paid = source := by
  have kept := frontier.resume_accounts graph acyclic source fuel balanced
  rw [accounts, done, pendingWork, List.map_nil, List.sum_nil, Nat.add_zero] at kept
  exact kept

/-- How a source-metric budget client stopped. `paused` means the caller
supplied no further steps while pending work remains. `finished` means that
pending list is empty. `insufficient` means the next matched-row charge
exceeds the remaining budget. Insufficiency keeps the ordinary frontier.
It is not an empty answer, and it is not the analysis runner's `.overflow`
status. -/
inductive BudgetStop where
  | paused
  | finished
  | insufficient
  deriving DecidableEq, Repr

/-- Ordinary frontier after a budgeted continuation, with the unspent source
budget and the number of admitted expansions. -/
structure BudgetRun where
  stop : BudgetStop
  frontier : SourceFrontier
  remaining : Nat
  steps : Nat
  deriving DecidableEq, Repr

/-- Admit expansions while each matched-row charge fits the remaining source
budget. The charge is `(graph.rows node).length`, the same charge as
`expand`, including a repeated successor. Refusal returns the current
frontier and the current budget. The metric is the finite acyclic catalogue's
unfolding work. It is not a budget for an arbitrary higher-order Prime
program. -/
def continueWithin (graph : Graph) (budget fuel : Nat) (frontier : SourceFrontier) : BudgetRun :=
  match fuel with
  | 0 =>
    if frontier.pending.isEmpty then
      { stop := .finished, frontier, remaining := budget, steps := 0 }
    else
      { stop := .paused, frontier, remaining := budget, steps := 0 }
  | fuel + 1 =>
    match frontier.pending with
    | [] => { stop := .finished, frontier, remaining := budget, steps := 0 }
    | node :: _ =>
      let charge := (graph.rows node).length
      if charge ≤ budget then
        let next := continueWithin graph (budget - charge) fuel (frontier.expand graph)
        { next with steps := next.steps + 1 }
      else
        { stop := .insufficient, frontier, remaining := budget, steps := 0 }

theorem continueWithin_resume (graph : Graph) (budget fuel : Nat) (frontier : SourceFrontier) :
    (continueWithin graph budget fuel frontier).frontier =
      frontier.resume graph (continueWithin graph budget fuel frontier).steps := by
  induction fuel generalizing frontier budget with
  | zero =>
    unfold continueWithin resume
    split <;> rfl
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending, resume]
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · have ihv := ih (budget - (graph.rows node).length) (frontier.expand graph)
        simp only [continueWithin, pending, fits, ↓reduceIte, resume, List.isEmpty_cons]
        exact ihv
      · simp only [continueWithin, pending, fits, ↓reduceIte, resume]

theorem continueWithin_spent (graph : Graph) (budget fuel : Nat) (frontier : SourceFrontier) :
    let ran := continueWithin graph budget fuel frontier
    ran.remaining ≤ budget ∧
      ran.frontier.paid = frontier.paid + (budget - ran.remaining) := by
  induction fuel generalizing frontier budget with
  | zero =>
    unfold continueWithin
    constructor
    · split <;> exact Nat.le_refl _
    · split <;> (dsimp; omega)
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending]
      omega
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · have stepped : (frontier.expand graph).paid =
            frontier.paid + (graph.rows node).length := by
          unfold expand
          rw [pending]
        have ihv := ih (budget - (graph.rows node).length) (frontier.expand graph)
        simp only [continueWithin, pending, fits, ↓reduceIte] at ihv ⊢
        obtain ⟨left, paid⟩ := ihv
        refine ⟨Nat.le_trans left (Nat.sub_le _ _), ?_⟩
        rw [paid, stepped]
        omega
      · simp only [continueWithin, pending, fits, ↓reduceIte]
        omega

theorem continueWithin_accounts (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source budget fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source) :
    (continueWithin graph budget fuel frontier).frontier.accounts graph acyclic source := by
  induction fuel generalizing frontier budget with
  | zero =>
    unfold continueWithin
    split <;> exact balanced
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending]
      exact balanced
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · simp only [continueWithin, pending, fits, ↓reduceIte]
        exact ih (budget - (graph.rows node).length) (frontier.expand graph)
          (frontier.expand_accounts graph acyclic source balanced)
      · simp only [continueWithin, pending, fits, ↓reduceIte]
        exact balanced

theorem continueWithin_paid_eq_pending_drop (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source budget fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source) :
    let ran := continueWithin graph budget fuel frontier
    ran.frontier.paid - frontier.paid =
      pendingWork graph acyclic frontier.pending -
        pendingWork graph acyclic ran.frontier.pending := by
  have kept := continueWithin_accounts graph acyclic source budget fuel frontier balanced
  have spent := continueWithin_spent graph budget fuel frontier
  rw [accounts] at balanced kept
  omega

theorem continueWithin_finished_pending (graph : Graph) (budget fuel : Nat)
    (frontier : SourceFrontier)
    (done : (continueWithin graph budget fuel frontier).stop = .finished) :
    (continueWithin graph budget fuel frontier).frontier.pending = [] := by
  induction fuel generalizing frontier budget with
  | zero =>
    unfold continueWithin at done ⊢
    cases empty : frontier.pending.isEmpty with
    | true =>
      rw [List.isEmpty_iff] at empty
      exact empty
    | false =>
      simp only [empty] at done
      cases done
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending]
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · simp only [continueWithin, pending, fits, ↓reduceIte] at done ⊢
        exact ih (budget - (graph.rows node).length) (frontier.expand graph) done
      · simp only [continueWithin, pending, fits, ↓reduceIte] at done
        cases done

theorem continueWithin_finished_paid (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source budget fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source)
    (done : (continueWithin graph budget fuel frontier).stop = .finished) :
    (continueWithin graph budget fuel frontier).frontier.paid = source := by
  have pending := continueWithin_finished_pending graph budget fuel frontier done
  have kept := continueWithin_accounts graph acyclic source budget fuel frontier balanced
  rw [accounts, pending, pendingWork, List.map_nil, List.sum_nil, Nat.add_zero] at kept
  exact kept

theorem continueWithin_paused_pending (graph : Graph) (budget fuel : Nat)
    (frontier : SourceFrontier)
    (paused : (continueWithin graph budget fuel frontier).stop = .paused) :
    (continueWithin graph budget fuel frontier).frontier.pending ≠ [] := by
  induction fuel generalizing frontier budget with
  | zero =>
    by_cases gone : frontier.pending = []
    · have flag : frontier.pending.isEmpty = true := by
        rw [List.isEmpty_iff]
        exact gone
      unfold continueWithin at paused
      rw [flag] at paused
      cases paused
    · have flag : frontier.pending.isEmpty = false := by
        cases mark : frontier.pending.isEmpty
        · rfl
        · rw [List.isEmpty_iff] at mark
          exact absurd mark gone
      unfold continueWithin at paused ⊢
      rw [flag]
      exact gone
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending] at paused
      cases paused
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · simp only [continueWithin, pending, fits, ↓reduceIte] at paused ⊢
        exact ih (budget - (graph.rows node).length) (frontier.expand graph) paused
      · simp only [continueWithin, pending, fits, ↓reduceIte] at paused
        cases paused

theorem continueWithin_insufficient (graph : Graph) (budget fuel : Nat)
    (frontier : SourceFrontier)
    (refused : (continueWithin graph budget fuel frontier).stop = .insufficient) :
    ∃ node rest,
      (continueWithin graph budget fuel frontier).frontier.pending = node :: rest ∧
        (continueWithin graph budget fuel frontier).remaining < (graph.rows node).length ∧
        (continueWithin graph budget fuel frontier).frontier =
          frontier.resume graph (continueWithin graph budget fuel frontier).steps := by
  induction fuel generalizing frontier budget with
  | zero =>
    unfold continueWithin at refused
    split at refused <;> cases refused
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      simp only [continueWithin, pending] at refused
      cases refused
    | cons node rest =>
      by_cases fits : (graph.rows node).length ≤ budget
      · simp only [continueWithin, pending, fits, ↓reduceIte] at refused ⊢
        obtain ⟨node', rest', pending', short, resumed⟩ :=
          ih (budget - (graph.rows node).length) (frontier.expand graph) refused
        refine ⟨node', rest', pending', short, ?_⟩
        rw [resume, pending, List.isEmpty_cons]
        exact resumed
      · simp only [continueWithin, pending, fits, ↓reduceIte] at refused ⊢
        refine ⟨node, rest, rfl, ?_, by unfold resume; rfl⟩
        omega

/-- One admitted step is `expand`. Linked successors stay in order, including
duplicates. `catalogue.deps` is not deduplicated. -/
theorem continueWithin_one_keeps_dependencies (graph : Graph) (budget : Nat)
    (frontier : SourceFrontier) {node : Nat} {rest : List Nat}
    (pending : frontier.pending = node :: rest)
    (fits : (graph.rows node).length ≤ budget) :
    (continueWithin graph budget 1 frontier).frontier.pending =
      rest ++ graph.catalogue.deps node := by
  have expanded : (frontier.expand graph).pending = rest ++ graph.catalogue.deps node := by
    unfold expand
    rw [pending]
  simp only [continueWithin, pending, fits, ↓reduceIte]
  split <;> exact expanded

/-- A refused step stays refused on a later attempt with the same remaining
budget. The frontier is unchanged. -/
theorem continueWithin_insufficient_retry (graph : Graph) (budget fuel more : Nat)
    (frontier : SourceFrontier)
    (refused : (continueWithin graph budget fuel frontier).stop = .insufficient) :
    let ran := continueWithin graph budget fuel frontier
    continueWithin graph ran.remaining (more + 1) ran.frontier =
      { stop := .insufficient, frontier := ran.frontier, remaining := ran.remaining, steps := 0 } := by
  obtain ⟨node, rest, pending, short, _⟩ :=
    continueWithin_insufficient graph budget fuel frontier refused
  simp only [continueWithin, pending, Nat.not_le_of_gt short, ↓reduceIte]

theorem expand_fixed (graph : Graph) (frontier : SourceFrontier)
    (done : frontier.pending = []) : frontier.expand graph = frontier := by
  unfold expand
  rw [done]

theorem resume_iterate (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    frontier.resume graph fuel = (expand graph)^[fuel] frontier := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases pending : frontier.pending with
    | nil =>
      have fixed := expand_fixed graph frontier pending
      rw [fixed]
      unfold resume
      rw [pending]
      simp [List.isEmpty_nil]
      exact (Function.iterate_fixed fixed fuel).symm
    | cons _ _ =>
      unfold resume
      rw [pending]
      simp [List.isEmpty_cons]
      exact ih (frontier.expand graph)

theorem resume_add (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    frontier.resume graph (first + second) =
      (frontier.resume graph first).resume graph second := by
  rw [resume_iterate, resume_iterate, resume_iterate, Nat.add_comm first second]
  exact Function.iterate_add_apply (expand graph) second first frontier

theorem resume_fixed (graph : Graph) (fuel : Nat) (frontier : SourceFrontier)
    (done : frontier.pending = []) : frontier.resume graph fuel = frontier := by
  rw [resume_iterate]
  exact Function.iterate_fixed (expand_fixed graph frontier done) fuel

/-- Optional recorded word of the same expansion. This is not the source
algorithm: the frontier keeps `paid` and `pending` only. -/
def recorded (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) : List SourceFrontier :=
  List.iterate (expand graph) frontier fuel

theorem recorded_prefix_states (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (List.range fuel).map (fun i => frontier.resume graph i) = frontier.recorded graph fuel := by
  rw [recorded, ← List.range_map_iterate]
  refine List.map_congr_left fun _ _ => ?_
  rw [resume_iterate]

theorem recorded_prefix (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    frontier.recorded graph (first + second) =
      frontier.recorded graph first ++
        (frontier.resume graph first).recorded graph second := by
  rw [recorded, recorded, recorded, List.iterate_add, resume_iterate]

theorem recorded_take (graph : Graph) (shorter longer : Nat) (frontier : SourceFrontier) :
    List.take shorter (frontier.recorded graph longer) =
      frontier.recorded graph (min shorter longer) := by
  simp only [recorded, List.take_iterate]

end SourceFrontier

/-! Two referring rows name the same successor, and one local row returns
nothing. The frontier charges every row. -/

def repeatedBranchGraph : Graph :=
  ⟨[[⟨1, some 1⟩, ⟨2, some 1⟩, ⟨3, none⟩], [⟨4, none⟩]]⟩

def repeatedBranchCertificate : repeatedBranchGraph.catalogue.Acyclic :=
  repeatedBranchGraph.catalogue.acyclic?.get (by decide)

def repeatedBranchAnswers : Row → List Nat := fun _ => []

private theorem repeatedBranch_leaf :
    repeatedBranchGraph.sourceValuation repeatedBranchCertificate 1 = ⟨1, 1⟩ := by
  rw [Graph.sourceValuation_eq repeatedBranchGraph repeatedBranchCertificate 1 (by decide)]
  rfl

private theorem repeatedBranch_root :
    repeatedBranchGraph.sourceValuation repeatedBranchCertificate 0 = ⟨5, 2⟩ := by
  rw [Graph.sourceValuation_eq repeatedBranchGraph repeatedBranchCertificate 0 (by decide)]
  change repeatedBranchGraph.sourceCombine 0
      [repeatedBranchGraph.sourceValuation repeatedBranchCertificate 1,
       repeatedBranchGraph.sourceValuation repeatedBranchCertificate 1] = ⟨5, 2⟩
  simp only [repeatedBranch_leaf]
  rfl

def repeatedBranchExpanded : SourceFrontier :=
  (SourceFrontier.start 0).expand repeatedBranchGraph

def repeatedBranchDone : SourceFrontier :=
  (SourceFrontier.start 0).resume repeatedBranchGraph 3

/-- Rows the depth-fan frontier charges: the root once and the one successor
five times. This list is a control reading, not frontier state. -/
def depthFanOccurrenceRows : List Row :=
  depthFanGraph.rows 0 ++ depthFanGraph.rows 1 ++ depthFanGraph.rows 1 ++
    depthFanGraph.rows 1 ++ depthFanGraph.rows 1 ++ depthFanGraph.rows 1

/-- Budget 10 admits the whole depth fan. The paid number is the quoted
unfolding work. Dependency depth, the transition count, and either answer
annotation are different numbers. The same quotation ignores the annotation.
This finite catalogue is not an arbitrary higher-order Prime analyzer. -/
theorem depth_fan_source_budget_completes :
    SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0) =
      { stop := .finished, frontier := { paid := 10, pending := [] },
        remaining := 0, steps := 6 } ∧
    (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid =
      (depthFanGraph.sourceValuation depthFanCertificate 0).work ∧
    (depthFanGraph.admissionValuation depthFanCertificate (fun _ => [0, 0]) 0).work =
      (depthFanGraph.sourceValuation depthFanCertificate 0).work ∧
    depthFanGraph.dependencyDepth depthFanCertificate 0 = 2 ∧
    returnedAnswerCount (rowAdmissions depthFanOccurrenceRows fun _ => []) = 0 ∧
    returnedAnswerCount (rowAdmissions depthFanOccurrenceRows fun _ => [0, 0]) = 20 ∧
    (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid ≠
      depthFanGraph.dependencyDepth depthFanCertificate 0 ∧
    (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid ≠
      (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).steps ∧
    (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid ≠
      returnedAnswerCount (rowAdmissions depthFanOccurrenceRows fun _ => []) ∧
    (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid ≠
      returnedAnswerCount (rowAdmissions depthFanOccurrenceRows fun _ => [0, 0]) := by
  have shape : SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0) =
      { stop := .finished, frontier := { paid := 10, pending := [] },
        remaining := 0, steps := 6 } := by
    decide
  have finished : (SourceFrontier.continueWithin depthFanGraph 10 6
      (SourceFrontier.start 0)).stop = .finished := by
    rw [shape]
  have paidSource := SourceFrontier.continueWithin_finished_paid depthFanGraph
    depthFanCertificate
    (depthFanGraph.catalogue.unfoldingWork depthFanCertificate
      (fun node => (depthFanGraph.rows node).length) 0)
    10 6 (SourceFrontier.start 0)
    (SourceFrontier.start_accounts depthFanGraph depthFanCertificate 0) finished
  have quoted : (depthFanGraph.sourceValuation depthFanCertificate 0).work =
      depthFanGraph.catalogue.unfoldingWork depthFanCertificate
        (fun node => (depthFanGraph.rows node).length) 0 := by
    rw [depthFanGraph.sourceValuation_work]
  have ignoredWork : (depthFanGraph.admissionValuation depthFanCertificate
      (fun _ => [0, 0]) 0).work =
      (depthFanGraph.sourceValuation depthFanCertificate 0).work := by
    rw [depthFanGraph.admissionValuation_ignores_answers depthFanCertificate
        (fun _ => [0, 0]) (fun _ => []) 0,
      depthFanGraph.admissionValuation_eq_sourceValuation]
  have depth := (depth_fan_binds_when_work_overflows).2.1
  have emptyAnswers : returnedAnswerCount (rowAdmissions depthFanOccurrenceRows fun _ => []) = 0 := by
    decide
  have doubledAnswers : returnedAnswerCount
      (rowAdmissions depthFanOccurrenceRows fun _ => [0, 0]) = 20 := by
    decide
  rw [shape] at paidSource
  have paidQuoted : (10 : Nat) = (depthFanGraph.sourceValuation depthFanCertificate 0).work := by
    rw [quoted]
    exact paidSource.symm
  refine ⟨shape, ?_, ignoredWork, depth, emptyAnswers, doubledAnswers, ?_, ?_, ?_, ?_⟩
  · rw [shape]
    exact paidQuoted
  · rw [shape, depth]
    decide
  · rw [shape]
    decide
  · rw [shape, emptyAnswers]
    decide
  · rw [shape, doubledAnswers]
    decide

/-- Budget 9 admits the root and four successor occurrences, then refuses the
last successor. Pending work stays `[1]`. The refusal is not a finished
frontier. The analysis runner's unfolding readout at ceiling 9 is a different
machine: that status is overflow and its bound is none. -/
theorem depth_fan_insufficient_budget_keeps_pending :
    SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0) =
      { stop := .insufficient, frontier := { paid := 9, pending := [1] },
        remaining := 0, steps := 5 } ∧
    (SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0)).frontier.pending ≠
      [] ∧
    (run depthFanGraph 9 9 depthFanInitial .unfolding).status = .overflow ∧
    bound? (run depthFanGraph 9 9 depthFanInitial .unfolding) = none := by
  have shape : SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0) =
      { stop := .insufficient, frontier := { paid := 9, pending := [1] },
        remaining := 0, steps := 5 } := by
    decide
  refine ⟨shape, ?_, depth_fan_binds_when_work_overflows.2.2.1,
    depth_fan_binds_when_work_overflows.2.2.2.1⟩
  rw [shape]
  decide

/-- One budgeted expansion of the repeated branch keeps both successor
occurrences. The dependency list is not deduplicated. -/
theorem repeated_branch_budget_keeps_duplicate_successors :
    (SourceFrontier.continueWithin repeatedBranchGraph 3 1 (SourceFrontier.start 0)).frontier.pending =
      [1, 1] := by
  have pending : (SourceFrontier.start 0).pending = 0 :: ([] : List Nat) := rfl
  have fits : (repeatedBranchGraph.rows 0).length ≤ 3 := by decide
  have kept := SourceFrontier.continueWithin_one_keeps_dependencies repeatedBranchGraph 3
    (SourceFrontier.start 0) pending fits
  have deps : repeatedBranchGraph.catalogue.deps 0 = [1, 1] := by decide
  rw [deps, List.nil_append] at kept
  exact kept

/-- Rows the numerical frontier charges: the root once and the successor
twice. This list is a control reading, not frontier state. -/
private def repeatedBranchChargedRows : List MatchedAdmission :=
  repeatedBranchGraph.admittedRows repeatedBranchAnswers 0
    ++ repeatedBranchGraph.admittedRows repeatedBranchAnswers 1
    ++ repeatedBranchGraph.admittedRows repeatedBranchAnswers 1

/-- One expansion charges the three root rows and keeps both successor
occurrences. The completed frontier pays five, the unfolding work. -/
theorem repeated_successor_frontier_pays :
    repeatedBranchExpanded.pending = [1, 1] ∧
    repeatedBranchExpanded.paid = 3 ∧
    repeatedBranchDone.pending = [] ∧
    repeatedBranchDone.paid = 5 ∧
    repeatedBranchDone.paid =
      repeatedBranchGraph.catalogue.unfoldingWork repeatedBranchCertificate
        (fun node => (repeatedBranchGraph.rows node).length) 0 := by
  have shape : repeatedBranchExpanded.pending = [1, 1] ∧
      repeatedBranchExpanded.paid = 3 ∧
      repeatedBranchDone.pending = [] ∧
      repeatedBranchDone.paid = 5 := by
    decide
  refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2, ?_⟩
  exact SourceFrontier.completed_paid repeatedBranchGraph repeatedBranchCertificate
    (repeatedBranchGraph.catalogue.unfoldingWork repeatedBranchCertificate
      (fun node => (repeatedBranchGraph.rows node).length) 0)
    3 (SourceFrontier.start 0)
    (SourceFrontier.start_accounts repeatedBranchGraph repeatedBranchCertificate 0)
    shape.2.2.1

/-- The same charged rows return no answers. Dependency depth is two.
Neither equals the numerical cost, and depth is not a native worker span. -/
theorem empty_answers_are_not_frontier_cost :
    returnedAnswerCount repeatedBranchChargedRows = 0 ∧
    repeatedBranchGraph.dependencyDepth repeatedBranchCertificate 0 = 2 ∧
    repeatedBranchDone.paid ≠ returnedAnswerCount repeatedBranchChargedRows ∧
    repeatedBranchDone.paid ≠
      repeatedBranchGraph.dependencyDepth repeatedBranchCertificate 0 := by
  have answers : returnedAnswerCount repeatedBranchChargedRows = 0 := by decide
  have depth : repeatedBranchGraph.dependencyDepth repeatedBranchCertificate 0 = 2 := by
    rw [← repeatedBranchGraph.sourceValuation_depth, repeatedBranch_root]
  obtain ⟨_, _, _, five, _⟩ := repeated_successor_frontier_pays
  refine ⟨answers, depth, ?_, ?_⟩
  · rw [answers, five]
    decide
  · rw [depth, five]
    decide

/-- The repeated successor stays in the pending list across a split
resumption. The optional trace's first step is a prefix of the combined
trace, and that trace is not the paid count. -/
theorem repeated_successor_resumption_splits :
    (SourceFrontier.start 0).resume repeatedBranchGraph 3 =
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1).resume repeatedBranchGraph 2 ∧
    (SourceFrontier.start 0).recorded repeatedBranchGraph 3 =
      (SourceFrontier.start 0).recorded repeatedBranchGraph 1 ++
        ((SourceFrontier.start 0).resume repeatedBranchGraph 1).recorded
          repeatedBranchGraph 2 ∧
    List.take 1 ((SourceFrontier.start 0).recorded repeatedBranchGraph 3) =
      (SourceFrontier.start 0).recorded repeatedBranchGraph 1 ∧
    (SourceFrontier.start 0).recorded repeatedBranchGraph 2 =
      [SourceFrontier.start 0, repeatedBranchExpanded] ∧
    repeatedBranchExpanded.pending = [1, 1] ∧
    ((SourceFrontier.start 0).recorded repeatedBranchGraph 3).length = 3 ∧
    repeatedBranchDone.paid = 5 := by
  obtain ⟨pending, _, _, five, _⟩ := repeated_successor_frontier_pays
  refine ⟨SourceFrontier.resume_add repeatedBranchGraph 1 2 (SourceFrontier.start 0),
    SourceFrontier.recorded_prefix repeatedBranchGraph 1 2 (SourceFrontier.start 0), ?_, ?_,
    pending, ?_, five⟩
  · have shorter : min 1 3 = 1 := by decide
    rw [← shorter]
    exact SourceFrontier.recorded_take repeatedBranchGraph 1 3 (SourceFrontier.start 0)
  · rw [← SourceFrontier.recorded_prefix_states]
    have range : List.range 2 = [0, 1] := by decide
    rw [range, List.map_cons, List.map_cons, List.map_nil, SourceFrontier.resume_iterate,
      SourceFrontier.resume_iterate, Function.iterate_zero_apply, Function.iterate_one]
    rfl
  · rw [SourceFrontier.recorded, List.length_iterate]

/-- Dropping one repeated successor keeps the paid number and leaves the
iteration. The optional trace is not required to see the loss. -/
def repeatedBranchDropped : SourceFrontier where
  paid := repeatedBranchExpanded.paid
  pending := [1]

theorem dropped_occurrence_breaks_iteration :
    repeatedBranchDropped.paid = repeatedBranchExpanded.paid ∧
    repeatedBranchDropped.pending = [1] ∧
    repeatedBranchExpanded.pending = [1, 1] ∧
    repeatedBranchDropped.resume repeatedBranchGraph 1 ≠
      (SourceFrontier.start 0).resume repeatedBranchGraph 2 := by
  obtain ⟨pending, _, _, _, _⟩ := repeated_successor_frontier_pays
  refine ⟨rfl, rfl, pending, ?_⟩
  have one : (SourceFrontier.start 0).resume repeatedBranchGraph 1 =
      repeatedBranchExpanded := by
    rw [SourceFrontier.resume_iterate, Function.iterate_one]
    rfl
  have split := SourceFrontier.resume_add repeatedBranchGraph 1 1 (SourceFrontier.start 0)
  rw [one, show (1 + 1) = 2 from rfl] at split
  rw [split, SourceFrontier.resume_iterate, Function.iterate_one]
  decide

end OccurrenceGraph

end Mettapedia.Algorithms.WellFoundedServices
