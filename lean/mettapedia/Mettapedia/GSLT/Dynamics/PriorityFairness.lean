import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex

/-!
# Priority and fairness

A scheduler holds a finite set of pending items, fires the least one under a
linear order (its priority, or MM2's least key), and the firing may add new
pending items (`Run`).

* **Starvation** (`Controls.starves`): if every firing regenerates work ahead of
  an item, the item stays pending and never fires.  So a priority scheduler is
  not weakly fair: an item that is always enabled need not ever fire
  (`Controls.priority_not_weakly_fair`).  This is the shape of the starvation
  of MM2's least-key queue by regenerated work at a smaller key.
* **No arrivals ahead, no starvation** (`fires_within`): if no item arrives
  ahead of `x` from some time on, `x` fires within as many steps as there are
  pending items ahead of it at that time.

Two repairs follow from the second theorem.

* **Fairness within a priority class** (`classFair`): order by priority, then by
  arrival.  An item fires once no higher-priority work arrives, whatever work of
  its own class keeps arriving.  Priority stays semantic: higher classes may
  still starve lower ones, and must, under strict priority.
* **Epochs** (`epoch_fires_within`): stamp each item with an epoch and order by
  epoch first.  When arrivals carry an epoch beyond every pending item, every
  item fires; priority is respected within an epoch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PriorityFairness

universe u

/-- A run of a least-first scheduler. -/
structure Run (α : Type u) [LinearOrder α] where
  pending : ℕ → Finset α
  fired : ℕ → α
  arrivals : ℕ → Finset α
  fired_mem : ∀ t, fired t ∈ pending t
  fired_least : ∀ t, ∀ y ∈ pending t, fired t ≤ y
  next : ∀ t, pending (t + 1) = (pending t).erase (fired t) ∪ arrivals t

namespace Run

variable {α : Type u} [LinearOrder α] (run : Run α)

/-- Pending items ahead of `x`. -/
def ahead (t : ℕ) (x : α) : Finset α := (run.pending t).filter (· < x)

theorem ahead_succ {t : ℕ} {x : α} (pending : x ∈ run.pending t) (notFired : run.fired t ≠ x)
    (behind : ∀ y ∈ run.arrivals t, x < y) :
    x ∈ run.pending (t + 1) ∧ (run.ahead (t + 1) x).card < (run.ahead t x).card := by
  have firedAhead : run.fired t < x :=
    lt_of_le_of_ne (run.fired_least t x pending) notFired
  constructor
  · rw [run.next t]
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨notFired.symm, pending⟩)
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨run.fired t, Finset.mem_filter.2 ⟨run.fired_mem t, firedAhead⟩, ?_⟩
      intro inNext
      obtain ⟨member, _⟩ := Finset.mem_filter.1 inNext
      rw [run.next t] at member
      rcases Finset.mem_union.1 member with erased | arrived
      · exact (Finset.mem_erase.1 erased).1 rfl
      · exact (lt_asymm firedAhead) (behind _ arrived)
    · intro y inNext
      obtain ⟨member, below⟩ := Finset.mem_filter.1 inNext
      rw [run.next t] at member
      rcases Finset.mem_union.1 member with erased | arrived
      · exact Finset.mem_filter.2 ⟨(Finset.mem_erase.1 erased).2, below⟩
      · exact absurd (behind y arrived) (not_lt.2 below.le)

/-- **No arrivals ahead, no starvation**: `x` fires within as many steps as
there are pending items ahead of it. -/
theorem fires_within {start : ℕ} {x : α} (pending : x ∈ run.pending start)
    (behind : ∀ t, start ≤ t → ∀ y ∈ run.arrivals t, x < y) :
    ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card ∧ run.fired t = x := by
  suffices key : ∀ n t, start ≤ t → x ∈ run.pending t → (run.ahead t x).card ≤ n →
      ∃ t', t ≤ t' ∧ t' ≤ t + (run.ahead t x).card ∧ run.fired t' = x by
    obtain ⟨t, le, bound, fired⟩ := key _ start le_rfl pending le_rfl
    exact ⟨t, le, bound, fired⟩
  intro n
  induction n with
  | zero =>
      intro t _ member count
      by_cases fired : run.fired t = x
      · exact ⟨t, le_rfl, Nat.le_add_right _ _, fired⟩
      · have := (run.ahead_succ member fired (behind t ‹_›)).2
        omega
  | succ n ih =>
      intro t later member count
      by_cases fired : run.fired t = x
      · exact ⟨t, le_rfl, Nat.le_add_right _ _, fired⟩
      · obtain ⟨member', smaller⟩ := run.ahead_succ member fired (behind t later)
        obtain ⟨t', le, bound, fired'⟩ :=
          ih (t + 1) (Nat.le_succ_of_le later) member' (by omega)
        exact ⟨t', Nat.le_of_succ_le le, by omega, fired'⟩

end Run

/-! ## Fairness within a priority class -/

/-- **Fairness within a priority class**: items are ordered by priority class,
then by arrival stamp.  An item fires once no work of a higher class arrives,
whatever work of its own class arrives later. -/
theorem classFair (run : Run (Lex (ℕ × ℕ))) {start : ℕ} {x : Lex (ℕ × ℕ)}
    (pending : x ∈ run.pending start)
    (noHigher : ∀ t, start ≤ t → ∀ y ∈ run.arrivals t, (ofLex x).1 ≤ (ofLex y).1)
    (later : ∀ t, start ≤ t → ∀ y ∈ run.arrivals t, (ofLex y).1 = (ofLex x).1 →
      (ofLex x).2 < (ofLex y).2) :
    ∃ t, start ≤ t ∧ run.fired t = x := by
  obtain ⟨t, le, _, fired⟩ := run.fires_within pending (by
    intro t after y arrived
    rcases lt_or_eq_of_le (noHigher t after y arrived) with lower | same
    · exact Prod.Lex.lt_iff.2 (Or.inl lower)
    · exact Prod.Lex.lt_iff.2 (Or.inr ⟨same, later t after y arrived same.symm⟩))
  exact ⟨t, le, fired⟩

/-! ## Epochs -/

section Epochs

variable {Key : Type u} [LinearOrder Key]

/-- **Epochs give fairness**: if every arrival carries an epoch beyond every
pending item, every pending item fires. -/
theorem epoch_fires_within (run : Run (Lex (ℕ × Key))) {start : ℕ} {x : Lex (ℕ × Key)}
    (pending : x ∈ run.pending start)
    (stamped : ∀ t, ∀ y ∈ run.arrivals t, ∀ z ∈ run.pending t, (ofLex z).1 < (ofLex y).1) :
    ∃ t, start ≤ t ∧ run.fired t = x := by
  -- `x` stays pending until it fires, so every arrival is behind it.
  have stays : ∀ t, start ≤ t → (∀ s, start ≤ s → s < t → run.fired s ≠ x) →
      x ∈ run.pending t := by
    intro t le
    induction t, le using Nat.le_induction with
    | base => exact fun _ => pending
    | succ t le ih =>
        intro notYet
        have member := ih fun s first before => notYet s first (Nat.lt_succ_of_lt before)
        rw [run.next t]
        exact Finset.mem_union_left _
          (Finset.mem_erase.2 ⟨(notYet t le (Nat.lt_succ_self t)).symm, member⟩)
  by_contra never
  simp only [not_exists, not_and] at never
  obtain ⟨t, le, _, fired⟩ := run.fires_within pending (by
    intro t after y arrived
    have member := stays t after fun s first _ => never s first
    exact Prod.Lex.lt_iff.2 (Or.inl (stamped t y arrived x member)))
  exact never t le fired

end Epochs

/-! ## Controls -/

namespace Controls

/-- Item `0` regenerates itself ahead of item `1` at every step. -/
def starvingRun : Run ℕ where
  pending _ := {0, 1}
  fired _ := 0
  arrivals _ := {0}
  fired_mem _ := by decide
  fired_least _ y member := Nat.zero_le y
  next _ := by decide

/-- **Starvation**: item `1` is pending forever and never fires. -/
theorem starves : (∀ t, 1 ∈ starvingRun.pending t) ∧ ∀ t, starvingRun.fired t ≠ 1 :=
  ⟨fun _ => show 1 ∈ ({0, 1} : Finset ℕ) by decide, fun _ => show (0 : ℕ) ≠ 1 by decide⟩

/-- A run is weakly fair when an item pending from some time on fires at or
after that time. -/
def WeaklyFair {α : Type u} [LinearOrder α] (run : Run α) : Prop :=
  ∀ x start, (∀ t, start ≤ t → x ∈ run.pending t) → ∃ t, start ≤ t ∧ run.fired t = x

/-- **Priority is not weakly fair.** -/
theorem priority_not_weakly_fair : ¬ WeaklyFair starvingRun := by
  intro fair
  obtain ⟨t, _, fired⟩ := fair 1 0 fun t _ => starves.1 t
  exact starves.2 t fired

end Controls

end Mettapedia.GSLT.Dynamics.PriorityFairness
