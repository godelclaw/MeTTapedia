import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceMachine
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceRenaming

/-!
# Spec stores and machine heaps

The correspondence used by the adequacy theorem. A list `φ` of machine cells
names the specification's cells: spec cell `ℓ` is machine cell `φ[ℓ]`.

* `ValRel φ` (from `CallTimeChoiceRenaming`): values equal up to that renaming
  of cells.
* `Corr φ σ w`: every spec cell is present in the machine heap with the same
  code, a related environment and a related cache (`pending`/`suspended`,
  `evaluating`/`evaluating`, `done`/`value`); `φ` has no repetition; and every
  heap cell's slot is below the world's allocation counter, so allocation
  never collides. Its emitted-event projection equals the specification trace.
* `OutRel φ`: outcomes related; the specification's `fail` is the machine's
  domain failure or its no-rule retry, and `blackhole` is its blackhole retry.

Machine cells outside `φ` are private to the machine: the cells that carry a
sequencing or call continuation and the fresh cells of resampling.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference

/-! ## Cells, stores and outcomes -/

/-- Related caches. -/
inductive MemoRel (φ : List CellId) : Memo → Cache MVal Empty → Prop where
  | pending : MemoRel φ .pending .suspended
  | evaluating (owner : EvaluatorId) : MemoRel φ .evaluating (.evaluating owner)
  | done {v : Val Nat} {v' : MVal} : ValRel φ v v' → MemoRel φ (.done v) (.value v')

theorem MemoRel.mono {φ φ' : List CellId} (hp : φ <+: φ') {m : Memo} {k : Cache MVal Empty}
    (h : MemoRel φ m k) : MemoRel φ' m k := by
  cases h with
  | pending => exact .pending
  | evaluating o => exact .evaluating o
  | done hv => exact .done (hv.mono hp)

/-- A spec cell and a machine cell record: same code, related environment and cache. -/
structure SuspRel (φ : List CellId) (s : Suspension)
    (rec : CellRecord (Comp × MEnv) MVal Empty) : Prop where
  code : rec.origin.1 = s.code
  env : EnvRel φ s.env rec.origin.2
  memo : MemoRel φ s.memo rec.cache

theorem SuspRel.mono {φ φ' : List CellId} (hp : φ <+: φ') {s : Suspension}
    {rec : CellRecord (Comp × MEnv) MVal Empty} (h : SuspRel φ s rec) : SuspRel φ' s rec :=
  ⟨h.code, h.env.mono hp, h.memo.mono hp⟩

/-- Every heap cell's slot is below the allocation counter. -/
def SlotBound (w : MWorld) : Prop :=
  ∀ c rec, w.heap.lookup c = some rec → c.slot < w.nextCell

/-- The store-heap correspondence. -/
structure Corr (φ : List CellId) (σ : Store) (w : MWorld) : Prop where
  length : φ.length = σ.cells.length
  nodup : φ.Nodup
  cells : ∀ (ℓ : Nat) (s : Suspension), σ.cells[ℓ]? = some s →
    ∃ (c : CellId) (rec : CellRecord (Comp × MEnv) MVal Empty),
      φ[ℓ]? = some c ∧ w.heap.lookup c = some rec ∧ SuspRel φ s rec
  slot : SlotBound w
  events : w.receipts.effects = σ.trace

/-- Related outcomes. -/
inductive OutRel (φ : List CellId) : Outcome → MOutcome → Prop where
  | ok {v : Val Nat} {v' : MVal} : ValRel φ v v' → OutRel φ (.ok v) (.value v')
  | failDomain : OutRel φ .fail (.retryableFault (.domain .fail))
  | failNoRule (c : CellId) : OutRel φ .fail (.retryableFault (.noRule c))
  | blackhole (c : CellId) : OutRel φ .blackhole (.retryableFault (.blackhole c))

/-- An answer related up to the naming of retained cells. -/
def OutcomeRel (r : Result) (o : MOutcome) : Prop := ∃ φ, OutRel φ r.1 o

/-- A related answer and the chronological emissions of its own branch. -/
def ObservationRel (r : Result) (observation : MOutcome × List Nat) : Prop :=
  OutcomeRel r observation.1 ∧ observation.2 = r.2.trace

theorem OutRel.mono {φ φ' : List CellId} (hp : φ <+: φ') {o : Outcome} {o' : MOutcome}
    (h : OutRel φ o o') : OutRel φ' o o' := by
  cases h with
  | ok hv => exact .ok (hv.mono hp)
  | failDomain => exact .failDomain
  | failNoRule c => exact .failNoRule c
  | blackhole c => exact .blackhole c

theorem OutRel.isOk_false {φ : List CellId} {o : Outcome} {o' : MOutcome} (h : OutRel φ o o')
    (hk : o.isOk = false) : ∃ r, o' = .retryableFault r := by
  cases h with
  | ok _ => simp [Outcome.isOk] at hk
  | failDomain => exact ⟨_, rfl⟩
  | failNoRule c => exact ⟨_, rfl⟩
  | blackhole c => exact ⟨_, rfl⟩

/-! ## Heap facts -/

/-- Worlds with the same heap and the same allocation counter. -/
theorem Corr.of_heap_eq {φ : List CellId} {σ : Store} {w w' : MWorld} (h : Corr φ σ w)
    (heap : w'.heap = w.heap) (next : w'.nextCell = w.nextCell)
    (events : w'.receipts.effects = w.receipts.effects := by
      simp [recorded, World.record, World.setKnownCache, World.fork]) : Corr φ σ w' where
  length := h.length
  nodup := h.nodup
  cells := by
    intro ℓ s hs
    obtain ⟨c, rec, hc, hl, hr⟩ := h.cells ℓ s hs
    exact ⟨c, rec, hc, by rw [heap]; exact hl, hr⟩
  slot := by
    intro c rec hl
    rw [heap] at hl
    rw [next]
    exact h.slot c rec hl
  events := events.trans h.events

theorem Corr.trace {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w) (e : Nat) :
    Corr φ (σ.emit e) (recorded w (.effect e)) where
  length := h.length
  nodup := h.nodup
  cells := fun ℓ s hs => h.cells ℓ s hs
  slot := h.slot
  events := by simp [recorded, World.record, Store.emit, h.events]

/-- A machine cell named by `φ` is in the heap with a slot below the counter. -/
theorem Corr.mem_slot {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w)
    {ℓ : Nat} {c : CellId} (hc : φ[ℓ]? = some c) : c.slot < w.nextCell := by
  have hlt : ℓ < σ.cells.length := by
    rw [← h.length]; exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨s, hs⟩ : ∃ s, σ.cells[ℓ]? = some s := ⟨σ.cells[ℓ], List.getElem?_eq_getElem hlt⟩
  obtain ⟨c', rec, hc', hl, _⟩ := h.cells ℓ s hs
  rw [hc] at hc'
  cases hc'
  exact h.slot c rec hl

/-- The cell a fresh allocation would use is not named by `φ`. -/
theorem Corr.fresh_not_mem {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w)
    (generation : Nat) : w.freshCell generation ∉ φ := by
  intro hm
  obtain ⟨ℓ, hℓ, he⟩ := List.getElem_of_mem hm
  have := h.mem_slot (List.getElem?_eq_some_iff.mpr ⟨hℓ, he⟩)
  simp [World.freshCell] at this

theorem Corr.fresh_absent {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w)
    (generation : Nat) : w.heap.lookup (w.freshCell generation) = none := by
  cases hl : w.heap.lookup (w.freshCell generation) with
  | none => rfl
  | some rec =>
      have := h.slot _ rec hl
      simp [World.freshCell] at this

/-- Allocation succeeds in a corresponding world. -/
theorem Corr.allocate {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w)
    (origin : Comp × MEnv) (generation : Nat) :
    ∃ w', w.allocate? origin generation = some (w', w.freshCell generation) := by
  simp only [World.allocate?, Heap.allocate?, Heap.lookup] at *
  have habs := h.fresh_absent generation
  simp only [Heap.lookup] at habs
  simp [habs]

theorem allocate_heap {w w' : MWorld} {origin : Comp × MEnv} {generation : Nat} {c : CellId}
    (ha : w.allocate? origin generation = some (w', c)) :
    w'.heap.lookup c = some ⟨origin, .suspended⟩ ∧
      (∀ c', c' ≠ c → w'.heap.lookup c' = w.heap.lookup c') ∧
      w'.nextCell = w.nextCell + 1 ∧ c = w.freshCell generation :=
  ⟨World.allocate?_lookup_same ha, fun _ hne => World.allocate?_preserves_other ha hne,
    World.allocate?_nextCell ha, World.allocate?_fresh_cell ha⟩

/-- A world after allocation still corresponds to the same store. -/
theorem Corr.after_allocate {φ : List CellId} {σ : Store} {w w' : MWorld}
    {origin : Comp × MEnv} {generation : Nat} {c : CellId}
    (h : Corr φ σ w) (ha : w.allocate? origin generation = some (w', c)) : Corr φ σ w' := by
  obtain ⟨hnew, hother, hnext, hc⟩ := allocate_heap ha
  refine ⟨h.length, h.nodup, ?_, ?_, (World.allocate?_effects ha).trans h.events⟩
  · intro ℓ s hs
    obtain ⟨c', rec, hc', hl, hr⟩ := h.cells ℓ s hs
    refine ⟨c', rec, hc', ?_, hr⟩
    have hne : c' ≠ c := by
      intro he; subst he; rw [hc] at hc'
      exact h.fresh_not_mem generation (List.mem_of_getElem? hc')
    rw [hother c' hne]; exact hl
  · intro c' rec hl
    rw [hnext]
    by_cases he : c' = c
    · subst he; rw [hc]; simp [World.freshCell]
    · rw [hother c' he] at hl
      exact Nat.lt_succ_of_lt (h.slot c' rec hl)

/-- Allocation of a related spec cell and machine cell extends the correspondence. -/
theorem Corr.alloc_cell {φ : List CellId} {σ : Store} {w w' : MWorld}
    {m : Comp} {ρ : List (Val Nat)} {ρ' : MEnv} {c : CellId}
    (h : Corr φ σ w) (hρ : EnvRel φ ρ ρ') (ha : w.allocate? (m, ρ') 0 = some (w', c)) :
    Corr (φ ++ [c]) (σ.alloc m ρ) w' := by
  obtain ⟨hnew, hother, hnext, hc⟩ := allocate_heap ha
  have hp : φ <+: φ ++ [c] := List.prefix_append φ [c]
  have hw' := h.after_allocate ha
  refine ⟨by simp [Store.alloc, h.length], ?_, ?_, hw'.slot, hw'.events⟩
  · rw [List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton c, ?_⟩
    intro a hamem b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    subst hab
    rw [hc] at hamem
    exact h.fresh_not_mem 0 hamem
  · intro ℓ s hs
    simp only [Store.alloc] at hs
    by_cases hℓ : ℓ < σ.cells.length
    · rw [List.getElem?_append_left hℓ] at hs
      obtain ⟨c', rec, hc', hl, hr⟩ := hw'.cells ℓ s hs
      exact ⟨c', rec, by rw [List.getElem?_append_left (h.length ▸ hℓ)]; exact hc', hl,
        hr.mono hp⟩
    · have hge : σ.cells.length ≤ ℓ := Nat.le_of_not_lt hℓ
      rw [List.getElem?_append_right hge] at hs
      have hz : ℓ - σ.cells.length = 0 := by
        cases hk : ℓ - σ.cells.length with
        | zero => rfl
        | succ k => rw [hk] at hs; simp at hs
      rw [hz] at hs
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      have hℓeq : ℓ = φ.length := by rw [h.length]; omega
      refine ⟨c, ⟨(m, ρ'), .suspended⟩, ?_, hnew, ?_⟩
      · rw [hℓeq]; simp
      · exact ⟨rfl, hρ.mono hp, .pending⟩

/-- Changing the record of a cell that `φ` does not name keeps the correspondence. -/
theorem Corr.set_private {φ : List CellId} {σ : Store} {w w' : MWorld} {c : CellId}
    (h : Corr φ σ w) (hc : c ∉ φ)
    (other : ∀ c', c' ≠ c → w'.heap.lookup c' = w.heap.lookup c')
    (present : ∀ rec', w'.heap.lookup c = some rec' → ∃ rec, w.heap.lookup c = some rec)
    (next : w'.nextCell = w.nextCell)
    (events : w'.receipts.effects = w.receipts.effects := by
      simp [recorded, World.record, World.setKnownCache, World.fork]) : Corr φ σ w' := by
  refine ⟨h.length, h.nodup, ?_, ?_, events.trans h.events⟩
  · intro ℓ s hs
    obtain ⟨c', rec, hc', hl, hr⟩ := h.cells ℓ s hs
    have hne : c' ≠ c := by
      intro he; subst he; exact hc (List.mem_of_getElem? hc')
    exact ⟨c', rec, hc', by rw [other c' hne]; exact hl, hr⟩
  · intro c' rec hl
    rw [next]
    by_cases he : c' = c
    · subst he
      obtain ⟨rec₀, hl₀⟩ := present rec hl
      exact h.slot c' rec₀ hl₀
    · rw [other c' he] at hl
      exact h.slot c' rec hl

/-- Changing the record of the cell `φ[ℓ]`, with a related cache change on the spec
side, keeps the correspondence. -/
theorem Corr.set_named {φ : List CellId} {σ : Store} {w w' : MWorld} {ℓ : Nat} {c : CellId}
    {s : Suspension} {memo : Memo} {rec' : CellRecord (Comp × MEnv) MVal Empty}
    (h : Corr φ σ w) (hc : φ[ℓ]? = some c) (hs : σ.cells[ℓ]? = some s)
    (hnew : w'.heap.lookup c = some rec')
    (hrel : SuspRel φ { s with memo := memo } rec')
    (other : ∀ c', c' ≠ c → w'.heap.lookup c' = w.heap.lookup c')
    (next : w'.nextCell = w.nextCell)
    (events : w'.receipts.effects = w.receipts.effects := by
      simp [recorded, World.record, World.setKnownCache, World.fork]) : Corr φ (σ.setMemo ℓ memo) w' := by
  refine ⟨by simp [Store.setMemo, h.length], h.nodup, ?_, ?_, events.trans h.events⟩
  · intro ℓ' s' hs'
    simp only [Store.setMemo, List.getElem?_modify] at hs'
    by_cases he : ℓ = ℓ'
    · subst he
      rw [hs] at hs'
      simp only [if_true, Option.map_eq_map, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      exact ⟨c, rec', hc, hnew, hrel⟩
    · simp only [he, if_false, Option.map_eq_map, Option.map_id'] at hs'
      obtain ⟨c', rec, hc', hl, hr⟩ := h.cells ℓ' s' hs'
      have hne : c' ≠ c := by
        intro hcc; subst hcc
        obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.mp hc
        obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.mp hc'
        exact he ((List.Nodup.getElem_inj_iff h.nodup (hi := hi) (hj := hj)).mp
          (hci.trans hcj.symm))
      exact ⟨c', rec, hc', by rw [other c' hne]; exact hl, hr⟩
  · intro c' rec hl
    rw [next]
    by_cases he : c' = c
    · subst he
      exact h.mem_slot hc
    · rw [other c' he] at hl
      exact h.slot c' rec hl

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
