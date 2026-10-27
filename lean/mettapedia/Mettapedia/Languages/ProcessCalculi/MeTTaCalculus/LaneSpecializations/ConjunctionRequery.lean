import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.LaneSpecialization

/-!
# A conjunction re-queried after effects (the PeTTa lane) against the snapshot (the transform)

A `match` whose pattern is a conjunction `(, p q)` binds `p` first and then `q`. A transform fires
one commit at one store: every row of both conjuncts is computed there, and the template's
effects run afterwards, one answer at a time (**the snapshot reading**, `snapshot`). The Prime and
HE lanes answer this way. The PeTTa lane runs the conjunction as nested calls, each call seeing
the store as it is when the call starts: the rows of `p` come from the store at the start, and
for each of them the rows of `q` come from the store as the earlier answers' effects left it
(**the re-query reading**, `requery`).

* **The readings agree when the effects write nothing into the second conjunct's region**
  (`requery_eq_snapshot`): if no effect changes the rows of `q`, under any binding of `p`, then
  the answers and the final store are the same. Under that condition the PeTTa lane's `match` is
  the transform (`petta_conj_specializes`).
* **They differ otherwise** (`Controls.removal_into_region`): with `j 1, j 2, k 1, k 2` stored and
  a template that removes `k 2`, the snapshot answers four pairs and the re-query three. A
  template whose effect lands outside the region gives the same four pairs in both readings
  (`Controls.disjoint_effect`). These are the stores and templates of the runs on the five lanes.

The model is generic: rows are any functions of the store, so the theorem holds for every matcher
and every term layer. Only the effects' region matters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

universe u v w x

/-- A conjunction query: the rows of the first conjunct at a store, the rows of the second at a
store given a row of the first, the answer of a pair, and the effect an answer's template has on
the store when it is evaluated. -/
structure Conj (T : Type u) (α : Type v) (β : Type w) (Ans : Type x) where
  outer : List T → List α
  inner : α → List T → List β
  answer : α → β → Ans
  effect : Ans → List T → List T

namespace Conj

variable {T : Type u} {α : Type v} {β : Type w} {Ans : Type x} (c : Conj T α β Ans)

/-- Evaluate answers in order: each answer's effect applies to the store the previous left. -/
def effects (answers : List Ans) (s : List T) : List T := answers.foldl (fun s r => c.effect r s) s

/-- **The snapshot reading**: every row at the store of the call; then the effects, in row order. -/
def snapshot (xs : List T) : List Ans × List T :=
  let answers := (c.outer xs).flatMap fun a => (c.inner a xs).map (c.answer a)
  (answers, c.effects answers xs)

/-- One inner call: the rows of the second conjunct at the store as it is now, then their effects. -/
def innerRun (a : α) (s : List T) : List Ans × List T :=
  let answers := (c.inner a s).map (c.answer a)
  (answers, c.effects answers s)

/-- One step of the outer loop. -/
def requeryStep (acc : List Ans × List T) (a : α) : List Ans × List T :=
  (acc.1 ++ (c.innerRun a acc.2).1, (c.innerRun a acc.2).2)

/-- **The re-query reading**: the rows of the first conjunct at the store of the call; for each, in
order, an inner call at the store as the earlier answers left it. -/
def requery (xs : List T) : List Ans × List T := (c.outer xs).foldl c.requeryStep ([], xs)

/-- Effects **write nothing into the second conjunct's region** when no effect changes its rows,
under any binding of the first. -/
def RegionDisjoint : Prop := ∀ a r s, c.inner a (c.effect r s) = c.inner a s

variable {c}

theorem effects_append (rs rs' : List Ans) (s : List T) :
    c.effects (rs ++ rs') s = c.effects rs' (c.effects rs s) := by
  unfold effects
  rw [List.foldl_append]

theorem inner_effects (disjoint : c.RegionDisjoint) (a : α) (rs : List Ans) (s : List T) :
    c.inner a (c.effects rs s) = c.inner a s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      change c.inner a (c.effects rest (c.effect r s)) = c.inner a s
      rw [ih, disjoint]

theorem foldl_requeryStep (disjoint : c.RegionDisjoint) (xs : List T) :
    ∀ (as : List α) (acc : List Ans) (s : List T), (∀ a, c.inner a s = c.inner a xs) →
      as.foldl c.requeryStep (acc, s) =
        (acc ++ as.flatMap (fun a => (c.inner a xs).map (c.answer a)),
          c.effects (as.flatMap fun a => (c.inner a xs).map (c.answer a)) s) := by
  intro as
  induction as with
  | nil => intro acc s _; simp [effects]
  | cons a rest ih =>
      intro acc s same
      simp only [List.foldl_cons, requeryStep, innerRun, same a]
      have same' : ∀ b, c.inner b (c.effects ((c.inner a xs).map (c.answer a)) s) = c.inner b xs :=
        fun b => by rw [inner_effects disjoint, same]
      rw [ih _ _ same', List.flatMap_cons, effects_append, List.append_assoc]

/-- **When the effects write nothing into the second conjunct's region, the re-query reading is
the snapshot**: same answers in the same order, same final store. -/
theorem requery_eq_snapshot (disjoint : c.RegionDisjoint) (xs : List T) :
    c.requery xs = c.snapshot xs := by
  unfold requery snapshot
  rw [foldl_requeryStep disjoint xs _ [] xs fun _ => rfl]
  simp

end Conj

/-- The lane that observes the answers in order and the store after them. -/
noncomputable def answersAndStore (T : Type u) (Ans : Type x) :
    Lane (List T) Ans (List Ans × List T) (List Ans × List T) :=
  ⟨fun xs b => (b.toList, xs), id⟩

/-- **Under region-disjoint effects, the PeTTa lane's conjunction `match` is the transform**: the
two readings are lane-equivalent for the lane that sees answers, their order, and the store. -/
theorem petta_conj_specializes {T : Type u} {α : Type v} {β : Type w} {Ans : Type x}
    {c : Conj T α β Ans} (disjoint : c.RegionDisjoint) :
    (answersAndStore T Ans).Equiv c.requery c.snapshot :=
  fun xs => Conj.requery_eq_snapshot disjoint xs

namespace Controls

/-- Stored atoms, coded: `j n` is `10 + n`, `k n` is `20 + n`, `log a b` is `100 + 10 a + b`. -/
def conjRows (effect : ℕ × ℕ → List ℕ → List ℕ) : Conj ℕ ℕ ℕ (ℕ × ℕ) where
  outer xs := (xs.filter fun t => t / 10 = 1).map (· % 10)
  inner _ s := (s.filter fun t => t / 10 = 2).map (· % 10)
  answer a b := (a, b)
  effect := effect

/-- The store `j 1, j 2, k 1, k 2`. -/
def store : List ℕ := [11, 12, 21, 22]

/-- A template that removes `k 2` (every copy, as the PeTTa lane removes). -/
def removeK2 : ℕ × ℕ → List ℕ → List ℕ := fun _ s => s.filter (· ≠ 22)

/-- A template that adds `log a b`, outside the second conjunct's region. -/
def addLog : ℕ × ℕ → List ℕ → List ℕ := fun r s => s ++ [100 + 10 * r.1 + r.2]

/-- **An effect into the region separates the readings**: four pairs in the snapshot, three when
re-queried; the store ends without `k 2` in both. -/
theorem removal_into_region :
    (conjRows removeK2).snapshot store = ([(1, 1), (1, 2), (2, 1), (2, 2)], [11, 12, 21]) ∧
      (conjRows removeK2).requery store = ([(1, 1), (1, 2), (2, 1)], [11, 12, 21]) ∧
      ¬ (conjRows removeK2).RegionDisjoint := by
  refine ⟨by decide, by decide, fun disjoint => ?_⟩
  have := disjoint 1 (1, 1) store
  revert this
  decide

/-- **An effect outside the region**: the theorem applies, and the four pairs agree. -/
theorem disjoint_effect :
    (conjRows addLog).RegionDisjoint ∧
      (conjRows addLog).requery store = (conjRows addLog).snapshot store ∧
      ((conjRows addLog).snapshot store).1 = [(1, 1), (1, 2), (2, 1), (2, 2)] := by
  have disjoint : (conjRows addLog).RegionDisjoint := by
    intro a r s
    simp only [conjRows, addLog, List.filter_append, List.map_append]
    have : ((100 + 10 * r.1 + r.2) / 10 = 2) = False := by
      apply propext; constructor
      · intro h; omega
      · exact False.elim
    simp [this]
  exact ⟨disjoint, Conj.requery_eq_snapshot disjoint store, by decide⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations
