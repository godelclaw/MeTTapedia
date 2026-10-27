import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Gaps

/-!
# Laws of `await`, `whenever` and `choose`

A program's parked processes are occurrences in the store beside its data. A parked process waits
on a transform: once (`await t`), on every enabling (`whenever t`), or on the first of several to
fire (`choose ts`). The transform's ground rows say what one firing takes, keeps, queries and
makes (`rows t`); the rules a program generates (`Fires`) add the parked process itself:

* `await t` fires a row and is taken: a linear occurrence;
* `whenever t` fires a row and is kept: each firing reads the rule, so firings do not serialize;
* `choose ts` fires a row of one of its transforms and is taken, which withdraws the others.

A **data row** touches only data: what it takes, keeps and queries is data (`DataRows`); its
template may make parked processes (the continuation). Over data rows, parked processes are seen
only by their own firings, and the laws below hold under bisimilarity over borrowed contexts, for
every admissible class.

## Laws

* **`whenever` is replication** (`whenever_absorbs_await`): beside a parked `whenever t`, one more
  `await t` changes nothing; in particular `whenever t ≅ await t | whenever t`, the law `!P ≅ P | !P`.
  Likewise `whenever t ≅ whenever t | whenever t` (`whenever_idempotent`).
* **Two linear parked processes with interchangeable rows are bisimilar** (`linear_similar_rows`;
  rows are interchangeable when they use the same bag, close the same regions and have the same
  effect). With the same rows (`linear_same_rows`): `choose [t] ≅ await t`, `choose` is commutative
  and idempotent on its list of transforms, and a branch with no rows can be dropped
  (`choose_singleton`, `choose_perm`, `choose_dead_branch`).

## Separations

* **Once against always** (`Controls.once_not_always`): beside two messages, `await t` fires once
  and `whenever t` twice.
* **One choice against two waits** (`Controls.choose_not_par`): `choose [t, s]` fires one branch,
  `await t | await s` both.
* **Replication fails over bags when copies are counted**
  (`Controls.replication_fails_when_counted`): a rule that queries the region of `t`'s parked
  processes (for instance "exactly one waiter") tells `whenever t` from `await t | whenever t`. In a
  bag the number of copies is an observable as soon as a predicate query can reach the parked
  processes; the replication law needs parked processes to be opaque to every rule but their own.

## A limit of the equivalence

* **Peek and take-and-remake are bisimilar** (`Controls.peek_vs_take_remake`): a parked process
  that reads a message and one that takes it and makes it again in the same commit have the same
  labels and the same results. They differ in independence (two peeks commute, two
  take-and-remakes of one message clash: the basis module's `keep_not_take_remake`). The
  equivalence here interleaves single commits; telling the two apart needs a true-concurrency
  equivalence (steps labelled by sets of independent commits).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Agents

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v w

/-- A parked process: once, always, or the first of several. -/
inductive Agent (T : Type u) where
  | await (t : T)
  | whenever (t : T)
  | choose (ts : List T)
  deriving DecidableEq

/-- Labels: data, and parked processes. -/
inductive Lbl (D : Type v) (T : Type u) where
  | data (d : D)
  | agent (a : Agent T)
  deriving DecidableEq

namespace Lbl

/-- A label is data. -/
def IsData {D : Type v} {T : Type u} : Lbl D T → Prop
  | data _ => True
  | agent _ => False

end Lbl

/-- A parked process is linear when its firings take it. -/
def Agent.Linear {T : Type u} : Agent T → Prop
  | .whenever _ => False
  | _ => True

variable {D : Type v} {T : Type u} [DecidableEq D] [DecidableEq T]

/-- **The rules a program generates.** -/
inductive Fires (rows : T → Rule (Lbl D T) → Prop) : Rule (Lbl D T) → Prop
  | await {t : T} {r : Rule (Lbl D T)} : rows t r →
      Fires rows ⟨.agent (.await t) ::ₘ r.take, r.keep, r.make, r.closed⟩
  | whenever {t : T} {r : Rule (Lbl D T)} : rows t r →
      Fires rows ⟨r.take, .agent (.whenever t) ::ₘ r.keep, r.make, r.closed⟩
  | choose {ts : List T} {t : T} {r : Rule (Lbl D T)} : t ∈ ts → rows t r →
      Fires rows ⟨.agent (.choose ts) ::ₘ r.take, r.keep, r.make, r.closed⟩

/-- Rows touch only data. -/
def DataRows (rows : T → Rule (Lbl D T) → Prop) : Prop :=
  ∀ t r, rows t r → (∀ x ∈ r.redex, x.IsData) ∧ ∀ x, r.closed x = true → x.IsData

/-- The rows a linear parked process fires with. -/
def LinRows (rows : T → Rule (Lbl D T) → Prop) : Agent T → Rule (Lbl D T) → Prop
  | .await t => rows t
  | .whenever _ => fun _ => False
  | .choose ts => fun r => ∃ t ∈ ts, rows t r

/-- A linear firing: the parked process and a row. -/
def linearRule (a : Agent T) (r : Rule (Lbl D T)) : Rule (Lbl D T) :=
  ⟨.agent a ::ₘ r.take, r.keep, r.make, r.closed⟩

/-! ## Bag helpers -/

section Bags

variable {α : Type w} [DecidableEq α]

theorem cons_sub_of_le {l Z : Multiset α} (x : α) (sub : l ≤ Z) : (x ::ₘ Z) - l = x ::ₘ (Z - l) := by
  ext y
  have := Multiset.le_iff_count.mp sub y
  simp only [Multiset.count_sub, Multiset.count_cons]
  split_ifs <;> omega

theorem le_of_le_cons_not_mem {l Z : Multiset α} {x : α} (sub : l ≤ x ::ₘ Z) (notMem : x ∉ l) :
    l ≤ Z := by
  rw [Multiset.le_iff_count] at sub ⊢
  intro y
  have := sub y
  by_cases h : y = x
  · subst h; rw [Multiset.count_eq_zero.mpr notMem]; exact Nat.zero_le _
  · simpa [Multiset.count_cons, h] using this

theorem cons_le_of_mem {l Z : Multiset α} {x : α} (mem : x ∈ Z) (notMem : x ∉ l) (sub : l ≤ Z) :
    x ::ₘ l ≤ Z := by
  rw [Multiset.le_iff_count] at sub ⊢
  intro y
  have := sub y
  by_cases h : y = x
  · subst h
    rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr notMem]
    exact Multiset.count_pos.mpr mem
  · simpa [Multiset.count_cons, h] using this

theorem sub_cons_cons (x : α) (Z l : Multiset α) : (x ::ₘ Z) - (x ::ₘ l) = Z - l := by
  ext y
  simp only [Multiset.count_sub, Multiset.count_cons]
  split_ifs <;> omega

theorem cons_result {take Z : Multiset α} (x : α) (sub : take ≤ Z) (make : Multiset α) :
    (x ::ₘ Z) - take + make = x ::ₘ (Z - take + make) := by
  rw [cons_sub_of_le x sub, Multiset.cons_add]

end Bags

/-! ## The shape of the generated rules -/

section Shape

variable {rows : T → Rule (Lbl D T) → Prop}

omit [DecidableEq D] [DecidableEq T] in
theorem linearRule_redex (a : Agent T) (r : Rule (Lbl D T)) :
    (linearRule a r).redex = .agent a ::ₘ r.redex := by
  simp [linearRule, Rule.redex, Multiset.cons_add]

omit [DecidableEq D] [DecidableEq T] in
theorem fires_linearRule {a : Agent T} {r : Rule (Lbl D T)} (h : LinRows rows a r) :
    Fires rows (linearRule a r) := by
  cases a with
  | await t => exact Fires.await h
  | whenever t => exact h.elim
  | choose ts =>
      obtain ⟨t, member, row⟩ := h
      exact Fires.choose member row

omit [DecidableEq D] [DecidableEq T] in
theorem agent_not_mem_row (data : DataRows rows) {t : T} {r : Rule (Lbl D T)} (row : rows t r)
    (a : Agent T) : Lbl.agent a ∉ r.redex := fun member => (data t r row).1 _ member

omit [DecidableEq D] [DecidableEq T] in
/-- A generated rule closes no parked process. -/
theorem closed_agent (data : DataRows rows) {ρ : Rule (Lbl D T)} (fires : Fires rows ρ)
    (a : Agent T) : ρ.closed (.agent a) = false := by
  have key : ∀ {t r}, rows t r → r.closed (.agent a) = false := by
    intro t r row
    cases h : r.closed (.agent a)
    · rfl
    · exact ((data t r row).2 _ h).elim
  cases fires with
  | @await t r row => exact key (t := t) (r := r) row
  | @whenever t r row => exact key (t := t) (r := r) row
  | @choose ts t r _ row => exact key (t := t) (r := r) row

omit [DecidableEq D] [DecidableEq T] in
/-- A parked process avoids every region a generated rule closes. -/
theorem agents_avoid (data : DataRows rows) {ρ : Rule (Lbl D T)} (fires : Fires rows ρ)
    {A : Multiset (Lbl D T)} (agents : ∀ x ∈ A, ¬ x.IsData) : Avoids A ρ.closed := by
  intro x member
  cases x with
  | data d => exact ((agents _ member) trivial).elim
  | agent a => exact closed_agent data fires a

omit [DecidableEq D] [DecidableEq T] in
/-- **A generated rule that uses a linear parked process is that process's own firing.** -/
theorem linear_mem_redex (data : DataRows rows) {ρ : Rule (Lbl D T)} (fires : Fires rows ρ)
    {a : Agent T} (linear : a.Linear) (member : Lbl.agent a ∈ ρ.redex) :
    ∃ r, LinRows rows a r ∧ ρ = linearRule a r := by
  cases fires with
  | @await t r row =>
      have : Lbl.agent a ∈ Lbl.agent (.await t) ::ₘ r.redex := by
        simpa [Rule.redex, Multiset.cons_add] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h; exact ⟨r, row, rfl⟩
      · exact absurd h (agent_not_mem_row data row a)
  | @whenever t r row =>
      have : Lbl.agent a ∈ Lbl.agent (.whenever t) ::ₘ r.redex := by
        simp only [Rule.redex] at member
        rw [Multiset.add_cons] at member
        simpa [Rule.redex] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h; exact linear.elim
      · exact absurd h (agent_not_mem_row data row a)
  | @choose ts t r tmem row =>
      have : Lbl.agent a ∈ Lbl.agent (.choose ts) ::ₘ r.redex := by
        simpa [Rule.redex, Multiset.cons_add] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h; exact ⟨r, ⟨t, tmem, row⟩, rfl⟩
      · exact absurd h (agent_not_mem_row data row a)

omit [DecidableEq D] [DecidableEq T] in
/-- A generated rule never takes a `whenever`. -/
theorem whenever_not_taken (data : DataRows rows) {ρ : Rule (Lbl D T)} (fires : Fires rows ρ)
    (t : T) : Lbl.agent (.whenever t) ∉ ρ.take := by
  cases fires with
  | @await s r row =>
      intro member
      rcases Multiset.mem_cons.mp member with h | h
      · cases h
      · exact agent_not_mem_row data row _ (Multiset.mem_of_le (Rule.take_le_redex r) h)
  | @whenever s r row =>
      intro member
      exact agent_not_mem_row data row _ (Multiset.mem_of_le (Rule.take_le_redex r) member)
  | @choose ts s r _ row =>
      intro member
      rcases Multiset.mem_cons.mp member with h | h
      · cases h
      · exact agent_not_mem_row data row _ (Multiset.mem_of_le (Rule.take_le_redex r) h)

/-- The firing of `whenever t` with a row. -/
def wheneverRule (t : T) (r : Rule (Lbl D T)) : Rule (Lbl D T) :=
  ⟨r.take, .agent (.whenever t) ::ₘ r.keep, r.make, r.closed⟩

omit [DecidableEq D] [DecidableEq T] in
theorem wheneverRule_redex (t : T) (r : Rule (Lbl D T)) :
    (wheneverRule t r).redex = .agent (.whenever t) ::ₘ r.redex := by
  simp [wheneverRule, Rule.redex, Multiset.add_cons]

omit [DecidableEq D] [DecidableEq T] in
/-- A generated rule that uses a `whenever t` is one of its firings. -/
theorem whenever_mem_redex (data : DataRows rows) {ρ : Rule (Lbl D T)} (fires : Fires rows ρ)
    {t : T} (member : Lbl.agent (.whenever t) ∈ ρ.redex) :
    ∃ r, rows t r ∧ ρ = wheneverRule t r := by
  cases fires with
  | @await s r row =>
      have : Lbl.agent (.whenever t) ∈ Lbl.agent (.await s) ::ₘ r.redex := by
        simpa [Rule.redex, Multiset.cons_add] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h
      · exact absurd h (agent_not_mem_row data row _)
  | @whenever s r row =>
      have : Lbl.agent (.whenever t) ∈ Lbl.agent (.whenever s) ::ₘ r.redex := by
        simp only [Rule.redex] at member
        rw [Multiset.add_cons] at member
        simpa [Rule.redex] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h; exact ⟨r, row, rfl⟩
      · exact absurd h (agent_not_mem_row data row _)
  | @choose ts s r _ row =>
      have : Lbl.agent (.whenever t) ∈ Lbl.agent (.choose ts) ::ₘ r.redex := by
        simpa [Rule.redex, Multiset.cons_add] using member
      rcases Multiset.mem_cons.mp this with h | h
      · cases h
      · exact absurd h (agent_not_mem_row data row _)

end Shape

/-! ## Two linear parked processes with the same rows -/

section Linear

variable {rows : T → Rule (Lbl D T) → Prop} {Adm : Lbl D T → Prop} {ι : Type w}
  {obs : ι → Lbl D T → Prop}

omit [DecidableEq D] [DecidableEq T] in
theorem swapRel_comm {a b : Lbl D T} {X Y : Multiset (Lbl D T)} (h : SwapRel b a X Y) :
    SwapRel a b X Y := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- Two rows are **interchangeable** when they use the same bag, close the same regions, and
have the same effect on every bag that holds what they use. -/
def Interchangeable (r r' : Rule (Lbl D T)) : Prop :=
  r'.redex = r.redex ∧ r'.closed = r.closed ∧
    ∀ W : Multiset (Lbl D T), r.redex ≤ W → W - r.take + r.make = W - r'.take + r'.make

theorem interchangeable_refl (r : Rule (Lbl D T)) : Interchangeable r r := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- A step that borrows nothing, at a bag holding the parked process `a`, is matched at the bag
holding `b` instead, when `a` and `b` are linear with interchangeable rows. -/
theorem swap_step (data : DataRows rows) {a b : Agent T} (la : a.Linear)
    (sim : ∀ r, LinRows rows a r → ∃ r', LinRows rows b r' ∧ Interchangeable r r')
    {Z P' : Multiset (Lbl D T)} {F : Lbl D T → Bool}
    (step : BStep (Fires rows) (.agent a ::ₘ Z) ⟨0, F⟩ P') :
    ∃ Q', BStep (Fires rows) (.agent b ::ₘ Z) ⟨0, F⟩ Q' ∧ SwapRel (.agent a) (.agent b) P' Q' := by
  obtain ⟨ρ, fires, step⟩ := step
  obtain ⟨-, hF, ⟨sub, avoids⟩, hP⟩ := Rule.step_iff_enabled.mp step
  simp only [add_zero] at sub avoids hP
  by_cases member : Lbl.agent a ∈ ρ.redex
  · obtain ⟨r, row, rfl⟩ := linear_mem_redex data fires la member
    rw [linearRule_redex] at sub avoids
    have subZ : r.redex ≤ Z := (Multiset.cons_le_cons_iff _).mp sub
    rw [sub_cons_cons] at avoids
    obtain ⟨r', rowB, sameRedex, sameClosed, sameEffect⟩ := sim r row
    have firesB := fires_linearRule rowB
    have subB : (linearRule b r').redex ≤ .agent b ::ₘ Z := by
      rw [linearRule_redex, sameRedex]; exact (Multiset.cons_le_cons_iff _).mpr subZ
    have frameB : (.agent b ::ₘ Z) - (linearRule b r').redex = Z - r.redex := by
      rw [linearRule_redex, sub_cons_cons, sameRedex]
    refine ⟨(linearRule b r').result (.agent b ::ₘ Z), ⟨linearRule b r', firesB,
      Rule.step_iff_enabled.mpr ⟨?_, ?_, ⟨?_, ?_⟩, by simp⟩⟩, Or.inl ?_⟩
    · simp [tsub_eq_zero_of_le subB]
    · rw [hF]; exact sameClosed.symm
    · simpa using subB
    · rw [add_zero, frameB]
      show Avoids (Z - r.redex) r'.closed
      rw [sameClosed]; exact avoids
    · rw [hP]
      simp only [linearRule, Rule.result, sub_cons_cons]
      exact sameEffect Z subZ
  · have subZ : ρ.redex ≤ Z := le_of_le_cons_not_mem sub member
    have avoidsZ : Avoids (Z - ρ.redex) ρ.closed := by
      rw [cons_sub_of_le _ subZ] at avoids
      intro x m; exact avoids x (Multiset.mem_cons_of_mem m)
    have avoidsB : Avoids (.agent b ::ₘ (Z - ρ.redex)) ρ.closed := by
      intro x m
      rcases Multiset.mem_cons.mp m with h | h
      · subst h; exact closed_agent data fires b
      · exact avoidsZ x h
    refine ⟨ρ.result (.agent b ::ₘ Z), ⟨ρ, fires, Rule.step_iff_enabled.mpr ⟨?_, hF, ⟨?_, ?_⟩,
      by simp⟩⟩, Or.inr (Or.inl ⟨Z - ρ.take + ρ.make, ?_, ?_⟩)⟩
    · simp [tsub_eq_zero_of_le (subZ.trans (Multiset.le_cons_self _ _))]
    · simpa using subZ.trans (Multiset.le_cons_self _ _)
    · simpa [cons_sub_of_le _ subZ] using avoidsB
    · rw [hP]; exact cons_result _ (ρ.take_le_redex.trans subZ) _
    · exact cons_result _ (ρ.take_le_redex.trans subZ) _

/-- **Two linear parked processes whose rows are interchangeable are bisimilar**, beside every
rest. -/
theorem linear_similar_rows (data : DataRows rows) {a b : Agent T} (la : a.Linear) (lb : b.Linear)
    (simAB : ∀ r, LinRows rows a r → ∃ r', LinRows rows b r' ∧ Interchangeable r r')
    (simBA : ∀ r, LinRows rows b r → ∃ r', LinRows rows a r' ∧ Interchangeable r r')
    (blindA : ∀ i, ¬ obs i (.agent a)) (blindB : ∀ i, ¬ obs i (.agent b)) (Z : Multiset (Lbl D T)) :
    Bisimilar (Fires rows) Adm obs (.agent a ::ₘ Z) (.agent b ::ₘ Z) := by
  have barbSwap : ∀ {c d : Lbl D T}, (∀ i, ¬ obs i c) → ∀ (W : Multiset (Lbl D T)) i,
      Barb (obs i) (c ::ₘ W) → Barb (obs i) (d ::ₘ W) := by
    intro c d obsC W i ⟨y, member, shows⟩
    rcases Multiset.mem_cons.mp member with rfl | inW
    · exact absurd shows (obsC i)
    · exact ⟨y, Multiset.mem_cons_of_mem inW, shows⟩
  refine bisimilar_of_conditional (B := SwapRel (.agent a) (.agent b))
    ⟨fun _ _ h => h.symm, ?_, ?_, fun _ _ h C _ => h.add C⟩ (Or.inr (Or.inl ⟨Z, rfl, rfl⟩))
  · rintro X Y (rfl | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩) i shows
    · exact shows
    · exact barbSwap blindA W i shows
    · exact barbSwap blindB W i shows
  · rintro X Y F X' (rfl | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩) step
    · exact ⟨F, X', Weaker.refl _ _, step, Or.inl rfl⟩
    · obtain ⟨Q', answer, rel⟩ := swap_step data la simAB step
      exact ⟨F, Q', Weaker.refl _ _, answer, rel⟩
    · obtain ⟨Q', answer, rel⟩ := swap_step data lb simBA step
      exact ⟨F, Q', Weaker.refl _ _, answer, swapRel_comm rel⟩

/-- **Two linear parked processes with the same rows are bisimilar**, beside every rest. -/
theorem linear_same_rows (data : DataRows rows) {a b : Agent T} (la : a.Linear) (lb : b.Linear)
    (same : ∀ r, LinRows rows a r ↔ LinRows rows b r) (blindA : ∀ i, ¬ obs i (.agent a))
    (blindB : ∀ i, ¬ obs i (.agent b)) (Z : Multiset (Lbl D T)) :
    Bisimilar (Fires rows) Adm obs (.agent a ::ₘ Z) (.agent b ::ₘ Z) :=
  linear_similar_rows data la lb (fun r h => ⟨r, (same r).mp h, interchangeable_refl r⟩)
    (fun r h => ⟨r, (same r).mpr h, interchangeable_refl r⟩) blindA blindB Z

/-- `choose [t] ≅ await t`. -/
theorem choose_singleton (data : DataRows rows) (t : T)
    (blind : ∀ i, ¬ obs i (.agent (.choose [t])) ∧ ¬ obs i (.agent (.await t))) (Z : Multiset (Lbl D T)) :
    Bisimilar (Fires rows) Adm obs (.agent (.choose [t]) ::ₘ Z) (.agent (.await t) ::ₘ Z) :=
  linear_same_rows (a := .choose [t]) (b := .await t) data trivial trivial
    (fun r => by simp [LinRows]) (fun i => (blind i).1) (fun i => (blind i).2) Z

/-- **`choose` depends only on which transforms it lists**: commutative, idempotent. -/
theorem choose_perm (data : DataRows rows) {ts ss : List T} (same : ∀ t, t ∈ ts ↔ t ∈ ss)
    (blind : ∀ i, ¬ obs i (.agent (.choose ts)) ∧ ¬ obs i (.agent (.choose ss)))
    (Z : Multiset (Lbl D T)) :
    Bisimilar (Fires rows) Adm obs (.agent (.choose ts) ::ₘ Z) (.agent (.choose ss) ::ₘ Z) :=
  linear_same_rows (a := .choose ts) (b := .choose ss) data trivial trivial
    (fun _ => ⟨fun ⟨t, m, row⟩ => ⟨t, (same t).mp m, row⟩, fun ⟨t, m, row⟩ => ⟨t, (same t).mpr m, row⟩⟩)
    (fun i => (blind i).1) (fun i => (blind i).2) Z

/-- A branch with no rows can be dropped from a `choose`. -/
theorem choose_dead_branch (data : DataRows rows) {ts : List T} {dead : T} (none : ∀ r, ¬ rows dead r)
    (blind : ∀ i, ¬ obs i (.agent (.choose (dead :: ts))) ∧ ¬ obs i (.agent (.choose ts)))
    (Z : Multiset (Lbl D T)) :
    Bisimilar (Fires rows) Adm obs (.agent (.choose (dead :: ts)) ::ₘ Z) (.agent (.choose ts) ::ₘ Z) :=
  linear_same_rows (a := .choose (dead :: ts)) (b := .choose ts) data trivial trivial
    (fun r => ⟨fun ⟨t, m, row⟩ => by
      rcases List.mem_cons.mp m with rfl | m'
      · exact absurd row (none r)
      · exact ⟨t, m', row⟩, fun ⟨t, m, row⟩ => ⟨t, List.mem_cons_of_mem _ m, row⟩⟩)
    (fun i => (blind i).1) (fun i => (blind i).2) Z

end Linear

/-! ## `whenever` is replication -/

section Replication

variable {rows : T → Rule (Lbl D T) → Prop} {Adm : Lbl D T → Prop} {ι : Type w}
  {obs : ι → Lbl D T → Prop}

/-- One more copy of `x` beside a bag that holds `w`. -/
def AddRel (x w : Lbl D T) (X Y : Multiset (Lbl D T)) : Prop :=
  X = Y ∨ (w ∈ X ∧ Y = x ::ₘ X) ∨ (w ∈ Y ∧ X = x ::ₘ Y)

omit [DecidableEq D] [DecidableEq T] in
theorem AddRel.symm {x w : Lbl D T} {X Y : Multiset (Lbl D T)} (h : AddRel x w X Y) :
    AddRel x w Y X := by
  rcases h with h | ⟨m, h⟩ | ⟨m, h⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨m, h⟩)
  · exact Or.inr (Or.inl ⟨m, h⟩)

omit [DecidableEq D] [DecidableEq T] in
theorem AddRel.add {x w : Lbl D T} {X Y : Multiset (Lbl D T)} (h : AddRel x w X Y)
    (C : Multiset (Lbl D T)) : AddRel x w (X + C) (Y + C) := by
  rcases h with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨Multiset.mem_add.mpr (Or.inl m), Multiset.cons_add _ _ _⟩)
  · exact Or.inr (Or.inr ⟨Multiset.mem_add.mpr (Or.inl m), Multiset.cons_add _ _ _⟩)

omit [DecidableEq D] [DecidableEq T] in
theorem singleton_add_eq_cons {α : Type w} (x : α) (Z : Multiset α) : Z + {x} = x ::ₘ Z := by
  rw [add_comm, Multiset.singleton_add]

/-- A step that borrows nothing is a step beside one more parked process. -/
theorem step_beside_agent (data : DataRows rows) (x : Agent T) {Z Z' : Multiset (Lbl D T)}
    {F : Lbl D T → Bool} (step : BStep (Fires rows) Z ⟨0, F⟩ Z') :
    BStep (Fires rows) (.agent x ::ₘ Z) ⟨0, F⟩ (.agent x ::ₘ Z') := by
  obtain ⟨ρ, fires, stepρ⟩ := step
  obtain ⟨-, hF, -, -⟩ := Rule.step_iff_enabled.mp stepρ
  have bstep : BStep (Fires rows) Z ⟨0, F⟩ Z' := ⟨ρ, fires, stepρ⟩
  have lifted := bstep.lift_zero (C := {.agent x})
    (by rw [hF]; exact agents_avoid data fires (by intro y m; simp at m; subst m; exact id))
  rw [singleton_add_eq_cons, singleton_add_eq_cons] at lifted
  exact lifted

/-- A step keeps every parked `whenever`. -/
theorem whenever_kept (data : DataRows rows) (t : T) {Z Z' : Multiset (Lbl D T)} {F : Lbl D T → Bool}
    (step : BStep (Fires rows) Z ⟨0, F⟩ Z') (hW : Lbl.agent (.whenever t) ∈ Z) :
    Lbl.agent (.whenever t) ∈ Z' := by
  obtain ⟨ρ, fires, stepρ⟩ := step
  obtain ⟨-, -, -, hZ'⟩ := Rule.step_iff_enabled.mp stepρ
  rw [hZ']
  simp only [add_zero, Rule.result]
  refine Multiset.mem_add.mpr (Or.inl ?_)
  have notTaken := whenever_not_taken data fires t
  rw [← Multiset.count_pos] at hW ⊢
  rw [Multiset.count_sub, Multiset.count_eq_zero.mpr notTaken]
  simpa using hW

/-- **`whenever` absorbs an `await` of the same transform**: beside a bag holding `whenever t`, one
more `await t` changes nothing. -/
theorem whenever_absorbs_await (data : DataRows rows) (t : T)
    (blind : ∀ i, ¬ obs i (.agent (.await t))) {Z : Multiset (Lbl D T)}
    (holds : Lbl.agent (.whenever t) ∈ Z) :
    Bisimilar (Fires rows) Adm obs Z (.agent (.await t) ::ₘ Z) := by
  let A : Lbl D T := .agent (.await t)
  let W : Lbl D T := .agent (.whenever t)
  -- Steps of the bag holding `W` alone are steps beside the extra `A`, and keep `W`.
  have plainSide : ∀ {Z Z' : Multiset (Lbl D T)} {F}, W ∈ Z → BStep (Fires rows) Z ⟨0, F⟩ Z' →
      BStep (Fires rows) (A ::ₘ Z) ⟨0, F⟩ (A ::ₘ Z') ∧ W ∈ Z' :=
    fun hW step => ⟨step_beside_agent data _ step, whenever_kept data t step hW⟩
  -- Steps of the bag with the extra `A` are matched without it.
  have extraSide : ∀ {Z X' : Multiset (Lbl D T)} {F}, W ∈ Z → BStep (Fires rows) (A ::ₘ Z) ⟨0, F⟩ X' →
      ∃ Y', BStep (Fires rows) Z ⟨0, F⟩ Y' ∧ AddRel A W Y' X' := by
    intro Z X' F hW step
    obtain ⟨ρ, fires, stepρ⟩ := step
    obtain ⟨-, hF, ⟨sub, avoids⟩, hX⟩ := Rule.step_iff_enabled.mp stepρ
    simp only [add_zero] at sub avoids hX
    by_cases member : A ∈ ρ.redex
    · -- the extra `A` fired: `W` fires the same row
      obtain ⟨r, row, rfl⟩ := linear_mem_redex data fires (a := .await t) trivial member
      rw [linearRule_redex] at sub avoids
      have subZ : r.redex ≤ Z := (Multiset.cons_le_cons_iff _).mp sub
      rw [sub_cons_cons] at avoids
      have subW : (wheneverRule t r).redex ≤ Z := by
        rw [wheneverRule_redex]
        exact cons_le_of_mem hW (agent_not_mem_row data row _) subZ
      refine ⟨(wheneverRule t r).result Z, ⟨wheneverRule t r, Fires.whenever row,
        Rule.step_iff_enabled.mpr ⟨by simp [tsub_eq_zero_of_le subW], hF, ⟨by simpa using subW, ?_⟩,
          by simp⟩⟩, Or.inl ?_⟩
      · have mono : Z - (wheneverRule t r).redex ≤ Z - r.redex := by
          rw [wheneverRule_redex]
          exact tsub_le_tsub_left (Multiset.le_cons_self _ _) _
        have := avoids.mono mono
        rw [add_zero]
        exact this
      · rw [hX]
        simp [wheneverRule, linearRule, Rule.result, A]
    · -- the extra `A` stayed parked
      have subZ : ρ.redex ≤ Z := le_of_le_cons_not_mem sub member
      have avoidsZ : Avoids (Z - ρ.redex) ρ.closed := by
        rw [cons_sub_of_le _ subZ] at avoids
        intro x m; exact avoids x (Multiset.mem_cons_of_mem m)
      have stepZ : BStep (Fires rows) Z ⟨0, F⟩ (ρ.result Z) :=
        ⟨ρ, fires, Rule.step_iff_enabled.mpr ⟨by simp [tsub_eq_zero_of_le subZ], hF,
          ⟨by simpa using subZ, by simpa using avoidsZ⟩, by simp⟩⟩
      refine ⟨ρ.result Z, stepZ, Or.inr (Or.inl ⟨(plainSide hW stepZ).2, ?_⟩)⟩
      rw [hX]
      exact cons_result _ (ρ.take_le_redex.trans subZ) _
  refine bisimilar_of_conditional (B := AddRel A W)
    ⟨fun _ _ h => h.symm, ?_, ?_, fun _ _ h C _ => h.add C⟩ (Or.inr (Or.inl ⟨holds, rfl⟩))
  · rintro X Y (rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩) i shows
    · exact shows
    · exact ⟨_, Multiset.mem_cons_of_mem shows.choose_spec.1, shows.choose_spec.2⟩
    · obtain ⟨y, member, h⟩ := shows
      rcases Multiset.mem_cons.mp member with rfl | inV
      · exact absurd h (blind i)
      · exact ⟨y, inV, h⟩
  · rintro X Y F X' (rfl | ⟨hW, rfl⟩ | ⟨hW, rfl⟩) step
    · exact ⟨F, X', Weaker.refl _ _, step, Or.inl rfl⟩
    · obtain ⟨answer, keeps⟩ := plainSide hW step
      exact ⟨F, A ::ₘ X', Weaker.refl _ _, answer, Or.inr (Or.inl ⟨keeps, rfl⟩)⟩
    · obtain ⟨Y', answer, rel⟩ := extraSide hW step
      exact ⟨F, Y', Weaker.refl _ _, answer, rel.symm⟩

/-- **`whenever t ≅ await t | whenever t`**: the law `!P ≅ P | !P`. -/
theorem whenever_replication (data : DataRows rows) (t : T) (blind : ∀ i, ¬ obs i (.agent (.await t))) :
    Bisimilar (Fires rows) Adm obs {.agent (.whenever t)} {.agent (.await t), .agent (.whenever t)} :=
  whenever_absorbs_await data t blind (Multiset.mem_singleton_self _)

/-- **`whenever t ≅ whenever t | whenever t`**: beside a bag holding `whenever t`, one more copy
changes nothing. -/
theorem whenever_idempotent (data : DataRows rows) (t : T) {Z : Multiset (Lbl D T)}
    (holds : Lbl.agent (.whenever t) ∈ Z) :
    Bisimilar (Fires rows) Adm obs Z (.agent (.whenever t) ::ₘ Z) := by
  let W : Lbl D T := .agent (.whenever t)
  have extraSide : ∀ {Z X' : Multiset (Lbl D T)} {F}, W ∈ Z → BStep (Fires rows) (W ::ₘ Z) ⟨0, F⟩ X' →
      ∃ Y', BStep (Fires rows) Z ⟨0, F⟩ Y' ∧ X' = W ::ₘ Y' := by
    intro Z X' F hW step
    obtain ⟨ρ, fires, stepρ⟩ := step
    obtain ⟨-, hF, ⟨sub, avoids⟩, hX⟩ := Rule.step_iff_enabled.mp stepρ
    simp only [add_zero] at sub avoids hX
    have subZ : ρ.redex ≤ Z := by
      by_cases member : W ∈ ρ.redex
      · obtain ⟨r, row, rfl⟩ := whenever_mem_redex data fires member
        rw [wheneverRule_redex] at sub ⊢
        exact cons_le_of_mem hW (agent_not_mem_row data row _) ((Multiset.cons_le_cons_iff _).mp sub)
      · exact le_of_le_cons_not_mem sub member
    have avoidsZ : Avoids (Z - ρ.redex) ρ.closed := by
      rw [cons_sub_of_le _ subZ] at avoids
      intro x m; exact avoids x (Multiset.mem_cons_of_mem m)
    refine ⟨ρ.result Z, ⟨ρ, fires, Rule.step_iff_enabled.mpr ⟨by simp [tsub_eq_zero_of_le subZ], hF,
      ⟨by simpa using subZ, by simpa using avoidsZ⟩, by simp⟩⟩, ?_⟩
    rw [hX]
    exact cons_result _ (ρ.take_le_redex.trans subZ) _
  refine bisimilar_of_conditional (B := AddRel W W)
    ⟨fun _ _ h => h.symm, ?_, ?_, fun _ _ h C _ => h.add C⟩ (Or.inr (Or.inl ⟨holds, rfl⟩))
  · rintro X Y (rfl | ⟨hW, rfl⟩ | ⟨hW, rfl⟩) i shows
    · exact shows
    · exact ⟨_, Multiset.mem_cons_of_mem shows.choose_spec.1, shows.choose_spec.2⟩
    · obtain ⟨y, member, h⟩ := shows
      rcases Multiset.mem_cons.mp member with rfl | inV
      · exact ⟨_, hW, h⟩
      · exact ⟨y, inV, h⟩
  · rintro X Y F X' (rfl | ⟨hW, rfl⟩ | ⟨hW, rfl⟩) step
    · exact ⟨F, X', Weaker.refl _ _, step, Or.inl rfl⟩
    · exact ⟨F, W ::ₘ X', Weaker.refl _ _, step_beside_agent data _ step,
        Or.inr (Or.inl ⟨whenever_kept data t step hW, rfl⟩)⟩
    · obtain ⟨Y', answer, rfl⟩ := extraSide hW step
      exact ⟨F, Y', Weaker.refl _ _, answer, Or.inr (Or.inr ⟨whenever_kept data t answer hW, rfl⟩)⟩

end Replication

/-! ## Controls -/

namespace Controls

/-- Data: a message, an output, and a mark. -/
inductive MData where
  | m
  | out
  | seen
  deriving DecidableEq, Repr

open MData

/-- Labels over two transforms, `true` and `false`. -/
abbrev L := Lbl MData Bool

/-- The one row: take a message, make an output. -/
def row : Rule L := ⟨{.data m}, 0, {.data out}, fun _ => false⟩

/-- Both transforms have that row. -/
def rowsC : Bool → Rule L → Prop := fun _ r => r = row

theorem rowsC_data : DataRows rowsC := by
  rintro t r rfl
  refine ⟨fun x member => ?_, fun x h => by simp [row] at h⟩
  simp [row, Rule.redex] at member
  subst member
  trivial

/-- No barbs. -/
def noBarbs : Empty → L → Prop := Empty.elim

/-- Every reduction of a bag without parked processes is impossible. -/
theorem no_reduction_without_agents {M M' : Multiset L} (noAgent : ∀ a, Lbl.agent a ∉ M)
    {Γ : Rule L → Prop} (sub : ∀ ρ, Γ ρ → ∃ a, Lbl.agent a ∈ ρ.redex) (reduces : Reduces Γ M M') : False := by
  obtain ⟨ρ, member, ⟨le, -⟩, -⟩ := reduces
  obtain ⟨a, inRedex⟩ := sub ρ member
  exact noAgent a (Multiset.mem_of_le le inRedex)

theorem fires_has_agent : ∀ ρ, Fires rowsC ρ → ∃ a, Lbl.agent a ∈ ρ.redex := by
  intro ρ fires
  cases fires with
  | @await t r _ => exact ⟨.await t, by simp [Rule.redex]⟩
  | @whenever t r _ => exact ⟨.whenever t, by simp [Rule.redex]⟩
  | @choose ts t r _ _ => exact ⟨.choose ts, by simp [Rule.redex]⟩

/-- **Once against always.** Beside two messages, `await` fires once and `whenever` twice, so they are
not contextually equivalent (and so not bisimilar). -/
theorem once_not_always :
    ¬ Contextual (Fires rowsC) (fun _ => True) noBarbs {.agent (.await true)} {.agent (.whenever true)} := by
  rintro ⟨B, ctx, related⟩
  have inContext := ctx.context related (C := {.data m, .data m}) (fun _ _ => trivial)
  obtain ⟨N', reduces, rel⟩ := ctx.reduce inContext (M' := {.data m, .data out})
    ⟨linearRule (.await true) row, Fires.await rfl, ⟨by decide, by decide⟩, by decide⟩
  -- the only reduction of the `whenever` side fires the row and keeps the process
  have hN' : N' = {.agent (.whenever true), .data m, .data out} := by
    obtain ⟨ρ, fires, ⟨le, -⟩, rfl⟩ := reduces
    cases fires with
    | @await t r hr => subst hr; cases t <;> exact absurd le (by decide)
    | @whenever t r hr => subst hr; cases t <;> first | exact absurd le (by decide) | decide
    | @choose ts t r _ hr =>
        subst hr
        have := Multiset.mem_of_le le (show Lbl.agent (.choose ts) ∈ _ by simp [Rule.redex])
        simp at this
  subst hN'
  obtain ⟨X', reducesX, -⟩ := ctx.reduce (ctx.symm rel) (M' := {.agent (.whenever true), .data out, .data out})
    ⟨wheneverRule true row, Fires.whenever rfl, ⟨by decide, by decide⟩, by decide⟩
  exact no_reduction_without_agents (by intro a h; simp at h) fires_has_agent reducesX

/-- **One choice against two waits.** Beside two messages, `choose [true, false]` fires one branch,
`await true | await false` fires both. -/
theorem choose_not_par :
    ¬ Contextual (Fires rowsC) (fun _ => True) noBarbs {.agent (.await true), .agent (.await false)}
      {.agent (.choose [true, false])} := by
  rintro ⟨B, ctx, related⟩
  have inContext := ctx.context related (C := {.data m, .data m}) (fun _ _ => trivial)
  obtain ⟨N', reduces, rel⟩ := ctx.reduce inContext (M' := {.agent (.await false), .data m, .data out})
    ⟨linearRule (.await true) row, Fires.await rfl, ⟨by decide, by decide⟩, by decide⟩
  have hN' : N' = {.data m, .data out} := by
    obtain ⟨ρ, fires, ⟨le, -⟩, rfl⟩ := reduces
    cases fires with
    | @await t r hr => subst hr; cases t <;> exact absurd le (by decide)
    | @whenever t r hr => subst hr; cases t <;> exact absurd le (by decide)
    | @choose ts t r tmem hr =>
        subst hr
        by_cases hts : ts = [true, false]
        · subst hts; decide
        · exfalso
          have := Multiset.mem_of_le le (show Lbl.agent (.choose ts) ∈ _ by simp [Rule.redex])
          simp at this
          exact hts this
  subst hN'
  obtain ⟨X', reducesX, -⟩ := ctx.reduce rel (M' := {.data out, .data out})
    ⟨linearRule (.await false) row, Fires.await rfl, ⟨by decide, by decide⟩, by decide⟩
  exact no_reduction_without_agents (by intro a h; simp at h) fires_has_agent reducesX

/-- The region of the parked processes of transform `true`. -/
def waitersOfTrue : L → Bool
  | .agent (.await true) => true
  | .agent (.whenever true) => true
  | _ => false

/-- A rule that queries the waiters of `true`: "exactly one waiter, and it is the `whenever`". -/
def counter : Rule L := ⟨0, {.agent (.whenever true)}, {.data seen}, waitersOfTrue⟩

/-- The program's rules, with the counter beside them. -/
def countedRules : Rule L → Prop := fun ρ => Fires rowsC ρ ∨ ρ = counter

/-- **Replication fails over bags when copies are counted.** With a rule that queries the parked
processes of `true`, `whenever true` and `await true | whenever true` are not contextually
equivalent, though without it they are bisimilar (`whenever_replication`). -/
theorem replication_fails_when_counted :
    Bisimilar (Fires rowsC) (fun _ => True) noBarbs {.agent (.whenever true)}
        {.agent (.await true), .agent (.whenever true)} ∧
      ¬ Contextual countedRules (fun _ => True) noBarbs {.agent (.whenever true)}
        {.agent (.await true), .agent (.whenever true)} := by
  refine ⟨whenever_replication rowsC_data true (fun i => i.elim), ?_⟩
  rintro ⟨B, ctx, related⟩
  obtain ⟨N', reduces, -⟩ := ctx.reduce related (M' := {.agent (.whenever true), .data seen})
    ⟨counter, Or.inr rfl, ⟨by decide, by decide⟩, by decide⟩
  obtain ⟨ρ, member, ⟨le, avoids⟩, -⟩ := reduces
  rcases member with fires | rfl
  · cases fires with
    | @await t r hr => subst hr; cases t <;> exact absurd le (by decide)
    | @whenever t r hr => subst hr; cases t <;> exact absurd le (by decide)
    | @choose ts t r _ hr =>
        subst hr
        have := Multiset.mem_of_le le (show Lbl.agent (.choose ts) ∈ _ by simp [Rule.redex])
        simp at this
  · exact absurd avoids (by decide)

/-- Peek: keep the message, make an output. -/
def peekRow : Rule L := ⟨0, {.data m}, {.data out}, fun _ => false⟩

/-- Take the message and make it again, with the output. -/
def remakeRow : Rule L := ⟨{.data m}, 0, {.data m, .data out}, fun _ => false⟩

/-- Transform `true` peeks, transform `false` takes and remakes. -/
def rowsPeek : Bool → Rule L → Prop := fun t r => r = if t then peekRow else remakeRow

theorem rowsPeek_data : DataRows rowsPeek := by
  rintro t r rfl
  cases t <;> refine ⟨fun x member => ?_, fun x h => by simp [peekRow, remakeRow] at h⟩ <;>
    simp [peekRow, remakeRow, Rule.redex] at member <;> subst member <;> trivial

theorem peek_remake_interchangeable :
    Interchangeable peekRow remakeRow ∧ Interchangeable remakeRow peekRow := by
  have effect : ∀ W : Multiset L, ({.data m} : Multiset L) ≤ W →
      W - 0 + {.data out} = W - {.data m} + {.data m, .data out} := by
    intro W sub
    rw [tsub_zero, show ({.data m, .data out} : Multiset L) = {.data m} + {.data out} from rfl,
      ← add_assoc, tsub_add_cancel_of_le sub]
  refine ⟨⟨by simp [peekRow, remakeRow, Rule.redex], rfl, fun W sub => ?_⟩,
    ⟨by simp [peekRow, remakeRow, Rule.redex], rfl, fun W sub => ?_⟩⟩
  · exact effect W (by simpa [peekRow, Rule.redex] using sub)
  · exact (effect W (by simpa [remakeRow, Rule.redex] using sub)).symm

/-- **Peek and take-and-remake are bisimilar.** The equivalence interleaves single commits, so it does
not see that two peeks commute while two take-and-remakes of one message clash (the independence
control of the basis module, `keep_not_take_remake`): a true-concurrency equivalence would. -/
theorem peek_vs_take_remake :
    Bisimilar (Fires rowsPeek) (fun _ => True) noBarbs {.agent (.await true)} {.agent (.await false)} :=
  linear_similar_rows (a := .await true) (b := .await false) rowsPeek_data trivial trivial
    (fun r h => ⟨remakeRow, rfl, by rw [show r = peekRow from h]; exact peek_remake_interchangeable.1⟩)
    (fun r h => ⟨peekRow, rfl, by rw [show r = remakeRow from h]; exact peek_remake_interchangeable.2⟩)
    (fun i => i.elim) (fun i => i.elim) 0

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Agents
