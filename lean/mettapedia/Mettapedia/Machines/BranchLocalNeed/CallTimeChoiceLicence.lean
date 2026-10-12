import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceAgreement

/-!
# The performance licence of call-time choice

Which memoization does call-time choice license?

* **Within a branch, along its continuations: licensed.** A cell whose cache is
  ready (or under evaluation) keeps exactly its record in every result of every
  judgment that starts from its store (`settled_stable`, `ready_stable`):
  continuations, nested forces, calls and alternatives inside the branch all see
  the same ready value, and forcing a ready cell never runs its producer
  (`force_ready_iff`). After the first successful force of a pending cell the
  cell is ready in that result's store (`force_commits`). A runtime may
  therefore cache the value once per branch and reuse it along every shared
  continuation.
* **Across branches, for a nondeterministic producer: forbidden.** A sibling
  branch starts from the store of the fork, where the cell is still pending.
  Giving it a value memoized in another branch (pre-filling) replaces all the
  producer's answers by that one value: for a producer with answers `vs`, the
  pre-filled force agrees with the specified one exactly when `vs = [v]`
  (`prefill_agrees_iff`). The producer's events are dropped as well
  (`prefill_drops_events`).
* **Deterministic, effect-free producers** are the exception: their single answer
  may be shared across branches, and eager, lazy and resampling evaluation then
  agree for every number of uses (`deterministic_agree`).
* **Run-time choice licenses the opposite**: re-running a suspension, that is,
  inlining it at every use (a resampled force is a fresh run of the code,
  `force_thunk_iff`), and forbids sharing its value between uses unless the
  producer has at most one answer (`profiles_agree_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

variable (P : Program)

/-! ## Store facts -/

theorem alloc_get_old {σ : Store} {ℓ : Nat} {s : Suspension} (hs : σ.cells[ℓ]? = some s)
    (m : Comp) (ρ : List (Val Nat)) : (σ.alloc m ρ).cells[ℓ]? = some s := by
  have hlt : ℓ < σ.cells.length := (List.getElem?_eq_some_iff.mp hs).1
  simp only [Store.alloc]
  rw [List.getElem?_append_left hlt]
  exact hs

theorem setMemo_get_other {σ : Store} {ℓ ℓ₀ : Nat} (hne : ℓ ≠ ℓ₀) (k : Memo) :
    (σ.setMemo ℓ₀ k).cells[ℓ]? = σ.cells[ℓ]? := by
  simp [Store.setMemo, Ne.symm hne]

/-! ## Settled cells are stable -/

/-- Every result store holds cell `ℓ` with record `s`. -/
def HoldsIn (ℓ : Nat) (s : Suspension) (L : List Result) : Prop :=
  ∀ r ∈ L, r.2.cells[ℓ]? = some s

theorem HoldsIn.append {ℓ : Nat} {s : Suspension} {L₁ L₂ : List Result} (h₁ : HoldsIn ℓ s L₁)
    (h₂ : HoldsIn ℓ s L₂) : HoldsIn ℓ s (L₁ ++ L₂) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ r hr
  · exact h₂ r hr

theorem HoldsIn.single {ℓ : Nat} {s : Suspension} {o : Outcome} {σ : Store}
    (h : σ.cells[ℓ]? = some s) : HoldsIn ℓ s [(o, σ)] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h

theorem HoldsIn.cons {ℓ : Nat} {s : Suspension} {r : Result} {L : List Result}
    (h : r.2.cells[ℓ]? = some s) (hL : HoldsIn ℓ s L) : HoldsIn ℓ s (r :: L) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hL x hx

theorem HoldsIn.tail {ℓ : Nat} {s : Suspension} {r : Result} {L : List Result}
    (h : HoldsIn ℓ s (r :: L)) : HoldsIn ℓ s L :=
  fun x hx => h x (List.mem_cons_of_mem r hx)

/-- The stability motive: cells that are not pending keep their records. -/
def Stable : Goal → List Result → Prop
  | .eval σ _ _, L => ∀ ℓ s, σ.cells[ℓ]? = some s → s.memo ≠ .pending → HoldsIn ℓ s L
  | .alts σ _, L => ∀ ℓ s, σ.cells[ℓ]? = some s → s.memo ≠ .pending → HoldsIn ℓ s L
  | .forceVal σ _, L => ∀ ℓ s, σ.cells[ℓ]? = some s → s.memo ≠ .pending → HoldsIn ℓ s L
  | .seqK _ _ rs, L => ∀ ℓ s, s.memo ≠ .pending → HoldsIn ℓ s rs → HoldsIn ℓ s L
  | .followK rs, L => ∀ ℓ s, s.memo ≠ .pending → HoldsIn ℓ s rs → HoldsIn ℓ s L
  | .commitK ℓ₀ rs, L =>
      ∀ ℓ s, ℓ ≠ ℓ₀ → s.memo ≠ .pending → HoldsIn ℓ s rs → HoldsIn ℓ s L

theorem stable_all : ∀ g L, Derives P g L → Stable g L := by
  intro g L h
  induction h with
  | ret => intro ℓ s hs _; exact HoldsIn.single hs
  | seq _ _ ih₁ ih₂ => intro ℓ s hs hp; exact ih₂ ℓ s hp (ih₁ ℓ s hs hp)
  | need _ ih => intro ℓ s hs hp; exact ih ℓ s (alloc_get_old hs _ _) hp
  | delay _ ih => intro ℓ s hs hp; exact ih ℓ s (alloc_get_old hs _ _) hp
  | force _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | caseConHit _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | caseConMiss _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | caseAppHit _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | caseAppMiss _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | call _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | callNone _ => intro ℓ s hs _; exact HoldsIn.single hs
  | callRule _ _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | callRuleNone _ => intro ℓ s hs _; exact HoldsIn.single hs
  | choose _ _ ih₁ ih₂ => intro ℓ s hs hp; exact (ih₁ ℓ s hs hp).append (ih₂ ℓ s hs hp)
  | fail => intro ℓ s hs _; exact HoldsIn.single hs
  | emit _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | quote => intro ℓ s hs _; exact HoldsIn.single (alloc_get_old hs _ _)
  | runCode _ _ _ _ ih₁ ih₂ => intro ℓ s hs hp; exact ih₂ ℓ s hp (ih₁ ℓ s hs hp)
  | runOther _ => intro ℓ s hs _; exact HoldsIn.single hs
  | prim => intro ℓ s hs _; exact HoldsIn.single hs
  | altsNil => intro ℓ s _ _ r hr; simp at hr
  | altsCons _ _ ih₁ ih₂ => intro ℓ s hs hp; exact (ih₁ ℓ s hs hp).append (ih₂ ℓ s hs hp)
  | seqKNil => intro ℓ s _ _ r hr; simp at hr
  | seqKOk _ _ ih₁ ih₂ =>
      intro ℓ s hp hrs
      exact (ih₁ ℓ s (hrs _ List.mem_cons_self) hp).append (ih₂ ℓ s hp hrs.tail)
  | seqKStop _ _ ih =>
      intro ℓ s hp hrs
      exact HoldsIn.cons (hrs _ List.mem_cons_self) (ih ℓ s hp hrs.tail)
  | forceWhnf _ => intro ℓ s hs _; exact HoldsIn.single hs
  | forceDone _ _ _ ih => intro ℓ s hs hp; exact ih ℓ s hs hp
  | forceBlackhole _ _ => intro ℓ s hs _; exact HoldsIn.single hs
  | @forcePending σ ℓ₀ c L₁ L hc hk _ _ ih₁ ih₂ =>
      intro ℓ s hs hp
      have hne : ℓ ≠ ℓ₀ := by
        intro e; subst e; rw [hs] at hc; cases hc; exact hp hk
      have hs' : (σ.setMemo ℓ₀ .evaluating).cells[ℓ]? = some s := by
        rw [setMemo_get_other hne]; exact hs
      exact ih₂ ℓ s hne hp (ih₁ ℓ s hs' hp)
  | forceThunk _ _ _ ih₁ ih₂ => intro ℓ s hs hp; exact ih₂ ℓ s hp (ih₁ ℓ s hs hp)
  | commitNil => intro ℓ s _ _ _ r hr; simp at hr
  | @commitOk ℓ₀ w σ rs L₁ L₂ _ _ ih₁ ih₂ =>
      intro ℓ s hne hp hrs
      have hs : (σ.setMemo ℓ₀ (.done w)).cells[ℓ]? = some s := by
        rw [setMemo_get_other hne]; exact hrs _ List.mem_cons_self
      exact (ih₁ ℓ s hs hp).append (ih₂ ℓ s hne hp hrs.tail)
  | @commitStop ℓ₀ o σ rs L₂ _ _ ih =>
      intro ℓ s hne hp hrs
      have hs : (σ.setMemo ℓ₀ .pending).cells[ℓ]? = some s := by
        rw [setMemo_get_other hne]; exact hrs _ List.mem_cons_self
      exact HoldsIn.cons hs (ih ℓ s hne hp hrs.tail)
  | followNil => intro ℓ s _ _ r hr; simp at hr
  | followOk _ _ ih₁ ih₂ =>
      intro ℓ s hp hrs
      exact (ih₁ ℓ s (hrs _ List.mem_cons_self) hp).append (ih₂ ℓ s hp hrs.tail)
  | followStop _ _ ih =>
      intro ℓ s hp hrs
      exact HoldsIn.cons (hrs _ List.mem_cons_self) (ih ℓ s hp hrs.tail)

/-- **Settled cells are stable.** A cell that is ready or under evaluation keeps
its record in every result of a computation run from its store. -/
theorem settled_stable {σ : Store} {ρ : List (Val Nat)} {M : Comp} {L : List Result}
    (h : Derives P (.eval σ ρ M) L) {ℓ : Nat} {s : Suspension} (hs : σ.cells[ℓ]? = some s)
    (hp : s.memo ≠ .pending) : ∀ r ∈ L, r.2.cells[ℓ]? = some s :=
  stable_all P _ _ h ℓ s hs hp

/-- **Ready values are never recomputed within a branch.** -/
theorem ready_stable {σ : Store} {ρ : List (Val Nat)} {M : Comp} {L : List Result}
    (h : Derives P (.eval σ ρ M) L) {ℓ : Nat} {s : Suspension} {w : Val Nat}
    (hs : σ.cells[ℓ]? = some s) (hw : s.memo = .done w) :
    ∀ r ∈ L, r.2.cells[ℓ]? = some s :=
  settled_stable P h hs (by rw [hw]; intro h; cases h)

/-- Forcing a ready cell reads its cache: the producer is not run. -/
theorem force_ready_iff {σ : Store} {ℓ : Nat} {s : Suspension} {w : Val Nat}
    (hs : σ.cells[ℓ]? = some s) (hw : s.memo = .done w) (L : List Result) :
    Derives P (.forceVal σ (.need ℓ)) L ↔ Derives P (.forceVal σ w) L := by
  constructor
  · intro h
    cases h with
    | forceWhnf hc => simp [Val.isCell] at hc
    | forceDone hs' hw' h => rw [hs] at hs'; cases hs'; rw [hw] at hw'; cases hw'; exact h
    | forceBlackhole hs' hk => rw [hs] at hs'; cases hs'; rw [hw] at hk; cases hk
    | forcePending hs' hk _ _ => rw [hs] at hs'; cases hs'; rw [hw] at hk; cases hk
  · exact .forceDone hs hw

/-- A resampled force is a fresh run of the cell's code. -/
theorem force_thunk_iff {σ : Store} {ℓ : Nat} {s : Suspension} (hs : σ.cells[ℓ]? = some s)
    (L : List Result) :
    Derives P (.forceVal σ (.thunk ℓ)) L ↔
      ∃ L₁, Derives P (.eval σ s.env s.code) L₁ ∧ Derives P (.followK L₁) L := by
  constructor
  · intro h
    cases h with
    | forceWhnf hc => simp [Val.isCell] at hc
    | forceThunk hs' h₁ h₂ => rw [hs] at hs'; cases hs'; exact ⟨_, h₁, h₂⟩
  · rintro ⟨L₁, h₁, h₂⟩
    exact .forceThunk hs h₁ h₂

theorem commit_ready :
    ∀ {ℓ : Nat} {rs L : List Result}, Derives P (.commitK ℓ rs) L →
      (∀ r ∈ rs, ∃ s, r.2.cells[ℓ]? = some s) →
      ∀ r ∈ L, ∀ v, r.1 = .ok v → ∃ s w, r.2.cells[ℓ]? = some s ∧ s.memo = .done w := by
  intro ℓ rs L h
  induction rs generalizing L with
  | nil => intro _ r hr; cases h; simp at hr
  | cons r₀ rs ih =>
      intro hrs r hr v hv
      cases h with
      | @commitOk _ w σ _ L₁ L₂ h₁ h₂ =>
          rcases List.mem_append.mp hr with hr | hr
          · obtain ⟨s₀, hs₀⟩ := hrs _ List.mem_cons_self
            have hset : (σ.setMemo ℓ (.done w)).cells[ℓ]? = some { s₀ with memo := .done w } :=
              setMemo_lookup hs₀ _
            have := stable_all P _ _ h₁ ℓ _ hset (by intro e; cases e)
            exact ⟨_, w, this r hr, rfl⟩
          · exact ih h₂ (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) r hr v hv
      | @commitStop _ o σ _ L₂ hs h₂ =>
          rcases List.mem_cons.mp hr with rfl | hr
          · simp only at hv; subst hv; simp [Outcome.isOk] at hs
          · exact ih h₂ (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) r hr v hv

/-- **The first successful force commits.** Every value result of forcing a
pending cell holds the cell ready. -/
theorem force_commits {σ : Store} {ℓ : Nat} {s : Suspension} {L : List Result}
    (h : Derives P (.forceVal σ (.need ℓ)) L) (hs : σ.cells[ℓ]? = some s)
    (hp : s.memo = .pending) :
    ∀ r ∈ L, ∀ v, r.1 = .ok v → ∃ s' w, r.2.cells[ℓ]? = some s' ∧ s'.memo = .done w := by
  cases h with
  | forceWhnf hc => simp [Val.isCell] at hc
  | forceDone hs' hw _ => rw [hs] at hs'; cases hs'; rw [hp] at hw; cases hw
  | forceBlackhole hs' hk => rw [hs] at hs'; cases hs'; rw [hp] at hk; cases hk
  | @forcePending _ _ c L₁ _ hs' _ h₁ h₂ =>
      rw [hs] at hs'
      cases hs'
      have hset : (σ.setMemo ℓ .evaluating).cells[ℓ]? = some { s with memo := .evaluating } :=
        setMemo_lookup hs _
      have hheld := stable_all P _ _ h₁ ℓ _ hset (by intro e; cases e)
      exact commit_ready P h₂ (fun r hr => ⟨_, hheld r hr⟩)

/-! ## Sharing across branches -/

/-- The first force of a cell of a producer runs the producer: every answer. -/
theorem first_force_values (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (σ : Store)
    (ρ : List (Val Nat)) :
    ∃ L, Derives P (.eval (σ.alloc (coin es) ρ) (.need σ.cells.length :: ρ) (.force (.var 0))) L ∧
      values L = coinValues es := by
  set ℓ := σ.cells.length
  set σ₁ := σ.alloc (coin es) ρ
  have hcell : σ₁.cells[ℓ]? = some ⟨coin es, ρ, .pending⟩ := alloc_lookup σ (coin es) ρ
  set σe := σ₁.setMemo ℓ .evaluating
  have hb := coin_derives P σe ρ es hes
  let commitOut : Result → List Result := fun r =>
    match r.1 with
    | .ok v => [(.ok v, r.2.setMemo ℓ (.done v))]
    | _ => [(r.1, r.2.setMemo ℓ .pending)]
  have hcommit : Derives P (.commitK ℓ (coinResults es σe))
      ((coinResults es σe).flatMap commitOut) := by
    apply commitK_flatMap
    intro r hr
    cases es with
    | nil =>
        simp only [coinResults, List.mem_singleton] at hr
        subst hr
        exact Or.inr ⟨rfl, rfl⟩
    | cons e es' =>
        simp only [coinResults, List.mem_map] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        exact Or.inl ⟨_, _, rfl, .forceWhnf (VExp.eval_closed_isCell (hes x hx))⟩
  refine ⟨_, .force (.forcePending hcell rfl hb hcommit), ?_⟩
  rw [values_flatMap]
  cases es with
  | nil => simp [coinResults, coinValues, commitOut, values]
  | cons e es' =>
      simp [coinResults, coinValues, commitOut, values, List.flatMap_map, flatMap_single]

/-- A cell pre-filled with a value memoized elsewhere answers only that value. -/
theorem prefilled_force_values (es : List VExp) (v : Val Nat) (hv : v.isCell = false)
    (σ : Store) (ρ : List (Val Nat)) :
    Derives P (.eval ((σ.alloc (coin es) ρ).setMemo σ.cells.length (.done v))
      (.need σ.cells.length :: ρ) (.force (.var 0)))
      [(.ok v, (σ.alloc (coin es) ρ).setMemo σ.cells.length (.done v))] := by
  have hs := setMemo_lookup (alloc_lookup σ (coin es) ρ) (.done v)
  exact .force (.forceDone hs rfl (.forceWhnf hv))

/-- **Memoization across branches.** Giving a sibling branch the value `v`
memoized elsewhere agrees with the specified force exactly when the producer's
only answer is `v`. -/
theorem prefill_agrees_iff (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (v : Val Nat)
    (hv : v.isCell = false) (σ : Store) (ρ : List (Val Nat)) {L L' : List Result}
    (h : Derives P (.eval (σ.alloc (coin es) ρ) (.need σ.cells.length :: ρ) (.force (.var 0))) L)
    (h' : Derives P (.eval ((σ.alloc (coin es) ρ).setMemo σ.cells.length (.done v))
      (.need σ.cells.length :: ρ) (.force (.var 0))) L') :
    values L = values L' ↔ coinValues es = [v] := by
  obtain ⟨L₀, h₀, hv₀⟩ := first_force_values P es hes σ ρ
  rw [Derives.deterministic h h₀, hv₀,
    Derives.deterministic h' (prefilled_force_values P es v hv σ ρ)]
  simp [values]

/-- Pre-filling also drops the producer's events. -/
theorem prefill_drops_events :
    let σ₀ := Store.empty.alloc emitting []
    (run [] 20 (.eval σ₀ [.need 0] (.force (.var 0)))).map (fun L => L.map (·.2.trace)) =
        some [[7]] ∧
      (run [] 20 (.eval (σ₀.setMemo 0 (.done (.sym 1))) [.need 0] (.force (.var 0)))).map
        (fun L => L.map (·.2.trace)) = some [[]] := by
  decide +kernel

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
