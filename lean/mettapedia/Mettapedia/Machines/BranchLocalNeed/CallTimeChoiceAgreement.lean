import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource
import Mettapedia.GSLT.Dynamics.DemandAgreement

/-!
# When eager, lazy and resampling evaluation agree

The three argument-passing profiles of the call-time choice core realize the
denotations of `DemandAgreement` on the family `x ← b; T x … x`: a variable bound
to a producer `b` whose alternatives return the values `vs`, then used `n` times
and collected into the constructor `T`.

* eagerly (`value`): the bag `eagerShared n vs` (`value_bag`);
* lazily with sharing (`need`): the bag `lazyShared n vs` (`need_bag`);
* resampling (`name`): the bag `resampledUses n vs` (`name_bag`).

`profiles_agree_iff` transfers `strategies_agree_iff`: the three profiles observe
equal bags of answers exactly when `(1 ≤ n ∨ |vs| = 1) ∧ (n ≤ 1 ∨ |vs| ≤ 1)`.
Discarding (`n = 0`) agrees with eager evaluation only for a producer with
exactly one answer; copying (`n ≥ 2`) agrees with resampling only for a producer
with at most one answer. A deterministic producer, with one answer, makes all
three agree for every `n`. The answer lists keep their order: lazy and eager
lists coincide whenever the bags do (`value_values`, `need_values`).

Effects are a separate line: an event emitted by the producer belongs to the
store's trace, not to the answers. The witnesses `trace_*` show that eager
evaluation emits it once even when the variable is unused, lazy evaluation once
at the first use, and resampling once per use; and that eager and lazy order it
differently against the body's own events. Agreement of answers therefore says
nothing about traces unless the producer is effect-free.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open Mettapedia.GSLT.Dynamics.DemandAgreement

/-! ## Producers with given answers -/

/-- A value expression without variables. -/
def VExp.closed : VExp → Bool
  | .var _ => false
  | .sym _ => true
  | .app f x => f.closed && x.closed

theorem VExp.eval_closed {e : VExp} (h : e.closed = true) (ρ : List (Val Nat)) :
    e.eval ρ = e.eval [] := by
  induction e with
  | var i => simp [VExp.closed] at h
  | sym c => rfl
  | app f x ihf ihx =>
      simp only [VExp.closed, Bool.and_eq_true] at h
      simp [VExp.eval, ihf h.1, ihx h.2]

theorem VExp.eval_closed_isCell {e : VExp} (h : e.closed = true) :
    (e.eval ([] : List (Val Nat))).isCell = false := by
  cases e with
  | var i => simp [VExp.closed] at h
  | sym c => rfl
  | app f x => rfl

/-- A producer whose alternatives return the given closed values, in order. -/
def coin : List VExp → Comp
  | [] => .fail
  | [e] => .ret e
  | e :: es => .choose (.ret e) (coin es)

/-- The answers of a producer, in order. -/
def coinValues (es : List VExp) : List (Val Nat) :=
  es.map fun e => e.eval []

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The results of a producer in a store: one failure if it has no alternative. -/
def coinResults (es : List VExp) (σ : Store) : List Result :=
  match es with
  | [] => [(.fail, σ)]
  | _ :: _ => es.map fun e => (.ok (e.eval []), σ)

variable (P : Program)

theorem coin_derives (σ : Store) (ρ : List (Val Nat)) :
    ∀ es : List VExp, (∀ e ∈ es, e.closed = true) →
      Derives P (.eval σ ρ (coin es)) (coinResults es σ)
  | [], _ => .fail
  | [e], h => by
      have he := VExp.eval_closed (h e (by simp)) ρ
      have hr := Derives.ret (P := P) (σ := σ) (ρ := ρ) (v := e)
      rw [he] at hr
      exact hr
  | e :: e' :: es, h => by
      have he := VExp.eval_closed (h e (by simp)) ρ
      have ih := coin_derives σ ρ (e' :: es) (fun x hx => h x (by simp [hx]))
      have hr := Derives.ret (P := P) (σ := σ) (ρ := ρ) (v := e)
      rw [he] at hr
      have hres : coinResults (e :: e' :: es) σ =
          [(.ok (e.eval []), σ)] ++ coinResults (e' :: es) σ := by
        simp [coinResults]
      rw [hres]
      exact .choose hr ih

/-! ## Uses of a bound variable -/

/-- `n` uses of the variable bound `done` binders below, collected into `T`. -/
def usesFrom (p : Profile) (T : Nat) : Nat → Nat → Comp
  | 0, done => .ret (spineOf (.sym T) (varsDesc done))
  | n + 1, done => .seq (useVar p done) (usesFrom p T n (done + 1))

/-- A variable bound to `b` under profile `p`, then used `n` times. -/
def usedTimes (p : Profile) (b : Comp) (T n : Nat) : Comp :=
  bindFor p b (usesFrom p T n 0)

theorem spineOf_eval (ρ : List (Val Nat)) :
    ∀ (fs : List VExp) (h : VExp),
      (spineOf h fs).eval ρ = (fs.map (·.eval ρ)).foldl Val.app (h.eval ρ)
  | [], _ => rfl
  | f :: fs, h => by
      have := spineOf_eval ρ fs (.app h f)
      simp only [spineOf, List.foldl_cons, List.map_cons] at this ⊢
      rw [this]
      rfl

theorem varsDesc_eval (rest : List (Val Nat)) :
    ∀ us : List (Val Nat), (varsDesc us.length).map (·.eval (us.reverse ++ rest)) = us
  | [] => rfl
  | u :: us => by
      have ih := varsDesc_eval (u :: rest) us
      have henv : (u :: us).reverse ++ rest = us.reverse ++ (u :: rest) := by simp
      have hk : (us.reverse ++ (u :: rest)).getD us.length (.sym 0) = u := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      unfold varsDesc at ih ⊢
      rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, List.map_cons, henv, ih]
      simp only [VExp.eval, hk]

theorem spine_term (T : Nat) (us : List (Val Nat)) (rest : List (Val Nat)) :
    (spineOf (.sym T) (varsDesc us.length)).eval (us.reverse ++ rest) = term T us := by
  rw [spineOf_eval, varsDesc_eval]
  rfl

theorem spine_foldl_app {Cell : Type} :
    ∀ (us : List (Val Cell)) (h : Val Cell),
      (us.foldl Val.app h).spine = h.spine.map fun p => (p.1, p.2 ++ us)
  | [], h => by simp
  | u :: us, h => by
      rw [List.foldl_cons, spine_foldl_app us (.app h u)]
      simp only [Val.spine, Option.map_map]
      congr 1
      funext p
      simp

theorem term_injective (T : Nat) : Function.Injective (term T) := by
  intro us us' h
  have hs := congrArg Val.spine h
  simp only [term, spine_foldl_app, Val.spine, Option.map_some, List.nil_append,
    Option.some.injEq, Prod.mk.injEq] at hs
  exact hs.2

/-! ## Continuations over lists of results -/

theorem seqK_flatMap (k : Comp) (ρ : List (Val Nat)) (out : Result → List Result) :
    ∀ rs : List Result,
      (∀ r ∈ rs, (∃ v σ', r = (.ok v, σ') ∧ Derives P (.eval σ' (v :: ρ) k) (out r)) ∨
        (r.1.isOk = false ∧ out r = [r])) →
      Derives P (.seqK k ρ rs) (rs.flatMap out)
  | [], _ => .seqKNil
  | r :: rs, h => by
      have ih := seqK_flatMap k ρ out rs (fun x hx => h x (by simp [hx]))
      rcases h r (by simp) with ⟨v, σ', rfl, hd⟩ | ⟨hs, ho⟩
      · exact .seqKOk hd ih
      · obtain ⟨o, σ'⟩ := r
        rw [List.flatMap_cons, ho]
        exact .seqKStop hs ih

theorem followK_flatMap (out : Result → List Result) :
    ∀ rs : List Result,
      (∀ r ∈ rs, (∃ v σ', r = (.ok v, σ') ∧ Derives P (.forceVal σ' v) (out r)) ∨
        (r.1.isOk = false ∧ out r = [r])) →
      Derives P (.followK rs) (rs.flatMap out)
  | [], _ => .followNil
  | r :: rs, h => by
      have ih := followK_flatMap out rs (fun x hx => h x (by simp [hx]))
      rcases h r (by simp) with ⟨v, σ', rfl, hd⟩ | ⟨hs, ho⟩
      · exact .followOk hd ih
      · obtain ⟨o, σ'⟩ := r
        rw [List.flatMap_cons, ho]
        exact .followStop hs ih

theorem commitK_flatMap (ℓ : Nat) (out : Result → List Result) :
    ∀ rs : List Result,
      (∀ r ∈ rs, (∃ v σ', r = (.ok v, σ') ∧
          Derives P (.forceVal (σ'.setMemo ℓ (.done v)) v) (out r)) ∨
        (r.1.isOk = false ∧ out r = [(r.1, r.2.setMemo ℓ .pending)])) →
      Derives P (.commitK ℓ rs) (rs.flatMap out)
  | [], _ => .commitNil
  | r :: rs, h => by
      have ih := commitK_flatMap ℓ out rs (fun x hx => h x (by simp [hx]))
      rcases h r (by simp) with ⟨v, σ', rfl, hd⟩ | ⟨hs, ho⟩
      · exact .commitOk hd ih
      · obtain ⟨o, σ'⟩ := r
        rw [List.flatMap_cons, ho]
        exact .commitStop hs ih

theorem values_append (L₁ L₂ : List Result) : values (L₁ ++ L₂) = values L₁ ++ values L₂ := by
  simp [values, List.filterMap_append]

theorem values_flatMap {α : Type} (xs : List α) (out : α → List Result) :
    values (xs.flatMap out) = xs.flatMap fun x => values (out x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, List.flatMap_cons, values_append, ih]

/-! ## The eager profile -/

theorem value_uses (σ : Store) (ρ : List (Val Nat)) (v : Val Nat) (T : Nat) :
    ∀ (n done : Nat), Derives P (.eval σ (List.replicate done v ++ v :: ρ) (usesFrom .value T n done))
      [(.ok (term T (List.replicate (done + n) v)), σ)]
  | 0, done => by
      have hr := Derives.ret (P := P) (σ := σ) (ρ := List.replicate done v ++ v :: ρ)
        (v := spineOf (.sym T) (varsDesc done))
      have hs := spine_term T (List.replicate done v) (v :: ρ)
      rw [List.reverse_replicate, List.length_replicate] at hs
      rw [hs] at hr
      exact hr
  | n + 1, done => by
      have hget : (VExp.var done).eval (List.replicate done v ++ v :: ρ) = v := by
        simp only [VExp.eval]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      have henv : v :: (List.replicate done v ++ v :: ρ) =
          List.replicate (done + 1) v ++ v :: ρ := by
        simp [List.replicate_succ]
      have ih := value_uses σ ρ v T n (done + 1)
      rw [← henv, show done + 1 + n = done + (n + 1) by omega] at ih
      have hk := Derives.seqKOk (P := P) (rs := []) ih .seqKNil
      rw [List.append_nil] at hk
      have hr := Derives.ret (P := P) (σ := σ) (ρ := List.replicate done v ++ v :: ρ)
        (v := .var done)
      rw [hget] at hr
      exact .seq hr hk

/-- The eager profile: the producer runs first; every answer is used `n` times. -/
theorem value_values (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) :
    ∃ L, Derives P (.eval σ ρ (usedTimes .value (coin es) T n)) L ∧
      values L = (coinValues es).map fun v => term T (List.replicate n v) := by
  have hb := coin_derives P σ ρ es hes
  cases es with
  | nil =>
      refine ⟨_, .seq hb (.seqKStop rfl .seqKNil), rfl⟩
  | cons e es' =>
      let out : Result → List Result := fun r =>
        match r.1 with
        | .ok v => [(.ok (term T (List.replicate n v)), σ)]
        | _ => [r]
      have hk : Derives P (.seqK (usesFrom .value T n 0) ρ (coinResults (e :: es') σ))
          ((coinResults (e :: es') σ).flatMap out) := by
        apply seqK_flatMap
        intro r hr
        simp only [coinResults, List.mem_map] at hr
        obtain ⟨x, _, rfl⟩ := hr
        refine Or.inl ⟨_, _, rfl, ?_⟩
        simpa [out] using value_uses P σ ρ (x.eval []) T n 0
      refine ⟨_, .seq hb hk, ?_⟩
      rw [values_flatMap]
      simp [coinResults, coinValues, out, values, List.flatMap_map, flatMap_single]

/-! ## The lazy profile -/

theorem alloc_lookup (σ : Store) (m : Comp) (ρ : List (Val Nat)) :
    (σ.alloc m ρ).cells[σ.cells.length]? = some ⟨m, ρ, .pending⟩ := by
  simp [Store.alloc]

theorem setMemo_lookup {σ : Store} {ℓ : Nat} {s : Suspension} (hs : σ.cells[ℓ]? = some s)
    (k : Memo) : (σ.setMemo ℓ k).cells[ℓ]? = some { s with memo := k } := by
  simp [Store.setMemo, hs]

theorem need_uses (ρ : List (Val Nat)) (ℓ : Nat) (v : Val Nat) (hv : v.isCell = false)
    (T : Nat) (σ : Store) (s : Suspension) (hs : σ.cells[ℓ]? = some s)
    (hmemo : s.memo = .done v) :
    ∀ (n done : Nat),
      Derives P (.eval σ (List.replicate done v ++ .need ℓ :: ρ) (usesFrom .need T n done))
        [(.ok (term T (List.replicate (done + n) v)), σ)]
  | 0, done => by
      have hr := Derives.ret (P := P) (σ := σ) (ρ := List.replicate done v ++ .need ℓ :: ρ)
        (v := spineOf (.sym T) (varsDesc done))
      have hsp := spine_term T (List.replicate done v) (.need ℓ :: ρ)
      rw [List.reverse_replicate, List.length_replicate] at hsp
      rw [hsp] at hr
      exact hr
  | n + 1, done => by
      have hget : (VExp.var done).eval (List.replicate done v ++ .need ℓ :: ρ) = .need ℓ := by
        simp only [VExp.eval]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      have henv : v :: (List.replicate done v ++ .need ℓ :: ρ) =
          List.replicate (done + 1) v ++ .need ℓ :: ρ := by
        simp [List.replicate_succ]
      have ih := need_uses ρ ℓ v hv T σ s hs hmemo n (done + 1)
      rw [← henv, show done + 1 + n = done + (n + 1) by omega] at ih
      have hk := Derives.seqKOk (P := P) (rs := []) ih .seqKNil
      rw [List.append_nil] at hk
      have hf : Derives P (.eval σ (List.replicate done v ++ .need ℓ :: ρ) (.force (.var done)))
          [(.ok v, σ)] := by
        refine .force ?_
        rw [hget]
        exact .forceDone hs hmemo (.forceWhnf hv)
      exact .seq hf hk

/-- The lazy profile: the producer runs at the first use, and its answer is
shared by the later uses; an unused variable never runs it. -/
theorem need_values (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) :
    ∃ L, Derives P (.eval σ ρ (usedTimes .need (coin es) T n)) L ∧
      values L = if n = 0 then [term T []]
        else (coinValues es).map fun v => term T (List.replicate n v) := by
  set ℓ := σ.cells.length
  set σ₁ := σ.alloc (coin es) ρ
  have hcell : σ₁.cells[ℓ]? = some ⟨coin es, ρ, .pending⟩ := alloc_lookup σ (coin es) ρ
  cases n with
  | zero =>
      refine ⟨_, .need (.ret (v := spineOf (.sym T) (varsDesc 0))), ?_⟩
      simp [values, spineOf, varsDesc, term, VExp.eval]
  | succ m =>
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
            refine Or.inl ⟨_, _, rfl, ?_⟩
            exact .forceWhnf (VExp.eval_closed_isCell (hes x hx))
      have hforce : Derives P (.eval σ₁ (.need ℓ :: ρ) (.force (.var 0)))
          ((coinResults es σe).flatMap commitOut) :=
        .force (.forcePending hcell rfl hb hcommit)
      let useOut : Result → List Result := fun r =>
        match r.1 with
        | .ok v => [(.ok (term T (List.replicate (m + 1) v)), r.2)]
        | _ => [r]
      have hk : Derives P (.seqK (usesFrom .need T m 1) (.need ℓ :: ρ)
          ((coinResults es σe).flatMap commitOut))
          (((coinResults es σe).flatMap commitOut).flatMap useOut) := by
        apply seqK_flatMap
        intro r hr
        cases es with
        | nil =>
            simp only [coinResults, List.flatMap_cons, List.flatMap_nil, List.append_nil,
              commitOut, List.mem_singleton] at hr
            subst hr
            exact Or.inr ⟨rfl, rfl⟩
        | cons e es' =>
            simp only [coinResults, List.flatMap_map, List.mem_flatMap, commitOut,
              List.mem_singleton] at hr
            obtain ⟨x, hx, rfl⟩ := hr
            refine Or.inl ⟨_, _, rfl, ?_⟩
            have hv := VExp.eval_closed_isCell (hes x hx)
            have hsx : (σe.setMemo ℓ (.done (x.eval []))).cells[ℓ]? =
                some ⟨coin (e :: es'), ρ, .done (x.eval [])⟩ := by
              rw [setMemo_lookup (setMemo_lookup hcell .evaluating)]
            have := need_uses P ρ ℓ (x.eval []) hv T _ _ hsx rfl m 1
            simpa [useOut, Nat.add_comm] using this
      refine ⟨_, .need (.seq hforce hk), ?_⟩
      rw [values_flatMap]
      cases es with
      | nil => simp [coinResults, coinValues, commitOut, useOut, values]
      | cons e es' =>
          simp [coinResults, coinValues, commitOut, useOut, values, List.flatMap_map,
            flatMap_single]

/-! ## The resampling profile -/

/-- All `n`-tuples over `vs`, the first position outermost. -/
def tuples (vs : List (Val Nat)) : Nat → List (List (Val Nat))
  | 0 => [[]]
  | n + 1 => vs.flatMap fun v => (tuples vs n).map (v :: ·)

/-- The results of the remaining `m` resampled uses after the uses `us`. -/
def nameOut (es : List VExp) (σ₁ : Store) (T : Nat) : Nat → List (Val Nat) → List Result
  | 0, us => [(.ok (term T us), σ₁)]
  | m + 1, us =>
      match es with
      | [] => [(.fail, σ₁)]
      | _ :: _ => (coinValues es).flatMap fun v => nameOut es σ₁ T m (us ++ [v])

theorem name_uses (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T : Nat)
    (ρ : List (Val Nat)) (σ₁ : Store) (ℓ : Nat) (hcell : σ₁.cells[ℓ]? = some ⟨coin es, ρ, .pending⟩) :
    ∀ (m : Nat) (us : List (Val Nat)),
      Derives P (.eval σ₁ (us.reverse ++ .thunk ℓ :: ρ) (usesFrom .name T m us.length))
        (nameOut es σ₁ T m us)
  | 0, us => by
      have hr := Derives.ret (P := P) (σ := σ₁) (ρ := us.reverse ++ .thunk ℓ :: ρ)
        (v := spineOf (.sym T) (varsDesc us.length))
      rw [spine_term T us (.thunk ℓ :: ρ)] at hr
      exact hr
  | m + 1, us => by
      have hget : (VExp.var us.length).eval (us.reverse ++ .thunk ℓ :: ρ) = .thunk ℓ := by
        simp only [VExp.eval]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      have hb := coin_derives P σ₁ ρ es hes
      have hfollow : Derives P (.followK (coinResults es σ₁)) (coinResults es σ₁) := by
        have := followK_flatMap P (fun r => [r]) (coinResults es σ₁) (by
          intro r hr
          cases es with
          | nil =>
              simp only [coinResults, List.mem_singleton] at hr
              subst hr
              exact Or.inr ⟨rfl, rfl⟩
          | cons e es' =>
              simp only [coinResults, List.mem_map] at hr
              obtain ⟨x, hx, rfl⟩ := hr
              exact Or.inl ⟨_, _, rfl, .forceWhnf (VExp.eval_closed_isCell (hes x hx))⟩)
        simpa using this
      have hforce : Derives P (.eval σ₁ (us.reverse ++ .thunk ℓ :: ρ) (.force (.var us.length)))
          (coinResults es σ₁) := by
        refine .force ?_
        rw [hget]
        exact .forceThunk hcell hb hfollow
      have hk : Derives P (.seqK (usesFrom .name T m (us.length + 1)) (us.reverse ++ .thunk ℓ :: ρ)
          (coinResults es σ₁)) (nameOut es σ₁ T (m + 1) us) := by
        cases es with
        | nil =>
            simp only [coinResults, nameOut]
            exact .seqKStop rfl .seqKNil
        | cons e es' =>
            have := seqK_flatMap P (usesFrom .name T m (us.length + 1)) (us.reverse ++ .thunk ℓ :: ρ)
              (fun r => match r.1 with
                | .ok v => nameOut (e :: es') σ₁ T m (us ++ [v])
                | _ => [r])
              (coinResults (e :: es') σ₁) (by
                intro r hr
                simp only [coinResults, List.mem_map] at hr
                obtain ⟨x, _, rfl⟩ := hr
                refine Or.inl ⟨_, _, rfl, ?_⟩
                have ih := name_uses (e :: es') hes T ρ σ₁ ℓ hcell m (us ++ [x.eval []])
                simpa using ih)
            simpa [coinResults, nameOut, coinValues, List.flatMap_map] using this
      exact .seq hforce hk

theorem values_nameOut (es : List VExp) (σ₁ : Store) (T : Nat) :
    ∀ (m : Nat) (us : List (Val Nat)),
      values (nameOut es σ₁ T m us) =
        (tuples (coinValues es) m).map fun t => term T (us ++ t)
  | 0, us => by simp [nameOut, tuples, values]
  | m + 1, us => by
      cases es with
      | nil => simp [nameOut, tuples, values, coinValues]
      | cons e es' =>
          rw [nameOut, values_flatMap]
          simp only [values_nameOut (e :: es') σ₁ T m, tuples, List.map_flatMap, List.map_map]
          apply List.flatMap_congr
          intro v _
          apply List.map_congr_left
          intro t _
          simp

/-- The resampling profile: every use runs the producer again. -/
theorem name_values (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) :
    ∃ L, Derives P (.eval σ ρ (usedTimes .name (coin es) T n)) L ∧
      values L = (tuples (coinValues es) n).map (term T) := by
  have h := name_uses P es hes T ρ (σ.alloc (coin es) ρ) σ.cells.length
    (alloc_lookup σ (coin es) ρ) n []
  refine ⟨_, .delay h, ?_⟩
  rw [values_nameOut]
  simp

/-! ## Bags of answers and the agreement theorem -/

theorem tuples_coe (vs : List (Val Nat)) :
    ∀ n, ((tuples vs n : List (List (Val Nat))) : Multiset (List (Val Nat))) =
      resampledUses n (vs : Multiset (Val Nat))
  | 0 => by simp [tuples, resampledUses]
  | n + 1 => by
      rw [tuples, resampledUses_succ, ← tuples_coe vs n]
      simp only [Multiset.map_coe]
      rw [Multiset.coe_bind]

/-- The eager bag of answers is `eagerShared`. -/
theorem value_bag (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) {L : List Result}
    (h : Derives P (.eval σ ρ (usedTimes .value (coin es) T n)) L) :
    (values L : Multiset (Val Nat)) =
      (eagerShared n ((coinValues es : List (Val Nat)) : Multiset (Val Nat))).map (term T) := by
  obtain ⟨L', h', hv⟩ := value_values P es hes T n σ ρ
  rw [Derives.deterministic h h', hv]
  simp [eagerShared, shareTuple, Multiset.bind_singleton, List.map_map, Function.comp_def]

/-- The lazy bag of answers is `lazyShared`. -/
theorem need_bag (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) {L : List Result}
    (h : Derives P (.eval σ ρ (usedTimes .need (coin es) T n)) L) :
    (values L : Multiset (Val Nat)) =
      (lazyShared n ((coinValues es : List (Val Nat)) : Multiset (Val Nat))).map (term T) := by
  obtain ⟨L', h', hv⟩ := need_values P es hes T n σ ρ
  rw [Derives.deterministic h h', hv]
  by_cases hn : n = 0
  · subst hn; simp [lazyShared]
  · simp [lazyShared, hn, shareTuple, Multiset.bind_singleton, List.map_map, Function.comp_def]

/-- The resampled bag of answers is `resampledUses`. -/
theorem name_bag (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) {L : List Result}
    (h : Derives P (.eval σ ρ (usedTimes .name (coin es) T n)) L) :
    (values L : Multiset (Val Nat)) =
      (resampledUses n ((coinValues es : List (Val Nat)) : Multiset (Val Nat))).map (term T) := by
  obtain ⟨L', h', hv⟩ := name_values P es hes T n σ ρ
  rw [Derives.deterministic h h', hv, ← tuples_coe, Multiset.map_coe]

/-- **When eager, lazy and resampling evaluation agree.** For a producer with
answers `vs` used `n` times, the three profiles observe equal bags of answers
exactly when `(1 ≤ n ∨ |vs| = 1) ∧ (n ≤ 1 ∨ |vs| ≤ 1)`. -/
theorem profiles_agree_iff (es : List VExp) (hes : ∀ e ∈ es, e.closed = true) (T n : Nat)
    (σ : Store) (ρ : List (Val Nat)) {Lv Ln Lr : List Result}
    (hv : Derives P (.eval σ ρ (usedTimes .value (coin es) T n)) Lv)
    (hn : Derives P (.eval σ ρ (usedTimes .need (coin es) T n)) Ln)
    (hr : Derives P (.eval σ ρ (usedTimes .name (coin es) T n)) Lr) :
    ((values Lv : Multiset (Val Nat)) = values Ln ∧ (values Ln : Multiset (Val Nat)) = values Lr) ↔
      (1 ≤ n ∨ es.length = 1) ∧ (n ≤ 1 ∨ es.length ≤ 1) := by
  rw [value_bag P es hes T n σ ρ hv, need_bag P es hes T n σ ρ hn,
    name_bag P es hes T n σ ρ hr]
  have hinj := Multiset.map_injective (term_injective T)
  rw [hinj.eq_iff, hinj.eq_iff]
  have := strategies_agree_iff n ((coinValues es : List (Val Nat)) : Multiset (Val Nat))
  simpa [coinValues] using this

/-- A deterministic producer: the three profiles observe the same answers, in
the same order, for every number of uses. -/
theorem deterministic_agree (e : VExp) (he : e.closed = true) (T n : Nat) (σ : Store)
    (ρ : List (Val Nat)) :
    ∃ Lv Ln Lr, Derives P (.eval σ ρ (usedTimes .value (coin [e]) T n)) Lv ∧
      Derives P (.eval σ ρ (usedTimes .need (coin [e]) T n)) Ln ∧
      Derives P (.eval σ ρ (usedTimes .name (coin [e]) T n)) Lr ∧
      values Lv = values Ln ∧ values Ln = values Lr := by
  have hes : ∀ x ∈ [e], x.closed = true := by simpa using he
  obtain ⟨Lv, hv, hvv⟩ := value_values P [e] hes T n σ ρ
  obtain ⟨Ln, hn, hnv⟩ := need_values P [e] hes T n σ ρ
  obtain ⟨Lr, hr, hrv⟩ := name_values P [e] hes T n σ ρ
  refine ⟨Lv, Ln, Lr, hv, hn, hr, ?_, ?_⟩
  · rw [hvv, hnv]
    by_cases h0 : n = 0
    · subst h0; simp [coinValues]
    · simp [h0]
  · rw [hnv, hrv]
    have htup : ∀ m, tuples [e.eval []] m = [List.replicate m (e.eval [])] := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp [tuples, ih, List.replicate_succ]
    by_cases h0 : n = 0
    · subst h0; simp [tuples]
    · simp [h0, htup, coinValues]

/-! ## Effects -/

/-- A deterministic producer with an event. -/
def emitting : Comp := .emit 7 (.ret (.sym 1))

/-- The event traces of the results of a closed computation. -/
def traces (M : Comp) : Option (List (List Nat)) :=
  (run [] 60 (.eval Store.empty [] M)).map fun L => L.map fun r => r.2.trace

/-- The answers of a closed computation. -/
def answersOf (M : Comp) : Option (List (Val Nat)) :=
  (run [] 60 (.eval Store.empty [] M)).map values

/-- Unused: the eager profile runs the event, the others do not; the answers agree. -/
theorem trace_unused :
    traces (usedTimes .value emitting 3 0) = some [[7]] ∧
    traces (usedTimes .need emitting 3 0) = some [[]] ∧
    traces (usedTimes .name emitting 3 0) = some [[]] ∧
    answersOf (usedTimes .value emitting 3 0) = answersOf (usedTimes .need emitting 3 0) := by
  decide +kernel

/-- Used twice: resampling runs the event twice; the answers agree. -/
theorem trace_twice :
    traces (usedTimes .value emitting 3 2) = some [[7]] ∧
    traces (usedTimes .need emitting 3 2) = some [[7]] ∧
    traces (usedTimes .name emitting 3 2) = some [[7, 7]] ∧
    answersOf (usedTimes .need emitting 3 2) = answersOf (usedTimes .name emitting 3 2) := by
  decide +kernel

/-- The body's own event before the first use: eager and lazy evaluation order
the two events differently. -/
def bodyFirst (p : Profile) : Comp := bindFor p emitting (.emit 9 (usesFrom p 3 1 0))

theorem trace_order :
    traces (bodyFirst .value) = some [[7, 9]] ∧ traces (bodyFirst .need) = some [[9, 7]] ∧
    answersOf (bodyFirst .value) = answersOf (bodyFirst .need) := by
  decide +kernel

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
