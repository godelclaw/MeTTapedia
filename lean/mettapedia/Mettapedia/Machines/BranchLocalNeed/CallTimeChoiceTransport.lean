import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceRenaming
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceStrict

/-!
# Transport of branch-local worlds

A runtime moves suspended computations between worlds: into the cells of
another heap, of a service world or of a worker. Such a move keeps call-time
choice if it is a *transport* (`Transport φ σ σ'`):

* **identity**: cells are mapped injectively (`φ` has no repetition), so one
  shared cell is never split into two and two cells are never merged;
* **roles**: every cell keeps its role. A ready value stays ready with the
  transported value, a pending cell stays pending, and a cell under evaluation
  stays under evaluation; the code is unchanged and the environment is
  transported;
* **freshness**: the target's own further cells lie outside the image, so
  allocation in both worlds stays in correspondence;
* **trace**: the event trace is the same.

`transport_eval` states that every judgment of the natural semantics commutes
with transport: from a transported configuration the semantics derives the
transported results, one by one, in order and with multiplicity, each in its own
branch's transported world (`ResTr`). Branch forks (`alts`), weak-head returns
committed to a cell (`commitK`) and resampling (`followK`) are all cases of
the induction. By `Derives.deterministic` these are the only results.

The target may hold further cells that no transported cell reaches; transport
therefore also states that the semantics is invariant under renaming of cells
and under unreachable cells. The controls show that dropping identity, roles or
the branch's own world changes the answers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-! ## Transports of stores -/

/-- Related caches: every cell keeps its role. -/
inductive MemoTr (φ : List Nat) : Memo → Memo → Prop where
  | pending : MemoTr φ .pending .pending
  | evaluating : MemoTr φ .evaluating .evaluating
  | done {v v' : Val Nat} : ValRel φ v v' → MemoTr φ (.done v) (.done v')

theorem MemoTr.mono {φ φ' : List Nat} (hp : φ <+: φ') {m m' : Memo} (h : MemoTr φ m m') :
    MemoTr φ' m m' := by
  cases h with
  | pending => exact .pending
  | evaluating => exact .evaluating
  | done hv => exact .done (hv.mono hp)

/-- Related cells: the same code, a transported environment and a related cache. -/
structure SuspTr (φ : List Nat) (s s' : Suspension) : Prop where
  code : s'.code = s.code
  env : EnvRel φ s.env s'.env
  memo : MemoTr φ s.memo s'.memo

theorem SuspTr.mono {φ φ' : List Nat} (hp : φ <+: φ') {s s' : Suspension} (h : SuspTr φ s s') :
    SuspTr φ' s s' :=
  ⟨h.code, h.env.mono hp, h.memo.mono hp⟩

theorem MemoTr.comp {φ ψ χ : List Nat}
    (lookup : ∀ (i j k : Nat), φ[i]? = some j → ψ[j]? = some k → χ[i]? = some k)
    {m m' m'' : Memo} (first : MemoTr φ m m') (second : MemoTr ψ m' m'') :
    MemoTr χ m m'' := by
  cases first with
  | pending => cases second; exact .pending
  | evaluating => cases second; exact .evaluating
  | done hv => cases second with | done hw => exact .done (hv.comp lookup hw)

theorem SuspTr.comp {φ ψ χ : List Nat}
    (lookup : ∀ (i j k : Nat), φ[i]? = some j → ψ[j]? = some k → χ[i]? = some k)
    {s s' s'' : Suspension} (first : SuspTr φ s s') (second : SuspTr ψ s' s'') :
    SuspTr χ s s'' :=
  ⟨second.code.trans first.code, first.env.comp lookup second.env,
    first.memo.comp lookup second.memo⟩

/-- A transport of the store `σ` into the store `σ'` along the cell map `φ`
(cell `ℓ` of `σ` is cell `φ[ℓ]` of `σ'`). -/
structure Transport (φ : List Nat) (σ σ' : Store) : Prop where
  length : φ.length = σ.cells.length
  nodup : φ.Nodup
  cells : ∀ (ℓ : Nat) (s : Suspension), σ.cells[ℓ]? = some s →
    ∃ (ℓ' : Nat) (s' : Suspension), φ[ℓ]? = some ℓ' ∧ σ'.cells[ℓ']? = some s' ∧ SuspTr φ s s'
  bound : ∀ ℓ' ∈ φ, ℓ' < σ'.cells.length
  trace : σ'.trace = σ.trace

namespace Transport

variable {φ : List Nat} {σ σ' : Store}

theorem lookup (h : Transport φ σ σ') {ℓ ℓ' : Nat} (hφ : φ[ℓ]? = some ℓ') {s : Suspension}
    (hs : σ.cells[ℓ]? = some s) : ∃ s', σ'.cells[ℓ']? = some s' ∧ SuspTr φ s s' := by
  obtain ⟨ℓ₀, s', h₀, hs', hr⟩ := h.cells ℓ s hs
  rw [hφ] at h₀
  cases h₀
  exact ⟨s', hs', hr⟩

theorem cell_of_index (h : Transport φ σ σ') {ℓ ℓ' : Nat} (hφ : φ[ℓ]? = some ℓ') :
    ∃ s, σ.cells[ℓ]? = some s := by
  have hlt : ℓ < σ.cells.length := by
    rw [← h.length]; exact (List.getElem?_eq_some_iff.mp hφ).1
  exact ⟨σ.cells[ℓ], List.getElem?_eq_getElem hlt⟩

/-- A transported value's references resolve in the target store's allocated
range. Readiness and retention use the same role-preserving cell map. -/
theorem value_referencesBounded (h : Transport φ σ σ')
    {value represented : Val Nat} (related : ValRel φ value represented) :
    represented.referencesSatisfy (fun i => i < σ'.cells.length) :=
  related.referencesSatisfy h.bound

/-- The environments captured by transferred cells keep their live target
references, even when the target has additional unrelated cells. -/
theorem captured_referencesBounded (h : Transport φ σ σ')
    {source target : Suspension} (related : SuspTr φ source target) :
    EnvReferencesSatisfy (fun i => i < σ'.cells.length) target.env :=
  related.env.referencesSatisfy h.bound

/-- An earlier carrier without a mapped field cannot represent this result.
Keeping the original field identifier alone does not repair the transport. -/
theorem missing_named {index target : Nat} (named : φ[index]? = some target)
    (missing : σ'.cells[target]? = none) : ¬ Transport φ σ σ' := by
  intro transferred
  obtain ⟨source, sourceLookup⟩ := transferred.cell_of_index named
  obtain ⟨_, targetLookup, _⟩ := transferred.lookup named sourceLookup
  rw [missing] at targetLookup
  cases targetLookup

theorem fresh_not_mem (h : Transport φ σ σ') : σ'.cells.length ∉ φ :=
  fun hm => Nat.lt_irrefl _ (h.bound _ hm)

/-- A worker may transfer its retained world again. The composite map is
computed from the two maps; the first bound and the second length ensure that
its default is never used. Unreachable cells may be present in either target. -/
theorem comp {ψ : List Nat} {σ'' : Store}
    (first : Transport φ σ σ') (second : Transport ψ σ' σ'') :
    Transport (φ.map (fun i => ψ.getD i 0)) σ σ'' := by
  have lookup : ∀ (i j k : Nat), φ[i]? = some j → ψ[j]? = some k →
      (φ.map (fun i => ψ.getD i 0))[i]? = some k := by
    intro i j k hi hj
    simp [List.getElem?_map, hi, List.getD_eq_getElem?_getD, hj]
  have inRange : ∀ i ∈ φ, ψ[i]? = some (ψ.getD i 0) := by
    intro i hi
    have bound : i < ψ.length := by rw [second.length]; exact first.bound i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  refine ⟨by simpa only [List.length_map] using first.length, ?_, ?_, ?_,
    second.trace.trans first.trace⟩
  · apply List.Nodup.map_on _ first.nodup
    intro i hi j hj equal
    exact nodup_index second.nodup (inRange i hi) (equal ▸ inRange j hj)
  · intro i s hs
    obtain ⟨j, s', hi, hj, related⟩ := first.cells i s hs
    obtain ⟨k, s'', hj', hk, related'⟩ := second.cells j s' hj
    exact ⟨k, s'', lookup i j k hi hj', hk, related.comp lookup related'⟩
  · intro k present
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp present
    exact second.bound _ (List.mem_of_getElem? (inRange i hi))

/-- Allocation of related cells extends a transport. -/
theorem alloc (h : Transport φ σ σ') {ρ : List (Val Nat)} {ρ' : List (Val Nat)}
    (hρ : EnvRel φ ρ ρ') (m : Comp) :
    Transport (φ ++ [σ'.cells.length]) (σ.alloc m ρ) (σ'.alloc m ρ') := by
  have hp : φ <+: φ ++ [σ'.cells.length] := List.prefix_append _ _
  refine ⟨by simp [Store.alloc, h.length], ?_, ?_, ?_, by simp [Store.alloc, h.trace]⟩
  · rw [List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    subst hab
    exact h.fresh_not_mem ha
  · intro ℓ s hs
    simp only [Store.alloc] at hs
    by_cases hℓ : ℓ < σ.cells.length
    · rw [List.getElem?_append_left hℓ] at hs
      obtain ⟨ℓ', s', hφ, hs', hr⟩ := h.cells ℓ s hs
      have hlt : ℓ' < σ'.cells.length := h.bound ℓ' (List.mem_of_getElem? hφ)
      refine ⟨ℓ', s', ?_, ?_, hr.mono hp⟩
      · rw [List.getElem?_append_left (h.length ▸ hℓ)]; exact hφ
      · simp only [Store.alloc]; rw [List.getElem?_append_left hlt]; exact hs'
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
      refine ⟨σ'.cells.length, ⟨m, ρ', .pending⟩, ?_, ?_, ⟨rfl, hρ.mono hp, .pending⟩⟩
      · rw [hℓeq]; simp
      · simp [Store.alloc]
  · intro ℓ' hmem
    simp only [Store.alloc, List.length_append, List.length_singleton]
    rcases List.mem_append.mp hmem with hm | hm
    · exact Nat.lt_succ_of_lt (h.bound ℓ' hm)
    · simp only [List.mem_singleton] at hm; subst hm; exact Nat.lt_succ_self _

/-- Changing the caches of related cells with related caches keeps a transport. -/
theorem setMemo (h : Transport φ σ σ') {ℓ ℓ' : Nat} (hφ : φ[ℓ]? = some ℓ') {k k' : Memo}
    (hk : MemoTr φ k k') : Transport φ (σ.setMemo ℓ k) (σ'.setMemo ℓ' k') := by
  refine ⟨by simp [Store.setMemo, h.length], h.nodup, ?_, ?_, by simp [Store.setMemo, h.trace]⟩
  · intro ℓ₀ s hs
    simp only [Store.setMemo, List.getElem?_modify] at hs
    by_cases he : ℓ = ℓ₀
    · subst he
      obtain ⟨s₀, hs₀⟩ := h.cell_of_index hφ
      rw [hs₀] at hs
      simp only [if_true, Option.map_eq_map, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨s', hs', hr⟩ := h.lookup hφ hs₀
      refine ⟨ℓ', { s' with memo := k' }, hφ, ?_, ⟨hr.code, hr.env, hk⟩⟩
      simp [Store.setMemo, hs']
    · simp only [he, if_false, Option.map_eq_map, Option.map_id'] at hs
      obtain ⟨ℓ₁, s', hφ₁, hs', hr⟩ := h.cells ℓ₀ s hs
      have hne : ℓ' ≠ ℓ₁ := by
        intro e; subst e; exact he (nodup_index h.nodup hφ hφ₁)
      refine ⟨ℓ₁, s', hφ₁, ?_, hr⟩
      simp [Store.setMemo, hne, hs']
  · intro ℓ₁ hm
    simp only [Store.setMemo, List.length_modify]
    exact h.bound ℓ₁ hm

theorem emit (h : Transport φ σ σ') (e : Nat) : Transport φ (σ.emit e) (σ'.emit e) :=
  ⟨h.length, h.nodup, h.cells, h.bound, by simp [Store.emit, h.trace]⟩

end Transport

/-! ## Results -/

/-- Related outcomes. -/
inductive OutTr (φ : List Nat) : Outcome → Outcome → Prop where
  | ok {v v' : Val Nat} : ValRel φ v v' → OutTr φ (.ok v) (.ok v')
  | fail : OutTr φ .fail .fail
  | blackhole : OutTr φ .blackhole .blackhole

theorem OutTr.isOk_eq {φ : List Nat} {o o' : Outcome} (h : OutTr φ o o') : o'.isOk = o.isOk := by
  cases h <;> rfl

/-- A result and its transport: the cell map may have grown with the branch. -/
def ResTr (φ : List Nat) (r r' : Result) : Prop :=
  ∃ φ', φ <+: φ' ∧ Transport φ' r.2 r'.2 ∧ OutTr φ' r.1 r'.1

theorem ResTr.weaken {φ φ₁ : List Nat} {r r' : Result} (h : ResTr φ₁ r r') (hp : φ <+: φ₁) :
    ResTr φ r r' := by
  obtain ⟨φ', hp', ht, ho⟩ := h
  exact ⟨φ', hp.trans hp', ht, ho⟩

theorem ResTr.base {φ : List Nat} {σ σ' : Store} {o o' : Outcome} (ht : Transport φ σ σ')
    (ho : OutTr φ o o') : ResTr φ (o, σ) (o', σ') :=
  ⟨φ, List.prefix_refl φ, ht, ho⟩

theorem resTr_weaken {φ φ₁ : List Nat} {L L' : List Result} (h : List.Forall₂ (ResTr φ₁) L L')
    (hp : φ <+: φ₁) : List.Forall₂ (ResTr φ) L L' :=
  h.imp fun _ _ hr => hr.weaken hp

/-- Related alternatives: the same computation in a transported environment. -/
def BranchTr (φ : List Nat) (b b' : Comp × List (Val Nat)) : Prop :=
  b'.1 = b.1 ∧ EnvRel φ b.2 b'.2

theorem branchTr_rules {φ : List Nat} {a a' : List (Val Nat)} (ha : EnvRel φ a a') :
    ∀ rs : List Rule, List.Forall₂ (BranchTr φ) (rs.map fun r => (r.body, a))
      (rs.map fun r => (r.body, a'))
  | [] => .nil
  | _ :: rs => .cons ⟨rfl, ha⟩ (branchTr_rules ha rs)

/-! ## The motive -/

variable (P : Program)

def TrEval (σ : Store) (ρ : List (Val Nat)) (M : Comp) (L : List Result) : Prop :=
  ∀ (φ : List Nat) (σ' : Store) (ρ' : List (Val Nat)), Transport φ σ σ' → EnvRel φ ρ ρ' →
    ∃ L', Derives P (.eval σ' ρ' M) L' ∧ List.Forall₂ (ResTr φ) L L'

def TrAlts (σ : Store) (bs : List (Comp × List (Val Nat))) (L : List Result) : Prop :=
  ∀ (φ : List Nat) (σ' : Store) (bs' : List (Comp × List (Val Nat))), Transport φ σ σ' →
    List.Forall₂ (BranchTr φ) bs bs' →
    ∃ L', Derives P (.alts σ' bs') L' ∧ List.Forall₂ (ResTr φ) L L'

def TrSeqK (n : Comp) (ρ : List (Val Nat)) (rs L : List Result) : Prop :=
  ∀ (φ : List Nat) (ρ' : List (Val Nat)) (rs' : List Result), EnvRel φ ρ ρ' →
    List.Forall₂ (ResTr φ) rs rs' →
    ∃ L', Derives P (.seqK n ρ' rs') L' ∧ List.Forall₂ (ResTr φ) L L'

def TrForce (σ : Store) (v : Val Nat) (L : List Result) : Prop :=
  ∀ (φ : List Nat) (σ' : Store) (v' : Val Nat), Transport φ σ σ' → ValRel φ v v' →
    ∃ L', Derives P (.forceVal σ' v') L' ∧ List.Forall₂ (ResTr φ) L L'

def TrCommit (ℓ : Nat) (rs L : List Result) : Prop :=
  ∀ (φ : List Nat) (ℓ' : Nat) (rs' : List Result), φ[ℓ]? = some ℓ' →
    List.Forall₂ (ResTr φ) rs rs' →
    ∃ L', Derives P (.commitK ℓ' rs') L' ∧ List.Forall₂ (ResTr φ) L L'

def TrFollow (rs L : List Result) : Prop :=
  ∀ (φ : List Nat) (rs' : List Result), List.Forall₂ (ResTr φ) rs rs' →
    ∃ L', Derives P (.followK rs') L' ∧ List.Forall₂ (ResTr φ) L L'

def Tr : Goal → List Result → Prop
  | .eval σ ρ M, L => TrEval P σ ρ M L
  | .alts σ bs, L => TrAlts P σ bs L
  | .seqK n ρ rs, L => TrSeqK P n ρ rs L
  | .forceVal σ v, L => TrForce P σ v L
  | .commitK ℓ rs, L => TrCommit P ℓ rs L
  | .followK rs, L => TrFollow P rs L

/-! ## Transport commutes with every judgment -/

/-- Binding a new cell in both worlds. -/
theorem tr_bind_cell {σ σ' : Store} {ρ ρ' : List (Val Nat)} {φ : List Nat} (m : Comp)
    (hσ : Transport φ σ σ') (hρ : EnvRel φ ρ ρ') (mk : Nat → Val Nat)
    (hmk : ∀ ψ : List Nat, ∀ ℓ ℓ', ψ[ℓ]? = some ℓ' → ValRel ψ (mk ℓ) (mk ℓ')) :
    Transport (φ ++ [σ'.cells.length]) (σ.alloc m ρ) (σ'.alloc m ρ') ∧
      EnvRel (φ ++ [σ'.cells.length]) (mk σ.cells.length :: ρ) (mk σ'.cells.length :: ρ') := by
  refine ⟨hσ.alloc hρ m, .cons (hmk _ _ _ ?_) (hρ.mono (List.prefix_append _ _))⟩
  rw [← hσ.length]
  simp

theorem transport_all : ∀ g L, Derives P g L → Tr P g L := by
  intro g L h
  induction h with
  | ret =>
      intro φ σ' ρ' hσ hρ
      exact ⟨_, .ret, .cons (ResTr.base hσ (.ok (VExp.eval_rel hρ _))) .nil⟩
  | seq _ _ ih₁ ih₂ =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ σ' ρ' hσ hρ
      obtain ⟨L', h₂, r⟩ := ih₂ φ ρ' L₁' hρ r₁
      exact ⟨L', .seq h₁ h₂, r⟩
  | @need σ ρ m n L _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨hσ₁, hρ₁⟩ := tr_bind_cell m hσ hρ Val.need (fun _ _ _ h => .need h)
      obtain ⟨L', h', r⟩ := ih _ _ _ hσ₁ hρ₁
      exact ⟨L', .need h', resTr_weaken r (List.prefix_append _ _)⟩
  | @delay σ ρ m n L _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨hσ₁, hρ₁⟩ := tr_bind_cell m hσ hρ Val.thunk (fun _ _ _ h => .thunk h)
      obtain ⟨L', h', r⟩ := ih _ _ _ hσ₁ hρ₁
      exact ⟨L', .delay h', resTr_weaken r (List.prefix_append _ _)⟩
  | @force σ ρ v L _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L', h', r⟩ := ih φ σ' (v.eval ρ') hσ (VExp.eval_rel hρ v)
      exact ⟨L', .force h', r⟩
  | @caseConHit σ ρ v c k hit miss args L hm _ ih =>
      intro φ σ' ρ' hσ hρ
      rcases (VExp.eval_rel hρ v).matchCon c k with ⟨h1, _⟩ | ⟨a, a', h1, h2, hargs⟩
      · rw [hm] at h1; cases h1
      · rw [hm] at h1; cases h1
        obtain ⟨L', h', r⟩ := ih φ σ' (a' ++ ρ') hσ (List.rel_append hargs hρ)
        exact ⟨L', .caseConHit h2 h', r⟩
  | @caseConMiss σ ρ v c k hit miss L hm _ ih =>
      intro φ σ' ρ' hσ hρ
      rcases (VExp.eval_rel hρ v).matchCon c k with ⟨_, h2⟩ | ⟨a, a', h1, _, _⟩
      · obtain ⟨L', h', r⟩ := ih φ σ' ρ' hσ hρ
        exact ⟨L', .caseConMiss h2 h', r⟩
      · rw [hm] at h1; cases h1
  | @caseAppHit σ ρ v hit miss f x L hm _ ih =>
      intro φ σ' ρ' hσ hρ
      rcases (VExp.eval_rel hρ v).matchApp with ⟨h1, _⟩ | ⟨f₀, x₀, f', x', h1, h2, hf, hx⟩
      · rw [hm] at h1; cases h1
      · rw [hm] at h1; cases h1
        obtain ⟨L', h', r⟩ := ih φ σ' (f' :: x' :: ρ') hσ (.cons hf (.cons hx hρ))
        exact ⟨L', .caseAppHit h2 h', r⟩
  | @caseAppMiss σ ρ v hit miss L hm _ ih =>
      intro φ σ' ρ' hσ hρ
      rcases (VExp.eval_rel hρ v).matchApp with ⟨_, h2⟩ | ⟨f₀, x₀, f', x', h1, _, _, _⟩
      · obtain ⟨L', h', r⟩ := ih φ σ' ρ' hσ hρ
        exact ⟨L', .caseAppMiss h2 h', r⟩
      · rw [hm] at h1; cases h1
  | @call σ ρ f args L hne _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L', h', r⟩ := ih φ σ' _ hσ
        (branchTr_rules (hρ.map_eval args) (candidates P f args.length))
      exact ⟨L', .call hne h', r⟩
  | @callNone σ ρ f args hc =>
      intro φ σ' ρ' hσ hρ
      exact ⟨_, .callNone hc, .cons (ResTr.base hσ .fail) .nil⟩
  | @callRule σ ρ i args r L hr ha _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L', h', rel⟩ := ih φ σ' _ hσ (hρ.map_eval args)
      exact ⟨L', .callRule hr ha h', rel⟩
  | @callRuleNone σ ρ i args hn =>
      intro φ σ' ρ' hσ hρ
      exact ⟨_, .callRuleNone hn, .cons (ResTr.base hσ .fail) .nil⟩
  | choose _ _ ih₁ ih₂ =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ σ' ρ' hσ hρ
      obtain ⟨L₂', h₂, r₂⟩ := ih₂ φ σ' ρ' hσ hρ
      exact ⟨_, .choose h₁ h₂, List.rel_append r₁ r₂⟩
  | fail =>
      intro φ σ' ρ' hσ hρ
      exact ⟨_, .fail, .cons (ResTr.base hσ .fail) .nil⟩
  | @emit σ ρ e m L _ ih =>
      intro φ σ' ρ' hσ hρ
      obtain ⟨L', h', r⟩ := ih φ (σ'.emit e) ρ' (hσ.emit e) hρ
      exact ⟨L', .emit h', r⟩
  | @quote σ ρ m =>
      intro φ σ' ρ' hσ hρ
      refine ⟨_, .quote, .cons ?_ .nil⟩
      refine (ResTr.base (hσ.alloc hρ m) (.ok (.code ?_))).weaken (List.prefix_append _ _)
      rw [← hσ.length]
      simp
  | @runCode σ ρ v ℓ c L₁ L hv hs _ _ ih₁ ih₂ =>
      intro φ σ' ρ' hσ hρ
      have hvr := VExp.eval_rel hρ v
      rw [hv] at hvr
      generalize hw' : v.eval ρ' = w' at hvr
      cases hvr with
      | @code _ ℓ' hφ =>
          obtain ⟨c', hc', hr⟩ := hσ.lookup hφ hs
          obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ σ' c'.env hσ hr.env
          rw [← hr.code] at h₁
          obtain ⟨L', h₂, r⟩ := ih₂ φ L₁' r₁
          exact ⟨L', .runCode hw' hc' h₁ h₂, r⟩
  | @runOther σ ρ v hn =>
      intro φ σ' ρ' hσ hρ
      have hvr := VExp.eval_rel hρ v
      have hn' : ∀ ℓ', v.eval ρ' ≠ .code ℓ' := by
        intro ℓ' e
        rw [e] at hvr
        generalize hw : v.eval ρ = w at hvr hn
        cases hvr with
        | code _ => exact hn _ rfl
      exact ⟨_, .runOther hn', .cons (ResTr.base hσ (.ok (.app (.sym _) hvr))) .nil⟩
  | @prim σ ρ op args =>
      intro φ σ' ρ' hσ hρ
      refine ⟨_, .prim, .cons (ResTr.base hσ ?_) .nil⟩
      rcases Prim.apply_rel hσ.nodup op (hρ.map_eval args) with ⟨h1, h2⟩ | ⟨w, w', h1, h2, hw⟩
      · simp only [primOutcome, h1, h2]; exact .fail
      · simp only [primOutcome, h1, h2]; exact .ok hw
  | altsNil =>
      intro φ σ' bs' hσ hbs
      cases hbs
      exact ⟨[], .altsNil, .nil⟩
  | @altsCons σ m ρ bs L₁ L₂ _ _ ih₁ ih₂ =>
      intro φ σ' bs' hσ hbs
      cases hbs with
      | @cons _ b' _ bs'' hb hrest =>
          obtain ⟨m', ρ'⟩ := b'
          obtain ⟨hm, hρ⟩ := hb
          simp only at hm hρ
          subst hm
          obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ σ' ρ' hσ hρ
          obtain ⟨L₂', h₂, r₂⟩ := ih₂ φ σ' bs'' hσ hrest
          exact ⟨_, .altsCons h₁ h₂, List.rel_append r₁ r₂⟩
  | seqKNil =>
      intro φ ρ' rs' hρ hrs
      cases hrs
      exact ⟨[], .seqKNil, .nil⟩
  | @seqKOk n ρ w σ rs L₁ L₂ _ _ ih₁ ih₂ =>
      intro φ ρ' rs' hρ hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          cases ho with
          | @ok _ w' hw =>
              obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ₁ σ' (w' :: ρ') hσ (.cons hw (hρ.mono hp))
              obtain ⟨L₂', h₂, r₂⟩ := ih₂ φ ρ' rs'' hρ hrest
              exact ⟨_, .seqKOk h₁ h₂, List.rel_append (resTr_weaken r₁ hp) r₂⟩
  | @seqKStop n ρ o σ rs L₂ hs _ ih =>
      intro φ ρ' rs' hρ hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          have hr' := hr
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          obtain ⟨L₂', h₂, r₂⟩ := ih φ ρ' rs'' hρ hrest
          exact ⟨_, .seqKStop (by rw [ho.isOk_eq]; exact hs) h₂, .cons hr' r₂⟩
  | @forceWhnf σ w hw =>
      intro φ σ' v' hσ hv
      refine ⟨_, .forceWhnf (by rw [hv.isCell_eq]; exact hw), .cons (ResTr.base hσ (.ok hv)) .nil⟩
  | @forceDone σ ℓ c w L hc hk _ ih =>
      intro φ σ' v' hσ hv
      cases hv with
      | @need _ ℓ' hφ =>
          obtain ⟨c', hc', hr⟩ := hσ.lookup hφ hc
          have hmemo := hr.memo
          rw [hk] at hmemo
          generalize hk' : c'.memo = memo' at hmemo
          cases hmemo with
          | @done _ w' hw =>
              obtain ⟨L', h', r⟩ := ih φ σ' w' hσ hw
              exact ⟨L', .forceDone hc' hk' h', r⟩
  | @forceBlackhole σ ℓ c hc hk =>
      intro φ σ' v' hσ hv
      cases hv with
      | @need _ ℓ' hφ =>
          obtain ⟨c', hc', hr⟩ := hσ.lookup hφ hc
          have hmemo := hr.memo
          rw [hk] at hmemo
          generalize hk' : c'.memo = memo' at hmemo
          cases hmemo with
          | evaluating =>
              exact ⟨_, .forceBlackhole hc' hk', .cons (ResTr.base hσ .blackhole) .nil⟩
  | @forcePending σ ℓ c L₁ L hc hk _ _ ih₁ ih₂ =>
      intro φ σ' v' hσ hv
      cases hv with
      | @need _ ℓ' hφ =>
          obtain ⟨c', hc', hr⟩ := hσ.lookup hφ hc
          have hmemo := hr.memo
          rw [hk] at hmemo
          generalize hk' : c'.memo = memo' at hmemo
          cases hmemo with
          | pending =>
              obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ (σ'.setMemo ℓ' .evaluating) c'.env
                (hσ.setMemo hφ .evaluating) hr.env
              rw [← hr.code] at h₁
              obtain ⟨L', h₂, r⟩ := ih₂ φ ℓ' L₁' hφ r₁
              exact ⟨L', .forcePending hc' hk' h₁ h₂, r⟩
  | @forceThunk σ ℓ c L₁ L hc _ _ ih₁ ih₂ =>
      intro φ σ' v' hσ hv
      cases hv with
      | @thunk _ ℓ' hφ =>
          obtain ⟨c', hc', hr⟩ := hσ.lookup hφ hc
          obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ σ' c'.env hσ hr.env
          rw [← hr.code] at h₁
          obtain ⟨L', h₂, r⟩ := ih₂ φ L₁' r₁
          exact ⟨L', .forceThunk hc' h₁ h₂, r⟩
  | commitNil =>
      intro φ ℓ' rs' hφ hrs
      cases hrs
      exact ⟨[], .commitNil, .nil⟩
  | @commitOk ℓ w σ rs L₁ L₂ _ _ ih₁ ih₂ =>
      intro φ ℓ' rs' hφ hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          cases ho with
          | @ok _ w' hw =>
              have hφ₁ : φ₁[ℓ]? = some ℓ' := prefix_getElem? hp hφ
              obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ₁ (σ'.setMemo ℓ' (.done w')) w'
                (hσ.setMemo hφ₁ (.done hw)) hw
              obtain ⟨L₂', h₂, r₂⟩ := ih₂ φ ℓ' rs'' hφ hrest
              exact ⟨_, .commitOk h₁ h₂, List.rel_append (resTr_weaken r₁ hp) r₂⟩
  | @commitStop ℓ o σ rs L₂ hs _ ih =>
      intro φ ℓ' rs' hφ hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          have hφ₁ : φ₁[ℓ]? = some ℓ' := prefix_getElem? hp hφ
          obtain ⟨L₂', h₂, r₂⟩ := ih φ ℓ' rs'' hφ hrest
          refine ⟨_, .commitStop (by rw [ho.isOk_eq]; exact hs) h₂, .cons ?_ r₂⟩
          exact ⟨φ₁, hp, hσ.setMemo hφ₁ .pending, ho⟩
  | followNil =>
      intro φ rs' hrs
      cases hrs
      exact ⟨[], .followNil, .nil⟩
  | @followOk w σ rs L₁ L₂ _ _ ih₁ ih₂ =>
      intro φ rs' hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          cases ho with
          | @ok _ w' hw =>
              obtain ⟨L₁', h₁, r₁⟩ := ih₁ φ₁ σ' w' hσ hw
              obtain ⟨L₂', h₂, r₂⟩ := ih₂ φ rs'' hrest
              exact ⟨_, .followOk h₁ h₂, List.rel_append (resTr_weaken r₁ hp) r₂⟩
  | @followStop o σ rs L₂ hs _ ih =>
      intro φ rs' hrs
      cases hrs with
      | @cons _ r' _ rs'' hr hrest =>
          obtain ⟨o', σ'⟩ := r'
          have hr' := hr
          obtain ⟨φ₁, hp, hσ, ho⟩ := hr
          simp only at hσ ho
          obtain ⟨L₂', h₂, r₂⟩ := ih φ rs'' hrest
          exact ⟨_, .followStop (by rw [ho.isOk_eq]; exact hs) h₂, .cons hr' r₂⟩

/-- **Transport invariance.** A computation run in a transported world derives
the transported results, one by one, in order and with multiplicity; by
determinism these are its only results there. -/
theorem transport_eval {σ σ' : Store} {ρ ρ' : List (Val Nat)} {M : Comp} {L : List Result}
    {φ : List Nat} (h : Derives P (.eval σ ρ M) L) (hσ : Transport φ σ σ') (hρ : EnvRel φ ρ ρ') :
    ∃ L', Derives P (.eval σ' ρ' M) L' ∧ List.Forall₂ (ResTr φ) L L' :=
  transport_all P _ _ h φ σ' ρ' hσ hρ

/-- The answers in a transported world are exactly the transported answers. -/
theorem transport_eval_unique {σ σ' : Store} {ρ ρ' : List (Val Nat)} {M : Comp}
    {L L' : List Result} {φ : List Nat} (h : Derives P (.eval σ ρ M) L)
    (h' : Derives P (.eval σ' ρ' M) L') (hσ : Transport φ σ σ') (hρ : EnvRel φ ρ ρ') :
    List.Forall₂ (ResTr φ) L L' := by
  obtain ⟨L'', h'', r⟩ := transport_eval P h hσ hρ
  rw [Derives.deterministic h' h'']
  exact r

/-- Materialization uses the transported origins, caches and branch stores.
Its complete ordered results remain related, and each successful transported
result is ready for a consumer. No source-text replay supplies the transport. -/
theorem normalized_transport (hP : candidates P normHead 1 = [normRule])
    {σ σ' : Store} {ρ ρ' : List (Val Nat)} {M : Comp} {L : List Result} {φ : List Nat}
    (source : Derives P (.eval σ ρ (normalized M)) L)
    (world : Transport φ σ σ') (environment : EnvRel φ ρ ρ') :
    ∃ L', Derives P (.eval σ' ρ' (normalized M)) L' ∧
      List.Forall₂ (ResTr φ) L L' ∧ OkAll IsNormal L' := by
  obtain ⟨results, target, related⟩ := transport_eval P source world environment
  exact ⟨results, target, related, normalized_okNormal hP target⟩

/-- A ready value's certificate survives transport with its owning world.
Both ordinary normalization calls preserve their own store, and their results
retain the same role-preserving value relation. -/
theorem norm_ready_transport (hP : candidates P normHead 1 = [normRule])
    {σ σ' : Store} {value value' : Val Nat} {φ : List Nat}
    (world : Transport φ σ σ') (valueRelated : ValRel φ value value') (ready : IsNormal value) :
    Derives P (.eval σ [value] (.call normHead [.var 0])) [(.ok value, σ)] ∧
    Derives P (.eval σ' [value'] (.call normHead [.var 0])) [(.ok value', σ')] ∧
    ResTr φ (.ok value, σ) (.ok value', σ') := by
  have targetReady : IsNormal value' := by
    change value'.noSusp = true
    rw [valueRelated.noSusp_eq]
    exact ready
  exact ⟨norm_call_ready hP σ [value] (.var 0) ready,
    norm_call_ready hP σ' [value'] (.var 0) targetReady, ResTr.base world (.ok valueRelated)⟩

/-- Evaluation after two actual transports has the original ordered results,
related by the computed composite cell map and each result's own world. -/
theorem transport_eval_composed {σ σ' σ'' : Store}
    {ρ ρ' ρ'' : List (Val Nat)} {M : Comp} {L : List Result} {φ ψ : List Nat}
    (h : Derives P (.eval σ ρ M) L)
    (first : Transport φ σ σ') (second : Transport ψ σ' σ'')
    (firstEnv : EnvRel φ ρ ρ') (secondEnv : EnvRel ψ ρ' ρ'') :
    ∃ L'', Derives P (.eval σ'' ρ'' M) L'' ∧
      List.Forall₂ (ResTr (φ.map (fun i => ψ.getD i 0))) L L'' := by
  apply transport_eval P h (first.comp second)
  apply firstEnv.comp (ψ := ψ) (second := secondEnv)
  intro i j k hi hj
  simp [List.getElem?_map, hi, List.getD_eq_getElem?_getD, hj]

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
