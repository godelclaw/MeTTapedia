import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceAdequacyLemmas
import Mettapedia.Machines.BranchLocalNeed.CacheLaws

/-!
# Forward adequacy: every specified answer list is realized by the machine

For every derivation of the natural semantics, the unchanged reference machine
`NeedReference.step (machineSpec P)`, started in any related configuration,
returns with leaves related to the derived results one by one, in order and with
multiplicity (`List.Forall₂`).

The motive `Fwd` states this for each judgment form:

* `EvalA`: running `enter M ρ'` with an empty stack;
* `EvalB`: forcing a suspended cell whose origin is `(M, ρ')`, carrier or named,
  through its update frame;
* `AltsF`, `SeqKF`, `FollowF`, `ForceF`: the alternatives of a forced cell, the
  continuation of a sequence, following an indirection after a force, and
  forcing a value.

`forward` proves `Fwd` for every derivation by induction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference NeedReturningRuns

variable (P : Program)

/-! ## The motive -/

def EvalA (σ : Store) (ρ : List (Val Nat)) (M : Comp) (L : List Result) : Prop :=
  ∀ (φ : List CellId) (ρ' : MEnv) (m : MMachine), Corr φ σ m.world → EnvRel φ ρ ρ' →
    m.control = .run (enter M ρ') [] →
    ∃ n leaves, Returns (machineSpec P) [] n [m] leaves ∧
      List.Forall₂ (ResRel φ m.world []) L leaves

def EvalB (σ : Store) (ρ : List (Val Nat)) (M : Comp) (L : List Result) : Prop :=
  ∀ (φ : List CellId) (ρ' : MEnv) (m : MMachine) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (mode : Mode),
    m.control = .force c [] → m.world.heap.lookup c = some rec → rec.cache = .suspended →
    rec.origin = (M, ρ') → EnvRel φ ρ ρ' → Corr φ σ (markWorld m.world c rec) →
    mode.OK φ σ c →
    ∃ n leaves, Returns (machineSpec P) [] n [m] leaves ∧
      List.Forall₂ (ResRel φ m.world []) (L.map mode.apply) leaves

/-- A branch of a forced cell: same heap and counter as the marked world. -/
def BranchRel (φ : List CellId) (w : MWorld) (b : Comp × List (Val Nat)) (m : MMachine) : Prop :=
  m.world.heap = w.heap ∧ m.world.nextCell = w.nextCell ∧
    m.world.receipts.effects = w.receipts.effects ∧
    ∃ ρ', EnvRel φ b.2 ρ' ∧ m.control = .run (enter b.1 ρ') []

def AltsF (σ : Store) (bs : List (Comp × List (Val Nat))) (L : List Result) : Prop :=
  ∀ (φ : List CellId) (w : MWorld) (ms : List MMachine), Corr φ σ w →
    List.Forall₂ (BranchRel φ w) bs ms →
    ∃ n leaves, Returns (machineSpec P) [] n ms leaves ∧
      List.Forall₂ (ResRel φ w []) L leaves

def SeqKF (n : Comp) (ρ : List (Val Nat)) (rs L : List Result) : Prop :=
  ∀ (φ : List CellId) (w : MWorld) (ρ' : MEnv) (ms : List MMachine), EnvRel φ ρ ρ' →
    List.Forall₂ (ResRel φ w [.resume (.seqRet n ρ')]) rs ms →
    ∃ k leaves, Returns (machineSpec P) [] k ms leaves ∧
      List.Forall₂ (ResRel φ w []) L leaves

def FollowF (rs L : List Result) : Prop :=
  ∀ (φ : List CellId) (w : MWorld) (ms : List MMachine),
    List.Forall₂ (ResRel φ w [.resume .forceRet]) rs ms →
    ∃ k leaves, Returns (machineSpec P) [] k ms leaves ∧
      List.Forall₂ (ResRel φ w []) L leaves

def ForceF (σ : Store) (v : Val Nat) (L : List Result) : Prop :=
  ∀ (φ : List CellId) (v' : MVal) (m : MMachine), Corr φ σ m.world → ValRel φ v v' →
    m.control = .run (forceLocal v') [] →
    ∃ n leaves, Returns (machineSpec P) [] n [m] leaves ∧
      List.Forall₂ (ResRel φ m.world []) L leaves

def Fwd : Goal → List Result → Prop
  | .eval σ ρ M, L => EvalA P σ ρ M L ∧ EvalB P σ ρ M L
  | .alts σ bs, L => AltsF P σ bs L
  | .seqK n ρ rs, L => SeqKF P n ρ rs L
  | .forceVal σ v, L => ForceF P σ v L
  | .commitK ℓ rs, L => FollowF P (rs.map (commitResult ℓ)) L
  | .followK rs, L => FollowF P rs L

/-! ## Shared steps -/

theorem Grows.of_allocate {w w₁ : MWorld} {o : Comp × MEnv} {g : Nat} {c : CellId}
    (ha : w.allocate? o g = some (w₁, c)) : Grows w w₁ := by
  obtain ⟨hnew, hother, hnext, -⟩ := allocate_heap ha
  refine ⟨?_, by omega⟩
  intro c₀ rec₀ hl₀ _
  have hne : c₀ ≠ c := by
    intro h; subst h
    rw [NeedCacheLaws.allocate_fresh_absent ha] at hl₀; cases hl₀
  rw [hother c₀ hne]; exact hl₀

theorem Fresh.alloc {φ : List CellId} {w : MWorld} {c : CellId} (hc : w.nextCell ≤ c.slot) :
    Fresh φ (φ ++ [c]) w := by
  intro c' hc' hn
  rcases List.mem_append.mp hc' with h | h
  · exact absurd h hn
  · simp only [List.mem_singleton] at h; subst h; exact hc

theorem Fresh.of_next {φ φ' : List CellId} {w w' : MWorld} (h : Fresh φ φ' w')
    (hn : w.nextCell ≤ w'.nextCell) : Fresh φ φ' w :=
  fun c hc hm => le_trans hn (h c hc hm)

/-- Allocating a carrier for `(M, ρ')` and demanding it under the frame `k`. -/
theorem carrier_prefix {φ : List CellId} {σ : Store} {m₀ : MMachine} {M : Comp} {ρ' : MEnv}
    {k₀ k : MResume} (hc : m₀.control = .run (.alloc (M, ρ') k₀) [])
    (hk : ∀ c, afterAllocation k₀ c = .demand c k) (hcorr : Corr φ σ m₀.world) :
    ∃ (w₁ : MWorld) (c : CellId) (work : Work),
      c ∉ φ ∧ w₁.heap.lookup c = some ⟨(M, ρ'), .suspended⟩ ∧
      Corr φ σ w₁ ∧ Grows m₀.world w₁ ∧
      (∀ n leaves, Returns (machineSpec P) [] n
          [below [.resume k] ({ world := w₁, control := .force c [], work := work } : MMachine)]
          leaves →
        Returns (machineSpec P) [] (n + 2) [m₀] leaves) := by
  obtain ⟨w₁, ha⟩ := hcorr.allocate (M, ρ') 0
  obtain ⟨hnew, -, -, -⟩ := allocate_heap ha
  have hs₁ := step_alloc P m₀ (M, ρ') k₀ [] hc w₁ _ ha
  set c := m₀.world.freshCell 0
  set m₁ := finished m₀ w₁ (.run (afterAllocation k₀ c) []) 1 1 1 1
  have hc₁ : m₁.control = .run (.demand c k) [] := by simp [m₁, hk]
  have hs₂ := step_demand P m₁ c k [] hc₁
  refine ⟨w₁, c, (finished m₁ m₁.world (.force c (.resume k :: [])) 0 0 0 0).work,
    hcorr.fresh_not_mem 0, hnew, hcorr.after_allocate ha, Grows.of_allocate ha, ?_⟩
  intro n leaves h
  set wk := (finished m₁ m₁.world (.force c (.resume k :: [])) 0 0 0 0).work
  have heq : finished m₁ m₁.world (.force c (.resume k :: [])) 0 0 0 0 =
      below [.resume k] (⟨w₁, .force c [], wk⟩ : MMachine) := rfl
  have h₂ : Returns (machineSpec P) [] (n + 1) [m₁] leaves :=
    returns_step P hs₂ (run_not_returned hc₁) (by rw [heq]; exact h)
  simpa using returns_step P hs₁ (run_not_returned hc) h₂

/-- The alternatives of a forced cell, run, then committed. -/
theorem evalB_core {φ : List CellId} {m : MMachine} {c : CellId}
    {rec : CellRecord (Comp × MEnv) MVal Empty} {mode : Mode} {σM : Store}
    {L : List Result} {inner : List MMachine} {n₁ : Nat} {leaves₁ : List MMachine}
    (hc : m.control = .force c []) (hl : m.world.heap.lookup c = some rec)
    (hs : rec.cache = .suspended)
    (hstep : step (machineSpec P) m = inner.map (below [.commit c m.world.nextEvaluator]))
    (hne : inner ≠ [])
    (hcorr : Corr φ σM (markWorld m.world c rec)) (hmode : mode.OK φ σM c)
    (hrun : Returns (machineSpec P) [] n₁ inner leaves₁)
    (hrel : List.Forall₂ (ResRel φ (markWorld m.world c rec) []) L leaves₁) :
    ∃ n leaves, Returns (machineSpec P) [] n [m] leaves ∧
      List.Forall₂ (ResRel φ m.world []) (L.map mode.apply) leaves := by
  obtain ⟨leaves', hrun', hrel'⟩ := commit_pops P hl hs hcorr hmode hrel
  have hjoin := seq_join (rest := []) (f := .commit c m.world.nextEvaluator) hrun hrun'
  refine ⟨n₁ + leaves₁.length + 1, leaves', ?_, hrel'⟩
  refine .move (force_not_returned hc) ?_ ?_
  · rw [hstep]; simpa using hne
  · rw [hstep, List.append_nil]; exact hjoin

theorem markWorld_heap_eq (m : MMachine) (c : CellId) (rec : CellRecord (Comp × MEnv) MVal Empty) :
    ({ m.world with nextEvaluator := m.world.nextEvaluator + 1 } : MWorld).heap.setKnownCache c rec
        (.evaluating m.world.nextEvaluator) = (markWorld m.world c rec).heap := rfl

/-- Branches of a forced cell that share one environment. -/
theorem branchInner_rules {φ : List CellId} (m : MMachine) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (ρs : List (Val Nat)) (ρs' : MEnv)
    (hρ : EnvRel φ ρs ρs') (lbl : MRule) :
    ∀ (bodies : List Comp) (i : Nat),
      List.Forall₂ (BranchRel φ (markWorld m.world c rec)) (bodies.map fun b => (b, ρs))
        (branchInner m { m.world with nextEvaluator := m.world.nextEvaluator + 1 } c rec
          m.world.nextEvaluator i (bodies.map fun b => (lbl, enter b ρs'))) := by
  intro bodies
  induction bodies with
  | nil => intro i; exact .nil
  | cons b bs ih =>
      intro i
      exact .cons ⟨rfl, rfl, by simp [markWorld, recorded, World.record, World.fork, World.setKnownCache], ρs', hρ, rfl⟩ (ih (i + 1))

/-- A cell whose origin has a single alternative. -/
theorem evalB_of_evalA {σ : Store} {ρ : List (Val Nat)} {M : Comp} {L : List Result}
    (hA : EvalA P σ ρ M L) (halt : ∀ ρ', alternatives P (M, ρ') = [(.builtin, enter M ρ')]) :
    EvalB P σ ρ M L := by
  intro φ ρ' m c rec mode hc hl hs horig hρ hcorr hmode
  have halts : alternatives P rec.origin = [(.builtin, enter M ρ')] := by rw [horig]; exact halt ρ'
  have hstep := step_force_suspended P m c [] hc rec hl hs _ _ halts
  rw [branchAlternatives_eq] at hstep
  set base : MWorld := { m.world with nextEvaluator := m.world.nextEvaluator + 1 }
  set x := finished m (recorded (recorded ((base.fork 0).setKnownCache c rec
    (.evaluating m.world.nextEvaluator)) (.evaluate c m.world.nextEvaluator))
    (.chooseRule c .builtin)) (.run (enter M ρ') []) 1 1 2 0
  have hinner : branchInner m base c rec m.world.nextEvaluator 0 [(.builtin, enter M ρ')] = [x] := rfl
  rw [hinner] at hstep
  have hcx : Corr φ σ x.world := hcorr.of_heap_eq rfl rfl (by
    simp [x, base, markWorld, recorded, World.record, World.fork, World.setKnownCache])
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ := hA φ ρ' x hcx hρ rfl
  exact evalB_core P hc hl hs hstep (by simp) hcorr hmode hrun (forall₂_base hrel rfl rfl)

/-- A computation entered through a carrier cell demanded by `callRet`. -/
theorem evalA_of_evalB {σ : Store} {ρ : List (Val Nat)} {M : Comp} {L : List Result}
    (hB : EvalB P σ ρ M L) (henter : ∀ ρ', enter M ρ' = .alloc (M, ρ') .callAlloc) :
    EvalA P σ ρ M L := by
  intro φ ρ' m₀ hcorr hρ hc
  rw [henter] at hc
  obtain ⟨w₁, c, work, hcnot, hnew, hcorr₁, hgrow, hprefix⟩ :=
    carrier_prefix P (k := .callRet) hc (fun _ => rfl) hcorr
  set m₂ : MMachine := { world := w₁, control := .force c [], work := work }
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ :=
    hB φ ρ' m₂ c ⟨(M, ρ'), .suspended⟩ .carrier rfl hnew rfl rfl hρ
      (hcorr₁.mark_private hcnot hnew) hcnot
  have hrel₁ : List.Forall₂ (ResRel φ w₁ []) L leaves₁ := by
    simpa [Mode.apply] using hrel
  -- each returned machine passes `callRet` in two transitions
  have pops : ∀ {L : List Result} {ms : List MMachine},
      List.Forall₂ (ResRel φ w₁ [.resume .callRet]) L ms →
      ∃ k ms', Returns (machineSpec P) [] k ms ms' ∧ List.Forall₂ (ResRel φ w₁ []) L ms' := by
    intro L ms h
    induction h with
    | nil => exact ⟨0, [], .nil, .nil⟩
    | @cons r x L' xs hr _ ih =>
        obtain ⟨k, ms', hrun', hrel'⟩ := ih
        obtain ⟨φ', hp, hf, hcx, hg, o, ho, hor⟩ := hr
        have hx := returns_pop_output P ho rfl
        refine ⟨2 + k, _ :: ms', by simpa using hx.append hrun', .cons ?_ hrel'⟩
        exact ⟨φ', hp, hf, hcx, hg, o, rfl, hor⟩
  obtain ⟨k, leaves₂, hrun₂, hrel₂⟩ := pops (ResRel.forall₂_below [.resume .callRet] hrel₁)
  have hjoin := seq_join (rest := []) (f := .resume .callRet) hrun hrun₂
  refine ⟨n₁ + k + 2, leaves₂, hprefix _ _ (by simpa using hjoin), ?_⟩
  exact forall₂_weaken hrel₂ (List.prefix_refl φ) (Fresh.refl φ _) hgrow

/-! ## Cases of the induction -/

theorem fwd_ret (σ : Store) (ρ : List (Val Nat)) (v : VExp) :
    EvalA P σ ρ (.ret v) [(.ok (v.eval ρ), σ)] := by
  intro φ ρ' m hcorr hρ hc
  exact ⟨1, _, returns_output P hc, .cons (resRel_output hcorr (.ok (VExp.eval_rel hρ v))) .nil⟩

theorem fwd_seq {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L₁ L : List Result}
    (hB : EvalB P σ ρ m L₁) (hK : SeqKF P n ρ L₁ L) : EvalA P σ ρ (.seq m n) L := by
  intro φ ρ' m₀ hcorr hρ hc
  obtain ⟨w₁, c, work, hcnot, hnew, hcorr₁, hgrow, hprefix⟩ :=
    carrier_prefix P (k := .seqRet n ρ') hc (fun _ => rfl) hcorr
  set m₂ : MMachine := { world := w₁, control := .force c [], work := work }
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ :=
    hB φ ρ' m₂ c ⟨(m, ρ'), .suspended⟩ .carrier rfl hnew rfl rfl hρ
      (hcorr₁.mark_private hcnot hnew) hcnot
  have hrel₁ : List.Forall₂ (ResRel φ w₁ []) L₁ leaves₁ := by
    simpa [Mode.apply] using hrel
  obtain ⟨k, leaves₂, hrun₂, hrel₂⟩ :=
    hK φ w₁ ρ' _ hρ (ResRel.forall₂_below [.resume (.seqRet n ρ')] hrel₁)
  have hjoin := seq_join (rest := []) (f := .resume (.seqRet n ρ')) hrun hrun₂
  refine ⟨n₁ + k + 2, leaves₂, hprefix _ _ (by simpa using hjoin), ?_⟩
  exact forall₂_weaken hrel₂ (List.prefix_refl φ) (Fresh.refl φ _) hgrow

/-- Allocating a cell bound in the continuation (`need` and `delay`). -/
theorem fwd_bind_cell {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L : List Result}
    (mk : Nat → Val Nat) (mk' : CellId → MVal)
    (hrel : ∀ (φ : List CellId) (c : CellId), (φ ++ [c])[φ.length]? = some c →
      ValRel (φ ++ [c]) (mk φ.length) (mk' c))
    (resume : MEnv → MResume)
    (hafter : ∀ ρ' c, afterAllocation (resume ρ') c = enter n (mk' c :: ρ'))
    (hA : EvalA P (σ.alloc m ρ) (mk σ.cells.length :: ρ) n L) :
    ∀ (φ : List CellId) (ρ' : MEnv) (m₀ : MMachine), Corr φ σ m₀.world → EnvRel φ ρ ρ' →
      m₀.control = .run (.alloc (m, ρ') (resume ρ')) [] →
      ∃ k leaves, Returns (machineSpec P) [] k [m₀] leaves ∧
        List.Forall₂ (ResRel φ m₀.world []) L leaves := by
  intro φ ρ' m₀ hcorr hρ hc
  obtain ⟨w₁, ha⟩ := hcorr.allocate (m, ρ') 0
  have hs := step_alloc P m₀ (m, ρ') (resume ρ') [] hc w₁ _ ha
  set c := m₀.world.freshCell 0
  have hcorr₁ : Corr (φ ++ [c]) (σ.alloc m ρ) w₁ := hcorr.alloc_cell hρ ha
  have hlen : σ.cells.length = φ.length := hcorr.length.symm
  have hφc : (φ ++ [c])[φ.length]? = some c := by simp
  have hρ₁ : EnvRel (φ ++ [c]) (mk σ.cells.length :: ρ) (mk' c :: ρ') := by
    rw [hlen]; exact .cons (hrel φ c hφc) (hρ.mono (List.prefix_append φ [c]))
  obtain ⟨n₁, leaves, hrun, hrel'⟩ := hA (φ ++ [c]) (mk' c :: ρ')
    (finished m₀ w₁ (.run (afterAllocation (resume ρ') c) []) 1 1 1 1) hcorr₁ hρ₁
    (by simp [hafter])
  refine ⟨n₁ + 1, leaves, returns_step P hs (run_not_returned hc) hrun, ?_⟩
  refine forall₂_weaken hrel' (List.prefix_append φ [c]) (Fresh.alloc ?_) (Grows.of_allocate ha)
  simp [c, World.freshCell]

theorem fwd_need {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L : List Result}
    (hA : EvalA P (σ.alloc m ρ) (.need σ.cells.length :: ρ) n L) : EvalA P σ ρ (.need m n) L := by
  intro φ ρ' m₀ hcorr hρ hc
  exact fwd_bind_cell P .need .need (fun _ _ h => .need h) (fun ρ' => .needAlloc n ρ')
    (fun _ _ => rfl) hA φ ρ' m₀ hcorr hρ hc

theorem fwd_delay {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L : List Result}
    (hA : EvalA P (σ.alloc m ρ) (.thunk σ.cells.length :: ρ) n L) :
    EvalA P σ ρ (.delay m n) L := by
  intro φ ρ' m₀ hcorr hρ hc
  exact fwd_bind_cell P .thunk .thunk (fun _ _ h => .thunk h) (fun ρ' => .delayAlloc n ρ')
    (fun _ _ => rfl) hA φ ρ' m₀ hcorr hρ hc

theorem fwd_force {σ : Store} {ρ : List (Val Nat)} {v : VExp} {L : List Result}
    (hF : ForceF P σ (v.eval ρ) L) : EvalA P σ ρ (.force v) L := by
  intro φ ρ' m hcorr hρ hc
  exact hF φ (v.eval ρ') m hcorr (VExp.eval_rel hρ v) hc

theorem fwd_caseConHit {σ : Store} {ρ : List (Val Nat)} {v : VExp} {c k : Nat} {hit miss : Comp}
    {args : List (Val Nat)} {L : List Result} (hm : (v.eval ρ).matchCon c k = some args)
    (hA : EvalA P σ (args ++ ρ) hit L) : EvalA P σ ρ (.caseCon v c k hit miss) L := by
  intro φ ρ' m hcorr hρ hc
  rcases (VExp.eval_rel hρ v).matchCon c k with ⟨h1, _⟩ | ⟨a, a', h1, h2, hargs⟩
  · rw [hm] at h1; cases h1
  · rw [hm] at h1; cases h1
    exact hA φ (a' ++ ρ') m hcorr (List.rel_append hargs hρ) (by rw [hc]; simp [enter, h2])

theorem fwd_caseConMiss {σ : Store} {ρ : List (Val Nat)} {v : VExp} {c k : Nat} {hit miss : Comp}
    {L : List Result} (hm : (v.eval ρ).matchCon c k = none)
    (hA : EvalA P σ ρ miss L) : EvalA P σ ρ (.caseCon v c k hit miss) L := by
  intro φ ρ' m hcorr hρ hc
  rcases (VExp.eval_rel hρ v).matchCon c k with ⟨_, h2⟩ | ⟨a, a', h1, _, _⟩
  · exact hA φ ρ' m hcorr hρ (by rw [hc]; simp [enter, h2])
  · rw [hm] at h1; cases h1

theorem fwd_caseAppHit {σ : Store} {ρ : List (Val Nat)} {v : VExp} {hit miss : Comp}
    {f x : Val Nat} {L : List Result} (hm : (v.eval ρ).matchApp = some (f, x))
    (hA : EvalA P σ (f :: x :: ρ) hit L) : EvalA P σ ρ (.caseApp v hit miss) L := by
  intro φ ρ' m hcorr hρ hc
  rcases (VExp.eval_rel hρ v).matchApp with ⟨h1, _⟩ | ⟨f₀, x₀, f', x', h1, h2, hf, hx⟩
  · rw [hm] at h1; cases h1
  · rw [hm] at h1; cases h1
    exact hA φ (f' :: x' :: ρ') m hcorr (.cons hf (.cons hx hρ)) (by rw [hc]; simp [enter, h2])

theorem fwd_caseAppMiss {σ : Store} {ρ : List (Val Nat)} {v : VExp} {hit miss : Comp}
    {L : List Result} (hm : (v.eval ρ).matchApp = none)
    (hA : EvalA P σ ρ miss L) : EvalA P σ ρ (.caseApp v hit miss) L := by
  intro φ ρ' m hcorr hρ hc
  rcases (VExp.eval_rel hρ v).matchApp with ⟨_, h2⟩ | ⟨f₀, x₀, f', x', h1, _, _, _⟩
  · exact hA φ ρ' m hcorr hρ (by rw [hc]; simp [enter, h2])
  · rw [hm] at h1; cases h1

theorem fwd_fail (σ : Store) (ρ : List (Val Nat)) : EvalA P σ ρ .fail [(.fail, σ)] := by
  intro φ ρ' m hcorr hρ hc
  exact ⟨1, _, returns_output P hc, .cons (resRel_output hcorr .failDomain) .nil⟩

theorem fwd_emit {σ : Store} {ρ : List (Val Nat)} {e : Nat} {m : Comp} {L : List Result}
    (hA : EvalA P (σ.emit e) ρ m L) : EvalA P σ ρ (.emit e m) L := by
  intro φ ρ' m₀ hcorr hρ hc
  have hs := step_emit P m₀ e (enter m ρ') [] hc
  obtain ⟨n₁, leaves, hrun, hrel⟩ :=
    hA φ ρ' (finished m₀ (recorded m₀.world (.effect e)) (.run (enter m ρ') []) 0 0 1 0)
      (hcorr.trace e) hρ rfl
  exact ⟨n₁ + 1, leaves, returns_step P hs (run_not_returned hc) hrun, forall₂_base hrel rfl rfl⟩

theorem fwd_quote (σ : Store) (ρ : List (Val Nat)) (m : Comp) :
    EvalA P σ ρ (.quote m) [(.ok (.code σ.cells.length), σ.alloc m ρ)] := by
  intro φ ρ' m₀ hcorr hρ hc
  have hc₀ : m₀.control = .run (.alloc (m, ρ') .quoteAlloc) [] := hc
  obtain ⟨w₁, ha⟩ := hcorr.allocate (m, ρ') 0
  have hs := step_alloc P m₀ (m, ρ') .quoteAlloc [] hc₀ w₁ _ ha
  set c := m₀.world.freshCell 0
  set m₁ := finished m₀ w₁ (.run (afterAllocation .quoteAlloc c) []) 1 1 1 1
  have hc₁ : m₁.control = .run (.output (.value (.code c))) [] := rfl
  have hcorr₁ : Corr (φ ++ [c]) (σ.alloc m ρ) w₁ := hcorr.alloc_cell hρ ha
  have hlen : σ.cells.length = φ.length := hcorr.length.symm
  refine ⟨2, _, returns_step P hs (run_not_returned hc₀) (returns_output P hc₁), .cons ?_ .nil⟩
  refine (resRel_output (o := .ok (.code σ.cells.length)) hcorr₁ ?_).weaken
    (List.prefix_append φ [c]) (Fresh.alloc ?_) (Grows.of_allocate ha)
  · rw [hlen]; exact .ok (.code (by simp))
  · simp [c, World.freshCell]

/-! ## Calls, choice and failure of rules -/

/-- A forced cell whose origin has exactly one alternative, running `M'` in an
environment derived from the origin's. -/
theorem evalB_single {σ : Store} {ρ ρs : List (Val Nat)} {M M' : Comp} {L : List Result}
    (lbl : MRule) (f : MEnv → MEnv) (hf : ∀ φ ρ', EnvRel φ ρ ρ' → EnvRel φ ρs (f ρ'))
    (halt : ∀ ρ', alternatives P (M, ρ') = [(lbl, enter M' (f ρ'))])
    (hA : EvalA P σ ρs M' L) : EvalB P σ ρ M L := by
  intro φ ρ' m c rec mode hc hl hs horig hρ hcorr hmode
  have halts : alternatives P rec.origin = [(lbl, enter M' (f ρ'))] := by rw [horig]; exact halt ρ'
  have hstep := step_force_suspended P m c [] hc rec hl hs _ _ halts
  rw [branchAlternatives_eq] at hstep
  set base : MWorld := { m.world with nextEvaluator := m.world.nextEvaluator + 1 }
  set x := finished m (recorded (recorded ((base.fork 0).setKnownCache c rec
    (.evaluating m.world.nextEvaluator)) (.evaluate c m.world.nextEvaluator))
    (.chooseRule c lbl)) (.run (enter M' (f ρ')) []) 1 1 2 0
  have hinner : branchInner m base c rec m.world.nextEvaluator 0 [(lbl, enter M' (f ρ'))] = [x] :=
    rfl
  rw [hinner] at hstep
  have hcx : Corr φ σ x.world := hcorr.of_heap_eq rfl rfl (by
    simp [x, base, markWorld, recorded, World.record, World.fork, World.setKnownCache])
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ := hA φ (f ρ') x hcx (hf φ ρ' hρ) rfl
  exact evalB_core P hc hl hs hstep (by simp) hcorr hmode hrun (forall₂_base hrel rfl rfl)

/-- A forced cell whose origin has no alternative: a no-rule retry, the cell
left suspended. -/
theorem evalB_noRule {σ : Store} {ρ : List (Val Nat)} {M : Comp}
    (halt : ∀ ρ', alternatives P (M, ρ') = []) : EvalB P σ ρ M [(.fail, σ)] := by
  intro φ ρ' m c rec mode hc hl hs horig hρ hcorr hmode
  have halts : alternatives P rec.origin = [] := by rw [horig]; exact halt ρ'
  have hstep := step_force_suspended_nil P m c [] hc rec hl hs halts
  set leaf := retryMachine m (recorded { m.world with nextEvaluator := m.world.nextEvaluator + 1 }
    (.evaluate c m.world.nextEvaluator)) c (.noRule c) [] 1 0 1 0
  have hleaf : leaf.control = .returned (.retryableFault (.noRule c)) [] := rfl
  have hheap : leaf.world.heap = m.world.heap := rfl
  have hother : ∀ c', c' ≠ c → leaf.world.heap.lookup c' =
      (markWorld m.world c rec).heap.lookup c' := by
    intro c' hne; rw [hheap, markWorld_lookup_other _ _ hne]
  refine ⟨1, [leaf], returns_step P hstep (force_not_returned hc) (Returns.single_leaf _ hleaf),
    .cons ?_ .nil⟩
  refine ⟨φ, List.prefix_refl φ, Fresh.refl φ _, ?_, Grows.of_heap hheap le_rfl,
    _, hleaf, ?_⟩
  · cases mode with
    | carrier =>
        exact hcorr.set_private hmode hother
          (fun _ _ => ⟨_, markWorld_lookup_same _ _ _⟩) rfl (by
            simp [leaf, markWorld, recorded, World.record])
    | named ℓ =>
        obtain ⟨hφ, s, hs', _⟩ := hmode
        obtain ⟨c'', rec'', hc'', hl'', hr''⟩ := hcorr.cells ℓ s hs'
        rw [hφ] at hc''; cases hc''
        rw [markWorld_lookup_same] at hl''; cases hl''
        have hcode : rec.origin.1 = s.code := hr''.code
        have henv : EnvRel φ s.env rec.origin.2 := hr''.env
        exact hcorr.set_named (memo := .pending) (rec' := rec) hφ hs' (by rw [hheap]; exact hl)
          ⟨hcode, henv, by rw [hs]; exact .pending⟩ hother rfl (by
            simp [leaf, markWorld, recorded, World.record])
  · rw [Mode.apply_fst]; exact .failNoRule c

theorem fwd_call_B {σ : Store} {ρ : List (Val Nat)} {f : Nat} {args : List VExp}
    {L : List Result} (hne : candidates P f args.length ≠ [])
    (hAlts : AltsF P σ ((candidates P f args.length).map
      fun r => (r.body, args.map (·.eval ρ))) L) :
    EvalB P σ ρ (.call f args) L := by
  intro φ ρ' m c rec mode hc hl hs horig hρ hcorr hmode
  set bodies := (candidates P f args.length).map (·.body)
  have halts : alternatives P rec.origin =
      bodies.map fun b => (MRule.equation, enter b (args.map (·.eval ρ'))) := by
    rw [horig]; simp [alternatives, bodies, List.map_map, Function.comp_def]
  obtain ⟨b₀, bs, hb⟩ : ∃ b₀ bs, bodies = b₀ :: bs := by
    cases hcs : candidates P f args.length with
    | nil => exact absurd hcs hne
    | cons r rs => exact ⟨r.body, rs.map (·.body), by simp [bodies, hcs]⟩
  rw [hb] at halts
  have hstep := step_force_suspended P m c [] hc rec hl hs _ _ halts
  rw [branchAlternatives_eq] at hstep
  have hrel_in := branchInner_rules m c rec (args.map (·.eval ρ)) (args.map (·.eval ρ'))
    (hρ.map_eval args) .equation (b₀ :: bs) 0
  have hbs : (candidates P f args.length).map (fun r => (r.body, args.map (·.eval ρ))) =
      (b₀ :: bs).map fun b => (b, args.map (·.eval ρ)) := by
    rw [← hb]; simp [bodies, List.map_map, Function.comp_def]
  rw [hbs] at hAlts
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ := hAlts φ (markWorld m.world c rec) _ hcorr hrel_in
  refine evalB_core P hc hl hs hstep ?_ hcorr hmode hrun hrel
  intro h
  have := congrArg List.length h
  simp [branchInner_length] at this

theorem fwd_choose_B {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L₁ L₂ : List Result}
    (hA₁ : EvalA P σ ρ m L₁) (hA₂ : EvalA P σ ρ n L₂) : EvalB P σ ρ (.choose m n) (L₁ ++ L₂) := by
  intro φ ρ' m₀ c rec mode hc hl hs horig hρ hcorr hmode
  have halts : alternatives P rec.origin = [(.left, enter m ρ'), (.right, enter n ρ')] := by
    rw [horig]; rfl
  have hstep := step_force_suspended P m₀ c [] hc rec hl hs _ _ halts
  rw [branchAlternatives_eq] at hstep
  set base : MWorld := { m₀.world with nextEvaluator := m₀.world.nextEvaluator + 1 }
  set inner := branchInner m₀ base c rec m₀.world.nextEvaluator 0
    [(.left, enter m ρ'), (.right, enter n ρ')]
  obtain ⟨x₁, x₂, hinner⟩ : ∃ x₁ x₂, inner = [x₁, x₂] := ⟨_, _, rfl⟩
  have hw := branchInner_world m₀ base c rec m₀.world.nextEvaluator 0
    [(.left, enter m ρ'), (.right, enter n ρ')]
  have hctl := branchInner_control m₀ base c rec m₀.world.nextEvaluator 0
    [(.left, enter m ρ'), (.right, enter n ρ')]
  rw [show branchInner m₀ base c rec m₀.world.nextEvaluator 0
    [(.left, enter m ρ'), (.right, enter n ρ')] = [x₁, x₂] from hinner] at hw hctl
  rw [hinner] at hstep
  obtain ⟨hw₁h, hw₁n, hw₁e⟩ := hw x₁ (by simp)
  obtain ⟨hw₂h, hw₂n, hw₂e⟩ := hw x₂ (by simp)
  cases hctl with
  | cons hx₁ hrest =>
      cases hrest with
      | cons hx₂ _ =>
          obtain ⟨k₁, l₁, hr₁, hl₁⟩ := hA₁ φ ρ' x₁ (hcorr.of_heap_eq hw₁h hw₁n hw₁e) hρ hx₁
          obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hA₂ φ ρ' x₂ (hcorr.of_heap_eq hw₂h hw₂n hw₂e) hρ hx₂
          refine evalB_core P hc hl hs hstep (by simp) hcorr hmode (hr₁.append hr₂) ?_
          exact List.rel_append (forall₂_base (w := markWorld m₀.world c rec) hl₁ hw₁h hw₁n)
            (forall₂_base (w := markWorld m₀.world c rec) hl₂ hw₂h hw₂n)

/-! ## Activation and primitives -/

theorem prim_rel {φ : List CellId} (hφ : φ.Nodup) (op : Prim) {vs : List (Val Nat)} {vs' : MEnv}
    (h : EnvRel φ vs vs') : ∃ o', primLocal op vs' = .output o' ∧ OutRel φ (primOutcome op vs) o' := by
  cases op with
  | eq yes no =>
      rcases h with _ | ⟨ha, h⟩
      · exact ⟨_, rfl, .failDomain⟩
      · rcases h with _ | ⟨hb, h⟩
        · exact ⟨_, rfl, .failDomain⟩
        · rcases h with _ | ⟨_, _⟩
          · rename_i a a' b b'
            have hiff : (a = b ↔ a' = b') :=
              ⟨fun e => by subst e; exact ha.functional hb,
               fun e => by subst e; exact ha.injective hφ hb⟩
            refine ⟨_, rfl, ?_⟩
            simp only [primOutcome, Prim.apply]
            by_cases e : a = b
            · rw [if_pos e, if_pos (hiff.mp e)]; exact .ok (.sym _)
            · rw [if_neg e, if_neg (fun e' => e (hiff.mpr e'))]; exact .ok (.sym _)
          · exact ⟨_, rfl, .failDomain⟩

theorem fwd_prim (σ : Store) (ρ : List (Val Nat)) (op : Prim) (args : List VExp) :
    EvalA P σ ρ (.prim op args) [(primOutcome op (args.map (·.eval ρ)), σ)] := by
  intro φ ρ' m hcorr hρ hc
  obtain ⟨o', ho', hrel⟩ := prim_rel hcorr.nodup op (hρ.map_eval args)
  have hc' : m.control = .run (.output o') [] := by rw [hc]; simp [enter, ho']
  exact ⟨1, _, returns_output P hc', .cons (resRel_output hcorr hrel) .nil⟩

theorem fwd_runOther {σ : Store} {ρ : List (Val Nat)} {v : VExp}
    (hn : ∀ ℓ, v.eval ρ ≠ .code ℓ) :
    EvalA P σ ρ (.run v) [(.ok (.app (.sym unquoteHead) (v.eval ρ)), σ)] := by
  intro φ ρ' m hcorr hρ hc
  have hvr := VExp.eval_rel hρ v
  have hloc : runLocal (v.eval ρ') = .output (.value (.app (.sym unquoteHead) (v.eval ρ'))) := by
    generalize hw : v.eval ρ = w at hvr hn
    generalize hw' : v.eval ρ' = w' at hvr
    cases hvr with
    | sym c => rfl
    | app _ _ => rfl
    | need _ => rfl
    | thunk _ => rfl
    | code _ => exact absurd rfl (hn _)
  have hc' : m.control = .run (.output (.value (.app (.sym unquoteHead) (v.eval ρ')))) [] := by
    rw [hc]; simp [enter, hloc]
  exact ⟨1, _, returns_output P hc',
    .cons (resRel_output hcorr (.ok (.app (.sym _) hvr))) .nil⟩

/-- Resampling a cell: a fresh carrier with the same origin, demanded under
`forceRet`, then the indirections followed. -/
theorem resample_run {σ : Store} {ℓ : Nat} {s : Suspension} {L₁ L : List Result}
    {φ : List CellId} {c : CellId} {m₀ : MMachine}
    (hφ : φ[ℓ]? = some c) (hs : σ.cells[ℓ]? = some s) (hcorr : Corr φ σ m₀.world)
    (hc : m₀.control = .run (.resample c .resampleAlloc) [])
    (hB : EvalB P σ s.env s.code L₁) (hF : FollowF P L₁ L) :
    ∃ k leaves, Returns (machineSpec P) [] k [m₀] leaves ∧
      List.Forall₂ (ResRel φ m₀.world []) L leaves := by
  obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
  rw [hφ] at hc₀; cases hc₀
  obtain ⟨w₁, ha⟩ := hcorr.allocate recC.origin (c.generation + 1)
  obtain ⟨hnew, -, -, -⟩ := allocate_heap ha
  set c' := m₀.world.freshCell (c.generation + 1)
  have hs₁ := step_resample P m₀ c .resampleAlloc [] hc recC hlC w₁ c' ha
  set m₁ := finished m₀ (recorded w₁ (.resample c c'))
    (.run (afterAllocation .resampleAlloc c') []) 2 1 2 1
  have hc₁ : m₁.control = .run (.demand c' .forceRet) [] := rfl
  have hs₂ := step_demand P m₁ c' .forceRet [] hc₁
  set wk := (finished m₁ m₁.world (.force c' (.resume .forceRet :: [])) 0 0 0 0).work
  set m₂ : MMachine := ⟨recorded w₁ (.resample c c'), .force c' [], wk⟩
  have heq : finished m₁ m₁.world (.force c' (.resume .forceRet :: [])) 0 0 0 0 =
      below [.resume .forceRet] m₂ := rfl
  have hcorr₁ : Corr φ σ m₂.world := (hcorr.after_allocate ha).of_heap_eq rfl rfl (by
    simp [m₂, recorded, World.record])
  have hcnot : c' ∉ φ := hcorr.fresh_not_mem _
  have horig : recC.origin = (s.code, recC.origin.2) := by
    rw [← hrC.code]
  obtain ⟨n₁, leaves₁, hrun, hrel⟩ :=
    hB φ recC.origin.2 m₂ c' ⟨recC.origin, .suspended⟩ .carrier rfl hnew rfl horig hrC.env
      (hcorr₁.mark_private hcnot hnew) hcnot
  have hrel₁ : List.Forall₂ (ResRel φ m₂.world []) L₁ leaves₁ := by
    simpa [Mode.apply] using hrel
  obtain ⟨k, leaves₂, hrun₂, hrel₂⟩ := hF φ m₂.world _
    (ResRel.forall₂_below [.resume .forceRet] hrel₁)
  have hjoin := seq_join (rest := []) (f := .resume .forceRet) hrun hrun₂
  have h₂ : Returns (machineSpec P) [] (n₁ + k + 1) [m₁] leaves₂ :=
    returns_step P hs₂ (run_not_returned hc₁) (by rw [heq]; simpa using hjoin)
  refine ⟨n₁ + k + 1 + 1, leaves₂, returns_step P hs₁ (run_not_returned hc) h₂, ?_⟩
  exact forall₂_weaken hrel₂ (List.prefix_refl φ) (Fresh.refl φ _)
    ((Grows.of_allocate ha).trans (Grows.of_heap rfl le_rfl))

theorem fwd_runCode {σ : Store} {ρ : List (Val Nat)} {v : VExp} {ℓ : Nat} {s : Suspension}
    {L₁ L : List Result} (hv : v.eval ρ = .code ℓ) (hs : σ.cells[ℓ]? = some s)
    (hB : EvalB P σ s.env s.code L₁) (hF : FollowF P L₁ L) : EvalA P σ ρ (.run v) L := by
  intro φ ρ' m₀ hcorr hρ hc
  have hvr := VExp.eval_rel hρ v
  rw [hv] at hvr
  generalize hw' : v.eval ρ' = w' at hvr
  cases hvr with
  | @code _ c hφ =>
      have hc' : m₀.control = .run (.resample c .resampleAlloc) [] := by
        rw [hc]; simp [enter, hw', runLocal]
      exact resample_run P hφ hs hcorr hc' hB hF

/-! ## Alternatives, continuations and forcing -/

theorem fwd_altsNil (σ : Store) : AltsF P σ [] [] := by
  intro φ w ms _ h; cases h; exact ⟨0, [], .nil, .nil⟩

theorem fwd_altsCons {σ : Store} {m : Comp} {ρ : List (Val Nat)}
    {bs : List (Comp × List (Val Nat))} {L₁ L₂ : List Result}
    (hA : EvalA P σ ρ m L₁) (hAlts : AltsF P σ bs L₂) : AltsF P σ ((m, ρ) :: bs) (L₁ ++ L₂) := by
  intro φ w ms hcorr h
  cases h with
  | @cons _ x _ xs hx hxs =>
      obtain ⟨hheap, hnext, hevents, ρ', hρ, hcx⟩ := hx
      obtain ⟨k₁, l₁, hr₁, hl₁⟩ := hA φ ρ' x (hcorr.of_heap_eq hheap hnext hevents) hρ hcx
      obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hAlts φ w xs hcorr hxs
      exact ⟨k₁ + k₂, l₁ ++ l₂, hr₁.append hr₂,
        List.rel_append (forall₂_base hl₁ hheap hnext) hl₂⟩

theorem fwd_seqKNil (n : Comp) (ρ : List (Val Nat)) : SeqKF P n ρ [] [] := by
  intro φ w ρ' ms _ h; cases h; exact ⟨0, [], .nil, .nil⟩

theorem fwd_seqKOk {n : Comp} {ρ : List (Val Nat)} {v : Val Nat} {σ : Store}
    {rs L₁ L₂ : List Result} (hA : EvalA P σ (v :: ρ) n L₁) (hK : SeqKF P n ρ rs L₂) :
    SeqKF P n ρ ((.ok v, σ) :: rs) (L₁ ++ L₂) := by
  intro φ w ρ' ms hρ h
  cases h with
  | @cons _ x _ xs hx hxs =>
      obtain ⟨φ', hp, hf, hcx, hg, o, ho, hor⟩ := hx
      cases hor with
      | @ok _ v' hv =>
          have hs := step_returned_resume P x (.value v') (.seqRet n ρ') [] ho
          obtain ⟨k₁, l₁, hr₁, hl₁⟩ := hA φ' (v' :: ρ')
            (finished x x.world (.run (afterDemand (.seqRet n ρ') (.value v')) []) 0 0 0 0)
            hcx (.cons hv (hρ.mono hp)) rfl
          obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hK φ w ρ' xs hρ hxs
          refine ⟨k₁ + 1 + k₂, l₁ ++ l₂,
            (returns_step P hs (returned_cons_not_returned ho) hr₁).append hr₂, ?_⟩
          exact List.rel_append (forall₂_weaken hl₁ hp hf hg) hl₂

theorem fwd_seqKStop {n : Comp} {ρ : List (Val Nat)} {o : Outcome} {σ : Store}
    {rs L₂ : List Result} (hstop : o.isOk = false) (hK : SeqKF P n ρ rs L₂) :
    SeqKF P n ρ ((o, σ) :: rs) ((o, σ) :: L₂) := by
  intro φ w ρ' ms hρ h
  cases h with
  | @cons _ x _ xs hx hxs =>
      obtain ⟨φ', hp, hf, hcx, hg, o', ho, hor⟩ := hx
      obtain ⟨reason, rfl⟩ := hor.isOk_false hstop
      have hx := returns_pop_output P ho rfl
      obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hK φ w ρ' xs hρ hxs
      exact ⟨2 + k₂, _ :: l₂, hx.append hr₂, .cons ⟨φ', hp, hf, hcx, hg, _, rfl, hor⟩ hl₂⟩

theorem fwd_followNil : FollowF P [] [] := by
  intro φ w ms h; cases h; exact ⟨0, [], .nil, .nil⟩

theorem fwd_followOk {v : Val Nat} {σ : Store} {rs L₁ L₂ : List Result}
    (hF : ForceF P σ v L₁) (hK : FollowF P rs L₂) : FollowF P ((.ok v, σ) :: rs) (L₁ ++ L₂) := by
  intro φ w ms h
  cases h with
  | @cons _ x _ xs hx hxs =>
      obtain ⟨φ', hp, hf, hcx, hg, o, ho, hor⟩ := hx
      cases hor with
      | @ok _ v' hv =>
          have hs := step_returned_resume P x (.value v') .forceRet [] ho
          obtain ⟨k₁, l₁, hr₁, hl₁⟩ := hF φ' v'
            (finished x x.world (.run (afterDemand .forceRet (.value v')) []) 0 0 0 0) hcx hv rfl
          obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hK φ w xs hxs
          refine ⟨k₁ + 1 + k₂, l₁ ++ l₂,
            (returns_step P hs (returned_cons_not_returned ho) hr₁).append hr₂, ?_⟩
          exact List.rel_append (forall₂_weaken hl₁ hp hf hg) hl₂

theorem fwd_followStop {o : Outcome} {σ : Store} {rs L₂ : List Result}
    (hstop : o.isOk = false) (hK : FollowF P rs L₂) : FollowF P ((o, σ) :: rs) ((o, σ) :: L₂) := by
  intro φ w ms h
  cases h with
  | @cons _ x _ xs hx hxs =>
      obtain ⟨φ', hp, hf, hcx, hg, o', ho, hor⟩ := hx
      obtain ⟨reason, rfl⟩ := hor.isOk_false hstop
      have hx := returns_pop_output P ho rfl
      obtain ⟨k₂, l₂, hr₂, hl₂⟩ := hK φ w xs hxs
      exact ⟨2 + k₂, _ :: l₂, hx.append hr₂, .cons ⟨φ', hp, hf, hcx, hg, _, rfl, hor⟩ hl₂⟩

theorem fwd_forceWhnf {σ : Store} {v : Val Nat} (hw : v.isCell = false) :
    ForceF P σ v [(.ok v, σ)] := by
  intro φ v' m hcorr hv hc
  have hloc : forceLocal v' = .output (.value v') := by
    cases hv with
    | sym c => rfl
    | app _ _ => rfl
    | need _ => simp [Val.isCell] at hw
    | thunk _ => simp [Val.isCell] at hw
    | code _ => rfl
  have hc' : m.control = .run (.output (.value v')) [] := by rw [hc, hloc]
  exact ⟨1, _, returns_output P hc', .cons (resRel_output hcorr (.ok hv)) .nil⟩

theorem fwd_forceDone {σ : Store} {ℓ : Nat} {s : Suspension} {w : Val Nat} {L : List Result}
    (hs : σ.cells[ℓ]? = some s) (hk : s.memo = .done w) (hF : ForceF P σ w L) :
    ForceF P σ (.need ℓ) L := by
  intro φ v' m hcorr hv hc
  cases hv with
  | @need _ c hφ =>
      obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
      rw [hφ] at hc₀; cases hc₀
      have hmemo := hrC.memo
      rw [hk] at hmemo
      generalize hcache : recC.cache = cache at hmemo
      cases hmemo with
      | @done _ w' hw =>
          have hc₁ : m.control = .run (.demand c .forceRet) [] := hc
          have hs₁ := step_demand P m c .forceRet [] hc₁
          set m₁ := finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0
          have hs₂ := step_force_value P m₁ c _ rfl recC hlC w' hcache
          set m₂ := finished m₁ (recorded m₁.world (.observe c (.value w')))
            (.returned (.value w') (.resume .forceRet :: [])) 1 0 1 0
          have hs₃ := step_returned_resume P m₂ (.value w') .forceRet [] rfl
          obtain ⟨k, l, hr, hl⟩ := hF φ w'
            (finished m₂ m₂.world (.run (afterDemand .forceRet (.value w')) []) 0 0 0 0)
            (hcorr.of_heap_eq rfl rfl (by simp [m₂, m₁, recorded, World.record])) hw rfl
          refine ⟨k + 1 + 1 + 1, l, ?_, forall₂_base hl rfl rfl⟩
          refine returns_step P hs₁ (run_not_returned hc₁) ?_
          refine returns_step P hs₂ (force_not_returned rfl) ?_
          exact returns_step P hs₃ (returned_cons_not_returned rfl) hr

theorem fwd_forceBlackhole {σ : Store} {ℓ : Nat} {s : Suspension}
    (hs : σ.cells[ℓ]? = some s) (hk : s.memo = .evaluating) :
    ForceF P σ (.need ℓ) [(.blackhole, σ)] := by
  intro φ v' m hcorr hv hc
  cases hv with
  | @need _ c hφ =>
      obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
      rw [hφ] at hc₀; cases hc₀
      have hmemo := hrC.memo
      rw [hk] at hmemo
      generalize hcache : recC.cache = cache at hmemo
      cases hmemo with
      | evaluating owner =>
          have hc₁ : m.control = .run (.demand c .forceRet) [] := hc
          have hs₁ := step_demand P m c .forceRet [] hc₁
          set m₁ := finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0
          have hs₂ := step_force_evaluating P m₁ c _ rfl recC hlC owner hcache
          have hpop := returns_pop_output P
            (m := retryMachine m₁ m₁.world c (.blackhole c) [.resume .forceRet] 1 0 0 0)
            (k := .forceRet) rfl rfl
          exact ⟨2 + 1 + 1, _,
            returns_step P hs₁ (run_not_returned hc₁)
              (returns_step P hs₂ (force_not_returned rfl) hpop),
            .cons ⟨φ, List.prefix_refl φ, Fresh.refl φ _, hcorr.of_heap_eq rfl rfl (by simp [m₁, recorded, World.record]),
              Grows.of_heap rfl le_rfl, _, rfl, .blackhole c⟩ .nil⟩

theorem fwd_forcePending {σ : Store} {ℓ : Nat} {s : Suspension} {L₁ L : List Result}
    (hs : σ.cells[ℓ]? = some s) (hk : s.memo = .pending)
    (hB : EvalB P (σ.setMemo ℓ .evaluating) s.env s.code L₁)
    (hF : FollowF P (L₁.map (commitResult ℓ)) L) : ForceF P σ (.need ℓ) L := by
  intro φ v' m hcorr hv hc
  cases hv with
  | @need _ c hφ =>
      obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
      rw [hφ] at hc₀; cases hc₀
      have hmemo := hrC.memo
      rw [hk] at hmemo
      generalize hcache : recC.cache = cache at hmemo
      cases hmemo with
      | pending =>
          have hc₁ : m.control = .run (.demand c .forceRet) [] := hc
          have hs₁ := step_demand P m c .forceRet [] hc₁
          set wk := (finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0).work
          set m₁ : MMachine := ⟨m.world, .force c [], wk⟩
          have heq : finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0 =
              below [.resume .forceRet] m₁ := rfl
          have horig : recC.origin = (s.code, recC.origin.2) := by rw [← hrC.code]
          have hsM : (σ.setMemo ℓ .evaluating).cells[ℓ]? =
              some { s with memo := .evaluating } := by
            simp [Store.setMemo, hs]
          obtain ⟨n₁, leaves₁, hrun, hrel⟩ :=
            hB φ recC.origin.2 m₁ c recC (.named ℓ) rfl hlC hcache horig hrC.env
              (hcorr.mark_named hφ hs hrC) ⟨hφ, _, hsM, rfl⟩
          rw [commitResult_map] at hrel
          obtain ⟨k, leaves₂, hrun₂, hrel₂⟩ := hF φ m.world _
            (ResRel.forall₂_below [.resume .forceRet] hrel)
          have hjoin := seq_join (rest := []) (f := .resume .forceRet) hrun hrun₂
          exact ⟨n₁ + k + 1, leaves₂,
            returns_step P hs₁ (run_not_returned hc₁) (by rw [heq]; simpa using hjoin), hrel₂⟩

theorem fwd_forceThunk {σ : Store} {ℓ : Nat} {s : Suspension} {L₁ L : List Result}
    (hs : σ.cells[ℓ]? = some s) (hB : EvalB P σ s.env s.code L₁) (hF : FollowF P L₁ L) :
    ForceF P σ (.thunk ℓ) L := by
  intro φ v' m hcorr hv hc
  cases hv with
  | @thunk _ c hφ => exact resample_run P hφ hs hcorr hc hB hF

theorem fwd_commitOk {ℓ : Nat} {w : Val Nat} {σ : Store} {rs L₁ L₂ : List Result}
    (hF : ForceF P (σ.setMemo ℓ (.done w)) w L₁) (hK : FollowF P (rs.map (commitResult ℓ)) L₂) :
    FollowF P (((.ok w, σ) :: rs).map (commitResult ℓ)) (L₁ ++ L₂) :=
  fwd_followOk P hF hK

theorem fwd_commitStop {ℓ : Nat} {o : Outcome} {σ : Store} {rs L₂ : List Result}
    (hstop : o.isOk = false) (hK : FollowF P (rs.map (commitResult ℓ)) L₂) :
    FollowF P (((o, σ) :: rs).map (commitResult ℓ)) ((o, σ.setMemo ℓ .pending) :: L₂) := by
  have hc : commitResult ℓ (o, σ) = (o, σ.setMemo ℓ .pending) := by
    cases o with
    | ok v => simp [Outcome.isOk] at hstop
    | fail => rfl
    | blackhole => rfl
  simp only [List.map_cons, hc]
  exact fwd_followStop P hstop hK

/-! ## The forward theorem -/

/-- **Forward adequacy.** Every derivation of the natural semantics is realized
by the reference machine from every related configuration, with the results
related one by one, in order and with multiplicity. -/
theorem forward : ∀ g L, Derives P g L → Fwd P g L := by
  intro g L h
  induction h with
  | ret => exact ⟨fwd_ret P _ _ _, evalB_of_evalA P (fwd_ret P _ _ _) (fun _ => rfl)⟩
  | seq _ _ ih₁ ih₂ =>
      have hA := fwd_seq P ih₁.2 ih₂
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | need _ ih =>
      have hA := fwd_need P ih.1
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | delay _ ih =>
      have hA := fwd_delay P ih.1
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | force _ ih =>
      have hA := fwd_force P ih
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | caseConHit hm _ ih =>
      exact ⟨fwd_caseConHit P hm ih.1, evalB_of_evalA P (fwd_caseConHit P hm ih.1) (fun _ => rfl)⟩
  | caseConMiss hm _ ih =>
      exact ⟨fwd_caseConMiss P hm ih.1, evalB_of_evalA P (fwd_caseConMiss P hm ih.1) (fun _ => rfl)⟩
  | caseAppHit hm _ ih =>
      exact ⟨fwd_caseAppHit P hm ih.1, evalB_of_evalA P (fwd_caseAppHit P hm ih.1) (fun _ => rfl)⟩
  | caseAppMiss hm _ ih =>
      exact ⟨fwd_caseAppMiss P hm ih.1, evalB_of_evalA P (fwd_caseAppMiss P hm ih.1) (fun _ => rfl)⟩
  | call hne _ ih =>
      have hB := fwd_call_B P hne ih
      exact ⟨evalA_of_evalB P hB (fun _ => rfl), hB⟩
  | @callNone σ ρ f args hc =>
      have hB : EvalB P σ ρ (.call f args) [(.fail, σ)] :=
        evalB_noRule P (fun ρ' => by simp [alternatives, hc])
      exact ⟨evalA_of_evalB P hB (fun _ => rfl), hB⟩
  | @callRule σ ρ i args r L hr ha _ ih =>
      have hB : EvalB P σ ρ (.callRule i args) L :=
        evalB_single P .equation (fun ρ' => args.map (·.eval ρ'))
          (fun φ ρ' hρ => hρ.map_eval args) (fun ρ' => by simp [alternatives, hr, ha]) ih.1
      exact ⟨evalA_of_evalB P hB (fun _ => rfl), hB⟩
  | @callRuleNone σ ρ i args hn =>
      have hB : EvalB P σ ρ (.callRule i args) [(.fail, σ)] := by
        apply evalB_noRule P
        intro ρ'
        cases hr : P[i]? with
        | none => simp [alternatives, hr]
        | some r => simp [alternatives, hr, hn r hr]
      exact ⟨evalA_of_evalB P hB (fun _ => rfl), hB⟩
  | choose _ _ ih₁ ih₂ =>
      have hB := fwd_choose_B P ih₁.1 ih₂.1
      exact ⟨evalA_of_evalB P hB (fun _ => rfl), hB⟩
  | fail => exact ⟨fwd_fail P _ _, evalB_of_evalA P (fwd_fail P _ _) (fun _ => rfl)⟩
  | emit _ ih =>
      have hA := fwd_emit P ih.1
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | quote => exact ⟨fwd_quote P _ _ _, evalB_of_evalA P (fwd_quote P _ _ _) (fun _ => rfl)⟩
  | runCode hv hs _ _ ih₁ ih₂ =>
      have hA := fwd_runCode P hv hs ih₁.2 ih₂
      exact ⟨hA, evalB_of_evalA P hA (fun _ => rfl)⟩
  | runOther hn =>
      exact ⟨fwd_runOther P hn, evalB_of_evalA P (fwd_runOther P hn) (fun _ => rfl)⟩
  | prim =>
      exact ⟨fwd_prim P _ _ _ _, evalB_of_evalA P (fwd_prim P _ _ _ _) (fun _ => rfl)⟩
  | altsNil => exact fwd_altsNil P _
  | altsCons _ _ ih₁ ih₂ => exact fwd_altsCons P ih₁.1 ih₂
  | seqKNil => exact fwd_seqKNil P _ _
  | seqKOk _ _ ih₁ ih₂ => exact fwd_seqKOk P ih₁.1 ih₂
  | seqKStop hs _ ih => exact fwd_seqKStop P hs ih
  | forceWhnf hw => exact fwd_forceWhnf P hw
  | forceDone hs hk _ ih => exact fwd_forceDone P hs hk ih
  | forceBlackhole hs hk => exact fwd_forceBlackhole P hs hk
  | forcePending hs hk _ _ ih₁ ih₂ => exact fwd_forcePending P hs hk ih₁.2 ih₂
  | forceThunk hs _ _ ih₁ ih₂ => exact fwd_forceThunk P hs ih₁.2 ih₂
  | commitNil => exact fwd_followNil P
  | commitOk _ _ ih₁ ih₂ => exact fwd_commitOk P ih₁ ih₂
  | commitStop hs _ ih => exact fwd_commitStop P hs ih
  | followNil => exact fwd_followNil P
  | followOk _ _ ih₁ ih₂ => exact fwd_followOk P ih₁ ih₂
  | followStop hs _ ih => exact fwd_followStop P hs ih

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
