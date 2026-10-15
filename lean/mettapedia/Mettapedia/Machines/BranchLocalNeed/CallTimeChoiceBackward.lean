import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceAdequacy

/-!
# Backward adequacy: every completed machine run is specified

If the reference machine, started in a configuration related to a judgment of
the natural semantics, completes, then that judgment has a derivation; by the
forward theorem and the determinism of runs, the machine's leaves are then
related to the derived results one by one (`backward_eval`, `observe_backward`).

The proof is a strong induction on the number of machine transitions. Each
judgment form has a motive stating only the existence of a derivation:
`BwdEval` (running `enter M ρ'`), `BwdCell` (forcing a suspended cell), `BwdForce`
(forcing a value), `BwdSeqK` and `BwdFollow` (continuations). A run under a
frame splits (`seq_iff`) into a strictly shorter run to the frame and a strictly
shorter continuation; the forward theorem, applied to the derivation obtained
for the first part, identifies the first part's leaves with derived results, so
the continuation's motive applies to them. The cases that do not take a
transition (forcing, `case`) are discharged by structural induction on the
computation at the same size.

`adequacy` combines both directions at the level of the machine's answers: a
specified observation exists exactly when the machine's frontier halts, and the
answers then agree outcome by outcome, in order and with multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference NeedReturningRuns

variable (P : Program)

/-! ## A commit is a follow of the committed results -/

theorem commitK_of_followK (ℓ : Nat) :
    ∀ (rs L : List Result), Derives P (.followK (rs.map (commitResult ℓ))) L →
      Derives P (.commitK ℓ rs) L := by
  intro rs
  induction rs with
  | nil => intro L h; cases h; exact .commitNil
  | cons r rest ih =>
      intro L h
      obtain ⟨o, σ⟩ := r
      cases o with
      | ok v =>
          cases h with
          | followOk h₁ h₂ => exact .commitOk h₁ (ih _ h₂)
          | followStop hs _ => simp [Outcome.isOk] at hs
      | fail =>
          cases h with
          | followStop _ h₂ => exact .commitStop rfl (ih _ h₂)
      | blackhole =>
          cases h with
          | followStop _ h₂ => exact .commitStop rfl (ih _ h₂)

/-! ## Inverting runs -/

theorem returns_single_inv {m : MMachine} {m' : MMachine} {n : Nat} {leaves : List MMachine}
    (hs : step (machineSpec P) m = [m']) (hr : ∀ o, m.control ≠ .returned o [])
    (h : Returns (machineSpec P) [] n [m] leaves) :
    ∃ n', n = n' + 1 ∧ Returns (machineSpec P) [] n' [m'] leaves := by
  obtain ⟨n', hn, h'⟩ := h.singleton_step hr
  rw [hs] at h'
  exact ⟨n', hn, h'⟩

/-- A run under one frame splits into a run to the frame and its continuation. -/
theorem returns_frame_inv {f : Frame MResume} {m : MMachine} {n : Nat}
    {leaves : List MMachine} (h : Returns (machineSpec P) [] n [below [f] m] leaves) :
    ∃ n₁ n₂ inner, n = n₁ + n₂ ∧ Returns (machineSpec P) [] n₁ [m] inner ∧
      Returns (machineSpec P) [] n₂ (inner.map (below [f])) leaves := by
  have := (seq_iff (rest := []) (f := f) (ms := [m])).mp (by simpa using h)
  obtain ⟨n₁, n₂, inner, hn, h₁, h₂⟩ := this
  exact ⟨n₁, n₂, inner, hn, h₁, h₂⟩

theorem corr_cell {φ : List CellId} {σ : Store} {w : MWorld} (h : Corr φ σ w) {ℓ : Nat}
    {c : CellId} (hc : φ[ℓ]? = some c) : ∃ s, σ.cells[ℓ]? = some s := by
  have hlt : ℓ < σ.cells.length := by
    rw [← h.length]; exact (List.getElem?_eq_some_iff.mp hc).1
  exact ⟨σ.cells[ℓ], List.getElem?_eq_getElem hlt⟩

/-- The leaves of a forced cell's completed run are the forward theorem's leaves
for any derivation of the cell's computation. -/
theorem inner_related {σ : Store} {ρ : List (Val Nat)} {M : Comp} {L₁ : List Result}
    {φ : List CellId} {ρ' : MEnv} {m : MMachine} {c : CellId}
    {rec : CellRecord (Comp × MEnv) MVal Empty} {mode : Mode} {n : Nat} {inner : List MMachine}
    (hL : Derives P (.eval σ ρ M) L₁) (hc : m.control = .force c [])
    (hl : m.world.heap.lookup c = some rec) (hs : rec.cache = .suspended)
    (horig : rec.origin = (M, ρ')) (hρ : EnvRel φ ρ ρ')
    (hcorr : Corr φ σ (markWorld m.world c rec)) (hmode : mode.OK φ σ c)
    (h : Returns (machineSpec P) [] n [m] inner) :
    List.Forall₂ (ResRel φ m.world []) (L₁.map mode.apply) inner := by
  obtain ⟨n', leaves', h', hrel⟩ :=
    (forward P _ _ hL).2 φ ρ' m c rec mode hc hl hs horig hρ hcorr hmode
  obtain ⟨-, rfl⟩ := Returns.deterministic h' h
  exact hrel

/-- Allocating a carrier for `(M, ρ')` and demanding it, inverted. -/
theorem carrier_prefix_inv {φ : List CellId} {σ : Store} {m₀ : MMachine} {M : Comp}
    {ρ' : MEnv} {k₀ k : MResume} (hc : m₀.control = .run (.alloc (M, ρ') k₀) [])
    (hk : ∀ c, afterAllocation k₀ c = .demand c k) (hcorr : Corr φ σ m₀.world)
    {n : Nat} {leaves : List MMachine} (h : Returns (machineSpec P) [] n [m₀] leaves) :
    ∃ (w₁ : MWorld) (c : CellId) (work : Work) (n' : Nat),
      n = n' + 2 ∧ c ∉ φ ∧ w₁.heap.lookup c = some ⟨(M, ρ'), .suspended⟩ ∧ Corr φ σ w₁ ∧
      Returns (machineSpec P) [] n'
        [below [.resume k] ({ world := w₁, control := .force c [], work := work } : MMachine)]
        leaves := by
  obtain ⟨w₁, ha⟩ := hcorr.allocate (M, ρ') 0
  obtain ⟨hnew, -, -, -⟩ := allocate_heap ha
  have hs₁ := step_alloc P m₀ (M, ρ') k₀ [] hc w₁ _ ha
  set c := m₀.world.freshCell 0
  set m₁ := finished m₀ w₁ (.run (afterAllocation k₀ c) []) 1 1 1 1
  have hc₁ : m₁.control = .run (.demand c k) [] := by simp [m₁, hk]
  have hs₂ := step_demand P m₁ c k [] hc₁
  obtain ⟨n₁, rfl, h₁⟩ := returns_single_inv P hs₁ (run_not_returned hc) h
  obtain ⟨n₂, rfl, h₂⟩ := returns_single_inv P hs₂ (run_not_returned hc₁) h₁
  have heq : finished m₁ m₁.world (.force c (.resume k :: [])) 0 0 0 0 =
      below [.resume k] (⟨w₁, .force c [],
        (finished m₁ m₁.world (.force c (.resume k :: [])) 0 0 0 0).work⟩ : MMachine) :=
    rfl
  rw [heq] at h₂
  exact ⟨w₁, c, _, n₂, rfl, hcorr.fresh_not_mem 0, hnew, hcorr.after_allocate ha, h₂⟩

/-! ## The motives -/

def BwdEval (n : Nat) : Prop :=
  ∀ (M : Comp) (σ : Store) (ρ : List (Val Nat)) (φ : List CellId) (ρ' : MEnv) (m : MMachine)
    (leaves : List MMachine),
    Corr φ σ m.world → EnvRel φ ρ ρ' → m.control = .run (enter M ρ') [] →
    Returns (machineSpec P) [] n [m] leaves → ∃ L, Derives P (.eval σ ρ M) L

def BwdCell (n : Nat) : Prop :=
  ∀ (σ : Store) (ρ : List (Val Nat)) (M : Comp) (φ : List CellId) (ρ' : MEnv) (m : MMachine)
    (c : CellId) (rec : CellRecord (Comp × MEnv) MVal Empty) (leaves : List MMachine),
    m.control = .force c [] → m.world.heap.lookup c = some rec → rec.cache = .suspended →
    rec.origin = (M, ρ') → EnvRel φ ρ ρ' → Corr φ σ (markWorld m.world c rec) →
    Returns (machineSpec P) [] n [m] leaves → ∃ L, Derives P (.eval σ ρ M) L

def BwdForce (n : Nat) : Prop :=
  ∀ (σ : Store) (v : Val Nat) (φ : List CellId) (v' : MVal) (m : MMachine)
    (leaves : List MMachine),
    Corr φ σ m.world → ValRel φ v v' → m.control = .run (forceLocal v') [] →
    Returns (machineSpec P) [] n [m] leaves → ∃ L, Derives P (.forceVal σ v) L

def BwdSeqK (n : Nat) : Prop :=
  ∀ (body : Comp) (ρ : List (Val Nat)) (rs : List Result) (φ : List CellId) (w : MWorld)
    (ρ' : MEnv) (ms leaves : List MMachine),
    EnvRel φ ρ ρ' → List.Forall₂ (ResRel φ w [.resume (.seqRet body ρ')]) rs ms →
    Returns (machineSpec P) [] n ms leaves → ∃ L, Derives P (.seqK body ρ rs) L

def BwdFollow (n : Nat) : Prop :=
  ∀ (rs : List Result) (φ : List CellId) (w : MWorld) (ms leaves : List MMachine),
    List.Forall₂ (ResRel φ w [.resume .forceRet]) rs ms →
    Returns (machineSpec P) [] n ms leaves → ∃ L, Derives P (.followK rs) L

/-! ## The alternatives of a forced cell -/

/-- Branches of a forced cell that share one environment, with any labels. -/
theorem branchInner_rel {φ : List CellId} (m : MMachine) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (ρs : List (Val Nat)) (ρs' : MEnv)
    (hρ : EnvRel φ ρs ρs') :
    ∀ (alts : List (MRule × Comp)) (i : Nat),
      List.Forall₂ (BranchRel φ (markWorld m.world c rec)) (alts.map fun a => (a.2, ρs))
        (branchInner m { m.world with nextEvaluator := m.world.nextEvaluator + 1 } c rec
          m.world.nextEvaluator i (alts.map fun a => (a.1, enter a.2 ρs'))) := by
  intro alts
  induction alts with
  | nil => intro i; exact .nil
  | cons a as ih =>
      intro i
      exact .cons ⟨rfl, rfl, by simp [markWorld, recorded, World.record, World.fork, World.setKnownCache], ρs', hρ, rfl⟩ (ih (i + 1))

/-- The first-level alternatives of a computation: either there is none, and the
specification fails, or they are bodies sharing one environment and the
specification's alternatives judgment for them yields the computation's
judgment. -/
theorem cell_alternatives (σ : Store) {φ : List CellId} {ρ : List (Val Nat)} {ρ' : MEnv}
    (hρ : EnvRel φ ρ ρ') (M : Comp) :
    (alternatives P (M, ρ') = [] ∧ Derives P (.eval σ ρ M) [(.fail, σ)]) ∨
    ∃ (alts : List (MRule × Comp)) (ρs : List (Val Nat)) (ρs' : MEnv), alts ≠ [] ∧
      EnvRel φ ρs ρs' ∧ alternatives P (M, ρ') = alts.map (fun a => (a.1, enter a.2 ρs')) ∧
      ∀ L, Derives P (.alts σ (alts.map fun a => (a.2, ρs))) L → Derives P (.eval σ ρ M) L := by
  have single : ∀ M', alternatives P (M', ρ') = [(.builtin, enter M' ρ')] →
      ∃ (alts : List (MRule × Comp)) (ρs : List (Val Nat)) (ρs' : MEnv), alts ≠ [] ∧
        EnvRel φ ρs ρs' ∧ alternatives P (M', ρ') = alts.map (fun a => (a.1, enter a.2 ρs')) ∧
        ∀ L, Derives P (.alts σ (alts.map fun a => (a.2, ρs))) L →
          Derives P (.eval σ ρ M') L := by
    intro M' hM'
    refine ⟨[(.builtin, M')], ρ, ρ', by simp, hρ, by rw [hM']; rfl, fun L h => ?_⟩
    simp only [List.map_cons, List.map_nil] at h
    cases h with
    | altsCons h₁ h₂ => cases h₂; simpa using h₁
  cases M with
  | ret v => exact Or.inr (single _ rfl)
  | seq a b => exact Or.inr (single _ rfl)
  | need a b => exact Or.inr (single _ rfl)
  | delay a b => exact Or.inr (single _ rfl)
  | force v => exact Or.inr (single _ rfl)
  | caseCon v c k hit miss => exact Or.inr (single _ rfl)
  | caseApp v hit miss => exact Or.inr (single _ rfl)
  | fail => exact Or.inr (single _ rfl)
  | emit e a => exact Or.inr (single _ rfl)
  | quote a => exact Or.inr (single _ rfl)
  | run v => exact Or.inr (single _ rfl)
  | prim op args => exact Or.inr (single _ rfl)
  | choose a b =>
      refine Or.inr ⟨[(.left, a), (.right, b)], ρ, ρ', by simp, hρ, rfl, fun L h => ?_⟩
      simp only [List.map_cons, List.map_nil] at h
      cases h with
      | altsCons h₁ h₂ =>
          cases h₂ with
          | altsCons h₂ h₃ => cases h₃; simpa using Derives.choose h₁ h₂
  | call f args =>
      by_cases hc : candidates P f args.length = []
      · exact Or.inl ⟨by simp [alternatives, hc], .callNone hc⟩
      · refine Or.inr ⟨(candidates P f args.length).map (fun r => (MRule.equation, r.body)),
          args.map (·.eval ρ), args.map (·.eval ρ'), by simpa using hc, hρ.map_eval args,
          by simp [alternatives, List.map_map, Function.comp_def], fun L h => ?_⟩
        refine .call hc ?_
        simpa [List.map_map, Function.comp_def] using h
  | callRule i args =>
      cases hr : P[i]? with
      | none => exact Or.inl ⟨by simp [alternatives, hr], .callRuleNone (by simp [hr])⟩
      | some r =>
          by_cases ha : r.arity = args.length
          · refine Or.inr ⟨[(.equation, r.body)], args.map (·.eval ρ), args.map (·.eval ρ'),
              by simp, hρ.map_eval args, by simp [alternatives, hr, ha], fun L h => ?_⟩
            simp only [List.map_cons, List.map_nil] at h
            cases h with
            | altsCons h₁ h₂ => cases h₂; simpa using Derives.callRule hr ha h₁
          · exact Or.inl ⟨by simp [alternatives, hr, ha],
              .callRuleNone (fun r' hr' => by rw [hr] at hr'; cases hr'; exact ha)⟩

/-- Completed runs of the branches of a forced cell give the alternatives
judgment. -/
theorem bwd_alts {n : Nat} (hE : ∀ k < n, BwdEval P k) {σ : Store} {φ : List CellId}
    {w : MWorld} (hcorr : Corr φ σ w) :
    ∀ {bs : List (Comp × List (Val Nat))} {ms : List MMachine},
      List.Forall₂ (BranchRel φ w) bs ms →
      ∀ {k : Nat} {leaves : List MMachine}, k < n → Returns (machineSpec P) [] k ms leaves →
        ∃ L, Derives P (.alts σ bs) L := by
  intro bs ms hrel
  induction hrel with
  | nil => intro _ _ _ _; exact ⟨[], .altsNil⟩
  | @cons b x bs xs hx _ ih =>
      intro k leaves hk h
      obtain ⟨k₁, k₂, l₁, l₂, hkk, -, h₁, h₂⟩ := h.split [x] xs rfl
      obtain ⟨hheap, hnext, hevents, ρ', hρ, hcx⟩ := hx
      obtain ⟨M, ρb⟩ := b
      obtain ⟨L₁, hL₁⟩ := hE k₁ (by omega) M σ ρb φ ρ' x l₁ (hcorr.of_heap_eq hheap hnext hevents) hρ hcx h₁
      obtain ⟨L₂, hL₂⟩ := ih (by omega) h₂
      exact ⟨L₁ ++ L₂, .altsCons hL₁ hL₂⟩

/-! ## The cases of the induction -/

theorem bwd_cell (n : Nat) (hE : ∀ k < n, BwdEval P k) : BwdCell P n := by
  intro σ ρ M φ ρ' m c rec leaves hc hl hs horig hρ hcorr h
  rcases cell_alternatives P σ hρ M with ⟨-, hd⟩ | ⟨alts, ρs, ρs', hne, hρs, halts, hconv⟩
  · exact ⟨_, hd⟩
  · obtain ⟨a, as, hcons⟩ : ∃ a as, alts.map (fun a => (a.1, enter a.2 ρs')) = a :: as := by
      cases alts with
      | nil => exact absurd rfl hne
      | cons a as => exact ⟨_, _, rfl⟩
    have halts' : alternatives P rec.origin = a :: as := by rw [horig, halts, hcons]
    have hstep := step_force_suspended P m c [] hc rec hl hs a as halts'
    rw [branchAlternatives_eq, ← hcons] at hstep
    obtain ⟨n', hn, h'⟩ := h.singleton_step (force_not_returned hc)
    rw [hstep] at h'
    obtain ⟨n₁, n₂, inner, hn', h₁, -⟩ :=
      (seq_iff (rest := []) (f := .commit c m.world.nextEvaluator)).mp h'
    obtain ⟨L, hL⟩ := bwd_alts P hE hcorr (branchInner_rel m c rec ρs ρs' hρs alts 0)
      (by omega) h₁
    exact ⟨L, hconv L hL⟩

/-- Resampling a cell, inverted: the run of a fresh copy of the cell's origin
and the indirections after it. -/
theorem resample_inv {σ : Store} {ℓ : Nat} {s : Suspension} {φ : List CellId} {c : CellId}
    {m₀ : MMachine} {n : Nat} {leaves : List MMachine}
    (hC : ∀ k < n, BwdCell P k) (hFo : ∀ k < n, BwdFollow P k)
    (hφ : φ[ℓ]? = some c) (hs : σ.cells[ℓ]? = some s) (hcorr : Corr φ σ m₀.world)
    (hc : m₀.control = .run (.resample c .resampleAlloc) [])
    (h : Returns (machineSpec P) [] n [m₀] leaves) :
    ∃ L₁ L, Derives P (.eval σ s.env s.code) L₁ ∧ Derives P (.followK L₁) L := by
  obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
  rw [hφ] at hc₀; cases hc₀
  obtain ⟨w₁, ha⟩ := hcorr.allocate recC.origin (c.generation + 1)
  obtain ⟨hnew, -, -, -⟩ := allocate_heap ha
  have hs₁ := step_resample P m₀ c .resampleAlloc [] hc recC hlC w₁ _ ha
  set c' := m₀.world.freshCell (c.generation + 1)
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
  have horig : recC.origin = (s.code, recC.origin.2) := by rw [← hrC.code]
  obtain ⟨n₁, rfl, h₁⟩ := returns_single_inv P hs₁ (run_not_returned hc) h
  obtain ⟨n₂, rfl, h₂⟩ := returns_single_inv P hs₂ (run_not_returned hc₁) h₁
  rw [heq] at h₂
  obtain ⟨k₁, k₂, inner, hk, hr₁, hr₂⟩ := returns_frame_inv P h₂
  have hcorrM : Corr φ σ (markWorld m₂.world c' ⟨recC.origin, .suspended⟩) :=
    hcorr₁.mark_private hcnot hnew
  obtain ⟨L₁, hL₁⟩ := hC k₁ (by omega) σ s.env s.code φ recC.origin.2 m₂ c'
    ⟨recC.origin, .suspended⟩ inner rfl hnew rfl horig hrC.env hcorrM hr₁
  have hrel := inner_related P (m := m₂) (mode := .carrier) hL₁ rfl hnew rfl horig hrC.env
    hcorrM hcnot hr₁
  have hrel₁ : List.Forall₂ (ResRel φ m₂.world []) L₁ inner := by simpa [Mode.apply] using hrel
  obtain ⟨L, hL⟩ := hFo k₂ (by omega) L₁ φ _ _ leaves
    (ResRel.forall₂_below [.resume .forceRet] hrel₁) hr₂
  exact ⟨L₁, L, hL₁, hL⟩

theorem bwd_force (n : Nat) (hF : ∀ k < n, BwdForce P k) (hC : ∀ k < n, BwdCell P k)
    (hFo : ∀ k < n, BwdFollow P k) : BwdForce P n := by
  intro σ v φ v' m leaves hcorr hv hc h
  cases hv with
  | sym c => exact ⟨_, .forceWhnf rfl⟩
  | app _ _ => exact ⟨_, .forceWhnf rfl⟩
  | code _ => exact ⟨_, .forceWhnf rfl⟩
  | @thunk ℓ c hφ =>
      obtain ⟨s, hs⟩ := corr_cell hcorr hφ
      obtain ⟨L₁, L, hL₁, hL⟩ := resample_inv P hC hFo hφ hs hcorr hc h
      exact ⟨L, .forceThunk hs hL₁ hL⟩
  | @need ℓ c hφ =>
      obtain ⟨s, hs⟩ := corr_cell hcorr hφ
      obtain ⟨c₀, recC, hc₀, hlC, hrC⟩ := hcorr.cells ℓ s hs
      rw [hφ] at hc₀; cases hc₀
      have hc₁ : m.control = .run (.demand c .forceRet) [] := hc
      have hmemo := hrC.memo
      generalize hk : s.memo = memo at hmemo
      generalize hcache : recC.cache = cache at hmemo
      cases hmemo with
      | evaluating owner => exact ⟨_, .forceBlackhole hs hk⟩
      | @done w w' hw =>
          have hs₁ := step_demand P m c .forceRet [] hc₁
          set m₁ := finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0
          have hs₂ := step_force_value P m₁ c _ rfl recC hlC w' hcache
          set m₂ := finished m₁ (recorded m₁.world (.observe c (.value w')))
            (.returned (.value w') (.resume .forceRet :: [])) 1 0 1 0
          have hs₃ := step_returned_resume P m₂ (.value w') .forceRet [] rfl
          obtain ⟨n₁, rfl, h₁⟩ := returns_single_inv P hs₁ (run_not_returned hc₁) h
          obtain ⟨n₂, rfl, h₂⟩ := returns_single_inv P hs₂ (force_not_returned rfl) h₁
          obtain ⟨n₃, rfl, h₃⟩ := returns_single_inv P hs₃ (returned_cons_not_returned rfl) h₂
          obtain ⟨L, hL⟩ := hF n₃ (by omega) σ w φ w'
            (finished m₂ m₂.world (.run (afterDemand .forceRet (.value w')) []) 0 0 0 0) leaves
            (hcorr.of_heap_eq rfl rfl (by simp [m₂, m₁, recorded, World.record])) hw rfl h₃
          exact ⟨L, .forceDone hs hk hL⟩
      | pending =>
          have hs₁ := step_demand P m c .forceRet [] hc₁
          set wk := (finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0).work
          set m₁ : MMachine := ⟨m.world, .force c [], wk⟩
          have heq : finished m m.world (.force c (.resume .forceRet :: [])) 0 0 0 0 =
              below [.resume .forceRet] m₁ := rfl
          obtain ⟨n', rfl, h'⟩ := returns_single_inv P hs₁ (run_not_returned hc₁) h
          rw [heq] at h'
          obtain ⟨n₁, n₂, inner, hn, h₁, h₂⟩ := returns_frame_inv P h'
          have horig : recC.origin = (s.code, recC.origin.2) := by rw [← hrC.code]
          have hsM : (σ.setMemo ℓ .evaluating).cells[ℓ]? =
              some { s with memo := .evaluating } := by
            simp [Store.setMemo, hs]
          have hcorrM := hcorr.mark_named hφ hs hrC
          obtain ⟨L₁, hL₁⟩ := hC n₁ (by omega) (σ.setMemo ℓ .evaluating) s.env s.code φ
            recC.origin.2 m₁ c recC inner rfl hlC hcache horig hrC.env hcorrM h₁
          have hrel := inner_related P (m := m₁) (mode := .named ℓ) hL₁ rfl hlC hcache horig
            hrC.env hcorrM ⟨hφ, _, hsM, rfl⟩ h₁
          rw [commitResult_map] at hrel
          obtain ⟨L, hL⟩ := hFo n₂ (by omega) (L₁.map (commitResult ℓ)) φ _ _ leaves
            (ResRel.forall₂_below [.resume .forceRet] hrel) h₂
          exact ⟨L, .forcePending hs hk hL₁ (commitK_of_followK P ℓ L₁ L hL)⟩

/-- A computation entered through a carrier cell demanded by `callRet`. -/
theorem bwd_via_carrier {n : Nat} (hC : ∀ k < n, BwdCell P k) {M : Comp} {σ : Store}
    {ρ : List (Val Nat)} {φ : List CellId} {ρ' : MEnv} {m₀ : MMachine} {leaves : List MMachine}
    (hc : m₀.control = .run (.alloc (M, ρ') .callAlloc) []) (hcorr : Corr φ σ m₀.world)
    (hρ : EnvRel φ ρ ρ') (h : Returns (machineSpec P) [] n [m₀] leaves) :
    ∃ L, Derives P (.eval σ ρ M) L := by
  obtain ⟨w₁, c, work, n', rfl, hcnot, hnew, hcorr₁, h'⟩ :=
    carrier_prefix_inv P (k := .callRet) hc (fun _ => rfl) hcorr h
  obtain ⟨n₁, n₂, inner, hn, h₁, -⟩ := returns_frame_inv P h'
  exact hC n₁ (by omega) σ ρ M φ ρ' ⟨w₁, .force c [], work⟩ c ⟨(M, ρ'), .suspended⟩ inner rfl
    hnew rfl rfl hρ (hcorr₁.mark_private hcnot hnew) h₁

theorem bwd_eval (n : Nat) (hForce : BwdForce P n) (hE : ∀ k < n, BwdEval P k)
    (hC : ∀ k < n, BwdCell P k) (hS : ∀ k < n, BwdSeqK P k) (hFo : ∀ k < n, BwdFollow P k) :
    BwdEval P n := by
  intro M
  induction M with
  | ret v =>
      intro σ ρ φ ρ' m leaves _ _ _ _
      exact ⟨_, .ret⟩
  | seq a b _ _ =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      have hc' : m₀.control = .run (.alloc (a, ρ') (.seqAlloc b ρ')) [] := hc
      obtain ⟨w₁, c, work, n', rfl, hcnot, hnew, hcorr₁, h'⟩ :=
        carrier_prefix_inv P (k := .seqRet b ρ') hc' (fun _ => rfl) hcorr h
      obtain ⟨n₁, n₂, inner, hn, h₁, h₂⟩ := returns_frame_inv P h'
      have hcorrM := hcorr₁.mark_private hcnot hnew
      obtain ⟨L₁, hL₁⟩ := hC n₁ (by omega) σ ρ a φ ρ' ⟨w₁, .force c [], work⟩ c
        ⟨(a, ρ'), .suspended⟩ inner rfl hnew rfl rfl hρ hcorrM h₁
      have hrel := inner_related P (m := ⟨w₁, .force c [], work⟩) (mode := .carrier) hL₁ rfl
        hnew rfl rfl hρ hcorrM hcnot h₁
      have hrel₁ : List.Forall₂ (ResRel φ w₁ []) L₁ inner := by simpa [Mode.apply] using hrel
      obtain ⟨L, hL⟩ := hS n₂ (by omega) b ρ L₁ φ w₁ ρ' _ leaves hρ
        (ResRel.forall₂_below [.resume (.seqRet b ρ')] hrel₁) h₂
      exact ⟨L, .seq hL₁ hL⟩
  | need a b _ _ =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      have hc' : m₀.control = .run (.alloc (a, ρ') (.needAlloc b ρ')) [] := hc
      obtain ⟨w₁, ha⟩ := hcorr.allocate (a, ρ') 0
      have hs := step_alloc P m₀ (a, ρ') (.needAlloc b ρ') [] hc' w₁ _ ha
      have hcorr₁ : Corr (φ ++ [m₀.world.freshCell 0]) (σ.alloc a ρ) w₁ :=
        hcorr.alloc_cell hρ ha
      have hρ₁ : EnvRel (φ ++ [m₀.world.freshCell 0]) (.need σ.cells.length :: ρ)
          (.need (m₀.world.freshCell 0) :: ρ') := by
        rw [← hcorr.length]
        exact .cons (.need (by simp)) (hρ.mono (List.prefix_append _ _))
      obtain ⟨n', rfl, h'⟩ := returns_single_inv P hs (run_not_returned hc') h
      obtain ⟨L, hL⟩ := hE n' (by omega) b (σ.alloc a ρ) (.need σ.cells.length :: ρ)
        (φ ++ [m₀.world.freshCell 0]) (.need (m₀.world.freshCell 0) :: ρ')
        (finished m₀ w₁ (.run (afterAllocation (.needAlloc b ρ') (m₀.world.freshCell 0)) [])
          1 1 1 1) leaves hcorr₁ hρ₁ rfl h'
      exact ⟨L, .need hL⟩
  | delay a b _ _ =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      have hc' : m₀.control = .run (.alloc (a, ρ') (.delayAlloc b ρ')) [] := hc
      obtain ⟨w₁, ha⟩ := hcorr.allocate (a, ρ') 0
      have hs := step_alloc P m₀ (a, ρ') (.delayAlloc b ρ') [] hc' w₁ _ ha
      have hcorr₁ : Corr (φ ++ [m₀.world.freshCell 0]) (σ.alloc a ρ) w₁ :=
        hcorr.alloc_cell hρ ha
      have hρ₁ : EnvRel (φ ++ [m₀.world.freshCell 0]) (.thunk σ.cells.length :: ρ)
          (.thunk (m₀.world.freshCell 0) :: ρ') := by
        rw [← hcorr.length]
        exact .cons (.thunk (by simp)) (hρ.mono (List.prefix_append _ _))
      obtain ⟨n', rfl, h'⟩ := returns_single_inv P hs (run_not_returned hc') h
      obtain ⟨L, hL⟩ := hE n' (by omega) b (σ.alloc a ρ) (.thunk σ.cells.length :: ρ)
        (φ ++ [m₀.world.freshCell 0]) (.thunk (m₀.world.freshCell 0) :: ρ')
        (finished m₀ w₁ (.run (afterAllocation (.delayAlloc b ρ') (m₀.world.freshCell 0)) [])
          1 1 1 1) leaves hcorr₁ hρ₁ rfl h'
      exact ⟨L, .delay hL⟩
  | force v =>
      intro σ ρ φ ρ' m leaves hcorr hρ hc h
      obtain ⟨L, hL⟩ := hForce σ (v.eval ρ) φ (v.eval ρ') m leaves hcorr (VExp.eval_rel hρ v) hc h
      exact ⟨L, .force hL⟩
  | caseCon v c k hit miss ihHit ihMiss =>
      intro σ ρ φ ρ' m leaves hcorr hρ hc h
      rcases (VExp.eval_rel hρ v).matchCon c k with ⟨h1, h2⟩ | ⟨as, as', h1, h2, hargs⟩
      · obtain ⟨L, hL⟩ := ihMiss σ ρ φ ρ' m leaves hcorr hρ (by rw [hc]; simp [enter, h2]) h
        exact ⟨L, .caseConMiss h1 hL⟩
      · obtain ⟨L, hL⟩ := ihHit σ (as ++ ρ) φ (as' ++ ρ') m leaves hcorr
          (List.rel_append hargs hρ) (by rw [hc]; simp [enter, h2]) h
        exact ⟨L, .caseConHit h1 hL⟩
  | caseApp v hit miss ihHit ihMiss =>
      intro σ ρ φ ρ' m leaves hcorr hρ hc h
      rcases (VExp.eval_rel hρ v).matchApp with ⟨h1, h2⟩ | ⟨f₀, x₀, f', x', h1, h2, hf, hx⟩
      · obtain ⟨L, hL⟩ := ihMiss σ ρ φ ρ' m leaves hcorr hρ (by rw [hc]; simp [enter, h2]) h
        exact ⟨L, .caseAppMiss h1 hL⟩
      · obtain ⟨L, hL⟩ := ihHit σ (f₀ :: x₀ :: ρ) φ (f' :: x' :: ρ') m leaves hcorr
          (.cons hf (.cons hx hρ)) (by rw [hc]; simp [enter, h2]) h
        exact ⟨L, .caseAppHit h1 hL⟩
  | call f args =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      exact bwd_via_carrier P hC hc hcorr hρ h
  | callRule i args =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      exact bwd_via_carrier P hC hc hcorr hρ h
  | choose a b _ _ =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      exact bwd_via_carrier P hC hc hcorr hρ h
  | fail =>
      intro σ ρ φ ρ' m leaves _ _ _ _
      exact ⟨_, .fail⟩
  | emit e a _ =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      have hc' : m₀.control = .run (.emit e (enter a ρ')) [] := hc
      have hs := step_emit P m₀ e (enter a ρ') [] hc'
      obtain ⟨n', rfl, h'⟩ := returns_single_inv P hs (run_not_returned hc') h
      obtain ⟨L, hL⟩ := hE n' (by omega) a (σ.emit e) ρ φ ρ'
        (finished m₀ (recorded m₀.world (.effect e)) (.run (enter a ρ') []) 0 0 1 0) leaves
        (hcorr.trace e) hρ rfl h'
      exact ⟨L, .emit hL⟩
  | quote a _ =>
      intro σ ρ φ ρ' m leaves _ _ _ _
      exact ⟨_, .quote⟩
  | run v =>
      intro σ ρ φ ρ' m₀ leaves hcorr hρ hc h
      by_cases hv : ∃ ℓ, v.eval ρ = .code ℓ
      · obtain ⟨ℓ, hv⟩ := hv
        have hvr := VExp.eval_rel hρ v
        rw [hv] at hvr
        generalize hw' : v.eval ρ' = w' at hvr
        cases hvr with
        | @code _ c hφ =>
            have hc' : m₀.control = .run (.resample c .resampleAlloc) [] := by
              rw [hc]; simp [enter, hw', runLocal]
            obtain ⟨s, hs⟩ := corr_cell hcorr hφ
            obtain ⟨L₁, L, hL₁, hL⟩ := resample_inv P hC hFo hφ hs hcorr hc' h
            exact ⟨L, .runCode hv hs hL₁ hL⟩
      · exact ⟨_, .runOther fun ℓ e => hv ⟨ℓ, e⟩⟩
  | prim op args =>
      intro σ ρ φ ρ' m leaves _ _ _ _
      exact ⟨_, .prim⟩

theorem bwd_seqK (n : Nat) (hE : ∀ k < n, BwdEval P k) : BwdSeqK P n := by
  intro body ρ rs φ w ρ' ms leaves hρ hrel h
  suffices H : ∀ k, k ≤ n → ∀ leaves, Returns (machineSpec P) [] k ms leaves →
      ∃ L, Derives P (.seqK body ρ rs) L from H n le_rfl leaves h
  clear h
  clear leaves
  induction hrel with
  | nil => intro _ _ _ _; exact ⟨[], .seqKNil⟩
  | @cons r x rs' xs hr _ ih =>
      intro k hk leaves h
      obtain ⟨k₁, k₂, l₁, l₂, hkk, -, h₁, h₂⟩ := h.split [x] xs rfl
      obtain ⟨L₂, hL₂⟩ := ih k₂ (by omega) l₂ h₂
      obtain ⟨o₀, σ₀⟩ := r
      obtain ⟨φ', hp, -, hcx, -, o, ho, hor⟩ := hr
      cases hor with
      | @ok v v' hv =>
          have hs := step_returned_resume P x (.value v') (.seqRet body ρ') [] ho
          obtain ⟨k₁', rfl, h₁'⟩ := returns_single_inv P hs (returned_cons_not_returned ho) h₁
          obtain ⟨L₁, hL₁⟩ := hE k₁' (by omega) body σ₀ (v :: ρ) φ' (v' :: ρ')
            (finished x x.world (.run (afterDemand (.seqRet body ρ') (.value v')) []) 0 0 0 0)
            l₁ hcx (.cons hv (hρ.mono hp)) rfl h₁'
          exact ⟨L₁ ++ L₂, .seqKOk hL₁ hL₂⟩
      | failDomain => exact ⟨_, .seqKStop rfl hL₂⟩
      | failNoRule _ => exact ⟨_, .seqKStop rfl hL₂⟩
      | blackhole _ => exact ⟨_, .seqKStop rfl hL₂⟩

theorem bwd_follow (n : Nat) (hF : ∀ k < n, BwdForce P k) : BwdFollow P n := by
  intro rs φ w ms leaves hrel h
  suffices H : ∀ k, k ≤ n → ∀ leaves, Returns (machineSpec P) [] k ms leaves →
      ∃ L, Derives P (.followK rs) L from H n le_rfl leaves h
  clear h
  clear leaves
  induction hrel with
  | nil => intro _ _ _ _; exact ⟨[], .followNil⟩
  | @cons r x rs' xs hr _ ih =>
      intro k hk leaves h
      obtain ⟨k₁, k₂, l₁, l₂, hkk, -, h₁, h₂⟩ := h.split [x] xs rfl
      obtain ⟨L₂, hL₂⟩ := ih k₂ (by omega) l₂ h₂
      obtain ⟨o₀, σ₀⟩ := r
      obtain ⟨φ', -, -, hcx, -, o, ho, hor⟩ := hr
      cases hor with
      | @ok v v' hv =>
          have hs := step_returned_resume P x (.value v') .forceRet [] ho
          obtain ⟨k₁', rfl, h₁'⟩ := returns_single_inv P hs (returned_cons_not_returned ho) h₁
          obtain ⟨L₁, hL₁⟩ := hF k₁' (by omega) σ₀ v φ' v'
            (finished x x.world (.run (afterDemand .forceRet (.value v')) []) 0 0 0 0)
            l₁ hcx hv rfl h₁'
          exact ⟨L₁ ++ L₂, .followOk hL₁ hL₂⟩
      | failDomain => exact ⟨_, .followStop rfl hL₂⟩
      | failNoRule _ => exact ⟨_, .followStop rfl hL₂⟩
      | blackhole _ => exact ⟨_, .followStop rfl hL₂⟩

/-! ## The backward theorem -/

theorem backward_all (n : Nat) :
    BwdEval P n ∧ BwdCell P n ∧ BwdForce P n ∧ BwdSeqK P n ∧ BwdFollow P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      have hE : ∀ k < n, BwdEval P k := fun k hk => (ih k hk).1
      have hC : ∀ k < n, BwdCell P k := fun k hk => (ih k hk).2.1
      have hF : ∀ k < n, BwdForce P k := fun k hk => (ih k hk).2.2.1
      have hS : ∀ k < n, BwdSeqK P k := fun k hk => (ih k hk).2.2.2.1
      have hFo : ∀ k < n, BwdFollow P k := fun k hk => (ih k hk).2.2.2.2
      have hForce := bwd_force P n hF hC hFo
      exact ⟨bwd_eval P n hForce hE hC hS hFo, bwd_cell P n hE, hForce, bwd_seqK P n hE,
        bwd_follow P n hF⟩

/-- **Backward adequacy.** A completed run of the reference machine from a
configuration related to `(σ, ρ, M)` is specified: the natural semantics derives
a result list, related to the run's leaves one by one. -/
theorem backward_eval {σ : Store} {ρ : List (Val Nat)} {M : Comp} {φ : List CellId}
    {ρ' : MEnv} {m : MMachine} {n : Nat} {leaves : List MMachine}
    (hcorr : Corr φ σ m.world) (hρ : EnvRel φ ρ ρ') (hc : m.control = .run (enter M ρ') [])
    (h : Returns (machineSpec P) [] n [m] leaves) :
    ∃ L, Derives P (.eval σ ρ M) L ∧ List.Forall₂ (ResRel φ m.world []) L leaves := by
  obtain ⟨L, hL⟩ := (backward_all P n).1 M σ ρ φ ρ' m leaves hcorr hρ hc h
  obtain ⟨n', leaves', h', hrel⟩ := (forward P _ _ hL).1 φ ρ' m hcorr hρ hc
  obtain ⟨-, rfl⟩ := Returns.deterministic h' h
  exact ⟨L, hL, hrel⟩

/-- **Backward adequacy for observations.** -/
theorem observe_backward {P : Program} {M : Comp} {n : Nat} {leaves : List MMachine}
    (h : Returns (machineSpec (observed P)) [] n [initialMachine (observe M)] leaves) :
    ∃ L, Observes P M L ∧ List.Forall₂ (ResRel [] initialWorld []) L leaves :=
  backward_eval (observed P) corr_initial .nil rfl h

/-! ## Answers -/

theorem leafOutcomes_rel {φ : List CellId} {w : MWorld} {L : List Result}
    {leaves : List MMachine} (h : List.Forall₂ (ResRel φ w []) L leaves) :
    List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ', OutRel φ' r.1 o) L
      (leaves.filterMap leafOutcome) := by
  induction h with
  | nil => exact .nil
  | @cons r l L' ls hr _ ih =>
      obtain ⟨φ', _, _, _, _, o, ho, hor⟩ := hr
      have : leafOutcome l = some o := by simp [leafOutcome, ho]
      simp only [List.filterMap_cons, this]
      exact .cons ⟨φ', hor⟩ ih

theorem answers_of_frontier {P : Program} {m : MMachine} {n : Nat} {leaves : List MMachine}
    (h : Returns (machineSpec P) [] n [m] leaves) {fuel : Nat}
    (hfr : runFrontier (machineSpec P) fuel [m] = leaves.map haltOf) :
    answers (machineSpec P) fuel m = leaves.filterMap leafOutcome := by
  unfold answers
  rw [hfr, List.filterMap_map]
  apply List.filterMap_congr
  intro l hl
  obtain ⟨o, ho⟩ := h.leaves_returned l hl
  simp [Function.comp_apply, haltedOutcome_haltOf l o ho, leafOutcome, ho]

/-- The machine's frontier for the observation of `M` has halted at `fuel`. -/
def Halted (P : Program) (M : Comp) (fuel : Nat) : Prop :=
  ∀ x ∈ runFrontier (machineSpec (observed P)) fuel [initialMachine (observe M)],
    isHalted x = true

/-- **Backward adequacy for answers.** If the machine's frontier has halted, the
specification observes an outcome list, and the machine's answers are those
outcomes, one by one, in order and with multiplicity. -/
theorem answers_backward {P : Program} {M : Comp} {N : Nat} (hN : Halted P M N) :
    ∃ L, Observes P M L ∧
      List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
        (machineAnswers P N M) := by
  unfold Halted at hN
  rw [NeedFrontierLaws.runFrontier_eq_flatMap] at hN
  obtain ⟨n, leaves, h⟩ := returns_of_frontier_halted N [initialMachine (observe M)]
    (by intro m hm; simp only [List.mem_singleton] at hm; subst hm; rfl) hN
  obtain ⟨L, hL, hrel⟩ := observe_backward h
  refine ⟨L, hL, ?_⟩
  have hfr : runFrontier (machineSpec (observed P)) N [initialMachine (observe M)] =
      leaves.map haltOf := by
    rw [NeedFrontierLaws.runFrontier_eq_flatMap]
    exact frontier_eq_of_halted h N hN
  unfold machineAnswers
  rw [answers_of_frontier h hfr]
  exact leafOutcomes_rel hrel

/-- Every halted answer-and-effect observation is specified, in order and
with multiplicity. The store correspondence relates the events of each leaf. -/
theorem observations_backward {P : Program} {M : Comp} {N : Nat}
    (hN : Halted P M N) :
    ∃ L, Observes P M L ∧
      List.Forall₂ ObservationRel L
        (machineObservations P N M) := by
  unfold Halted at hN
  rw [NeedFrontierLaws.runFrontier_eq_flatMap] at hN
  obtain ⟨n, leaves, h⟩ := returns_of_frontier_halted N [initialMachine (observe M)]
    (by intro m hm; simp only [List.mem_singleton] at hm; subst hm; rfl) hN
  obtain ⟨L, hL, hrel⟩ := observe_backward h
  refine ⟨L, hL, ?_⟩
  have hfr : runFrontier (machineSpec (observed P)) N [initialMachine (observe M)] =
      leaves.map haltOf := by
    rw [NeedFrontierLaws.runFrontier_eq_flatMap]
    exact frontier_eq_of_halted h N hN
  unfold machineObservations
  rw [observations_of_frontier h hfr]
  exact leafObservations_rel hrel

/-- **Adequacy of the reference machine for call-time choice.**

* Every specified observation is realized: from some fuel on, the machine's
  frontier has halted and its answers are the specified outcomes, one by one.
* Every halted frontier is specified: the specification observes an outcome
  list, and the machine's answers at that fuel are its outcomes, one by one.

Outcomes are related by `OutRel`: values equal up to a renaming of cells, the
specification's failure as the machine's domain failure or no-rule retry, and
its blackhole as the machine's blackhole retry. With `Derives.deterministic`, the
observed list is unique. -/
theorem adequacy (P : Program) (M : Comp) :
    (∀ L, Observes P M L → ∃ N, ∀ fuel, N ≤ fuel → Halted P M fuel ∧
        List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
          (machineAnswers P fuel M)) ∧
    (∀ N, Halted P M N → ∃ L, Observes P M L ∧
        List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
          (machineAnswers P N M)) := by
  refine ⟨fun L hL => ?_, fun N hN => answers_backward hN⟩
  obtain ⟨n, leaves, hrun, hrel⟩ := observe_forward hL
  obtain ⟨N, hN⟩ := frontier_eq_haltOf hrun
  refine ⟨N, fun fuel hfuel => ⟨?_, ?_⟩⟩
  · intro x hx
    rw [NeedFrontierLaws.runFrontier_eq_flatMap, hN fuel hfuel] at hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨o, ho⟩ := hrun.leaves_returned l hl
    exact haltOf_isHalted l o ho
  · have hfr : runFrontier (machineSpec (observed P)) fuel [initialMachine (observe M)] =
        leaves.map haltOf := by
      rw [NeedFrontierLaws.runFrontier_eq_flatMap]
      exact hN fuel hfuel
    unfold machineAnswers
    rw [answers_of_frontier hrun hfr]
    exact leafOutcomes_rel hrel

/-- A specified observation exists exactly when the machine's frontier halts. -/
theorem observes_iff_halts (P : Program) (M : Comp) :
    (∃ L, Observes P M L) ↔ ∃ N, Halted P M N := by
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨N, hN⟩ := (adequacy P M).1 L hL
    exact ⟨N, (hN N le_rfl).1⟩
  · rintro ⟨N, hN⟩
    obtain ⟨L, hL, -⟩ := (adequacy P M).2 N hN
    exact ⟨L, hL⟩

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
