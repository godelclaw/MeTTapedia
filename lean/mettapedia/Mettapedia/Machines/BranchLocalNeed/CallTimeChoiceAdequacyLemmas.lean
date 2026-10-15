import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSteps

/-!
# Lemmas for the adequacy proof

* `Grows w w'`: cells under evaluation in `w` keep their exact records in `w'`,
  and the allocation counter does not decrease.
* `ResRel φ w stk r m`: a specification result `r` and a machine `m` that has
  returned to the stack `stk`. The cell map may have grown to `φ'`, by cells at
  or above `w`'s counter only.
* `Mode`: how a forced cell is committed. A carrier cell (private to the
  machine: it carries a sequencing or call continuation, or a resampled copy)
  leaves the specification's store unchanged; a named cell `ℓ` is the
  specification's cell `ℓ`, whose memo becomes `done` or returns to `pending`.
* `commit_pops`: every returned alternative of a forced cell takes one machine
  step through its update frame.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference NeedReturningRuns

variable (P : Program)

/-! ## Growth of worlds -/

/-- Cells under evaluation keep their records; the counter does not decrease. -/
structure Grows (w w' : MWorld) : Prop where
  keeps : ∀ (c : CellId) (rec : CellRecord (Comp × MEnv) MVal Empty),
    w.heap.lookup c = some rec → (∃ o, rec.cache = .evaluating o) → w'.heap.lookup c = some rec
  next : w.nextCell ≤ w'.nextCell

theorem Grows.refl (w : MWorld) : Grows w w := ⟨fun _ _ h _ => h, le_refl _⟩

theorem Grows.trans {w₁ w₂ w₃ : MWorld} (h₁ : Grows w₁ w₂) (h₂ : Grows w₂ w₃) : Grows w₁ w₃ :=
  ⟨fun c rec h e => h₂.keeps c rec (h₁.keeps c rec h e) e, le_trans h₁.next h₂.next⟩

theorem Grows.of_heap {w w' : MWorld} (heap : w'.heap = w.heap) (next : w.nextCell ≤ w'.nextCell) :
    Grows w w' :=
  ⟨fun _ _ h _ => by rw [heap]; exact h, next⟩

/-- Cells added to `φ` have slots at or above `w`'s counter. -/
def Fresh (φ φ' : List CellId) (w : MWorld) : Prop :=
  ∀ c ∈ φ', c ∉ φ → w.nextCell ≤ c.slot

theorem Fresh.refl (φ : List CellId) (w : MWorld) : Fresh φ φ w := fun _ h n => absurd h n

/-! ## Results and returned machines -/

/-- A specification result and a machine returned to `stk`. -/
def ResRel (φ : List CellId) (w : MWorld) (stk : List (Frame MResume)) (r : Result)
    (m : MMachine) : Prop :=
  ∃ φ', φ <+: φ' ∧ Fresh φ φ' w ∧ Corr φ' r.2 m.world ∧ Grows w m.world ∧
    ∃ o, m.control = .returned o stk ∧ OutRel φ' r.1 o

/-- A successful machine return retains its references in its own resulting
world. The ancestor world in the relation is not a substitute carrier. -/
theorem ResRel.value_references_live {φ : List CellId} {world : MWorld}
    {stack : List (Frame MResume)} {value : Val Nat} {store : Store} {machine : MMachine}
    (related : ResRel φ world stack (.ok value, store) machine) :
    ∃ represented, machine.control = .returned (.value represented) stack ∧
      represented.referencesSatisfy (fun c => ∃ rec, machine.world.heap.lookup c = some rec) := by
  obtain ⟨_, _, _, correspondence, _, outcome, returned, output⟩ := related
  cases output with
  | ok valueRelated =>
      exact ⟨_, returned, correspondence.value_references_live valueRelated⟩

theorem ResRel.weaken {φ φ₁ : List CellId} {w w₁ : MWorld} {stk : List (Frame MResume)}
    {r : Result} {m : MMachine} (h : ResRel φ₁ w₁ stk r m) (hp : φ <+: φ₁) (hf : Fresh φ φ₁ w)
    (hg : Grows w w₁) : ResRel φ w stk r m := by
  obtain ⟨φ', hp', hf', hc, hgr, o, ho, hor⟩ := h
  refine ⟨φ', hp.trans hp', ?_, hc, hg.trans hgr, o, ho, hor⟩
  intro c hc' hn
  by_cases h₁ : c ∈ φ₁
  · exact hf c h₁ hn
  · exact le_trans hg.next (hf' c hc' h₁)

theorem ResRel.weaken_same {φ : List CellId} {w w₁ : MWorld} {stk : List (Frame MResume)}
    {r : Result} {m : MMachine} (h : ResRel φ w₁ stk r m) (hg : Grows w w₁) :
    ResRel φ w stk r m :=
  h.weaken (List.prefix_refl φ) (Fresh.refl φ w) hg

theorem ResRel.base {φ : List CellId} {w w₁ : MWorld} {stk : List (Frame MResume)}
    {r : Result} {m : MMachine} (h : ResRel φ w₁ stk r m) (heap : w₁.heap = w.heap)
    (next : w₁.nextCell = w.nextCell) : ResRel φ w stk r m := by
  obtain ⟨φ', hp, hf, hc, hg, o, ho, hor⟩ := h
  refine ⟨φ', hp, ?_, hc, ?_, o, ho, hor⟩
  · intro c hc' hn; rw [← next]; exact hf c hc' hn
  · exact (Grows.of_heap heap (le_of_eq next.symm)).trans hg

theorem ResRel.below {φ : List CellId} {w : MWorld} {r : Result} {m : MMachine}
    (stk : List (Frame MResume)) (h : ResRel φ w [] r m) : ResRel φ w stk r (below stk m) := by
  obtain ⟨φ', hp, hf, hc, hg, o, ho, hor⟩ := h
  exact ⟨φ', hp, hf, hc, hg, o, by simp [ho, extendControl], hor⟩

theorem ResRel.forall₂_below {φ : List CellId} {w : MWorld} {L : List Result}
    {ms : List MMachine} (stk : List (Frame MResume)) (h : List.Forall₂ (ResRel φ w []) L ms) :
    List.Forall₂ (ResRel φ w stk) L (ms.map (NeedReturningRuns.below stk)) := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hr.below stk) ih

theorem forall₂_weaken {φ φ₁ : List CellId} {w w₁ : MWorld} {stk : List (Frame MResume)}
    {L : List Result} {ms : List MMachine} (h : List.Forall₂ (ResRel φ₁ w₁ stk) L ms)
    (hp : φ <+: φ₁) (hf : Fresh φ φ₁ w) (hg : Grows w w₁) :
    List.Forall₂ (ResRel φ w stk) L ms :=
  h.imp fun _ _ hr => hr.weaken hp hf hg

theorem forall₂_base {φ : List CellId} {w w₁ : MWorld} {stk : List (Frame MResume)}
    {L : List Result} {ms : List MMachine} (h : List.Forall₂ (ResRel φ w₁ stk) L ms)
    (heap : w₁.heap = w.heap) (next : w₁.nextCell = w.nextCell) :
    List.Forall₂ (ResRel φ w stk) L ms :=
  h.imp fun _ _ hr => hr.base heap next

/-! ## Single transitions inside runs -/

theorem returns_step {m m' : MMachine} {n : Nat} {leaves : List MMachine}
    (hs : step (machineSpec P) m = [m']) (hr : ∀ o, m.control ≠ .returned o [])
    (h : Returns (machineSpec P) [] n [m'] leaves) :
    Returns (machineSpec P) [] (n + 1) [m] leaves :=
  Returns.of_step hr (by rw [hs]; simp) (by rw [hs]; exact h)

theorem run_not_returned {m : MMachine} {s : MLocal} {stk : List (Frame MResume)}
    (hc : m.control = .run s stk) : ∀ o, m.control ≠ .returned o [] := by
  intro o h; rw [hc] at h; cases h

theorem force_not_returned {m : MMachine} {c : CellId} {stk : List (Frame MResume)}
    (hc : m.control = .force c stk) : ∀ o, m.control ≠ .returned o [] := by
  intro o h; rw [hc] at h; cases h

theorem returned_cons_not_returned {m : MMachine} {o' : MOutcome} {f : Frame MResume}
    {stk : List (Frame MResume)} (hc : m.control = .returned o' (f :: stk)) :
    ∀ o, m.control ≠ .returned o [] := by
  intro o h; rw [hc] at h; cases h

/-- A local output is one transition to a returned leaf. -/
theorem returns_output {m : MMachine} {o : MOutcome} (hc : m.control = .run (.output o) []) :
    Returns (machineSpec P) [] 1 [m] [finished m m.world (.returned o []) 0 0 0 0] :=
  returns_step P (step_output P m o [] hc) (run_not_returned hc) (Returns.single_leaf o rfl)

/-- An output leaf related to a result in the same world. -/
theorem resRel_output {φ : List CellId} {σ : Store} {m : MMachine} {o : Outcome} {o' : MOutcome}
    (hcorr : Corr φ σ m.world) (hout : OutRel φ o o') :
    ResRel φ m.world [] (o, σ) (finished m m.world (.returned o' []) 0 0 0 0) :=
  ⟨φ, List.prefix_refl φ, Fresh.refl φ _, hcorr, Grows.refl _, o', rfl, hout⟩

/-- A returned machine whose outcome is a retryable fault pops a frame whose
continuation outputs that outcome, in two transitions. -/
theorem returns_pop_output {m : MMachine} {o : MOutcome} {k : MResume}
    (hc : m.control = .returned o [.resume k]) (hk : afterDemand k o = .output o) :
    Returns (machineSpec P) [] 2 [m]
      [finished (finished m m.world (.run (afterDemand k o) []) 0 0 0 0) m.world
        (.returned o []) 0 0 0 0] := by
  have h1 := step_returned_resume P m o k [] hc
  refine returns_step P h1 (returned_cons_not_returned hc) ?_
  exact returns_output P (by simp [hk])

/-! ## Marking a cell under evaluation -/

/-- The world in which a forced cell is under evaluation by the next owner. -/
def markWorld (w : MWorld) (c : CellId) (rec : CellRecord (Comp × MEnv) MVal Empty) : MWorld :=
  { w with heap := w.heap.setKnownCache c rec (.evaluating w.nextEvaluator) }

@[simp] theorem markWorld_nextCell (w : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) : (markWorld w c rec).nextCell = w.nextCell := rfl

theorem markWorld_lookup_same (w : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) :
    (markWorld w c rec).heap.lookup c = some { rec with cache := .evaluating w.nextEvaluator } :=
  Heap.setKnownCache_lookup_same _ _ _ _

theorem markWorld_lookup_other (w : MWorld) {c c' : CellId}
    (rec : CellRecord (Comp × MEnv) MVal Empty) (h : c' ≠ c) :
    (markWorld w c rec).heap.lookup c' = w.heap.lookup c' :=
  Heap.setKnownCache_preserves_other _ _ _ h

theorem Corr.mark_private {φ : List CellId} {σ : Store} {w : MWorld} {c : CellId}
    {rec : CellRecord (Comp × MEnv) MVal Empty} (h : Corr φ σ w) (hc : c ∉ φ)
    (hl : w.heap.lookup c = some rec) : Corr φ σ (markWorld w c rec) :=
  h.set_private hc (fun _ hne => markWorld_lookup_other w rec hne)
    (fun _ _ => ⟨rec, hl⟩) rfl rfl

theorem Corr.mark_named {φ : List CellId} {σ : Store} {w : MWorld} {ℓ : Nat} {c : CellId}
    {s : Suspension} {rec : CellRecord (Comp × MEnv) MVal Empty} (h : Corr φ σ w)
    (hc : φ[ℓ]? = some c) (hs : σ.cells[ℓ]? = some s)
    (hr : SuspRel φ s rec) : Corr φ (σ.setMemo ℓ .evaluating) (markWorld w c rec) :=
  h.set_named hc hs (markWorld_lookup_same w c rec)
    ⟨hr.code, hr.env, .evaluating _⟩ (fun _ hne => markWorld_lookup_other w rec hne) rfl rfl

/-! ## Commit modes -/

/-- How a forced cell is committed in the specification's store. -/
inductive Mode where
  | carrier
  | named (ℓ : Nat)

/-- The specification's commit of a named cell. -/
def commitResult (ℓ : Nat) : Result → Result
  | (.ok v, σ) => (.ok v, σ.setMemo ℓ (.done v))
  | (o, σ) => (o, σ.setMemo ℓ .pending)

def Mode.apply : Mode → Result → Result
  | .carrier, r => r
  | .named ℓ, r => commitResult ℓ r

/-- The side condition of a mode. -/
def Mode.OK (φ : List CellId) (σ : Store) (c : CellId) : Mode → Prop
  | .carrier => c ∉ φ
  | .named ℓ => φ[ℓ]? = some c ∧ ∃ s, σ.cells[ℓ]? = some s ∧ s.memo = .evaluating

theorem Mode.apply_fst (mode : Mode) (r : Result) : (mode.apply r).1 = r.1 := by
  cases mode with
  | carrier => rfl
  | named ℓ =>
      obtain ⟨o, σ⟩ := r
      cases o <;> rfl

theorem commitResult_map (ℓ : Nat) (L : List Result) :
    L.map (Mode.named ℓ).apply = L.map (commitResult ℓ) := rfl

/-- One step through the update frame of a forced cell, from a returned alternative. -/
theorem commit_pop {φ : List CellId} {m : MMachine} {c : CellId}
    {rec : CellRecord (Comp × MEnv) MVal Empty} {mode : Mode} {σM : Store}
    (hl : m.world.heap.lookup c = some rec) (hs : rec.cache = .suspended)
    (hcorr : Corr φ σM (markWorld m.world c rec)) (hmode : mode.OK φ σM c)
    {r : Result} {l : MMachine} (hr : ResRel φ (markWorld m.world c rec) [] r l) :
    ∃ l', step (machineSpec P) (below [.commit c m.world.nextEvaluator] l) = [l'] ∧
      ResRel φ m.world [] (mode.apply r) l' := by
  obtain ⟨o₀, σ'⟩ := r
  obtain ⟨φ', hp, hf, hc, hg, o, ho, hor⟩ := hr
  simp only at hc hor
  set owner := m.world.nextEvaluator
  set recM : CellRecord (Comp × MEnv) MVal Empty := { rec with cache := .evaluating owner }
  have hlM : (markWorld m.world c rec).heap.lookup c = some recM := markWorld_lookup_same _ _ _
  have hll : l.world.heap.lookup c = some recM := hg.keeps c recM hlM ⟨owner, rfl⟩
  have hcb : (below [.commit c owner] l).control = .returned o [.commit c owner] := by
    simp [ho, extendControl]
  have hslot : c.slot < m.world.nextCell := hcorr.slot c recM hlM
  have hgrow : ∀ (w' : MWorld), (∀ c', c' ≠ c → w'.heap.lookup c' = l.world.heap.lookup c') →
      w'.nextCell = l.world.nextCell → Grows m.world w' := by
    intro w' hother hnext
    refine ⟨?_, ?_⟩
    · intro c₀ rec₀ hl₀ he
      have hne : c₀ ≠ c := by
        intro h; subst h; rw [hl] at hl₀; cases hl₀
        obtain ⟨o', ho'⟩ := he; rw [hs] at ho'; cases ho'
      rw [hother c₀ hne]
      apply hg.keeps c₀ rec₀ _ he
      rw [markWorld_lookup_other _ _ hne]; exact hl₀
    · rw [hnext]; exact hg.next
  have hfresh : Fresh φ φ' m.world := hf
  have hnotmem : mode = .carrier → c ∉ φ' := by
    intro hm hmem
    subst hm
    have := hf c hmem hmode
    simp only [markWorld_nextCell] at this
    omega
  -- the named cell, when there is one, is the spec cell `ℓ` of the result store
  have named_cell : ∀ ℓ, mode = .named ℓ → φ'[ℓ]? = some c ∧
      ∃ s, σ'.cells[ℓ]? = some s ∧ SuspRel φ' s recM := by
    intro ℓ hm
    subst hm
    obtain ⟨hφ, _, _, _⟩ := hmode
    have hφ' : φ'[ℓ]? = some c := prefix_getElem? hp hφ
    have hlt : ℓ < σ'.cells.length := by
      rw [← hc.length]; exact (List.getElem?_eq_some_iff.mp hφ').1
    obtain ⟨s, hs'⟩ : ∃ s, σ'.cells[ℓ]? = some s := ⟨σ'.cells[ℓ], List.getElem?_eq_getElem hlt⟩
    obtain ⟨c'', rec'', hc'', hl'', hr''⟩ := hc.cells ℓ s hs'
    rw [hφ'] at hc''; cases hc''
    rw [hll] at hl''; cases hl''
    exact ⟨hφ', s, hs', hr''⟩
  cases o with
  | stableFault e => exact e.elim
  | value v' =>
      refine ⟨_, step_returned_commit_value P _ v' c owner [] hcb recM hll rfl, ?_⟩
      have hother : ∀ c', c' ≠ c →
          (recorded (l.world.setKnownCache c recM (.value v'))
            (.observe c (.value v'))).heap.lookup c' = l.world.heap.lookup c' := by
        intro c' hne
        simp [World.setKnownCache, Heap.setKnownCache_preserves_other _ _ _ hne]
      have hnew : (recorded (l.world.setKnownCache c recM (.value v'))
          (.observe c (.value v'))).heap.lookup c = some { recM with cache := .value v' } := by
        simp [World.setKnownCache]
      cases hor with
      | @ok v _ hv =>
      refine ⟨φ', hp, hfresh, ?_, hgrow _ hother rfl, .value v', rfl, ?_⟩
      · cases mode with
        | carrier =>
            exact hc.set_private (hnotmem rfl) hother (fun _ _ => ⟨recM, hll⟩) rfl
        | named ℓ =>
            obtain ⟨hφ', s, hs', hr''⟩ := named_cell ℓ rfl
            exact hc.set_named hφ' hs' hnew ⟨hr''.code, hr''.env, .done hv⟩ hother rfl
      · rw [Mode.apply_fst]; exact .ok hv
  | retryableFault reason =>
      refine ⟨_, step_returned_commit_retry P _ reason c owner [] hcb recM hll rfl, ?_⟩
      have hother : ∀ c', c' ≠ c →
          (recorded (l.world.setKnownCache c recM .suspended)
            (.retry c reason)).heap.lookup c' = l.world.heap.lookup c' := by
        intro c' hne
        simp [World.setKnownCache, Heap.setKnownCache_preserves_other _ _ _ hne]
      have hnew : (recorded (l.world.setKnownCache c recM .suspended)
          (.retry c reason)).heap.lookup c = some { recM with cache := .suspended } := by
        simp [World.setKnownCache]
      refine ⟨φ', hp, hfresh, ?_, hgrow _ hother rfl, .retryableFault reason, by simp, ?_⟩
      · cases mode with
        | carrier =>
            exact hc.set_private (hnotmem rfl) hother (fun _ _ => ⟨recM, hll⟩) rfl
        | named ℓ =>
            obtain ⟨hφ', s, hs', hr''⟩ := named_cell ℓ rfl
            have hset := hc.set_named (memo := .pending) hφ' hs' hnew
              ⟨hr''.code, hr''.env, .pending⟩ hother rfl
            cases o₀ with
            | ok v => cases hor
            | fail => exact hset
            | blackhole => exact hset
      · rw [Mode.apply_fst]; exact hor

/-- Every returned alternative passes through the update frame of the forced cell. -/
theorem commit_pops {φ : List CellId} {m : MMachine} {c : CellId}
    {rec : CellRecord (Comp × MEnv) MVal Empty} {mode : Mode} {σM : Store}
    (hl : m.world.heap.lookup c = some rec) (hs : rec.cache = .suspended)
    (hcorr : Corr φ σM (markWorld m.world c rec)) (hmode : mode.OK φ σM c) :
    ∀ {L : List Result} {leaves : List MMachine},
      List.Forall₂ (ResRel φ (markWorld m.world c rec) []) L leaves →
      ∃ leaves', Returns (machineSpec P) [] leaves.length
          (leaves.map (below [.commit c m.world.nextEvaluator])) leaves' ∧
        List.Forall₂ (ResRel φ m.world []) (L.map mode.apply) leaves' := by
  intro L leaves h
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons r l L' leaves₀ hr _ ih =>
      obtain ⟨leaves', hrun, hrel⟩ := ih
      obtain ⟨l', hstep, hrel'⟩ := commit_pop P hl hs hcorr hmode hr
      have hret : ∃ o', l'.control = .returned o' [] := by
        obtain ⟨_, _, _, _, _, o', ho', _⟩ := hrel'; exact ⟨o', ho'⟩
      obtain ⟨o', ho'⟩ := hret
      have hnot : ∀ o, (below [.commit c m.world.nextEvaluator] l).control ≠ .returned o [] := by
        obtain ⟨_, _, _, _, _, o, ho, _⟩ := hr
        intro o₁ h₁; simp [ho, extendControl] at h₁
      have first : Returns (machineSpec P) [] 1 [below [.commit c m.world.nextEvaluator] l] [l'] :=
        returns_step P hstep hnot (Returns.single_leaf o' ho')
      refine ⟨l' :: leaves', ?_, .cons hrel' hrel⟩
      have := first.append hrun
      simpa [Nat.add_comm] using this

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
