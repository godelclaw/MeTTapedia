/-!
# ContextCore — task context for MeTTaClaw agents (design skeleton)

The proposed context layer over the hybrid batch rule of `IterGrounding`:
pins outside any economy, an attention-allocated optional pool, compaction as
a checkpoint, and a gate on claims.  Core Lean 4 only, no imports, so one
`lean ContextCore.lean` checks it without building any library.

Harness invariants named below: S1 every call gets exactly one result; S2 no
silent deferral; S5 the transcript is append-only within a window; S6 outputs
are bounded and marked when cut; S7 compaction keeps the request and leaves a
recoverable stub for everything it drops; S9 steering happens at boundaries.

Modules, each tagged with the existing `lean/pettaclaw` (or mettapedia) file it
extends:

* §1 BatchRule + TaskTranscript — extends `AdmissionFrontier` (prefixKind),
  `ToolLoopComparison` (replaces its count limit), `IterBranches.wf`,
  `CodingAgent` round evidence, `StrategyTraceAudit` (adds `notRun`).
* §2 Pending — extends `AgentMemory/EventSourcedMemory` (requeue/resolve once).
* §3 Compaction — extends `ConversationContinuation.compact` (laws on the view)
  and `AgentArchitecture.compaction_can_erase_view_but_not_log`.
* §4 AttentionEconomy (pool only) — extends `StiMass`, `StiFloorDecay`,
  `StiFloor`, `AttentionEconomy.Forgettable`, `AgentMemory/WorkingMemory`.
* §5 ContextAssembler — generalises `ContextAttention.assemble` with a trigger;
  instantiates `ContextProjection.ContextPolicy`.
* §6 ClaimGate — extends `AgentArchitecture.step_claim_requires_end_to_end_evidence`
  to outgoing messages; `ObservedStrategy.Snapshot` gains the visible cids.

Not modelled: LLM behaviour, prose claim extraction (the gate is over declared
or detected claim cids), wall clocks, SQLite, the cache layer.
-/

namespace ContextCore

/-! ## §1 Batch rule and task transcript (S1, S2, S5) -/

/-- A proposed command: its call id and whether it is an effect (anything not in
the shared observation set, including `send`, `rest`, `nop`). -/
structure Cmd where
  cid : Nat
  effect : Bool
deriving Repr, DecidableEq

/-- Result status of a call.  Silence is not a status (S1). -/
inductive Status
  | ok | error | denied | withheld | notRun | aborted | cancelled
deriving Repr, DecidableEq

/-- What execution can return; never `notRun`. -/
inductive Exec
  | ok | error | denied | aborted
deriving Repr, DecidableEq

def Exec.toStatus : Exec → Status
  | .ok => .ok
  | .error => .error
  | .denied => .denied
  | .aborted => .aborted

/-- A status that witnesses an execution attempt. -/
def Status.ran : Status → Bool
  | .ok | .error | .denied | .aborted => true
  | _ => false

theorem Exec.toStatus_ran (e : Exec) : e.toStatus.ran = true := by
  cases e <;> rfl

/-- The batch rule: run the proposal in order up to the first command the host
holds back (it depends on new input, or follows a failed effect it depends
on); that command and everything after it are not run.  There is no count
limit: with nothing held back the whole proposal runs.  Returns (run, notRun).
It is a prefix split, so `AdmissionFrontier.admitted_prefix` is unchanged. -/
def admit (holds : Cmd → Bool) : List Cmd → List Cmd × List Cmd
  | [] => ([], [])
  | c :: cs =>
    if holds c then ([], c :: cs)
    else (c :: (admit holds cs).1, (admit holds cs).2)

/-- Nothing proposed is lost by the split: run ++ notRun = proposal. -/
theorem admit_append (holds : Cmd → Bool) (cs : List Cmd) :
    (admit holds cs).1 ++ (admit holds cs).2 = cs := by
  induction cs with
  | nil => simp [admit]
  | cons c cs ih =>
    by_cases h : holds c = true
    · simp [admit, h]
    · simp [admit, h, ih]

/-- With nothing held back every proposed command runs. -/
theorem admit_runs_whole_proposal (holds : Cmd → Bool) (cs : List Cmd)
    (free : ∀ c ∈ cs, holds c = false) : admit holds cs = (cs, []) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have here : holds c = false := free c (by simp)
    have rest : ∀ d ∈ cs, holds d = false := fun d m => free d (by simp [m])
    simp [admit, here, ih rest]

/-- One paired transcript entry. -/
structure Pair where
  cmd : Cmd
  status : Status
  step : Nat
deriving Repr, DecidableEq

/-- Host state: the model-visible task transcript, the execution log, Pending. -/
structure State where
  transcript : List Pair
  executed : List Nat
  pending : List Nat
deriving Repr

def runPairs (k : Nat) (exec : Cmd → Exec) (run : List Cmd) : List Pair :=
  run.map fun c => ⟨c, (exec c).toStatus, k⟩

def notRunPairs (k : Nat) (rest : List Cmd) : List Pair :=
  rest.map fun c => ⟨c, .notRun, k⟩

/-- One model step under the batch rule: every proposed command gets exactly
one paired result, executed ones from `exec`, the rest `notRun` (S1/S2). -/
def step (holds : Cmd → Bool) (k : Nat) (exec : Cmd → Exec) (s : State) (cs : List Cmd) : State :=
  { transcript := s.transcript ++ (runPairs k exec (admit holds cs).1 ++
                                    notRunPairs k (admit holds cs).2)
    executed := s.executed ++ (admit holds cs).1.map (·.cid)
    pending := s.pending ++ (admit holds cs).2.map (·.cid) }

/-- S5: the transcript only grows within a window. -/
theorem step_extends (holds : Cmd → Bool) (k : Nat) (exec : Cmd → Exec) (s : State) (cs : List Cmd) :
    s.transcript <+: (step holds k exec s cs).transcript :=
  List.prefix_append _ _

/-- S1: the appended segment pairs every proposed command exactly once, in order. -/
theorem step_pairs_every_proposed (holds : Cmd → Bool) (k : Nat) (exec : Cmd → Exec) (s : State)
    (cs : List Cmd) :
    ∃ new, (step holds k exec s cs).transcript = s.transcript ++ new ∧
      new.map (·.cmd) = cs := by
  refine ⟨runPairs k exec (admit holds cs).1 ++ notRunPairs k (admit holds cs).2, rfl, ?_⟩
  simp only [runPairs, notRunPairs, List.map_append, List.map_map]
  have h1 : ((fun p : Pair => p.cmd) ∘ fun c => (⟨c, (exec c).toStatus, k⟩ : Pair)) = id := rfl
  have h2 : ((fun p : Pair => p.cmd) ∘ fun c => (⟨c, Status.notRun, k⟩ : Pair)) = id := rfl
  rw [h1, h2, List.map_id, List.map_id]
  exact admit_append holds cs

theorem filter_ran_runPairs (k : Nat) (exec : Cmd → Exec) (run : List Cmd) :
    (runPairs k exec run).filter (·.status.ran) = runPairs k exec run := by
  induction run with
  | nil => rfl
  | cons c cs ih =>
    simp only [runPairs, List.map_cons, List.filter_cons, Exec.toStatus_ran]
    simp only [runPairs] at ih
    rw [if_pos trivial, ih]

theorem filter_ran_notRunPairs (k : Nat) (rest : List Cmd) :
    (notRunPairs k rest).filter (·.status.ran) = [] := by
  induction rest with
  | nil => rfl
  | cons c cs ih =>
    simp only [notRunPairs, List.map_cons, List.filter_cons, Status.ran] at ih ⊢
    simp [ih]

/-- Transcript ↔ execution log on each step: the newly executed cids are exactly
the cids of new pairs whose status witnesses a run (no silent execution, no
phantom result).  This is the per-step core of `transcript_bijection`. -/
theorem step_executed_are_run (holds : Cmd → Bool) (k : Nat) (exec : Cmd → Exec) (cs : List Cmd) :
    ((runPairs k exec (admit holds cs).1 ++ notRunPairs k (admit holds cs).2).filter
        (·.status.ran)).map (·.cmd.cid) =
      (admit holds cs).1.map (·.cid) := by
  rw [List.filter_append, filter_ran_runPairs, filter_ran_notRunPairs, List.append_nil]
  simp only [runPairs, List.map_map]
  rfl

/-- Every not-run command enters Pending (§2). -/
theorem step_notrun_enters_pending (holds : Cmd → Bool) (k : Nat) (exec : Cmd → Exec) (s : State)
    (cs : List Cmd) (c : Cmd) (h : c ∈ (admit holds cs).2) :
    c.cid ∈ (step holds k exec s cs).pending := by
  simp only [step]
  exact List.mem_append_right _ (List.mem_map_of_mem h)

/-! ## §2 Pending: resolve exactly one entry (run, cancel or expire) -/

def resolve (cid : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = cid then xs else x :: resolve cid xs

/-- Resolution removes exactly one entry when the cid is pending. -/
theorem resolve_removes_exactly_one (cid : Nat) (p : List Nat) (h : cid ∈ p) :
    (resolve cid p).length + 1 = p.length := by
  induction p with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = cid
    · simp [resolve, hx]
    · have : cid ∈ xs := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hx
        · exact h'
      simp [resolve, hx, ih this]

/-- Resolving one item never drops another. -/
theorem resolve_keeps_others (cid y : Nat) (p : List Nat) (hy : y ∈ p) (hne : y ≠ cid) :
    y ∈ resolve cid p := by
  induction p with
  | nil => simp at hy
  | cons x xs ih =>
    by_cases hx : x = cid
    · subst hx
      rcases List.mem_cons.mp hy with h' | h'
      · exact absurd h' hne
      · simpa [resolve] using h'
    · rcases List.mem_cons.mp hy with h' | h'
      · subst h'; simp [resolve, hx]
      · simp [resolve, hx, ih h']

/-! ## §3 Compaction: every dropped pair leaves a stub; checkpoint carry-forward -/

/-- Keep the last `keep` pairs verbatim, replace the older ones by stubs (cids). -/
def compact (keep : Nat) (t : List Pair) : List Nat × List Pair :=
  ((t.take (t.length - keep)).map (·.cmd.cid), t.drop (t.length - keep))

/-- Stubs ++ kept = all: compaction never loses a pair's identity (S6/S7). -/
theorem compact_partitions_pairs (keep : Nat) (t : List Pair) :
    (compact keep t).1 ++ (compact keep t).2.map (·.cmd.cid) = t.map (·.cmd.cid) := by
  simp only [compact]
  rw [← List.map_append, List.take_append_drop]

/-- The opencode checkpoint schema, as cid lists. -/
structure Checkpoint where
  active : List Nat
  blocked : List Nat
  next : List Nat
  completed : List Nat
deriving Repr, DecidableEq

def Checkpoint.unfinished (c : Checkpoint) : List Nat := c.active ++ c.blocked ++ c.next

/-- The host's decidable check on a model-written checkpoint. -/
def checkpointOk (pending : List Nat) (old new : Checkpoint) : Bool :=
  old.unfinished.all (fun x => decide (x ∈ new.unfinished) || decide (x ∈ new.completed)) &&
    pending.all (fun x => decide (x ∈ new.unfinished))

/-- Carry-forward and Pending inclusion follow from the check. -/
theorem checkpoint_check_sound (pending : List Nat) (old new : Checkpoint)
    (h : checkpointOk pending old new = true) :
    (∀ x ∈ old.unfinished, x ∈ new.unfinished ∨ x ∈ new.completed) ∧
      (∀ x ∈ pending, x ∈ new.unfinished) := by
  simp only [checkpointOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  exact h

/-! ## §4 Attention economy over the optional pool (integer STI, per-mille) -/

structure Item where
  id : Nat
  sti : Nat
  lti : Nat
  size : Nat
  lastInj : Nat
  created : Nat
deriving Repr, DecidableEq

def decay (retain : Nat) (i : Item) : Item := { i with sti := i.sti * retain / 1000 }

/-- Decay never increases salience (`StiMass.Decay.nonincreasing`). -/
theorem decay_nonincreasing (retain : Nat) (h : retain ≤ 1000) (i : Item) :
    (decay retain i).sti ≤ i.sti := by
  simp only [decay]
  apply Nat.div_le_of_le_mul
  calc i.sti * retain ≤ i.sti * 1000 := Nat.mul_le_mul_left _ h
    _ = 1000 * i.sti := Nat.mul_comm _ _

def mass : List Item → Nat
  | [] => 0
  | i :: is => i.sti + mass is

/-- Pure decay never increases total STI (`StiMass.sti_mass_decreases`). -/
theorem mass_after_decay_le (retain : Nat) (h : retain ≤ 1000) (is : List Item) :
    mass (is.map (decay retain)) ≤ mass is := by
  induction is with
  | nil => exact Nat.le_refl 0
  | cons i is ih =>
    simp only [List.map_cons, mass]
    exact Nat.add_le_add (decay_nonincreasing retain h i) ih

/-- A named stimulus: the only source of STI, capped at `dmax` per injection. -/
def stimulate (dmax target amount now : Nat) (i : Item) : Item :=
  if i.id = target then { i with sti := i.sti + min amount dmax, lastInj := now } else i

/-- One stimulus raises total mass by at most `dmax` per item
(`StiMass.sti_step_bounded`, finite form). -/
theorem mass_after_stimulus_le (dmax target amount now : Nat) (is : List Item) :
    mass (is.map (stimulate dmax target amount now)) ≤ mass is + is.length * dmax := by
  induction is with
  | nil => simp [mass]
  | cons i is ih =>
    simp only [List.map_cons, mass, List.length_cons]
    have hi : (stimulate dmax target amount now i).sti ≤ i.sti + dmax := by
      unfold stimulate
      split
      · exact Nat.add_le_add_left (Nat.min_le_right _ _) _
      · exact Nat.le_add_right _ _
    have : (is.length + 1) * dmax = is.length * dmax + dmax := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [this]
    omega

def sizeSum : List Item → Nat
  | [] => 0
  | i :: is => i.size + sizeSum is

/-- Greedy AF fill over an STI-ranked list: (admitted, stubbed ids). -/
def fill : Nat → List Item → List Item × List Nat
  | _, [] => ([], [])
  | b, i :: is =>
    if i.size ≤ b then (i :: (fill (b - i.size) is).1, (fill (b - i.size) is).2)
    else ((fill b is).1, i.id :: (fill b is).2)

theorem fill_within_budget (b : Nat) (is : List Item) : sizeSum (fill b is).1 ≤ b := by
  induction is generalizing b with
  | nil => simp [fill, sizeSum]
  | cons i is ih =>
    by_cases h : i.size ≤ b
    · simp only [fill]
      rw [if_pos h]
      simp only [sizeSum]
      have := ih (b - i.size)
      omega
    · simp only [fill]
      rw [if_neg h]
      exact ih b

/-- Recoverable eviction: every pool item is admitted or leaves a stub id. -/
theorem fill_partitions (b : Nat) (is : List Item) :
    ∀ i ∈ is, i ∈ (fill b is).1 ∨ i.id ∈ (fill b is).2 := by
  induction is generalizing b with
  | nil => intro i hi; simp at hi
  | cons j js ih =>
    intro i hi
    by_cases h : j.size ≤ b
    · simp only [fill]
      rw [if_pos h]
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih (b - j.size) i hi' with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr h2
    · simp only [fill]
      rw [if_neg h]
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih b i hi' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h2)

/-- Eviction happens only at checkpoints: between them the AF only grows by
appended deltas, so nothing the model saw disappears mid-task (re-planning guard). -/
inductive Boundary
  | step | checkpoint
deriving Repr, DecidableEq

def refresh : Boundary → List Nat → List Nat → List Nat
  | .step, af, cand => af ++ cand.filter (fun x => decide (x ∉ af))
  | .checkpoint, _, cand => cand

theorem refresh_step_keeps_af_prefix (af cand : List Nat) :
    af <+: refresh .step af cand :=
  List.prefix_append _ _

/-! ## §5 Context assembler: pure in (trigger, pins, transcript, pool, budget) -/

inductive Trigger
  | userNew | userCont | continuation | wake | heartbeat | channel
deriving Repr, DecidableEq

/-- Hard pins, outside the economy (S7, S9): request, addressed messages since
task start, Pending, and the last step's pairs. -/
structure Pins where
  request : Nat
  addressed : List Nat
  pending : List Nat
  last : List Pair
deriving Repr, DecidableEq

/-- Agent-owned parameters; shares in per-mille. -/
structure Policy where
  total : Nat
  share : Trigger → Nat

structure View where
  pins : Pins
  transcript : List Pair
  af : List Item
  stubs : List Nat

def poolBudget (pol : Policy) (tr : Trigger) (fixedSize : Nat) : Nat :=
  (pol.total - fixedSize) * pol.share tr / 1000

def assemble (pol : Policy) (tr : Trigger) (pins : Pins) (fixedSize : Nat)
    (t : List Pair) (ranked : List Item) : View :=
  { pins := pins
    transcript := t
    af := (fill (poolBudget pol tr fixedSize) ranked).1
    stubs := (fill (poolBudget pol tr fixedSize) ranked).2 }

/-- The pool cannot rewrite the pins (generalises
`ContextAttention.retrieval_cannot_rewrite_mandatory_context`). -/
theorem assemble_pins_independent_of_pool (pol : Policy) (tr : Trigger) (pins : Pins)
    (n : Nat) (t : List Pair) (a b : List Item) :
    (assemble pol tr pins n t a).pins = (assemble pol tr pins n t b).pins ∧
      (assemble pol tr pins n t a).transcript = (assemble pol tr pins n t b).transcript :=
  ⟨rfl, rfl⟩

/-- The trigger changes only the pool budget, never the pins or transcript. -/
theorem assemble_pins_independent_of_trigger (pol : Policy) (t1 t2 : Trigger) (pins : Pins)
    (n : Nat) (t : List Pair) (ranked : List Item) :
    (assemble pol t1 pins n t ranked).pins = (assemble pol t2 pins n t ranked).pins ∧
      (assemble pol t1 pins n t ranked).transcript =
        (assemble pol t2 pins n t ranked).transcript :=
  ⟨rfl, rfl⟩

theorem af_within_budget (pol : Policy) (tr : Trigger) (pins : Pins) (n : Nat)
    (t : List Pair) (ranked : List Item) :
    sizeSum (assemble pol tr pins n t ranked).af ≤ poolBudget pol tr n :=
  fill_within_budget _ _

theorem assemble_pool_recoverable (pol : Policy) (tr : Trigger) (pins : Pins) (n : Nat)
    (t : List Pair) (ranked : List Item) :
    ∀ i ∈ ranked, i ∈ (assemble pol tr pins n t ranked).af ∨
      i.id ∈ (assemble pol tr pins n t ranked).stubs :=
  fill_partitions _ _

/-! ## §6 Claim gate: a claimed effect needs a visible ok receipt -/

inductive GateMode
  | withhold | mark | off
deriving Repr, DecidableEq

inductive Decision
  | send | sendMarked | withheld
deriving Repr, DecidableEq

/-- Cids of ok effect results in the view the model saw this step. -/
def visibleOk (v : List Pair) : List Nat :=
  (v.filter (fun p => p.status == .ok && p.cmd.effect)).map (·.cmd.cid)

def gate (m : GateMode) (visible : List Pair) (claims : List Nat) : Decision :=
  if claims.all (fun c => decide (c ∈ visibleOk visible)) then .send
  else match m with
    | .withhold => .withheld
    | .mark => .sendMarked
    | .off => .send

theorem visibleOk_sound (v : List Pair) (c : Nat) (h : c ∈ visibleOk v) :
    ∃ p ∈ v, p.cmd.cid = c ∧ p.status = .ok ∧ p.cmd.effect = true := by
  simp only [visibleOk, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq] at h
  obtain ⟨p, ⟨hp, hs, he⟩, rfl⟩ := h
  exact ⟨p, hp, rfl, hs, he⟩

/-- Gate soundness: unless switched off, an unmarked send has every claimed
effect visible as an ok receipt. -/
theorem gate_send_sound (m : GateMode) (hm : m ≠ .off) (v : List Pair) (claims : List Nat)
    (h : gate m v claims = .send) : ∀ c ∈ claims, c ∈ visibleOk v := by
  unfold gate at h
  split at h
  · rename_i hall
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall
  · cases m with
    | withhold => cases h
    | mark => cases h
    | off => exact absurd rfl hm

/-- A not-run (or otherwise non-ok) result never backs a claim. -/
theorem notrun_never_backs_claim (v : List Pair) (c : Nat)
    (h : ∀ p ∈ v, p.cmd.cid = c → p.status ≠ .ok) : c ∉ visibleOk v := by
  intro hc
  obtain ⟨p, hp, hid, hs, _⟩ := visibleOk_sound v c hc
  exact h p hp hid hs

/-! ## Concrete checks (the 10-13 00:25 shape, synthetic) -/

def q : Cmd := ⟨1, false⟩   -- query (read)
def w : Cmd := ⟨2, true⟩    -- write-file (effect)
def s : Cmd := ⟨3, true⟩    -- send (effect)

/-- With nothing held back the read, the write and the send all run. -/
example : admit (fun _ => false) [q, w, s] = ([q, w, s], []) := by decide

/-- New input that the send depends on holds it back: it is not run and enters
Pending instead of vanishing. -/
def heldSend (c : Cmd) : Bool := c.cid == 3

example : admit heldSend [q, w, s] = ([q, w], [s]) := by decide

def s0 : State := ⟨[], [], []⟩
def s1 : State := step heldSend 1311 (fun _ => .ok) s0 [q, w, s]

example : s1.pending = [3] := by decide
example : s1.executed = [1, 2] := by decide

/-- A claim about the not-run send is withheld; a claim about the executed write
passes. -/
example : gate .withhold s1.transcript [3] = .withheld := by decide
example : gate .withhold s1.transcript [2] = .send := by decide

end ContextCore

#print axioms ContextCore.admit_append
#print axioms ContextCore.admit_runs_whole_proposal
#print axioms ContextCore.step_pairs_every_proposed
#print axioms ContextCore.step_executed_are_run
#print axioms ContextCore.step_notrun_enters_pending
#print axioms ContextCore.resolve_removes_exactly_one
#print axioms ContextCore.resolve_keeps_others
#print axioms ContextCore.compact_partitions_pairs
#print axioms ContextCore.checkpoint_check_sound
#print axioms ContextCore.mass_after_decay_le
#print axioms ContextCore.mass_after_stimulus_le
#print axioms ContextCore.fill_within_budget
#print axioms ContextCore.fill_partitions
#print axioms ContextCore.refresh_step_keeps_af_prefix
#print axioms ContextCore.assemble_pins_independent_of_pool
#print axioms ContextCore.af_within_budget
#print axioms ContextCore.assemble_pool_recoverable
#print axioms ContextCore.gate_send_sound
#print axioms ContextCore.notrun_never_backs_claim
