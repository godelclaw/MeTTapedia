import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceCorrespondence

/-!
# One transition of the instance, case by case

The unchanged `NeedReference.step` of `machineSpec P`, computed for each
control the adequacy proof meets: local outputs, allocation, demand,
resampling, events, forcing a cached, evaluating or suspended cell, and
returning through a resume frame or an update frame.

`branchInner` lists the alternatives of a forced suspended cell without their
update frame: `branchAlternatives_eq` states that the machine's own
alternatives are exactly these machines placed above `commit c owner`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference NeedReturningRuns

variable (P : Program)

@[simp] theorem finished_world (m : MMachine) (w : MWorld)
    (ctrl : Control MLocal MResume MVal Empty MFault) (a b c d : Nat) :
    (finished m w ctrl a b c d).world = w := rfl

@[simp] theorem finished_control (m : MMachine) (w : MWorld)
    (ctrl : Control MLocal MResume MVal Empty MFault) (a b c d : Nat) :
    (finished m w ctrl a b c d).control = ctrl := rfl

@[simp] theorem retryMachine_world' (m : MMachine) (w : MWorld) (c : CellId)
    (r : RetryReason MFault) (stk : List (Frame MResume)) (a b d e : Nat) :
    (retryMachine m w c r stk a b d e).world = recorded w (.retry c r) := rfl

@[simp] theorem retryMachine_control' (m : MMachine) (w : MWorld) (c : CellId)
    (r : RetryReason MFault) (stk : List (Frame MResume)) (a b d e : Nat) :
    (retryMachine m w c r stk a b d e).control = .returned (.retryableFault r) stk := rfl

@[simp] theorem recorded_heap' (w : MWorld)
    (p : ReceiptPayload (Comp × MEnv) MRule MVal Empty MFault Nat) :
    (recorded w p).heap = w.heap := rfl

@[simp] theorem recorded_nextCell (w : MWorld)
    (p : ReceiptPayload (Comp × MEnv) MRule MVal Empty MFault Nat) :
    (recorded w p).nextCell = w.nextCell := rfl

@[simp] theorem recorded_nextEvaluator (w : MWorld)
    (p : ReceiptPayload (Comp × MEnv) MRule MVal Empty MFault Nat) :
    (recorded w p).nextEvaluator = w.nextEvaluator := rfl

theorem step_output (m : MMachine) (o : MOutcome) (stk : List (Frame MResume))
    (hc : m.control = .run (.output o) stk) :
    step (machineSpec P) m = [finished m m.world (.returned o stk) 0 0 0 0] := by
  rcases m with ⟨w, ctrl, k⟩
  simp only at hc
  subst hc
  rfl

theorem step_alloc (m : MMachine) (origin : Comp × MEnv) (k : MResume)
    (stk : List (Frame MResume)) (hc : m.control = .run (.alloc origin k) stk)
    (w' : MWorld) (c : CellId) (ha : m.world.allocate? origin = some (w', c)) :
    step (machineSpec P) m =
      [finished m w' (.run (afterAllocation k c) stk) 1 1 1 1] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc ha
  subst hc
  simp [step, machineSpec, action, ha]

theorem step_demand (m : MMachine) (c : CellId) (k : MResume) (stk : List (Frame MResume))
    (hc : m.control = .run (.demand c k) stk) :
    step (machineSpec P) m = [finished m m.world (.force c (.resume k :: stk)) 0 0 0 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc
  subst hc
  rfl

theorem step_resample (m : MMachine) (c : CellId) (k : MResume) (stk : List (Frame MResume))
    (hc : m.control = .run (.resample c k) stk)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (hl : m.world.heap.lookup c = some rec)
    (w' : MWorld) (c' : CellId)
    (ha : m.world.allocate? rec.origin (c.generation + 1) = some (w', c')) :
    step (machineSpec P) m =
      [finished m (recorded w' (.resample c c')) (.run (afterAllocation k c') stk) 2 1 2 1] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl ha
  subst hc
  simp [step, machineSpec, action, hl, ha]

theorem step_emit (m : MMachine) (e : Nat) (next : MLocal) (stk : List (Frame MResume))
    (hc : m.control = .run (.emit e next) stk) :
    step (machineSpec P) m =
      [finished m (recorded m.world (.effect e)) (.run next stk) 0 0 1 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc
  subst hc
  rfl

theorem step_force_value (m : MMachine) (c : CellId) (stk : List (Frame MResume))
    (hc : m.control = .force c stk) (rec : CellRecord (Comp × MEnv) MVal Empty)
    (hl : m.world.heap.lookup c = some rec) (v : MVal) (hv : rec.cache = .value v) :
    step (machineSpec P) m =
      [finished m (recorded m.world (.observe c (.value v))) (.returned (.value v) stk)
        1 0 1 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv]

theorem step_force_evaluating (m : MMachine) (c : CellId) (stk : List (Frame MResume))
    (hc : m.control = .force c stk) (rec : CellRecord (Comp × MEnv) MVal Empty)
    (hl : m.world.heap.lookup c = some rec) (owner : EvaluatorId)
    (hv : rec.cache = .evaluating owner) :
    step (machineSpec P) m = [retryMachine m m.world c (.blackhole c) stk 1 0 0 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv]

theorem step_force_suspended_nil (m : MMachine) (c : CellId) (stk : List (Frame MResume))
    (hc : m.control = .force c stk) (rec : CellRecord (Comp × MEnv) MVal Empty)
    (hl : m.world.heap.lookup c = some rec) (hv : rec.cache = .suspended)
    (hn : alternatives P rec.origin = []) :
    step (machineSpec P) m =
      [retryMachine m
        (recorded { m.world with nextEvaluator := m.world.nextEvaluator + 1 }
          (.evaluate c m.world.nextEvaluator))
        c (.noRule c) stk 1 0 1 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv, machineSpec, hn]

theorem step_force_suspended (m : MMachine) (c : CellId) (stk : List (Frame MResume))
    (hc : m.control = .force c stk) (rec : CellRecord (Comp × MEnv) MVal Empty)
    (hl : m.world.heap.lookup c = some rec) (hv : rec.cache = .suspended)
    (a : MRule × MLocal) (as : List (MRule × MLocal))
    (hn : alternatives P rec.origin = a :: as) :
    step (machineSpec P) m =
      branchAlternatives m { m.world with nextEvaluator := m.world.nextEvaluator + 1 }
        c rec m.world.nextEvaluator stk 0 (a :: as) := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv, machineSpec, hn]

theorem step_returned_resume (m : MMachine) (o : MOutcome) (k : MResume)
    (stk : List (Frame MResume)) (hc : m.control = .returned o (.resume k :: stk)) :
    step (machineSpec P) m = [finished m m.world (.run (afterDemand k o) stk) 0 0 0 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc
  subst hc
  rfl

theorem step_returned_commit_value (m : MMachine) (v : MVal) (c : CellId) (owner : EvaluatorId)
    (stk : List (Frame MResume)) (hc : m.control = .returned (.value v) (.commit c owner :: stk))
    (rec : CellRecord (Comp × MEnv) MVal Empty) (hl : m.world.heap.lookup c = some rec)
    (hv : rec.cache = .evaluating owner) :
    step (machineSpec P) m =
      [finished m (recorded (m.world.setKnownCache c rec (.value v)) (.observe c (.value v)))
        (.returned (.value v) stk) 1 1 1 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv]

theorem step_returned_commit_retry (m : MMachine) (r : RetryReason MFault) (c : CellId)
    (owner : EvaluatorId) (stk : List (Frame MResume))
    (hc : m.control = .returned (.retryableFault r) (.commit c owner :: stk))
    (rec : CellRecord (Comp × MEnv) MVal Empty) (hl : m.world.heap.lookup c = some rec)
    (hv : rec.cache = .evaluating owner) :
    step (machineSpec P) m =
      [retryMachine m (m.world.setKnownCache c rec .suspended) c r stk 1 1 0 0] := by
  rcases m with ⟨w, ctrl, work⟩
  simp only at hc hl
  subst hc
  simp [step, hl, hv]

/-! ## Alternatives without their update frame -/

/-- The machines of `branchAlternatives` for an empty stack, before their update frame. -/
def branchInner (m : MMachine) (base : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (owner : EvaluatorId) :
    Nat → List (MRule × MLocal) → List MMachine
  | _, [] => []
  | i, (rule, s) :: rest =>
      finished m
          (recorded (recorded ((base.fork i).setKnownCache c rec (.evaluating owner))
            (.evaluate c owner)) (.chooseRule c rule))
          (.run s []) 1 1 2 0 ::
        branchInner m base c rec owner (i + 1) rest

theorem branchAlternatives_eq (m : MMachine) (base : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (owner : EvaluatorId) (i : Nat)
    (alts : List (MRule × MLocal)) :
    branchAlternatives m base c rec owner [] i alts =
      (branchInner m base c rec owner i alts).map (below [.commit c owner]) := by
  induction alts generalizing i with
  | nil => rfl
  | cons a as ih =>
      obtain ⟨rule, s⟩ := a
      simp only [branchAlternatives, branchInner, List.map_cons, ih]
      rfl

theorem branchInner_world (m : MMachine) (base : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (owner : EvaluatorId) (i : Nat)
    (alts : List (MRule × MLocal)) :
    ∀ x ∈ branchInner m base c rec owner i alts,
      x.world.heap = base.heap.setKnownCache c rec (.evaluating owner) ∧
        x.world.nextCell = base.nextCell ∧
        x.world.receipts.effects = base.receipts.effects := by
  induction alts generalizing i with
  | nil => simp [branchInner]
  | cons a as ih =>
      obtain ⟨rule, s⟩ := a
      intro x hx
      simp only [branchInner, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨rfl, rfl, by simp [recorded, World.record, World.fork, World.setKnownCache]⟩
      · exact ih (i + 1) x hx

theorem branchInner_control (m : MMachine) (base : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (owner : EvaluatorId) (i : Nat)
    (alts : List (MRule × MLocal)) :
    List.Forall₂ (fun (a : MRule × MLocal) (x : MMachine) => x.control = .run a.2 [])
      alts (branchInner m base c rec owner i alts) := by
  induction alts generalizing i with
  | nil => exact .nil
  | cons a as ih =>
      obtain ⟨rule, s⟩ := a
      exact .cons rfl (ih (i + 1))

theorem branchInner_length (m : MMachine) (base : MWorld) (c : CellId)
    (rec : CellRecord (Comp × MEnv) MVal Empty) (owner : EvaluatorId) (i : Nat)
    (alts : List (MRule × MLocal)) :
    (branchInner m base c rec owner i alts).length = alts.length :=
  ((branchInner_control m base c rec owner i alts).length_eq).symm

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
