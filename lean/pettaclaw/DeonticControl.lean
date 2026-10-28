/-!
# DeonticControl — grants, a reference monitor and the OODA cycle

`bgoertzel-sing/iter` branch `agent/protocosmo2-wmtm-live-20261005` (`4564185`)
adds a goal-driven control package next to its working memory. A cycle observes,
forms beliefs, plans, appraises plans with a deontic status (`OBLIGATED`,
`PERMITTED`, `FORBIDDEN`), asks a reference monitor for single-use grants and
hands the grants to a dispatcher. Its design names ten invariants, among them
"no grant, no effect", "obligation is not authorization", version closure,
at-most-once execution, "no memory-to-actuation" and "human stop dominates".

The monitor checks a grant's MAC, expiry, unused idempotency key, state
revision and unused grant identity, then records the key and identity in
process memory. The dispatcher executes whenever its caller passes
`authorized=True`, the default. The event store marks superseded events in
place and reports the maximum revision of the events that are not superseded.

Results:
* `deontic_filter_sound`: a cycle whose plans are all `FORBIDDEN` dispatches
  nothing. The appraisal gate is sound.
* `dispatch_trusts_flag`: the dispatcher executes a grant that the monitor
  never saw, even one whose MAC fails. "No grant, no effect" holds only if
  every caller is honest.
* `revoke_is_inert`: revoking a grant neither stops its dispatch nor changes a
  later authorization decision.
* `restart_reauthorizes`: the used-key set lives in memory, so after a restart
  the same grant is authorized a second time.
* `effects_authorized_once` (safety, every trace): when the dispatcher accepts
  only monitor approvals, consumes them once and honors revocation, every
  effect was approved, none repeats, and none follows its revocation.
* `revision_aba`: superseding the newest event with an older revision lowers
  the store's current revision, so a stale grant becomes valid again.
  `knowledge_time_monotone`: numbering by log position never decreases.
* `stale_plan_step_runs` and `one_effect_per_revision`: all grants of a plan
  carry one revision and are checked before the first effect, so a later step
  runs against a state its earlier steps changed. Advancing the revision with
  every effect and checking at dispatch admits one effect per revision.
* `stop_mid_plan_ignored` and `stop_checked_per_dispatch`: the stop flag is
  read once per cycle. A stop arriving after the first dispatch does not stop
  the rest of the plan; a check before every dispatch does.
* `adapter_grant_expired_on_arrival`: the integration adapter sets a grant's
  expiry to its issue time, so the monitor refuses every grant it mints after
  any delay. The integrated pipeline fails closed.
* `derived_item_becomes_observation`: the observer adapter turns every
  working-memory item, derived beliefs included, into an `Observation`.
* `deontic_status_rewrites_truth` and `prohibition_loses_attention`: branch
  `agent/protocosmo2-402-circuit` (`7c603b5`) enforces `forbidden` decisions by
  lowering the attention and the PLN strength of everything that shares a
  keyword with the action. The reason for a prohibition and its negation both
  drop to a tenth of their strength, which breaks `s(X) + s(¬X) = 1`, and the
  prohibition itself loses attention. `enforcement_only_lowers_attention`: the
  enforcer touches no grant or monitor state, so it cannot block an action.

A CeTTa-native controller keeps these invariants in the space. Grants,
approvals, revocations and consumed keys are atoms in the same log as effects
and observations, so they survive restarts and an effect atom can only be
added together with the approval it consumes. Deontic status is a separate
atom consulted by the gate; it never rewrites truth values or attention. Revisions are log positions.
Each effect is checked against the current revision immediately before
dispatch, a stop atom is checked before every effect, and only atoms from
observation channels can satisfy an observation premise.
-/

namespace DeonticControl

/-! ## Appraisal -/

inductive Deontic
  | obligated
  | permitted
  | forbidden
deriving Repr, DecidableEq

def eligible : Deontic → Bool
  | .obligated => true
  | .permitted => true
  | .forbidden => false

/-- A plan: its appraisal and the grants it would request. -/
structure Plan where
  status : Deontic
  grants : List Nat
deriving Repr, DecidableEq

/-- `Orchestrator.run_cycle` after appraisal: authorize and dispatch the first
eligible plan (ranking is abstracted). -/
def cycleDispatches (plans : List Plan) : List Nat :=
  match plans.find? (fun p => eligible p.status) with
  | some p => p.grants
  | none => []

theorem deontic_filter_sound (plans : List Plan)
    (hall : ∀ p ∈ plans, p.status = .forbidden) : cycleDispatches plans = [] := by
  unfold cycleDispatches
  have hnone : plans.find? (fun p => eligible p.status) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp [hall p hp, eligible]
  rw [hnone]

/-! ## The reference monitor and the dispatcher -/

structure Grant where
  id : Nat
  key : Nat
  revision : Nat
  issued : Nat
  expires : Nat
  macValid : Bool
deriving Repr, DecidableEq

/-- Used idempotency keys and dispatched grant identities, in process memory. -/
structure Monitor where
  usedKeys : List Nat
  dispatched : List Nat
deriving Repr, DecidableEq

def Monitor.empty : Monitor := ⟨[], []⟩

/-- `ReferenceMonitor.authorize`. -/
def authorize (m : Monitor) (g : Grant) (now current : Nat) : Bool × Monitor :=
  if g.macValid && decide (now ≤ g.expires) && !(m.usedKeys.contains g.key) &&
      decide (g.revision = current) && !(m.dispatched.contains g.id) then
    (true, ⟨g.key :: m.usedKeys, g.id :: m.dispatched⟩)
  else (false, m)

/-- `ReferenceMonitor.revoke`: forget the grant identity, keep its key. -/
def revoke (m : Monitor) (g : Grant) : Monitor := { m with dispatched := m.dispatched.erase g.id }

/-- `Dispatcher.dispatch`: execute when the caller says the grant is authorized. -/
def dispatchU (g : Grant) (authorized : Bool := true) : Option Nat :=
  if authorized then some g.id else none

def forged : Grant := ⟨7, 7, 0, 0, 0, false⟩

theorem dispatch_trusts_flag :
    (authorize Monitor.empty forged 0 0).1 = false ∧ dispatchU forged = some 7 := by
  decide

def sample : Grant := ⟨1, 10, 0, 0, 5, true⟩

theorem revoke_is_inert :
    let m1 := (authorize Monitor.empty sample 0 0).2
    (authorize Monitor.empty sample 0 0).1 = true ∧
      dispatchU sample = some 1 ∧
      (authorize (revoke m1 sample) sample 0 0).1 = (authorize m1 sample 0 0).1 := by
  decide

/-- A restart starts from an empty monitor. -/
def restart (_ : Monitor) : Monitor := Monitor.empty

theorem restart_reauthorizes :
    let m1 := (authorize Monitor.empty sample 0 0).2
    (authorize Monitor.empty sample 0 0).1 = true ∧
      (authorize m1 sample 0 0).1 = false ∧
      (authorize (restart m1) sample 0 0).1 = true := by
  decide

/-! ## Approvals as the only route to an effect -/

/-- Monitor state plus approvals, revocations, consumed approvals and effects. -/
structure Sys where
  monitor : Monitor
  approved : List Nat
  revoked : List Nat
  effects : List Nat
deriving Repr, DecidableEq

inductive Act
  | authorize (g : Grant) (now current : Nat)
  | revoke (id : Nat)
  | dispatch (id : Nat)
deriving Repr, DecidableEq

/-- The dispatcher accepts only an approved, unrevoked, unconsumed identity. -/
def stepC (s : Sys) : Act → Sys
  | .authorize g now current =>
      let r := authorize s.monitor g now current
      if r.1 then { s with monitor := r.2, approved := g.id :: s.approved } else s
  | .revoke id => { s with revoked := id :: s.revoked }
  | .dispatch id =>
      if id ∈ s.approved ∧ id ∉ s.revoked ∧ id ∉ s.effects then
        { s with effects := id :: s.effects }
      else s

def runC (s : Sys) : List Act → Sys
  | [] => s
  | a :: rest => runC (stepC s a) rest

def initial : Sys := ⟨Monitor.empty, [], [], []⟩

/-- Every effect was approved, effects never repeat, and an identity revoked
before its dispatch never produces an effect. -/
def Safe (s : Sys) : Prop :=
  (∀ e ∈ s.effects, e ∈ s.approved) ∧ s.effects.Nodup

theorem stepC_safe (s : Sys) (a : Act) (h : Safe s) : Safe (stepC s a) := by
  obtain ⟨happ, hnd⟩ := h
  cases a with
  | authorize g now current =>
    simp only [stepC]
    split
    · exact ⟨fun e he => List.mem_cons_of_mem _ (happ e he), hnd⟩
    · exact ⟨happ, hnd⟩
  | revoke id => exact ⟨happ, hnd⟩
  | dispatch id =>
    simp only [stepC]
    split
    · rename_i hc
      obtain ⟨ha, _, hnew⟩ := hc
      refine ⟨?_, List.nodup_cons.mpr ⟨hnew, hnd⟩⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ha
      · exact happ e he
    · exact ⟨happ, hnd⟩

theorem runC_safe (s : Sys) (acts : List Act) (h : Safe s) : Safe (runC s acts) := by
  induction acts generalizing s with
  | nil => exact h
  | cons a rest ih => exact ih (stepC s a) (stepC_safe s a h)

/-- Revocation sticks: a revoked identity with no effect yet never produces one. -/
theorem revoked_stays_without_effect (s : Sys) (id : Nat) (acts : List Act)
    (hr : id ∈ s.revoked) (he : id ∉ s.effects) : id ∉ (runC s acts).effects := by
  induction acts generalizing s with
  | nil => exact he
  | cons a rest ih =>
    apply ih
    · cases a <;> simp only [stepC] <;> (try split) <;> simp_all
    · cases a with
      | authorize g now current =>
        simp only [stepC]
        split <;> exact he
      | revoke id' => exact he
      | dispatch id' =>
        simp only [stepC]
        split
        · rename_i hc
          intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · subst h
            exact hc.2.1 hr
          · exact he h
        · exact he

theorem effects_authorized_once (acts : List Act) :
    (∀ e ∈ (runC initial acts).effects, e ∈ (runC initial acts).approved) ∧
      (runC initial acts).effects.Nodup :=
  runC_safe initial acts ⟨by simp [initial], List.nodup_nil⟩

/-! ## Revisions -/

structure Event where
  id : Nat
  revision : Nat
  superseded : Bool
deriving Repr, DecidableEq

/-- `EventStore.current_revision`: the maximum revision of live events. -/
def current (log : List Event) : Nat :=
  log.foldl (fun acc e => if e.superseded then acc else max acc e.revision) 0

/-- `EventStore.supersede`: mark the old event and append the correction with
whatever revision it carries. -/
def supersede (log : List Event) (old : Nat) (new : Event) : List Event :=
  log.map (fun e => if e.id = old then { e with superseded := true } else e) ++ [new]

/-- A grant minted at revision 1 is refused once revision 2 is logged, and
accepted again after revision 2 is superseded by a correction at revision 1. -/
theorem revision_aba :
    let log1 : List Event := [⟨1, 1, false⟩, ⟨2, 2, false⟩]
    let log2 := supersede log1 2 ⟨3, 1, false⟩
    let g : Grant := ⟨5, 50, 1, 0, 9, true⟩
    current log1 = 2 ∧ (authorize Monitor.empty g 0 (current log1)).1 = false ∧
      current log2 = 1 ∧ (authorize Monitor.empty g 0 (current log2)).1 = true := by
  decide

/-- Numbering revisions by log position: corrections append, so the revision
never decreases and a stale grant stays stale. -/
theorem knowledge_time_monotone (log : List Event) (old : Nat) (new : Event) :
    log.length < (supersede log old new).length := by
  simp [supersede]

/-! ## Version closure within a plan -/

/-- Upstream: every grant of a plan is checked against the revision current
before the first dispatch; effects do not advance it. -/
def dispatchPlanU (rev : Nat) (grants : List Grant) : List Nat :=
  (grants.filter (fun g => g.revision = rev)).map Grant.id

/-- Checked at dispatch: each effect advances the revision. -/
def dispatchPlanC : Nat → List Grant → List Nat
  | _, [] => []
  | rev, g :: rest =>
      if g.revision = rev then g.id :: dispatchPlanC (rev + 1) rest
      else dispatchPlanC rev rest

def step1 : Grant := ⟨1, 11, 4, 0, 9, true⟩
def step2 : Grant := ⟨2, 12, 4, 0, 9, true⟩

/-- Both steps of a plan minted at revision 4 run, the second against a state
the first already changed. -/
theorem stale_plan_step_runs : dispatchPlanU 4 [step1, step2] = [1, 2] := by
  decide

/-- With per-effect revisions, at most one grant minted at a given revision
runs. -/
theorem one_effect_per_revision (rev : Nat) (gs : List Grant)
    (hsame : ∀ g ∈ gs, g.revision = rev) : (dispatchPlanC rev gs).length ≤ 1 := by
  match gs, hsame with
  | [], _ => simp [dispatchPlanC]
  | g :: rest, hsame =>
    have hg : g.revision = rev := hsame g (by simp)
    have hrest : ∀ g' ∈ rest, g'.revision = rev := fun g' h => hsame g' (by simp [h])
    have hnone : ∀ (r : Nat) (l : List Grant), (∀ g' ∈ l, g'.revision = rev) →
        rev < r → dispatchPlanC r l = [] := by
      intro r l
      induction l with
      | nil => intros; rfl
      | cons h t ih =>
        intro hl hr
        have hh : h.revision = rev := hl h (by simp)
        have hne : ¬ h.revision = r := by omega
        simp only [dispatchPlanC, hne, if_false]
        exact ih (fun g' hm => hl g' (by simp [hm])) hr
    simp only [dispatchPlanC, hg, if_true, List.length_cons]
    rw [hnone (rev + 1) rest hrest (by omega)]
    simp

/-! ## Stop -/

/-- Upstream: the stop flag is read at the top of the cycle only. A stop that
arrives after the check does not change the dispatches. -/
def dispatchedWithStopU (_stopAfter : Nat) (grants : List Nat) : List Nat := grants

/-- The stop flag read before every dispatch. -/
def dispatchedWithStopC (stopAfter : Nat) (grants : List Nat) : List Nat :=
  grants.take stopAfter

theorem stop_mid_plan_ignored : dispatchedWithStopU 1 [1, 2, 3] = [1, 2, 3] := rfl

theorem stop_checked_per_dispatch (stopAfter : Nat) (grants : List Nat) :
    (dispatchedWithStopC stopAfter grants).length ≤ stopAfter := by
  simp only [dispatchedWithStopC, List.length_take]
  exact Nat.min_le_left _ _

/-! ## The integration adapter -/

/-- `RealAuthorizeAdapter` sets both timestamps to the minting time. -/
def mintAt (t id : Nat) : Grant := ⟨id, id, 0, t, t, true⟩

theorem adapter_grant_expired_on_arrival (t delay id : Nat) (hd : 0 < delay) :
    (authorize Monitor.empty (mintAt t id) (t + delay) 0).1 = false := by
  simp only [authorize, mintAt]
  have : ¬ t + delay ≤ t := by omega
  simp [this]

/-! ## Memory as observation -/

inductive Origin
  | observed
  | recalled
  | derived
deriving Repr, DecidableEq

structure WorkingItem where
  id : Nat
  origin : Origin
deriving Repr, DecidableEq

/-- An `Observation` as produced by `WMTMObserverAdapter`: source `wmtm`, one per
active item. -/
structure Observation where
  id : Nat
  fromObservationChannel : Bool
deriving Repr, DecidableEq

def observeU (items : List WorkingItem) : List Observation :=
  items.map (fun x => ⟨x.id, false⟩)

/-- A channel-aware observer admits only observed items. -/
def observeC (items : List WorkingItem) : List Observation :=
  (items.filter (fun x => x.origin = .observed)).map (fun x => ⟨x.id, true⟩)

theorem derived_item_becomes_observation :
    (⟨3, false⟩ : Observation) ∈ observeU [⟨3, .derived⟩] ∧ observeC [⟨3, .derived⟩] = [] := by
  decide

/-! ## Deontic status as attention and truth

Branch `agent/protocosmo2-402-circuit` (`7c603b5`) adds a `DeonticEnforcer`
and deontic propagation into PLN. For each decision labeled `forbidden`, every
working-memory item sharing a keyword (a word longer than three letters) with
the decision has its STI multiplied by `0.2`, and every PLN atom sharing one has
its strength multiplied by `0.1` and its confidence raised by `0.2`. Values are
in hundredths here. -/

/-- A PLN atom: its words, strength and confidence (hundredths). -/
structure Atom where
  words : List Nat
  strength : Nat
  confidence : Nat
deriving Repr, DecidableEq

def overlaps (keywords : List Nat) (a : Atom) : Bool := a.words.any (fun w => keywords.contains w)

/-- `apply_deontic_constraints_to_atoms` for a `forbidden` decision. -/
def forbidTruth (keywords : List Nat) (a : Atom) : Atom :=
  if overlaps keywords a then
    { a with strength := a.strength / 10, confidence := min 100 (a.confidence + 20) }
  else a

/-- Words: 1 delete, 2 backups, 3 loses, 4 data, 5 safe. The decision forbids
"delete backups". The claim that deleting backups loses data, the reason for the
prohibition, and its negation both drop to a tenth of their strength while
gaining confidence. Their strengths no longer sum to one. -/
theorem deontic_status_rewrites_truth :
    let reason : Atom := ⟨[1, 2, 3, 4], 80, 50⟩
    let negation : Atom := ⟨[1, 2, 5], 20, 50⟩
    forbidTruth [1, 2] reason = ⟨[1, 2, 3, 4], 8, 70⟩ ∧
      forbidTruth [1, 2] negation = ⟨[1, 2, 5], 2, 70⟩ ∧
      reason.strength + negation.strength = 100 ∧
      (forbidTruth [1, 2] reason).strength + (forbidTruth [1, 2] negation).strength = 10 := by
  decide

/-- `DeonticEnforcer.enforce` for a `forbidden` decision: STI times `0.2` for an
overlapping item. -/
def forbidAttention (keywords : List Nat) (words : List Nat) (sti : Nat) : Nat :=
  if words.any (fun w => keywords.contains w) then sti / 5 else sti

/-- The item stating the prohibition shares its keywords, so it loses four fifths
of its attention each time the decision is processed. -/
theorem prohibition_loses_attention :
    forbidAttention [1, 2] [6, 1, 2] 100 = 20 ∧
      forbidAttention [1, 2] [6, 1, 2] (forbidAttention [1, 2] [6, 1, 2] 100) = 4 := by
  decide

/-- The enforcer only lowers attention. It reads and writes no grant, approval or
monitor state, so it cannot block an authorized action. -/
theorem enforcement_only_lowers_attention (keywords words : List Nat) (sti : Nat) :
    forbidAttention keywords words sti ≤ sti := by
  unfold forbidAttention
  split
  · exact Nat.div_le_self sti 5
  · exact Nat.le_refl sti

end DeonticControl

/-! ## Axiom audit -/
#print axioms DeonticControl.deontic_filter_sound
#print axioms DeonticControl.dispatch_trusts_flag
#print axioms DeonticControl.revoke_is_inert
#print axioms DeonticControl.restart_reauthorizes
#print axioms DeonticControl.stepC_safe
#print axioms DeonticControl.runC_safe
#print axioms DeonticControl.revoked_stays_without_effect
#print axioms DeonticControl.effects_authorized_once
#print axioms DeonticControl.revision_aba
#print axioms DeonticControl.knowledge_time_monotone
#print axioms DeonticControl.stale_plan_step_runs
#print axioms DeonticControl.one_effect_per_revision
#print axioms DeonticControl.stop_mid_plan_ignored
#print axioms DeonticControl.stop_checked_per_dispatch
#print axioms DeonticControl.adapter_grant_expired_on_arrival
#print axioms DeonticControl.derived_item_becomes_observation
#print axioms DeonticControl.deontic_status_rewrites_truth
#print axioms DeonticControl.prohibition_loses_attention
#print axioms DeonticControl.enforcement_only_lowers_attention
