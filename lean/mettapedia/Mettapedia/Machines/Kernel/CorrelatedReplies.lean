import Mettapedia.Machines.Kernel.Delegation

/-!
# Bounded, correlated reply obligations

One caller owns a bounded window of outstanding calls. Each identity is fresh;
only the designated peer may claim and complete it. Completion retains the
value until consumption. Cancellation removes the obligation, not effects
already performed by a peer. A transport separately queues requests and proves
that its authenticated receiver is the actor passed to `claim` and `complete`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.CorrelatedReplies

inductive Phase where
  | queued | heard | ready (value : Nat)
  deriving DecidableEq, Repr

structure Call (Peer : Type) where
  id : Nat
  peer : Peer
  phase : Phase
  deriving DecidableEq, Repr

structure Window (Peer : Type) where
  issued : Nat
  calls : List (Call Peer)
  deriving DecidableEq, Repr

structure Config (Peer : Type) where
  capacity : Nat
  maxId : Nat
  allowed : Peer → Bool

inductive Result where
  | admitted (id : Nat)
  | value (word : Nat)
  | pending | refused | unavailable | exhausted | done
  deriving DecidableEq, Repr

variable {Peer : Type}

def lookup (w : Window Peer) (id : Nat) : Option (Call Peer) :=
  w.calls.find? fun c => c.id == id

def setPhase (w : Window Peer) (id : Nat) (phase : Phase) : Window Peer :=
  { w with calls := w.calls.map fun c => if c.id = id then { c with phase := phase } else c }

def remove (w : Window Peer) (id : Nat) : Window Peer :=
  { w with calls := w.calls.filter fun c => c.id != id }

def admit (config : Config Peer) (w : Window Peer) (peer : Peer)
    (registered room : Bool) : Window Peer × Result :=
  if !config.allowed peer then (w, .refused)
  else if !registered then (w, .unavailable)
  else if !room || w.calls.length ≥ config.capacity || w.issued ≥ config.maxId then (w, .exhausted)
  else
    let id := w.issued+1
    (⟨id, w.calls ++ [⟨id, peer, .queued⟩]⟩, .admitted id)

def claim [DecidableEq Peer] (w : Window Peer) (actor : Peer) (id : Nat) : Window Peer × Result :=
  match lookup w id with
  | some c =>
      if c.peer = actor ∧ c.phase = .queued then (setPhase w id .heard, .done)
      else (w, .refused)
  | none => (w, .refused)

def complete [DecidableEq Peer] (w : Window Peer) (actor : Peer) (id value : Nat) : Window Peer × Result :=
  match lookup w id with
  | some c =>
      if c.peer = actor ∧ c.phase = .heard then (setPhase w id (.ready value), .done)
      else (w, .refused)
  | none => (w, .refused)

def poll (w : Window Peer) (id : Nat) : Window Peer × Result :=
  match lookup w id with
  | some c => match c.phase with
      | .ready value => (remove w id, .value value)
      | _ => (w, .pending)
  | none => (w, .refused)

def cancel (w : Window Peer) (id : Nat) : Window Peer × Result :=
  if (lookup w id).isSome then (remove w id, .done) else (w, .refused)

structure Valid (config : Config Peer) (w : Window Peer) : Prop where
  bounded : w.calls.length ≤ config.capacity
  issuedBound : w.issued ≤ config.maxId
  fresh : ∀ c ∈ w.calls, 0 < c.id ∧ c.id ≤ w.issued
  unique : (w.calls.map Call.id).Nodup
  authority : ∀ c ∈ w.calls, config.allowed c.peer = true

theorem empty_valid (config : Config Peer) : Valid config ⟨0, []⟩ := by
  constructor <;> simp

theorem lookup_mem {w : Window Peer} {id : Nat} {c : Call Peer}
    (found : lookup w id = some c) : c ∈ w.calls ∧ c.id = id := by
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

theorem lookup_setPhase (w : Window Peer) (id : Nat) (phase : Phase) :
    lookup (setPhase w id phase) id = (lookup w id).map (fun c => { c with phase := phase }) := by
  rcases w with ⟨issued, calls⟩
  induction calls with
  | nil => rfl
  | cons c rest ih =>
      by_cases same : c.id = id <;> simp_all [lookup, setPhase]

theorem lookup_setPhase_other (w : Window Peer) (id other : Nat) (phase : Phase)
    (different : other ≠ id) : lookup (setPhase w id phase) other = lookup w other := by
  rcases w with ⟨issued, calls⟩
  induction calls with
  | nil => rfl
  | cons c rest ih =>
      by_cases same : c.id = id <;> by_cases hit : c.id = other <;>
        simp_all [lookup, setPhase]

theorem lookup_remove (w : Window Peer) (id : Nat) : lookup (remove w id) id = none := by
  unfold lookup remove
  rw [List.find?_eq_none]
  intro c member
  have h := (List.mem_filter.mp member).2
  simpa using h

theorem lookup_remove_other (w : Window Peer) (id other : Nat) (different : other ≠ id) :
    lookup (remove w id) other = lookup w other := by
  rcases w with ⟨issued, calls⟩
  induction calls with
  | nil => rfl
  | cons c rest ih =>
      by_cases same : c.id = id <;> by_cases hit : c.id = other <;>
        simp_all [lookup, remove]

theorem complete_requires_heard_peer [DecidableEq Peer] (w : Window Peer) (actor : Peer) (id value : Nat)
    (completed : (complete w actor id value).2 = .done) :
    ∃ c : Call Peer, lookup w id = some c ∧ c.peer = actor ∧ c.phase = .heard := by
  unfold complete at completed
  split at completed
  · split at completed
    · exact ⟨_, by assumption, by assumption⟩
    · contradiction
  · contradiction

theorem completion_retained [DecidableEq Peer] (w : Window Peer) (actor : Peer) (id value : Nat)
    (completed : (complete w actor id value).2 = .done) :
    ∃ c : Call Peer, lookup (complete w actor id value).1 id = some { c with phase := .ready value } := by
  obtain ⟨c, found, peer, heard⟩ := complete_requires_heard_peer w actor id value completed
  refine ⟨c, ?_⟩
  simp [complete, found, peer, heard, lookup_setPhase]

theorem completion_once [DecidableEq Peer] (w : Window Peer) (actor : Peer) (id value next : Nat)
    (completed : (complete w actor id value).2 = .done) :
    complete (complete w actor id value).1 actor id next =
      ((complete w actor id value).1, .refused) := by
  obtain ⟨c, found⟩ := completion_retained w actor id value completed
  rw [complete, found]
  simp

theorem poll_correct (w : Window Peer) (id value : Nat)
    (delivered : (poll w id).2 = .value value) :
    ∃ c : Call Peer, lookup w id = some c ∧ c.phase = .ready value ∧ (poll w id).1 = remove w id := by
  unfold poll at delivered ⊢
  split at delivered
  · rename_i c found
    split at delivered
    · rename_i actual phase
      cases Result.value.inj delivered
      exact ⟨c, found, phase, rfl⟩
    · contradiction
  · contradiction

theorem poll_consumes_once (w : Window Peer) (id value : Nat)
    (delivered : (poll w id).2 = .value value) :
    poll (poll w id).1 id = ((poll w id).1, .refused) := by
  obtain ⟨_, _, _, state⟩ := poll_correct w id value delivered
  simp only [state]
  rw [poll, lookup_remove]

theorem cancel_removes (w : Window Peer) (id : Nat) (cancelled : (cancel w id).2 = .done) :
    lookup (cancel w id).1 id = none := by
  unfold cancel at cancelled ⊢
  split at cancelled
  · simp_all [lookup_remove]
  · contradiction

theorem admit_fresh {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (peer : Peer) (registered room : Bool) (id : Nat)
    (accepted : (admit config w peer registered room).2 = .admitted id) :
    id = w.issued+1 ∧ ∀ c ∈ w.calls, c.id < id := by
  unfold admit at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  have same := Result.admitted.inj accepted
  refine ⟨same.symm, ?_⟩
  intro c member
  rw [← same]
  exact Nat.lt_succ_of_le (valid.fresh c member).2

theorem Valid.setPhase {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (id : Nat) (phase : Phase) : Valid config (setPhase w id phase) := by
  have identities : ((CorrelatedReplies.setPhase w id phase).calls.map Call.id) = w.calls.map Call.id := by
    simp only [CorrelatedReplies.setPhase, List.map_map]
    congr 1
    funext c
    simp only [Function.comp_apply]
    split <;> rfl
  constructor
  · simpa [CorrelatedReplies.setPhase] using valid.bounded
  · exact valid.issuedBound
  · intro c member
    obtain ⟨original, present, eq⟩ := List.mem_map.mp member
    subst c
    split <;> exact valid.fresh original present
  · rw [identities]
    exact valid.unique
  · intro c member
    obtain ⟨original, present, eq⟩ := List.mem_map.mp member
    subst c
    split <;> exact valid.authority original present

theorem remove_identities (w : Window Peer) (id : Nat) :
    (remove w id).calls.map Call.id = (w.calls.map Call.id).filter (fun n => n != id) := by
  rcases w with ⟨issued,calls⟩
  induction calls with
  | nil => rfl
  | cons c rest ih =>
      by_cases same : c.id = id <;> simp_all [remove]

theorem Valid.remove {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (id : Nat) : Valid config (remove w id) := by
  constructor
  · exact Nat.le_trans (List.length_filter_le _ _) valid.bounded
  · exact valid.issuedBound
  · intro c member
    exact valid.fresh c (List.mem_filter.mp member).1
  · rw [remove_identities]
    exact valid.unique.filter _
  · intro c member
    exact valid.authority c (List.mem_filter.mp member).1

theorem Valid.claim [DecidableEq Peer] {config : Config Peer} {w : Window Peer}
    (valid : Valid config w) (actor : Peer) (id : Nat) : Valid config (claim w actor id).1 := by
  unfold CorrelatedReplies.claim
  split
  · split
    · exact valid.setPhase id .heard
    · exact valid
  · exact valid

theorem Valid.complete [DecidableEq Peer] {config : Config Peer} {w : Window Peer}
    (valid : Valid config w) (actor : Peer) (id value : Nat) : Valid config (complete w actor id value).1 := by
  unfold CorrelatedReplies.complete
  split
  · split
    · exact valid.setPhase id (.ready value)
    · exact valid
  · exact valid

theorem Valid.poll {config : Config Peer} {w : Window Peer}
    (valid : Valid config w) (id : Nat) : Valid config (poll w id).1 := by
  unfold CorrelatedReplies.poll
  split
  · split
    · exact valid.remove id
    · exact valid
  · exact valid

theorem Valid.cancel {config : Config Peer} {w : Window Peer}
    (valid : Valid config w) (id : Nat) : Valid config (cancel w id).1 := by
  unfold CorrelatedReplies.cancel
  split
  · exact valid.remove id
  · exact valid

theorem Valid.append_call {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (peer : Peer) (allowed : config.allowed peer = true)
    (space : w.calls.length < config.capacity) (identity : w.issued < config.maxId) :
    Valid config ⟨w.issued+1,w.calls ++ [⟨w.issued+1,peer,.queued⟩]⟩ := by
  constructor
  · simpa using Nat.succ_le_of_lt space
  · exact Nat.succ_le_of_lt identity
  · intro c member
    rcases List.mem_append.mp member with old | new
    · exact ⟨(valid.fresh c old).1,Nat.le.step (valid.fresh c old).2⟩
    · have eq := List.mem_singleton.mp new
      subst c
      exact ⟨Nat.zero_lt_succ _,Nat.le_refl _⟩
  · simp only [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨valid.unique, by simp, ?_⟩
    intro a member b singleton
    have eq := List.mem_singleton.mp singleton
    subst b
    obtain ⟨c,present,same⟩ := List.mem_map.mp member
    subst a
    exact Nat.ne_of_lt (Nat.lt_succ_of_le (valid.fresh c present).2)
  · intro c member
    rcases List.mem_append.mp member with old | new
    · exact valid.authority c old
    · have eq := List.mem_singleton.mp new
      subst c
      exact allowed

theorem Valid.admit {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (peer : Peer) (registered room : Bool) : Valid config (admit config w peer registered room).1 := by
  unfold CorrelatedReplies.admit
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · apply valid.append_call peer
        · cases h : config.allowed peer <;> simp_all
        · simp_all
        · simp_all

inductive Op (Peer : Type) where
  | admit (peer : Peer) (registered room : Bool)
  | claim (actor : Peer) (id : Nat)
  | complete (actor : Peer) (id value : Nat)
  | poll (id : Nat)
  | cancel (id : Nat)
  deriving DecidableEq, Repr

def step [DecidableEq Peer] (config : Config Peer) (w : Window Peer) : Op Peer → Window Peer × Result
  | .admit peer registered room => admit config w peer registered room
  | .claim actor id => claim w actor id
  | .complete actor id value => complete w actor id value
  | .poll id => poll w id
  | .cancel id => cancel w id

def run [DecidableEq Peer] (config : Config Peer) (w : Window Peer) : List (Op Peer) → Window Peer
  | [] => w
  | op :: rest => run config (step config w op).1 rest

theorem Valid.step [DecidableEq Peer] {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (op : Op Peer) : Valid config (step config w op).1 := by
  cases op with
  | admit peer registered room => exact valid.admit peer registered room
  | claim actor id => exact valid.claim actor id
  | complete actor id value => exact valid.complete actor id value
  | poll id => exact valid.poll id
  | cancel id => exact valid.cancel id

theorem Valid.run [DecidableEq Peer] {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (ops : List (Op Peer)) : Valid config (run config w ops) := by
  induction ops generalizing w with
  | nil => exact valid
  | cons op rest ih => exact ih (valid.step op)

theorem step_issued_monotone [DecidableEq Peer] (config : Config Peer) (w : Window Peer) (op : Op Peer) :
    w.issued ≤ (step config w op).1.issued := by
  cases op with
  | admit peer registered room =>
      simp only [step, admit]
      split <;> (try exact Nat.le_refl _)
      split <;> (try exact Nat.le_refl _)
      split <;> simp
  | claim actor id =>
      simp only [step, claim]
      split <;> (try exact Nat.le_refl _)
      split <;> exact Nat.le_refl _
  | complete actor id value =>
      simp only [step, complete]
      split <;> (try exact Nat.le_refl _)
      split <;> exact Nat.le_refl _
  | poll id =>
      simp only [step, poll]
      split <;> (try exact Nat.le_refl _)
      split <;> exact Nat.le_refl _
  | cancel id => simp only [step, cancel]; split <;> exact Nat.le_refl _

theorem lookup_setPhase_absent (w : Window Peer) (id other : Nat) (phase : Phase)
    (absent : lookup w other = none) : lookup (setPhase w id phase) other = none := by
  by_cases same : other = id
  · subst other; simp [lookup_setPhase, absent]
  · rw [lookup_setPhase_other w id other phase same]
    exact absent

theorem lookup_remove_absent (w : Window Peer) (id other : Nat)
    (absent : lookup w other = none) : lookup (remove w id) other = none := by
  by_cases same : other = id
  · subst other; exact lookup_remove w id
  · rw [lookup_remove_other w id other same]
    exact absent

theorem old_identity_stays_absent [DecidableEq Peer] (config : Config Peer) (w : Window Peer)
    (id : Nat) (old : id ≤ w.issued) (absent : lookup w id = none) (op : Op Peer) :
    lookup (step config w op).1 id = none := by
  cases op with
  | admit peer registered room =>
      simp only [step, admit]
      split <;> (try exact absent)
      split <;> (try exact absent)
      split
      · exact absent
      · have different : w.issued+1 ≠ id := Nat.ne_of_gt (Nat.lt_succ_of_le old)
        simpa [lookup, List.find?_append, different] using absent
  | claim actor target =>
      simp only [step, claim]
      split <;> (try exact absent)
      split
      · exact lookup_setPhase_absent w target id .heard absent
      · exact absent
  | complete actor target value =>
      simp only [step, complete]
      split <;> (try exact absent)
      split
      · exact lookup_setPhase_absent w target id (.ready value) absent
      · exact absent
  | poll target =>
      simp only [step, poll]
      split <;> (try exact absent)
      split
      · exact lookup_remove_absent w target id absent
      · exact absent
  | cancel target =>
      simp only [step, cancel]
      split
      · exact lookup_remove_absent w target id absent
      · exact absent

theorem old_identity_stays_absent_run [DecidableEq Peer] (config : Config Peer) (w : Window Peer)
    (id : Nat) (old : id ≤ w.issued) (absent : lookup w id = none) (ops : List (Op Peer)) :
    lookup (run config w ops) id = none := by
  induction ops generalizing w with
  | nil => exact absent
  | cons op rest ih =>
      exact ih _ (Nat.le_trans old (step_issued_monotone config w op))
        (old_identity_stays_absent config w id old absent op)

theorem complete_preserves_other [DecidableEq Peer] (w : Window Peer) (actor : Peer)
    (id other value : Nat) (different : other ≠ id) :
    lookup (complete w actor id value).1 other = lookup w other := by
  unfold complete
  split <;> (try rfl)
  split
  · exact lookup_setPhase_other w id other (.ready value) different
  · rfl

/-- Once a reply is consumed, arbitrary later admissible operations cannot
make that identity authorize another completion. A later call has a fresh
identity even when it belongs to the same caller and peer. -/
theorem consumed_reply_stays_refused [DecidableEq Peer]
    {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (id value : Nat) (delivered : (poll w id).2 = .value value)
    (ops : List (Op Peer)) (actor : Peer) (late : Nat) :
    let after := run config (poll w id).1 ops
    complete after actor id late = (after, .refused) := by
  obtain ⟨call, found, _, state⟩ := poll_correct w id value delivered
  have old : id ≤ (poll w id).1.issued := by
    rw [state]
    exact (lookup_mem found).2 ▸ (valid.fresh call (lookup_mem found).1).2
  have absent : lookup (poll w id).1 id = none := by
    rw [state, lookup_remove]
  have stillAbsent := old_identity_stays_absent_run config (poll w id).1 id old absent ops
  simp only [complete, stillAbsent]

/-- Cancellation removes the reply obligation permanently. This concerns
delivery authority, without asserting that a peer performed no effect. -/
theorem cancelled_reply_stays_refused [DecidableEq Peer]
    {config : Config Peer} {w : Window Peer} (valid : Valid config w)
    (id : Nat) (cancelled : (cancel w id).2 = .done)
    (ops : List (Op Peer)) (actor : Peer) (late : Nat) :
    let after := run config (cancel w id).1 ops
    complete after actor id late = (after, .refused) := by
  have present : (lookup w id).isSome = true := by
    unfold cancel at cancelled
    split at cancelled
    · assumption
    · contradiction
  obtain ⟨call, found⟩ := Option.isSome_iff_exists.mp present
  have old : id ≤ (cancel w id).1.issued := by
    simpa [cancel, present, remove] using
      ((lookup_mem found).2 ▸ (valid.fresh call (lookup_mem found).1).2)
  have stillAbsent := old_identity_stays_absent_run config (cancel w id).1 id old
    (cancel_removes w id cancelled) ops
  simp only [complete, stillAbsent]

namespace Controls

def oneSlot : Config Nat := ⟨1, 8, fun peer => decide (peer = 0)⟩
def first : Window Nat := ⟨1, [⟨1, 0, .heard⟩]⟩
def next : Window Nat :=
  run oneSlot (poll (complete first 0 1 7).1 1).1 [.admit 0 true true, .claim 0 2]

/-- Two successive requests share a peer but never their reply authority. -/
theorem stale_request_cannot_answer_next :
    next = ⟨2, [⟨2, 0, .heard⟩]⟩ ∧
      complete next 0 1 99 = (next, .refused) ∧
      complete next 0 2 8 = (⟨2, [⟨2, 0, .ready 8⟩]⟩, .done) := by decide

/-- Retargeting an old reply to the current request loses correlation and
allows its value into the wrong continuation. The supplied identity matters. -/
theorem replacing_supplied_identity_accepts_wrong_reply :
    (complete next 0 1 99).2 = .refused ∧
      (poll (complete next 0 next.issued 99).1 next.issued).2 = .value 99 := by decide

end Controls

#print axioms consumed_reply_stays_refused
#print axioms cancelled_reply_stays_refused
#print axioms Controls.stale_request_cannot_answer_next
#print axioms Controls.replacing_supplied_identity_accepts_wrong_reply

theorem run_confined [DecidableEq Peer] (config : Config Peer) (ops : List (Op Peer))
    (c : Call Peer) (present : c ∈ (run config ⟨0,[]⟩ ops).calls) : config.allowed c.peer = true :=
  ((empty_valid config).run ops).authority c present

end Mettapedia.Machines.Kernel.CorrelatedReplies
