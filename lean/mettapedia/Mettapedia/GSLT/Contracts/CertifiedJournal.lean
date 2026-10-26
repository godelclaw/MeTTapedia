import Mettapedia.GSLT.Contracts.Quorums
import Mettapedia.GSLT.Contracts.AppendAuthority
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Powerset

/-!
# A certified append journal with durable votes

An honest replica persists one proposal per service and position before
emitting its vote. Proposals bind the entire parent prefix, request identity
and entry. Network evidence consists of authenticated sender/proposal pairs;
the adversary may send arbitrary proposals as faulty senders, but cannot
forge another sender. This is an ideal authentication boundary, not an
implementation of cryptography.

Certificates establish agreement, not factual truth. Safety survives delays,
reordering, replay and crashes retaining stable storage. This protocol has no
leader-change mechanism: split votes can block forever. Progress below is
only for an uncontended position with enough available compatible voters.
The quorum mathematics is classical Byzantine quorum theory; see
https://arxiv.org/abs/1803.05069 for the broader consensus setting.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.CertifiedJournal

variable {V Scope Entry : Type*} [DecidableEq V] [DecidableEq Scope] [DecidableEq Entry]

structure Proposal (Scope Entry : Type*) where
  service : Scope
  parent : List Entry
  request : Nat
  entry : Entry
  deriving DecidableEq

def Proposal.key (p : Proposal Scope Entry) : Scope × Nat := (p.service, p.parent.length)

structure State (V Scope Entry : Type*) where
  stable : V × (Scope × Nat) → Option (Proposal Scope Entry)
  sent : Finset (V × Proposal Scope Entry)
  inbox : Finset (V × Proposal Scope Entry)
  saved : V × Scope → List (Proposal Scope Entry × Finset V)

def initial : State V Scope Entry := ⟨fun _ => none, ∅, ∅, fun _ => []⟩

/-- The honest handler uses only its own persistent vote, not a fault oracle. -/
def vote (s : State V Scope Entry) (v : V) (p : Proposal Scope Entry) :
    Option (State V Scope Entry) :=
  if s.stable (v, p.key) = none ∨ s.stable (v, p.key) = some p then
    some { s with
      stable := Function.update s.stable (v, p.key) (some p)
      sent := insert (v, p) s.sent }
  else none

def HonestLog (faulty : Finset V) (s : State V Scope Entry) : Prop :=
  ∀ v p, (v, p) ∈ s.sent → v ∉ faulty → s.stable (v, p.key) = some p

theorem vote_recorded {s t : State V Scope Entry} {v : V} {p : Proposal Scope Entry}
    (accepted : vote s v p = some t) :
    t.stable (v, p.key) = some p ∧ (v, p) ∈ t.sent := by
  unfold vote at accepted
  split at accepted
  · cases Option.some.inj accepted
    simp
  · cases accepted

omit [DecidableEq Scope] [DecidableEq Entry] in
theorem initial_honest (faulty : Finset V) : HonestLog faulty (initial : State V Scope Entry) := by
  simp [HonestLog, initial]

theorem vote_honest (faulty : Finset V) (s t : State V Scope Entry)
    (v : V) (p : Proposal Scope Entry) (before : HonestLog faulty s)
    (accepted : vote s v p = some t) : HonestLog faulty t := by
  unfold vote at accepted
  split at accepted
  next allowed =>
    cases Option.some.inj accepted
    intro w r member honest
    rcases Finset.mem_insert.mp member with equal | old
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      simp
    · have previous := before w r old honest
      by_cases same : (w, r.key) = (v, p.key)
      · have value : r = p := by
          have prev : s.stable (v, p.key) = some r := same ▸ previous
          rcases allowed with absent | agrees
          · rw [prev] at absent
            cases absent
          · exact Option.some.inj (prev.symm.trans agrees)
        change Function.update s.stable (v, p.key) (some p) (w, r.key) = some r
        rw [same, Function.update_self, value]
      · simpa only [Function.update_of_ne same] using previous
  next => cases accepted

/-- Only the environment's adversary transition consults the specified fault set. -/
def inject (s : State V Scope Entry) (v : V) (p : Proposal Scope Entry) : State V Scope Entry :=
  { s with sent := insert (v, p) s.sent }

theorem inject_honest (faulty : Finset V) (s : State V Scope Entry)
    (v : V) (p : Proposal Scope Entry) (bad : v ∈ faulty) (before : HonestLog faulty s) :
    HonestLog faulty (inject s v p) := by
  intro w r member honest
  rcases Finset.mem_insert.mp member with equal | old
  · have eqWV : w = v := congrArg Prod.fst equal
    exact False.elim (honest (eqWV.symm ▸ bad))
  · exact before w r old honest

/-- A crash discards volatile received evidence, preserving stable votes. -/
def crash (s : State V Scope Entry) : State V Scope Entry := { s with inbox := ∅ }

/-- The network delivers a previously emitted authenticated message; delivery
may be repeated and arbitrarily reordered. Missing messages are not invented. -/
def receive (s : State V Scope Entry) (message : V × Proposal Scope Entry) : State V Scope Entry :=
  if message ∈ s.sent then { s with inbox := insert message s.inbox } else s

theorem receive_authentic (s : State V Scope Entry) (message : V × Proposal Scope Entry)
    (before : s.inbox ⊆ s.sent) : (receive s message).inbox ⊆ (receive s message).sent := by
  unfold receive
  split
  · exact Finset.insert_subset_iff.mpr ⟨by assumption, before⟩
  · exact before

theorem receive_honest (faulty : Finset V) (s : State V Scope Entry)
    (message : V × Proposal Scope Entry) (before : HonestLog faulty s) :
    HonestLog faulty (receive s message) := by
  unfold receive
  split <;> exact before

theorem persisted_vote_refuses_conflict (s : State V Scope Entry) (v : V)
    (p r : Proposal Scope Entry) (stored : s.stable (v, p.key) = some p)
    (same : p.key = r.key) (different : p ≠ r) : vote (crash s) v r = none := by
  simp [vote, crash, ← same, stored, different]

omit [DecidableEq V] [DecidableEq Scope] [DecidableEq Entry] in
theorem crash_honest (faulty : Finset V) (s : State V Scope Entry)
    (before : HonestLog faulty s) : HonestLog faulty (crash s) := before

omit [DecidableEq V] [DecidableEq Scope] [DecidableEq Entry] in
theorem crash_retains_certified_storage (s : State V Scope Entry) : (crash s).saved = s.saved := rfl

inductive Step (faulty : Finset V) : State V Scope Entry → State V Scope Entry → Prop where
  | vote {s t v p} : vote s v p = some t → Step faulty s t
  | adversary {s v p} : v ∈ faulty → Step faulty s (inject s v p)
  | crash {s} : Step faulty s (crash s)
  | receive {s message} : Step faulty s (receive s message)

theorem reached_honest (faulty : Finset V) {s t : State V Scope Entry}
    (before : HonestLog faulty s) (trace : Relation.ReflTransGen (Step faulty) s t) :
    HonestLog faulty t := by
  induction trace with
  | refl => exact before
  | tail _ move ih =>
    cases move with
    | vote accepted => exact vote_honest faulty _ _ _ _ ih accepted
    | adversary bad => exact inject_honest faulty _ _ _ bad ih
    | crash => exact crash_honest faulty _ ih
    | receive => exact receive_honest faulty _ _ ih

theorem step_sent_grows (faulty : Finset V) {s t : State V Scope Entry}
    (move : Step faulty s t) : s.sent ⊆ t.sent := by
  cases move with
  | vote accepted =>
    unfold vote at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Finset.subset_insert _ _
    · cases accepted
  | adversary => exact Finset.subset_insert _ _
  | crash => exact Finset.Subset.refl _
  | receive => unfold receive; split <;> exact Finset.Subset.refl _

theorem reached_sent_grows (faulty : Finset V) {s t : State V Scope Entry}
    (trace : Relation.ReflTransGen (Step faulty) s t) : s.sent ⊆ t.sent := by
  induction trace with
  | refl => exact Finset.Subset.refl _
  | tail _ move ih => exact ih.trans (step_sent_grows faulty move)

theorem step_inbox_authentic (faulty : Finset V) {s t : State V Scope Entry}
    (before : s.inbox ⊆ s.sent) (move : Step faulty s t) : t.inbox ⊆ t.sent := by
  cases move with
  | vote accepted =>
    unfold vote at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact before.trans (Finset.subset_insert _ _)
    · cases accepted
  | adversary => exact before.trans (Finset.subset_insert _ _)
  | crash => exact Finset.empty_subset _
  | receive => exact receive_authentic _ _ before

/-- Verification reads the supplied local evidence; distinct senders count once. -/
def Certificate (threshold : Nat) (view : Finset (V × Proposal Scope Entry))
    (p : Proposal Scope Entry) (signers : Finset V) : Prop :=
  threshold ≤ signers.card ∧ ∀ v ∈ signers, (v, p) ∈ view

instance (threshold : Nat) (view : Finset (V × Proposal Scope Entry))
    (p : Proposal Scope Entry) (signers : Finset V) :
    Decidable (Certificate threshold view p signers) := by
  unfold Certificate
  infer_instance

omit [DecidableEq V] [DecidableEq Scope] [DecidableEq Entry] in
theorem certificate_mono {threshold : Nat} {view larger : Finset (V × Proposal Scope Entry)}
    {p : Proposal Scope Entry} {signers : Finset V} (included : view ⊆ larger)
    (cert : Certificate threshold view p signers) : Certificate threshold larger p signers :=
  ⟨cert.1, fun v member => included (cert.2 v member)⟩

omit [DecidableEq Scope] [DecidableEq Entry] in
theorem certificates_agree [Fintype V] (faulty : Finset V) (f : Nat)
    (resilience : 3 * f + 1 ≤ Fintype.card V) (bad : faulty.card ≤ f)
    (s : State V Scope Entry) (honesty : HonestLog faulty s)
    {p r : Proposal Scope Entry} {a b : Finset V}
    (first : Certificate (Fintype.card V - f) s.sent p a)
    (second : Certificate (Fintype.card V - f) s.sent r b) (same : p.key = r.key) : p = r := by
  obtain ⟨v, va, vb, good⟩ := Quorums.honest_intersection faulty a b f resilience bad first.1 second.1
  have hp := honesty v p (first.2 v va) good
  have hr := honesty v r (second.2 v vb) good
  rw [same] at hp
  exact Option.some.inj (hp.symm.trans hr)

theorem certificates_across_time [Fintype V] (faulty : Finset V) (f : Nat)
    (resilience : 3 * f + 1 ≤ Fintype.card V) (bad : faulty.card ≤ f)
    {s t : State V Scope Entry} (honesty : HonestLog faulty s)
    (trace : Relation.ReflTransGen (Step faulty) s t)
    {p r : Proposal Scope Entry} {a b : Finset V}
    (earlier : Certificate (Fintype.card V - f) s.sent p a)
    (later : Certificate (Fintype.card V - f) t.sent r b) (same : p.key = r.key) : p = r :=
  certificates_agree faulty f resilience bad t (reached_honest faulty honesty trace)
    (certificate_mono (reached_sent_grows faulty trace) earlier) later same

def Certified (threshold : Nat) (s : State V Scope Entry) (p : Proposal Scope Entry) : Prop :=
  ∃ signers, Certificate threshold s.sent p signers

instance [Fintype V] (threshold : Nat) (s : State V Scope Entry) (p : Proposal Scope Entry) :
    Decidable (Certified threshold s p) := by
  unfold Certified
  infer_instance

/-- Every entry has its own certificate and names the actual preceding entries. -/
def ValidLog (threshold : Nat) (s : State V Scope Entry) (service : Scope)
    (log : List (Proposal Scope Entry)) : Prop :=
  ∀ i : Fin log.length,
    (log[i]).service = service ∧
    (log[i]).parent = (log.take i).map Proposal.entry ∧ Certified threshold s log[i]

omit [DecidableEq Scope] [DecidableEq Entry] in
theorem valid_logs_prefix [Fintype V] (faulty : Finset V) (f : Nat)
    (resilience : 3 * f + 1 ≤ Fintype.card V) (bad : faulty.card ≤ f)
    (s : State V Scope Entry) (honesty : HonestLog faulty s) (service : Scope)
    (left right : List (Proposal Scope Entry))
    (a : ValidLog (Fintype.card V - f) s service left)
    (b : ValidLog (Fintype.card V - f) s service right) :
    left <+: right ∨ right <+: left := by
  have agrees (i : Nat) (hi : i < left.length) (hj : i < right.length) : left[i] = right[i] := by
    obtain ⟨ls, lp, lv, lc⟩ := a ⟨i, hi⟩
    obtain ⟨rs, rp, rv, rc⟩ := b ⟨i, hj⟩
    apply certificates_agree faulty f resilience bad s honesty lc rc
    simp only [Proposal.key, ls, rs, lp, rp, List.length_map, List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (Nat.le_of_lt hj)]
  rcases Nat.le_total left.length right.length with h | h
  · exact Or.inl (List.prefix_iff_getElem.mpr ⟨h, fun i hi => agrees i hi (lt_of_lt_of_le hi h)⟩)
  · exact Or.inr (List.prefix_iff_getElem.mpr ⟨h, fun i hi => (agrees i (lt_of_lt_of_le hi h) hi).symm⟩)

structure ReplayState (X : Type*) where
  processed : Finset Nat
  value : X
  deriving DecidableEq

def applyOnce {X : Type*} (apply : X → Entry → X) (s : ReplayState X)
    (p : Proposal Scope Entry) : ReplayState X :=
  if p.request ∈ s.processed then s
  else ⟨insert p.request s.processed, apply s.value p.entry⟩

omit [DecidableEq Scope] [DecidableEq Entry] in
theorem duplicate_suppressed {X : Type*} (apply : X → Entry → X) (s : ReplayState X)
    (p : Proposal Scope Entry) : applyOnce apply (applyOnce apply s p) p = applyOnce apply s p := by
  by_cases h : p.request ∈ s.processed <;> simp [applyOnce, h]

/-- Recovery computes the state from a checked log, rather than trusting a snapshot. -/
def replay {X : Type*} (apply : X → Entry → X) (start : X)
    (log : List (Proposal Scope Entry)) : ReplayState X :=
  log.foldl (applyOnce apply) ⟨∅, start⟩

omit [DecidableEq Scope] [DecidableEq Entry] in
theorem replay_append {X : Type*} (apply : X → Entry → X) (start : X)
    (first second : List (Proposal Scope Entry)) :
    replay apply start (first ++ second) = second.foldl (applyOnce apply) (replay apply start first) :=
  List.foldl_append

omit [DecidableEq Scope] [DecidableEq Entry] in
/-- Available compatible votes suffice; this says nothing about resolving split votes. -/
theorem uncontended_certificate [Fintype V] (faulty : Finset V) (f : Nat)
    (bad : faulty.card ≤ f) (s : State V Scope Entry) (p : Proposal Scope Entry)
    (delivered : ∀ v ∉ faulty, (v, p) ∈ s.inbox) :
    Certificate (Fintype.card V - f) s.inbox p (Finset.univ \ faulty) :=
  ⟨(Quorums.honest_available faulty f bad).1,
    fun v member => delivered v (Finset.mem_sdiff.mp member).2⟩

omit [DecidableEq Scope] [DecidableEq Entry] in
/-- Fair delivery of each member of a finite quorum yields a certificate at
some common stage. Votes may arrive in any order and at different times. -/
theorem eventually_certificate (threshold : Nat) (views : Nat → Finset (V × Proposal Scope Entry))
    (persistent : Monotone views) (p : Proposal Scope Entry) (signers : Finset V)
    (enough : threshold ≤ signers.card)
    (fair : ∀ v ∈ signers, ∃ t, (v, p) ∈ views t) :
    ∃ t, Certificate threshold (views t) p signers := by
  have collect : ∀ voters : Finset V,
      (∀ v ∈ voters, ∃ t, (v, p) ∈ views t) → ∃ t, ∀ v ∈ voters, (v, p) ∈ views t := by
    intro voters
    induction voters using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert v voters absent ih =>
      intro delivered
      obtain ⟨first, atFirst⟩ := delivered v (by simp)
      obtain ⟨rest, atRest⟩ := ih (fun w member => delivered w (Finset.mem_insert_of_mem member))
      refine ⟨max first rest, ?_⟩
      intro w member
      rcases Finset.mem_insert.mp member with rfl | old
      · exact persistent (Nat.le_max_left _ _) atFirst
      · exact persistent (Nat.le_max_right _ _) (atRest w old)
  obtain ⟨t, all⟩ := collect signers fair
  exact ⟨t, enough, all⟩

/-- A snapshot is accepted only through its complete certified parent chain. -/
def checkLog (threshold : Nat) (s : State V Scope Entry) (service : Scope)
    (records : List (Proposal Scope Entry × Finset V)) : Bool :=
  decide (∀ i : Fin records.length,
    (records[i]).1.service = service ∧
    (records[i]).1.parent = (records.take i).map (fun r => r.1.entry) ∧
    Certificate threshold s.inbox (records[i]).1 (records[i]).2)

theorem checkLog_sound (threshold : Nat) (s : State V Scope Entry) (service : Scope)
    (records : List (Proposal Scope Entry × Finset V)) (authentic : s.inbox ⊆ s.sent)
    (checked : checkLog threshold s service records = true) :
    ValidLog threshold s service (records.map Prod.fst) := by
  have all := of_decide_eq_true checked
  intro i
  have hi : i.val < records.length := by simpa using i.isLt
  obtain ⟨scope, parent, cert⟩ := all ⟨i.val, hi⟩
  simpa only [Fin.getElem_fin, List.getElem_map, ← List.map_take, List.map_map,
    Function.comp_def, Certified] using
    And.intro scope (And.intro parent (Exists.intro (records[i.val]).2
      (certificate_mono authentic cert)))

def recoverChecked {X : Type*} (threshold : Nat) (s : State V Scope Entry) (service : Scope)
    (records : List (Proposal Scope Entry × Finset V)) (apply : X → Entry → X) (start : X) :
    Option (ReplayState X) :=
  if checkLog threshold s service records then some (replay apply start (records.map Prod.fst))
  else none

theorem recoverChecked_refuses {X : Type*} (threshold : Nat) (s : State V Scope Entry)
    (service : Scope) (records : List (Proposal Scope Entry × Finset V))
    (apply : X → Entry → X) (start : X) :
    recoverChecked threshold s service records apply start = none ↔
      checkLog threshold s service records = false := by
  simp [recoverChecked]

/-- Atomic stable publication stores the checked entries and their signer
certificates. A new checkpoint must extend the previous one. -/
def persist (threshold : Nat) (s : State V Scope Entry) (replica : V) (service : Scope)
    (records : List (Proposal Scope Entry × Finset V)) : Option (State V Scope Entry) :=
  if checkLog threshold s service records ∧ s.saved (replica, service) <+: records then
    some { s with saved := Function.update s.saved (replica, service) records }
  else none

theorem persist_retains_checked_prefix (threshold : Nat) (s t : State V Scope Entry)
    (replica : V) (service : Scope) (records : List (Proposal Scope Entry × Finset V))
    (authentic : s.inbox ⊆ s.sent) (saved : persist threshold s replica service records = some t) :
    t.saved (replica, service) = records ∧ s.saved (replica, service) <+: records ∧
      ValidLog threshold t service ((t.saved (replica, service)).map Prod.fst) := by
  unfold persist at saved
  split at saved
  next checked =>
    cases Option.some.inj saved
    refine ⟨by simp, checked.2, ?_⟩
    change ValidLog threshold s service
      ((Function.update s.saved (replica, service) records (replica, service)).map Prod.fst)
    rw [Function.update_self]
    exact checkLog_sound threshold s service records authentic checked.1
  next => cases saved

/-- Recovery replays durable certified entries, never a supplied mutable
state snapshot. Availability of this storage is separate from network progress. -/
def recoverSaved {X : Type*} (s : State V Scope Entry) (replica : V) (service : Scope)
    (apply : X → Entry → X) (start : X) : ReplayState X :=
  replay apply start ((s.saved (replica, service)).map Prod.fst)

omit [DecidableEq V] [DecidableEq Scope] [DecidableEq Entry] in
theorem saved_recovery_survives_crash {X : Type*} (s : State V Scope Entry)
    (replica : V) (service : Scope) (apply : X → Entry → X) (start : X) :
    recoverSaved (crash s) replica service apply start = recoverSaved s replica service apply start := rfl

namespace Controls

def proposal (value : Bool) : Proposal Unit Bool := ⟨(), [], 0, value⟩

def published : State (Fin 4) Unit Bool :=
  ⟨fun _ => some (proposal true),
    {(0, proposal true), (1, proposal true), (2, proposal true)},
    {(0, proposal true), (1, proposal true), (2, proposal true)}, fun _ => []⟩

theorem successful_publication :
    checkLog 3 published () [(proposal true, {0, 1, 2})] = true := by decide

theorem incomplete_snapshot_refused :
    checkLog 3 { published with inbox := {(0, proposal true), (1, proposal true)} }
      () [(proposal true, {0, 1, 2})] = false := by decide

theorem wrong_parent_refused :
    checkLog 3 published () [(⟨(), [true], 1, false⟩, {0, 1, 2})] = false := by decide

def persisted : State (Fin 4) Unit Bool :=
  (persist 3 published 0 () [(proposal true, {0, 1, 2})]).getD initial

theorem persisted_crash_recovery :
    (recoverSaved (crash persisted) 0 () (fun (n : Nat) (_ : Bool) => n + 1) 0).value = 1 := by decide

theorem certified_storage_does_not_rewind :
    (persist 3 persisted 0 () []).isNone = true := by decide

theorem certification_is_not_truth :
    checkLog 3 published () [(proposal true, {0, 1, 2})] = true ∧
    (proposal true).entry ≠ false := by decide

theorem duplicate_request_once :
    (replay (fun (n : Nat) (_ : Bool) => n + 1) 0 [proposal true, proposal true]).value = 1 := by
  decide

def splitVotes : State (Fin 4) Unit Bool :=
  ⟨fun key => if key.1 = 0 ∨ key.1 = 1 then some (proposal true) else some (proposal false),
    {(0, proposal true), (1, proposal true), (2, proposal false), (3, proposal false)}, ∅, fun _ => []⟩

theorem split_votes_block :
    ¬ Certified 3 splitVotes (proposal true) ∧ ¬ Certified 3 splitVotes (proposal false) := by
  decide

/-- Forgetting stable votes permits the same honest identity to vote twice. -/
theorem lost_storage_allows_conflict :
    (vote (initial : State (Fin 4) Unit Bool) 0 (proposal true)).isSome = true ∧
    (vote (initial : State (Fin 4) Unit Bool) 0 (proposal false)).isSome = true := by decide

theorem durable_crash_blocks_conflict :
    vote (crash published) 0 (proposal false) = none := by
  apply persisted_vote_refuses_conflict published 0 (proposal true) (proposal false) rfl rfl
  decide

def honestPublication : Option (State (Fin 4) Unit Bool) := do
  let s ← vote initial 0 (proposal true)
  let s ← vote s 1 (proposal true)
  vote s 2 (proposal true)

theorem emitted_publication :
    (match honestPublication with
     | none => false
     | some s => checkLog 3 { s with inbox := s.sent } () [(proposal true, {0, 1, 2})]) = true := by
  decide

/-- One Byzantine sender and one honest sender whose disk was rolled back
can produce incompatible three-of-four certificates. The normal crash rule
does not permit this rollback. -/
theorem rollback_destroys_safety :
    let messages : Finset (Fin 4 × Proposal Unit Bool) :=
      {(0, proposal true), (0, proposal false), (1, proposal true),
       (1, proposal false), (2, proposal true), (3, proposal false)}
    Certificate 3 messages (proposal true) {0, 1, 2} ∧
    Certificate 3 messages (proposal false) {0, 1, 3} := by decide

end Controls

end Mettapedia.GSLT.Contracts.CertifiedJournal
