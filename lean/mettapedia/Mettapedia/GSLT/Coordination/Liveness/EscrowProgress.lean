import Mettapedia.GSLT.Coordination.Escrow

/-!
# Escrow rebalancing makes progress

`Coordination.Escrow` splits a budget into shares spent locally, and shows that a spend larger than
the local share must wait for a rebalance (`Escrow.Controls.large_spend_needs_rebalance`). This
module proves that the wait ends: one **rebalancing round** toward a site gives it the whole
remaining budget, so every spend not larger than the remaining budget is accepted after it.

## The round (`rebalance`)

1. Deliver every transfer sent so far (duplicates and already applied ones change nothing).
2. Every other site sends its whole share to the requesting site, under fresh identifiers.
3. Deliver those transfers.

## Theorems

* **The round gathers the remaining budget** (`rebalance_share`): after it, the requesting site's
  share is the sum of all shares plus the units in flight before it. The proof is conservation
  (`Escrow.held_run`): after the round nothing is in flight, the other shares are empty, and no unit
  was spent.
* **A spend within the remaining budget is accepted after the round** (`rebalance_progress`).
* The round changes no other site's spending and spends nothing (`rebalance_spent`), so it is safe
  to run at any time; whether to run it is a policy.

What a round does not guarantee: if other sites spend concurrently, the remaining budget can fall
below the request, and refusing the request is then correct, not starvation. Between competing
requests a round is a resource held by one requester; giving it to the oldest request first is the
aging of `Liveness.FairLeaseService` and of `OccurrenceCommits.Liveness.PriorityRemedies`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Liveness.EscrowProgress

open Mettapedia.GSLT.Coordination.Escrow
open scoped BigOperators

universe u

variable {L : Type u} [DecidableEq L]

theorem run_append (σ : State L) (first second : List (Event L)) :
    run σ (first ++ second) = run (run σ first) second := by
  induction first generalizing σ with
  | nil => rfl
  | cons e rest ih => exact ih _

/-! ## Deliveries -/

/-- Deliver each transfer of a list. -/
def deliveries (ts : List (Transfer L)) : List (Event L) := ts.map .deliver

/-- What one delivery does: nothing to what is sent or spent, applied identifiers only grow, the
transfer is applied afterwards if it was sent, and only its target's share can change. -/
theorem step_deliver (σ : State L) (t : Transfer L) :
    (step σ (.deliver t)).sent = σ.sent ∧ (step σ (.deliver t)).spent = σ.spent ∧
      (∀ site, σ.applied site ⊆ (step σ (.deliver t)).applied site) ∧
      (t ∈ σ.sent → t.id ∈ (step σ (.deliver t)).applied t.target) ∧
      (∀ site, site ≠ t.target → (step σ (.deliver t)).share site = σ.share site) := by
  simp only [step]
  split_ifs with ok
  · refine ⟨rfl, rfl, fun site => ?_, fun _ => by simp, fun site ne => by
      simp [Function.update_of_ne ne]⟩
    by_cases same : site = t.target
    · subst same; simp
    · simp [Function.update_of_ne same]
  · refine ⟨rfl, rfl, fun _ => le_rfl, fun sent => ?_, fun _ _ => rfl⟩
    by_contra notApplied
    exact ok ⟨sent, notApplied⟩

/-- What a list of deliveries does. -/
theorem run_deliveries (σ : State L) (ts : List (Transfer L)) :
    (run σ (deliveries ts)).sent = σ.sent ∧ (run σ (deliveries ts)).spent = σ.spent ∧
      (∀ site, σ.applied site ⊆ (run σ (deliveries ts)).applied site) ∧
      (∀ t ∈ ts, t ∈ σ.sent → t.id ∈ (run σ (deliveries ts)).applied t.target) ∧
      (∀ site, (∀ t ∈ ts, site ≠ t.target) → (run σ (deliveries ts)).share site = σ.share site) := by
  induction ts generalizing σ with
  | nil => exact ⟨rfl, rfl, fun _ => le_rfl, by simp, fun _ _ => rfl⟩
  | cons t rest ih =>
      obtain ⟨sent₁, spent₁, applied₁, applies₁, share₁⟩ := step_deliver σ t
      obtain ⟨sent₂, spent₂, applied₂, applies₂, share₂⟩ := ih (step σ (.deliver t))
      have unfold : run σ (deliveries (t :: rest)) = run (step σ (.deliver t)) (deliveries rest) := rfl
      rw [unfold]
      refine ⟨sent₂.trans sent₁, spent₂.trans spent₁, fun site => (applied₁ site).trans (applied₂ site),
        fun t' member sent => ?_, fun site away => ?_⟩
      · rcases List.mem_cons.mp member with rfl | later
        · exact applied₂ _ (applies₁ sent)
        · exact applies₂ t' later (sent₁ ▸ sent)
      · rw [share₂ site fun t' member => away t' (List.mem_cons_of_mem _ member)]
        exact share₁ site (away t List.mem_cons_self)

/-! ## Donations -/

/-- The donation transfers: the sites of a list, in order, send their share in `σ` to `s` under
identifiers counting up from `b`. -/
def donationTransfers (σ : State L) (s : L) : ℕ → List L → List (Transfer L)
  | _, [] => []
  | b, x :: xs => ⟨b, x, s, σ.share x⟩ :: donationTransfers σ s (b + 1) xs

/-- The send event of a transfer. -/
def sendEvent (t : Transfer L) : Event L := .send t.id t.source t.target t.amount

theorem mem_donationTransfers {σ : State L} {s : L} {b : ℕ} {xs : List L} {t : Transfer L}
    (member : t ∈ donationTransfers σ s b xs) : t.target = s ∧ b ≤ t.id ∧ t.source ∈ xs := by
  induction xs generalizing b with
  | nil => simp [donationTransfers] at member
  | cons x xs ih =>
      simp only [donationTransfers, List.mem_cons] at member
      rcases member with rfl | later
      · exact ⟨rfl, le_rfl, List.mem_cons_self⟩
      · obtain ⟨target, le, source⟩ := ih later
        exact ⟨target, by omega, List.mem_cons_of_mem _ source⟩

/-- **What the donations do**: each donor's share becomes empty, every other share is unchanged,
the transfers are sent, and nothing is spent or applied. -/
theorem run_donations (σ : State L) (s : L) :
    ∀ (xs : List L) (b : ℕ) (τ : State L), xs.Nodup → s ∉ xs → (∀ t ∈ τ.sent, t.id < b) →
      (∀ x ∈ xs, τ.share x = σ.share x) →
      let τ' := run τ ((donationTransfers σ s b xs).map sendEvent)
      τ'.sent = τ.sent ∪ (donationTransfers σ s b xs).toFinset ∧ τ'.spent = τ.spent ∧
        τ'.applied = τ.applied ∧ (∀ x ∈ xs, τ'.share x = 0) ∧
        (∀ y, y ∉ xs → τ'.share y = τ.share y)
  | [], b, τ, _, _, _, _ => by simp [donationTransfers, run]
  | x :: xs, b, τ, nodup, notS, fresh, shares => by
      have xNotXs := (List.nodup_cons.mp nodup).1
      have accepted : σ.share x ≤ τ.share x ∧ ∀ t ∈ τ.sent, t.id ≠ b :=
        ⟨(shares x List.mem_cons_self).ge, fun t member => Nat.ne_of_lt (fresh t member)⟩
      set τ₁ := step τ (.send b x s (σ.share x)) with τ₁Def
      have stepEq : τ₁ = (⟨Function.update τ.share x (τ.share x - σ.share x), τ.spent,
          insert ⟨b, x, s, σ.share x⟩ τ.sent, τ.applied, τ.spends⟩ : State L) := by
        rw [τ₁Def]
        simp only [step]
        rw [if_pos accepted]
      have sent₁ : τ₁.sent = insert ⟨b, x, s, σ.share x⟩ τ.sent := by rw [stepEq]
      have share₁ : ∀ y, τ₁.share y = if y = x then 0 else τ.share y := by
        intro y
        rw [stepEq]
        by_cases same : y = x
        · subst same; simp [shares y List.mem_cons_self]
        · simp [same]
      have spent₁ : τ₁.spent = τ.spent := by rw [stepEq]
      have applied₁ : τ₁.applied = τ.applied := by rw [stepEq]
      obtain ⟨sent₂, spent₂, applied₂, empty₂, same₂⟩ := run_donations σ s xs (b + 1) τ₁
        (List.nodup_cons.mp nodup).2 (fun inXs => notS (List.mem_cons_of_mem _ inXs))
        (fun t member => by
          rw [sent₁, Finset.mem_insert] at member
          rcases member with rfl | old
          · simp
          · have := fresh t old; omega)
        (fun y inXs => by
          rw [share₁, if_neg (fun (same : y = x) => xNotXs (same ▸ inXs))]
          exact shares y (List.mem_cons_of_mem _ inXs))
      have unfold : run τ ((donationTransfers σ s b (x :: xs)).map sendEvent) =
          run τ₁ ((donationTransfers σ s (b + 1) xs).map sendEvent) := rfl
      dsimp only
      rw [unfold]
      refine ⟨?_, spent₂.trans spent₁, applied₂.trans applied₁, fun y member => ?_, fun y away => ?_⟩
      · rw [sent₂, sent₁]
        ext t
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, donationTransfers,
          List.mem_cons]
        tauto
      · rcases List.mem_cons.mp member with rfl | later
        · rw [same₂ y xNotXs, share₁, if_pos rfl]
        · exact empty₂ y later
      · rw [same₂ y (fun inXs => away (List.mem_cons_of_mem _ inXs)), share₁,
          if_neg (fun (same : y = x) => away (same ▸ List.mem_cons_self))]

/-! ## The round -/

/-- An identifier above every identifier sent. -/
def freshBase (σ : State L) : ℕ := σ.sent.sup Transfer.id + 1

theorem lt_freshBase {σ : State L} {t : Transfer L} (member : t ∈ σ.sent) : t.id < freshBase σ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := Transfer.id) member)

variable [Fintype L]

/-- The donation transfers of the round toward `s`, after the first deliveries. -/
noncomputable def roundTransfers (σ : State L) (s : L) : List (Transfer L) :=
  donationTransfers (run σ (deliveries σ.sent.toList)) s
    (freshBase (run σ (deliveries σ.sent.toList))) (Finset.univ.erase s).toList

/-- **The rebalancing round toward `s`**: deliver everything sent, let every other site send its
share to `s`, deliver those transfers. -/
noncomputable def rebalance (σ : State L) (s : L) : List (Event L) :=
  deliveries σ.sent.toList ++ (roundTransfers σ s).map sendEvent ++ deliveries (roundTransfers σ s)

/-- The facts at the end of the round: nothing spent, nothing in flight, every other share empty. -/
theorem rebalance_facts (σ : State L) (s : L) :
    (run σ (rebalance σ s)).spent = σ.spent ∧ inflight (run σ (rebalance σ s)) = 0 ∧
      ∀ x, x ≠ s → (run σ (rebalance σ s)).share x = 0 := by
  obtain ⟨sent₁, spent₁, _, applies₁, _⟩ := run_deliveries σ σ.sent.toList
  obtain ⟨sent₂, spent₂, applied₂, empty₂, _⟩ := run_donations (run σ (deliveries σ.sent.toList)) s
    (Finset.univ.erase s).toList (freshBase (run σ (deliveries σ.sent.toList)))
    (run σ (deliveries σ.sent.toList)) (Finset.nodup_toList _) (by simp)
    (fun t member => lt_freshBase member) (fun _ _ => rfl)
  have tsEq : roundTransfers σ s = donationTransfers (run σ (deliveries σ.sent.toList)) s
      (freshBase (run σ (deliveries σ.sent.toList))) (Finset.univ.erase s).toList := rfl
  rw [← tsEq] at sent₂ spent₂ applied₂ empty₂
  obtain ⟨sent₃, spent₃, applied₃, applies₃, share₃⟩ := run_deliveries
    (run (run σ (deliveries σ.sent.toList)) ((roundTransfers σ s).map sendEvent)) (roundTransfers σ s)
  have whole : run σ (rebalance σ s) = run (run (run σ (deliveries σ.sent.toList))
      ((roundTransfers σ s).map sendEvent)) (deliveries (roundTransfers σ s)) := by
    simp only [rebalance, run_append]
  rw [whole]
  refine ⟨spent₃.trans (spent₂.trans spent₁), ?_, fun x ne => ?_⟩
  · apply Finset.sum_eq_zero
    intro t member
    rw [sent₃, sent₂, Finset.mem_union] at member
    rw [if_pos]
    rcases member with old | new
    · rw [sent₁] at old
      have := applies₁ t (Finset.mem_toList.2 old) old
      exact applied₃ _ (by rw [applied₂]; exact this)
    · have inTs : t ∈ roundTransfers σ s := List.mem_toFinset.1 new
      exact applies₃ t inTs (by rw [sent₂]; exact Finset.mem_union_right _ new)
  · rw [share₃ x fun t member => by rw [(mem_donationTransfers (tsEq ▸ member)).1]; exact ne]
    exact empty₂ x (by simp [ne])

/-- **The round gathers the remaining budget.** -/
theorem rebalance_share (σ : State L) (inv : Inv σ) (s : L) :
    (run σ (rebalance σ s)).share s = (∑ x, σ.share x) + inflight σ := by
  obtain ⟨spent, flight, empty⟩ := rebalance_facts σ s
  have conserved := held_run inv (rebalance σ s)
  have single : (∑ x, (run σ (rebalance σ s)).share x) = (run σ (rebalance σ s)).share s :=
    Finset.sum_eq_single_of_mem s (Finset.mem_univ s) fun x _ ne => empty x ne
  simp only [held, spent, flight, single] at conserved
  omega

/-- The round spends nothing. -/
theorem rebalance_spent (σ : State L) (s : L) : (run σ (rebalance σ s)).spent = σ.spent :=
  (rebalance_facts σ s).1

/-- **A spend within the remaining budget is accepted after the round.** -/
theorem rebalance_progress (σ : State L) (inv : Inv σ) (s : L) {a : ℕ}
    (enough : a ≤ (∑ x, σ.share x) + inflight σ) :
    (run (run σ (rebalance σ s)) [.spend s a]).spends = (run σ (rebalance σ s)).spends ++ [(s, a)] := by
  have share := rebalance_share σ inv s
  show (step (run σ (rebalance σ s)) (.spend s a)).spends = _
  simp only [step]
  rw [if_pos (share ▸ enough)]

/-! ## Control -/

namespace Controls

/-- Two sites with one unit each; a spend of two at `true` is refused before the round
(`Escrow.Controls.large_spend_needs_rebalance`) and accepted after it. -/
theorem large_spend_after_round :
    (run (start (fun _ => 1)) [.spend true 2]).spends = [] ∧
      (run (run (start (fun _ : Bool => 1)) (rebalance (start fun _ => 1) true)) [.spend true 2]).spends =
        (run (start (fun _ : Bool => 1)) (rebalance (start fun _ => 1) true)).spends ++ [(true, 2)] := by
  refine ⟨by decide, rebalance_progress _ (inv_start _) true ?_⟩
  simp [inflight, start]

end Controls

end Mettapedia.GSLT.Coordination.Liveness.EscrowProgress
