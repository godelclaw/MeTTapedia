import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.ParkedWakeups
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.OptimisticRetries
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.PriorityRemedies
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.RematchingClaims
import Mettapedia.GSLT.Coordination.Liveness.FairLeaseService
import Mettapedia.GSLT.Coordination.Liveness.EscrowProgress

/-!
# Fairness is an observer policy: which result needs which assumption

A scheduler policy (weak or strong fairness, aging, a fixed order, first come first served) chooses
among the runs of a system. It changes which infinite runs are admitted, so it changes liveness and,
with probabilities, the distribution of outcomes. It does not change which finite behaviours are
possible, so no safety result and no outcome set depends on it: the classes of runs used here are
machine closed (`FairRuns.machineClosed_stronglyFair`, `machineClosed_weaklyFair`), and for a
machine-closed class invariants, finite-trace properties and visited states are those of all runs
(`MachineClosed.invariant_iff`, `traceSafety_iff`, `visits_iff`). This module states that for the
two systems of this folder (`reactive_*`, `optimistic_*`).

## Safety: no fairness

Every safety theorem of the commit semantics and of these modules is a statement about finite
executions or reachable states: refinement (`CommitProtocol.Run.refines`,
`OptimisticRetries.exec_refines`, `RematchingClaims.RRun.refines`), the wait-index invariant
(`ParkedWakeups.wakeInv_next`), at most one effect per task (`FencedLeases.effects_nodup`,
`FairLeaseService.fair_effects_nodup`), conservation (`Escrow.held_run`). They hold under every
policy and need none.

## Progress conditions: no fairness

| result | assumption |
|---|---|
| bounded lock-freedom: a commit in every `3·|T|+1` steps (`OptimisticRetries.Run.commit_within`) | none |
| obstruction-freedom: four solo steps include a commit (`Run.solo_commit_within`) | none |
| no aborts where nothing invalidates: unchecked mode, monotone programs (`never_aborts`) | none |
| deadlock-freedom of canonical claims (`RematchingClaims.progress_available`) | none |
| claims block a stalled holder's rivals (`RematchingClaims.claim_blocks`) | none (a negative result) |

## Liveness: the weakest assumption each result needs, and the control showing it is needed

| result | assumption | control without it |
|---|---|---|
| a parked `await` whose guard holds infinitely often fires (`ParkedWakeups.await_fires`) | strong fairness of running it; an index that loses no wakeup | weak fairness: `Controls.flicker_weaklyFair`, `flicker_await_never_fires`; wrong index: `Controls.makesIndex_loses_wakeup` |
| a stable guard fires (`await_fires_of_stable`, `await_fires_of_sole_consumer`) | weak fairness | none needed beyond it |
| no starvation under optimistic validation (`commits_of_stronglyFair_commit`) | strong fairness of the commit step | `Controls.optimistic_starvation` (weakly fair, every process steps forever) |
| aging decides every one-shot transaction (`PriorityRemedies.aging_decides`) | weak fairness of each transaction's steps | priority by process: `Controls.staticPriority_starves` |
| a fixed order decides every transaction (`sequenced_decides`) | weak fairness of each transaction's steps; one-shot transactions | same control |
| every lease task is done (`FairLeaseService.fifo_eventually_done`) | eventual expiry, first-come-first-served service, one correct worker asking once after stabilization and answering in time, eventual synchrony | no expiry: `FencedLeases.Controls.no_expiry_blocks`; no fair service: `FencedLeases.Controls.starvation`; no synchrony: `TimedLeases.Controls.async_never_completes`, `fixed_duration_fails` |
| a large escrow spend is accepted after a rebalancing round (`EscrowProgress.rebalance_progress`) | the round runs without competing spends | without the round: `Escrow.Controls.large_spend_needs_rebalance` |

Strong fairness is satisfiable in every system here: the aging scheduler realizes it
(`FairRuns.agingRun_stronglyFair`, `ParkedWakeups.exists_stronglyFair_reactive_run`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

/-! ## The reactive system -/

section Reactive

variable {O : Type u} [DecidableEq O] {R : Type v} {P : Type w} [Fintype P] [DecidableEq P]
  (label : O → R) (proc : P → Parked O R) (index : Parked O R → Commit O R → Prop)
  (envOK : Commit O R → Prop) (σ₀ : RState O P)

/-- **No invariant of the reactive system depends on fairness**: one holds on every strongly fair
run exactly when it holds at every reachable state. -/
theorem reactive_invariant_independent_of_fairness (Inv : RState O P → Prop) :
    (∀ r : Run (reactive label proc index envOK), (∀ p, r.StronglyFair (runTask p)) →
        r.state 0 = σ₀ → ∀ n, Inv (r.state n)) ↔
      ∀ σ, (reactive label proc index envOK).Reachable σ₀ σ → Inv σ :=
  (machineClosed_stronglyFair (fun p => runTask p) (reactive_nonBlocking label proc index envOK)
    σ₀).invariant_iff Inv

/-- **The states the reactive system can reach do not depend on fairness.** -/
theorem reactive_outcomes_independent_of_fairness (σ : RState O P) :
    (∃ r : Run (reactive label proc index envOK), (∀ p, r.StronglyFair (runTask p)) ∧
        r.state 0 = σ₀ ∧ ∃ n, r.state n = σ) ↔
      (reactive label proc index envOK).Reachable σ₀ σ :=
  (machineClosed_stronglyFair (fun p => runTask p) (reactive_nonBlocking label proc index envOK)
    σ₀).visits_iff σ

end Reactive

/-! ## The optimistic system -/

section Optimistic

variable {O : Type u} [DecidableEq O] {R : Type v} {T : Type w} [DecidableEq T] [Fintype T]
  (label : O → R) (mode : Finset Check) (prog : Program T O R) (refuse : OState T O R → T → Prop)
  (σ₀ : OState T O R)

/-- **No invariant of optimistic execution depends on fairness**, for any refusal policy: one
holds on every run that is strongly fair for every transaction's steps exactly when it holds at
every reachable state. -/
theorem optimistic_invariant_independent_of_fairness (Inv : OState T O R → Prop) :
    (∀ r : Run (optimistic label mode prog refuse).withIdle,
        (∀ x, r.StronglyFair (LTS.liftTask (stepTask x))) → r.state 0 = σ₀ → ∀ n, Inv (r.state n)) ↔
      ∀ σ, (optimistic label mode prog refuse).Reachable σ₀ σ → Inv σ := by
  rw [(machineClosed_stronglyFair (fun x => LTS.liftTask (stepTask x))
    (LTS.withIdle_nonBlocking _) σ₀).invariant_iff Inv]
  exact forall_congr' fun σ => imp_congr_left (LTS.withIdle_reachable_iff _ σ₀ σ)

/-- **The states optimistic execution can reach do not depend on fairness.** -/
theorem optimistic_outcomes_independent_of_fairness (σ : OState T O R) :
    (∃ r : Run (optimistic label mode prog refuse).withIdle,
        (∀ x, r.StronglyFair (LTS.liftTask (stepTask x))) ∧ r.state 0 = σ₀ ∧ ∃ n, r.state n = σ) ↔
      (optimistic label mode prog refuse).Reachable σ₀ σ := by
  rw [(machineClosed_stronglyFair (fun x => LTS.liftTask (stepTask x))
    (LTS.withIdle_nonBlocking _) σ₀).visits_iff σ]
  exact LTS.withIdle_reachable_iff _ σ₀ σ

/-- The same with weak fairness. -/
theorem optimistic_invariant_independent_of_weak_fairness (Inv : OState T O R → Prop) :
    (∀ r : Run (optimistic label mode prog refuse).withIdle,
        (∀ x, r.WeaklyFair (LTS.liftTask (stepTask x))) → r.state 0 = σ₀ → ∀ n, Inv (r.state n)) ↔
      ∀ σ, (optimistic label mode prog refuse).Reachable σ₀ σ → Inv σ := by
  rw [(machineClosed_weaklyFair (fun x => LTS.liftTask (stepTask x))
    (LTS.withIdle_nonBlocking _) σ₀).invariant_iff Inv]
  exact forall_congr' fun σ => imp_congr_left (LTS.withIdle_reachable_iff _ σ₀ σ)

end Optimistic

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
