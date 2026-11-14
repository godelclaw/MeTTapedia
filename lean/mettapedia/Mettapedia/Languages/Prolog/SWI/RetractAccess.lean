import Mettapedia.Machines.GracePeriodPins

set_option autoImplicit false

/-!
# retract/1 and clause garbage collection: the access generation

SWI-Prolog's clause garbage collector is a grace-period reclamation scheme
(`Mettapedia.Machines.GracePeriodPins`).  This module maps that model onto
the C sources of SWI-Prolog master `cf6960c` (stock) and of the fix
`bf81af4` on top of it, and names the consequences for retract/1.

## Source map

| Model | SWI-Prolog C |
|---|---|
| generation `gen` | `GD->_generation`, read by `global_generation()` |
| object, `born`, `died` | `Clause`, `generation.created`, `generation.erased` |
| `tick` | an assert, which gives the clause the next generation |
| `erase` | `retract_clause()`: `erased = GD->_generation+1` under `L_GENERATION`, then the generation advances |
| reader | a thread (`PL_local_data_t`) |
| reader's pins | the `definition_ref` access objects of the thread for the predicate (`LD->predicate_references`), and the generations of frames running the predicate |
| `pin` | `pushPredicateAccessObj(def)`: `generation = current_generation(def)`, re-read until stable |
| `acquire` | `firstClause()`/`nextClause()` selecting a clause visible at the frame generation; the walk runs under `acquire_def()`, so `gcClauseRefs()` frees no clause reference of the predicate during it |
| held objects | the candidate `clause` during `decompile()`/`retractClauseDefinition()`, and `ctx->chp.cref`, the next candidate kept for backtracking |
| `repin` | `retract_move_generation()` (fix): under `LD->thread.scan_lock`, `dref->generation = moved->generation` and `popPredicateAccess(def)`: the pins `[G, Gb]` become `[Gb]` |
| `release` | `free_retract_context()`: `popPredicateAccess(def)` once no clause is held |
| `start` | `pl_garbage_collect_clauses()`: `start_gen = global_generation()`, `ddi_reset()` |
| `scan` | `markPredicatesInEnvironments()` for the collecting thread, and for every other thread through `forThreadLocalDataUnsuspended()`, which holds that thread's `scan_lock` while it marks its frames and access objects (`markAccessedPredicates()`) |
| `Garbage` | `ddi_is_garbage()`: erased before `start_gen` and invisible at every marked generation |
| `finish` | `cleanDefinition()` unlinks garbage; `lingerClauseRef()`, then `gcClauseRefs()` frees it once no thread walks the predicate |

The frame of retract/1 runs `system:retract/1`, never the dynamic predicate,
so for that predicate the only pin of a thread inside retract/1 is its access
object `dref`.

## Consequences

* Stock (`cf6960c`): when `retractClauseDefinition()` fails on the first call
  (another thread erased the candidate first, or an update event refused),
  retract/1 calls `setGenerationFrame(environment_frame)`: the frame moves to
  the current generation, `dref` does not, and `nextClause()` selects at the
  frame generation.  That is a read at an unpinned generation:
  `Machines.GracePeriodPins.unpinned_view_unsafe` gives a run in which the
  held clause is freed.
* The fix (`bf81af4`) moves the pin with the frame in the protocol's own
  steps: `pin` (a second access object at the current generation), `acquire`
  at that pin (`nextClause()`), then `repin` keeping only the new
  generation, whose precondition holds because the candidate and the next
  candidate were selected at it.  `Machines.GracePeriodPins.safe_of_reach`
  applies.
* Moving `dref` in place to the current generation before the scan is
  `unchecked_repin_unsafe`: the saved candidate may be visible only at the
  old generation.
* Without `scan_lock` the collector may read the two access objects at
  different times, around the move: `slotwise_scan_unsafe`.
* That retract/1 erases nothing more once an update event has raised an
  exception is a separate, semantic requirement; it is tested, not part of
  this reclamation model.

## Assumptions that hold at the source boundary, not in the model

* Sequential consistency.  The publication loops of `pushPredicateAccessObj()`
  and `setGenerationFrame()`, and the barriers of the call-port fix (PR 6),
  are what make a published generation visible to a collector that starts
  later; the model takes that for granted.
* The walk returns only clauses whose memory is still valid: `acquire_def()`
  and the `activePredicate()` test of `gcClauseRefs()`.
* Transactions use their own generation space (`GEN_TRANSACTION_BASE`,
  `tr_starts`) and are not modelled; nor are address reuse, `erase/1` through
  clause references (protected by the reference count of the clause blob),
  or the update-event and constraint goals that run Prolog inside retract/1
  (the model lets any other step interleave at any point, which covers their
  database effects).
-/

namespace Mettapedia.Languages.Prolog.SWI.RetractAccess

open Mettapedia.Machines.GracePeriodPins

/-- The fixed protocol keeps every clause a thread uses unfreed, for every
interleaving of threads, writers and collector. -/
theorem fixed_safe {R O : Type} [DecidableEq R] [DecidableEq O] {s t : St R O}
    (hs : Inv s) (h : Reach s t) : ∀ r o, o ∈ t.held r → o ∉ t.freed :=
  safe_of_reach hs h

/-- Stock retract/1 reads at a frame generation it has not pinned; a clause
it holds can be freed. -/
theorem stock_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith UnpinnedAcquire) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed :=
  unpinned_view_unsafe.2

/-- Moving the access generation in place before the scan frees a clause
retract/1 still keeps. -/
theorem move_before_scan_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith UncheckedRepin) (mk 0 lives ∅ [0] [] .idle) t ∧
      false ∈ t.held () ∧ false ∈ t.freed :=
  unchecked_repin_unsafe.2

/-- Moving the access generation without `scan_lock`: a collector that
reads the two access objects at different times frees a held clause. -/
theorem unlocked_move_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith SlotwiseScan) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed :=
  slotwise_scan_unsafe.2

end Mettapedia.Languages.Prolog.SWI.RetractAccess
