# Models of the SWI-Prolog clause GC protocols

Part of MeTTapedia's main Lean project. These models use core Lean only.
Build from `lean/mettapedia` with
`lake build Mettapedia.Languages.Prolog.SWI`; every theorem
depends only on `propext`, `Quot.sound` and, in `Handoff.A`,
`Classical.choice`.

Each model is a transition system over the interleavings of its actors.
Each ordering the C code relies on is a flag. The publication models prove
their fixed protocols safe for every schedule. `SupervisorV1` refutes the
earlier three-fix supervisor safety claim even with its fixes enabled. Each
removed fix also has an explicit counterexample.

The ownership-aware model in `Supervisor.lean` defines list and supervisor
references separately. Its memory and erasure invariants are distinct; their
full reachability proofs are being developed. The legacy counterexample remains
under `Supervisor.V1`, rather than being relabeled as a result about ownership.

Import `Mettapedia.Languages.Prolog.SWI` for all models. Build
`Mettapedia.Languages.Prolog.SWI.Audit` for the axiom output of every explicitly
declared theorem. The models use this repository's existing toolchain and cache.

## Publish.lean: the call port and clause GC

| model | C |
|---|---|
| `call`: the frame takes `G` while still at lTop | `setGenerationFrame()` in `depart_or_retry_continue` (normal_call leaves lTop at the new frame) |
| `publish`: lTop above the frame, via the store buffer | `lTop = argFrameP(fr, arity)` in `publishGenerationFrame()` / `S_STATIC` |
| `retake`/`confirm`: re-read `G` until equal | the loop in `publishGenerationFrame()` |
| `readerFence` | its `MEMORY_BARRIER()` |
| `gcStart`, `gcFence`, `scan` | `start_gen = global_generation(); MEMORY_BARRIER();` and `markPredicatesInEnvironments()` (frames below lTop, under scan_lock) |
| `reclaim` | `ddi_is_garbage()`: erased before start, invisible in every registered generation (list mode; interval mode reclaims less) |
| `erase` | `retract_clause()`: under L_GENERATION, `erased := G+1; MEMORY_RELEASE(); G := G+1` |

Results:
- `fixed_safe`: re-validation plus both barriers is safe for any number of readers, clauses, writers and GC runs.
- `stock_unsafe`: without re-validation (the stock call port, and `S_STATIC` today) the frame selects a reclaimed clause.
- `no_reader_fence_unsafe`: without the reader's barrier the lTop store is still buffered when the frame re-reads.
- `no_gc_fence_unsafe`: without clause GC's barrier the scan can precede the start read (load-load reordering).

The same shape covers `pushPredicateAccessObj()` (clause/2, retract/1, retractall/1).

## PublishAsym.lean: asymmetric barrier

The reader uses no hardware barrier. Clause GC issues one process-wide barrier after reading its start generation (`membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED)`, `FlushProcessWriteBuffers()`). `asym_safe`: safe.

## Handoff.lean: snapshot to frame

Part A covers a `db_snapshot/1` handle. The goal frame is stamped without a lock, so the stamp may still be buffered. Close runs under `L_MISC`. Clause GC marks the open snapshots (`markDBSnapshots()`) before scanning frames.
- `handle_safe`.
- `handle_frames_first_unsafe`: frames scanned first. This is the surviving mutant `r_gc_order`.
- `handle_close_unsynced_unsafe`: a close that does not order the stamp before it.

Part B covers the `db_snapshot_scope/2` frame, stamped under the thread's scan lock.
- `scope_safe`.
- `scope_split_unsafe`: the generation read and the flag store split around a scan.

## CallPort.lean: the code of PR 6 revision 3

This model follows the code step by step. A frame protects what it reads only once clause GC can see it, so the call port moves lTop above the frame before `setGenerationFrame()`. That function's loop re-reads the generation after a barrier, and all of this happens before `DEF->codes` is read.

| model | C (PR 6 revision 3) |
|---|---|
| `call` | `normal_call`: the new frame, at lTop |
| `publish` | `lTop = FR+1` in `depart_or_retry_continue` |
| `grab` | `gen = global_generation()` in `setGenerationFrameAt()` |
| `put` (into the store buffer) | `setGenerationFrameVal(fr, gen)` |
| `check` | the barrier, `} while(gen != global_generation());` then `MEMORY_ACQUIRE()` |
| `fence` | `MEMORY_BARRIER()`: the first commit; `GENERATION_BARRIER()` and `depart_alerted` without a process-wide barrier |
| `cross`, per thread, while the others run | `processBarrier()` after `start_gen`: `membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED)` (Linux, FreeBSD), `FlushProcessWriteBuffers()` (Windows), `thread_get_register_pointer_values()` on every thread (macOS); the loop has a compiler barrier |
| `light` | `setGenerationCallPort()`: the loop with a compiler barrier; without a process-wide barrier `ALERT_FENCE` sends the call to `depart_alerted`, which runs the loop with `MEMORY_BARRIER()` |
| `dispatch` | `PC = DEF->codes` |
| `replace` | `freeCodesDefinition()` -> `linger_always()` (`c->generation = global_generation()`) |
| `freeCode` | `free_lingering(&def->lingering, min(oldest registered, start))` in `cleanDefinition()` |
| `freeClause` | `ddi_is_garbage()` |
| `drainGen`, `drainTop` | in order per address, any order across (ARM store reordering; contains TSO) |

Results:
- `safe`, `symmetric_safe`, `asymmetric_safe`: no frame ever holds a reclaimed clause or a freed supervisor.
- `fallback_safe`: the same without a process-wide barrier, with `light` rounds before the fenced one. `asymmetricLight_safe`: a thread that still has `ALERT_FENCE` while clause GC uses `membarrier()`.
- `early_codes_unsafe`: validating after `DEF->codes` was read, inside the supervisor. This is the S_TRUSTME use-after-free.
- `no_recheck_unsafe`: storing without loading again after the barrier.
- `neither_unsafe`: no fence and no crossing.

Still assumed here:
- Loads happen in program order. This is `MEMORY_ACQUIRE()` after the loop: free on x86, `dmb ishld` on ARM.
- One predicate here; see `CallPortPred` for several predicates and last calls.
- The scan reads lTop and the generation field in one step. A frame that matters has no pending stores at that point.
- The erase is one step.

## CallPortPred.lean: predicates and last calls

The same protocol, with three additions. Each clause and each supervisor version belongs to a predicate. The frame's predicate field is a third buffered store. Clause GC keys what it registers by that field, as `markPredicatesInEnvironments()` adds a generation to the `DirtyDefInfo` of `fr->predicate`.

The step `depart` is `I_DEPART`: a running frame that clause GC can see already is reused for another predicate. It stores the new predicate and passes the call port again.

`safe` (`symmetric_safe`, `asymmetric_safe`, `fallback_safe`, `asymmetricLight_safe`): no frame ever holds a reclaimed clause or a freed supervisor of its predicate, also when a visible frame changes its predicate. This removes the "one predicate" assumption of `CallPort`.

## SupervisorV1.lean: pre-ownership static supervisor lifetime, `3f6bfd9`

`fixed_unsafe` is a machine-checked counterexample to the earlier
`fixed_safe` claim. All three fixes are enabled, including the creator's
predicate hold. `not_fixed_safe` explicitly negates universal safety from
`Init`. This is the counterexample outcome of the supervisor verification;
there is no `fixed_safe` theorem.

These historical results are in the namespace
`Mettapedia.Languages.Prolog.SWI.Supervisor.V1`. The reference-owning protocol
is developed separately in `Supervisor.lean`, under
`Mettapedia.Languages.Prolog.SWI.Supervisor`.

The missing condition is the **birth** side of visibility. A reader can
stamp an old generation, then load a newly created supervisor whose clause
was born later. Detaching before publishing an erasure does not prevent
this. `S_TRUSTME` and `S_LIST` do not test visibility, while clause GC
protects the clause only in generations where it is visible.

`fixed_birth_gap` certifies this 23-step execution with two clauses and one
reader. The slot starts at `S_VIRGIN`; the predicate can already be defined.

| action | global generation | reader generation | replacement clause |
|---|---:|---:|---|
| reader stamps, before its slot load | 0 | 0 | not yet visible; born at 1 |
| first writer marks the old clause, detaches, publishes | 1 | 0 | now visible |
| creator scans the replacement, validates under the lock, CAS installs version 0, releases its hold | 1 | 0 | live |
| reader loads version 0 | 1 | 0 | embedded, although born after the reader's stamp |
| second writer marks the replacement, detaches and lingers version 0 at 1, publishes | 2 | 0 | erased at 2 |
| another generation is published; GC starts and records the reader's 0 | 3 | 0 | invisible at 0 because born at 1 |
| GC frees the replacement; reader runs the embedded operand | 3 | 0 | freed |

The witness also certifies `dup = false`, `vfreed 0 = false`, and
`lingered 0 = some 1`. The supervisor need not be reclaimed for its embedded
clause to be unsafe. The first writer actually erases an existing clause;
the last publication can represent an update that erases no further clause
of this predicate.

| model | C at `3f6bfd9` |
|---|---|
| `G`, `born`, `erased`, `cl_erased`, `cfreed` | global generation; clause creation/erasure generations, `CL_ERASED`, physical reclamation |
| `embeds v`, fresh `next`, `vfreed`, `slot` | allocated supervisor versions and their fixed clause operands; `DEF->codes`, with `none` representing the static `S_VIRGIN` code |
| `stamp`, `readSlot`, `wait`, `run`, `exit` | the CallPort guarantee, then the slot load; `S_VIRGIN`; `S_TRUSTME` / `S_LIST` trusting the embedded reference |
| `writerLock`, repeated `mark`, `writerDetach`, `publish` | `removeClausesPredicate()` / `reconsultFinalizePredicate()`: hold `L_GENERATION`, mark `CL_ERASED` and `erased = G+1`, `detachErasedSupervisor()`, publish and unlock |
| prescribed future `born` | pending reconsult additions: `reconsultFinalizePredicate()` sets their creation generation to the update generation before publishing it |
| `creatorRead`, repeated `scanClause`, `allocate` | `setDefaultSupervisor()` reads the old slot; `getClauses()` tests each candidate at the current global generation; `singleClauseSupervisor()` / `listSupervisor()` embed the collected references |
| `cr.holds` | the outer `acquire_def2()` through creation, validation and lingering; `release_def2()` afterwards |
| `creatorLock`, `install`, `retry` | `installSupervisor()`: `embedsErasedClause()` and CAS under `L_GENERATION`; retry on failed validation or CAS |
| `creatorLinger` | `freeSupervisor(old, true)` after `installSupervisor()` unlocks; the linger generation is the global generation at this later step |
| `detacherRead`, `detacherCas`, `detacherRetry`, `detacherLinger` | unlocked `freeCodesDefinition()` from consult, `fix_metapredicate()` or `resetProcedure()`; only the CAS winner lingers |
| `lingered`, `dup`, `St.linger` | `linger_always()`: record the generation at insertion and detect a second insertion of the same version; the model retains insertion history after free |
| `gcStart`, `gcScan`, `freeClause`, `gcEnd` | clause GC start generation, frame generation registration, `ddi_is_garbage()` and `gcClauseRefs()`; erased before start, invisible at every registered generation, no creator holding the predicate |
| `freeVersion` | `cleanDefinition()` → `free_lingering(min(start, oldest registered))`: linger generation strictly below both start and every registered generation |

The wrapped supervisor slot uses the same update protocol:
`setWrappedSupervisor()` uses `installSupervisor()`, and
`resetWrappedSupervisor()` retries its CAS and only lingers after success.
The one-slot abstraction covers either slot's updates. Its reader rule
assumes the stamp precedes the slot load. In the pinned C, `S_WRAP` loads
the wrapped code before calling `setGenerationFrame()`; applying the reader
rule to that VM path requires a separate ordering argument.

The five removed-fix results are explicit `Reach.tail` traces,
all starting from `unitInit`, with the sole clause born at 0:

- `no_detach_unsafe`: the unchanged-mode meta-predicate case retains an erased operand.
- `late_detach_unsafe`: a reader loads the old supervisor after publication and before detachment.
- `unvalidated_install_unsafe`: the creator installs an operand erased after its scan, despite holding the predicate.
- `plain_swap_unsafe`: two unlocked detachers read the same version; both linger it, setting `dup`.
- `no_hold_unsafe`: GC frees a collected operand before the creator enters its validation phase; taking `L_GENERATION` does not revive it.

`initial_init`, `init_init`, `unitInit_init` and `prepared_reach` establish
the initial states and the shared creation prefix. `#print axioms` checks
every theorem in this module: the initial-state and prefix lemmas and
`plain_swap_unsafe` use no axioms; the others use only `propext` and
`Quot.sound`.

Assumptions and limits:

- Sequential consistency. The store-buffer stretch is not attempted after
  the fixed protocol's counterexample.
- The reader's stamp already satisfies the guarantee proved in `CallPort`:
  a later GC scan sees its generation until exit. No visibility or liveness
  premise is added to `readSlot` or `run`.
- One predicate and one slot; arbitrary reader and unlocked-detacher index
  types; one creator serialized by `L_PREDICATE` and writers serialized by
  `L_GENERATION`. Fresh version numbers abstract allocations without address reuse.
- Clause births are prescribed, possibly after the initial generation, as
  also allowed by `CallPort.Init`. A future birth abstracts a pending
  addition becoming visible at publication. The fixed counterexample uses
  one such addition. Assuming every clause was born before every reader
  stamps would exclude this reconsult case.
- Scans may collect several operands over several steps. Writer detachment
  and lingering inside its generation critical section are combined into
  one step; the counterexample therefore needs no race inside that operation.
- `Safe` includes the liveness of operands in the creator's `checking`
  phase, immediately before `embedsErasedClause()` dereferences them.
  Reclamation is modeled once per object; lingering history is retained
  for duplicate detection. The clause rule uses generation-list GC;
  interval GC can conservatively retain more clauses.
- This is a Lean protocol result with a source mapping, not a compiled-C
  refinement proof or an executed SWI reproducer. The pinned ordinary
  defined-predicate `S_VIRGIN` path calls `setDefaultSupervisor()` and then
  loads `DEF->codes` without refreshing the frame's generation, consistent
  with the birth gap above.

## Assumptions of the earlier models (Publish, PublishAsym, Handoff)

1. A frame's generation store is visible together with the step that makes it. In C it is a store, so a scan could see the previous value between the reader's load and its store. Informally the loop covers this: the frame exits only on a read that follows its last store and a barrier. The next refinement puts generation stores through the store buffer.
2. Stores of one thread become visible in order (TSO). On ARM, the call-port generation store and the lTop store need a store-store barrier between them; there is none today.
3. A reader reads clause fields after its final generation read. On ARM this needs an acquire, for example `global_generation()` as an acquire load. The stock code has none, and the writer's `MEMORY_RELEASE()` has nothing to pair with.
4. The erase is one step (L_GENERATION serializes writers; the release orders `erased` before `G`).

## Experiments that match the counterexamples

- `stock_unsafe` on a dynamic predicate is the v12 race experiment (delay hooks): heap-use-after-free, 3 of 3 runs before PR 6, 0 of 3 after.
- `stock_unsafe` on a static predicate under reconsult, with PR 6 applied: heap-use-after-free in `next_clause_unindexed()`, 3 of 3 runs. PR 6 does not cover `S_STATIC` or the static supervisors.
