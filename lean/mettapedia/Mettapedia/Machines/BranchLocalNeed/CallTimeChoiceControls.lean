import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceOrdered
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceWitnesses

/-!
# Controls for call-time choice

Positive controls.

* `machine_samePick`: the unchanged reference machine, on `same pick`, halts and
  answers the two diagonal pairs, as `adequacy` predicts.
* `transport_renaming`: renaming a cell and adding an unreachable cell keeps the
  answers (an instance of `transport_eval`).
* `keep_branch_world`: forwarding each result with its own branch's world gives
  the 2/3/3 answers of the residual discriminator.

Negative controls: each removes one hypothesis and the answers change.

* `machine_partial`: before the frontier has halted the machine's answers are
  partial (here none), although the specification derives two; adequacy is
  stated for halted frontiers, not step by step.
* `identity_split`: one shared cell transported to two cells gives four answers
  instead of two; read backwards, merging two cells into one gives two instead
  of four (a transport must be injective and functional).
* `role_loss`: a ready value transported as pending runs the producer again.
* `sibling_merge`: a sibling alternative that starts from another sibling's
  store sees its memo and loses answers (forks must copy the parent's store).
* `keep_ancestor_world`: forwarding an unmatched return with the ancestor's
  cache for the cells the ancestor already had gives 4/9/7 answers instead of
  2/3/3. Resampling every use gives 4/9/9; 4/9/7 is neither choice discipline.

The strict-position controls (a primitive or an activation given the
parameter's suspension) are in `CallTimeChoiceWitnesses`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Controls

open NeedReference
open Witnesses.Core

/-! ## The reference machine -/

/-- `same pick` with call-time choice: one cell for the argument. -/
def samePickCall : Comp := .need pickC (.call fSame [.var 0])

def mA : MVal := .sym symA
def mB : MVal := .sym symB
def mpair (x y : MVal) : MVal := .app (.app (.sym symPair) x) y

theorem machine_samePick :
    Halted program samePickCall 200 ∧
      machineValues (machineAnswers program 200 samePickCall) = [mpair mA mA, mpair mB mB] := by
  refine ⟨?_, by decide +kernel⟩
  unfold Halted
  decide +kernel

theorem spec_samePick :
    observeValues program 200 samePickCall = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem machine_partial : (machineAnswers program 40 samePickCall).length = 0 := by
  decide +kernel

/-! ## Transport -/

/-- Observe a computation from a given store and environment. -/
def observeFrom (σ : Store) (ρ : List (Val Nat)) (M : Comp) : Option (List (Val Nat)) :=
  (run (observed program) 200 (.eval σ ρ (observe M))).map values

def useTwice : Comp := .ret (pairE (.var 0) (.var 0))
def useBoth : Comp := .ret (pairE (.var 0) (.var 1))

def oneCell : Store := Store.empty.alloc pickC []
def twoCells : Store := oneCell.alloc pickC []
def readyCell : Store := oneCell.setMemo 0 (.done vA)

theorem transport_renaming :
    observeFrom oneCell [.need 0] useTwice = observeFrom twoCells [.need 1] useTwice ∧
      observeFrom oneCell [.need 0] useTwice = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem identity_split :
    observeFrom oneCell [.need 0, .need 0] useBoth = some [pair vA vA, pair vB vB] ∧
      observeFrom twoCells [.need 0, .need 1] useBoth =
        some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

theorem role_loss :
    observeFrom readyCell [.need 0] useTwice = some [pair vA vA] ∧
      observeFrom oneCell [.need 0] useTwice = some [pair vA vA, pair vB vB] := by
  decide +kernel

def forkTwice : Comp := .choose (.force (.var 0)) (.force (.var 0))

/-- The second alternative started from the last store of the first. -/
def siblingMerged : Option (List (Val Nat)) :=
  match run (observed program) 200 (.eval oneCell [.need 0] (.force (.var 0))) with
  | some L₁ =>
      match L₁.getLast? with
      | some r =>
          (run (observed program) 200 (.eval r.2 [.need 0] (.force (.var 0)))).map
            fun L₂ => values L₁ ++ values L₂
      | none => none
  | none => none

theorem sibling_merge :
    (run (observed program) 200 (.eval oneCell [.need 0] forkTwice)).map values =
        some [vA, vB, vA, vB] ∧
      siblingMerged = some [vA, vB, vB] := by
  decide +kernel

/-! ## The branch's own world at unmatched returns -/

/-- Reset the cache of every cell the ancestor already had to its ancestor value. -/
def revertTo (σ₀ σ : Store) : Store :=
  { σ with cells := σ.cells.mapIdx fun i c =>
      match σ₀.cells[i]? with
      | some c₀ => { c with memo := c₀.memo }
      | none => c }

/-- A residual: the value of an unmatched equation. -/
def residualHeaded : Outcome → Bool
  | .ok v =>
      match v.spine with
      | some (c, _) => c == symResidual
      | none => false
  | _ => false

/-- Forward the unmatched returns with the ancestor's world. -/
def ancestorForward (σ₀ : Store) (L : List Result) : List Result :=
  L.map fun r => if residualHeaded r.1 then (r.1, revertTo σ₀ r.2) else r

/-- The continuation of `keep x = Pair (rwOnlyA x) x`, normalized. -/
def keepCont : Comp := .call normHead [pairE (.var 0) (.var 1)]

/-- The residual discriminator with a given forwarding of `rwOnlyA`'s returns. -/
def keepWith (forward : Store → List Result → List Result) (producer : Nat) :
    Option (List (Val Nat)) :=
  let σ₀ := Store.empty.alloc (.call producer []) []
  match run (observed program) 200 (.eval σ₀ [.need 0] (.call fRwOnlyA [.var 0])) with
  | some L₁ => (run (observed program) 200 (.seqK keepCont [.need 0] (forward σ₀ L₁))).map values
  | none => none

theorem keep_branch_world :
    keepWith (fun _ L => L) fSp1 =
        some [pair (residual (tagged symB sym1)) (tagged symB sym1),
          pair (residual (tagged symB sym2)) (tagged symB sym2)] ∧
      (keepWith (fun _ L => L) fSp2).map List.length = some 3 ∧
      (keepWith (fun _ L => L) fSp3).map List.length = some 3 := by
  decide +kernel

theorem keep_ancestor_world :
    (keepWith ancestorForward fSp1).map List.length = some 4 ∧
      (keepWith ancestorForward fSp2).map List.length = some 9 ∧
      (keepWith ancestorForward fSp3).map List.length = some 7 := by
  decide +kernel


/-! ## A ready container may retain pending fields -/

private def observationSummary (p : Program) (fuel : Nat) (store : Store)
    (environment : List (Val Nat)) (computation : Comp) :
    Option (List (List Nat) × List (Val Nat)) :=
  (run (observed p) fuel (.eval store environment (observe computation))).map
    fun results => (results.map (fun result => result.2.trace), values results)

private def fieldStore : Store :=
  Store.empty.alloc (.emit 17 (.ret (.sym 3))) []

private def fieldValue : Val Nat := .app (.sym 100) (.need 0)

private def readyContainer : Store :=
  (fieldStore.alloc (.ret (.sym 999)) []).setMemo 1 (.done fieldValue)

private def fieldObservation (store : Store) (value : Val Nat) :
    Option (List (List Nat) × List (Val Nat)) :=
  observationSummary [] 100 store [value] (.ret (.var 0))

/-- A cached parent already has its outer constructor. Reading that weak head
neither executes its pending field nor licenses treating that field as code. -/
theorem ready_parent_keeps_pending_field :
    run [] 10 (.forceVal readyContainer (.need 1)) =
      some [(.ok fieldValue, readyContainer)] := by
  decide +kernel

/-- Constructor matching must see the retained root's value. Exposing that
root and accepting its constructor leaves the whole store unchanged, including
the effectful field that this pattern only binds. -/
theorem retained_root_case_preserves_pending_field :
    run [] 30 (.eval readyContainer [.need 1]
      (.seq (.force (.var 0))
        (.caseCon (.var 0) 100 1 (.ret (.sym 7)) .fail))) =
      some [(.ok (.sym 7), readyContainer)] := by
  decide +kernel

/-- Pruning on the private cell representation loses a successful constructor
match. The same pattern and continuation above succeed after root exposure. -/
theorem pruning_before_retained_root_exposure_loses_answer :
    run [] 30 (.eval readyContainer [.need 1]
      (.caseCon (.var 0) 100 1 (.ret (.sym 7)) .fail)) =
      some [(.fail, readyContainer)] := by
  decide +kernel

/-- Normalizing the complete container before the same constructor match
returns the same answer but executes the otherwise unused field. Root demand
and complete observation are therefore distinct operations. -/
theorem full_observation_before_root_case_adds_an_effect :
    (run (observed []) 100 (.eval readyContainer [.need 1]
      (.seq (normalized (.force (.var 0)))
        (.caseCon (.var 0) 100 1 (.ret (.sym 7)) .fail)))).map
      (fun results => (results.map (fun result => result.2.trace), values results)) =
      some ([[17]], [.sym 7]) := by
  decide +kernel

/-- Complete structural observation still demands an implicit child, including
when it is reached through a cached parent. The field effect happens once. -/
theorem ready_parent_observation_demands_field :
    fieldObservation readyContainer (.need 1) =
      some ([[17]], [.app (.sym 100) (.sym 3)]) := by
  decide +kernel

/-- Returning the same constructor through a ready indirection preserves the
observed answer and effects; the extra cell is not an observable field. -/
theorem ready_parent_observation_agrees_with_direct_field :
    fieldObservation readyContainer (.need 1) = fieldObservation fieldStore fieldValue := by
  decide +kernel

/-- An explicitly quoted field remains code under that same structural
observer. Readiness of its parent does not grant activation authority. -/
theorem quoted_field_stays_unexecuted :
    fieldObservation fieldStore (.app (.sym 100) (.code 0)) =
      some ([[]], [.app (.sym 100) (.code 0)]) ∧
    fieldObservation fieldStore (.app (.sym 100) (.need 0)) ≠
      fieldObservation fieldStore (.app (.sym 100) (.code 0)) := by
  decide +kernel

/-- A retained field in application-head position is observed just as an
argument field is; its producer contributes its effect once. -/
theorem observation_demands_retained_head_field :
    fieldObservation fieldStore (.app (.need 0) (.sym 8)) =
      some ([[17]], [.app (.sym 3) (.sym 8)]) := by
  decide +kernel

/-- Taking apart the application does not itself demand its head. A consumer
that binds that field and uses only the other field leaves the producer alone. -/
theorem uninspected_head_field_stays_pending :
    (run [] 100 (.eval fieldStore [.app (.need 0) (.sym 8)]
      (.caseApp (.var 0) (.ret (.var 1)) .fail))).map
        (fun results => (results.map (fun result => result.2.trace), values results)) =
      some ([[]], [.sym 8]) := by
  decide +kernel

/-- Inspecting the retained head requires its value. Comparing the private
reference itself gives a different answer and omits the demanded effect. -/
theorem head_inspection_requires_its_retained_value :
    (run [] 100 (.eval fieldStore [.app (.need 0) (.sym 8)]
      (.caseApp (.var 0)
        (.seq (.force (.var 0)) (.prim (.eq 1 0) [.var 0, .sym 3]))
        .fail))).map
        (fun results => (results.map (fun result => result.2.trace), values results)) =
      some ([[17]], [.sym 1]) ∧
    (run [] 100 (.eval fieldStore [.app (.need 0) (.sym 8)]
      (.caseApp (.var 0) (.prim (.eq 1 0) [.var 0, .sym 3]) .fail))).map
        (fun results => (results.map (fun result => result.2.trace), values results)) =
      some ([[]], [.sym 0]) := by
  decide +kernel

/-- A quotation in head position remains inert, including when returned
through a ready cell. Its body has no activation authority from that position. -/
theorem retained_quoted_head_stays_unexecuted :
    fieldObservation fieldStore (.app (.code 0) (.sym 8)) =
      some ([[]], [.app (.code 0) (.sym 8)]) ∧
    fieldObservation
      ((fieldStore.alloc (.ret (.sym 999)) []).setMemo 1 (.done (.code 0)))
      (.app (.need 1) (.sym 8)) =
      some ([[]], [.app (.code 0) (.sym 8)]) := by
  decide +kernel

/-! ## Map demand and an explicit collection boundary

These finite witnesses use the existing calculus and observer. They separate
effect order from result equality; they do not assert a general fusion law or
a translation theorem for any surface language.
-/

section MapDemand

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def mapCons (head tail : VExp) : VExp := .app (.app (.sym 100) head) tail

private def mapDouble : Rule := ⟨11, 1,
  .seq (.force (.var 0))
    (.caseCon (.var 0) 1 0 (.emit 11 (.ret (.sym 2)))
      (.caseCon (.var 0) 2 0 (.emit 12 (.ret (.sym 4))) .fail))⟩

private def mapIncrement : Rule := ⟨12, 1,
  .seq (.force (.var 0))
    (.caseCon (.var 0) 2 0 (.emit 22 (.ret (.sym 3)))
      (.caseCon (.var 0) 4 0 (.emit 24 (.ret (.sym 5))) .fail))⟩

/-- The current element is demanded; the recursive tail retains its producer
and lexical environment in the existing branch-local store. -/
private def mapStepRule (self element : Nat) : Rule := ⟨self, 1,
  .seq (.force (.var 0))
    (.caseCon (.var 0) 100 2
      (.seq (.call element [.var 0])
        (.need (.call self [.var 2]) (.ret (mapCons (.var 1) (.var 0)))))
      (.caseCon (.var 0) 101 0 (.ret (.sym 101)) .fail))⟩

private def mapFusedRule : Rule := ⟨15, 1,
  .seq (.force (.var 0))
    (.caseCon (.var 0) 100 2
      (.seq (.call 11 [.var 0])
        (.seq (.call 12 [.var 0])
          (.need (.call 15 [.var 3]) (.ret (mapCons (.var 1) (.var 0))))))
      (.caseCon (.var 0) 101 0 (.ret (.sym 101)) .fail))⟩

private def mapProgram : Program :=
  [mapDouble, mapIncrement, mapStepRule 13 11, mapStepRule 14 12, mapFusedRule]

private def mapInput : VExp := mapCons (.sym 1) (mapCons (.sym 2) (.sym 101))
private def mapPipeline : Comp := .need (.call 13 [mapInput]) (.call 14 [.var 0])
private def mapCollectedPipeline : Comp :=
  .seq (normalized (.call 13 [mapInput])) (.call 14 [.var 0])
private def mapFusedPipeline : Comp := .call 15 [mapInput]

private def mapSummary (computation : Comp) : Option (List (List Nat) × List (Val Nat)) :=
  observationSummary mapProgram 500 Store.empty [] computation

private def mapResult : Val Nat := .app (.app (.sym 100) (.sym 3))
  (.app (.app (.sym 100) (.sym 5)) (.sym 101))

theorem map_lazy_pipeline_trace :
    mapSummary mapPipeline = some ([[11, 22, 12, 24]], [mapResult]) := by
  decide +kernel

theorem map_collected_pipeline_trace :
    mapSummary mapCollectedPipeline = some ([[11, 12, 22, 24]], [mapResult]) := by
  decide +kernel

theorem map_fused_pipeline_trace :
    mapSummary mapFusedPipeline = some ([[11, 22, 12, 24]], [mapResult]) := by
  decide +kernel

theorem map_lazy_fused_agree : mapSummary mapPipeline = mapSummary mapFusedPipeline := by
  rw [map_lazy_pipeline_trace, map_fused_pipeline_trace]

theorem map_collection_barrier_is_observable :
    mapSummary mapCollectedPipeline ≠ mapSummary mapFusedPipeline := by
  rw [map_collected_pipeline_trace, map_fused_pipeline_trace]
  decide

end MapDemand

/-- One shared producer emits once; deliberately resampling emits twice even
when both observations return the same pair. -/
theorem machine_shared_and_resampled_events :
    machineObservations program 200 (.need (.emit 11 (.ret (.sym symA))) useTwice) =
      [(.value (mpair mA mA), [11])] ∧
    machineObservations program 200 (.delay (.emit 11 (.ret (.sym symA))) useTwice) =
      [(.value (mpair mA mA), [11, 11])] := by
  decide +kernel

/-- Source argument lowering allocates one shared producer even when the
called equation returns two uses inside a constructor. The machine completes
and the producer event occurs only once. -/
theorem source_shared_parameter_emits_once :
    let code := (Witnesses.call1 Witnesses.fnSame
      (.emit 11 (Witnesses.k0 Witnesses.symA))).toCore .need id
    Halted (Witnesses.program.toCore .need) code 400 ∧
      machineObservations (Witnesses.program.toCore .need) 400 code =
        [(.value (mpair mA mA), [11])] := by
  dsimp only
  constructor
  · unfold Halted
    decide +kernel
  · decide +kernel

/-- The same source under the name profile answers with the same pair, but
runs the producer event twice. Equal answers do not license this replacement
when producer events are observed. -/
theorem source_resampled_parameter_emits_twice :
    let code := (Witnesses.call1 Witnesses.fnSame
      (.emit 11 (Witnesses.k0 Witnesses.symA))).toCore .name id
    Halted (Witnesses.program.toCore .name) code 400 ∧
      machineObservations (Witnesses.program.toCore .name) 400 code =
        [(.value (mpair mA mA), [11, 11])] := by
  dsimp only
  constructor
  · unfold Halted
    decide +kernel
  · decide +kernel

/-- Equal answers from sibling branches retain separate event sequences. -/
theorem machine_sibling_event_occurrences :
    machineObservations program 120
      (.choose (.emit 11 (.ret (.sym symA))) (.emit 22 (.ret (.sym symA)))) =
      [(.value mA, [11]), (.value mA, [22])] := by
  decide +kernel

/-- A failed branch retains effects already emitted before the failure. -/
theorem machine_failed_branch_events :
    machineObservations program 80 (.emit 11 .fail) =
      [(.retryableFault (.domain .fail), [11])] := by
  decide +kernel

/-- Equal empty heaps cannot justify forgetting an emitted event. -/
theorem equal_heap_does_not_erase_emission :
    ¬ Corr [] (Store.empty.emit 11) initialWorld := by
  intro h
  have events := h.events
  simp [initialWorld, Store.empty, Store.emit] at events

/-! ## Shared-return observer boundary -/

/-- The shared-return implementation retains the selected producer value:
`same pick` has just the two diagonal pairs. -/
theorem shared_samePick :
    SharedFinished program samePickCall 200 ∧
      machineValues (sharedAnswers program 200 samePickCall) = [mpair mA mA, mpair mB mB] := by
  constructor
  · unfold SharedFinished
    apply List.length_eq_zero_iff.mp
    decide +kernel
  · decide +kernel

/-- Equal answers from distinct alternatives remain separate occurrences in
the shared-return representation. -/
theorem shared_duplicate_occurrences :
    let code := .choose (.emit 11 (.ret (.sym symA))) (.emit 22 (.ret (.sym symA)))
    SharedFinished program code 120 ∧
      sharedAnswers program 120 code = [.value mA, .value mA] := by
  dsimp only
  constructor
  · unfold SharedFinished
    apply List.length_eq_zero_iff.mp
    decide +kernel
  · decide +kernel

/-- Receipt erasure admits an answer comparison that an event observer must
reject: sharing emits once, resampling twice. Both shared runs finish, so
equality of their answer lists is not an empty-prefix coincidence. -/
theorem shared_answers_do_not_determine_events :
    let shared := .need (.emit 11 (.ret (.sym symA))) useTwice
    let resampled := .delay (.emit 11 (.ret (.sym symA))) useTwice
    SharedFinished program shared 200 ∧ SharedFinished program resampled 200 ∧
      sharedAnswers program 200 shared = sharedAnswers program 200 resampled ∧
      machineObservations program 200 shared ≠ machineObservations program 200 resampled := by
  dsimp only
  refine ⟨?_, ?_, by decide +kernel, ?_⟩
  · unfold SharedFinished
    apply List.length_eq_zero_iff.mp
    decide +kernel
  · unfold SharedFinished
    apply List.length_eq_zero_iff.mp
    decide +kernel
  · rw [machine_shared_and_resampled_events.1, machine_shared_and_resampled_events.2]
    decide

/-- The recorded shared representation distinguishes choose-once reuse from
resampling by their actual retained event histories. -/
theorem shared_recorded_need_and_resampling :
    sharedObservations program 200 (.need (.emit 11 (.ret (.sym symA))) useTwice) =
      some [(.value (mpair mA mA), [11])] ∧
    sharedObservations program 200 (.delay (.emit 11 (.ret (.sym symA))) useTwice) =
      some [(.value (mpair mA mA), [11, 11])] := by
  constructor <;> decide +kernel

/-- Duplicate answers remain distinct branches with their own effect histories. -/
theorem shared_recorded_sibling_events :
    sharedObservations program 120
      (.choose (.emit 11 (.ret (.sym symA))) (.emit 22 (.ret (.sym symA)))) =
      some [(.value mA, [11]), (.value mA, [22])] := by
  decide +kernel

/-- Forgetting is explicit: a completed answer-only run cannot claim that an
emission-free computation has a recorded empty history. -/
theorem shared_erased_history_unavailable :
    SharedFinished program (.ret (.sym symA)) 80 ∧
    sharedObservations program 80 (.ret (.sym symA)) false = none ∧
    sharedObservations program 80 (.ret (.sym symA)) true = some [(.value mA, [])] := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  unfold SharedFinished
  apply List.length_eq_zero_iff.mp
  decide +kernel

/-- A failed branch retains the emission preceding its failure. -/
theorem shared_recorded_failed_branch :
    sharedObservations program 80 (.emit 11 .fail) =
      some [(.retryableFault (.domain .fail), [11])] := by
  decide +kernel

/-- Pause after the producer has emitted and before observation completes.
Resumption retains that receipt and forces the shared value without replay. -/
theorem shared_recorded_resume :
    let core := SharedContinuation.sharedCore
      (NeedContinuation.program (machineSpec (observed program)))
    let initial := SharedContinuation.encode
      (sharedInitial (.need (.emit 11 (.ret (.sym symA))) useTwice) true)
    let paused := MachineCore.runSlice core 56 initial
    let resumed := MachineCore.runSlice core 200 paused.1
    paused.1.1.frontier.length = 1 ∧
      ((NeedContinuation.machines paused.1.1.decode).mapM
        NeedExecution.CoreMachine.readback?).map
          (List.map fun m => m.world.receipts.effects) = some [[11]] ∧
      ((NeedContinuation.machines resumed.1.1.decode).mapM
        NeedExecution.CoreMachine.readback?).map (List.filterMap haltedObservation) =
          some [(.value (mpair mA mA), [11])] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The eager divergent witness never acquires a completed recorded run.
This follows from the independent source nonderivability result, not a timeout. -/
theorem recorded_eager_loop_never_finishes (steps : Nat) :
    ¬ SharedFinished (Witnesses.programExt.toCore .value)
      (Witnesses.konstLoop.toCore .value id) steps true := by
  intro done
  obtain ⟨results, source, _⟩ := shared_answers_backward done
  exact Witnesses.konstLoop_value_diverges results source

/-- Every pause of that nonterminating computation still has exact rich
readback and makes reference progress at the proved bounded overhead. Infinite
administration cannot account for its divergence. -/
theorem recorded_eager_loop_productive_prefix (steps : Nat) :
    ∃ count ≤ steps, steps ≤ 2 * count + 1 ∧
      sharedReadback (Witnesses.programExt.toCore .value) steps
        (Witnesses.konstLoop.toCore .value id) =
      some (((orderedMachine (Witnesses.programExt.toCore .value)).expandFirst)^[count]
        [initialMachine (observe (Witnesses.konstLoop.toCore .value id))]) := by
  obtain ⟨count, bound, productive, readback⟩ :=
    shared_readback_prefix (Witnesses.programExt.toCore .value)
      (Witnesses.konstLoop.toCore .value id) steps
  exact ⟨count, bound, productive (recorded_eager_loop_never_finishes steps), readback⟩

/-- The same source expression under call-time choice does finish: its unused
diverging argument remains suspended in the recorded machine. -/
theorem recorded_unused_loop_finishes :
    sharedObservations (Witnesses.programExt.toCore .need) 400
      (Witnesses.konstLoop.toCore .need id) = some [(.value mA, [])] := by
  decide +kernel

/-! ## Constructor returns and structural consumer demand -/

def fieldProducer : Comp := .emit 91 (.ret (.sym symA))

/-- Returning an outer constructor retains its pending field rather than
running it or replacing its cell by the producer's source. -/
def pendingConstructorReturn : Comp :=
  .need fieldProducer (.ret (.app (.sym fSame) (.var 0)))

def demandReturnedTwice : Comp :=
  .seq pendingConstructorReturn
    (.seq (normalized (.ret (.var 0))) (normalized (.ret (.var 0))))

theorem constructor_return_retains_field :
    run (observed program) 40 (.eval Store.empty [] pendingConstructorReturn) =
      some [(.ok (.app (.sym fSame) (.need 0)), Store.empty.alloc fieldProducer [])] ∧
    (Val.app (.sym fSame) (.need 0) : Val Nat).isCell = false ∧
    (Val.app (.sym fSame) (.need 0) : Val Nat).noSusp = false := by
  refine ⟨by decide +kernel, rfl, rfl⟩

/-- A declared callable head remains a data head during structural demand. -/
theorem callable_looking_value_stays_inert :
    candidates program fSame 1 ≠ [] ∧
    run (observed program) 100
      (.eval Store.empty [.app (.sym fSame) (.sym symA)] (.call normHead [.var 0])) =
      some [(.ok (.app (.sym fSame) (.sym symA)), Store.empty)] := by
  constructor <;> decide +kernel

/-- Two demands of the returned field keep one cached producer and one
emission. The second demand receives the completed constructor unchanged. -/
theorem returned_field_demanded_once :
    (run (observed program) 200 (.eval Store.empty [] demandReturnedTwice)).map
      (List.map fun result => (result.1, result.2.trace, result.2.cells[0]?.map Suspension.memo)) =
        some [(.ok (.app (.sym fSame) (.sym symA)), [91], some (.done vA))] := by
  decide +kernel

def sharedReturnedChoice : Comp :=
  .need (.emit 92 (.choose (.ret (.sym symA))
    (.choose (.ret (.sym symA)) (.ret (.sym symB)))))
    (.ret (pairE (.app (.sym fSame) (.var 0)) (.app (.sym fSame) (.var 0))))

/-- Repeated equal producer alternatives remain separate ordered answers.
Both returned fields share their branch's one choice and single emission. -/
theorem returned_choice_keeps_duplicates_and_correlation :
    (run (observed program) 200 (.eval Store.empty [] (observe sharedReturnedChoice))).map
      (List.map fun result => (result.1, result.2.trace)) = some [
        (.ok (pair (.app (.sym fSame) vA) (.app (.sym fSame) vA)), [92]),
        (.ok (pair (.app (.sym fSame) vA) (.app (.sym fSame) vA)), [92]),
        (.ok (pair (.app (.sym fSame) vB) (.app (.sym fSame) vB)), [92])] := by
  decide +kernel

/-- Quoted code is ready opaque data. Normalization does not activate it. -/
theorem quoted_callable_not_activated :
    (run (observed program) 100
      (.eval Store.empty [] (normalized (.quote fieldProducer)))).map
      (List.map fun result => (result.1, result.2.trace)) = some [(.ok (.code 0), [])] ∧
    (run (observed program) 100
      (.eval Store.empty [] (strictRun (.quote fieldProducer)))).map
      (List.map fun result => (result.1, result.2.trace)) = some [(.ok vA, [91])] := by
  constructor <;> decide +kernel

/-- The actual recorded shared machine retains the source's single effect
through constructor return and repeated consumer demand. -/
theorem recorded_returned_field_demanded_once :
    sharedObservations program 600 demandReturnedTwice =
      some [(.value (.app (.sym fSame) mA), [91])] := by
  decide +kernel

/-- Equal completed values and effect traces do not imply equal internal
administration: repeated preparation can change private allocation counters.
An observer of those identities cannot erase the extra preparation. -/
theorem ready_value_observation_differs_from_administration :
    let returned := Comp.ret (.app (.sym fSame) (.sym symA))
    sharedObservations program 600 returned = some [(.value (.app (.sym fSame) mA), [])] ∧
    sharedObservations program 600 (normalized returned) = some [(.value (.app (.sym fSame) mA), [])] ∧
    (sharedReadback program 600 returned).map (List.map fun machine => machine.world.nextCell) ≠
      (sharedReadback program 600 (normalized returned)).map (List.map fun machine => machine.world.nextCell) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Retained carriers at value-reader boundaries -/

/-- A field created while producing a constructor exists in its result's
store and cannot be resolved using the ancestor's empty heap. -/
theorem returned_field_requires_refined_store :
    let retained := Store.empty.alloc fieldProducer []
    let value := Val.app (.sym fSame) (.need 0)
    value.referencesSatisfy (fun i => i < retained.cells.length) ∧
    ¬ value.referencesSatisfy (fun i => i < Store.empty.cells.length) ∧
    run (observed program) 100 (.forceVal Store.empty (.need 0)) = none ∧
    run (observed program) 100 (.forceVal retained (.need 0)) =
      some [(.ok vA, (retained.emit 91).setMemo 0 (.done vA))] := by
  refine ⟨by simp [Val.referencesSatisfy, Store.alloc, Store.empty],
    by simp [Val.referencesSatisfy, Store.empty], by decide +kernel, by decide +kernel⟩

/-- A normalizer does not validate an injected code carrier. This reference
is ready opaque data but is absent from the supplied heap. Closed execution
cannot manufacture it, by `run_closed_referencesClosed`. -/
theorem readiness_does_not_validate_carrier :
    (Val.code 0 : Val Nat).noSusp = true ∧
    ¬ (Val.code 0 : Val Nat).referencesSatisfy (fun i => i < Store.empty.cells.length) ∧
    run (observed program) 100
      (.eval Store.empty [.code 0] (normalized (.ret (.var 0)))) =
        some [(.ok (.code 0), Store.empty)] := by
  refine ⟨rfl, by simp [Val.referencesSatisfy, Store.empty], by decide +kernel⟩

/-- Genuine quotation allocates its carrier while keeping the body inert.
It returns both a ready value and the live store that owns its captured code. -/
theorem quotation_constructs_live_carrier :
    let retained := Store.empty.alloc fieldProducer []
    run (observed program) 100 (.eval Store.empty [] (normalized (.quote fieldProducer))) =
      some [(.ok (.code 0), retained)] ∧
    retained.referencesClosed ∧
    (Val.code 0 : Val Nat).referencesSatisfy (fun i => i < retained.cells.length) ∧
    retained.trace = [] := by
  refine ⟨by decide +kernel, ?_, by simp [Val.referencesSatisfy, Store.alloc, Store.empty], rfl⟩
  exact Store.referencesClosed_alloc Store.referencesClosed_empty fieldProducer
    (by intro value member; cases member)

/-- A producer can change the world while returning the same ready value.
An atom-only equality check does not license restoring the prior carrier. -/
theorem same_value_still_changes_world :
    run program 100 (.eval Store.empty [] (.ret (.sym symA))) =
      some [(.ok vA, Store.empty)] ∧
    run program 100 (.eval Store.empty [] (.emit 91 (.ret (.sym symA)))) =
      some [(.ok vA, Store.empty.emit 91)] ∧
    Store.empty.trace ≠ (Store.empty.emit 91).trace := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Pending continuation carriers -/

/-- The saved continuation captures a suspension even though the computation
that returns to it produces an ordinary constructor value. -/
def capturedSequence : Comp :=
  .need fieldProducer (.seq (.ret (.sym symA)) (.force (.var 1)))

def capturedCell : NeedReference.CellId := initialWorld.freshCell 0

/-- An actual six-transition prefix, paused before the saved continuation runs. -/
def capturedPause : MMachine :=
  (NeedReference.runFrontier (machineSpec program) 6 [initialMachine capturedSequence]).headD
    (initialMachine capturedSequence)

theorem capturedPause_frontier :
    NeedReference.runFrontier (machineSpec program) 6 [initialMachine capturedSequence] =
      [capturedPause] := rfl

/-- The active value is plain data; the only operational reference in this
returned control is inside the saved continuation's environment. -/
theorem capturedPause_control :
    capturedPause.control = .returned (.value mA)
      [.resume (.seqRet (.force (.var 1)) [.need capturedCell])] := rfl

/-- The real prefix is reference-closed, while transporting its plain result
and continuation to the ancestor's empty heap loses the captured producer. -/
theorem paused_continuation_requires_refined_heap :
    (machineReferenceDiscipline program).machineClosed capturedPause ∧
    ¬ (machineReferenceDiscipline program).control
      (NeedCacheLaws.heapLive initialWorld.heap) capturedPause.control := by
  constructor
  · apply runFrontier_referencesClosed program capturedSequence 6
    rw [capturedPause_frontier]
    exact List.mem_singleton_self _
  · rw [capturedPause_control]
    intro valid
    have saved := ((machineReferenceDiscipline program).stack_cons.mp valid.2).1
    change EnvReferencesSatisfy (NeedCacheLaws.heapLive initialWorld.heap) [.need capturedCell] at saved
    obtain ⟨record, lookup⟩ := saved (.need capturedCell) (List.mem_singleton_self _)
    simp [initialWorld, NeedReference.Heap.empty, NeedReference.Heap.lookup] at lookup

/-- Resuming the computation evaluates its captured producer in its retained
world and commits the emission once. -/
theorem captured_continuation_commits_once :
    sharedObservations program 600 capturedSequence = some [(.value mA, [91])] := by
  decide +kernel

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Controls
