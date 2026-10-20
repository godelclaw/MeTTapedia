import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution

/-!
# Retained execution for finite candidate source programs

Each candidate owns the installed executor's replay-certified scheduler state.
Resumption advances these states rather than rerunning earlier budgets. The
certificate contains the full source receipts in source and occurrence order.
Draining a replayed agenda earns complete receipt coverage independently of
the response checker; an empty unfinished agenda cannot be forged here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Execution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open NativeBindingEventAction (bound)
open FiniteFocusChecking

def source (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (pattern : Pattern) : BindingPipeline.Installed.Source :=
  ⟨bound ambient, .base (installed.programSort index), pattern⟩

abbrev Run (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (pattern : Pattern) :=
  BindingPipeline.Installed.CertifiedExecution.Session installed.indexed.operational
    (source installed index ambient pattern)

structure Batch (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (sources : List Pattern) where
  runs : (position : Fin sources.length) → Run installed index ambient sources[position]

variable {installed : Joined.Installed} {index : installed.Index}
  {ambient : List String} {sources : List Pattern}

namespace Batch

@[ext] theorem ext (first second : Batch installed index ambient sources)
    (same : ∀ position, first.runs position = second.runs position) : first = second := by
  cases first
  cases second
  congr
  exact funext same

def begin (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (sources : List Pattern) : Batch installed index ambient sources :=
  ⟨fun position => BindingPipeline.Installed.CertifiedExecution.begin
    installed.indexed.operational (source installed index ambient sources[position])⟩

/-- A fuel unit permits one retained scheduler tick for each source. This is
not a bound on physical running time or aggregate memory use. -/
def resume (batch : Batch installed index ambient sources) (fuel : Nat) :
    Batch installed index ambient sources := ⟨fun position => (batch.runs position).resume fuel⟩

@[simp] theorem resume_runs (batch : Batch installed index ambient sources) (fuel : Nat)
    (position : Fin sources.length) :
    (batch.resume fuel).runs position = (batch.runs position).resume fuel := rfl

theorem resume_add (batch : Batch installed index ambient sources) (first extra : Nat) :
    batch.resume (first + extra) = (batch.resume first).resume extra := by
  apply ext
  intro position
  exact (batch.runs position).resume_add first extra

@[simp] theorem resume_zero (batch : Batch installed index ambient sources) : batch.resume 0 = batch := by
  apply ext
  intro position
  apply BindingPipeline.Installed.CertifiedExecution.Session.ext
  · exact Nat.add_zero _
  · rfl

def settled (batch : Batch installed index ambient sources) : Bool :=
  (List.finRange sources.length).all fun position => (batch.runs position).state.agenda.isEmpty

theorem settled_exact (batch : Batch installed index ambient sources) :
    batch.settled = true ↔ ∀ position, (batch.runs position).state.agenda = [] := by
  simp [settled, List.all_eq_true]

theorem source_stable (batch : Batch installed index ambient sources) (position : Fin sources.length)
    (drained : (batch.runs position).state.agenda = []) (fuel : Nat) :
    ((batch.resume fuel).runs position).state = (batch.runs position).state := by
  change Scheduler.run _ fuel (batch.runs position).state = (batch.runs position).state
  exact Scheduler.run_idle _ _ _ drained

def sourceWitnesses (batch : Batch installed index ambient sources) (position : Fin sources.length) :
    List Witness :=
  (batch.runs position).receipts.map fun answer => ⟨sources[position], read answer⟩

def certificate (batch : Batch installed index ambient sources) : List Witness :=
  (List.finRange sources.length).flatMap batch.sourceWitnesses

theorem source_receipts_preserved (batch : Batch installed index ambient sources)
    (position : Fin sources.length) (fuel : Nat) :
    Scheduler.Prefix (batch.runs position).receipts ((batch.resume fuel).runs position).receipts :=
  (batch.runs position).receipts_preserved fuel

theorem source_witnesses_preserved (batch : Batch installed index ambient sources)
    (position : Fin sources.length) (fuel : Nat) :
    Scheduler.Prefix (batch.sourceWitnesses position) ((batch.resume fuel).sourceWitnesses position) := by
  obtain ⟨suffix, preserved⟩ := batch.source_receipts_preserved position fuel
  refine ⟨suffix.map (fun answer => ⟨sources[position], read answer⟩), ?_⟩
  simp only [sourceWitnesses, preserved, List.map_append]

theorem certificate_preserved (batch : Batch installed index ambient sources) (fuel : Nat)
    (witness : Witness) (member : witness ∈ batch.certificate) :
    witness ∈ (batch.resume fuel).certificate := by
  obtain ⟨position, range, member⟩ := List.mem_flatMap.mp member
  obtain ⟨suffix, preserved⟩ := batch.source_witnesses_preserved position fuel
  exact List.mem_flatMap.mpr ⟨position, range, by
    rw [preserved]
    exact List.mem_append_left _ member⟩

/-- Inserting later receipts into earlier source blocks need not preserve a
global prefix. It preserves the entire source-ordered certificate as a
sublist, including repeated payloads and distinct origins. -/
theorem certificate_sublist (batch : Batch installed index ambient sources) (fuel : Nat) :
    batch.certificate.Sublist (batch.resume fuel).certificate := by
  apply List.Sublist.flatMap_right
  intro position _
  obtain ⟨suffix, preserved⟩ := batch.source_witnesses_preserved position fuel
  rw [preserved]
  exact List.sublist_append_left _ _

theorem source_witnesses_stable (batch : Batch installed index ambient sources)
    (position : Fin sources.length) (drained : (batch.runs position).state.agenda = []) (fuel : Nat) :
    (batch.resume fuel).sourceWitnesses position = batch.sourceWitnesses position := by
  unfold sourceWitnesses BindingPipeline.Installed.CertifiedExecution.Session.receipts
  rw [batch.source_stable position drained fuel]

theorem certificate_stable (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (fuel : Nat) :
    (batch.resume fuel).certificate = batch.certificate := by
  unfold certificate
  apply congrArg (fun f => (List.finRange sources.length).flatMap f)
  funext position
  exact batch.source_witnesses_stable position ((batch.settled_exact).mp complete position) fuel

theorem witness_sound (batch : Batch installed index ambient sources)
    (witness : Witness) (member : witness ∈ batch.certificate) :
    witness.source ∈ sources ∧ Valid installed.indexed.operational.Environment (bound ambient)
      (.base (installed.programSort index)) witness.source witness.payload := by
  obtain ⟨position, _, found⟩ := List.mem_flatMap.mp member
  obtain ⟨answer, _, rfl⟩ := List.mem_map.mp found
  exact ⟨List.getElem_mem _, answer.valid⟩

theorem source_receipt_covered (batch : Batch installed index ambient sources)
    (position : Fin sources.length) (drained : (batch.runs position).state.agenda = [])
    (answer : StructuralDescent.Execution.RootAnswer installed.indexed.operational.Environment
      (bound ambient) (.base (installed.programSort index)) sources[position]) :
    answer ∈ (batch.runs position).receipts := by
  change answer ∈ Scheduled.receipts (batch.runs position).state
  rw [(batch.runs position).replay]
  have replay := (batch.runs position).replay
  rw [replay] at drained
  exact Scheduled.drained_receipts_complete installed.indexed.operational.Environment
      installed.indexed.operational.structural (bound ambient) (.base (installed.programSort index))
      sources[position] (batch.runs position).budget drained answer

/-- Complete source coverage is derived from the scheduler's independent
firing completeness, and retains the entire payload rather than endpoints. -/
theorem payload_covered (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (pattern : Pattern) (member : pattern ∈ sources)
    (payload : Payload) (valid : Valid installed.indexed.operational.Environment (bound ambient)
      (.base (installed.programSort index)) pattern payload) :
    (⟨pattern, payload⟩ : Witness) ∈ batch.certificate := by
  obtain ⟨n, bounded, same⟩ := List.getElem_of_mem member
  let position : Fin sources.length := ⟨n, bounded⟩
  have same' : sources[position] = pattern := same
  let answer : StructuralDescent.Execution.RootAnswer installed.indexed.operational.Environment
      (bound ambient) (.base (installed.programSort index)) sources[position] :=
    ⟨payload.index, payload.trace, payload.captured, payload.completed, payload.history,
      payload.target, by simpa only [same', Valid] using valid⟩
  have covered := batch.source_receipt_covered position
    ((batch.settled_exact).mp complete position) answer
  apply List.mem_flatMap.mpr
  refine ⟨position, List.mem_finRange _, List.mem_map.mpr ⟨answer, covered, ?_⟩⟩
  simp only [answer, NativeReceiptRechecking.read, same']

def finish (batch : Batch installed index ambient sources) : Batch installed index ambient sources :=
  ⟨fun position => (batch.runs position).finish⟩

theorem finish_settled (batch : Batch installed index ambient sources) : batch.finish.settled = true := by
  apply (batch.finish.settled_exact).mpr
  intro position
  exact (batch.runs position).finish_drained

def completionBudget (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (sources : List Pattern) : Nat :=
  (sources.map fun pattern => Scheduled.completeBudget installed.indexed.operational.Environment
    (bound ambient) (.base (installed.programSort index)) pattern).sum

theorem source_budget_le (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (sources : List Pattern) (position : Fin sources.length) :
    Scheduled.completeBudget installed.indexed.operational.Environment (bound ambient)
      (.base (installed.programSort index)) sources[position] ≤ completionBudget installed index ambient sources := by
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨sources[position], List.getElem_mem _, rfl⟩

theorem resume_settled (batch : Batch installed index ambient sources) (fuel : Nat)
    (enough : completionBudget installed index ambient sources ≤ fuel) :
    (batch.resume fuel).settled = true := by
  apply ((batch.resume fuel).settled_exact).mpr
  intro position
  let sourceBudget := Scheduled.completeBudget installed.indexed.operational.Environment
    (bound ambient) (.base (installed.programSort index)) sources[position]
  have bounded : sourceBudget ≤ fuel := le_trans (source_budget_le installed index ambient sources position) enough
  have fuelSplit : fuel = sourceBudget + (fuel - sourceBudget) := by omega
  rw [fuelSplit, resume_add]
  exact congrArg (·.agenda) (source_stable (batch.resume sourceBudget) position
    (batch.runs position).finish_drained (fuel - sourceBudget)) |>.trans
      (batch.runs position).finish_drained

theorem resume_source_state (batch : Batch installed index ambient sources) (fuel : Nat)
    (enough : completionBudget installed index ambient sources ≤ fuel) (position : Fin sources.length) :
    ((batch.resume fuel).runs position).state = (batch.finish.runs position).state := by
  let sourceBudget := Scheduled.completeBudget installed.indexed.operational.Environment
    (bound ambient) (.base (installed.programSort index)) sources[position]
  have bounded : sourceBudget ≤ fuel := le_trans (source_budget_le installed index ambient sources position) enough
  have fuelSplit : fuel = sourceBudget + (fuel - sourceBudget) := by omega
  rw [fuelSplit, resume_add]
  exact (batch.resume sourceBudget).source_stable (position := position) (fuel := fuel - sourceBudget)
    (batch.runs position).finish_drained

theorem resume_certificate (batch : Batch installed index ambient sources) (fuel : Nat)
    (enough : completionBudget installed index ambient sources ≤ fuel) :
    (batch.resume fuel).certificate = batch.finish.certificate := by
  unfold certificate
  apply congrArg (fun f => (List.finRange sources.length).flatMap f)
  funext position
  unfold sourceWitnesses BindingPipeline.Installed.CertifiedExecution.Session.receipts
  rw [batch.resume_source_state fuel enough position]

end Batch

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Execution
