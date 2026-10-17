import Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt
import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.Machines.Cursor.ProofChecking

/-!
# MM2 execution evidence on the common proof-checking cursor

The rule meaning is the original recursive leave-inert list transition, not
receipt acceptance. A fixed initial workspace supplies the only zero-premise
rule. A step has exactly one premise: its actual predecessor workspace.
The executable witnesses are an initial-workspace request or the previously
specified complete physical-match receipt.

The shared graph checker resolves those predecessor edges and the common
retained worker checks a supplied source schedule. Its node count does not
bound the work inside an MM2 receipt check: matching must close and staged
sinks must be finalized. This instance retains the supported finite profile's
scope; it proves neither native byte decoding nor all current Rust factories.
Initial workspace indexing establishes a logical evidence boundary, not a
native capability or immutable-store implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2InferenceCursor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic
open Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor
open ReflectiveComputable

abbrev Workspace := List Atom

/-- The initial fact and the independent original source transition are the
entire inference meaning. Neither constructor mentions the executable checker. -/
inductive Rules (initial : Workspace) : List Workspace → Workspace → Prop where
  | seed : Rules initial [] initial
  | step {source target : Workspace} :
      cReflectiveSourceWorkQueueStep .leaveInert source = some target →
      Rules initial [source] target

inductive Witness where
  | seed
  | step (receipt : MM2StepReceipt.Receipt)
  deriving DecidableEq, Repr

def isInstance (initial : Workspace) : Witness → List Workspace → Workspace → Bool
  | .seed, [], conclusion => decide (conclusion = initial)
  | .step receipt, [source], conclusion => MM2StepReceipt.check source conclusion receipt
  | _, _, _ => false

theorem seed_exact (initial : Workspace) (premises : List Workspace) (conclusion : Workspace) :
    isInstance initial .seed premises conclusion = true ↔
      premises = [] ∧ conclusion = initial := by
  cases premises <;> simp [isInstance]

theorem step_exact (initial : Workspace) (receipt : MM2StepReceipt.Receipt)
    (premises : List Workspace) (conclusion : Workspace) :
    isInstance initial (.step receipt) premises conclusion = true ↔
      ∃ source, premises = [source] ∧ MM2StepReceipt.check source conclusion receipt = true := by
  cases premises with
  | nil => simp [isInstance]
  | cons source rest => cases rest <;> simp [isInstance]

def interface (initial : Workspace) : RuleWitness (Rules initial) where
  W := Witness
  isInstance := isInstance initial
  sound witness premises conclusion accepted := by
    cases witness with
    | seed =>
        obtain ⟨rfl, rfl⟩ := (seed_exact initial premises conclusion).mp accepted
        exact .seed
    | step receipt =>
        obtain ⟨source, rfl, checked⟩ := (step_exact initial receipt premises conclusion).mp accepted
        exact .step (MM2StepReceipt.check_sound source conclusion receipt checked)
  complete premises conclusion rule := by
    cases rule with
    | seed => exact ⟨.seed, by simp [isInstance]⟩
    | step moved =>
        obtain ⟨receipt, checked⟩ := MM2StepReceipt.check_complete _ _ moved
        exact ⟨.step receipt, checked⟩

theorem rule_admission_exact (initial : Workspace) (premises : List Workspace)
    (conclusion : Workspace) :
    (∃ witness, isInstance initial witness premises conclusion = true) ↔
      Rules initial premises conclusion :=
  ⟨fun ⟨witness, checked⟩ => (interface initial).sound witness premises conclusion checked,
    (interface initial).complete premises conclusion⟩

/-- This is the original GSLT's reflexive-transitive source reachability. -/
abbrev Reachable (initial target : Workspace) : Prop :=
  (reflectiveNativeListExecGSLT .leaveInert).MultiStep initial target

theorem derives_iff_reachable (initial target : Workspace) :
    Derives (Rules initial) target ↔ Reachable initial target := by
  constructor
  · intro derivation
    apply Derives.least (Reachable initial) _ derivation
    intro premises conclusion rule earlier
    cases rule with
    | seed => exact .refl _
    | @step source target moved =>
        exact Mettapedia.GSLT.Meredith.multiStep_trans _ (earlier source (by simp))
          (.step moved (.refl _))
  · intro reached
    have path := (Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen
      (reflectiveNativeListExecGSLT .leaveInert) initial target).mp reached
    clear reached
    induction path with
    | refl => exact .node [] initial .seed (by simp)
    | @tail middle final _ moved earlier =>
        exact .node [middle] final (.step moved) (by
          intro premise present
          have same : premise = middle := by simpa using present
          simpa only [same] using earlier)

abbrev Source := Store Workspace Witness Nat
abbrev SourceNode := StoredNode Workspace Witness Nat
abbrev Cursor (initial : Workspace) (source : Source) := CheckedCursor (interface initial) source

def begin (initial : Workspace) (source : Source) : Cursor initial source :=
  CheckedCursor.begin (interface initial) source

/-- A complete source derivation has an independently replayable finite graph;
conversely every accepted graph root has that original execution meaning. -/
theorem reachable_iff_graph (initial target : Workspace) :
    Reachable initial target ↔
      ∃ (nodes : List (Node Workspace Witness Nat)) (cache : Array Workspace) (root : Nat),
        replay (interface initial) nodes = some cache ∧ cache[root]? = some target := by
  rw [← derives_iff_reachable]
  exact derives_iff_checked_graph (interface initial) (0 : Nat) target

theorem stored_root_reachable (initial : Workspace) (source : Source)
    (schedule : List Nat) (result : State Workspace)
    (accepted : run (interface initial) source (start source) schedule = some result)
    (address : Nat) (target : Workspace) (found : rootAt result address = some target) :
    Reachable initial target :=
  (derives_iff_reachable initial target).mp
    (root_derivable (interface initial) source schedule result accepted address target found)

theorem checked_root_reachable (initial : Workspace) {source : Source}
    (cursor : Cursor initial source) (address : Nat) (target : Workspace)
    (found : (cursor.root address).map CheckedJudgment.judgment = some target) :
    Reachable initial target := by
  obtain ⟨evidence, _checked, same⟩ := Option.map_eq_some_iff.mp found
  exact same ▸ (derives_iff_reachable initial evidence.judgment).mp evidence.valid

/-- A finished accepting shared worker has consumed its entire supplied
schedule. Its retained checked root denotes original MM2 reachability. -/
theorem worker_root_reachable (initial : Workspace) (source : Source)
    (schedule : List Nat) (fuel : Nat)
    (report : Mettapedia.Machines.Cursor.ProofChecking.Report (interface initial) source)
    (completed : Mettapedia.Machines.OutcomeRunner.run
      (Mettapedia.Machines.Cursor.ProofChecking.machine (interface initial) source) fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin initial source) schedule) =
        .finished report)
    (accepted : report.accepted = true)
    (address : Nat) (target : Workspace)
    (found : (report.work.cursor.root address).map CheckedJudgment.judgment = some target) :
    Reachable initial target ∧ report.work.pending = [] ∧
      report.work.accepted = schedule.length := by
  have meaning := Mettapedia.Machines.Cursor.ProofChecking.check_only_report_meaning
    (interface initial) source (begin initial source) schedule fuel report completed
  have observed : Mettapedia.Machines.Cursor.ProofChecking.verdict report.work = some true := by
    simpa [accepted] using report.valid
  obtain ⟨empty, count, _executed⟩ := Mettapedia.Machines.Cursor.ProofChecking.completed_run
    (interface initial) source (begin initial source) schedule report.work meaning observed
  exact ⟨checked_root_reachable initial report.work.cursor address target found, empty, count⟩

namespace Controls

open MM2MatchingBatch.Controls (symbol term exec)
open MM2MatchingCursor (Row)

def activation : Atom := exec "a" [term "seed" [.var "id", .var "x"]]
  [term "out" [.var "x"]]
def seed (name : String) : Atom := term "seed" [symbol name, symbol "a"]
def output : Atom := term "out" [symbol "a"]
def initial : Workspace := [activation, seed "u", seed "v"]
def target : Workspace := [seed "u", seed "v", output]
def rows : List Row := [
  ([("x", symbol "a"), ("id", symbol "u")], [(seed "u", 1)]),
  ([("x", symbol "a"), ("id", symbol "v")], [(seed "v", 2)])]
def receipt : MM2StepReceipt.Receipt := ⟨activation, 256, rows⟩

def source : Source := ⟨1, fun address => match address with
  | 10 => some ⟨initial, .seed, [], 10⟩
  | 20 => some ⟨target, .step receipt, [10], 20⟩
  | 30 => some ⟨target, .step receipt, [20], 30⟩
  | _ => none⟩

private def checkedRoot (theory : Workspace) (store : Source) (schedule : List Nat)
    (address : Nat) : Option Workspace := do
  let cursor ← (begin theory store).advance schedule
  let checked ← cursor.root address
  pure checked.judgment

private def workerVerdict (theory : Workspace) (store : Source) (schedule : List Nat)
    (fuel : Nat) : Option Bool :=
  Mettapedia.Machines.Cursor.ProofChecking.completedVerdict
    (Mettapedia.Machines.OutcomeRunner.run
      (Mettapedia.Machines.Cursor.ProofChecking.machine (interface theory) store) fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin theory store) schedule))

theorem complete_receipt_admitted :
    isInstance initial (.step receipt) [initial] target = true := by decide +kernel

theorem borrowed_root_is_original_target :
    checkedRoot initial source [10, 20] 20 = some target := by decide +kernel

theorem shared_worker_accepts_complete_schedule :
    workerVerdict initial source [10, 20] 4 = some true := by decide +kernel

theorem false_initial_workspace_refused :
    isInstance initial .seed [] target = false ∧
      checkedRoot target source [10] 10 = none := by decide +kernel

theorem predecessor_is_mandatory :
    isInstance initial (.step receipt) [] target = false ∧
      checkedRoot initial source [20] 20 = none := by decide +kernel

theorem wrong_predecessor_refused :
    isInstance initial (.step receipt) [target] target = false ∧
      workerVerdict initial source [10, 20, 30] 5 = some false := by decide +kernel

def omittedMatches : Source := ⟨1, fun address => match address with
  | 10 => some ⟨initial, .seed, [], 10⟩
  | 20 => some ⟨target, .step { receipt with rows := rows.take 1 }, [10], 20⟩
  | _ => none⟩

theorem omitted_match_receipt_refused :
    workerVerdict initial omittedMatches [10, 20] 4 = some false := by decide +kernel

theorem repeated_predecessor_is_not_a_unary_step :
    isInstance initial (.step receipt) [initial, initial] target = false := by decide +kernel

theorem original_target_reachable : Reachable initial target := by
  apply (derives_iff_reachable initial target).mp
  exact .node [initial] target
    ((interface initial).sound (.step receipt) [initial] target complete_receipt_admitted)
    (by
      intro premise present
      have same : premise = initial := by simpa using present
      subst premise
      exact .node [] initial .seed (by simp))

end Controls

#print axioms seed_exact
#print axioms step_exact
#print axioms rule_admission_exact
#print axioms derives_iff_reachable
#print axioms reachable_iff_graph
#print axioms stored_root_reachable
#print axioms checked_root_reachable
#print axioms worker_root_reachable
#print axioms Controls.borrowed_root_is_original_target
#print axioms Controls.wrong_predecessor_refused
#print axioms Controls.omitted_match_receipt_refused

end Mettapedia.Languages.ProcessCalculi.MORK.MM2InferenceCursor
