import Mettapedia.Languages.Megalodon.ObservedCursor
import Mettapedia.Languages.Megalodon.NativeTheorem
import Mettapedia.Languages.Megalodon.NativeCursorWire

/-!
# Retained native sessions and closed theorem publication

Sessions retain a selected environment and borrowed source. Resumption executes
the observed cursor once, keeps every checked judgment, and returns the exact
unfinished suffix. Both bounds are explicit invocation parameters. Theorems
are indexed by the environment, not by a particular bound.

The batch operation cannot publish merely because an earlier root succeeded:
the submitted suffix must finish. Inspecting either a session or a theorem
does not instantiate its variables. Native ownership, opaque values and atomic
allocation/publication must implement these private construction boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeSession
open MathdataKernel BorrowedProofCursor
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

structure Session (environment : Environment) (source : Store Judgment Witness Nat) where
  private mk ::
  state : State Judgment
  valid : ObservedCursor.Valid environment state

def begin (environment : Environment) (source : Store Judgment Witness Nat) : Session environment source :=
  ⟨start source, ObservedCursor.start_valid environment source⟩

structure Resumed (environment : Environment) (source : Store Judgment Witness Nat) where
  private mk ::
  session : Session environment source
  status : ObservedCursor.Status
  pending : List NodeId

def resume {environment : Environment} {source : Store Judgment Witness Nat}
    (session : Session environment source) (normalizationBound rowBound : Nat) (schedule : List NodeId) :
    Resumed environment source :=
  let report := ObservedCursor.walk environment normalizationBound source rowBound session.state schedule
  ⟨⟨report.checkpoint, ObservedCursor.walk_valid environment normalizationBound source rowBound
      session.state schedule session.valid⟩, report.status, report.pending⟩

theorem resume_partition {environment : Environment} {source : Store Judgment Witness Nat}
    (session : Session environment source) (normalizationBound rowBound : Nat) (schedule : List NodeId) :
    let result := resume session normalizationBound rowBound schedule
    ∃ checked, schedule = checked ++ result.pending ∧ checked.length ≤ rowBound ∧
      run (BorrowedProofCursor.interface environment normalizationBound) source session.state checked =
        some result.session.state :=
  ObservedCursor.walk_partition environment normalizationBound source rowBound session.state schedule

theorem resume_retains_old_root {environment : Environment} {source : Store Judgment Witness Nat}
    (session : Session environment source) (normalizationBound rowBound : Nat) (schedule : List NodeId)
    {root : NodeId} {judgment : Judgment} (found : rootAt session.state root = some judgment) :
    rootAt (resume session normalizationBound rowBound schedule).session.state root = some judgment := by
  obtain ⟨checked, _, _, ran⟩ := resume_partition session normalizationBound rowBound schedule
  have keep (before after : State Judgment) (steps : List NodeId)
      (ran : run (BorrowedProofCursor.interface environment normalizationBound) source before steps = some after)
      (found : rootAt before root = some judgment) : rootAt after root = some judgment := by
    induction steps generalizing before with
    | nil => cases Option.some.inj ran; exact found
    | cons address rest ih =>
        cases first : step (BorrowedProofCursor.interface environment normalizationBound) source before address with
        | none => simp [run, first] at ran
        | some next =>
            exact ih next (by simpa [run, first] using ran)
              (step_preserves_root (BorrowedProofCursor.interface environment normalizationBound)
                source before next address root judgment first found)
  exact keep session.state _ checked ran found

def ValidTheorem (environment : Environment) (proposition : Tm) : Prop :=
  ∃ fuel, NativeTheorem.ClosedValid environment fuel proposition

structure Theorem (environment : Environment) where
  private mk ::
  proposition : Tm
  valid : ValidTheorem environment proposition

private theorem valid_of_root {environment : Environment} {state : State Judgment} {source : NodeId}
    {judgment : Judgment} {proposition : Tm} {goalFuel : Nat}
    (valid : ObservedCursor.Valid environment state) (found : rootAt state source = some judgment)
    (closed : judgment.context = ⟨0, [], []⟩)
    (formed : checkProposition environment 0 [] proposition = true)
    (normalized : normalize environment goalFuel proposition = some judgment.proposition) :
    ValidTheorem environment proposition := by
  obtain ⟨proofFuel, proof, inferred⟩ := ObservedCursor.retained_root_original valid found
  have derived := (derives_iff_original environment proofFuel judgment).mpr ⟨proof, inferred⟩
  have lifted := BudgetIndependent.derives_mono (Nat.le_max_left proofFuel goalFuel) derived
  obtain ⟨liftedProof, liftedInference⟩ :=
    (derives_iff_original environment (max proofFuel goalFuel) judgment).mp lifted
  have liftedNormal := FuelledConversionProfile.normalize_mono environment proposition judgment.proposition
    (Nat.le_max_right proofFuel goalFuel) normalized
  rw [closed] at liftedInference
  exact ⟨max proofFuel goalFuel, formed, liftedProof,
    (ProofJudgment.check_iff environment _ ⟨0, [], []⟩ liftedProof proposition).mpr
      ⟨judgment.proposition, liftedNormal, ProofJudgment.proves_of_infer liftedInference⟩⟩

inductive Publication (environment : Environment) where
  | accepted (theorem_ : Theorem environment)
  | refused
  | malformed
  | exhausted
  | unfinished (status : ObservedCursor.Status)

def Publication.isAccepted {environment : Environment} : Publication environment → Bool
  | .accepted _ => true
  | _ => false

def publish {environment : Environment} {source : Store Judgment Witness Nat}
    (session : Session environment source) (root : NodeId) (goalFuel : Nat) (proposition : Tm) :
    Publication environment :=
  match found : rootAt session.state root with
  | none => .malformed
  | some judgment =>
      if closed : judgment.context = ⟨0, [], []⟩ then
        if formed : checkProposition environment 0 [] proposition = true then
          match normalized : normalize environment goalFuel proposition with
          | none => .exhausted
          | some actual => if same : actual = judgment.proposition then
              .accepted ⟨proposition, valid_of_root session.valid found closed formed
                (same ▸ normalized)⟩ else .refused
        else .refused
      else .refused

def finish {environment : Environment} {source : Store Judgment Witness Nat}
    (result : Resumed environment source) (root : NodeId) (goalFuel : Nat) (proposition : Tm) :
    Publication environment :=
  if result.status = .finished ∧ result.pending = [] then publish result.session root goalFuel proposition
  else .unfinished result.status

theorem publish_accepts_iff {environment : Environment} {source : Store Judgment Witness Nat}
    (session : Session environment source) (root goalFuel : Nat) (proposition : Tm) :
    (publish session root goalFuel proposition).isAccepted = true ↔
      ∃ judgment, rootAt session.state root = some judgment ∧ judgment.context = ⟨0, [], []⟩ ∧
        checkProposition environment 0 [] proposition = true ∧
        normalize environment goalFuel proposition = some judgment.proposition := by
  unfold publish
  split
  · rename_i absent
    simp [Publication.isAccepted, absent]
  · rename_i judgment found
    split
    · rename_i closed
      split
      · rename_i formed
        split
        · rename_i exhausted
          simp [Publication.isAccepted, found, exhausted]
        · rename_i normal normalized
          split
          · rename_i same
            simp [Publication.isAccepted, found, closed, formed, normalized, same]
          · rename_i different
            simp [Publication.isAccepted, found, normalized, different]
      · rename_i unformed
        simp [Publication.isAccepted, found, unformed]
    · rename_i openContext
      simp [Publication.isAccepted, found, openContext]

theorem finish_accepts_iff {environment : Environment} {source : Store Judgment Witness Nat}
    (result : Resumed environment source) (root goalFuel : Nat) (proposition : Tm) :
    (finish result root goalFuel proposition).isAccepted = true ↔
      result.status = .finished ∧ result.pending = [] ∧
      ∃ judgment, rootAt result.session.state root = some judgment ∧ judgment.context = ⟨0, [], []⟩ ∧
        checkProposition environment 0 [] proposition = true ∧
        normalize environment goalFuel proposition = some judgment.proposition := by
  by_cases done_ : result.status = .finished ∧ result.pending = []
  · simp [finish, done_, publish_accepts_iff]
  · simp only [finish, if_neg done_, Publication.isAccepted, Bool.false_eq_true, false_iff]
    exact fun completed => done_ ⟨completed.1, completed.2.1⟩

theorem publish_correct {environment : Environment} {source : Store Judgment Witness Nat}
    {session : Session environment source} {root goalFuel : Nat} {proposition : Tm}
    {theorem_ : Theorem environment}
    (accepted : publish session root goalFuel proposition = .accepted theorem_) :
    theorem_.proposition = proposition ∧ ValidTheorem environment proposition := by
  have same : theorem_.proposition = proposition := by
    unfold publish at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · split at accepted
        · split at accepted
          · cases accepted
          · split at accepted
            · cases accepted
              rfl
            · cases accepted
        · cases accepted
      · cases accepted
  exact ⟨same, same ▸ theorem_.valid⟩

theorem finish_checks_whole_suffix {environment : Environment} {source : Store Judgment Witness Nat}
    {result : Resumed environment source} {root goalFuel : Nat} {proposition : Tm}
    {theorem_ : Theorem environment}
    (accepted : finish result root goalFuel proposition = .accepted theorem_) :
    result.status = .finished ∧ result.pending = [] ∧
      theorem_.proposition = proposition ∧ ValidTheorem environment proposition := by
  unfold finish at accepted
  split at accepted
  · rename_i complete
    exact ⟨complete.1, complete.2, publish_correct accepted⟩
  · cases accepted

/-- Syntax decoding supplies rows; it cannot mint a theorem or a retained
session. Invalid encodings appear as malformed rows to the observed cursor. -/
def sourceOfWire (revision : Nat) (read : NodeId → Option NativeSyntaxWire.Wire) :
    Store Judgment Witness Nat :=
  ⟨revision, fun address => (read address).bind NativeCursorWire.decodeNode⟩

theorem unfinished_batch_does_not_publish {environment : Environment} {source : Store Judgment Witness Nat}
    (result : Resumed environment source) (root goalFuel : Nat) (proposition : Tm)
    (pending : result.pending ≠ []) :
    finish result root goalFuel proposition = .unfinished result.status := by simp [finish, pending]

end Mettapedia.Languages.Megalodon.NativeSession
