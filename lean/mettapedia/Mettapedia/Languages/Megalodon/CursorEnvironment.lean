import Mettapedia.Languages.Megalodon.ObservedCursor
import Mettapedia.Languages.Megalodon.EnvironmentDependencyCheck

/-!
# Declaration footprints of local native proof rows

Each row records the environment queries its local checker can make. The
computed closure includes definition bodies, known propositions and negative
lookups. Agreement on that finite closure preserves the full observation,
including refusal and exhaustion, at every bound. No proof-tree reconstruction
or comparison of unrelated declarations is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.CursorEnvironment
open MathdataKernel BorrowedProofCursor NativeSupport EnvironmentDependency EnvironmentDependencyCheck

def requested : Witness → Support
  | .known name => {.knownName name}
  | .termApp argument _ body => termSupport argument ∪ termSupport body
  | .proofLam proposition => termSupport proposition
  | _ => ∅

def footprint (environment : Environment) (witness : Witness) : Support :=
  dependencyClosure environment (requested witness)

def revalidate (source target : Environment) (witness : Witness) : Bool :=
  agreementCheck source target (footprint source witness)

theorem observation_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (closed : Closed source support)
    (fuel : Nat) (witness : Witness) (conclusion : Judgment) (included : requested witness ⊆ support) :
    RuleObservation.observe target fuel witness conclusion = RuleObservation.observe source fuel witness conclusion := by
  cases witness with
  | hyp | proofApp | termLam | typeApp | typeLam => rfl
  | known name =>
      have member : Dependency.knownName name ∈ support := included (by simp [requested])
      have same := agreement.known member
      simp only [RuleObservation.observe, same]
      cases found : source.lookupKnown? name with
      | none => rfl
      | some proposition =>
          dsimp only
          rw [normalize_frame agreement closed (closed.known member found)]
  | termApp argument domain body =>
      have members : termSupport argument ⊆ support ∧ termSupport body ⊆ support :=
        Finset.union_subset_iff.mp included
      have typeSame := inferTerm_frame agreement (typeDepth := conclusion.context.typeDepth)
        (termContext := conclusion.context.terms) members.1
      have argumentSame := deltaNormalize_frame agreement closed (fuel := fuel) members.1
      simp only [RuleObservation.observe, typeSame, argumentSame]
      by_cases typed : inferTerm source conclusion.context.typeDepth conclusion.context.terms argument = some domain
      · simp only [typed, ne_eq, not_true_eq_false, ↓reduceIte]
        cases unfolded : deltaNormalize source fuel argument with
        | none => rfl
        | some normal =>
            have normalSupport := deltaNormalize_support closed members.1 unfolded
            have substitutionSupport : termSupport (Tm.instantiate normal body) ⊆ support :=
              (termSupport_instantiateAt_subset 0 normal body).trans
                (Finset.union_subset normalSupport members.2)
            dsimp only
            rw [normalize_frame agreement closed substitutionSupport]
      · simp [typed]
  | proofLam proposition =>
      have typeSame := inferTerm_frame agreement (typeDepth := conclusion.context.typeDepth)
        (termContext := conclusion.context.terms) included
      have normalizeSame := normalize_frame agreement closed (fuel := fuel) included
      cases conclusion.proposition <;> simp only [RuleObservation.observe, typeSame, normalizeSame]

theorem revalidate_observation {source target : Environment} {witness : Witness}
    (accepted : revalidate source target witness = true) (fuel : Nat) (conclusion : Judgment) :
    RuleObservation.observe target fuel witness conclusion = RuleObservation.observe source fuel witness conclusion :=
  observation_frame (agreementCheck_iff source target _ |>.mp accepted)
    (dependencyClosure_closed source (requested witness)) fuel witness conclusion
    (subset_dependencyClosure source (requested witness))

theorem revalidate_requirements {source target : Environment} {witness : Witness}
    (accepted : revalidate source target witness = true) (fuel : Nat) (conclusion : Judgment) :
    requirements target fuel witness conclusion = requirements source fuel witness conclusion := by
  rw [← RuleObservation.observe_erases, ← RuleObservation.observe_erases,
    revalidate_observation accepted]

theorem revalidate_instance {source target : Environment} {witness : Witness}
    (accepted : revalidate source target witness = true) (fuel : Nat)
    (parents : List Judgment) (conclusion : Judgment) :
    (BorrowedProofCursor.interface target fuel).isInstance witness parents conclusion =
      (BorrowedProofCursor.interface source fuel).isInstance witness parents conclusion := by
  simp only [BorrowedProofCursor.interface, revalidate_requirements accepted]

/-- Only addresses in the supplied schedule are required. The borrowed store
and cached judgments are retained unchanged; this concerns declaration edits,
not mutation of proof rows. -/
def RowsAgree {Origin : Type} (source target : Environment)
    (store : Mettapedia.Logic.DerivationGraph.BorrowedCursor.Store Judgment Witness Origin)
    (addresses : List Nat) : Prop :=
  ∀ address ∈ addresses, ∀ node, store.read address = some node →
    revalidate source target node.request = true

open Mettapedia.Logic.DerivationGraph.BorrowedCursor

theorem observed_step_frame {Origin : Type} {source target : Environment}
    {store : Store Judgment Witness Origin} {address : Nat}
    (agreement : ∀ node, store.read address = some node → revalidate source target node.request = true)
    (fuel : Nat) (state : State Judgment) :
    ObservedCursor.observeStep target fuel store state address =
      ObservedCursor.observeStep source fuel store state address := by
  cases found : store.read address with
  | none => simp [ObservedCursor.observeStep, found]
  | some node =>
      simp only [ObservedCursor.observeStep, found,
        revalidate_observation (agreement node found)]

/-- The complete worker observation is stable: status, retained checkpoint and
unfinished suffix all agree. This requires no reconstructed proof tree. -/
theorem walk_frame {Origin : Type} {source target : Environment}
    (store : Store Judgment Witness Origin) (fuel rows : Nat)
    (state : State Judgment) (schedule : List Nat)
    (agreement : RowsAgree source target store schedule) :
    ObservedCursor.walk target fuel store rows state schedule =
      ObservedCursor.walk source fuel store rows state schedule := by
  induction rows generalizing state schedule with
  | zero => cases schedule <;> rfl
  | succ rows ih =>
      cases schedule with
      | nil => rfl
      | cons address rest =>
          have first := observed_step_frame (agreement address (by simp)) fuel state
          have tail : RowsAgree source target store rest := by
            intro id member
            exact agreement id (by simp [member])
          simp only [ObservedCursor.walk, first]
          cases observed : ObservedCursor.observeStep source fuel store state address with
          | accepted next => exact ih next rest tail
          | refused | malformed | exhausted => rfl

theorem run_frame {Origin : Type} {source target : Environment}
    (store : Store Judgment Witness Origin) (fuel : Nat)
    (state : State Judgment) (schedule : List Nat)
    (agreement : RowsAgree source target store schedule) :
    run (BorrowedProofCursor.interface target fuel) store state schedule =
      run (BorrowedProofCursor.interface source fuel) store state schedule := by
  induction schedule generalizing state with
  | nil => rfl
  | cons address rest ih =>
      have first : step (BorrowedProofCursor.interface target fuel) store state address =
          step (BorrowedProofCursor.interface source fuel) store state address := by
        rw [← ObservedCursor.observeStep_erases, ← ObservedCursor.observeStep_erases,
          observed_step_frame (agreement address (by simp))]
      have tail : RowsAgree source target store rest := by
        intro id member
        exact agreement id (by simp [member])
      simp only [run, first]
      cases step (BorrowedProofCursor.interface source fuel) store state address with
      | none => rfl
      | some next => exact ih next tail

/-- Revalidation transports the validity of every cache entry in a completed
batch. The source checkpoint is reused as-is, including row identities. -/
theorem completed_cache_valid {Origin : Type} {source target : Environment}
    {store : Store Judgment Witness Origin} {fuel : Nat} {schedule : List Nat}
    {final : State Judgment}
    (accepted : run (BorrowedProofCursor.interface source fuel) store (start store) schedule = some final)
    (agreement : RowsAgree source target store schedule) : ObservedCursor.Valid target final := by
  apply ObservedCursor.run_valid (ObservedCursor.start_valid target store)
  rw [run_frame store fuel (start store) schedule agreement]
  exact accepted

namespace Controls
private def source : Environment :=
  { terms := [⟨"alias", .prop, some (.named "p")⟩, ⟨"p", .prop, none⟩]
    known := [⟨"proof", .named "alias"⟩] }
private def unrelated : Environment := { source with terms := ⟨"unused", .prop, none⟩ :: source.terms }
private def changed : Environment := { source with terms := [⟨"alias", .prop, none⟩, ⟨"p", .prop, none⟩] }

theorem unused_declaration_does_not_invalidate : revalidate source unrelated (.known "proof") = true := by decide
theorem hidden_definition_change_invalidates : revalidate source changed (.known "proof") = false := by decide
theorem adding_missing_known_invalidates :
    revalidate source { source with known := ⟨"missing", .named "p"⟩ :: source.known } (.known "missing") = false := by decide
theorem equally_absent_known_is_stable : revalidate source unrelated (.known "missing") = true := by decide
theorem purely_structural_rule_has_empty_footprint : footprint source (.proofApp (.named "p")) = ∅ := by decide
end Controls

end Mettapedia.Languages.Megalodon.CursorEnvironment
