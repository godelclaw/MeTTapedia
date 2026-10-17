import Mettapedia.GSLT.LanguageDef.CertificateGSLT
import Mettapedia.OSLF.NativeTypes.Certificates.DerivationGraph
import Mettapedia.Logic.DerivationGraph.CheckedCursor
import Mettapedia.Machines.Cursor.ProofChecking
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Borrowed source evidence for an authored calculus definition

The theory is the existing validated calculus definition. Source rows are the
existing `DAGNode` data, and their rule instances are admitted by the existing
scope-, binder- and side-condition-aware instantiator. A borrowed cursor reads
those rows, retains checked conclusions and source addresses, and never expands
a source proof tree. The original independent `RuleApplication` and `Derivation`
judgments remain the meaning of its accepted roots.

The source in this module is the elaborated calculus document. Its exact
authored-source recovery is reused below; textual `.module` parsing and native
cursor ownership are separate refinement obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.BorrowedCursor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.Logic.DerivationGraph.BorrowedCursor
  (State indexAt premiseValues step start rootAt)

/-- A source rule code after actual local admission. The proof is erased;
admission computes the original rule lookup, arguments and side conditions. -/
structure AdmittedInstance (definition : ValidatedCalculusLanguageDef) where
  ruleInstance : RuleInstance
  premises : List Pattern
  conclusion : Pattern
  admitted : instantiateRule? definition ruleInstance = some (premises, conclusion)

def admitInstance? (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :
    Option (AdmittedInstance definition) :=
  match admitted : instantiateRule? definition ruleInstance with
  | none => none
  | some (premises, conclusion) => some ⟨ruleInstance, premises, conclusion, admitted⟩

private theorem admitInstance?_none {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} (refused : instantiateRule? definition ruleInstance = none) :
    admitInstance? definition ruleInstance = none := by
  unfold admitInstance?
  split
  · rfl
  · rename_i premises conclusion admitted
    rw [refused] at admitted
    cases admitted

private theorem admitInstance?_some {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    admitInstance? definition ruleInstance = some ⟨ruleInstance, premises, conclusion, accepted⟩ := by
  unfold admitInstance?
  split
  · rename_i refused
    rw [accepted] at refused
    cases refused
  · rename_i actualPremises actualConclusion admitted
    have equal := Option.some.inj (accepted.symm.trans admitted)
    cases equal
    rfl

/-- No new logical rules: this is the existing independent local application
relation, presented in the common finite-premise format. -/
abbrev presentation (definition : ValidatedCalculusLanguageDef) : Presentation where
  Judgment := Pattern
  Rule := AdmittedInstance definition
  conclusion := AdmittedInstance.conclusion
  premises := AdmittedInstance.premises

theorem admitInstance?_exact (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern) :
    (∃ admitted, admitInstance? definition ruleInstance = some admitted ∧
      admitted.premises = premises ∧ admitted.conclusion = conclusion) ↔
      RuleApplication definition ruleInstance premises conclusion := by
  rw [← instantiateRule?_eq_some_iff_application]
  unfold admitInstance?
  split
  · rename_i refused
    simp [refused]
  · rename_i actualPremises actualConclusion computed
    simp [computed, Prod.mk.injEq]

/-- The presentation's local rule relation is exactly source rule application,
with the actual submitted source instance retained as its witness. -/
theorem rules_iff_application (definition : ValidatedCalculusLanguageDef)
    (premises : List Pattern) (conclusion : Pattern) :
    (presentation definition).rules premises conclusion ↔
      ∃ ruleInstance, RuleApplication definition ruleInstance premises conclusion := by
  constructor
  · rintro ⟨code, rfl, rfl⟩
    exact ⟨code.ruleInstance, instantiateRule?_eq_some_iff_application.mp code.admitted⟩
  · rintro ⟨ruleInstance, application⟩
    exact ⟨⟨ruleInstance, premises, conclusion,
      instantiateRule?_eq_some_iff_application.mpr application⟩, rfl, rfl⟩

private theorem nonempty_derivationList {definition : ValidatedCalculusLanguageDef}
    (premises : List Pattern) (children : ∀ premise ∈ premises, Nonempty (Derivation definition premise)) :
    Nonempty (DerivationList definition premises) := by
  induction premises with
  | nil => exact ⟨.nil⟩
  | cons first rest ih =>
      obtain ⟨head⟩ := children first (by simp)
      obtain ⟨tail⟩ := ih (fun premise member => children premise (by simp [member]))
      exact ⟨.cons head tail⟩

/-- The graph rules generate precisely the existing source derivations.
This is an earned bridge, rather than a new definition of source meaning. -/
theorem source_derivation_iff_rules (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔
      Mettapedia.Logic.Derives (presentation definition).rules goal := by
  constructor
  · rintro ⟨tree⟩
    apply tree.sound_of_ruleApplications
      (fun goal => Mettapedia.Logic.Derives (presentation definition).rules goal)
    intro ruleInstance premises conclusion application children
    exact .node premises conclusion
      ((rules_iff_application definition premises conclusion).mpr ⟨ruleInstance, application⟩) children
  · intro derived
    apply Mettapedia.Logic.Derives.least
      (fun goal => Nonempty (Derivation definition goal)) ?_ derived
    intro premises conclusion instance_ children
    obtain ⟨ruleInstance, application⟩ := (rules_iff_application definition _ _).mp instance_
    obtain ⟨children⟩ := nonempty_derivationList premises children
    exact ⟨.byRule ruleInstance application children⟩

theorem source_derivation_iff_presentation (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔ Nonempty ((presentation definition).Derivation goal) := by
  rw [Presentation.nonempty_derivation_iff_derives, source_derivation_iff_rules]

/-- Source-addressed rows. The revision is checked dynamically, while checked
cursors below are indexed by this actual source and calculus definition. -/
structure Source where
  revision : Nat
  read : Nat → Option DAGNode

/-- Decode one actual authored row. A source address is not allowed to borrow
another row's identity. A malformed or absent rule remains a refusal. -/
def readRow (definition : ValidatedCalculusLanguageDef) (source : Source) (address : Nat) :
    Option (Mettapedia.Logic.DerivationGraph.BorrowedCursor.StoredNode
      Pattern (AdmittedInstance definition) Nat) := do
  let row ← source.read address
  if row.id ≠ address then none else do
    let rule ← admitInstance? definition row.ruleInstance
    pure ⟨rule.conclusion, rule, row.children, row.id⟩

def store (definition : ValidatedCalculusLanguageDef) (source : Source) :
    Mettapedia.Logic.DerivationGraph.BorrowedCursor.Store
      Pattern (AdmittedInstance definition) Nat :=
  ⟨source.revision, readRow definition source⟩

/-- Independent admission of the actual supplied source row. Its source rule
application determines the conclusion; a claimed display label does not. -/
def LicensedStep (definition : ValidatedCalculusLanguageDef) (source : Source)
    (before : State Pattern) (address : Nat) (after : State Pattern) : Prop :=
  before.revision = source.revision ∧ indexAt before.checked address = none ∧
    ∃ row premises conclusion,
      source.read address = some row ∧ row.id = address ∧
      RuleApplication definition row.ruleInstance premises conclusion ∧
      premiseValues before row.children = some premises ∧
      after = ⟨before.revision, (address, before.cache.size) :: before.checked,
        before.cache.push conclusion⟩

/-- Exact local source/worker correspondence includes failure: an accepted
step is exactly one original rule application on its actual ordered parents. -/
theorem step_exact (definition : ValidatedCalculusLanguageDef) (source : Source)
    (before after : State Pattern) (address : Nat) :
    step (presentation definition).ruleWitness (store definition source)
      before address = some after ↔ LicensedStep definition source before address after := by
  unfold LicensedStep
  simp only [← instantiateRule?_eq_some_iff_application]
  by_cases revision : before.revision = source.revision
  · cases fresh : indexAt before.checked address with
    | some index => simp [step, store, revision, fresh]
    | none =>
        cases read : source.read address with
        | none => simp [step, store, readRow, revision, fresh, read]
        | some row =>
            by_cases identity : row.id = address
            · cases admitted : instantiateRule? definition row.ruleInstance with
              | none =>
                  have decoded := admitInstance?_none admitted
                  simp [step, store, readRow, decoded, revision, fresh, read, identity, admitted]
              | some result =>
                  obtain ⟨premises, conclusion⟩ := result
                  cases values : premiseValues before row.children with
                  | none =>
                      have decoded := admitInstance?_some admitted
                      simp [step, store, readRow, decoded, revision, fresh, read, identity,
                        admitted, values]
                  | some actual =>
                      have decoded := admitInstance?_some admitted
                      by_cases same : actual = premises
                      · subst actual
                        simp [step, store, readRow, decoded, revision, fresh, read, identity,
                          admitted, values, Presentation.ruleWitness]
                        exact eq_comm
                      · simp [step, store, readRow, decoded, revision, fresh, read, identity,
                          admitted, values, Presentation.ruleWitness, same]
            · simp [step, store, readRow, revision, fresh, read, identity]
  · simp [step, store, revision]

/-- A finite supplied schedule is licensed by its actual source rows, without
appealing to the executable rule-witness checker. -/
inductive LicensedRun (definition : ValidatedCalculusLanguageDef) (source : Source) :
    State Pattern → List Nat → State Pattern → Prop where
  | nil (state : State Pattern) : LicensedRun definition source state [] state
  | cons {before middle after : State Pattern} {address : Nat} {rest : List Nat} :
      LicensedStep definition source before address middle →
      LicensedRun definition source middle rest after →
      LicensedRun definition source before (address :: rest) after

/-- Whole-run acceptance is exact for the supplied authored evidence, including
its particular source addresses and each performed original rule application. -/
theorem run_exact (definition : ValidatedCalculusLanguageDef) (source : Source)
    (before after : State Pattern) (schedule : List Nat) :
    Mettapedia.Logic.DerivationGraph.BorrowedCursor.run
      (presentation definition).ruleWitness (store definition source) before schedule = some after ↔
        LicensedRun definition source before schedule after := by
  induction schedule generalizing before with
  | nil =>
      constructor
      · intro accepted
        cases Option.some.inj accepted
        exact .nil _
      · intro licensed
        cases licensed
        rfl
  | cons address rest ih =>
      constructor
      · intro accepted
        obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp accepted
        exact .cons ((step_exact definition source before middle address).mp first)
          ((ih middle).mp later)
      · intro licensed
        cases licensed with
        | cons first later =>
            exact Option.bind_eq_some_iff.mpr
              ⟨_, (step_exact definition source _ _ address).mpr first, (ih _).mpr later⟩

abbrev Cursor (definition : ValidatedCalculusLanguageDef) (source : Source) :=
  Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor
    (presentation definition).ruleWitness (store definition source)

def begin (definition : ValidatedCalculusLanguageDef) (source : Source) : Cursor definition source :=
  Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor.begin
    (presentation definition).ruleWitness (store definition source)

/-- A projected root is inspected without freshening its schematic variables.
The exact calculus theory is part of the checked value's type. -/
theorem checked_root_source_derivation (definition : ValidatedCalculusLanguageDef)
    (source : Source) (cursor : Cursor definition source) (address : Nat)
    (goal : Pattern) (found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt
      cursor.state address = some goal) : Nonempty (Derivation definition goal) := by
  apply (source_derivation_iff_rules definition goal).mpr
  obtain ⟨schedule, accepted⟩ := cursor.checkedPrefix
  exact Mettapedia.Logic.DerivationGraph.BorrowedCursor.root_derivable
    (presentation definition).ruleWitness (store definition source) schedule cursor.state
    accepted address goal found

/-- A protected cursor root has evidence accepted by the original source
checker. This is an export-existence theorem, not runtime tree expansion. -/
theorem checked_root_has_source_certificate (definition : ValidatedCalculusLanguageDef)
    (source : Source) (cursor : Cursor definition source) (address : Nat)
    (goal : Pattern) (found : rootAt cursor.state address = some goal) :
    ∃ proof : RawProof, checkRaw definition goal proof = true := by
  obtain ⟨tree⟩ := checked_root_source_derivation definition source cursor address goal found
  exact ⟨tree.erase, checkRaw_erase tree⟩

/-- Authored source recovery and graph derivability use exactly one definition.
This does not claim that a textual module parser has been verified. -/
theorem authored_source_and_graph (object : Object) (goal : Pattern) :
    InferenceExtension.elaborate object.authoredSource = some object.definition.1.toCalculus ∧
      (Nonempty (Derivation object.definition goal) ↔
        ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Pattern
          (AdmittedInstance object.definition) Nat)) (cache : Array Pattern) (root : Nat),
          Mettapedia.Logic.DerivationGraph.replay (presentation object.definition).ruleWitness
            nodes = some cache ∧ cache[root]? = some goal) := by
  refine ⟨object.authoredSource_elaborates, ?_⟩
  rw [source_derivation_iff_presentation]
  exact PresentationGraph.nonempty_derivation_iff_graph (P := presentation object.definition) (0 : Nat) goal

/-- The actual source-address checker is an object of the existing machine
category. One advance admits one original rule instance and its cited premises;
it does not run proof search or expand a proof tree. -/
def checkingObject (definition : ValidatedCalculusLanguageDef) (source : Source) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.ObservedMachine.of
    (Mettapedia.Machines.Cursor.ProofChecking.machine
      (presentation definition).ruleWitness (store definition source))

/-- A completed successful check is exactly a licensed run of the original
authored rows. A valid root in a prefix cannot hide a bad unused suffix. -/
theorem finished_iff_licensed (definition : ValidatedCalculusLanguageDef) (source : Source)
    (initial : Cursor definition source) (schedule : List Nat) :
    (∃ fuel events report, (checkingObject definition source).machine.run fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start initial schedule) =
        (events, .finished report) ∧ report.accepted = true) ↔
      ∃ after, LicensedRun definition source initial.state schedule after := by
  exact (Mettapedia.Machines.Cursor.ProofChecking.finished_true_iff
    (presentation definition).ruleWitness (store definition source) initial schedule).trans
      (exists_congr (fun after => run_exact definition source initial.state after schedule))

/-- Retaining a checked prefix does not change the actual residual or events
when the checking budget is split. Counts refer to worker advances, not the
physical cost of schema instantiation or syntax comparison. -/
theorem checking_run_add (definition : ValidatedCalculusLanguageDef) (source : Source)
    (first extra : Nat)
    (work : Mettapedia.Machines.Cursor.ProofChecking.Work
      (presentation definition).ruleWitness (store definition source)) :
    (checkingObject definition source).machine.run (first + extra) work =
      (checkingObject definition source).machine.continueRun extra
        ((checkingObject definition source).machine.run first work) :=
  (checkingObject definition source).machine.run_add first extra work

namespace Controls

private def a : Pattern := .apply "BorrowedA" []
private def b : Pattern := .apply "BorrowedB" []

private def axiomA : RuleSchema :=
  { id := ⟨"borrowed-axiom"⟩, metavariables := [], premises := [], conclusion := a }

private def twice : RuleSchema :=
  { id := ⟨"borrowed-twice"⟩, metavariables := [], premises := [a, a], conclusion := b }

private def definitionData (includeAxiom : Bool) : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "borrowed-calculus"
    judgments := [{ head := "BorrowedA", arity := 0 }, { head := "BorrowedB", arity := 0 }]
    rules := if includeAxiom then [axiomA, twice] else [twice] }

private def definition (includeAxiom : Bool) : ValidatedCalculusLanguageDef :=
  ⟨definitionData includeAxiom, by cases includeAxiom <;> decide +kernel⟩

private def axiomRow : DAGNode := ⟨0, ⟨⟨"borrowed-axiom"⟩, []⟩, []⟩
private def twiceRow : DAGNode := ⟨1, ⟨⟨"borrowed-twice"⟩, []⟩, [0, 0]⟩

private def source : Source :=
  ⟨7, fun address => match address with
    | 0 => some axiomRow
    | 1 => some twiceRow
    | _ => none⟩

private def checkedRoot (definition : ValidatedCalculusLanguageDef) (source : Source)
    (schedule : List Nat) (address : Nat) : Option Pattern := do
  let checked ← (begin definition source).advance schedule
  (checked.root address).map Mettapedia.Logic.DerivationGraph.CheckedJudgment.judgment

theorem duplicate_premises_accept :
    checkedRoot (definition true) source [0, 1] 1 = some b := by decide +kernel

theorem forward_premises_refused :
    checkedRoot (definition true) source [1, 0] 1 = none := by decide +kernel

theorem absent_root_refused :
    checkedRoot (definition true) source [0, 1] 2 = none := by decide +kernel

theorem changed_theory_same_label_refused :
    checkedRoot (definition false) source [0, 1] 1 = none := by decide +kernel

theorem forged_source_identity_refused :
    checkedRoot (definition true)
      ⟨7, fun _ => some { axiomRow with id := 1 }⟩ [0] 0 = none := by decide +kernel

theorem source_and_reference_agree :
    checkedRoot (definition true) source [0, 1] 1 = some b ∧
      checkDAGBlocks (definition true) b 1 [[axiomRow], [twiceRow]] = true := by decide +kernel

private def completedCheck (definition : ValidatedCalculusLanguageDef) (schedule : List Nat) :
    Option Bool :=
  Mettapedia.Machines.Cursor.ProofChecking.completedVerdict
    ((checkingObject definition source).machine.run (schedule.length + 2)
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin definition source) schedule)).2

theorem retained_duplicate_premises_accept :
    completedCheck (definition true) [0, 1] = some true := by decide +kernel

theorem retained_missing_axiom_refuses :
    completedCheck (definition false) [0, 1] = some false := by decide +kernel

theorem retained_bad_unused_suffix_refuses :
    completedCheck (definition true) [0, 1, 2] = some false := by decide +kernel

end Controls

#print axioms rules_iff_application
#print axioms source_derivation_iff_rules
#print axioms source_derivation_iff_presentation
#print axioms step_exact
#print axioms run_exact
#print axioms checked_root_source_derivation
#print axioms checked_root_has_source_certificate
#print axioms authored_source_and_graph

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.BorrowedCursor
