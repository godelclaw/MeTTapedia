import Mettapedia.Languages.HOLLight.ProofExecution
import Lean.Data.Json

/-!
# Receiving exported HOL proof graphs

Source addresses are translated to the existing registered proof cache.
Every claimed sequent is compared with the actual output of the registered
command. A type definition is one command with two separately addressable
outputs. Printed theorem names do not authorize any inference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportReplay

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open ProofExecution DefinitionAdapters SignatureFormation

structure Event where
  sourceIds : List Nat
  sourceParents : List Nat
  command : Registered.Command
  claims : List Sequent

structure State where
  registered : Registered.State
  addresses : Std.TreeMap Nat Nat := {}
  receipts : Array Event := #[]

def empty (context : TheoryContext) : State := ⟨Registered.empty context, {}, #[]⟩

/-- Each exported result retains its own ordered parent occurrences. The
two results of a type definition cite the same existence proof separately. -/
def Event.sourceEdges (event : Event) : List (Nat × List Nat) :=
  event.sourceIds.map (fun id => (id, event.sourceParents))

def Event.premiseOccurrences (event : Event) : Nat :=
  event.sourceIds.length * event.sourceParents.length

theorem Event.sourceEdges_length (event : Event) :
    event.sourceEdges.length = event.sourceIds.length := by simp [sourceEdges]

theorem Event.sourceEdges_occurrences (event : Event) :
    (event.sourceEdges.map (fun edge => edge.2.length)).sum = event.premiseOccurrences := by
  simp only [sourceEdges, List.map_map, premiseOccurrences]
  induction event.sourceIds with
  | nil => simp
  | cons id ids ih => simp_all [Nat.add_mul, Nat.add_comm]

def resolveParents (state : State) (parents : List Nat) : Option (List Nat) :=
  parents.mapM state.addresses.get?

def claimsSame (claims : List Sequent) (outputs : List Theorem) : Bool :=
  match claims, outputs with
  | [], [] => true
  | claim :: claims, output :: outputs =>
      decide (claim = output.sequent) && claimsSame claims outputs
  | _, _ => false

theorem claimsSame_eq_true_iff (claims : List Sequent) (outputs : List Theorem) :
    claimsSame claims outputs = true ↔ claims = outputs.map Theorem.sequent := by
  induction claims generalizing outputs with
  | nil => cases outputs <;> simp [claimsSame]
  | cons claim claims ih => cases outputs <;> simp [claimsSame, ih]

def idsFreshB (state : State) (ids : List Nat) : Bool :=
  decide ids.Nodup && ids.all (fun id => (state.addresses[id]?).isNone)

def addAddresses (addresses : Std.TreeMap Nat Nat) (start : Nat) :
    List Nat → Std.TreeMap Nat Nat
  | [] => addresses
  | id :: ids => addAddresses (addresses.insert id start) (start + 1) ids

def apply (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (event : Event) : Option State := do
  let parents ← resolveParents before event.sourceParents
  if parents ≠ event.command.parents ∨ idsFreshB before event.sourceIds ≠ true then none
  else do
    let output ← event.command.check policy before.registered.context before.registered.cache
    if event.sourceIds.length ≠ output.theorems.length ∨
        claimsSame event.claims output.theorems ≠ true then none
    else
      let after : Registered.State :=
        ⟨output.context, before.registered.cache ++ output.theorems.toArray,
          before.registered.receipts.push ⟨event.command, output.theorems⟩⟩
      pure ⟨after, addAddresses before.addresses before.registered.cache.size event.sourceIds,
        before.receipts.push event⟩

/-- Receiving an event really performs the same registered command and
checks both the graph edges and every displayed output sequent. -/
theorem apply_checked (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {event : Event}
    (accepted : apply policy before event = some after) :
    Registered.apply policy before.registered event.command = some after.registered ∧
      resolveParents before event.sourceParents = some event.command.parents ∧
      idsFreshB before event.sourceIds = true ∧
      after.receipts = before.receipts.push event ∧
      ∃ output, event.command.check policy before.registered.context before.registered.cache =
        some output ∧ event.sourceIds.length = output.theorems.length ∧
        event.claims = output.theorems.map Theorem.sequent := by
  unfold apply at accepted
  cases parentsFound : resolveParents before event.sourceParents with
  | none => simp [parentsFound] at accepted
  | some parents =>
    simp only [parentsFound, bind, Option.bind] at accepted
    split at accepted
    · contradiction
    · rename_i guards
      have hg : parents = event.command.parents ∧ idsFreshB before event.sourceIds = true :=
        by simpa only [not_or, not_not] using guards
      cases checked : event.command.check policy before.registered.context before.registered.cache with
      | none => simp [checked] at accepted
      | some output =>
        simp only [checked] at accepted
        split at accepted
        · contradiction
        · rename_i outputGuards
          have ho : event.sourceIds.length = output.theorems.length ∧
              claimsSame event.claims output.theorems = true :=
            by simpa only [not_or, not_not] using outputGuards
          have equal := Option.some.inj accepted
          subst after
          refine ⟨?_, congrArg some hg.1, hg.2, rfl, output, rfl, ho.1,
            (claimsSame_eq_true_iff _ _).mp ho.2⟩
          simp [Registered.apply, checked]

def Valid (policy : AxiomPolicy) (state : State) : Prop :=
  Registered.Valid policy state.registered

theorem empty_valid (policy : AxiomPolicy) (context : TheoryContext) :
    Valid policy (empty context) := Registered.empty_valid policy context

theorem apply_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {event : Event} (valid : Valid policy before)
    (accepted : apply policy before event = some after) : Valid policy after :=
  Registered.apply_preserves_derivations policy valid (apply_checked policy accepted).1

def replayFrom (policy : AxiomPolicy) [DecidablePred policy] :
    State → List Event → Option State
  | before, [] => some before
  | before, event :: events => do
    let after ← apply policy before event
    replayFrom policy after events

/-- Every accepted finite export has an actual execution in the registered
source calculus, including definition admissions, rather than a name lookup. -/
theorem replayFrom_reachable (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (events : List Event) (after : State)
    (accepted : replayFrom policy before events = some after) :
    (Registered.gslt policy).MultiStep before.registered after.registered := by
  induction events generalizing before with
  | nil =>
    have equal := Option.some.inj accepted
    subst after
    exact .refl _
  | cons event events ih =>
    cases first : apply policy before event with
    | none => simp [replayFrom, first] at accepted
    | some middle =>
      have rest : replayFrom policy middle events = some after := by
        simpa [replayFrom, first] using accepted
      exact .step ⟨event.command, (apply_checked policy first).1⟩ (ih middle rest)

theorem replayFrom_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (events : List Event) (after : State) (valid : Valid policy before)
    (accepted : replayFrom policy before events = some after) : Valid policy after := by
  induction events generalizing before with
  | nil => exact (Option.some.inj accepted) ▸ valid
  | cons event events ih =>
    cases first : apply policy before event with
    | none => simp [replayFrom, first] at accepted
    | some middle =>
      apply ih middle (apply_preserves_derivations policy valid first)
      simpa [replayFrom, first] using accepted

/-- A root retains the theorem actually present at its received cache
address; the export contributes no replacement axiom-dependency annotation. -/
def root? (state : State) (id : Nat) (claim : Sequent) : Option Theorem :=
  match state.addresses[id]? with
  | none => none
  | some index =>
    match state.registered.cache[index]? with
    | none => none
    | some actual => if actual.sequent = claim then some actual else none

theorem root_derivation (policy : AxiomPolicy) {state : State}
    (valid : Valid policy state) {id : Nat} {claim : Sequent} {out : Theorem}
    (found : root? state id claim = some out) :
    TheoryDerives policy state.registered.context out ∧ out.sequent = claim := by
  cases address : state.addresses[id]? with
  | none => simp [root?, address] at found
  | some index =>
    cases cached : state.registered.cache[index]? with
    | none => simp [root?, address, cached] at found
    | some actual =>
      simp only [root?, address, cached] at found
      split at found
      · rename_i same
        have equal := Option.some.inj found
        subst out
        exact ⟨valid actual (Array.mem_of_getElem? cached), same⟩
      · contradiction

/-! The certificate finder proposes schema substitutions. The registered
checker verifies the proposal independently, including repeated parameters. -/

mutual
  def assignments : Ty → Ty → Option (List (Name × Ty))
    | .var name, target => some [(name, target)]
    | .op operator arguments, .op targetOperator targets =>
      if TypeOp.same operator targetOperator then assignmentsList arguments targets else none
    | _, _ => none
  termination_by schema _ => sizeOf schema

  def assignmentsList : List Ty → List Ty → Option (List (Name × Ty))
    | [], [] => some []
    | schema :: schemas, target :: targets => do
      let head ← assignments schema target
      let tail ← assignmentsList schemas targets
      pure (head ++ tail)
    | _, _ => none
  termination_by schemas _ => sizeOf schemas
end

def instanceCertificates (signature : Signature) : InstanceWitnesses := fun constant annotation =>
  match signature.constants constant with
  | none => TypeSubst.empty
  | some schema => TypeSubst.ofList ((assignments schema annotation).getD [])

def checkedSource? (source : SourceTerm) : Option CheckedSourceTerm :=
  match checked : source.inferType with
  | none => none
  | some type => some ⟨source, type, checked⟩

theorem checkedSource?_retains {source : SourceTerm} {out : CheckedSourceTerm}
    (accepted : checkedSource? source = some out) : out.source = source := by
  unfold checkedSource? at accepted
  split at accepted
  · contradiction
  · cases Option.some.inj accepted
    rfl

theorem replayFrom_registered (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (events : List Event) (after : State)
    (accepted : replayFrom policy before events = some after) :
    Registered.replayFrom policy before.registered (events.map Event.command) = some after.registered := by
  induction events generalizing before with
  | nil =>
    have same := Option.some.inj accepted
    cases same
    rfl
  | cons head tail ih =>
    cases applied : apply policy before head with
    | none => simp [replayFrom,applied] at accepted
    | some middle =>
      have rest : replayFrom policy middle tail = some after := by simpa [replayFrom,applied] using accepted
      simpa only [List.map,Registered.replayFrom,(apply_checked policy applied).1,bind,Option.bind] using ih middle rest

theorem root_mem_cache {state : State} {id : Nat} {claim : Sequent} {out : Theorem}
    (found : root? state id claim = some out) : out ∈ state.registered.cache := by
  cases address : state.addresses[id]? with
  | none => simp [root?,address] at found
  | some index =>
    cases cached : state.registered.cache[index]? with
    | none => simp [root?,address,cached] at found
    | some actual =>
      simp only [root?,address,cached] at found
      split at found
      · cases Option.some.inj found
        exact Array.mem_of_getElem? cached
      · contradiction


end Mettapedia.Languages.HOLLight.ExportReplay
