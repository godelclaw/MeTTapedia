import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremCommandExecution
import Mettapedia.Languages.MM0.MeTTa.Session.Sharing

/-!
# Original MMB recorded-witness genealogy

The original recorder moves each initializer into the saved list and places
its fresh hypothesis reference on the stack. These laws retain the complete
original targets, chronological indices and ordered proof-pop fields. A
recorded claim remains distinct from a logically checked conclusion.

The unchanged shared-proof source is realized under the loaded binary
program. Its actual acceptance checks every initializer in its preceding
prefix, including unused rows, before supplying original kernel derivations
for generated references. Constructor/slot provenance, theorem dispatch and
conversion continuations remain separate qualifications.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBRecordedWitnessAuthority

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)
open Kernel (Preterm ProofWitness Context)
open Presentation.ComputationalTyping (signatureOf)

abbrev program := MMBTheoremCommandExecution.program

/-- The physical source recorder retains newest-first initializers; its
original shared-proof service receives their chronological reversal. -/
def savedValue (recorded : List Sharing.Entry) : List Atom :=
  recorded.reverse.map Sharing.entryValue

/-- These are declared claims, not checked conclusions. The original service
must check every initializer before they become logical premises. -/
def claimedScope (hypotheses : List Preterm) (recorded : List Sharing.Entry) : List (Option Preterm) :=
  hypotheses.map some ++ recorded.map Sharing.Entry.expected

/-- A proved entry refers to an original hypothesis or an already recorded
claim. Its complete target fields remain distinct from witness validity. -/
def ReferenceClaim (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (witness target : Atom) : Prop :=
  ∃ index allocation claim node,
    witness = Proof.witnessValue (.hyp index) ∧
    target = expressionValue allocation (Data.preterm claim) node ∧
    (claimedScope hypotheses recorded)[index]? = some (some claim)

/-- Only actual proved fields are constrained; expression and pending
conversion entries do not acquire proof evidence through this predicate. -/
def ProvedReferences (hypotheses : List Preterm) (recorded : List Sharing.Entry) (entries : List Atom) : Prop :=
  ∀ witness target, provedValue witness target ∈ entries → ReferenceClaim hypotheses recorded witness target

@[simp] theorem savedValue_append (recorded : List Sharing.Entry) (entry : Sharing.Entry) :
    savedValue (recorded ++ [entry]) = Sharing.entryValue entry :: savedValue recorded := by
  simp [savedValue]

@[simp] theorem claimedScope_length (hypotheses : List Preterm) (recorded : List Sharing.Entry) :
    (claimedScope hypotheses recorded).length = hypotheses.length + recorded.length := by
  simp [claimedScope]

@[simp] theorem claimedScope_append (hypotheses : List Preterm) (recorded added : List Sharing.Entry) :
    claimedScope hypotheses (recorded ++ added) = claimedScope hypotheses recorded ++ added.map Sharing.Entry.expected := by
  simp [claimedScope, List.append_assoc]

theorem ReferenceClaim.append {hypotheses : List Preterm} {recorded added : List Sharing.Entry} {witness target : Atom}
    (given : ReferenceClaim hypotheses recorded witness target) :
    ReferenceClaim hypotheses (recorded ++ added) witness target := by
  obtain ⟨index, allocation, claim, node, witnessShape, targetShape, found⟩ := given
  refine ⟨index, allocation, claim, node, witnessShape, targetShape, ?_⟩
  rw [claimedScope_append, List.getElem?_append_left]
  · exact found
  · exact (getElem?_eq_some_iff.mp found).choose

theorem ReferenceClaim.hypothesis (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (index allocation : Nat) (claim : Preterm) (node : Atom)
    (found : hypotheses[index]? = some claim) :
    ReferenceClaim hypotheses recorded (Proof.witnessValue (.hyp index))
      (expressionValue allocation (Data.preterm claim) node) := by
  refine ⟨index, allocation, claim, node, rfl, rfl, ?_⟩
  rw [claimedScope, List.getElem?_append_left]
  · simp [found]
  · simpa only [List.length_map] using (getElem?_eq_some_iff.mp found).choose

theorem ReferenceClaim.record (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (allocation : Nat) (claim : Preterm) (node : Atom) (initializer : ProofWitness) :
    ReferenceClaim hypotheses (recorded ++ [⟨some claim, initializer⟩])
      (Proof.witnessValue (.hyp (hypotheses.length + recorded.length)))
      (expressionValue allocation (Data.preterm claim) node) := by
  refine ⟨hypotheses.length + recorded.length, allocation, claim, node, rfl, rfl, ?_⟩
  rw [claimedScope_append, List.getElem?_append_right]
  · simp
  · simp

theorem ProvedReferences.nil (hypotheses : List Preterm) (recorded : List Sharing.Entry) :
    ProvedReferences hypotheses recorded [] := by
  intro witness target member
  cases member

theorem ProvedReferences.append {hypotheses : List Preterm} {recorded added : List Sharing.Entry} {entries : List Atom}
    (given : ProvedReferences hypotheses recorded entries) : ProvedReferences hypotheses (recorded ++ added) entries := by
  intro witness target member
  exact (given witness target member).append

theorem ProvedReferences.prepend {hypotheses : List Preterm} {recorded : List Sharing.Entry} {entries : List Atom}
    {witness target : Atom} (given : ProvedReferences hypotheses recorded entries)
    (fresh : ReferenceClaim hypotheses recorded witness target) :
    ProvedReferences hypotheses recorded (provedValue witness target :: entries) := by
  intro input targetValue member
  rcases List.mem_cons.mp member with same | old
  · have fields : input = witness ∧ targetValue = target := by
      simpa [provedValue] using same
    simpa only [fields.1, fields.2] using fresh
  · exact given input targetValue old

/-- Actual successful proof pops retain every original child and supply its
preceding reference and complete original target, in source order. -/
theorem Pops.reference_fields {hypotheses : List Preterm} {recorded : List Sharing.Entry}
    {count : Nat} {stack children remaining : List Atom}
    (popped : MMBTheoremCommandExecution.Pops .proofs count stack (some (children, remaining)))
    (authorized : ProvedReferences hypotheses recorded stack) :
    ∃ fields : List (Atom × Atom), children = MMBTheoremCommandExecution.provedEntries fields ∧
      ∀ pair ∈ fields, ReferenceClaim hypotheses recorded pair.1 pair.2 := by
  obtain ⟨fields, represented⟩ := popped.proof_fields
  refine ⟨fields, represented, ?_⟩
  intro pair member
  apply authorized pair.1 pair.2
  obtain ⟨_, ordered⟩ := popped.ordered
  rw [ordered]
  apply List.mem_append_left
  apply List.mem_reverse.mpr
  rw [represented]
  exact List.mem_map.mpr ⟨pair, member, rfl⟩

private theorem canonical_reference_fields (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (fields : List (Atom × Atom)) (authorized : ∀ pair ∈ fields, ReferenceClaim hypotheses recorded pair.1 pair.2) :
    ∃ indices claims,
      fields.map Prod.fst = (indices.map ProofWitness.hyp).map Proof.witnessValue ∧
      MMBProofRunExecution.ExpressionClaims (fields.map Prod.snd) (claims.map Data.preterm) ∧
      List.Forall₂ (fun index claim => (claimedScope hypotheses recorded)[index]? = some (some claim)) indices claims := by
  induction fields with
  | nil => exact ⟨[], [], rfl, .nil, .nil⟩
  | cons pair tail ih =>
      obtain ⟨index, allocation, claim, node, witnessShape, targetShape, found⟩ :=
        authorized pair (by simp)
      obtain ⟨indices, claims, witnessShapes, targetShapes, lookups⟩ :=
        ih (fun item member => authorized item (by simp [member]))
      refine ⟨index :: indices, claim :: claims, ?_, ?_, .cons found lookups⟩
      · simp only [List.map_cons, witnessShape, witnessShapes]
      · simpa only [List.map_cons, targetShape] using MMBProofRunExecution.ExpressionClaims.cons
          allocation (Data.preterm claim) node targetShapes

/-- The theorem preparer earns canonical witnesses and preterm projections
from the real popped entries. It executes all three unchanged source
operations and retains the original ordered target objects. -/
theorem prepared_reference_proofs_returns (bindings : Subst) (state : State)
    (hypotheses : List Preterm) (recorded : List Sharing.Entry) (count : Nat)
    (stack children remaining : List Atom) (kindName countName stackName childrenName : String)
    (kindCaptured : applySubst bindings (.var kindName) = MMBTheoremCommandExecution.StackKind.proofs.value)
    (countCaptured : applySubst bindings (.var countName) = Store.natural count)
    (stackCaptured : applySubst bindings (.var stackName) = listValue stack)
    (childrenCaptured : applySubst bindings (.var childrenName) = listValue children)
    (popped : MMBTheoremCommandExecution.Pops .proofs count stack (some (children, remaining)))
    (authorized : ProvedReferences hypotheses recorded stack) :
    ∃ fields indices claims,
      children = MMBTheoremCommandExecution.provedEntries fields ∧
      fields.map Prod.fst = (indices.map ProofWitness.hyp).map Proof.witnessValue ∧
      MMBProofRunExecution.ExpressionClaims (fields.map Prod.snd) (claims.map Data.preterm) ∧
      List.Forall₂ (fun index claim => (claimedScope hypotheses recorded)[index]? = some (some claim)) indices claims ∧
      PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:pop-many", .var kindName, .var countName, .var stackName]) state
        (MMBTheoremCommandExecution.poppedValue (some (children, remaining))) ∧
      PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-values", .var childrenName]) state
        (optionValue (some (listValue ((indices.map ProofWitness.hyp).map Proof.witnessValue)))) ∧
      PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-conclusions", .var childrenName]) state
        (optionValue (some (listValue (fields.map Prod.snd)))) := by
  obtain ⟨fields, represented, references⟩ := Pops.reference_fields popped authorized
  obtain ⟨indices, claims, witnesses, targets, lookups⟩ := canonical_reference_fields hypotheses recorded fields references
  have captured : applySubst bindings (.var childrenName) =
      listValue (MMBTheoremCommandExecution.provedEntries fields) := by
    simpa only [represented] using childrenCaptured
  refine ⟨fields, indices, claims, represented, witnesses, targets, lookups,
    MMBTheoremCommandExecution.pop_many_returns bindings state .proofs count stack (some (children, remaining))
      kindName countName stackName kindCaptured countCaptured stackCaptured popped, ?_, ?_⟩
  · simpa only [witnesses] using MMBTheoremCommandExecution.proof_values_returns bindings state fields
      (.var childrenName) captured
  · exact MMBTheoremCommandExecution.proof_conclusions_returns bindings state fields (.var childrenName) captured

/-- Self and future references have no claimed preceding position. The
original recorder's fresh root is authorized only by its append step. -/
theorem future_reference_refused (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (index : Nat) (outside : hypotheses.length + recorded.length ≤ index) (target : Atom) :
    ¬ ReferenceClaim hypotheses recorded (Proof.witnessValue (.hyp index)) target := by
  rintro ⟨foundIndex, allocation, claim, node, witnessShape, _, found⟩
  have same : index = foundIndex := by
    apply Data.natural_injective
    simpa [Proof.witnessValue, Hypothesis.witness, listValue] using witnessShape
  subst foundIndex
  have absent : (claimedScope hypotheses recorded)[index]? = none :=
    List.getElem?_eq_none (by simpa using outside)
  rw [absent] at found
  cases found

/-- Changing a referenced claim while retaining its physical index does not
satisfy the original recorder genealogy. -/
theorem changed_claim_refused (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (index allocation : Nat) (claim changed : Preterm) (node : Atom)
    (found : (claimedScope hypotheses recorded)[index]? = some (some claim)) (different : claim ≠ changed) :
    ¬ ReferenceClaim hypotheses recorded (Proof.witnessValue (.hyp index))
      (expressionValue allocation (Data.preterm changed) node) := by
  rintro ⟨foundIndex, foundAllocation, foundClaim, foundNode, witnessShape, targetShape, matching⟩
  have sameIndex : index = foundIndex := by
    apply Data.natural_injective
    simpa [Proof.witnessValue, Hypothesis.witness, listValue] using witnessShape
  subst foundIndex
  have sameClaim : claim = foundClaim := Option.some.inj (Option.some.inj (found.symm.trans matching))
  have sameTarget : changed = foundClaim := by
    apply Data.preterm_injective
    simp only [expressionValue, Atom.expression.injEq, List.cons.injEq, and_true, true_and] at targetShape
    exact targetShape.2.1
  exact different (sameClaim.trans sameTarget.symm)

/-- Saving uses the exact old count and physical saved length; its generated
reference becomes available only after the initializer has been appended. -/
theorem save_proof_recorded_returns (bindings : Subst) (state : State)
    (next arity allocation : Nat) (hypotheses : List Preterm) (recorded : List Sharing.Entry)
    (stack heap dummies originalHypotheses : List Atom) (claim : Preterm) (node : Atom) (initializer : ProofWitness)
    (stateName targetName witnessName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      stateValue next arity hypotheses.length stack heap dummies originalHypotheses (savedValue recorded))
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue allocation (Data.preterm claim) node)
    (witnessCaptured : applySubst bindings (.var witnessName) = Proof.witnessValue initializer) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:save-proof", .var stateName, .var targetName, .var witnessName]) state
      (optionValue (some (stateValue next arity hypotheses.length
        (provedValue (Proof.witnessValue (.hyp (hypotheses.length + recorded.length)))
          (expressionValue allocation (Data.preterm claim) node) :: stack)
        heap dummies originalHypotheses (savedValue (recorded ++ [⟨some claim, initializer⟩]))))) := by
  have returned := MMBTheoremCommandExecution.save_proof_returns bindings state next arity hypotheses.length allocation
    stack heap dummies originalHypotheses (savedValue recorded) (Data.preterm claim) node (Proof.witnessValue initializer)
    stateName targetName witnessName stateCaptured targetCaptured witnessCaptured
  simpa [MMBTheoremCommandExecution.saveProofResult, savedValue, Sharing.entryValue,
    Proof.witnessValue, ProofResults.resultValue, optionValue] using returned

/-- Original recording retains all earlier proof references and creates its
new reference with the precise newly recorded expectation. This does not
claim that the initializer passed the logical checker. -/
theorem record_preserves_references {hypotheses : List Preterm} {recorded : List Sharing.Entry}
    {stack : List Atom} (old : ProvedReferences hypotheses recorded stack)
    (allocation : Nat) (claim : Preterm) (node : Atom) (initializer : ProofWitness) :
    ProvedReferences hypotheses (recorded ++ [⟨some claim, initializer⟩])
      (provedValue (Proof.witnessValue (.hyp (hypotheses.length + recorded.length)))
        (expressionValue allocation (Data.preterm claim) node) :: stack) :=
  old.append.prepend (ReferenceClaim.record hypotheses recorded allocation claim node initializer)

private theorem expected_claims_subset {recorded : List Sharing.Entry} {checked : List (Preterm × ProofWitness)}
    (matching : List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
      (entry.expected = none ∨ entry.expected = some pair.1)) recorded checked) :
    ∀ claim, some claim ∈ recorded.map Sharing.Entry.expected → claim ∈ checked.map Prod.fst := by
  induction matching with
  | nil => intro claim member; cases member
  | @cons entry pair entries pairs related matching ih =>
      intro claim member
      rcases List.mem_cons.mp member with same | later
      · rcases related.2 with absent | expected
        · rw [absent] at same; cases same
        · have claimSame : claim = pair.1 := Option.some.inj (same.trans expected)
          simp [claimSame]
      · exact List.mem_cons_of_mem _ (ih claim later)

/-- Acceptance of the original chronological service earns logical authority
for each declared claim at a referenced position. Each saved initializer,
including every unused row, remains checked in its preceding prefix. -/
theorem claimedScope_derives {tables : Proof.Tables} {context : Context} {recorded : List Sharing.Entry}
    {root : ProofWitness} {goal : Preterm} (accepted : Sharing.Checked context root goal tables recorded)
    (index : Nat) (claim : Preterm) (found : (claimedScope tables.values recorded)[index]? = some (some claim)) :
    Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values claim := by
  obtain ⟨checked, initializers, _, matching⟩ := accepted.retains_witnesses
  have member := List.mem_of_getElem? found
  rw [claimedScope] at member
  rcases List.mem_append.mp member with hypothesis | saved
  · obtain ⟨original, member, same⟩ := List.mem_map.mp hypothesis
    cases Option.some.inj same
    exact .hypothesis member
  · exact initializers.sound claim (expected_claims_subset matching claim saved)

/-- The same chronological service is executed under the loaded binary
program, retaining its real declaration/cache/store admission and frame. -/
theorem recorded_check_returns (tables : Proof.Tables) (context : Context)
    (recorded : List Sharing.Entry) (root : ProofWitness) (goal : Preterm) (before : State)
    (input : Sharing.Input tables before) :
    ∃ after values answer,
      (∀ bindings tn dn thn cn hn sn rn qn,
        applySubst bindings (.var tn) = TableAccess.tableValue tables.terms →
        applySubst bindings (.var dn) = TableAccess.tableValue tables.definitions →
        applySubst bindings (.var thn) = TableAccess.tableValue tables.theorems →
        applySubst bindings (.var cn) = Data.context context →
        applySubst bindings (.var hn) = ListSubstitution.expressionsValue tables.values →
        applySubst bindings (.var sn) = listValue (recorded.map Sharing.entryValue) →
        applySubst bindings (.var rn) = Proof.witnessValue root →
        applySubst bindings (.var qn) = Data.preterm goal →
        PureReturns program bindings before (.expression [.symbol "mm0:shared-proof", .var tn,
          .var dn, .var thn, .var cn, .var hn, .var sn, .var rn, .var qn]) after (boolean answer)) ∧
      Proof.Ready { tables with values := values } after ∧
      (Sharing.Checked context root goal tables recorded ↔ answer = true) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨stored, allocated, shaped⟩ := input.allocated
  obtain ⟨after, values, answer, called, ready, justified, others, cells⟩ :=
    Sharing.returns tables context recorded root goal before stored input.terms input.definitions input.theorems
      input.cache input.current allocated shaped input.independent
  refine ⟨after, values, answer, ?_, ready, justified, others, cells⟩
  intro bindings tn dn thn cn hn sn rn qn ct cd cth cc ch cs cr cq
  apply MMBProofRunExecution.checker_returns (by
    simp only [codeWithin, atomsWithin, expressionHeadWithin]
    decide +kernel)
  exact called bindings tn dn thn cn hn sn rn qn ct cd cth cc ch cs cr cq

private def requestBindings (tables : Proof.Tables) (context : Context) (recorded : List Sharing.Entry)
    (root : ProofWitness) (goal : Preterm) : Subst :=
  ("saved", listValue (recorded.map Sharing.entryValue)) ::
  [("claim", Data.preterm goal), ("root", Proof.witnessValue root),
   ("saved", .expression (recorded.map Sharing.entryValue)),
   ("hyps", ListSubstitution.expressionsValue tables.values), ("ctx", Data.context context),
   ("thms", TableAccess.tableValue tables.theorems), ("defs", TableAccess.tableValue tables.definitions),
   ("terms", TableAccess.tableValue tables.terms)]

private theorem request_shape (tables : Proof.Tables) (context : Context) (recorded : List Sharing.Entry)
    (root : ProofWitness) (goal : Preterm) (before : State) :
    Sharing.requestConfiguration before tables context recorded root goal =
      {state := before, control := .evaluate (requestBindings tables context recorded root goal)
        (.expression [.symbol "mm0:shared-proof", .var "terms", .var "defs", .var "thms", .var "ctx",
          .var "hyps", .var "saved", .var "root", .var "claim"])} := rfl

/-- Every admitted recorded submission terminates with the original Boolean
result. Its output store retains the existing proof-table readiness and
non-proof-store frame, including on refusal. -/
theorem loaded_source_sufficient_fuel (tables : Proof.Tables) (context : Context)
    (recorded : List Sharing.Entry) (root : ProofWitness) (goal : Preterm) (before : State)
    (input : Sharing.Input tables before) :
    ∃ after values answer fuel,
      (∀ extra, Eval.run program (fuel + extra)
        (Sharing.requestConfiguration before tables context recorded root goal) =
          .complete after [boolean answer] [] []) ∧
      Proof.Ready {tables with values := values} after ∧
      (Sharing.Checked context root goal tables recorded ↔ answer = true) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, values, answer, called, ready, justified, others, cells⟩ :=
    recorded_check_returns tables context recorded root goal before input
  let bindings := requestBindings tables context recorded root goal
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings before after _ _
    (called bindings "terms" "defs" "thms" "ctx" "hyps" "saved" "root" "claim" rfl rfl rfl rfl rfl rfl rfl rfl)
  refine ⟨after, values, answer, fuel, ?_, ready, justified, others, cells⟩
  intro extra
  rw [request_shape]
  exact completed_run_more_fuel program fuel extra _ after _ [] [] completed

theorem checked_iff_loaded_source_accepts (tables : Proof.Tables) (context : Context)
    (recorded : List Sharing.Entry) (root : ProofWitness) (goal : Preterm) (before : State)
    (input : Sharing.Input tables before) :
    Sharing.Checked context root goal tables recorded ↔
      ∃ after fuel, Eval.run program fuel (Sharing.requestConfiguration before tables context recorded root goal) =
        .complete after [boolean true] [] [] := by
  obtain ⟨reference, _, answer, referenceFuel, completed, _, justified, _, _⟩ :=
    loaded_source_sufficient_fuel tables context recorded root goal before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro accepted
    exact ⟨reference, referenceFuel, by simpa only [justified.mp accepted] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] []
      referenceCompleted returned
    apply justified.mpr
    simpa [boolean] using same.2.1

theorem refused_iff_loaded_source_refuses (tables : Proof.Tables) (context : Context)
    (recorded : List Sharing.Entry) (root : ProofWitness) (goal : Preterm) (before : State)
    (input : Sharing.Input tables before) :
    (¬ Sharing.Checked context root goal tables recorded) ↔
      ∃ after fuel, Eval.run program fuel (Sharing.requestConfiguration before tables context recorded root goal) =
        .complete after [boolean false] [] [] := by
  obtain ⟨reference, _, answer, referenceFuel, completed, _, justified, _, _⟩ :=
    loaded_source_sufficient_fuel tables context recorded root goal before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro refused
    have falseAnswer : answer = false := Bool.eq_false_iff.mpr (fun yes => refused (justified.mpr yes))
    exact ⟨reference, referenceFuel, by simpa only [falseAnswer] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] []
      referenceCompleted returned
    have falseAnswer : answer = false := by simpa [boolean] using same.2.1
    rw [justified, falseAnswer]
    decide

/-- A reference generated and retained by the binary recorder obtains its
logical claim from an actual accepted source-service execution. No incoming
proved atom or its tag is used as a proof-validity assumption. -/
theorem reference_derives_of_source_accepts (tables : Proof.Tables) (context : Context)
    (recorded : List Sharing.Entry) (root : ProofWitness) (goal : Preterm) (before after : State) (fuel : Nat)
    (input : Sharing.Input tables before)
    (completed : Eval.run program fuel (Sharing.requestConfiguration before tables context recorded root goal) =
      .complete after [boolean true] [] [])
    (witness target : Atom) (reference : ReferenceClaim tables.values recorded witness target) :
    ∃ index allocation claim node,
      witness = Proof.witnessValue (.hyp index) ∧ target = expressionValue allocation (Data.preterm claim) node ∧
      Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values claim := by
  obtain ⟨index, allocation, claim, node, witnessShape, targetShape, found⟩ := reference
  have accepted := (checked_iff_loaded_source_accepts tables context recorded root goal before input).mpr
    ⟨after, fuel, completed⟩
  exact ⟨index, allocation, claim, node, witnessShape, targetShape, claimedScope_derives accepted index claim found⟩

end Mettapedia.Languages.MM0.MeTTa.MMBRecordedWitnessAuthority
