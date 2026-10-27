import Mettapedia.Languages.HOLLight.HypothesisExpansion

/-!
# Discharging two hypotheses from retained theorem-cache roots

Four primitive inferences discharge two cached facts from a third cached
theorem. The earlier proofs are referenced, not copied. The resulting claim
keeps its conclusion and the exact union of axiom dependencies. Empty output
hypotheses require actual coverage by the two proved facts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedHypothesisDischarge

open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open GraphExpansion HypothesisExpansion

def result (first second input : Theorem) : Theorem :=
  proveHypResult second (proveHypResult first input)

def block (first second input : Theorem)
    (firstType : first.sequent.concl.ty = input.sequent.concl.ty)
    (secondType : second.sequent.concl.ty = input.sequent.concl.ty)
    (origin : ProofExecution.Origin) : ProofSystem.Certificate :=
  ([⟨deductionResult first input firstType, .inference (.deductAntisym first input), [0, 2], origin⟩,
    ⟨proveHypResult first input, .inference (.eqMp (deductionResult first input firstType) first), [3, 0], origin⟩,
    ⟨deductionResult second (proveHypResult first input) secondType,
      .inference (.deductAntisym second (proveHypResult first input)), [1, 4], origin⟩,
    ⟨result first second input,
      .inference (.eqMp (deductionResult second (proveHypResult first input) secondType) second), [5, 1], origin⟩], 6)

theorem block_checked (policy : AxiomPolicy) [DecidablePred policy]
    (first second input : Theorem)
    (firstType : first.sequent.concl.ty = input.sequent.concl.ty)
    (secondType : second.sequent.concl.ty = input.sequent.concl.ty)
    (origin : ProofExecution.Origin) :
    BlockChecked policy [first, second, input] (result first second input)
      (block first second input firstType secondType origin) := by
  let nodes := (block first second input firstType secondType origin).1
  have nodeCount : nodes.length = 4 := rfl
  let initial := #[first, second, input]
  let a := initial.push (deductionResult first input firstType)
  let b := a.push (proveHypResult first input)
  let c := b.push (deductionResult second (proveHypResult first input) secondType)
  let d := c.push (result first second input)
  have step0 : nodes[0].replay (ruleWitness policy) initial = some a := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, deductionResult_checked first input firstType, rfl⟩
  have step1 : nodes[1].replay (ruleWitness policy) a = some b := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, proveHypResult_checked first input firstType, rfl⟩
  have step2 : nodes[2].replay (ruleWitness policy) b = some c := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, deductionResult_checked second (proveHypResult first input) secondType, rfl⟩
  have step3 : nodes[3].replay (ruleWitness policy) c = some d := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, proveHypResult_checked second (proveHypResult first input) secondType, rfl⟩
  refine ⟨d, ?_, rfl⟩
  change replayFrom (ruleWitness policy) initial [nodes[0], nodes[1], nodes[2], nodes[3]] = some d
  simp [replayFrom, step0, step1, step2, step3]

theorem result_conclusion (first second input : Theorem) :
    (result first second input).sequent.concl = input.sequent.concl := rfl

theorem result_axioms (first second input : Theorem) :
    (result first second input).axioms = second.axioms ∪ first.axioms ∪ input.axioms := by
  simp [result, proveHypResult, Theorem.unionResult, Finset.union_assoc]

theorem result_hypotheses_empty (first second input : Theorem)
    (firstClosed : first.sequent.hyp = ∅) (secondClosed : second.sequent.hyp = ∅)
    (covered : input.sequent.hyp ⊆ {first.sequent.concl, second.sequent.concl}) :
    (result first second input).sequent.hyp = ∅ := by
  simp only [result, proveHypResult, Theorem.unionResult, firstClosed, secondClosed, Finset.empty_union]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term member
  simp only [Finset.mem_erase] at member
  have present := covered member.2.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with equal | equal
  · exact member.2.1 equal
  · exact member.1 equal

/-- Lookup and type checks are performed on the actual receiving cache. -/
def close? (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (firstRoot secondRoot inputRoot : Nat) (origin : ProofExecution.Origin) :
    Option (ProofExecution.State × Nat) := do
  let first ← state.cache[firstRoot]?
  let second ← state.cache[secondRoot]?
  let input ← state.cache[inputRoot]?
  if sameFirst : Ty.same first.sequent.concl.ty input.sequent.concl.ty = true then
    if sameSecond : Ty.same second.sequent.concl.ty input.sequent.concl.ty = true then
      emitBlock policy [firstRoot, secondRoot, inputRoot]
        (block first second input ((Ty.same_eq_true_iff _ _).mp sameFirst)
          ((Ty.same_eq_true_iff _ _).mp sameSecond) origin) state
    else none
  else none

theorem close_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State}
    {first second input : Theorem} {firstRoot secondRoot inputRoot : Nat}
    (earlier : BuildChecked policy premises state)
    (firstFound : state.cache[firstRoot]? = some first)
    (secondFound : state.cache[secondRoot]? = some second)
    (inputFound : state.cache[inputRoot]? = some input)
    (firstType : first.sequent.concl.ty = input.sequent.concl.ty)
    (secondType : second.sequent.concl.ty = input.sequent.concl.ty)
    (origin : ProofExecution.Origin) :
    ∃ after root, close? policy state firstRoot secondRoot inputRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (result first second input) ∧
      after.receipts.size = state.receipts.size + 4 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  have selected : lookupPremises state.cache [firstRoot, secondRoot, inputRoot] = some [first, second, input] := by
    simp [lookupPremises, firstFound, secondFound, inputFound]
  obtain ⟨after, root, emitted, checked, found, _, preserved⟩ := emitBlock_checked earlier selected
    (block_checked policy first second input firstType secondType origin)
  have sizes := emitBlock_size emitted
  refine ⟨after, root, ?_, checked, found, ?_, preserved⟩
  · simpa [close?, firstFound, secondFound, inputFound,
      (Ty.same_eq_true_iff _ _).mpr firstType, (Ty.same_eq_true_iff _ _).mpr secondType] using emitted
  · simpa only [block, List.length_cons, List.length_nil] using sizes.2

theorem close_missing_first (policy : AxiomPolicy) [DecidablePred policy]
    (state : ProofExecution.State) (firstRoot secondRoot inputRoot : Nat) (origin : ProofExecution.Origin)
    (missing : state.cache[firstRoot]? = none) :
    close? policy state firstRoot secondRoot inputRoot origin = none := by
  simp [close?, missing]

/-- A closure result is publishable only after every hypothesis is removed. -/
def requireClosed? (state : ProofExecution.State) (root : Nat) : Option (ProofExecution.State × Nat) := do
  let fact ← state.cache[root]?
  if fact.sequent.hyp.card == 0 then some (state, root) else none

theorem requireClosed_iff (state : ProofExecution.State) (root : Nat) :
    requireClosed? state root = some (state, root) ↔
      ∃ fact, state.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ := by
  cases found : state.cache[root]? with
  | none => simp [requireClosed?, found]
  | some fact => simp [requireClosed?, found, Finset.card_eq_zero]

theorem requireClosed_missing (state : ProofExecution.State) (root : Nat)
    (missing : state.cache[root]? = none) : requireClosed? state root = none := by
  simp [requireClosed?, missing]

theorem requireClosed_hypothesis_refused (state : ProofExecution.State) (root : Nat) (fact : Theorem)
    (found : state.cache[root]? = some fact) (unresolved : fact.sequent.hyp ≠ ∅) :
    requireClosed? state root = none := by
  simp [requireClosed?, found, Finset.card_eq_zero, unresolved]

#print axioms block_checked
#print axioms result_hypotheses_empty
#print axioms close_checked

end Mettapedia.Languages.HOLLight.CachedHypothesisDischarge
