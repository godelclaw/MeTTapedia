import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation

/-!
# Registered source exports as fixed-theory HOL proof graphs

Registered definition commands grow the source signature. The fixed-theory
graph checker instead treats each admitted defining sequent as an explicit
axiom. Primitive requests are rebuilt from the translated cache: the source
sequents remain unchanged, while the actual target checks propagate the
additional definition dependencies. Constant definitions contribute one
axiom; a type definition contributes its two independently checked outputs.
The originating command and output ordinal are retained in the axiom map.

This translation consumes the receipts of the existing registered receiver.
It neither authorizes source axioms nor bypasses source definition admission.
The finite target theory is relative to these explicit commitments; no
conservativity assertion is made for their use as axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportGraph

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open ProofExecution SourceSubstitution

inductive CommitmentKind where
  | sourceAxiom | constantDefinition | typeDefinition
  deriving DecidableEq, Repr

structure Commitment where
  kind : CommitmentKind
  origin : Origin
  outputOrdinal : Nat
  sequent : Sequent

def commandCommitments (receipt : Registered.CommandReceipt) : List Commitment :=
  match receipt.command with
  | .proof node _ =>
      match node.witness with
      | .inference _ => []
      | .axiom sequent => [⟨.sourceAxiom, node.origin, 0, sequent⟩]
  | .constant origin _ _ _ =>
      receipt.outputs.zipIdx.map fun (output, ordinal) =>
        ⟨.constantDefinition, origin, ordinal, output.sequent⟩
  | .typeDefinition origin _ _ _ =>
      receipt.outputs.zipIdx.map fun (output, ordinal) =>
        ⟨.typeDefinition, origin, ordinal, output.sequent⟩

def commitments (receipts : List Registered.CommandReceipt) : List Commitment :=
  receipts.flatMap commandCommitments

def axioms (receipts : List Registered.CommandReceipt) : List Sequent :=
  (commitments receipts).map Commitment.sequent

def finitePolicy (axioms : List Sequent) : AxiomPolicy := fun sequent => sequent ∈ axioms

instance (axioms : List Sequent) : DecidablePred (finitePolicy axioms) :=
  fun _ => inferInstanceAs (Decidable (_ ∈ axioms))

/-- Preserve every primitive parameter and replace only its actual ordered
premise theorem objects. Wrong premise-vector lengths are refused. -/
def rebindInference? : InferenceRequest → List Theorem → Option InferenceRequest
  | .refl term, [] => some (.refl term)
  | .beta term, [] => some (.beta term)
  | .assume term, [] => some (.assume term)
  | .trans _ _, [left, right] => some (.trans left right)
  | .mkComb _ _, [left, right] => some (.mkComb left right)
  | .eqMp _ _, [left, right] => some (.eqMp left right)
  | .deductAntisym _ _, [left, right] => some (.deductAntisym left right)
  | .abs binder _, [input] => some (.abs binder input)
  | .instType entries _, [input] => some (.instType entries input)
  | .inst entries _, [input] => some (.inst entries input)
  | _, _ => none

def rebindRequest? : RuleRequest → List Theorem → Option RuleRequest
  | .inference request, premises => (rebindInference? request premises).map .inference
  | .axiom sequent, [] => some (.axiom sequent)
  | _, _ => none

theorem rebindInference?_premises {request rebound : InferenceRequest}
    {premises : List Theorem} (computed : rebindInference? request premises = some rebound) :
    rebound.premises = premises := by
  unfold rebindInference? at computed
  split at computed <;> try contradiction
  all_goals cases Option.some.inj computed; rfl

/-- Primitive replay observes premise sequents independently of their retained
axiom dependency sets. -/
theorem rebindInference?_sequent {request rebound : InferenceRequest}
    {premises : List Theorem} (computed : rebindInference? request premises = some rebound)
    (same : request.premises.map Theorem.sequent = premises.map Theorem.sequent) :
    request.check.map Theorem.sequent = rebound.check.map Theorem.sequent := by
  unfold rebindInference? at computed
  split at computed <;> try contradiction
  all_goals cases Option.some.inj computed
  all_goals simp only [InferenceRequest.premises, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at same
  all_goals simp_all only [InferenceRequest.check, checkRefl, checkSourceBeta, checkAssume,
    checkTrans, checkApp, checkEqMp, checkDeductAntisym, checkAbs, checkTheoremSubstitution,
    substituteTheorem, Theorem.preserveAxiomsResult, Theorem.unionResult,
    bind, pure, Option.map_bind, Function.comp_def, apply_ite, Option.map_some, Option.map_none]
  all_goals simp

/-- Any correctly sized ordered theorem vector can replace the primitive
request's premises. -/
theorem rebindInference?_exists (request : InferenceRequest) (premises : List Theorem)
    (sameLength : request.premises.length = premises.length) :
    ∃ rebound, rebindInference? request premises = some rebound := by
  cases request <;> cases premises with
  | nil => simp_all [rebindInference?, InferenceRequest.premises]
  | cons first rest =>
    cases rest with
    | nil => simp_all [rebindInference?, InferenceRequest.premises]
    | cons second rest =>
      cases rest with
      | nil => simp_all [rebindInference?, InferenceRequest.premises]
      | cons third rest => simp_all [InferenceRequest.premises]

theorem rebindInference?_checked (request : InferenceRequest) (premises : List Theorem)
    {out : Theorem} (checked : request.check = some out)
    (same : request.premises.map Theorem.sequent = premises.map Theorem.sequent) :
    ∃ rebound actual, rebindInference? request premises = some rebound ∧
      rebound.check = some actual ∧ actual.sequent = out.sequent := by
  obtain ⟨rebound, reb⟩ := rebindInference?_exists request premises
    (by simpa using congrArg List.length same)
  have equality := rebindInference?_sequent reb same
  rw [checked, Option.map_some] at equality
  obtain ⟨actual, actualChecked, sameSequent⟩ := Option.map_eq_some_iff.mp equality.symm
  exact ⟨rebound, actual, reb, actualChecked, sameSequent⟩

theorem rebindRequest?_premises {request rebound : RuleRequest}
    {premises : List Theorem} (computed : rebindRequest? request premises = some rebound) :
    rebound.premises = premises := by
  cases request with
  | inference request =>
      obtain ⟨actual, bound, equal⟩ := Option.map_eq_some_iff.mp computed
      cases equal
      exact rebindInference?_premises bound
  | «axiom» sequent =>
      cases premises with
      | nil => cases Option.some.inj computed; rfl
      | cons head tail => simp [rebindRequest?] at computed

/-- Replay under the new policy retains the source result sequent.
Explicit axiom requests must belong to that policy. -/
theorem rebindRequest?_checked (beforePolicy afterPolicy : AxiomPolicy)
    [DecidablePred beforePolicy] [DecidablePred afterPolicy]
    (request : RuleRequest) (premises : List Theorem) {out : Theorem}
    (checked : request.check beforePolicy = some out)
    (same : request.premises.map Theorem.sequent = premises.map Theorem.sequent)
    (allowed : ∀ sequent, request = .axiom sequent → afterPolicy sequent) :
    ∃ rebound actual, rebindRequest? request premises = some rebound ∧
      rebound.check afterPolicy = some actual ∧ actual.sequent = out.sequent := by
  cases request with
  | inference request =>
    obtain ⟨rebound,actual,computed,checked,exactSequent⟩ :=
      rebindInference?_checked request premises checked same
    exact ⟨.inference rebound, actual, by simp [rebindRequest?,computed], checked,exactSequent⟩
  | «axiom» sequent =>
    cases premises with
    | cons first rest => simp [RuleRequest.premises] at same
    | nil =>
      have semantics := (RuleRequest.check_eq_some_iff beforePolicy (.axiom sequent) out).mp checked
      exact ⟨.axiom sequent,out,rfl,
        (RuleRequest.check_eq_some_iff afterPolicy (.axiom sequent) out).mpr
          ⟨semantics.1,allowed sequent rfl,semantics.2.2⟩,rfl⟩

structure State where
  cache : Array Theorem := #[]
  nodes : Array Receipt := #[]

def State.Checked (policy : AxiomPolicy) [DecidablePred policy] (state : State) : Prop :=
  DerivationGraph.replay (ruleWitness policy) state.nodes.toList = some state.cache

theorem empty_checked (policy : AxiomPolicy) [DecidablePred policy] :
    State.Checked policy ({} : State) := rfl

/-- Emit one original primitive graph node, comparing its computed sequent
with the original receiver's output before retaining the new dependency set. -/
def emit? (policy : AxiomPolicy) [DecidablePred policy] (before : State)
    (request : RuleRequest) (parents : List Nat) (origin : Origin)
    (expected : Sequent) : Option State := do
  let premises ← DerivationGraph.lookupPremises before.cache parents
  let request ← rebindRequest? request premises
  let conclusion ← request.check policy
  if conclusion.sequent ≠ expected then none else do
    let node : Receipt := ⟨conclusion, request, parents, origin⟩
    let cache ← node.replay (ruleWitness policy) before.cache
    pure ⟨cache, before.nodes.push node⟩

theorem emit?_result (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {request : RuleRequest} {parents : List Nat}
    {origin : Origin} {expected : Sequent}
    (computed : emit? policy before request parents origin expected = some after) :
    ∃ node : Receipt, node.parents = parents ∧ node.origin = origin ∧
      node.conclusion.sequent = expected ∧
      node.replay (ruleWitness policy) before.cache = some after.cache ∧
      after.nodes = before.nodes.push node := by
  cases hpremises : DerivationGraph.lookupPremises before.cache parents with
  | none => simp [emit?, hpremises] at computed
  | some premises =>
      cases hreb : rebindRequest? request premises with
      | none => simp [emit?, hpremises, hreb] at computed
      | some rebound =>
          cases hconcl : rebound.check policy with
          | none => simp [emit?, hpremises, hreb, hconcl] at computed
          | some conclusion =>
              by_cases same : conclusion.sequent = expected
              · let node : Receipt := ⟨conclusion, rebound, parents, origin⟩
                cases hreplayed : node.replay (ruleWitness policy) before.cache with
                | none => simp [emit?, hpremises, hreb, hconcl, same, node, hreplayed] at computed
                | some cache =>
                    have equal : (⟨cache, before.nodes.push node⟩ : State) = after := by
                      simpa [emit?, hpremises, hreb, hconcl, same, node, hreplayed] using computed
                    subst after
                    exact ⟨node, rfl, rfl, same, hreplayed, rfl⟩
              · simp [emit?, hpremises, hreb, hconcl, same] at computed

theorem emit?_checked (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {request : RuleRequest} {parents : List Nat}
    {origin : Origin} {expected : Sequent} (valid : before.Checked policy)
    (computed : emit? policy before request parents origin expected = some after) :
    after.Checked policy := by
  obtain ⟨node, _, _, _, replayed, nodes⟩ := emit?_result policy computed
  unfold State.Checked at valid ⊢
  rw [nodes, Array.toList_push]
  exact DerivationGraph.replayFrom_append (ruleWitness policy) valid
    (by simpa [DerivationGraph.replayFrom] using replayed)

/-- An admitted primitive step remains executable over a cache of the
same ordered premise sequents, with its new dependency annotations. -/
theorem emit?_complete (beforePolicy afterPolicy : AxiomPolicy)
    [DecidablePred beforePolicy] [DecidablePred afterPolicy]
    (before : State) (request : RuleRequest) (parents : List Nat) (origin : Origin)
    (premises : List Theorem) (out : Theorem)
    (found : DerivationGraph.lookupPremises before.cache parents = some premises)
    (checked : request.check beforePolicy = some out)
    (same : request.premises.map Theorem.sequent = premises.map Theorem.sequent)
    (allowed : ∀ sequent, request = .axiom sequent → afterPolicy sequent) :
    ∃ after, emit? afterPolicy before request parents origin out.sequent = some after := by
  obtain ⟨rebound,actual,computed,actualChecked,exactSequent⟩ :=
    rebindRequest?_checked beforePolicy afterPolicy request premises checked same allowed
  have instanceChecked : rebound.isInstance afterPolicy premises actual = true :=
    (RuleRequest.isInstance_eq_true_iff afterPolicy _ _ _).mpr
      ⟨rebindRequest?_premises computed,
          (RuleRequest.check_eq_some_iff afterPolicy rebound actual).mp actualChecked⟩
  let node : Receipt := ⟨actual,rebound,parents,origin⟩
  have replayed : node.replay (ruleWitness afterPolicy) before.cache =
      some (before.cache.push actual) :=
    (node.replay_eq_some_iff (ruleWitness afterPolicy) before.cache _).mpr
      ⟨premises,found,instanceChecked,rfl⟩
  refine ⟨⟨before.cache.push actual,before.nodes.push node⟩,?_⟩
  simp [emit?,found,computed,actualChecked,exactSequent,node,replayed]

def emitDefinitions? (policy : AxiomPolicy) [DecidablePred policy]
    (origin : Origin) : State → List Theorem → Option State
  | before, [] => some before
  | before, output :: rest => do
      let after ← emit? policy before (.axiom output.sequent) [] origin output.sequent
      emitDefinitions? policy origin after rest

theorem emitDefinitions?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (origin : Origin) {before after : State} {outputs : List Theorem}
    (valid : before.Checked policy)
    (computed : emitDefinitions? policy origin before outputs = some after) :
    after.Checked policy := by
  induction outputs generalizing before with
  | nil => cases Option.some.inj computed; exact valid
  | cons output outputs ih =>
      obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp computed
      exact ih (emit?_checked policy valid first) remaining

def command? (policy : AxiomPolicy) [DecidablePred policy] (before : State)
    (receipt : Registered.CommandReceipt) : Option State :=
  match receipt.command with
  | .proof node _ =>
      if receipt.outputs = [node.conclusion] then
        emit? policy before node.witness node.parents node.origin node.conclusion.sequent
      else none
  | .constant origin _ _ _ | .typeDefinition origin _ _ _ =>
      emitDefinitions? policy origin before receipt.outputs

theorem command?_checked (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {receipt : Registered.CommandReceipt}
    (valid : before.Checked policy)
    (computed : command? policy before receipt = some after) : after.Checked policy := by
  cases commandEq : receipt.command with
  | proof node witnesses =>
      simp only [command?, commandEq] at computed
      split at computed
      · exact emit?_checked policy valid computed
      · contradiction
  | constant origin name body witnesses =>
      exact emitDefinitions?_checked policy origin valid (by simpa [command?, commandEq] using computed)
  | typeDefinition origin request index witnesses =>
      exact emitDefinitions?_checked policy origin valid (by simpa [command?, commandEq] using computed)

def replay? (policy : AxiomPolicy) [DecidablePred policy] :
    State → List Registered.CommandReceipt → Option State
  | before, [] => some before
  | before, receipt :: rest => do
      let after ← command? policy before receipt
      replay? policy after rest

theorem replay?_checked (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {receipts : List Registered.CommandReceipt}
    (valid : before.Checked policy)
    (computed : replay? policy before receipts = some after) : after.Checked policy := by
  induction receipts generalizing before with
  | nil => cases Option.some.inj computed; exact valid
  | cons receipt receipts ih =>
      obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp computed
      exact ih (command?_checked policy valid first) remaining

/-- Lower the entire original receipt history under its explicitly collected
finite commitments. This is a computational replay, not proof extraction. -/
def lower? (source : ExportReplay.State) : Option State :=
  let receipts := source.registered.receipts.toList
  replay? (finitePolicy (axioms receipts)) {} receipts

theorem lower?_checked {source : ExportReplay.State} {result : State}
    (computed : lower? source = some result) :
    result.Checked (finitePolicy (axioms source.registered.receipts.toList)) :=
  replay?_checked _ (empty_checked _) computed

/-- Cache indices remain aligned with every ordered source output, including
both outputs of each admitted type definition. -/
theorem emit?_cache_sequents (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {request : RuleRequest} {parents : List Nat}
    {origin : Origin} {expected : Sequent}
    (computed : emit? policy before request parents origin expected = some after) :
    after.cache.toList.map Theorem.sequent =
      before.cache.toList.map Theorem.sequent ++ [expected] := by
  obtain ⟨node,_,_,same,replayed,_⟩ := emit?_result policy computed
  rw [DerivationGraph.Node.replay_eq_push (ruleWitness policy) replayed,
    Array.toList_push,List.map_append]
  simp [same]

theorem emitDefinitions?_cache_sequents (policy : AxiomPolicy) [DecidablePred policy]
    (origin : Origin) {before after : State} {outputs : List Theorem}
    (computed : emitDefinitions? policy origin before outputs = some after) :
    after.cache.toList.map Theorem.sequent =
      before.cache.toList.map Theorem.sequent ++ outputs.map Theorem.sequent := by
  induction outputs generalizing before with
  | nil => cases Option.some.inj computed; simp
  | cons output outputs ih =>
    obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp computed
    rw [ih remaining,emit?_cache_sequents policy first]
    simp [List.append_assoc]

theorem command?_cache_sequents (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {receipt : Registered.CommandReceipt}
    (computed : command? policy before receipt = some after) :
    after.cache.toList.map Theorem.sequent =
      before.cache.toList.map Theorem.sequent ++ receipt.outputs.map Theorem.sequent := by
  cases commandEq : receipt.command with
  | proof node witnesses =>
    simp only [command?,commandEq] at computed
    split at computed
    · rename_i outputsEq
      rw [outputsEq]
      simpa using emit?_cache_sequents policy computed
    · contradiction
  | constant origin name body witnesses =>
    exact emitDefinitions?_cache_sequents policy origin (by simpa [command?,commandEq] using computed)
  | typeDefinition origin request index witnesses =>
    exact emitDefinitions?_cache_sequents policy origin (by simpa [command?,commandEq] using computed)

theorem replay?_cache_sequents (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {receipts : List Registered.CommandReceipt}
    (computed : replay? policy before receipts = some after) :
    after.cache.toList.map Theorem.sequent = before.cache.toList.map Theorem.sequent ++
      receipts.flatMap (fun receipt => receipt.outputs.map Theorem.sequent) := by
  induction receipts generalizing before with
  | nil => cases Option.some.inj computed; simp
  | cons receipt receipts ih =>
    obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp computed
    rw [ih remaining,command?_cache_sequents policy first]
    simp [List.append_assoc]

theorem lower?_cache_sequents {source : ExportReplay.State} {result : State}
    (computed : lower? source = some result) :
    result.cache.toList.map Theorem.sequent = source.registered.receipts.toList.flatMap
      (fun receipt => receipt.outputs.map Theorem.sequent) := by
  simpa using replay?_cache_sequents _ computed

/-- Select the original source address and compare its complete sequent.
The returned graph claim retains the actual translated dependency set. -/
def root? (source : ExportReplay.State) (result : State) (id : Nat)
    (expected : Sequent) : Option (Theorem × ProofSystem.Certificate) := do
  let index ← source.addresses.get? id
  let original ← source.registered.cache[index]?
  if original.sequent ≠ expected then none else do
    let claim ← result.cache[index]?
    if claim.sequent ≠ expected then none else
      pure (claim, (result.nodes.toList, index))

theorem root?_checked {source : ExportReplay.State} {result : State} {id : Nat}
    {expected : Sequent} {claim : Theorem} {certificate : ProofSystem.Certificate}
    (lowered : lower? source = some result)
    (found : root? source result id expected = some (claim, certificate)) :
    (ProofSystem.checker (finitePolicy (axioms source.registered.receipts.toList))).check
      claim certificate = true ∧ claim.sequent = expected := by
  unfold root? at found
  simp only [bind, pure, Option.bind_eq_some_iff] at found
  obtain ⟨index, _, original, _, remaining⟩ := found
  split at remaining
  · contradiction
  · simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨actual, actualFound, remaining⟩ := remaining
    split at remaining
    · contradiction
    · rename_i same
      cases Option.some.inj remaining
      exact ⟨(ProofSystem.checker_check_iff _ _ _).mpr
        ⟨result.cache, lower?_checked lowered, actualFound⟩, not_ne_iff.mp same⟩

/-- The original accepted graph is supplied directly to the existing A3
translation, using its explicitly collected finite axiom list. -/
theorem root?_firstOrder_checked {source : ExportReplay.State} {result : State}
    {id : Nat} {expected : Sequent} {claim : Theorem}
    {certificate : ProofSystem.Certificate}
    (lowered : lower? source = some result)
    (found : root? source result id expected = some (claim, certificate)) :
    (Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmaChecker
      (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList))
      (FirstOrder.holCalculus_firstOrder_axioms (axioms source.registered.receipts.toList))).check
      (FirstOrder.render claim)
      (FirstOrder.graphTranslate
        (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList))
        rfl certificate) = true := by
  exact FirstOrder.graph_preserves
    (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList)) rfl (fun _ member => member)
    (FirstOrder.holCalculus_firstOrder_axioms _) (root?_checked lowered found).1

/-- A3 followed by the original shared-lemma compiler produces accepted
MM0 saved proofs. The actual root and every shared graph node are retained. -/
theorem root?_mm0_saved_checked {source : ExportReplay.State} {result : State}
    {id : Nat} {expected : Sequent} {claim : Theorem}
    {certificate : ProofSystem.Certificate}
    (lowered : lower? source = some result)
    (found : root? source result id expected = some (claim, certificate)) :
    let firstOrder := FirstOrder.holCalculus_firstOrder_axioms (axioms source.registered.receipts.toList)
    (Mettapedia.Languages.MM0.Translation.CalculusSimulation.savedChecker
      (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList)) firstOrder).check
      (FirstOrder.render claim)
      ((Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmaSimulation
        (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList)) firstOrder).translate
        (FirstOrder.render claim)
        (FirstOrder.graphTranslate
          (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList))
          rfl certificate)) = true := by
  exact (Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmaSimulation
    (definition := FirstOrder.validatedHolCalculus (axioms source.registered.receipts.toList))
    (FirstOrder.holCalculus_firstOrder_axioms _)).preserves _ _
      (root?_firstOrder_checked lowered found)

end Mettapedia.Languages.HOLLight.ExportGraph
