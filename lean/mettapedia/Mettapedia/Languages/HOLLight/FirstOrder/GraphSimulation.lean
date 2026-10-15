import Mettapedia.Languages.HOLLight.FirstOrder.StepSizes
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.MM0.Translation.LemmaSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.CalculusControls

/-!
# HOL Light's proof graphs as lemma lists of its first-order calculus

`ProofSystem.checker` replays a proof graph: each node names a rule request, cites earlier
nodes, and is accepted when the cited theorems are the request's premises and the rule
computes the node's conclusion. The graph translates into a certificate of the calculus
with lemmas (`CalculusSimulation.lemmaChecker`): one lemma per node, proving the node's
rendered sequent from the rendered sequents before it, with the cited ones as premise
holes (`graphLemmas`). The claim's proof cites its node.

The proof of a node is built without HOL Light's kernel: structural comparisons decide
whether the data has the shapes its rule reads, and the node's core is erased
(`Steps.ruleProof`). Every node the kernel accepts passes the comparisons, so an accepted
graph translates into an accepted certificate (`graphLemmas_checked`, `graph_preserves`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (OpenDerivation RawOpenProof checkOpenRaw)
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (weight weights FirstOrder FirstOrderList FirstOrderClaim FirstOrderCalculus Lemmas LemmaCertificate
    checkLemmas lemmaChecker lemmasWeight openWeight comapChecker comapSimulation toSequent savedChecker lemmaSimulation
    firstOrderCheck_sound)
open Polynomial
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open ProofExecution (Receipt)
open Mettapedia.Logic (Derives)

/-! ## Rendering theorems as claims -/

theorem firstOrder_numeralP : ∀ count : Nat, FirstOrder (numeralP count)
  | 0 => .apply .nil
  | count + 1 => .apply (.cons (firstOrder_numeralP count) .nil)

mutual
  theorem firstOrder_toPattern : ∀ tree : LabeledTree, FirstOrder tree.toPattern
    | .node label children =>
        .apply (.cons (firstOrder_numeralP label) (.cons (firstOrder_toPatternList children) .nil))

  theorem firstOrder_toPatternList : ∀ trees : List LabeledTree, FirstOrder (LabeledTree.toPatternList trees)
    | [] => .apply .nil
    | tree :: rest => .apply (.cons (firstOrder_toPattern tree) (.cons (firstOrder_toPatternList rest) .nil))
end

theorem firstOrder_listP : ∀ {items : List Pattern}, (∀ item ∈ items, FirstOrder item) → FirstOrder (listP items)
  | [], _ => .apply .nil
  | item :: _, firstOrder =>
      .apply (.cons (firstOrder item (List.mem_cons.mpr (Or.inl rfl)))
        (.cons (firstOrder_listP fun other member => firstOrder other (List.mem_cons_of_mem _ member)) .nil))

theorem firstOrder_sequentJ (sequent : Sequent) : FirstOrder (sequentJ sequent) := by
  unfold sequentJ thmJ
  rw [sequentHypothesesP_eq_treesP]
  refine .apply (.cons (firstOrder_listP ?_) (.cons (firstOrder_toPattern _) .nil))
  intro item member
  obtain ⟨tree, -, rfl⟩ := List.mem_map.mp member
  exact firstOrder_toPattern tree

/-- A theorem as a claim of the calculus: its rendered sequent. -/
def render (claim : Theorem) : FirstOrderClaim := ⟨sequentJ claim.sequent, firstOrder_sequentJ _⟩

/-! ## The size of a proof graph -/

/-- The size of a node: its conclusion, its request and its citations. -/
def receiptSize (receipt : Receipt) : ℕ :=
  weight (sequentJ receipt.conclusion.sequent) + requestSize receipt.witness + receipt.parents.length + 1

/-- The size of a proof graph. -/
def graphSize (certificate : ProofSystem.Certificate) : ℕ := (certificate.1.map receiptSize).sum + 1

/-- HOL Light's checker of proof graphs, with claims measured by their rendering. -/
def holChecker (policy : AxiomPolicy) [DecidablePred policy] {definition : ValidatedCalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition.1) : SizedChecker Theorem ProofSystem.Certificate where
  check := (ProofSystem.checker policy).check
  claimSize claim := (toSequent firstOrder (render claim)).size
  certificateSize := graphSize

/-! ## Replay facts -/

theorem lookupPremises_getElem? : ∀ {cache : Array Theorem} {parents : List Nat} {premises : List Theorem},
    Logic.DerivationGraph.lookupPremises cache parents = some premises →
      ∀ (index : Nat) (bound : index < premises.length), cache[parents.getD index 0]? = some premises[index]
  | cache, [], premises, found, index, bound => by
      cases Option.some.inj found
      simp at bound
  | cache, parent :: parents, premises, found, index, bound => by
      cases head : cache[parent]? with
      | none => simp [Logic.DerivationGraph.lookupPremises, head] at found
      | some premise =>
          cases tail : Logic.DerivationGraph.lookupPremises cache parents with
          | none => simp [Logic.DerivationGraph.lookupPremises, head, tail] at found
          | some earlier =>
              have equal : premise :: earlier = premises := by
                simpa [Logic.DerivationGraph.lookupPremises, head, tail] using found
              subst premises
              cases index with
              | zero => simpa using head
              | succ index =>
                  simpa using lookupPremises_getElem? tail index (by simpa using bound)

theorem rendered_getElem? {cache : Array Theorem} {index : Nat} {claim : Theorem} (found : cache[index]? = some claim) :
    (cache.toList.map fun stored => sequentJ stored.sequent)[index]? = some (sequentJ claim.sequent) := by
  rw [List.getElem?_map, Array.getElem?_toList, found]
  rfl

theorem replayFrom_toList {policy : AxiomPolicy} [DecidablePred policy] :
    ∀ {cache result : Array Theorem} {nodes : List Receipt},
      Logic.DerivationGraph.replayFrom (ruleWitness policy) cache nodes = some result →
        result.toList = cache.toList ++ nodes.map (·.conclusion)
  | cache, result, [], replayed => by
      cases Option.some.inj replayed
      simp
  | cache, result, node :: rest, replayed => by
      cases first : node.replay (ruleWitness policy) cache with
      | none => simp [Logic.DerivationGraph.replayFrom, first] at replayed
      | some next =>
          have remaining : Logic.DerivationGraph.replayFrom (ruleWitness policy) next rest = some result := by
            simpa [Logic.DerivationGraph.replayFrom, first] using replayed
          rw [replayFrom_toList remaining, Logic.DerivationGraph.Node.replay_eq_push _ first]
          simp

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)

/-! ## The translation -/

include calculus in
/-- One lemma per node: the node's rendered sequent, proved from the rendered sequents before it. -/
def graphLemmas : List Pattern → List Receipt → Lemmas
  | _, [] => []
  | earlier, node :: rest =>
      (sequentJ node.conclusion.sequent, ruleProof calculus (context := earlier) node.parents node.witness) ::
        graphLemmas (earlier ++ [sequentJ node.conclusion.sequent]) rest

include calculus in
/-- A proof graph as a certificate of the calculus with lemmas. -/
def graphTranslate (certificate : ProofSystem.Certificate) : LemmaCertificate :=
  (graphLemmas calculus [] certificate.1, .premise certificate.2)

theorem graphLemmas_goals : ∀ (earlier : List Pattern) (nodes : List Receipt),
    (graphLemmas calculus earlier nodes).map Prod.fst = nodes.map fun node => sequentJ node.conclusion.sequent
  | _, [] => rfl
  | earlier, node :: rest => by
      rw [graphLemmas, List.map_cons, graphLemmas_goals, List.map_cons]

include calculus in
/-- **The lemmas of an accepted graph are accepted.** -/
theorem graphLemmas_checked {policy : AxiomPolicy} [DecidablePred policy]
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) :
    ∀ {cache : Array Theorem} {nodes : List Receipt} {result : Array Theorem},
      Logic.DerivationGraph.replayFrom (ruleWitness policy) cache nodes = some result →
        checkLemmas definition (cache.toList.map fun stored => sequentJ stored.sequent)
          (graphLemmas calculus (cache.toList.map fun stored => sequentJ stored.sequent) nodes) = true
  | cache, [], _, _ => rfl
  | cache, node :: rest, result, replayed => by
      cases first : node.replay (ruleWitness policy) cache with
      | none => simp [Logic.DerivationGraph.replayFrom, first] at replayed
      | some next =>
          have remaining : Logic.DerivationGraph.replayFrom (ruleWitness policy) next rest = some result := by
            simpa [Logic.DerivationGraph.replayFrom, first] using replayed
          obtain ⟨premises, found, admitted, pushed⟩ := (Logic.DerivationGraph.Node.replay_eq_some_iff _ _ _ _).mp first
          obtain ⟨same, semantics⟩ := (RuleRequest.isInstance_eq_true_iff policy _ _ _).mp admitted
          rw [graphLemmas, checkLemmas, Bool.and_eq_true]
          refine ⟨ruleProof_accepted calculus inList node.parents node.witness semantics fun index => ?_, ?_⟩
          · subst same
            have cited := lookupPremises_getElem? found index index.2
            rw [List.get_eq_getElem]
            exact rendered_getElem? cited
          · have rested := graphLemmas_checked inList remaining
            rw [pushed] at rested
            simpa [Array.toList_push] using rested

include calculus in
/-- **An accepted proof graph translates into an accepted certificate with lemmas.** -/
theorem graph_preserves {policy : AxiomPolicy} [DecidablePred policy]
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (firstOrder : FirstOrderCalculus definition.1)
    {claim : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker policy).check claim certificate = true) :
    (lemmaChecker firstOrder).check (render claim) (graphTranslate calculus certificate) = true := by
  obtain ⟨cache, replayed, found⟩ := (ProofSystem.checker_check_iff policy claim certificate).mp accepted
  have checked := graphLemmas_checked calculus inList (cache := #[]) replayed
  have goals : (graphLemmas calculus [] certificate.1).map Prod.fst =
      cache.toList.map fun stored => sequentJ stored.sequent := by
    rw [graphLemmas_goals, replayFrom_toList replayed]
    simp
  simp only [lemmaChecker, graphTranslate, Bool.and_eq_true]
  refine ⟨by simpa using checked, ?_⟩
  rw [goals, checkOpenRaw, rendered_getElem? found]
  simp [render]

/-! ## Sizes -/

theorem receiptSize_bounds (node : Receipt) :
    weight (sequentJ node.conclusion.sequent) + requestSize node.witness + 1 ≤ receiptSize node := by
  unfold receiptSize
  omega

theorem le_succ_pow (value : ℕ) : value + 1 ≤ (value + 1) ^ 9 :=
  le_trans (le_of_eq (pow_one (value + 1)).symm) (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem lemmaWeight_node (earlier : List Pattern) (node : Receipt) :
    weight (sequentJ node.conclusion.sequent) +
        openWeight (ruleProof calculus (context := earlier) node.parents node.witness) ≤
      (nodeFactor + 1) * (receiptSize node + 1) ^ 9 := by
  have proof := ruleProof_weight calculus (context := earlier) node.parents node.witness
  have bounds := receiptSize_bounds node
  have mono : (requestSize node.witness + 1) ^ 9 ≤ (receiptSize node + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have grows := le_succ_pow (receiptSize node)
  have scaled := Nat.mul_le_mul_left nodeFactor mono
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem lemmasWeight_graphLemmas : ∀ (earlier : List Pattern) (nodes : List Receipt),
    lemmasWeight (graphLemmas calculus earlier nodes) ≤
      (nodes.map fun node => (nodeFactor + 1) * (receiptSize node + 1) ^ 9).sum
  | _, [] => by simp [graphLemmas, lemmasWeight]
  | earlier, node :: rest => by
      have first := lemmaWeight_node calculus earlier node
      have rested := lemmasWeight_graphLemmas (earlier ++ [sequentJ node.conclusion.sequent]) rest
      rw [graphLemmas, lemmasWeight, List.map_cons, List.sum_cons]
      omega

theorem sum_within : ∀ {nodes : List Receipt} {bound : ℕ}, (∀ node ∈ nodes, receiptSize node ≤ bound) →
    (nodes.map fun node => (nodeFactor + 1) * (receiptSize node + 1) ^ 9).sum ≤
      nodes.length * ((nodeFactor + 1) * (bound + 1) ^ 9)
  | [], _, _ => by simp
  | node :: rest, bound, small => by
      have first : (nodeFactor + 1) * (receiptSize node + 1) ^ 9 ≤ (nodeFactor + 1) * (bound + 1) ^ 9 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := small node (List.mem_cons.mpr (Or.inl rfl)); omega) 9)
      have rested := sum_within (bound := bound) fun other member => small other (List.mem_cons_of_mem _ member)
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have expand : (rest.length + 1) * ((nodeFactor + 1) * (bound + 1) ^ 9) =
          rest.length * ((nodeFactor + 1) * (bound + 1) ^ 9) + (nodeFactor + 1) * (bound + 1) ^ 9 := by ring
      omega

theorem length_le_sum : ∀ nodes : List Receipt, nodes.length ≤ (nodes.map receiptSize).sum
  | [] => by simp
  | node :: rest => by
      have first := receiptSize_bounds node
      have rested := length_le_sum rest
      rw [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem receiptSize_le_sum {nodes : List Receipt} {node : Receipt} (member : node ∈ nodes) :
    receiptSize node ≤ (nodes.map receiptSize).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨node, member, rfl⟩)

/-- **The certificate of a proof graph is polynomial in the graph.** -/
theorem graphTranslate_weight (certificate : ProofSystem.Certificate) :
    lemmasWeight (graphTranslate calculus certificate).1 + openWeight (graphTranslate calculus certificate).2 ≤
      (nodeFactor + 2) * (graphSize certificate + 1) ^ 10 := by
  have lemmas := lemmasWeight_graphLemmas calculus [] certificate.1
  have summed := sum_within (nodes := certificate.1) (bound := (certificate.1.map receiptSize).sum)
    fun node member => receiptSize_le_sum member
  have counted := length_le_sum certificate.1
  set total := (certificate.1.map receiptSize).sum with totalEq
  have sized : graphSize certificate = total + 1 := rfl
  have product : certificate.1.length * ((nodeFactor + 1) * (total + 1) ^ 9) ≤
      (nodeFactor + 1) * (total + 1) ^ 10 := by
    calc certificate.1.length * ((nodeFactor + 1) * (total + 1) ^ 9)
        ≤ (total + 1) * ((nodeFactor + 1) * (total + 1) ^ 9) := Nat.mul_le_mul_right _ (by omega)
      _ = (nodeFactor + 1) * (total + 1) ^ 10 := by ring
  have larger : (total + 1) ^ 10 ≤ (graphSize certificate + 1) ^ 10 := Nat.pow_le_pow_left (by omega) 10
  have one : 1 ≤ (graphSize certificate + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
  simp only [graphTranslate, openWeight]
  nlinarith

/-! ## Time -/

/-- The time to translate the nodes from a context: for each node, one unit per earlier lemma
passed when locating the cited ones, the fourth power of the node's size for reading, comparing
and sorting its data, and one unit per symbol of the lemma written. -/
def graphTime : List Pattern → List Receipt → ℕ
  | _, [] => 0
  | earlier, node :: rest =>
      earlier.length + (receiptSize node + 1) ^ 4 + weight (sequentJ node.conclusion.sequent) +
        openWeight (ruleProof calculus (context := earlier) node.parents node.witness) +
          graphTime (earlier ++ [sequentJ node.conclusion.sequent]) rest

theorem graphTime_le : ∀ (earlier : List Pattern) (nodes : List Receipt) (bound : ℕ),
    (∀ node ∈ nodes, receiptSize node ≤ bound) → earlier.length + nodes.length ≤ bound →
      graphTime calculus earlier nodes ≤ nodes.length * ((nodeFactor + 3) * (bound + 1) ^ 9)
  | _, [], _, _, _ => by simp [graphTime]
  | earlier, node :: rest, bound, small, short => by
      have nodeSmall := small node (List.mem_cons.mpr (Or.inl rfl))
      have first := lemmaWeight_node calculus earlier node
      have rested := graphTime_le (earlier ++ [sequentJ node.conclusion.sequent]) rest bound
        (fun other member => small other (List.mem_cons_of_mem _ member)) (by simp at short ⊢; omega)
      have weighed : (nodeFactor + 1) * (receiptSize node + 1) ^ 9 ≤ (nodeFactor + 1) * (bound + 1) ^ 9 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 9)
      have fourth : (receiptSize node + 1) ^ 4 ≤ (bound + 1) ^ 9 :=
        le_trans (Nat.pow_le_pow_left (by omega) 4) (Nat.pow_le_pow_right (by omega) (by norm_num))
      have lengthLe : earlier.length ≤ (bound + 1) ^ 9 := le_trans (by simp at short; omega) (le_succ_pow bound)
      rw [graphTime, List.length_cons]
      have expand : (rest.length + 1) * ((nodeFactor + 3) * (bound + 1) ^ 9) =
          rest.length * ((nodeFactor + 3) * (bound + 1) ^ 9) + ((nodeFactor + 1) * (bound + 1) ^ 9 +
            (bound + 1) ^ 9 + (bound + 1) ^ 9) := by ring
      omega

/-! ## The p-simulation -/

/-- A graph translates into one lemma per node, with a degree-ten certificate
bound and a degree-ten declared cost account. `PSimulation` does not connect
that account to an operational execution of this translator. -/
def graphTrace {policy : AxiomPolicy} [DecidablePred policy] (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    (firstOrder : FirstOrderCalculus definition.1) :
    PSimulation (comapChecker render (lemmaChecker firstOrder)) (holChecker policy firstOrder) where
  translate _ certificate := graphTranslate calculus certificate
  preserves _ _ accepted := graph_preserves calculus inList firstOrder accepted
  sizeBound := ⟨C (nodeFactor + 2) * (X + 1) ^ 10, fun input => by
    have bound := graphTranslate_weight calculus input.2
    have larger : (graphSize input.2 + 1) ^ 10 ≤ ((holChecker policy firstOrder).inputSize input + 1) ^ 10 :=
      Nat.pow_le_pow_left (by simp only [SizedChecker.inputSize, holChecker]; omega) 10
    simp only [comapChecker, lemmaChecker, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    nlinarith⟩
  translationTime _ certificate := graphTime calculus [] certificate.1 + 1
  timeBound := ⟨C (nodeFactor + 4) * (X + 1) ^ 10, fun input => by
    have counted := length_le_sum input.2.1
    have timed := graphTime_le calculus [] input.2.1 ((input.2.1.map receiptSize).sum)
      (fun node member => receiptSize_le_sum member) (by simpa using counted)
    set total := (input.2.1.map receiptSize).sum with totalEq
    have sized : graphSize input.2 = total + 1 := rfl
    have product : input.2.1.length * ((nodeFactor + 3) * (total + 1) ^ 9) ≤
        (nodeFactor + 3) * (total + 1) ^ 10 := by
      calc input.2.1.length * ((nodeFactor + 3) * (total + 1) ^ 9)
          ≤ (total + 1) * ((nodeFactor + 3) * (total + 1) ^ 9) := Nat.mul_le_mul_right _ (by omega)
        _ = (nodeFactor + 3) * (total + 1) ^ 10 := by ring
    have larger : (total + 1) ^ 10 ≤ ((holChecker policy firstOrder).inputSize input + 1) ^ 10 :=
      Nat.pow_le_pow_left (by simp only [SizedChecker.inputSize, holChecker]; omega) 10
    have one : 1 ≤ ((holChecker policy firstOrder).inputSize input + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    nlinarith⟩

/-- The rendered theorem of an accepted HOL graph is accepted by MM0 with
saved proofs. The certificate size and declared translation cost are polynomial
in the graph; an operational polynomial-time realization is a separate law. -/
def mm0Simulation {policy : AxiomPolicy} [DecidablePred policy] (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    (firstOrder : FirstOrderCalculus definition.1) :
    PSimulation (comapChecker render (savedChecker firstOrder)) (holChecker policy firstOrder) :=
  (comapSimulation render (lemmaSimulation firstOrder)).trans (graphTrace calculus inList firstOrder) rfl

/-! ## Exactness on the MM0 side -/

/-- A sequent as a claim of the calculus. -/
def renderSequent (sequent : Sequent) : FirstOrderClaim := ⟨sequentJ sequent, firstOrder_sequentJ sequent⟩

include calculus in
/-- **MM0 with saved proofs accepts the rendering of a sequent exactly when HOL Light derives it**,
for axioms admitted by a policy that admits nothing else. -/
theorem savedChecker_exact {policy : AxiomPolicy} [DecidablePred policy]
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (firstOrder : FirstOrderCalculus definition.1)
    (sequent : Sequent) :
    (∃ certificate, (savedChecker firstOrder).check (renderSequent sequent) certificate = true) ↔
      ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent := by
  constructor
  · rintro ⟨certificate, accepted⟩
    have derived := Mettapedia.Languages.MM0.Translation.CalculusSimulation.savedChecker_sound firstOrder accepted
    obtain ⟨witness, checked⟩ := (Mettapedia.Languages.MM0.Kernel.derives_iff_checked _ _ _ _ _ _).mp derived
    have calculusAccepted := (Mettapedia.Languages.MM0.Translation.CalculusSimulation.calculusSimulation
      firstOrder).preserves (renderSequent sequent) witness checked
    exact (holCalculus_accepts_iff calculus policy admitted inList sequent).mp ⟨_, calculusAccepted⟩
  · rintro ⟨out, derived, same⟩
    obtain ⟨certificate, accepted⟩ := (ProofSystem.checker_authority policy).complete out derived
    have translated := (mm0Simulation calculus inList firstOrder).preserves out certificate accepted
    have rendered : render out = renderSequent sequent := Subtype.ext (by simp [render, renderSequent, same])
    exact ⟨_, by simpa [comapChecker, rendered] using translated⟩

end Calculus

/-! ## HOL Light's kernel -/

namespace Kernel

open CalculusControls

theorem firstOrder : FirstOrderCalculus validated.1 := firstOrderCheck_sound holCalculus_firstOrder

/-- **MM0 with saved proofs p-simulates HOL Light's kernel**, the ten inference rules with no
axioms, on its proof graphs. -/
def mm0Simulation : PSimulation (comapChecker render (savedChecker firstOrder))
    (holChecker emptyAxiomPolicy firstOrder) :=
  FirstOrder.mm0Simulation (axioms := []) (definition := validated) rfl
    (fun _ impossible => impossible.elim) firstOrder

/-- A positive control: the one-node graph proving `p = p` by `REFL` translates into a
certificate the MM0 kernel with saved proofs accepts. -/
theorem reflexivity_accepted :
    (savedChecker firstOrder).check (render ProofExecution.Controls.reflexivityTheorem)
      (mm0Simulation.translate ProofExecution.Controls.reflexivityTheorem
        ProofSystem.Controls.reflexivityCertificate) = true :=
  mm0Simulation.preserves _ _ ProofSystem.Controls.reflexivity_accepted

/-- A negative control: MM0 with saved proofs accepts no certificate for `⊢ F`, since HOL
Light's kernel does not derive it. -/
theorem falsity_refused (certificate : Mettapedia.Languages.MM0.Translation.CalculusSimulation.SavedCertificate) :
    (savedChecker firstOrder).check (renderSequent ⟨∅, falsity⟩) certificate = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  obtain ⟨out, derived, same⟩ := (savedChecker_exact (axioms := []) (definition := validated) rfl
    (policy := emptyAxiomPolicy) (fun _ member => absurd member (List.not_mem_nil))
    (fun _ impossible => impossible.elim) firstOrder ⟨∅, falsity⟩).mp ⟨certificate, accepted⟩
  exact falsity_not_derivable (derives_shared emptyAxiomPolicy derived) same

end Kernel

end Mettapedia.Languages.HOLLight.FirstOrder
