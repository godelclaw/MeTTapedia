import Mettapedia.Languages.HOLLight.InferenceHosting
import Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.GraphExpansion

/-!
# First-order inference presentations compiled to HOL Light

Each authored rule becomes one finite, universally quantified Horn axiom over
the shared data type. A source rule application instantiates this axiom with its
original arguments and discharges its ordered premises using the ten-rule HOL
Light kernel. The generated axiom policy admits only these complete, closed
sequents. Neither the source derivability relation nor a rule's conclusion is
used to generate an axiom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.InferenceCompiler

open Mettapedia.Logic
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Logic.HOL.Embedding.InferenceRules
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation

/-- The finite target theory contains one closed sequent per authored rule row. -/
def compileAxioms (definition : CalculusLanguageDef) : List Sequent :=
  (axioms (inferenceRules definition)).map fun formula => ⟨∅, render formula⟩

/-- The source claim is represented by an ordinary closed HOL proposition. -/
def compileClaim (goal : Pattern) : CanonicalTerm := render (judgment goal)

theorem compileAxioms_length (definition : CalculusLanguageDef) :
    (compileAxioms definition).length = definition.rules.length := by
  simp [compileAxioms, axioms, inferenceRules]

/-- Membership in the generated finite theory is exactly its target axiom policy. -/
theorem compileAxioms_policy (definition : CalculusLanguageDef) (sequent : Sequent) :
    sequent ∈ compileAxioms definition ↔ policy (inferenceRules definition) sequent := by
  unfold compileAxioms
  simp only [List.mem_map]
  constructor
  · rintro ⟨formula, member, rfl⟩
    exact ⟨rfl, List.mem_map.mpr ⟨formula, member, rfl⟩⟩
  · rintro ⟨hypotheses, member⟩
    obtain ⟨formula, member, conclusion⟩ := List.mem_map.mp member
    refine ⟨formula, member, ?_⟩
    cases sequent
    cases hypotheses
    cases conclusion
    rfl

/-- The complete finite target axiom list is admitted by the existing HOL
kernel's first-order rendering calculus, including duplicate axiom values. -/
theorem compileAxioms_valid (definition : CalculusLanguageDef) :
    (FirstOrder.holCalculus (compileAxioms definition)).isValid = true :=
  FirstOrder.holCalculus_valid_axioms _

/-- Each source derivation is replayed through the actual HOL Light primitive
kernel; quantifier instantiation and implication elimination retain their
explicit kernel evidence. -/
theorem preserves {rules : List FORule} (package : SchemaPackage rules) {goal : Pattern}
    (derivation : FODerivable rules goal) :
    KernelProvable (policy rules) ∅ (render (judgment goal)).term := by
  induction derivation with
  | rule rule member arguments arity _valid _premises ih =>
      have axiomProof := render_axiom rules (List.mem_map.mpr ⟨rule, member, rfl⟩)
      have instanceProof := render_closeAll_elim (policy rules)
        (openRule rule) (argumentSubstitution rule.vars arguments arity) axiomProof
      rw [subst_openRule package member arguments arity] at instanceProof
      apply render_hypChain_elim (policy rules) _ _ instanceProof
      intro premise premiseMember
      obtain ⟨sourcePremise, sourceMember, rfl⟩ := List.mem_map.mp premiseMember
      exact ih sourcePremise sourceMember

/-- Compilation preserves the original admitted calculus's derivations. -/
theorem derivation_preserves (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (derivation : Nonempty (InferenceChecker.Derivation definition goal)) :
    KernelProvable (policy (inferenceRules definition.1)) ∅ (compileClaim goal).term :=
  preserves (inferenceRules_schemaPackage firstOrder)
    ((derivation_iff definition firstOrder goal).mp derivation)

/-- A source checker receipt produces an accepted certificate for precisely
the compiled claim, with no hypotheses introduced at the boundary. -/
theorem checked_preserves (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (accepted : ∃ proof, checkRaw definition goal proof = true) :
    ∃ (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest),
      certificate.valid (ruleWitness (policy (inferenceRules definition.1))) = true ∧
      certificate.concl = out ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = compileClaim goal :=
  checked_of_render_provable _ _
    (preserves (inferenceRules_schemaPackage firstOrder)
      ((checker_iff definition firstOrder goal).mp accepted))

/-- Arbitrary target HOL Light inference, including admitted substitutions,
cannot invent an encoded canonical judgment outside the source calculus. -/
theorem checked_reflects (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (validGoal : argumentValidAt 0 goal = true)
    (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest)
    (accepted : certificate.valid (ruleWitness (policy (inferenceRules definition.1))) = true)
    (root : certificate.concl = out) (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = compileClaim goal) :
    ∃ proof, checkRaw definition goal proof = true := by
  apply (checker_iff definition firstOrder goal).mpr
  apply InferenceHosting.reflects (inferenceRules_schemaPackage firstOrder) validGoal
    _ hypotheses conclusion
  rw [← root]
  exact certificate.valid_sound (ruleWitness _) accepted

/-- The source checker and the actual ten-rule HOL Light checker accept
precisely the same canonical ground claims under the generated finite theory. -/
theorem checked_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (validGoal : argumentValidAt 0 goal = true) :
    (∃ proof, checkRaw definition goal proof = true) ↔
      ∃ (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest),
        certificate.valid (ruleWitness (policy (inferenceRules definition.1))) = true ∧
        certificate.concl = out ∧ out.sequent.hyp = ∅ ∧
        out.sequent.concl = compileClaim goal := by
  constructor
  · exact checked_preserves definition firstOrder
  · rintro ⟨out, certificate, accepted, root, hypotheses, conclusion⟩
    exact checked_reflects definition firstOrder validGoal out certificate
      accepted root hypotheses conclusion

/-- Faithful hosting also holds for the existing chronological graph checker.
This is an existence equivalence; computational graph expansion and its cost
are separate obligations. -/
theorem graph_checked_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (validGoal : argumentValidAt 0 goal = true) :
    (∃ proof, checkRaw definition goal proof = true) ↔
      ∃ (out : Theorem) (certificate : ProofSystem.Certificate),
        (ProofSystem.checker (policy (inferenceRules definition.1))).check out certificate = true ∧
        out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
  constructor
  · intro accepted
    obtain ⟨out, certificate, checked, root, hypotheses, conclusion⟩ :=
      checked_preserves definition firstOrder accepted
    subst out
    have derivation := certificate.valid_sound (ruleWitness _) checked
    obtain ⟨graph, graphAccepted⟩ :=
      (ProofSystem.checker_authority (policy (inferenceRules definition.1))).complete
        certificate.concl derivation
    exact ⟨certificate.concl, graph, graphAccepted, hypotheses, conclusion⟩
  · rintro ⟨out, certificate, accepted, hypotheses, conclusion⟩
    apply (checker_iff definition firstOrder goal).mpr
    apply InferenceHosting.reflects (inferenceRules_schemaPackage firstOrder) validGoal
      _ hypotheses conclusion
    exact (ProofSystem.checker_authority _).sound out certificate accepted

/-- The existing first-order presentation of the actual HOL kernel, equipped
with precisely this compiler's finite target axiom list. -/
def renderingCalculus (definition : CalculusLanguageDef) : ValidatedCalculusLanguageDef :=
  FirstOrder.validatedHolCalculus (compileAxioms definition)

theorem renderingCalculus_firstOrder (definition : CalculusLanguageDef) :
    FirstOrderCalculus (renderingCalculus definition).1 :=
  FirstOrder.holCalculus_firstOrder_axioms _

theorem compileAxioms_admitted (definition : CalculusLanguageDef) :
    ∀ sequent ∈ compileAxioms definition,
      sequent.hyp = ∅ ∧ policy (inferenceRules definition) sequent ∧ sequent.IsBool := by
  intro sequent member
  have admitted := (compileAxioms_policy definition sequent).mp member
  unfold compileAxioms at member
  simp only [List.mem_map] at member
  obtain ⟨formula, _, rfl⟩ := member
  exact ⟨rfl, admitted, render_isBool formula, by simp⟩

/-- One executable primitive axiom receipt for a physical authored rule row. -/
def axiomReceipt (definition : CalculusLanguageDef)
    (index : Fin (compileAxioms definition).length) : ProofExecution.Receipt :=
  let sequent := (compileAxioms definition).get index
  let admitted := compileAxioms_admitted definition sequent (List.getElem_mem index.isLt)
  ⟨Theorem.axiomResult sequent admitted.2.2, .axiom sequent, [], ("rule", index.val)⟩

/-- The finite declaration prefix is generated directly from the authored
theory. Duplicate row values retain separate physical receipts and origins. -/
def axiomGraph (definition : CalculusLanguageDef) : List ProofExecution.Receipt :=
  List.ofFn (axiomReceipt definition)

theorem axiomReceipt_checked (definition : CalculusLanguageDef)
    (index : Fin (compileAxioms definition).length) :
    (axiomReceipt definition index).witness.check (policy (inferenceRules definition)) =
      some (axiomReceipt definition index).conclusion := by
  apply (RuleRequest.check_eq_some_iff _ _ _).mpr
  let sequent := (compileAxioms definition).get index
  have admitted := compileAxioms_admitted definition sequent (List.getElem_mem index.isLt)
  exact ⟨admitted.1, admitted.2.1, admitted.2.2, rfl, rfl, rfl⟩

theorem axiomGraph_length (definition : CalculusLanguageDef) :
    (axiomGraph definition).length = definition.rules.length := by
  rw [axiomGraph, List.length_ofFn, compileAxioms_length]

theorem axiomGraph_origins (definition : CalculusLanguageDef) :
    (axiomGraph definition).map (fun receipt => receipt.origin) =
      List.ofFn (fun index : Fin (compileAxioms definition).length => ("rule", index.val)) := by
  simp only [axiomGraph, List.map_ofFn]
  rfl

private theorem replay_nullary {policy : AxiomPolicy} [DecidablePred policy]
    (nodes : List ProofExecution.Receipt)
    (checked : ∀ node ∈ nodes, node.parents = [] ∧ node.witness.premises = [] ∧
      node.witness.check policy = some node.conclusion) (cache : Array Theorem) :
    ∃ result, DerivationGraph.replayFrom (ruleWitness policy) cache nodes = some result := by
  induction nodes generalizing cache with
  | nil => exact ⟨cache, rfl⟩
  | cons node nodes ih =>
      obtain ⟨parents, premises, accepted⟩ := checked node (by simp)
      have first : node.replay (ruleWitness policy) cache = some (cache.push node.conclusion) :=
        (ProofSystem.node_replay_iff policy _ _ _).mpr
          ⟨by simp [parents, premises, DerivationGraph.lookupPremises], accepted, rfl⟩
      obtain ⟨result, replayed⟩ := ih
        (fun next member => checked next (List.mem_cons_of_mem _ member)) (cache.push node.conclusion)
      exact ⟨result, by simpa [DerivationGraph.replayFrom, first] using replayed⟩

/-- The generated declaration prefix is accepted by the actual HOL graph
replay and stores exactly its emitted theorem objects in physical order. -/
theorem axiomGraph_checked (definition : CalculusLanguageDef) :
    ∃ cache, DerivationGraph.replay (ruleWitness (policy (inferenceRules definition)))
      (axiomGraph definition) = some cache ∧
      cache.toList = (axiomGraph definition).map (fun receipt => receipt.conclusion) := by
  obtain ⟨cache, accepted⟩ := replay_nullary (axiomGraph definition) (by
    intro node member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨rfl, rfl, axiomReceipt_checked definition index⟩) #[]
  refine ⟨cache, accepted, ?_⟩
  exact DerivationGraph.replayFrom_toList (ruleWitness _) accepted

/-- The generated HOL kernel theory also feeds the existing independent MM0
saved-proof checker. All finite axiom-list admission obligations are earned. -/
theorem mm0_saved_checked_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (validGoal : argumentValidAt 0 goal = true) :
    (∃ proof, checkRaw definition goal proof = true) ↔
      ∃ certificate,
        (savedChecker (renderingCalculus_firstOrder definition.1)).check
          (FirstOrder.renderSequent ⟨∅, compileClaim goal⟩) certificate = true := by
  rw [FirstOrder.savedChecker_exact
    (axioms := compileAxioms definition.1)
    (definition := renderingCalculus definition.1) rfl
    (compileAxioms_admitted definition.1)
    (fun sequent admitted => (compileAxioms_policy definition.1 sequent).mpr admitted)
    (renderingCalculus_firstOrder definition.1)]
  constructor
  · intro accepted
    obtain ⟨out, graph, checked, hypotheses, conclusion⟩ :=
      (graph_checked_iff definition firstOrder validGoal).mp accepted
    refine ⟨out, (ProofSystem.checker_authority _).sound out graph checked, ?_⟩
    exact Sequent.ext hypotheses conclusion
  · rintro ⟨out, derivation, same⟩
    apply (checker_iff definition firstOrder goal).mpr
    apply InferenceHosting.reflects (inferenceRules_schemaPackage firstOrder) validGoal
      derivation
    · exact congrArg Sequent.hyp same
    · exact congrArg Sequent.concl same

namespace Controls

open FirstOrder.InferenceTranslation.Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

/-- A canonical binder-bearing data argument passes through both real checkers. -/
theorem binder_checked :
    ∃ (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest),
      certificate.valid (ruleWitness (policy (inferenceRules dataCalculus.1))) = true ∧
      certificate.concl = out ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = compileClaim (judgmentP binderValue) :=
  checked_preserves dataCalculus dataCalculus_firstOrder ⟨_, binder_accepted⟩

/-- The concrete finite theory retains one axiom for its single source rule. -/
theorem single_axiom : (compileAxioms dataCalculus.1).length = 1 := by
  rw [compileAxioms_length]
  rfl

def emptyCalculus : ValidatedCalculusLanguageDef :=
  ⟨modusPonens [], by decide +kernel⟩

theorem empty_firstOrder : FirstOrderCalculus emptyCalculus.1 :=
  firstOrderCheck_sound (by decide +kernel)

/-- An empty source theory cannot gain a conclusion through target HOL reasoning. -/
theorem empty_graph_refused :
    ¬ ∃ (out : Theorem) (certificate : ProofSystem.Certificate),
      (ProofSystem.checker (policy (inferenceRules emptyCalculus.1))).check out certificate = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim (judgmentP binderValue) := by
  intro accepted
  have canonical : argumentValidAt 0 (judgmentP binderValue) = true := by decide +kernel
  have sourceAccepted := (graph_checked_iff emptyCalculus empty_firstOrder canonical).mpr accepted
  have sourceDerivation := (checker_iff emptyCalculus empty_firstOrder _).mp sourceAccepted
  exact HOL.Embedding.InferenceRules.Controls.empty_underivable _ sourceDerivation

end Controls

end Mettapedia.Languages.HOLLight.InferenceCompiler
