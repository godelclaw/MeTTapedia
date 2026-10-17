import Mettapedia.Languages.HOLLight.InferenceHosting
import Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Languages.HOLLight.InferenceRuleExpansion
import Mettapedia.Languages.HOLLight.StorageSize
import Mettapedia.Languages.HOLLight.InferenceStorageBounds
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mathlib.Data.Nat.Digits.Lemmas

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

/-! ## Chronological compilation of the existing source certificates -/

/-- Every axiom tag of an accepted target proof comes from an actual generated
source-rule axiom. The checker cannot introduce a separate theory premise. -/
theorem graph_authorized_axioms (definition : CalculusLanguageDef)
    {out : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker (policy (inferenceRules definition))).check out certificate = true) :
    ∀ sequent ∈ out.axioms, sequent ∈ compileAxioms definition := by
  have derivation := (ProofSystem.checker_authority _).sound out certificate accepted
  have shared := Mettapedia.Languages.HOLLight.derives_shared _ derivation
  have authorized := Mettapedia.Languages.OpenTheory.derives_only_authorized_axioms _ shared
  intro sequent member
  exact (compileAxioms_policy definition sequent).mpr (authorized sequent member)

/-- A compiled proof's dependency set is bounded by the finite authored rule
table, independently of how many times its saved proofs are referenced. -/
theorem graph_axiom_count (definition : CalculusLanguageDef)
    {out : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker (policy (inferenceRules definition))).check out certificate = true) :
    out.axioms.card ≤ definition.rules.length := by
  have included : out.axioms ⊆ (compileAxioms definition).toFinset := by
    intro sequent member
    exact List.mem_toFinset.mpr (graph_authorized_axioms definition accepted sequent member)
  calc
    out.axioms.card ≤ (compileAxioms definition).toFinset.card := Finset.card_le_card included
    _ ≤ (compileAxioms definition).length := List.toFinset_card_le _
    _ = definition.rules.length := compileAxioms_length definition

/-- An accepted source-claim theorem has a complete payload bound: its
axiom dependencies come from the finite theory and its conclusion uses the
actual typed data rendering. -/
theorem graph_theorem_storage (definition : CalculusLanguageDef) (goal : Pattern)
    {out : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker (policy (inferenceRules definition))).check out certificate = true)
    (hypotheses : out.sequent.hyp = ∅) (conclusion : out.sequent.concl = compileClaim goal) :
    OpenTheory.StorageSize.theoremData out ≤
      InferenceStorageBounds.theoryPayload (inferenceRules definition) + 3 +
        184 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight goal := by
  have allowed : (policy (inferenceRules definition)).AllowsTheorem out := by
    intro tagged member
    exact (compileAxioms_policy definition tagged).mp (graph_authorized_axioms definition accepted tagged member)
  have tags := InferenceStorageBounds.theorem_storage (inferenceRules definition) out allowed hypotheses
  have rendered := InferenceStorageBounds.render_judgment_storage goal
  rw [conclusion] at tags
  exact tags.trans (Nat.add_le_add_left rendered _)

open Mettapedia.GSLT.LanguageDef.CertificateGSLT (RawOpenProof)

/-- A local emitter computes explicit kernel requests for one original rule
instance and its ordered theorem premises. Its output is replayed by HOL Light;
the emitter is not installed as a new rule authority. -/
abbrev RuleEmitter := RuleInstance → List Theorem → ProofExecution.Origin → Option ProofSystem.Certificate

/-- Physical roots already admitted by a builder remain available unchanged. -/
def KeepsOld (before after : ProofExecution.State) : Prop :=
  ∀ (index : Nat) (out : Theorem), before.cache[index]? = some out → after.cache[index]? = some out

theorem KeepsOld.refl (state : ProofExecution.State) : KeepsOld state state := fun _ _ found => found

theorem KeepsOld.trans {first middle last : ProofExecution.State}
    (initial : KeepsOld first middle) (later : KeepsOld middle last) : KeepsOld first last :=
  fun index out found => later index out (initial index out found)

private theorem emittedBlock_safe {axiomPolicy : AxiomPolicy} [DecidablePred axiomPolicy]
    {premises : List Theorem} {state result : ProofExecution.State} {root : Nat}
    {roots : List Nat} {block : ProofSystem.Certificate}
    (earlier : GraphExpansion.BuildChecked axiomPolicy premises state)
    (emitted : GraphExpansion.emitBlock axiomPolicy roots block state = some (result, root)) :
    GraphExpansion.BuildChecked axiomPolicy premises result ∧ KeepsOld state result ∧
      ∃ out, result.cache[root]? = some out := by
  cases selected : DerivationGraph.lookupPremises state.cache roots with
  | none => simp [GraphExpansion.emitBlock, selected] at emitted
  | some inputs =>
      cases replayed : DerivationGraph.replayFrom (ruleWitness axiomPolicy) state.cache
          (GraphExpansion.expandBlock roots state.cache.size block).1 with
      | none => simp [GraphExpansion.emitBlock, selected, replayed] at emitted
      | some cache =>
          cases found : cache[(GraphExpansion.expandBlock roots state.cache.size block).2]? with
          | none => simp [GraphExpansion.emitBlock, selected, replayed, found] at emitted
          | some out =>
              have same :
                  (⟨cache, state.receipts ++ (GraphExpansion.expandBlock roots state.cache.size block).1.toArray⟩,
                    (GraphExpansion.expandBlock roots state.cache.size block).2) = (result, root) := by
                simpa [GraphExpansion.emitBlock, selected, replayed, found] using emitted
              obtain ⟨sameState, sameRoot⟩ := Prod.mk.inj same
              subst result
              subst root
              refine ⟨?_, ?_, out, found⟩
              · unfold GraphExpansion.BuildChecked
                simp only [Array.toList_append]
                exact DerivationGraph.replayFrom_append (ruleWitness axiomPolicy) earlier replayed
              · intro index fact foundEarlier
                exact DerivationGraph.replayFrom_preserves_lookup (ruleWitness axiomPolicy) replayed foundEarlier

/-- The expected source judgment is checked against the complete target sequent.
The theorem's axiom provenance is retained by the existing theorem object. -/
def hasClaim (goal : Pattern) (out : Theorem) : Bool :=
  decide (out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal)

/-- A source-claim interface to the original HOL graph replay. The graph need
not have been emitted by this compiler. Canonical source claims are admitted
explicitly; the selected target theorem must have exactly the encoded claim
and no residual hypotheses. -/
def compiledChecker (definition : CalculusLanguageDef) :
    KernelAuthority.Checker Pattern ProofSystem.Certificate where
  check goal certificate := argumentValidAt 0 goal &&
    match DerivationGraph.replay (ruleWitness (policy (inferenceRules definition))) certificate.1 with
    | none => false
    | some cache =>
        match cache[certificate.2]? with
        | none => false
        | some out => hasClaim goal out

/-- The claim interface neither adds rules nor accepts a residual hypothesis.
Its successful observations are precisely those of the original graph checker
with the declared compiled conclusion. -/
theorem compiledChecker_check_iff (definition : CalculusLanguageDef)
    (goal : Pattern) (certificate : ProofSystem.Certificate) :
    (compiledChecker definition).check goal certificate = true ↔
      argumentValidAt 0 goal = true ∧ ∃ out,
        (ProofSystem.checker (policy (inferenceRules definition))).check out certificate = true ∧
        out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
  simp only [compiledChecker, Bool.and_eq_true]
  constructor
  · rintro ⟨valid, accepted⟩
    cases replayed : DerivationGraph.replay (ruleWitness (policy (inferenceRules definition)))
        certificate.1 with
    | none => simp [replayed] at accepted
    | some cache =>
        cases found : cache[certificate.2]? with
        | none => simp [replayed, found] at accepted
        | some out =>
            have claim : out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
              simpa [replayed, found, hasClaim] using accepted
            exact ⟨valid, out,
              (ProofSystem.checker_check_iff _ _ _).mpr ⟨cache, replayed, found⟩, claim⟩
  · rintro ⟨valid, out, accepted, hypotheses, conclusion⟩
    obtain ⟨cache, replayed, found⟩ := (ProofSystem.checker_check_iff _ _ _).mp accepted
    exact ⟨valid, by simp [replayed, found, hasClaim, hypotheses, conclusion]⟩

/-- Independent target replay has exact authority for the original admitted
calculus on canonical source claims. Reflection ranges over every accepted
target graph, rather than only outputs of the source compiler. -/
theorem compiledChecker_authority (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    (compiledChecker definition.1).Authority (fun goal =>
      argumentValidAt 0 goal = true ∧ Nonempty (InferenceChecker.Derivation definition goal)) where
  sound goal certificate accepted := by
    obtain ⟨valid, out, checked, hypotheses, conclusion⟩ :=
      (compiledChecker_check_iff definition.1 goal certificate).mp accepted
    have source := (graph_checked_iff definition firstOrder valid).mpr
      ⟨out, certificate, checked, hypotheses, conclusion⟩
    exact ⟨valid, (derivation_iff definition firstOrder goal).mpr
      ((checker_iff definition firstOrder goal).mp source)⟩
  complete goal meaningful := by
    obtain ⟨valid, derivation⟩ := meaningful
    have source := (checker_iff definition firstOrder goal).mpr
      ((derivation_iff definition firstOrder goal).mp derivation)
    obtain ⟨out, certificate, checked, hypotheses, conclusion⟩ :=
      (graph_checked_iff definition firstOrder valid).mp source
    exact ⟨certificate, (compiledChecker_check_iff definition.1 goal certificate).mpr
      ⟨valid, out, checked, hypotheses, conclusion⟩⟩

/-- Faithful hosting through an executable claim interface to the actual
HOL Light kernel. -/
theorem derives_iff_compiled_graph (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern)
    (valid : argumentValidAt 0 goal = true) :
    Nonempty (InferenceChecker.Derivation definition goal) ↔
      ∃ certificate, (compiledChecker definition.1).check goal certificate = true := by
  have exactness := (compiledChecker_authority definition firstOrder).meaning_iff_exists_certificate goal
  simpa only [valid, true_and] using exactness

/-- A noncanonical source claim is refused before target replay. -/
theorem compiledChecker_invalid_claim (definition : CalculusLanguageDef)
    (goal : Pattern) (certificate : ProofSystem.Certificate)
    (invalid : argumentValidAt 0 goal = false) :
    (compiledChecker definition).check goal certificate = false := by
  simp [compiledChecker, invalid]

/-- One physical graph root cannot certify two different encoded claims.
Repeated source uses of that root retain their own occurrences, but do not
change the theorem stored there. -/
theorem compiledChecker_claim_unique (definition : CalculusLanguageDef)
    (first second : Pattern) (certificate : ProofSystem.Certificate)
    (acceptedFirst : (compiledChecker definition).check first certificate = true)
    (acceptedSecond : (compiledChecker definition).check second certificate = true) :
    compileClaim first = compileClaim second := by
  obtain ⟨_, firstOut, firstChecked, _, firstConcluded⟩ :=
    (compiledChecker_check_iff definition first certificate).mp acceptedFirst
  obtain ⟨_, secondOut, secondChecked, _, secondConcluded⟩ :=
    (compiledChecker_check_iff definition second certificate).mp acceptedSecond
  obtain ⟨firstCache, firstReplay, firstRoot⟩ :=
    (ProofSystem.checker_check_iff _ _ _).mp firstChecked
  obtain ⟨secondCache, secondReplay, secondRoot⟩ :=
    (ProofSystem.checker_check_iff _ _ _).mp secondChecked
  have caches : firstCache = secondCache := Option.some.inj (firstReplay.symm.trans secondReplay)
  subst secondCache
  have outputs : firstOut = secondOut := Option.some.inj (firstRoot.symm.trans secondRoot)
  simpa only [← firstConcluded, ← secondConcluded] using
    congrArg (fun out : Theorem => out.sequent.concl) outputs

/-- A graph accepted for one encoded claim refuses a different encoded claim,
even if that second claim has an independent proof in the source theory. -/
theorem compiledChecker_wrong_claim (definition : CalculusLanguageDef)
    (first second : Pattern) (certificate : ProofSystem.Certificate)
    (accepted : (compiledChecker definition).check first certificate = true)
    (different : compileClaim first ≠ compileClaim second) :
    (compiledChecker definition).check second certificate = false := by
  apply Bool.eq_false_iff.mpr
  intro another
  exact different (compiledChecker_claim_unique definition first second certificate accepted another)

/-- An ordered source context is represented by checked physical roots. -/
def Represents (state : ProofExecution.State) (goals : List Pattern) (roots : List Nat) : Prop :=
  List.Forall₂ (fun goal root => ∃ out, state.cache[root]? = some out ∧ hasClaim goal out = true) goals roots

theorem Represents.kept {before after : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (represented : Represents before goals roots) (kept : KeepsOld before after) : Represents after goals roots :=
  represented.imp (fun _ _ ⟨out, found, valid⟩ => ⟨out, kept _ _ found, valid⟩)

/-- The builder's actual replay supplies the finite-theory dependency bound
for each selected earlier source claim. -/
theorem builder_claim_storage (definition : CalculusLanguageDef) (goal : Pattern)
    {state : ProofExecution.State} {index : Nat} {out : Theorem}
    (earlier : GraphExpansion.BuildChecked (policy (inferenceRules definition)) [] state)
    (found : state.cache[index]? = some out) (claim : hasClaim goal out = true) :
    OpenTheory.StorageSize.theoremData out ≤
      InferenceStorageBounds.theoryPayload (inferenceRules definition) + 3 +
        184 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight goal := by
  have accepted : (ProofSystem.checker (policy (inferenceRules definition))).check out
      (state.receipts.toList, index) = true :=
    (ProofSystem.checker_check_iff _ _ _).mpr ⟨state.cache, earlier, found⟩
  have shape : out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
    simpa only [hasClaim, decide_eq_true_eq] using claim
  exact graph_theorem_storage definition goal accepted shape.1 shape.2

/-- The actual ordered lookup vector pays for every copied premise theorem,
including repeated uses of one physical root. -/
theorem represented_inputs_storage (definition : CalculusLanguageDef)
    {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (earlier : GraphExpansion.BuildChecked (policy (inferenceRules definition)) [] state)
    (represented : Represents state goals roots) {inputs : List Theorem}
    (selected : DerivationGraph.lookupPremises state.cache roots = some inputs) :
    OpenTheory.StorageSize.list OpenTheory.StorageSize.theoremData inputs ≤
      inputs.length * (InferenceStorageBounds.theoryPayload (inferenceRules definition) + 3) +
        184 * Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight goals := by
  induction represented generalizing inputs with
  | nil =>
      have empty : inputs = [] := Option.some.inj selected.symm
      subst inputs
      simp [OpenTheory.StorageSize.list, Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight]
  | @cons goal root goals roots current related ih =>
      obtain ⟨out, found, valid⟩ := current
      cases tailSelected : DerivationGraph.lookupPremises state.cache roots with
      | none => simp [DerivationGraph.lookupPremises, found, tailSelected] at selected
      | some tailInputs =>
          have same : out :: tailInputs = inputs := by
            simpa [DerivationGraph.lookupPremises, found, tailSelected] using selected
          subst inputs
          have head := builder_claim_storage definition goal earlier found valid
          have tail := ih tailSelected
          simp only [OpenTheory.StorageSize.list_cons, List.length_cons,
            Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight]
          nlinarith

/-- A source-context occurrence selects its corresponding checked HOL root. -/
theorem represented_lookup {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (represented : Represents state goals roots) {index : Nat} {goal : Pattern}
    (found : goals[index]? = some goal) :
    ∃ root out, roots[index]? = some root ∧ state.cache[root]? = some out ∧ hasClaim goal out = true := by
  induction represented generalizing index with
  | nil => simp at found
  | @cons head root goals roots headRelated _ ih =>
      cases index with
      | zero =>
          have same : head = goal := Option.some.inj found
          subst head
          obtain ⟨out, stored, valid⟩ := headRelated
          exact ⟨root, out, rfl, stored, valid⟩
      | succ index => exact ih found

private theorem represented_inputs {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (represented : Represents state goals roots) :
    ∃ inputs, DerivationGraph.lookupPremises state.cache roots = some inputs ∧
      List.Forall₂ (fun goal out => hasClaim goal out = true) goals inputs := by
  induction represented with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons goal root goals roots headRelated _ ih =>
      obtain ⟨out, found, valid⟩ := headRelated
      obtain ⟨inputs, selected, correct⟩ := ih
      exact ⟨out :: inputs, by simp [DerivationGraph.lookupPremises, found, selected], .cons valid correct⟩

/-- A local emitter realizes the original instantiated rule by a concrete
checked block. The driver below composes such blocks; a concrete backend must
earn this property for its actual emitter. -/
def RuleEmitter.Realizes (definition : ValidatedCalculusLanguageDef) (emitRule : RuleEmitter) : Prop :=
  ∀ (ruleInstance : RuleInstance) (premises : List Pattern) (conclusion : Pattern) (inputs : List Theorem)
    (origin : ProofExecution.Origin),
    instantiateRule? definition ruleInstance = some (premises, conclusion) →
    List.Forall₂ (fun goal out => hasClaim goal out = true) premises inputs →
    ∃ block out, emitRule ruleInstance inputs origin = some block ∧
      GraphExpansion.BlockChecked (policy (inferenceRules definition.1)) inputs out block ∧
      hasClaim conclusion out = true

mutual
  /-- Traverse one original open certificate. Premise holes select retained
  physical roots; they never unfold a previously compiled proof. -/
  def compileOpenWith (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin) :
      Pattern → RawOpenProof → ProofExecution.State → Option (ProofExecution.State × Nat)
    | goal, .premise index, state => do
        let root ← context[index]?
        let out ← state.cache[root]?
        if hasClaim goal out then pure (state, root) else none
    | goal, .node ruleInstance children, state => do
        let (premises, conclusion) ← instantiateRule? definition ruleInstance
        if conclusion = goal then do
          let (middle, roots) ← compileChildrenWith definition emitRule context origin
            premises children state
          let inputs ← DerivationGraph.lookupPremises middle.cache roots
          let block ← emitRule ruleInstance inputs origin
          let (result, root) ← GraphExpansion.emitBlock (policy (inferenceRules definition.1))
            roots block middle
          let out ← result.cache[root]?
          if hasClaim goal out then pure (result, root) else none
        else none
  termination_by _ proof _ => sizeOf proof

  /-- Children are emitted in their original premise order. Repeated references
  remain repeated entries in the root vector. A mismatched child count refuses. -/
  def compileChildrenWith (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin) :
      List Pattern → List RawOpenProof → ProofExecution.State →
        Option (ProofExecution.State × List Nat)
    | [], [], state => some (state, [])
    | goal :: goals, proof :: proofs, state => do
        let (middle, root) ← compileOpenWith definition emitRule context origin goal proof state
        let (result, roots) ← compileChildrenWith definition emitRule context origin goals proofs middle
        pure (result, root :: roots)
    | _, _, _ => none
  termination_by _ proofs _ => sizeOf proofs
end

mutual
  /-- A successful traversal retains the checked prefix and returns an actual
  stored theorem for the requested sequent. Even an untrusted local emitter
  cannot bypass the existing primitive replay. -/
  theorem compileOpenWith_safe (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
      (external : List Theorem) :
      ∀ (goal : Pattern) (proof : RawOpenProof) (state result : ProofExecution.State) (root : Nat),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
        compileOpenWith definition emitRule context origin goal proof state = some (result, root) →
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧
          KeepsOld state result ∧ ∃ out, result.cache[root]? = some out ∧ hasClaim goal out = true
    | goal, .premise index, state, result, root, earlier, accepted => by
        cases selected : context[index]? with
        | none => simp [compileOpenWith, selected] at accepted
        | some selectedRoot =>
            cases found : state.cache[selectedRoot]? with
            | none => simp [compileOpenWith, selected, found] at accepted
            | some out =>
                cases valid : hasClaim goal out with
                | false => simp [compileOpenWith, selected, found, valid] at accepted
                | true =>
                    have same : (state, selectedRoot) = (result, root) := by
                      simpa [compileOpenWith, selected, found, valid] using accepted
                    cases same
                    exact ⟨earlier, KeepsOld.refl state, out, found, valid⟩
    | goal, .node ruleInstance children, state, result, root, earlier, accepted => by
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [compileOpenWith, instantiated] at accepted
        | some pair =>
            obtain ⟨premises, conclusion⟩ := pair
            by_cases sameGoal : conclusion = goal
            · cases childrenEmitted : compileChildrenWith definition emitRule context origin
                  premises children state with
              | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted] at accepted
              | some middlePair =>
                  obtain ⟨middle, roots⟩ := middlePair
                  obtain ⟨middleChecked, keptFirst⟩ := compileChildrenWith_safe definition emitRule
                    context origin external premises children state middle roots earlier childrenEmitted
                  cases selected : DerivationGraph.lookupPremises middle.cache roots with
                  | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected] at accepted
                  | some inputs =>
                      cases emitted : emitRule ruleInstance inputs origin with
                      | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, emitted] at accepted
                      | some block =>
                          cases extended : GraphExpansion.emitBlock (policy (inferenceRules definition.1))
                              roots block middle with
                          | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected,
                              emitted, extended] at accepted
                          | some lastPair =>
                              obtain ⟨last, lastRoot⟩ := lastPair
                              obtain ⟨lastChecked, keptLast, _⟩ := emittedBlock_safe middleChecked extended
                              cases found : last.cache[lastRoot]? with
                              | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected,
                                  emitted, extended, found] at accepted
                              | some out =>
                                  cases valid : hasClaim goal out with
                                  | false => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                                      selected, emitted, extended, found, valid] at accepted
                                  | true =>
                                      have same : (last, lastRoot) = (result, root) := by
                                        simpa [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                                          selected, emitted, extended, found, valid] using accepted
                                      cases same
                                      exact ⟨lastChecked, keptFirst.trans keptLast, out, found, valid⟩
            · simp [compileOpenWith, instantiated, sameGoal] at accepted
  termination_by _ proof _ _ _ _ _ => sizeOf proof

  /-- Ordered child traversal preserves all previously stored proofs while
  emitting only nodes checked by the original HOL replay. -/
  theorem compileChildrenWith_safe (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
      (external : List Theorem) :
      ∀ (goals : List Pattern) (proofs : List RawOpenProof) (state result : ProofExecution.State)
        (roots : List Nat),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
        compileChildrenWith definition emitRule context origin goals proofs state = some (result, roots) →
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧ KeepsOld state result
    | [], [], state, result, roots, earlier, accepted => by
        have same : (state, []) = (result, roots) := by
          simpa only [compileChildrenWith, Option.some.injEq] using accepted
        cases same
        exact ⟨earlier, KeepsOld.refl state⟩
    | goal :: goals, proof :: proofs, state, result, roots, earlier, accepted => by
        cases emitted : compileOpenWith definition emitRule context origin goal proof state with
        | none => simp [compileChildrenWith, emitted] at accepted
        | some headPair =>
            obtain ⟨middle, root⟩ := headPair
            obtain ⟨middleChecked, keptFirst, _⟩ := compileOpenWith_safe definition emitRule context origin
              external goal proof state middle root earlier emitted
            cases rest : compileChildrenWith definition emitRule context origin goals proofs middle with
            | none => simp [compileChildrenWith, emitted, rest] at accepted
            | some tailPair =>
                obtain ⟨last, laterRoots⟩ := tailPair
                have same : (last, root :: laterRoots) = (result, roots) := by
                  simpa [compileChildrenWith, emitted, rest] using accepted
                obtain ⟨lastChecked, keptLast⟩ := compileChildrenWith_safe definition emitRule context origin
                  external goals proofs middle last laterRoots middleChecked rest
                cases same
                exact ⟨lastChecked, keptFirst.trans keptLast⟩
    | [], _ :: _, _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
    | _ :: _, [], _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
  termination_by _ proofs _ _ _ _ _ => sizeOf proofs
end

/-- Successful child traversal represents each requested premise at its final
physical address, independently of any assumptions on the local emitter. -/
theorem compileChildrenWith_represents (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
    (external : List Theorem) :
    ∀ (goals : List Pattern) (proofs : List RawOpenProof) (state result : ProofExecution.State)
      (roots : List Nat),
      GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
      compileChildrenWith definition emitRule context origin goals proofs state = some (result, roots) →
      Represents result goals roots
  | [], [], state, result, roots, _, accepted => by
      have same : (state, []) = (result, roots) := by
        simpa only [compileChildrenWith, Option.some.injEq] using accepted
      cases same
      exact .nil
  | goal :: goals, proof :: proofs, state, result, roots, earlier, accepted => by
      cases emitted : compileOpenWith definition emitRule context origin goal proof state with
      | none => simp [compileChildrenWith, emitted] at accepted
      | some headPair =>
          obtain ⟨middle, root⟩ := headPair
          obtain ⟨middleChecked, _, out, found, valid⟩ := compileOpenWith_safe definition emitRule
            context origin external goal proof state middle root earlier emitted
          cases rest : compileChildrenWith definition emitRule context origin goals proofs middle with
          | none => simp [compileChildrenWith, emitted, rest] at accepted
          | some tailPair =>
              obtain ⟨last, laterRoots⟩ := tailPair
              have same : (last, root :: laterRoots) = (result, roots) := by
                simpa [compileChildrenWith, emitted, rest] using accepted
              obtain ⟨_, keptLast⟩ := compileChildrenWith_safe definition emitRule context origin
                external goals proofs middle last laterRoots middleChecked rest
              have tail := compileChildrenWith_represents definition emitRule context origin
                external goals proofs middle last laterRoots middleChecked rest
              cases same
              exact .cons ⟨out, keptLast _ _ found, valid⟩ tail
  | [], _ :: _, _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
  | _ :: _, [], _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
termination_by _ proofs _ _ _ _ _ => sizeOf proofs

mutual
  /-- Every accepted original open proof is compiled when its actual local
  emitter realizes the admitted rule instances. The exact conclusion and all
  earlier addresses survive the traversal. -/
  theorem compileOpenWith_complete (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (realizes : emitRule.Realizes definition)
      (sourceContext : List Pattern) (context : List Nat) (origin : ProofExecution.Origin)
      (external : List Theorem) :
      ∀ (goal : Pattern) (proof : RawOpenProof) (state : ProofExecution.State),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
        Represents state sourceContext context →
        CertificateGSLT.checkOpenRaw definition sourceContext goal proof = true →
        ∃ result root, compileOpenWith definition emitRule context origin goal proof state = some (result, root) ∧
          GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧
          KeepsOld state result ∧ ∃ out, result.cache[root]? = some out ∧ hasClaim goal out = true
    | goal, .premise index, state, earlier, represented, accepted => by
        cases sourceFound : sourceContext[index]? with
        | none => simp [CertificateGSLT.checkOpenRaw, sourceFound] at accepted
        | some premise =>
            have same : premise = goal := by
              simpa [CertificateGSLT.checkOpenRaw, sourceFound] using accepted
            subst premise
            obtain ⟨root, out, selected, found, valid⟩ := represented_lookup represented sourceFound
            exact ⟨state, root, by simp [compileOpenWith, selected, found, valid], earlier,
              KeepsOld.refl state, out, found, valid⟩
    | goal, .node ruleInstance children, state, earlier, represented, accepted => by
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [CertificateGSLT.checkOpenRaw, instantiated] at accepted
        | some pair =>
            obtain ⟨premises, conclusion⟩ := pair
            simp only [CertificateGSLT.checkOpenRaw, instantiated, Bool.and_eq_true, decide_eq_true_eq] at accepted
            obtain ⟨sameGoal, childrenAccepted⟩ := accepted
            obtain ⟨middle, roots, childrenEmitted, middleChecked, keptFirst, inputsRepresented⟩ :=
              compileChildrenWith_complete definition emitRule realizes sourceContext context origin external
                premises children state earlier represented childrenAccepted
            obtain ⟨inputs, selected, inputsCorrect⟩ := represented_inputs inputsRepresented
            obtain ⟨block, out, generated, blockChecked, valid⟩ :=
              realizes ruleInstance premises conclusion inputs origin instantiated inputsCorrect
            obtain ⟨result, root, extended, resultChecked, found, _, keptLast⟩ :=
              GraphExpansion.emitBlock_checked middleChecked selected blockChecked
            have goalCorrect : hasClaim goal out = true := sameGoal ▸ valid
            refine ⟨result, root, ?_, resultChecked, keptFirst.trans keptLast, out, found, goalCorrect⟩
            simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected,
              generated, extended, found, goalCorrect]
  termination_by _ proof _ _ _ _ => sizeOf proof

  /-- The compiled child vector retains every premise occurrence in order,
  including repeated physical roots. -/
  theorem compileChildrenWith_complete (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (realizes : emitRule.Realizes definition)
      (sourceContext : List Pattern) (context : List Nat) (origin : ProofExecution.Origin)
      (external : List Theorem) :
      ∀ (goals : List Pattern) (proofs : List RawOpenProof) (state : ProofExecution.State),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
        Represents state sourceContext context →
        CertificateGSLT.checkOpenRawChildren definition sourceContext goals proofs = true →
        ∃ result roots, compileChildrenWith definition emitRule context origin goals proofs state = some (result, roots) ∧
          GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧
          KeepsOld state result ∧ Represents result goals roots
    | [], [], state, earlier, _, _ =>
        ⟨state, [], by simp [compileChildrenWith], earlier, KeepsOld.refl state, .nil⟩
    | goal :: goals, proof :: proofs, state, earlier, represented, accepted => by
        simp only [CertificateGSLT.checkOpenRawChildren, Bool.and_eq_true] at accepted
        obtain ⟨middle, root, emitted, middleChecked, keptFirst, out, found, valid⟩ :=
          compileOpenWith_complete definition emitRule realizes sourceContext context origin external
            goal proof state earlier represented accepted.1
        obtain ⟨result, roots, rested, resultChecked, keptLast, tailRepresented⟩ :=
          compileChildrenWith_complete definition emitRule realizes sourceContext context origin external
            goals proofs middle middleChecked (represented.kept keptFirst) accepted.2
        exact ⟨result, root :: roots, by simp [compileChildrenWith, emitted, rested], resultChecked,
          keptFirst.trans keptLast, .cons ⟨out, keptLast _ _ found, valid⟩ tailRepresented⟩
    | [], _ :: _, _, _, _, accepted => by simp [CertificateGSLT.checkOpenRawChildren] at accepted
    | _ :: _, [], _, _, _, accepted => by simp [CertificateGSLT.checkOpenRawChildren] at accepted
  termination_by _ proofs _ _ _ _ => sizeOf proofs
end

/-- Compile the existing chronological lemma carrier. Each lemma adds one root
to the environment; subsequent uses refer to that physical proof. -/
def compileLemmasWith (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) : Nat → List Nat → Lemmas → ProofExecution.State →
      Option (ProofExecution.State × List Nat)
  | _, context, [], state => some (state, context)
  | index, context, (goal, proof) :: rest, state => do
      let (middle, root) ← compileOpenWith definition emitRule context ("lemma", index) goal proof state
      compileLemmasWith definition emitRule (index + 1) (context ++ [root]) rest middle

/-- The lemma fold retains its checked history and every physical proof root
already stored before the fold began. -/
theorem compileLemmasWith_safe (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (external : List Theorem) :
    ∀ (lemmas : Lemmas) (index : Nat) (context : List Nat) (state result : ProofExecution.State)
      (roots : List Nat),
      GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
      compileLemmasWith definition emitRule index context lemmas state = some (result, roots) →
      GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧ KeepsOld state result
  | [], _, context, state, result, roots, earlier, accepted => by
      have same : (state, context) = (result, roots) := Option.some.inj accepted
      cases same
      exact ⟨earlier, KeepsOld.refl state⟩
  | (goal, proof) :: rest, index, context, state, result, roots, earlier, accepted => by
      cases emitted : compileOpenWith definition emitRule context ("lemma", index) goal proof state with
      | none => simp [compileLemmasWith, emitted] at accepted
      | some pair =>
          obtain ⟨middle, root⟩ := pair
          obtain ⟨middleChecked, keptFirst, _⟩ := compileOpenWith_safe definition emitRule context
            ("lemma", index) external goal proof state middle root earlier emitted
          have rested : compileLemmasWith definition emitRule (index + 1) (context ++ [root]) rest middle =
              some (result, roots) := by
            simpa [compileLemmasWith, emitted] using accepted
          obtain ⟨lastChecked, keptLast⟩ := compileLemmasWith_safe definition emitRule external rest
            (index + 1) (context ++ [root]) middle result roots middleChecked rested
          exact ⟨lastChecked, keptFirst.trans keptLast⟩

/-- Every accepted lemma history compiles while retaining an exact ordered
environment for the final open certificate. -/
theorem compileLemmasWith_complete (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (realizes : emitRule.Realizes definition) (external : List Theorem) :
    ∀ (lemmas : Lemmas) (index : Nat) (sourceContext : List Pattern) (context : List Nat)
      (state : ProofExecution.State),
      GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external state →
      Represents state sourceContext context →
      checkLemmas definition sourceContext lemmas = true →
      ∃ result roots, compileLemmasWith definition emitRule index context lemmas state = some (result, roots) ∧
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) external result ∧
        KeepsOld state result ∧ Represents result (sourceContext ++ lemmas.map Prod.fst) roots
  | [], _, sourceContext, context, state, earlier, represented, _ => by
      exact ⟨state, context, rfl, earlier, KeepsOld.refl state, by simpa using represented⟩
  | (goal, proof) :: rest, index, sourceContext, context, state, earlier, represented, accepted => by
      simp only [checkLemmas, Bool.and_eq_true] at accepted
      obtain ⟨middle, root, emitted, middleChecked, keptFirst, out, found, valid⟩ :=
        compileOpenWith_complete definition emitRule realizes sourceContext context ("lemma", index) external
          goal proof state earlier represented accepted.1
      have extended : Represents middle (sourceContext ++ [goal]) (context ++ [root]) :=
        List.rel_append (represented.kept keptFirst) (.cons ⟨out, found, valid⟩ .nil)
      obtain ⟨result, roots, rested, resultChecked, keptLast, finalRepresented⟩ :=
        compileLemmasWith_complete definition emitRule realizes external rest (index + 1)
          (sourceContext ++ [goal]) (context ++ [root]) middle middleChecked extended accepted.2
      refine ⟨result, roots, ?_, resultChecked, keptFirst.trans keptLast, ?_⟩
      · simp [compileLemmasWith, emitted, rested]
      · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using finalRepresented

/-- Start with the directly generated, checked finite theory prefix. -/
def initialState (definition : CalculusLanguageDef) : ProofExecution.State :=
  ⟨((axiomGraph definition).map (fun node => node.conclusion)).toArray,
    (axiomGraph definition).toArray⟩

theorem initialState_checked (definition : CalculusLanguageDef) :
    GraphExpansion.BuildChecked (policy (inferenceRules definition)) [] (initialState definition) := by
  obtain ⟨cache, checked, values⟩ := axiomGraph_checked definition
  have cacheSame : cache = ((axiomGraph definition).map (fun node => node.conclusion)).toArray := by
    rw [← values, Array.toArray_toList]
  simpa [GraphExpansion.BuildChecked, initialState, DerivationGraph.replay, cacheSame] using checked

/-- The public output is the existing HOL Light certificate representation.
This driver takes a concrete local emitter; completeness of a backend also
requires that emitter's checked realization of all source rule instances. -/
def compileSharedWith (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (goal : Pattern) (certificate : LemmaCertificate) :
    Option ProofSystem.Certificate := do
  let (middle, context) ← compileLemmasWith definition emitRule 0 [] certificate.1
    (initialState definition.1)
  let (result, root) ← compileOpenWith definition emitRule context ("root", 0) goal certificate.2 middle
  pure (GraphExpansion.finish result root)

/-- The actual traversal accepts every supplied source lemma certificate when
its concrete local emitter has earned realization of all original rules. -/
theorem compileSharedWith_preserves (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (realizes : emitRule.Realizes definition)
    (goal : Pattern) (source : LemmaCertificate)
    (lemmasAccepted : checkLemmas definition [] source.1 = true)
    (rootAccepted : CertificateGSLT.checkOpenRaw definition (source.1.map Prod.fst) goal source.2 = true) :
    ∃ certificate, compileSharedWith definition emitRule goal source = some certificate := by
  obtain ⟨middle, context, emitted, middleChecked, _, represented⟩ :=
    compileLemmasWith_complete definition emitRule realizes [] source.1 0 [] []
      (initialState definition.1) (initialState_checked definition.1) .nil lemmasAccepted
  have contextRepresented : Represents middle (source.1.map Prod.fst) context := by
    simpa using represented
  obtain ⟨result, root, finished, _⟩ := compileOpenWith_complete definition emitRule realizes
    (source.1.map Prod.fst) context ("root", 0) [] goal source.2 middle middleChecked contextRepresented rootAccepted
  exact ⟨GraphExpansion.finish result root, by simp [compileSharedWith, emitted, finished]⟩

/-- Successful compilation produces an accepted certificate for the exact
encoded source claim, including the original checked theory prefix. -/
theorem compileSharedWith_checked (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (goal : Pattern) (source : LemmaCertificate)
    {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    ∃ out, (ProofSystem.checker (policy (inferenceRules definition.1))).check out certificate = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
  cases emitted : compileLemmasWith definition emitRule 0 [] source.1 (initialState definition.1) with
  | none => simp [compileSharedWith, emitted] at compiled
  | some pair =>
      obtain ⟨middle, context⟩ := pair
      obtain ⟨middleChecked, _⟩ := compileLemmasWith_safe definition emitRule [] source.1 0 []
        (initialState definition.1) middle context (initialState_checked definition.1) emitted
      cases finished : compileOpenWith definition emitRule context ("root", 0) goal source.2 middle with
      | none => simp [compileSharedWith, emitted, finished] at compiled
      | some lastPair =>
          obtain ⟨result, root⟩ := lastPair
          obtain ⟨checked, _, out, found, valid⟩ := compileOpenWith_safe definition emitRule context
            ("root", 0) [] goal source.2 middle result root middleChecked finished
          have same : GraphExpansion.finish result root = certificate := by
            simpa [compileSharedWith, emitted, finished] using compiled
          subst certificate
          refine ⟨out, (ProofSystem.checker_check_iff _ _ _).mpr ⟨result.cache, checked, found⟩, ?_⟩
          exact of_decide_eq_true valid

/-- Actual successful target replay cannot invent a canonical source judgment,
regardless of the local emitter supplied to the traversal. -/
theorem compileSharedWith_reflects (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (emitRule : RuleEmitter)
    (goal : Pattern) (source : LemmaCertificate) (valid : argumentValidAt 0 goal = true)
    {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    ∃ proof, checkRaw definition goal proof = true := by
  obtain ⟨out, checked, hypotheses, conclusion⟩ := compileSharedWith_checked definition emitRule goal source compiled
  exact (graph_checked_iff definition firstOrder valid).mpr ⟨out, certificate, checked, hypotheses, conclusion⟩

/-- An unavailable source premise is refused before any local emitter runs. -/
theorem compileOpenWith_missing_premise (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
    (goal : Pattern) (state : ProofExecution.State) (index : Nat)
    (missing : context[index]? = none) :
    compileOpenWith definition emitRule context origin goal (.premise index) state = none := by
  simp [compileOpenWith, missing]

/-- An admitted saved-premise use returns the original physical root and the
unchanged builder. Its proof is neither copied nor expanded. -/
theorem compileOpenWith_saved_premise (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
    (goal : Pattern) (state : ProofExecution.State) (index root : Nat) (out : Theorem)
    (selected : context[index]? = some root) (stored : state.cache[root]? = some out)
    (valid : hasClaim goal out = true) :
    compileOpenWith definition emitRule context origin goal (.premise index) state = some (state, root) := by
  simp [compileOpenWith, selected, stored, valid]

/-- Repeating the same saved premise retains its two physical occurrences in
the parent's ordered root vector, without duplicating the saved proof. -/
theorem compileChildrenWith_repeated_premise (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
    (goal : Pattern) (state : ProofExecution.State) (index root : Nat) (out : Theorem)
    (selected : context[index]? = some root) (stored : state.cache[root]? = some out)
    (valid : hasClaim goal out = true) :
    compileChildrenWith definition emitRule context origin [goal, goal]
      [.premise index, .premise index] state = some (state, [root, root]) := by
  have found := compileOpenWith_saved_premise definition emitRule context origin
    goal state index root out selected stored valid
  simp [compileChildrenWith, found]

/-- A missing child cannot be replaced by a target block, even if the emitter
could independently construct a proof of the requested conclusion. -/
theorem compileChildrenWith_missing_child (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (context : List Nat) (origin : ProofExecution.Origin)
    (goal : Pattern) (goals : List Pattern) (state : ProofExecution.State) :
    compileChildrenWith definition emitRule context origin (goal :: goals) [] state = none := by
  simp [compileChildrenWith]

/-- A local emitter's bound counts the physical receipts it actually returns.
It places no independent clock on the translation. -/
def RuleEmitter.NodeBound (emitRule : RuleEmitter) (budget : RuleInstance → Nat) : Prop :=
  ∀ ruleInstance inputs origin block, emitRule ruleInstance inputs origin = some block →
    block.1.length ≤ budget ruleInstance

mutual
  /-- Saved premise references emit no new proof nodes. Each source application
  contributes its local expansion and the expansions of its authored children. -/
  def openNodeBudget (budget : RuleInstance → Nat) : RawOpenProof → Nat
    | .premise _ => 0
    | .node ruleInstance children => budget ruleInstance + childrenNodeBudget budget children

  def childrenNodeBudget (budget : RuleInstance → Nat) : List RawOpenProof → Nat
    | [] => 0
    | proof :: rest => openNodeBudget budget proof + childrenNodeBudget budget rest
end

mutual
  /-- The actual open-proof traversal adds at most its local expansion budgets.
  Sharing is measured before any hypothetical unfolding into proof trees. -/
  theorem compileOpenWith_nodes (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (budget : RuleInstance → Nat)
      (bounded : emitRule.NodeBound budget) (context : List Nat) (origin : ProofExecution.Origin) :
      ∀ (goal : Pattern) (proof : RawOpenProof) (state result : ProofExecution.State) (root : Nat),
        compileOpenWith definition emitRule context origin goal proof state = some (result, root) →
          result.receipts.size ≤ state.receipts.size + openNodeBudget budget proof
    | goal, .premise index, state, result, root, accepted => by
        cases selected : context[index]? with
        | none => simp [compileOpenWith, selected] at accepted
        | some selectedRoot =>
            cases found : state.cache[selectedRoot]? with
            | none => simp [compileOpenWith, selected, found] at accepted
            | some out =>
                cases valid : hasClaim goal out with
                | false => simp [compileOpenWith, selected, found, valid] at accepted
                | true =>
                    have same : (state, selectedRoot) = (result, root) := by
                      simpa [compileOpenWith, selected, found, valid] using accepted
                    cases same
                    simp [openNodeBudget]
    | goal, .node ruleInstance children, state, result, root, accepted => by
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [compileOpenWith, instantiated] at accepted
        | some pair =>
            obtain ⟨premises, conclusion⟩ := pair
            by_cases sameGoal : conclusion = goal
            · cases childrenEmitted : compileChildrenWith definition emitRule context origin
                  premises children state with
              | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted] at accepted
              | some middlePair =>
                  obtain ⟨middle, roots⟩ := middlePair
                  have earlier := compileChildrenWith_nodes definition emitRule budget bounded
                    context origin premises children state middle roots childrenEmitted
                  cases selected : DerivationGraph.lookupPremises middle.cache roots with
                  | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected] at accepted
                  | some inputs =>
                      cases emitted : emitRule ruleInstance inputs origin with
                      | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, emitted] at accepted
                      | some block =>
                          have localBound := bounded ruleInstance inputs origin block emitted
                          cases extended : GraphExpansion.emitBlock (policy (inferenceRules definition.1))
                              roots block middle with
                          | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                              selected, emitted, extended] at accepted
                          | some lastPair =>
                              obtain ⟨last, lastRoot⟩ := lastPair
                              have counted := (GraphExpansion.emitBlock_size extended).2
                              cases found : last.cache[lastRoot]? with
                              | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                                  selected, emitted, extended, found] at accepted
                              | some out =>
                                  cases valid : hasClaim goal out with
                                  | false => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                                      selected, emitted, extended, found, valid] at accepted
                                  | true =>
                                      have same : (last, lastRoot) = (result, root) := by
                                        simpa [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                                          selected, emitted, extended, found, valid] using accepted
                                      cases same
                                      simp only [openNodeBudget]
                                      omega
            · simp [compileOpenWith, instantiated, sameGoal] at accepted
  termination_by _ proof _ _ _ _ => sizeOf proof

  /-- Ordered child traversal sums emitted proof-node budgets; repeated saved
  roots do not cause their defining proofs to be emitted again. -/
  theorem compileChildrenWith_nodes (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (budget : RuleInstance → Nat)
      (bounded : emitRule.NodeBound budget) (context : List Nat) (origin : ProofExecution.Origin) :
      ∀ (goals : List Pattern) (proofs : List RawOpenProof) (state result : ProofExecution.State)
        (roots : List Nat),
        compileChildrenWith definition emitRule context origin goals proofs state = some (result, roots) →
          result.receipts.size ≤ state.receipts.size + childrenNodeBudget budget proofs
    | [], [], state, result, roots, accepted => by
        have same : (state, []) = (result, roots) := by
          simpa only [compileChildrenWith, Option.some.injEq] using accepted
        cases same
        simp [childrenNodeBudget]
    | goal :: goals, proof :: proofs, state, result, roots, accepted => by
        cases emitted : compileOpenWith definition emitRule context origin goal proof state with
        | none => simp [compileChildrenWith, emitted] at accepted
        | some headPair =>
            obtain ⟨middle, root⟩ := headPair
            have earlier := compileOpenWith_nodes definition emitRule budget bounded context origin
              goal proof state middle root emitted
            cases rested : compileChildrenWith definition emitRule context origin goals proofs middle with
            | none => simp [compileChildrenWith, emitted, rested] at accepted
            | some tailPair =>
                obtain ⟨last, lastRoots⟩ := tailPair
                have later := compileChildrenWith_nodes definition emitRule budget bounded context origin
                  goals proofs middle last lastRoots rested
                have same : (last, root :: lastRoots) = (result, roots) := by
                  simpa [compileChildrenWith, emitted, rested] using accepted
                cases same
                simp only [childrenNodeBudget]
                omega
    | [], _ :: _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
    | _ :: _, [], _, _, _, accepted => by simp [compileChildrenWith] at accepted
  termination_by _ proofs _ _ _ _ => sizeOf proofs
end

/-- Physical expansion budget for a chronological source lemma history. -/
def lemmasNodeBudget (budget : RuleInstance → Nat) : Lemmas → Nat
  | [] => 0
  | (_, proof) :: rest => openNodeBudget budget proof + lemmasNodeBudget budget rest

theorem compileLemmasWith_nodes (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (budget : RuleInstance → Nat) (bounded : emitRule.NodeBound budget) :
    ∀ (lemmas : Lemmas) (index : Nat) (context : List Nat) (state result : ProofExecution.State)
      (roots : List Nat),
      compileLemmasWith definition emitRule index context lemmas state = some (result, roots) →
        result.receipts.size ≤ state.receipts.size + lemmasNodeBudget budget lemmas
  | [], _, context, state, result, roots, accepted => by
      have same : (state, context) = (result, roots) := Option.some.inj accepted
      cases same
      simp [lemmasNodeBudget]
  | (goal, proof) :: rest, index, context, state, result, roots, accepted => by
      cases emitted : compileOpenWith definition emitRule context ("lemma", index) goal proof state with
      | none => simp [compileLemmasWith, emitted] at accepted
      | some pair =>
          obtain ⟨middle, root⟩ := pair
          have earlier := compileOpenWith_nodes definition emitRule budget bounded context ("lemma", index)
            goal proof state middle root emitted
          have rested : compileLemmasWith definition emitRule (index + 1) (context ++ [root]) rest middle =
              some (result, roots) := by
            simpa [compileLemmasWith, emitted] using accepted
          have later := compileLemmasWith_nodes definition emitRule budget bounded rest (index + 1)
            (context ++ [root]) middle result roots rested
          simp only [lemmasNodeBudget]
          omega

/-- A complete emitted graph consists of the finite theory prefix and the
local expansions of its original shared source certificate. -/
theorem compileSharedWith_nodes (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (budget : RuleInstance → Nat) (bounded : emitRule.NodeBound budget)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    certificate.1.length ≤ definition.1.rules.length +
      lemmasNodeBudget budget source.1 + openNodeBudget budget source.2 := by
  cases emitted : compileLemmasWith definition emitRule 0 [] source.1 (initialState definition.1) with
  | none => simp [compileSharedWith, emitted] at compiled
  | some pair =>
      obtain ⟨middle, context⟩ := pair
      have earlier := compileLemmasWith_nodes definition emitRule budget bounded source.1 0 []
        (initialState definition.1) middle context emitted
      cases finished : compileOpenWith definition emitRule context ("root", 0) goal source.2 middle with
      | none => simp [compileSharedWith, emitted, finished] at compiled
      | some lastPair =>
          obtain ⟨result, root⟩ := lastPair
          have later := compileOpenWith_nodes definition emitRule budget bounded context ("root", 0)
            goal source.2 middle result root finished
          have same : GraphExpansion.finish result root = certificate := by
            simpa [compileSharedWith, emitted, finished] using compiled
          subst certificate
          have initial : (initialState definition.1).receipts.size = definition.1.rules.length := by
            simp [initialState, axiomGraph_length]
          simpa only [GraphExpansion.finish, Array.length_toList] using
            (show result.receipts.size ≤ definition.1.rules.length +
              lemmasNodeBudget budget source.1 + openNodeBudget budget source.2 by omega)

mutual
  /-- For a fixed finite calculus, a uniform local expansion bound gives a
  linear physical-node bound in the existing source-certificate weight. -/
  theorem openNodeBudget_constant (factor : Nat) (proof : RawOpenProof) :
      openNodeBudget (fun _ => factor) proof ≤ factor * openWeight proof := by
    cases proof with
    | premise _ => simp [openNodeBudget, openWeight]
    | node ruleInstance children =>
        have later := childrenNodeBudget_constant factor children
        simp only [openNodeBudget, openWeight]
        nlinarith

  theorem childrenNodeBudget_constant (factor : Nat) (proofs : List RawOpenProof) :
      childrenNodeBudget (fun _ => factor) proofs ≤ factor * openWeights proofs := by
    cases proofs with
    | nil => simp [childrenNodeBudget, openWeights]
    | cons proof rest =>
        have first := openNodeBudget_constant factor proof
        have later := childrenNodeBudget_constant factor rest
        simp only [childrenNodeBudget, openWeights]
        nlinarith
end

theorem lemmasNodeBudget_constant (factor : Nat) (lemmas : Lemmas) :
    lemmasNodeBudget (fun _ => factor) lemmas ≤ factor * lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [lemmasNodeBudget, lemmasWeight]
  | cons item rest ih =>
      obtain ⟨goal, proof⟩ := item
      have first := openNodeBudget_constant factor proof
      simp only [lemmasNodeBudget, lemmasWeight]
      nlinarith

/-- Linear node growth applies to the original certificate with chronological
lemmas, rather than its potentially exponential tree unfolding. -/
theorem compileSharedWith_linear_nodes (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (factor : Nat) (bounded : emitRule.NodeBound (fun _ => factor))
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    certificate.1.length ≤ definition.1.rules.length +
      factor * (lemmasWeight source.1 + openWeight source.2) := by
  have emitted := compileSharedWith_nodes definition emitRule _ bounded goal source compiled
  have earlier := lemmasNodeBudget_constant factor source.1
  have later := openNodeBudget_constant factor source.2
  nlinarith

/-! ## The concrete backend -/

/-- The executable local emitter earns the generic driver's realization law
for every admitted first-order rule, without a supplied correctness callback. -/
theorem ruleEmitter_realizes (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    RuleEmitter.Realizes definition (InferenceRuleExpansion.emitRule? definition) := by
  intro ruleInstance premises conclusion inputs origin admitted related
  have related' : List.Forall₂ (fun goal input =>
      input.sequent.hyp = ∅ ∧ input.sequent.concl = render (judgment goal)) premises inputs :=
    related.imp (fun _ _ receipt => of_decide_eq_true receipt)
  obtain ⟨_, block, out, _, computed, replayed, _, hypotheses, concluded⟩ :=
    InferenceRuleExpansion.emitRule?_checked firstOrder ruleInstance premises conclusion
      inputs origin admitted related'
  exact ⟨block, out, computed, replayed, by simp [hasClaim, compileClaim, hypotheses, concluded]⟩

/-- A finite theory determines a uniform physical expansion bound. It charges
the actual eighteen-node SPEC and fifty-eight-node MP expansions. -/
def localNodeFactor (definition : CalculusLanguageDef) : Nat :=
  1 + (definition.rules.map fun rule =>
    18 * rule.metavariables.length + 58 * rule.premises.length).sum

theorem ruleEmitter_nodeBound (definition : ValidatedCalculusLanguageDef) :
    RuleEmitter.NodeBound (InferenceRuleExpansion.emitRule? definition)
      (fun _ => localNodeFactor definition.1) := by
  intro ruleInstance inputs origin block computed
  change block.1.length ≤ localNodeFactor definition.1
  obtain ⟨premises, conclusion, admitted, inputsCount⟩ :=
    InferenceRuleExpansion.emitRule?_premise_count computed
  have application := instantiateRule?_eq_some_iff_application.mp admitted
  cases application with
  | intro rule found valid _side instantiated _concluded =>
      have argumentsCount := argumentsValidAt_length valid
      have premisesCount := instantiated.length_eq
      have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some found
      have stored : 18 * rule.metavariables.length + 58 * rule.premises.length ∈
          definition.1.rules.map (fun candidate =>
            18 * candidate.metavariables.length + 58 * candidate.premises.length) :=
        List.mem_map.mpr ⟨rule, member, rfl⟩
      have bound := List.le_sum_of_mem stored
      rw [InferenceRuleExpansion.emitRule?_size computed]
      unfold localNodeFactor
      omega

/-- The original source admission check for a supplied chronological lemma
certificate. It validates the entire input, including unused lemma entries. -/
def sharedSourceCheck (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) : Bool :=
  checkLemmas definition [] source.1 &&
    CertificateGSLT.checkOpenRaw definition (source.1.map Prod.fst) goal source.2

/-- Compile an admitted original certificate into the existing HOL Light graph
representation. Source admission precedes concrete expansion; every emitted
target block is still replayed by the original HOL kernel. -/
def compileShared (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) : Option ProofSystem.Certificate :=
  if sharedSourceCheck definition goal source then
    compileSharedWith definition (InferenceRuleExpansion.emitRule? definition) goal source
  else none

/-- Every accepted source certificate computes an actual shared HOL graph.
This is a theorem about the concrete emitter and traversal, not existence of
an independently selected target proof. -/
theorem compileShared_preserves (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate)
    (accepted : sharedSourceCheck definition goal source = true) :
    ∃ certificate, compileShared definition goal source = some certificate := by
  have admitted : checkLemmas definition [] source.1 = true ∧
      CertificateGSLT.checkOpenRaw definition (source.1.map Prod.fst) goal source.2 = true := by
    simpa only [sharedSourceCheck, Bool.and_eq_true] using accepted
  obtain ⟨lemmasAccepted, rootAccepted⟩ := admitted
  obtain ⟨certificate, compiled⟩ := compileSharedWith_preserves definition
    (InferenceRuleExpansion.emitRule? definition) (ruleEmitter_realizes definition firstOrder)
    goal source lemmasAccepted rootAccepted
  exact ⟨certificate, by simp [compileShared, accepted, compiled]⟩

/-- Malformed source certificates refuse before any target expansion, even
when their claim has a different valid proof in the generated HOL theory. -/
theorem compileShared_refused (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate)
    (rejected : sharedSourceCheck definition goal source = false) :
    compileShared definition goal source = none := by
  simp [compileShared, rejected]

/-- The supplied source certificate, rather than merely its provable claim,
is admitted exactly when the concrete graph compiler returns a certificate. -/
theorem compileShared_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate) :
    sharedSourceCheck definition goal source = true ↔
      ∃ certificate, compileShared definition goal source = some certificate := by
  constructor
  · exact compileShared_preserves definition firstOrder goal source
  · rintro ⟨certificate, compiled⟩
    cases admitted : sharedSourceCheck definition goal source with
    | false => simp [compileShared, admitted] at compiled
    | true => rfl

private theorem compileShared_to_driver (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    compileSharedWith definition (InferenceRuleExpansion.emitRule? definition) goal source =
      some certificate := by
  cases admitted : sharedSourceCheck definition goal source with
  | false => simp [compileShared, admitted] at compiled
  | true => simpa [compileShared, admitted] using compiled

/-- Successful concrete compilation is checked by the original target kernel
and produces exactly the encoded claim without residual hypotheses. -/
theorem compileShared_checked (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    ∃ out, (ProofSystem.checker (policy (inferenceRules definition.1))).check out certificate = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal :=
  compileSharedWith_checked definition (InferenceRuleExpansion.emitRule? definition) goal source
    (compileShared_to_driver definition goal source compiled)

/-- Concrete compiled graphs can be submitted through the independent
source-claim interface without reconstructing a theorem object at the caller. -/
theorem compileShared_claim_checked (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate)
    (valid : argumentValidAt 0 goal = true) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    (compiledChecker definition.1).check goal certificate = true := by
  obtain ⟨out, checked, hypotheses, conclusion⟩ := compileShared_checked definition goal source compiled
  exact (compiledChecker_check_iff definition.1 goal certificate).mpr
    ⟨valid, out, checked, hypotheses, conclusion⟩

/-- Reflection through the target's independent model remains valid for the
concrete compiler. It does not rely on the source-admission gate as a model. -/
theorem compileShared_reflects (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate)
    (validGoal : argumentValidAt 0 goal = true) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    ∃ proof, checkRaw definition goal proof = true :=
  compileSharedWith_reflects definition firstOrder (InferenceRuleExpansion.emitRule? definition)
    goal source validGoal (compileShared_to_driver definition goal source compiled)

/-- The concrete compiler has linear physical-node overhead for every fixed
finite source calculus and preserves chronological lemma sharing. This law
counts nodes; binary payload size and operational time are separate accounts. -/
theorem compileShared_linear_nodes (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    certificate.1.length ≤ definition.1.rules.length + localNodeFactor definition.1 *
      (lemmasWeight source.1 + openWeight source.2) :=
  compileSharedWith_linear_nodes definition (InferenceRuleExpansion.emitRule? definition)
    (localNodeFactor definition.1) (ruleEmitter_nodeBound definition) goal source
    (compileShared_to_driver definition goal source compiled)

mutual
  /-- The actual local-node budget is dominated by the independent source
  packet measure, which charges UTF-8 names and binary premise references. -/
  theorem openNodeBudget_bit_weight (factor : Nat) (proof : RawOpenProof) :
      openNodeBudget (fun _ => factor) proof ≤ factor * CertificateDataEncoding.proofWeight proof := by
    cases proof with
    | premise _ => simp [openNodeBudget]
    | node ruleInstance children =>
        have rest := childrenNodeBudget_bit_weight factor children
        simp only [openNodeBudget, CertificateDataEncoding.proofWeight]
        nlinarith

  theorem childrenNodeBudget_bit_weight (factor : Nat) (proofs : List RawOpenProof) :
      childrenNodeBudget (fun _ => factor) proofs ≤ factor * CertificateDataEncoding.proofsWeight proofs := by
    cases proofs with
    | nil => simp [childrenNodeBudget, CertificateDataEncoding.proofsWeight]
    | cons proof rest =>
        have first := openNodeBudget_bit_weight factor proof
        have later := childrenNodeBudget_bit_weight factor rest
        simp only [childrenNodeBudget, CertificateDataEncoding.proofsWeight]
        nlinarith
end

theorem lemmasNodeBudget_bit_weight (factor : Nat) (lemmas : Lemmas) :
    lemmasNodeBudget (fun _ => factor) lemmas ≤ factor * CertificateDataEncoding.lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [lemmasNodeBudget, CertificateDataEncoding.lemmasWeight]
  | cons item rest ih =>
      obtain ⟨goal, proof⟩ := item
      have first := openNodeBudget_bit_weight factor proof
      simp only [lemmasNodeBudget, CertificateDataEncoding.lemmasWeight]
      nlinarith

/-- Physical-node growth is linear in a full-bit input account for every
fixed admitted finite calculus. This account includes the goal, every lemma,
UTF-8 names, complete pattern metadata, and binary numeric fields. Output
payload storage and execution time require their additional bounds. -/
theorem compileShared_bit_node_bound (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    certificate.1.length ≤ definition.1.rules.length + localNodeFactor definition.1 *
      CertificateDataEncoding.inputBitWeight goal source := by
  have count := compileSharedWith_nodes definition (InferenceRuleExpansion.emitRule? definition)
    (fun _ => localNodeFactor definition.1) (ruleEmitter_nodeBound definition) goal source
    (compileShared_to_driver definition goal source compiled)
  have earlier := lemmasNodeBudget_bit_weight (localNodeFactor definition.1) source.1
  have later := openNodeBudget_bit_weight (localNodeFactor definition.1) source.2
  have sumBound : CertificateDataEncoding.lemmasWeight source.1 +
      CertificateDataEncoding.proofWeight source.2 ≤ CertificateDataEncoding.inputBitWeight goal source := by
    simp only [CertificateDataEncoding.inputBitWeight, CertificateDataEncoding.inputWeight,
      CertificateDataEncoding.sharedWeight]
    omega
  have scaled := Nat.mul_le_mul_left (localNodeFactor definition.1) sumBound
  rw [Nat.mul_add] at scaled
  omega

/-- The actual finite-alphabet input length is bounded by its independent
full-bit account; numeric field magnitudes are never treated as bit lengths. -/
theorem inputEncoding_length_bound :
    ProofSystems.PolyBoundedBy
      (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding)
      (fun input : Pattern × LemmaCertificate => CertificateDataEncoding.inputBitWeight input.1 input.2) := by
  refine ⟨Polynomial.C 16 * Polynomial.X, ?_⟩
  intro input
  have encoded := CertificateDataEncoding.encodeInput_length input.1 input.2
  simp only [ProofSystems.encodedSize, CertificateDataEncoding.inputEncoding,
    CertificateDataEncoding.inputBitWeight, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

/-- The actual finite-alphabet input, rather than an unencoded occurrence
count, bounds the emitted physical graph for every fixed source calculus. -/
theorem compileShared_encoded_node_bound (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    certificate.1.length ≤ definition.1.rules.length + 8 * localNodeFactor definition.1 *
      ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) := by
  have nodes := compileShared_bit_node_bound definition goal source compiled
  have storage := CertificateDataEncoding.inputBitWeight_le_encoded goal source
  have scaled := Nat.mul_le_mul_left (localNodeFactor definition.1) storage
  have joined := nodes.trans (Nat.add_le_add_left scaled definition.1.rules.length)
  simpa only [ProofSystems.encodedSize, CertificateDataEncoding.inputEncoding,
    Nat.mul_left_comm, Nat.mul_assoc] using joined

/-- In an accepted actual HOL graph the complete physical address metadata,
including its selected root, is polynomial in the number of emitted nodes.
The full theorem/request/origin payload remains charged by `graphWeight`. -/
theorem checked_certificateUnits_bound {definition : CalculusLanguageDef}
    {out : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker (policy (inferenceRules definition))).check out certificate = true) :
    StorageSize.certificateUnits certificate ≤
      GraphExpansion.graphWeight StorageSize.receiptPayload certificate.1 +
        2 * certificate.1.length * certificate.1.length + certificate.1.length + 2 := by
  obtain ⟨cache, replayed, found⟩ := (ProofSystem.checker_check_iff _ _ _).mp accepted
  have count : cache.size = certificate.1.length := by
    have counted : cache.size = (#[] : Array Theorem).size + certificate.1.length :=
      DerivationGraph.replayFrom_size (ruleWitness (policy (inferenceRules definition)))
        (cache := #[]) (nodes := certificate.1) replayed
    simpa only [Array.size_empty, Nat.zero_add] using counted
  have rootInside := (Array.getElem?_eq_some_iff.mp found).1
  rw [count] at rootInside
  have addresses := GraphExpansion.checked_parentAddressBits_node_bound replayed
  have sizeBound : Nat.size certificate.1.length ≤ certificate.1.length :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have addressBound := addresses.trans (Nat.mul_le_mul_left (2 * certificate.1.length) sizeBound)
  have digits : (Nat.digits 2 certificate.2).length ≤ certificate.2 :=
    (Nat.digits_length_le_iff (by decide) _).mpr Nat.lt_two_pow_self
  simp only [StorageSize.certificateUnits, GraphExpansion.binaryGraphWeight,
    OpenTheory.StorageSize.nat]
  omega

/-- Address metadata of the concrete compiler is bounded by a quadratic in
its actual encoded input length. Every theorem, request and origin payload
is still counted independently and cannot be erased by this estimate. -/
theorem compileShared_encoded_address_bound (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    StorageSize.certificateUnits certificate ≤
      GraphExpansion.graphWeight StorageSize.receiptPayload certificate.1 +
        2 * (definition.1.rules.length + 8 * localNodeFactor definition.1 *
          ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) ^ 2 +
        (definition.1.rules.length + 8 * localNodeFactor definition.1 *
          ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) + 2 := by
  obtain ⟨out, accepted, _, _⟩ := compileShared_checked definition goal source compiled
  have addresses := checked_certificateUnits_bound accepted
  have nodes := compileShared_encoded_node_bound definition goal source compiled
  nlinarith

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
