import Mettapedia.Languages.HOLLight.InferenceCompiler
import Mettapedia.Languages.HOLLight.ProofDataEncoding
import Mettapedia.GSLT.LanguageDef.SharedReferenceExecution

/-!
# Full stored-output bounds for shared inference compilation

The account follows the actual chronological source traversal and original
kernel replay. Stored theorem/request/origin payloads and binary physical
addresses are both included. Source arguments, unused lemmas and large numeric
references retain their finite-alphabet input charge.

Each polynomial is for a fixed finite source calculus. Its coefficient and
degree may depend on the original rule family; no uniform polynomial over
arbitrary calculus declarations is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.InferenceCompilerSize

open Mettapedia.Logic
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (RawOpenProof)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Logic.HOL.Embedding.InferenceRules
open FirstOrder.InferenceTranslation InferenceCompiler GraphExpansion InferenceHosting

/-- A local payload estimate applies to actual ordered premise lookups from
an already checked source-claim prefix. It is a storage contract, not a new
certificate authority. Concrete compiler estimates below discharge it for
the computed primitive rule emitter. -/
def PayloadBound (definition : ValidatedCalculusLanguageDef) (emitRule : RuleEmitter)
    (budget : RuleInstance → ProofExecution.Origin → Nat) : Prop :=
  ∀ ruleInstance premises conclusion origin state roots inputs block,
    instantiateRule? definition ruleInstance = some (premises, conclusion) →
    BuildChecked (policy (inferenceRules definition.1)) [] state →
    Represents state premises roots →
    DerivationGraph.lookupPremises state.cache roots = some inputs →
    emitRule ruleInstance inputs origin = some block →
    graphWeight StorageSize.receiptPayload block.1 ≤ budget ruleInstance origin

mutual
  /-- The actual open-proof traversal adds at most its local payload budgets.
  Sharing is measured before any hypothetical unfolding into proof trees. -/
  theorem compileOpenWith_payload (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (budget : RuleInstance → ProofExecution.Origin → Nat)
      (bounded : PayloadBound definition emitRule budget) (context : List Nat) (origin : ProofExecution.Origin) :
      ∀ (goal : Pattern) (proof : RawOpenProof) (state result : ProofExecution.State) (root : Nat),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) [] state →
        compileOpenWith definition emitRule context origin goal proof state = some (result, root) →
          graphWeight StorageSize.receiptPayload result.receipts.toList ≤
            graphWeight StorageSize.receiptPayload state.receipts.toList +
              openNodeBudget (fun ruleInstance => budget ruleInstance origin) proof
    | goal, .premise index, state, result, root, checkedPrefix, accepted => by
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
    | goal, .node ruleInstance children, state, result, root, checkedPrefix, accepted => by
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
                  have earlier := compileChildrenWith_payload definition emitRule budget bounded
                    context origin premises children state middle roots checkedPrefix childrenEmitted
                  cases selected : DerivationGraph.lookupPremises middle.cache roots with
                  | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected] at accepted
                  | some inputs =>
                      cases emitted : emitRule ruleInstance inputs origin with
                      | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, emitted] at accepted
                      | some block =>
                          have middleChecked := (compileChildrenWith_safe definition emitRule context origin []
                            premises children state middle roots checkedPrefix childrenEmitted).1
                          have represented := compileChildrenWith_represents definition emitRule context origin []
                            premises children state middle roots checkedPrefix childrenEmitted
                          have localBound := bounded ruleInstance premises conclusion origin middle roots inputs block
                            instantiated middleChecked represented selected emitted
                          cases extended : GraphExpansion.emitBlock (policy (inferenceRules definition.1))
                              roots block middle with
                          | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted,
                              selected, emitted, extended] at accepted
                          | some lastPair =>
                              obtain ⟨last, lastRoot⟩ := lastPair
                              have counted := GraphExpansion.emitBlock_weight StorageSize.receiptPayload extended
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
  termination_by _ proof _ _ _ _ _ => sizeOf proof

  /-- Ordered child traversal sums emitted full payload budgets; repeated saved
  roots do not cause their defining proofs to be emitted again. -/
  theorem compileChildrenWith_payload (definition : ValidatedCalculusLanguageDef)
      (emitRule : RuleEmitter) (budget : RuleInstance → ProofExecution.Origin → Nat)
      (bounded : PayloadBound definition emitRule budget) (context : List Nat) (origin : ProofExecution.Origin) :
      ∀ (goals : List Pattern) (proofs : List RawOpenProof) (state result : ProofExecution.State)
        (roots : List Nat),
        GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) [] state →
        compileChildrenWith definition emitRule context origin goals proofs state = some (result, roots) →
          graphWeight StorageSize.receiptPayload result.receipts.toList ≤
            graphWeight StorageSize.receiptPayload state.receipts.toList +
              childrenNodeBudget (fun ruleInstance => budget ruleInstance origin) proofs
    | [], [], state, result, roots, checkedPrefix, accepted => by
        have same : (state, []) = (result, roots) := by
          simpa only [compileChildrenWith, Option.some.injEq] using accepted
        cases same
        simp [childrenNodeBudget]
    | goal :: goals, proof :: proofs, state, result, roots, checkedPrefix, accepted => by
        cases emitted : compileOpenWith definition emitRule context origin goal proof state with
        | none => simp [compileChildrenWith, emitted] at accepted
        | some headPair =>
            obtain ⟨middle, root⟩ := headPair
            have earlier := compileOpenWith_payload definition emitRule budget bounded context origin
              goal proof state middle root checkedPrefix emitted
            cases rested : compileChildrenWith definition emitRule context origin goals proofs middle with
            | none => simp [compileChildrenWith, emitted, rested] at accepted
            | some tailPair =>
                obtain ⟨last, lastRoots⟩ := tailPair
                have middleChecked := (compileOpenWith_safe definition emitRule context origin []
                  goal proof state middle root checkedPrefix emitted).1
                have later := compileChildrenWith_payload definition emitRule budget bounded context origin
                  goals proofs middle last lastRoots middleChecked rested
                have same : (last, root :: lastRoots) = (result, roots) := by
                  simpa [compileChildrenWith, emitted, rested] using accepted
                cases same
                simp only [childrenNodeBudget]
                omega
    | [], _ :: _, _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
    | _ :: _, [], _, _, _, _, accepted => by simp [compileChildrenWith] at accepted
  termination_by _ proofs _ _ _ _ _ => sizeOf proofs
end


/-- The original lemma history chooses its recorded chronological origin;
its storage account follows those exact indices. -/
def lemmasPayloadBudget (budget : RuleInstance → ProofExecution.Origin → Nat) : Nat → Lemmas → Nat
  | _, [] => 0
  | index, (_, proof) :: rest =>
      openNodeBudget (fun ruleInstance => budget ruleInstance ("lemma", index)) proof +
        lemmasPayloadBudget budget (index + 1) rest

/-- Successful chronological lemma compilation accumulates concrete local
payloads without unfolding saved proofs at later premise holes. -/
theorem compileLemmasWith_payload (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition emitRule budget) :
    ∀ (lemmas : Lemmas) (index : Nat) (context : List Nat) (state result : ProofExecution.State)
      (roots : List Nat),
      BuildChecked (policy (inferenceRules definition.1)) [] state →
      compileLemmasWith definition emitRule index context lemmas state = some (result, roots) →
        graphWeight StorageSize.receiptPayload result.receipts.toList ≤
          graphWeight StorageSize.receiptPayload state.receipts.toList + lemmasPayloadBudget budget index lemmas
  | [], _, context, state, result, roots, _, accepted => by
      have same : (state, context) = (result, roots) := Option.some.inj accepted
      cases same
      simp [lemmasPayloadBudget]
  | (goal, proof) :: rest, index, context, state, result, roots, checkedPrefix, accepted => by
      cases emitted : compileOpenWith definition emitRule context ("lemma", index) goal proof state with
      | none => simp [compileLemmasWith, emitted] at accepted
      | some pair =>
          obtain ⟨middle, root⟩ := pair
          have earlier := compileOpenWith_payload definition emitRule budget bounded context ("lemma", index)
            goal proof state middle root checkedPrefix emitted
          have middleChecked := (compileOpenWith_safe definition emitRule context ("lemma", index) []
            goal proof state middle root checkedPrefix emitted).1
          have rested : compileLemmasWith definition emitRule (index + 1) (context ++ [root]) rest middle =
              some (result, roots) := by
            simpa [compileLemmasWith, emitted] using accepted
          have later := compileLemmasWith_payload definition emitRule budget bounded rest (index + 1)
            (context ++ [root]) middle result roots middleChecked rested
          simp only [lemmasPayloadBudget]
          omega

/-- The complete computed shared graph consists of its finite axiom prefix,
chronological local lemma payloads and the final original open proof. -/
theorem compileSharedWith_payload (definition : ValidatedCalculusLanguageDef)
    (emitRule : RuleEmitter) (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition emitRule budget)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    graphWeight StorageSize.receiptPayload certificate.1 ≤
      graphWeight StorageSize.receiptPayload (axiomGraph definition.1) +
        lemmasPayloadBudget budget 0 source.1 +
          openNodeBudget (fun ruleInstance => budget ruleInstance ("root", 0)) source.2 := by
  cases emitted : compileLemmasWith definition emitRule 0 [] source.1 (initialState definition.1) with
  | none => simp [compileSharedWith, emitted] at compiled
  | some pair =>
      obtain ⟨middle, context⟩ := pair
      have earlier := compileLemmasWith_payload definition emitRule budget bounded source.1 0 []
        (initialState definition.1) middle context (initialState_checked definition.1) emitted
      have middleChecked := (compileLemmasWith_safe definition emitRule [] source.1 0 []
        (initialState definition.1) middle context (initialState_checked definition.1) emitted).1
      cases finished : compileOpenWith definition emitRule context ("root", 0) goal source.2 middle with
      | none => simp [compileSharedWith, emitted, finished] at compiled
      | some lastPair =>
          obtain ⟨result, root⟩ := lastPair
          have later := compileOpenWith_payload definition emitRule budget bounded context ("root", 0)
            goal source.2 middle result root middleChecked finished
          have same : finish result root = certificate := by
            simpa [compileSharedWith, emitted, finished] using compiled
          subst certificate
          change graphWeight StorageSize.receiptPayload result.receipts.toList ≤ _
          have initial : graphWeight StorageSize.receiptPayload (initialState definition.1).receipts.toList =
              graphWeight StorageSize.receiptPayload (axiomGraph definition.1) := by
            simp [initialState]
          rw [initial] at earlier
          omega


open Mettapedia.OSLF.MeTTaIL

mutual
  /-- A uniform local payload envelope sums over the original physical
  application occurrences, measured by the submitted certificate data. -/
  theorem openNodeBudget_source_weight (budget : RuleInstance → Nat) (limit envelope : Nat)
      (bounded : ∀ ruleInstance, PatternTokens.listWeight ruleInstance.arguments ≤ limit →
        budget ruleInstance ≤ envelope) :
      ∀ proof : RawOpenProof, CertificateDataEncoding.proofWeight proof ≤ limit →
        openNodeBudget budget proof ≤ envelope * CertificateDataEncoding.proofWeight proof
    | .premise index, _ => by simp [openNodeBudget]
    | .node ruleInstance children, admitted => by
        have argBound : PatternTokens.listWeight ruleInstance.arguments ≤ limit := by
          simp only [CertificateDataEncoding.proofWeight] at admitted
          omega
        have childrenBound : CertificateDataEncoding.proofsWeight children ≤ limit := by
          simp only [CertificateDataEncoding.proofWeight] at admitted
          omega
        have currentBound := bounded ruleInstance argBound
        have rest := childrenNodeBudget_source_weight budget limit envelope bounded children childrenBound
        simp only [openNodeBudget, CertificateDataEncoding.proofWeight]
        nlinarith
  termination_by proof _ => sizeOf proof

  theorem childrenNodeBudget_source_weight (budget : RuleInstance → Nat) (limit envelope : Nat)
      (bounded : ∀ ruleInstance, PatternTokens.listWeight ruleInstance.arguments ≤ limit →
        budget ruleInstance ≤ envelope) :
      ∀ proofs : List RawOpenProof, CertificateDataEncoding.proofsWeight proofs ≤ limit →
        childrenNodeBudget budget proofs ≤ envelope * CertificateDataEncoding.proofsWeight proofs
    | [], _ => by simp [childrenNodeBudget]
    | proof :: proofs, admitted => by
        have firstBound : CertificateDataEncoding.proofWeight proof ≤ limit := by
          simp only [CertificateDataEncoding.proofsWeight] at admitted
          omega
        have laterBound : CertificateDataEncoding.proofsWeight proofs ≤ limit := by
          simp only [CertificateDataEncoding.proofsWeight] at admitted
          omega
        have first := openNodeBudget_source_weight budget limit envelope bounded proof firstBound
        have later := childrenNodeBudget_source_weight budget limit envelope bounded proofs laterBound
        simp only [childrenNodeBudget, CertificateDataEncoding.proofsWeight]
        nlinarith
  termination_by proofs _ => sizeOf proofs
end

/-- Every stored chronological lemma, including unused entries, contributes
one framing unit to the independent submitted-data weight. -/
theorem lemmas_length_le_weight (lemmas : Lemmas) :
    lemmas.length ≤ CertificateDataEncoding.lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [CertificateDataEncoding.lemmasWeight]
  | cons pair rest ih =>
      rcases pair with ⟨goal, proof⟩
      simp only [List.length_cons, CertificateDataEncoding.lemmasWeight]
      omega

/-- Chronological origin indices fit the submitted-data envelope, even for
lemmas that the final root never uses. -/
theorem lemmasPayloadBudget_source_weight
    (budget : RuleInstance → ProofExecution.Origin → Nat) (limit envelope : Nat)
    (bounded : ∀ ruleInstance index, PatternTokens.listWeight ruleInstance.arguments ≤ limit →
      index ≤ limit → budget ruleInstance ("lemma", index) ≤ envelope) :
    ∀ (lemmas : Lemmas) (index : Nat),
      CertificateDataEncoding.lemmasWeight lemmas ≤ limit → index + lemmas.length ≤ limit →
      lemmasPayloadBudget budget index lemmas ≤
        envelope * CertificateDataEncoding.lemmasWeight lemmas
  | [], _, _, _ => by simp [lemmasPayloadBudget]
  | (goal, proof) :: rest, index, admitted, indexBound => by
      have proofBound : CertificateDataEncoding.proofWeight proof ≤ limit := by
        simp only [CertificateDataEncoding.lemmasWeight] at admitted
        omega
      have laterBound : CertificateDataEncoding.lemmasWeight rest ≤ limit := by
        simp only [CertificateDataEncoding.lemmasWeight] at admitted
        omega
      have currentIndex : index ≤ limit := by simp only [List.length_cons] at indexBound; omega
      have nextIndex : index + 1 + rest.length ≤ limit := by
        simp only [List.length_cons] at indexBound
        omega
      have first := openNodeBudget_source_weight (fun ruleInstance => budget ruleInstance ("lemma", index))
        limit envelope (fun ruleInstance valid => bounded ruleInstance index valid currentIndex) proof proofBound
      have later := lemmasPayloadBudget_source_weight budget limit envelope bounded rest (index + 1)
        laterBound nextIndex
      simp only [lemmasPayloadBudget, CertificateDataEncoding.lemmasWeight]
      nlinarith

/-- The finite source rule family bounds every admitted argument vector. -/
def arityCap (definition : CalculusLanguageDef) : Nat :=
  (definition.rules.map (fun rule => rule.metavariables.length)).sum

/-- The finite source rule family bounds every ordered premise vector. -/
def premiseCap (definition : CalculusLanguageDef) : Nat :=
  (definition.rules.map (fun rule => rule.premises.length)).sum

theorem instantiateRule_caps (definition : ValidatedCalculusLanguageDef)
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (admitted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    ruleInstance.arguments.length ≤ arityCap definition.1 ∧
      premises.length ≤ premiseCap definition.1 := by
  cases instantiateRule?_eq_some_iff_application.mp admitted with
  | intro rule found valid _side instantiated _concluded =>
      have argCount := argumentsValidAt_length valid
      have premiseCount := instantiated.length_eq
      have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some found
      have args := List.le_sum_of_mem (List.mem_map.mpr ⟨rule, member, rfl⟩ :
        rule.metavariables.length ∈ definition.1.rules.map (fun candidate => candidate.metavariables.length))
      have inputs := List.le_sum_of_mem (List.mem_map.mpr ⟨rule, member, rfl⟩ :
        rule.premises.length ∈ definition.1.rules.map (fun candidate => candidate.premises.length))
      unfold arityCap premiseCap
      omega

theorem lemma_origin_storage (index : Nat) : StorageSize.origin ("lemma", index) ≤ index + 9 := by
  have digits := InferenceStorageBounds.binaryDigits_le index
  change 1 + (1 + "lemma".utf8ByteSize) + (1 + (Nat.digits 2 index).length) ≤ _
  have nameSize : "lemma".utf8ByteSize = 5 := rfl
  rw [nameSize]
  omega

theorem root_origin_storage : StorageSize.origin ("root", 0) = 7 := by decide +kernel


/-- A local polynomial payload bound composes over the actual complete
chronological certificate. The fixed finite axiom prefix is retained as a
constant, while every supplied source proof occurrence is charged. -/
theorem compileSharedWith_polynomial_payload
    (definition : ValidatedCalculusLanguageDef) (emitRule : RuleEmitter)
    (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition emitRule budget) (coefficient degree : Nat)
    (growth : ∀ ruleInstance origin, budget ruleInstance origin ≤
      coefficient * (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^ degree)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileSharedWith definition emitRule goal source = some certificate) :
    graphWeight StorageSize.receiptPayload certificate.1 ≤
      graphWeight StorageSize.receiptPayload (axiomGraph definition.1) +
        coefficient * 12 ^ degree * CertificateDataEncoding.inputWeight goal source ^ (degree + 1) := by
  let amount := CertificateDataEncoding.inputWeight goal source
  let envelope := coefficient * 12 ^ degree * amount ^ degree
  have amountPositive : 1 ≤ amount := by
    simp only [amount, CertificateDataEncoding.inputWeight]
    omega
  have lemmaWeight : CertificateDataEncoding.lemmasWeight source.1 ≤ amount := by
    simp only [amount, CertificateDataEncoding.inputWeight, CertificateDataEncoding.sharedWeight]
    omega
  have rootWeight : CertificateDataEncoding.proofWeight source.2 ≤ amount := by
    simp only [amount, CertificateDataEncoding.inputWeight, CertificateDataEncoding.sharedWeight]
    omega
  have localEnvelope (ruleInstance : RuleInstance) (origin : ProofExecution.Origin)
      (argumentBound : PatternTokens.listWeight ruleInstance.arguments ≤ amount)
      (originBound : StorageSize.origin origin ≤ amount + 9) :
      budget ruleInstance origin ≤ envelope := by
    have base : PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1 ≤
        12 * amount := by omega
    calc
      budget ruleInstance origin ≤ coefficient *
          (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^ degree :=
        growth ruleInstance origin
      _ ≤ coefficient * (12 * amount) ^ degree :=
        Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left base degree)
      _ = envelope := by simp only [envelope, Nat.mul_pow]; ring
  have lemmaBound := lemmasPayloadBudget_source_weight budget amount envelope
    (fun ruleInstance index argumentBound indexBound => localEnvelope ruleInstance ("lemma", index)
      argumentBound ((lemma_origin_storage index).trans (by omega))) source.1 0 lemmaWeight
      (by have stored := lemmas_length_le_weight source.1; omega)
  have finalBound := openNodeBudget_source_weight (fun ruleInstance => budget ruleInstance ("root", 0))
    amount envelope (fun ruleInstance argumentBound => localEnvelope ruleInstance ("root", 0)
      argumentBound (by rw [root_origin_storage]; omega)) source.2 rootWeight
  have emitted := compileSharedWith_payload definition emitRule budget bounded goal source compiled
  have totalWeight : CertificateDataEncoding.lemmasWeight source.1 +
      CertificateDataEncoding.proofWeight source.2 ≤ amount := by
    simp only [amount, CertificateDataEncoding.inputWeight, CertificateDataEncoding.sharedWeight]
    omega
  calc
    graphWeight StorageSize.receiptPayload certificate.1 ≤
        graphWeight StorageSize.receiptPayload (axiomGraph definition.1) +
          envelope * (CertificateDataEncoding.lemmasWeight source.1 + CertificateDataEncoding.proofWeight source.2) := by
      nlinarith [emitted, lemmaBound, finalBound]
    _ ≤ graphWeight StorageSize.receiptPayload (axiomGraph definition.1) + envelope * amount :=
      Nat.add_le_add_left (Nat.mul_le_mul_left envelope totalWeight) _
    _ = _ := by simp only [envelope, amount, pow_succ]; ring


/-- The fixed-calculus output account includes complete graph payloads,
binary parent addresses, the selected root and the refusal representation.
This is a mathematical polynomial witness, not a runtime operation. -/
noncomputable def outputPolynomial (definition : CalculusLanguageDef) (coefficient degree : Nat) : Polynomial Nat :=
  Polynomial.C 16 + Polynomial.C 8 *
    (Polynomial.C (graphWeight StorageSize.receiptPayload (axiomGraph definition)) +
      Polynomial.C (coefficient * 12 ^ degree) * Polynomial.X ^ (degree + 1) +
      Polynomial.C 2 * (Polynomial.C definition.rules.length +
        Polynomial.C (8 * localNodeFactor definition) * Polynomial.X) ^ 2 +
      (Polynomial.C definition.rules.length +
        Polynomial.C (8 * localNodeFactor definition) * Polynomial.X) + Polynomial.C 2)

/-- A successful concrete compiler run retains the generic payload estimate
and the checked physical address estimate in one full-bit polynomial. -/
theorem compileShared_polynomial_bits_of_payload
    (definition : ValidatedCalculusLanguageDef)
    (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition (InferenceRuleExpansion.emitRule? definition) budget)
    (coefficient degree : Nat)
    (growth : ∀ ruleInstance origin, budget ruleInstance origin ≤
      coefficient * (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^ degree)
    (goal : Pattern) (source : LemmaCertificate) {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    StorageSize.certificateBits certificate ≤
      (outputPolynomial definition.1 coefficient degree).eval
        (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) := by
  have driver : compileSharedWith definition (InferenceRuleExpansion.emitRule? definition) goal source =
      some certificate := by
    cases admitted : sharedSourceCheck definition goal source with
    | false => simp [compileShared, admitted] at compiled
    | true => simpa [compileShared, admitted] using compiled
  have payload := compileSharedWith_polynomial_payload definition
    (InferenceRuleExpansion.emitRule? definition) budget bounded coefficient degree growth goal source driver
  have encoded : CertificateDataEncoding.inputWeight goal source ≤
      ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) := by
    simpa only [ProofSystems.encodedSize, CertificateDataEncoding.inputEncoding] using
      CertificateDataEncoding.encodeInput_length_lower goal source
  have powers := Nat.pow_le_pow_left encoded (degree + 1)
  have stored := compileShared_encoded_address_bound definition goal source compiled
  simp only [StorageSize.certificateBits, outputPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  nlinarith [Nat.mul_le_mul_left (coefficient * 12 ^ degree) powers]

/-- The translation is the actual computed shared graph; refusal has the
original empty graph representation. No proof is selected by choice. -/
def translate (definition : ValidatedCalculusLanguageDef) (goal : Pattern) (source : LemmaCertificate) :
    ProofSystem.Certificate := (compileShared definition goal source).getD ([], 0)

/-- The source checker is the original chronological admission check with
an explicit canonical-goal check. Its sizes charge the complete submitted
packet, including every unused lemma and binary hole index. -/
def sourceSizedChecker (definition : ValidatedCalculusLanguageDef) :
    ProofSystems.SizedChecker Pattern LemmaCertificate where
  check goal source := argumentValidAt 0 goal && sharedSourceCheck definition goal source
  claimSize goal := 8 * PatternTokens.weight goal
  certificateSize source := CertificateDataEncoding.sharedBitWeight source

/-- The target is the independent existing HOL graph checker; the size is
its complete theorem/request/origin and physical-address account. -/
def targetSizedChecker (definition : CalculusLanguageDef) :
    ProofSystems.SizedChecker Pattern ProofSystem.Certificate where
  toChecker := compiledChecker definition
  claimSize goal := 8 * PatternTokens.weight goal
  certificateSize := StorageSize.certificateBits

theorem sourceSizedChecker_inputSize (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) :
    (sourceSizedChecker definition).inputSize (goal, source) + 8 =
      CertificateDataEncoding.inputBitWeight goal source := by
  simp only [ProofSystems.SizedChecker.inputSize, sourceSizedChecker,
    CertificateDataEncoding.sharedBitWeight, CertificateDataEncoding.inputBitWeight,
    CertificateDataEncoding.inputWeight]
  omega

theorem sourceSizedChecker_encoding_bound (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate) :
    ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) ≤
      16 * ((sourceSizedChecker definition).inputSize (goal, source) + 8) := by
  have stored := CertificateDataEncoding.encodeInput_length goal source
  simp only [ProofSystems.encodedSize, CertificateDataEncoding.inputEncoding]
  rw [sourceSizedChecker_inputSize]
  simp only [CertificateDataEncoding.inputBitWeight]
  omega

theorem translate_preserves (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate)
    (accepted : (sourceSizedChecker definition).check goal source = true) :
    (targetSizedChecker definition.1).check goal (translate definition goal source) = true := by
  have admitted : argumentValidAt 0 goal = true ∧ sharedSourceCheck definition goal source = true := by
    simpa only [sourceSizedChecker, Bool.and_eq_true] using accepted
  obtain ⟨certificate, computed⟩ := compileShared_preserves definition firstOrder goal source admitted.2
  have checked := compileShared_claim_checked definition goal source admitted.1 computed
  simpa only [targetSizedChecker, translate, computed, Option.getD_some] using checked

theorem empty_graph_refused (definition : CalculusLanguageDef) (goal : Pattern) :
    (targetSizedChecker definition).check goal ([], 0) = false := by
  simp [targetSizedChecker, compiledChecker, DerivationGraph.replay, DerivationGraph.replayFrom]

theorem translate_refused (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate)
    (refused : sharedSourceCheck definition goal source = false) :
    translate definition goal source = ([], 0) := by
  rw [translate, compileShared_refused definition goal source refused]
  rfl


/-- Refused packets retain the fixed empty representation, while accepted
packets retain the actual successful compiler graph. Both cases fit the same
complete-output polynomial. -/
theorem translate_polynomial_bits_of_payload
    (definition : ValidatedCalculusLanguageDef)
    (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition (InferenceRuleExpansion.emitRule? definition) budget)
    (coefficient degree : Nat)
    (growth : ∀ ruleInstance origin, budget ruleInstance origin ≤
      coefficient * (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^ degree)
    (goal : Pattern) (source : LemmaCertificate) :
    StorageSize.certificateBits (translate definition goal source) ≤
      (outputPolynomial definition.1 coefficient degree).eval
        (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) := by
  cases computed : compileShared definition goal source with
  | none =>
      have emptySize : StorageSize.certificateBits (([], 0) : ProofSystem.Certificate) = 16 := by
        decide +kernel
      rw [translate, computed, Option.getD_none, emptySize]
      simp only [outputPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      omega
  | some certificate =>
      simpa only [translate, computed, Option.getD_some] using
        compileShared_polynomial_bits_of_payload definition budget bounded coefficient degree growth
          goal source computed

/-- The compiler's reusable size join uses full storage measures and actual
translation. Runtime complexity remains a separate operational obligation. -/
def sizeSimulationOfPayload (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1)
    (budget : RuleInstance → ProofExecution.Origin → Nat)
    (bounded : PayloadBound definition (InferenceRuleExpansion.emitRule? definition) budget)
    (coefficient degree : Nat)
    (growth : ∀ ruleInstance origin, budget ruleInstance origin ≤
      coefficient * (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^ degree) :
    ProofSystems.SizeSimulation (targetSizedChecker definition.1) (sourceSizedChecker definition) where
  translate := translate definition
  preserves := translate_preserves definition firstOrder
  sizeBound := by
    refine ⟨(outputPolynomial definition.1 coefficient degree).comp
      (Polynomial.C 16 * (Polynomial.X + Polynomial.C 8)), ?_⟩
    intro input
    have actual := translate_polynomial_bits_of_payload definition budget bounded coefficient degree growth
      input.1 input.2
    have encoded := sourceSizedChecker_encoding_bound definition input.1 input.2
    have monotone := ProofSystems.eval_mono (outputPolynomial definition.1 coefficient degree) encoded
    have joined := actual.trans monotone
    simpa only [targetSizedChecker, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using joined


/-- A refused original certificate cannot acquire acceptance by passing
through the total translator, including a noncanonical supplied goal. -/
theorem translate_rejects (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate)
    (refused : (sourceSizedChecker definition).check goal source = false) :
    (targetSizedChecker definition.1).check goal (translate definition goal source) = false := by
  cases valid : argumentValidAt 0 goal with
  | false => simp [targetSizedChecker, compiledChecker, valid]
  | true =>
      have rejected : sharedSourceCheck definition goal source = false := by
        simpa only [sourceSizedChecker, valid, Bool.true_and] using refused
      rw [translate_refused definition goal source rejected]
      exact empty_graph_refused definition.1 goal

/-- Acceptance of the total executable translation is exact for each supplied
source packet; this is stronger than merely preserving a provable claim. -/
theorem translate_checked_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate) :
    (targetSizedChecker definition.1).check goal (translate definition goal source) = true ↔
      (sourceSizedChecker definition).check goal source = true := by
  constructor
  · intro checked
    cases admitted : (sourceSizedChecker definition).check goal source with
    | false => rw [translate_rejects definition goal source admitted] at checked; contradiction
    | true => rfl
  · exact translate_preserves definition firstOrder goal source

/-- Refusal storage is fixed and includes the root delimiter; a huge refused
reference never changes the selected empty representation. -/
theorem translate_refused_bits (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (source : LemmaCertificate)
    (refused : sharedSourceCheck definition goal source = false) :
    StorageSize.certificateBits (translate definition goal source) = 16 := by
  rw [translate_refused definition goal source refused]
  decide +kernel


/-- Complete fixed-calculus packet overhead: source schema axioms and
allowed theorem dependencies are retained, rather than hidden in a callback. -/
def packetFactor (definition : CalculusLanguageDef) : Nat :=
  1 + InferenceStorageBounds.ruleTheoremsPayload definition +
    premiseCap definition * (InferenceStorageBounds.theoryPayload (inferenceRules definition) + 3) +
      122 + 184 * schemaPayloadFactor definition

/-- The source packet feeding an actual rule emitter is bounded from the
original typed instantiation and the checked ordered premise vector. -/
theorem sourcePacketUnits_bound (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1)
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion))
    {state : ProofExecution.State} {roots : List Nat} {inputs : List Theorem}
    (earlier : BuildChecked (policy (inferenceRules definition.1)) [] state)
    (represented : Represents state premises roots)
    (selected : DerivationGraph.lookupPremises state.cache roots = some inputs)
    (origin : ProofExecution.Origin) :
    InferenceStorageBounds.sourcePacketUnits definition.1 ruleInstance inputs origin ≤
      packetFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) +
        StorageSize.origin origin := by
  have caps := instantiateRule_caps definition instantiated
  have inputCount : inputs.length = premises.length := by
    have selectedCount := DerivationGraph.lookupPremises_length state.cache selected
    have representedCount := List.Forall₂.length_eq represented
    omega
  have inputBound : inputs.length ≤ premiseCap definition.1 := by omega
  have payload := instantiateRule_payload definition firstOrder instantiated
  have selectedPayload := represented_inputs_storage definition.1 earlier represented selected
  have scaledCount := Nat.mul_le_mul_right
    (InferenceStorageBounds.theoryPayload (inferenceRules definition.1) + 3) inputBound
  simp only [OpenTheory.StorageSize.list] at selectedPayload
  have premiseFootprint : PatternTokens.listWeight premises ≤
      schemaPayloadFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) := by omega
  have scaledFootprint : 184 * PatternTokens.listWeight premises ≤
      184 * schemaPayloadFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 184 premiseFootprint
  have premiseSum : (inputs.map OpenTheory.StorageSize.theoremData).sum ≤
      premiseCap definition.1 * (InferenceStorageBounds.theoryPayload (inferenceRules definition.1) + 3) +
        184 * schemaPayloadFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) := by omega
  let fixed := 1 + InferenceStorageBounds.ruleTheoremsPayload definition.1 +
    premiseCap definition.1 * (InferenceStorageBounds.theoryPayload (inferenceRules definition.1) + 3)
  have fixedBound : fixed ≤ fixed * (PatternTokens.listWeight ruleInstance.arguments + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left fixed
      (by omega : 1 ≤ PatternTokens.listWeight ruleInstance.arguments + 1)
  have argsBound : 122 * PatternTokens.listWeight ruleInstance.arguments ≤
      122 * (PatternTokens.listWeight ruleInstance.arguments + 1) :=
    Nat.mul_le_mul_left 122 (Nat.le_succ _)
  calc
    InferenceStorageBounds.sourcePacketUnits definition.1 ruleInstance inputs origin ≤
        fixed + 122 * PatternTokens.listWeight ruleInstance.arguments +
          184 * schemaPayloadFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) +
            StorageSize.origin origin := by
      simp only [InferenceStorageBounds.sourcePacketUnits, fixed]
      omega
    _ ≤ fixed * (PatternTokens.listWeight ruleInstance.arguments + 1) +
        122 * (PatternTokens.listWeight ruleInstance.arguments + 1) +
          184 * schemaPayloadFactor definition.1 * (PatternTokens.listWeight ruleInstance.arguments + 1) +
            StorageSize.origin origin :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add fixedBound argsBound) _) _
    _ = _ := by simp only [fixed, packetFactor]; ring

/-- The emitter polynomial's degree is allowed to depend on its fixed
finite source arity cap. This is not a uniform variable-calculus claim. -/
def localPayloadDegree (definition : CalculusLanguageDef) : Nat := 4 * 2 ^ arityCap definition

def localPayloadCoefficient (definition : CalculusLanguageDef) : Nat :=
  InferenceStorageBounds.ruleEmissionCoefficient (arityCap definition) (premiseCap definition)

/-- A concrete local budget uses only the actual input arguments and physical
origin, with the fixed source theory overhead explicitly charged. -/
def localPayloadBudget (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (origin : ProofExecution.Origin) : Nat :=
  localPayloadCoefficient definition *
    (packetFactor definition * (PatternTokens.listWeight ruleInstance.arguments + 1) +
      StorageSize.origin origin) ^ localPayloadDegree definition

def payloadCoefficient (definition : CalculusLanguageDef) : Nat :=
  localPayloadCoefficient definition * (packetFactor definition + 1) ^ localPayloadDegree definition

theorem localPayloadBudget_growth (definition : CalculusLanguageDef)
    (ruleInstance : RuleInstance) (origin : ProofExecution.Origin) :
    localPayloadBudget definition ruleInstance origin ≤
      payloadCoefficient definition *
        (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) ^
          localPayloadDegree definition := by
  have base : packetFactor definition * (PatternTokens.listWeight ruleInstance.arguments + 1) +
      StorageSize.origin origin ≤
    (packetFactor definition + 1) *
      (PatternTokens.listWeight ruleInstance.arguments + StorageSize.origin origin + 1) := by nlinarith
  have powered := Nat.pow_le_pow_left base (localPayloadDegree definition)
  have scaled := Nat.mul_le_mul_left (localPayloadCoefficient definition) powered
  simpa only [localPayloadBudget, payloadCoefficient, Nat.mul_pow, Nat.mul_assoc] using scaled


/-- The actual primitive rule emitter discharges the local payload contract
from admitted source instantiation and actual checked premise lookup. No
external size callback appears in the final compiler estimate. -/
theorem ruleEmitter_payloadBound (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    PayloadBound definition (InferenceRuleExpansion.emitRule? definition)
      (localPayloadBudget definition.1) := by
  intro ruleInstance premises conclusion origin state roots inputs block instantiated earlier represented selected computed
  have caps := instantiateRule_caps definition instantiated
  have inputCount : inputs.length = premises.length := by
    have selectedCount := DerivationGraph.lookupPremises_length state.cache selected
    have representedCount := List.Forall₂.length_eq represented
    omega
  have inputCap : inputs.length ≤ premiseCap definition.1 := by omega
  have emitted := InferenceStorageBounds.emitRule?_payload definition ruleInstance inputs origin
    (arityCap definition.1) (premiseCap definition.1) caps.1 inputCap computed
  have packet := sourcePacketUnits_bound definition firstOrder instantiated earlier represented selected origin
  have powered := Nat.pow_le_pow_left packet (localPayloadDegree definition.1)
  have scaled := Nat.mul_le_mul_left (localPayloadCoefficient definition.1) powered
  change graphWeight StorageSize.receiptPayload block.1 ≤ _ at emitted
  change graphWeight StorageSize.receiptPayload block.1 ≤ localPayloadCoefficient definition.1 *
    InferenceStorageBounds.sourcePacketUnits definition.1 ruleInstance inputs origin ^
      localPayloadDegree definition.1 at emitted
  exact emitted.trans scaled

/-- Every successful actual shared compilation has a complete physical
certificate-bit bound polynomial in its actual finite-alphabet input length.
The theorem is for each fixed finite admitted first-order calculus. -/
theorem compileShared_polynomial_bits (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate)
    {certificate : ProofSystem.Certificate}
    (compiled : compileShared definition goal source = some certificate) :
    StorageSize.certificateBits certificate ≤
      (outputPolynomial definition.1 (payloadCoefficient definition.1) (localPayloadDegree definition.1)).eval
        (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) :=
  compileShared_polynomial_bits_of_payload definition (localPayloadBudget definition.1)
    (ruleEmitter_payloadBound definition firstOrder) (payloadCoefficient definition.1)
    (localPayloadDegree definition.1) (localPayloadBudget_growth definition.1) goal source compiled

/-- Honest per-calculus size simulation by the actual shared compiler and
original HOL graph checker. This construction claims a full output-size
bound and exact executable acceptance, but no translation-time bound. -/
def sizeSimulation (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    ProofSystems.SizeSimulation (targetSizedChecker definition.1) (sourceSizedChecker definition) :=
  sizeSimulationOfPayload definition firstOrder (localPayloadBudget definition.1)
    (ruleEmitter_payloadBound definition firstOrder) (payloadCoefficient definition.1)
    (localPayloadDegree definition.1) (localPayloadBudget_growth definition.1)

/-- The public size simulation uses the literal total compiler, without
selecting a target proof from a theorem of existence. -/
theorem sizeSimulation_translate (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate) :
    (sizeSimulation definition firstOrder).translate goal source =
      (compileShared definition goal source).getD ([], 0) := rfl

/-- Physical output words use the lossless finite-alphabet graph codec. Every
symbol fits in three bits; decoding retains the original graph and checker. -/
def serializedChecker (definition : CalculusLanguageDef) :
    ProofSystems.SizedChecker Pattern (List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet) where
  check goal word := ((ProofDataEncoding.decodeCertificate word).map
    (fun certificate => (compiledChecker definition).check goal certificate)).getD false
  claimSize goal := 8 * PatternTokens.weight goal
  certificateSize word := 3 * word.length

theorem serializedChecker_encoded (definition : CalculusLanguageDef)
    (goal : Pattern) (certificate : ProofSystem.Certificate) :
    (serializedChecker definition).check goal (ProofDataEncoding.encodeCertificate certificate) =
      (compiledChecker definition).check goal certificate := by
  simp only [serializedChecker, ProofDataEncoding.decodeCertificate_encodeCertificate,
    Option.map_some, Option.getD_some]

/-- Complete serialized certificates have a polynomial physical bit bound,
for the same fixed finite calculus as the structural storage theorem. -/
theorem translate_serialized_bits (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate) :
    3 * (ProofDataEncoding.encodeCertificate (translate definition goal source)).length ≤
      (Polynomial.C 24 * outputPolynomial definition.1 (payloadCoefficient definition.1)
        (localPayloadDegree definition.1)).eval
          (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source)) := by
  have storage := translate_polynomial_bits_of_payload definition (localPayloadBudget definition.1)
    (ruleEmitter_payloadBound definition firstOrder) (payloadCoefficient definition.1)
    (localPayloadDegree definition.1) (localPayloadBudget_growth definition.1) goal source
  have physical := ProofDataEncoding.encodeCertificate_bit_bound (translate definition goal source)
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  exact physical.trans (Nat.mul_le_mul_left 24 storage)

/-- Each original emitted occurrence has an executed receipt-packing stage
bounded by the supplied source packet's physical size. Producing its four
fields and executing the whole chronological driver remain separate joins. -/
def translatedNodeOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate)
    (node : ProofExecution.Receipt) (member : node ∈ (translate definition goal source).1) :
    Turing.TM2OutputsInTime
      (Mettapedia.Computability.WordTemplateMachine.Indexed.machine
        ProofDataEncoding.Serialization.nodeTemplate)
      (ProofDataEncoding.Serialization.nodeInput node)
      (some (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith ProofDataEncoding.receiptCodec node))
      ((Polynomial.C 256 * outputPolynomial definition.1 (payloadCoefficient definition.1)
        (localPayloadDegree definition.1) + Polynomial.C 64).eval
        (ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source))) := by
  have ran := ProofDataEncoding.Serialization.nodeEncodedOutputs node
  have inside := ProofDataEncoding.Serialization.nodeLength_le_certificate
    (translate definition goal source) node member
  have storage := translate_serialized_bits definition firstOrder goal source
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at storage
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  refine ⟨ran.toEvalsTo, ran.steps_le_m.trans ?_⟩
  omega

/-- The executable byte interface preserves and reflects acceptance of each
original supplied certificate, including rejected and unused lemma entries. -/
theorem serialized_translate_checked_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) (source : LemmaCertificate) :
    (serializedChecker definition.1).check goal
        (ProofDataEncoding.encodeCertificate (translate definition goal source)) = true ↔
      (sourceSizedChecker definition).check goal source = true := by
  rw [serializedChecker_encoded]
  exact translate_checked_iff definition firstOrder goal source

/-- Polynomial-size faithful compilation into actual serialized HOL graphs.
This law makes no whole-translation execution-time assertion. -/
def serializedSizeSimulation (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    ProofSystems.SizeSimulation (serializedChecker definition.1) (sourceSizedChecker definition) where
  translate goal source := ProofDataEncoding.encodeCertificate (translate definition goal source)
  preserves goal source accepted :=
    (serialized_translate_checked_iff definition firstOrder goal source).mpr accepted
  sizeBound := by
    obtain ⟨polynomial, bounded⟩ := (sizeSimulation definition firstOrder).sizeBound
    refine ⟨Polynomial.C 24 * polynomial, ?_⟩
    intro input
    have physical := ProofDataEncoding.encodeCertificate_bit_bound (translate definition input.1 input.2)
    have storage := bounded input
    change StorageSize.certificateBits (translate definition input.1 input.2) ≤ _ at storage
    change 3 * (ProofDataEncoding.encodeCertificate (translate definition input.1 input.2)).length ≤ _
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    exact physical.trans (Nat.mul_le_mul_left 24 storage)

/-- Arbitrary successful serialized target proofs certify source derivability;
the target interface never consults the source compiler or source proof file. -/
theorem derives_iff_serialized (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern)
    (valid : argumentValidAt 0 goal = true) :
    Nonempty (InferenceChecker.Derivation definition goal) ↔
      ∃ word, (serializedChecker definition.1).check goal word = true := by
  rw [derives_iff_compiled_graph definition firstOrder goal valid]
  constructor
  · rintro ⟨certificate, accepted⟩
    exact ⟨ProofDataEncoding.encodeCertificate certificate, by
      simpa only [serializedChecker_encoded] using accepted⟩
  · rintro ⟨word, accepted⟩
    cases decoded : ProofDataEncoding.decodeCertificate word with
    | none => simp [serializedChecker, decoded] at accepted
    | some certificate =>
        exact ⟨certificate, by simpa only [serializedChecker, decoded,
          Option.map_some, Option.getD_some] using accepted⟩

section ExecutedRootCache

set_option backward.isDefEq.respectTransparency false
open Turing

/-- Original source-context representation supplies genuine stored addresses. -/
theorem represented_roots_inside {state : ProofExecution.State}
    {goals : List Pattern} {roots : List Nat} (represented : Represents state goals roots) :
    ∀ root ∈ roots, root < state.cache.size := by
  induction represented with
  | nil => simp
  | @cons goal root goals roots related _ ih =>
      intro selected member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        obtain ⟨out, stored, _⟩ := related
        exact (Array.getElem?_eq_some_iff.mp stored).1
      · exact ih selected later

/-- The checked replay counts the original physical primitive-node prefix. -/
theorem checked_cache_size (definition : CalculusLanguageDef) {state : ProofExecution.State}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state) :
    state.cache.size = state.receipts.size := by
  have counted := DerivationGraph.replayFrom_size
    (ruleWitness (policy (inferenceRules definition))) (cache := #[])
    (nodes := state.receipts.toList) checked
  have nodes : state.receipts.toList.length = state.receipts.size := Array.length_toList
  have base : state.cache.size = state.receipts.toList.length := by
    simpa only [Array.size_empty, Nat.zero_add] using counted
  exact base.trans nodes

/-- The concrete chronological root-table payload is polynomial in the
source-context length and the already emitted primitive-node prefix. -/
theorem represented_rootTable_length (definition : CalculusLanguageDef)
    {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state)
    (represented : Represents state goals roots) :
    (SharedReferenceExecution.table (SharedReferenceExecution.indexed roots.toArray)).length ≤
      roots.length * (roots.length + state.receipts.size + 3) + 1 := by
  have stored := represented_roots_inside represented
  rw [checked_cache_size definition checked] at stored
  apply SharedReferenceExecution.PhysicalSize.indexed_table_length
  intro root member
  exact Nat.le_of_lt (stored root (by simpa using member))

/-- Lookup follows the concrete resolver's transition theorem and charges
all physically represented context rows, even when roots occur repeatedly. -/
def represented_referenceOutputs (definition : CalculusLanguageDef)
    {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state)
    (represented : Represents state goals roots) (query : Nat) :
    let payload := (SharedReferenceExecution.naturalKey query).length +
      roots.length * (roots.length + state.receipts.size + 3) + 2
    TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.referencePacket roots.toArray query)
      (some (SharedReferenceExecution.physicalOutput roots[query]?))
      (4 * payload ^ 2 + 20 * payload + 20) := by
  have stored := represented_roots_inside represented
  rw [checked_cache_size definition checked] at stored
  have executed := SharedReferenceExecution.PhysicalSize.referenceOutputs
    roots.toArray query state.receipts.size (by
      intro root member
      exact Nat.le_of_lt (stored root (by simpa using member)))
  simpa using executed

/-- A checked newly returned source root extends precisely the same
chronological table, with a clock for the real copied cache payload. -/
def represented_appendOutputs (definition : CalculusLanguageDef)
    {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state)
    (represented : Represents state goals roots) {physical : Nat} {out : Theorem}
    (found : state.cache[physical]? = some out) :
    let payload := roots.length * (roots.length + state.receipts.size + 3) +
      roots.length + state.receipts.size + 4
    TM2OutputsInTime SharedReferenceExecution.TableAppend.machine
      (SharedReferenceExecution.TableAppend.packet (SharedReferenceExecution.indexed roots.toArray)
        (SharedReferenceExecution.naturalKey roots.length) (SharedReferenceExecution.naturalKey physical))
      (some (SharedReferenceExecution.table (SharedReferenceExecution.indexed (roots.toArray.push physical))))
      (38 * payload + 36) := by
  have stored := represented_roots_inside represented
  have physicalBound := (Array.getElem?_eq_some_iff.mp found).1
  rw [checked_cache_size definition checked] at stored physicalBound
  have executed := SharedReferenceExecution.PhysicalSize.appendOutputs
    roots.toArray physical state.receipts.size (by
      intro root member
      exact Nat.le_of_lt (stored root (by simpa using member))) (Nat.le_of_lt physicalBound)
  simpa using executed


/-- Original goal words pay for all constructors, names and numerical fields. -/
theorem encodedClaim_length (goal : Pattern) :
    (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith
      CertificateDataEncoding.patternCodec goal).length ≤ 74 * PatternTokens.weight goal := by
  have bound := CertificateDataEncoding.dataWeight_pattern goal
  simpa only [Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith,
    Mettapedia.OSLF.Binding.WireCodec.Binary.encodeData,
    Mettapedia.OSLF.Binding.WireCodec.Binary.writeData_length, List.length_nil, Nat.add_zero] using bound

private theorem claimWords_length (goals : List Pattern) :
    (goals.map fun goal => (SharedReferenceExecution.EncodedTable.value
      CertificateDataEncoding.patternCodec goal).length).sum ≤
        222 * PatternTokens.listWeight goals := by
  induction goals with
  | nil => simp [PatternTokens.listWeight]
  | cons goal goals ih =>
      have head := encodedClaim_length goal
      simp only [List.map_cons, List.sum_cons, PatternTokens.listWeight]
      rw [SharedReferenceExecution.EncodedTable.encoded_length]
      omega

/-- The source-claim cache retains every original field and every occurrence. -/
theorem claimTable_length (goals : List Pattern) :
    (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
      CertificateDataEncoding.patternCodec goals.toArray)).length ≤
        222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) + 1 := by
  have table := SharedReferenceExecution.EncodedTable.table_length_bound
    (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec) 0 goals
  have words := claimWords_length goals
  simpa only [SharedReferenceExecution.EncodedTable.rows, List.toList_toArray,
    Nat.zero_add] using table.trans (Nat.add_le_add_right
      (Nat.add_le_add_right words _) _)

/-- Actual source-cache lookup is charged against complete stored goals, not
merely the number of rows or the numeric value of the query. -/
def claimReferenceOutputs (goals : List Pattern) (query : Nat) :
    let payload := (SharedReferenceExecution.naturalKey query).length +
      222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) + 2
    TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        goals.toArray query)
      (some (SharedReferenceExecution.output
        (goals[query]?.map (SharedReferenceExecution.EncodedTable.value
          CertificateDataEncoding.patternCodec))))
      (4 * payload ^ 2 + 20 * payload + 20) := by
  have executed := SharedReferenceExecution.EncodedTable.referenceOutputs
    CertificateDataEncoding.patternCodec goals.toArray query
  have stored := claimTable_length goals
  have packet := SharedReferenceExecution.packet_length
    (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)
  have run : TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        goals.toArray query)
      (some (SharedReferenceExecution.output (goals[query]?.map
        (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec))))
      (4 * (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        goals.toArray query).length ^ 2 + 20 *
        (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
          goals.toArray query).length + 20) := by simpa using executed
  dsimp only
  have inputBound : (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query)
      (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)).length ≤
        (SharedReferenceExecution.naturalKey query).length +
          222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) + 2 := by omega
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  change 4 * (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)).length ^ 2 +
    20 * (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query)
      (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)).length + 20 ≤ _
  nlinarith [Nat.pow_le_pow_left inputBound 2]

/-- Lossless byte lookup recovers the original claim before selecting its HOL
root. A physical address alone is insufficient to establish this conclusion. -/
theorem represented_encoded_lookup {state : ProofExecution.State}
    {goals : List Pattern} {roots : List Nat} (represented : Represents state goals roots)
    {query : Nat} {goal : Pattern}
    (found : SharedReferenceExecution.lookup (SharedReferenceExecution.naturalKey query)
      (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray) =
        some (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec goal)) :
    ∃ root out, roots[query]? = some root ∧ state.cache[root]? = some out ∧ hasClaim goal out = true := by
  rw [SharedReferenceExecution.EncodedTable.lookup_rows] at found
  cases selected : goals[query]? with
  | none => simp [selected] at found
  | some saved =>
      have words : SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec saved =
          SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec goal := by
        simpa [selected] using found
      have same := SharedReferenceExecution.EncodedTable.value_injective
        CertificateDataEncoding.patternCodec words
      subst saved
      exact represented_lookup represented selected

/-- The claim guard compares every original symbol and has an attached clock. -/
def claimEqualityOutputs (expected stored : Pattern) :
    TM2OutputsInTime
      (Mettapedia.Computability.WordEqualityMachine.machine
        Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet)
      (Mettapedia.OSLF.Binding.WireCodec.Binary.Equality.packet
        CertificateDataEncoding.patternCodec expected stored)
      (some [decide (expected = stored)])
      (222 * PatternTokens.weight expected + 74 * PatternTokens.weight stored + 4) := by
  have executed := Mettapedia.OSLF.Binding.WireCodec.Binary.Equality.outputs
    CertificateDataEncoding.patternCodec expected stored
  apply ProofSystems.BinaryReferenceMachine.within executed
  have left := encodedClaim_length expected
  have right := encodedClaim_length stored
  omega

/-- A different original judgment is refused by the same full-word guard. -/
def wrongClaimOutputs (expected stored : Pattern) (different : expected ≠ stored) :
    TM2OutputsInTime
      (Mettapedia.Computability.WordEqualityMachine.machine
        Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet)
      (Mettapedia.OSLF.Binding.WireCodec.Binary.Equality.packet
        CertificateDataEncoding.patternCodec expected stored)
      (some [false])
      (222 * PatternTokens.weight expected + 74 * PatternTokens.weight stored + 4) := by
  simpa only [decide_eq_false different] using claimEqualityOutputs expected stored

/-- Original claim insertion copies the complete old history and new goal. -/
def claimAppendOutputs (goals : List Pattern) (goal : Pattern) :
    let payload := 222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) +
      goals.length + 222 * PatternTokens.weight goal + 4
    TM2OutputsInTime SharedReferenceExecution.TableAppend.machine
      (SharedReferenceExecution.TableAppend.packet
        (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)
        (SharedReferenceExecution.naturalKey goals.length)
        (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec goal))
      (some (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
        CertificateDataEncoding.patternCodec (goals.toArray.push goal))))
      (38 * payload + 36) := by
  have executed := SharedReferenceExecution.EncodedTable.appendOutputs
    CertificateDataEncoding.patternCodec goals.toArray goal
  have stored := claimTable_length goals
  have key := SharedReferenceExecution.PhysicalSize.naturalKey_length goals.length
  have encoded := encodedClaim_length goal
  have word := SharedReferenceExecution.EncodedTable.encoded_length CertificateDataEncoding.patternCodec goal
  have run : TM2OutputsInTime SharedReferenceExecution.TableAppend.machine
      (SharedReferenceExecution.TableAppend.packet
        (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)
        (SharedReferenceExecution.naturalKey goals.length)
        (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec goal))
      (some (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
        CertificateDataEncoding.patternCodec (goals.toArray.push goal))))
      (38 * (SharedReferenceExecution.TableAppend.packet
        (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)
        (SharedReferenceExecution.naturalKey goals.length)
        (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec goal)).length + 36) := by
    simpa using executed
  dsimp only
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  simp only [SharedReferenceExecution.TableAppend.packet,
    Mettapedia.Computability.WordTemplateMachine.Indexed.argumentWire,
    Mettapedia.Computability.WordTemplateMachine.Indexed.frame,
    SharedReferenceExecution.TableAppend.fields, List.finRange_succ,
    List.finRange_zero, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.length_append, List.length_map,
    List.length_cons, List.length_nil, SharedReferenceExecution.field]
  omega


/-- The entire submitted source packet pays for every chronological goal
prefix, whether or not the final proof references its entries. -/
theorem sourceClaimCache_table_length (goal : Pattern) (source : LemmaCertificate) (count : Nat) :
    (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
      CertificateDataEncoding.patternCodec ((source.1.take count).map Prod.fst).toArray)).length ≤
        226 * ((CertificateDataEncoding.encodeInput goal source).length + 1) ^ 2 := by
  have stored := claimTable_length ((source.1.take count).map Prod.fst)
  have weights := CertificateDataEncoding.lemmaGoals_prefix_weight source.1 count
  have lengths := CertificateDataEncoding.lemmas_length_le_weight source.1
  have submitted := CertificateDataEncoding.encodeInput_length_lower goal source
  have prefixCount : ((source.1.take count).map Prod.fst).length ≤ source.1.length := by
    simp only [List.length_map, List.length_take]
    exact Nat.min_le_right _ _
  have prefixWeight : PatternTokens.listWeight ((source.1.take count).map Prod.fst) ≤
      (CertificateDataEncoding.encodeInput goal source).length := by
    simp only [CertificateDataEncoding.inputWeight, CertificateDataEncoding.sharedWeight] at submitted
    omega
  have prefixLength : ((source.1.take count).map Prod.fst).length ≤
      (CertificateDataEncoding.encodeInput goal source).length := by
    simp only [CertificateDataEncoding.inputWeight, CertificateDataEncoding.sharedWeight] at submitted
    omega
  nlinarith [Nat.mul_self_le_mul_self prefixLength]

/-- This concrete cache phase has a fourth-degree clock in the physical
submitted source and binary query lengths. It is not a whole-translator clock. -/
def sourceClaimCache_referenceOutputs (goal : Pattern) (source : LemmaCertificate)
    (count query : Nat) :
    let size := (SharedReferenceExecution.naturalKey query).length +
      (CertificateDataEncoding.encodeInput goal source).length + 1
    TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        ((source.1.take count).map Prod.fst).toArray query)
      (some (SharedReferenceExecution.output
        ((getElem? ((source.1.take count).map Prod.fst) query).map
          (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec))))
      (211000 * size ^ 4) := by
  have executed := SharedReferenceExecution.EncodedTable.referenceOutputs
    CertificateDataEncoding.patternCodec ((source.1.take count).map Prod.fst).toArray query
  have run : TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        ((source.1.take count).map Prod.fst).toArray query)
      (some (SharedReferenceExecution.output
        ((getElem? ((source.1.take count).map Prod.fst) query).map
          (SharedReferenceExecution.EncodedTable.value CertificateDataEncoding.patternCodec))))
      (4 * (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        ((source.1.take count).map Prod.fst).toArray query).length ^ 2 +
        20 * (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
          ((source.1.take count).map Prod.fst).toArray query).length + 20) := by simpa using executed
  have stored := sourceClaimCache_table_length goal source count
  have packet := SharedReferenceExecution.packet_length (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec
      ((source.1.take count).map Prod.fst).toArray)
  let size := (SharedReferenceExecution.naturalKey query).length +
    (CertificateDataEncoding.encodeInput goal source).length + 1
  have positive : 1 ≤ size := by dsimp only [size]; omega
  have submitted : (CertificateDataEncoding.encodeInput goal source).length + 1 ≤ size := by
    dsimp only [size]; omega
  have querySize : (SharedReferenceExecution.naturalKey query).length + 1 ≤ size := by
    dsimp only [size]; omega
  have submittedSquare := Nat.pow_le_pow_left submitted 2
  have squared : size ≤ size ^ 2 := by nlinarith
  have inputBound :
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        ((source.1.take count).map Prod.fst).toArray query).length ≤ 227 * size ^ 2 := by
    change (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query) _).length ≤ _
    nlinarith
  have enlarged := Nat.pow_le_pow_left inputBound 2
  have fourth : size ^ 2 ≤ size ^ 4 := by nlinarith
  dsimp only
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  change _ ≤ 211000 * size ^ 4
  nlinarith [pow_mul size 2 2]


/-- The checked original graph accounts for every stored primitive theorem,
including intermediate facts that are not selected source roots. -/
private theorem theoremWords_length (nodes : List ProofExecution.Receipt) :
    (nodes.map fun node => (SharedReferenceExecution.EncodedTable.value
      SyntaxEncoding.theoremCodec node.conclusion).length).sum ≤
        192 * graphWeight StorageSize.receiptPayload nodes := by
  induction nodes with
  | nil => simp [graphWeight]
  | cons node nodes ih =>
      have payload := SyntaxEncoding.theorem_payload_bound node.conclusion
      have encoded := SharedReferenceExecution.EncodedTable.encoded_length
        SyntaxEncoding.theoremCodec node.conclusion
      simp only [Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith,
        Mettapedia.OSLF.Binding.WireCodec.Binary.encodeData,
        Mettapedia.OSLF.Binding.WireCodec.Binary.writeData_length, List.length_nil, Nat.add_zero] at encoded
      simp only [List.map_cons, List.sum_cons, graphWeight, receiptWeight,
        StorageSize.receiptPayload] at ih ⊢
      omega

/-- Complete theorem-cache storage is bounded by the original emitted graph,
with full hypotheses, axiom dependencies and type/name payloads retained. -/
theorem checked_theoremCache_length (definition : CalculusLanguageDef)
    {state : ProofExecution.State}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state) :
    (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
      SyntaxEncoding.theoremCodec state.cache)).length ≤
        192 * graphWeight StorageSize.receiptPayload state.receipts.toList +
          state.receipts.size * (state.receipts.size + 3) + 1 := by
  have conclusions := DerivationGraph.replayFrom_toList
    (ruleWitness (policy (inferenceRules definition))) checked
  have same : state.cache.toList = state.receipts.toList.map (fun node => node.conclusion) := by
    simpa only [ruleWitness, Array.toList_empty, List.nil_append] using conclusions
  have stored := SharedReferenceExecution.EncodedTable.table_length_bound
    (SharedReferenceExecution.EncodedTable.value SyntaxEncoding.theoremCodec) 0 state.cache.toList
  have words : (state.cache.toList.map fun out =>
      (SharedReferenceExecution.EncodedTable.value SyntaxEncoding.theoremCodec out).length).sum ≤
        192 * graphWeight StorageSize.receiptPayload state.receipts.toList := by
    rw [same]
    simpa only [List.map_map, Function.comp_def] using theoremWords_length state.receipts.toList
  have counted := checked_cache_size definition checked
  simp only [Array.length_toList, Nat.zero_add] at stored
  change (SharedReferenceExecution.table (SharedReferenceExecution.EncodedTable.rows
      SyntaxEncoding.theoremCodec state.cache)).length ≤ _ at stored
  rw [counted] at stored
  omega

/-- The emitter obtains a complete original premise theorem from physical
cache bytes. The clock includes the full stored primitive prefix. -/
def checked_theoremReferenceOutputs (definition : CalculusLanguageDef)
    {state : ProofExecution.State}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state) (query : Nat) :
    let payload := (SharedReferenceExecution.naturalKey query).length +
      192 * graphWeight StorageSize.receiptPayload state.receipts.toList +
        state.receipts.size * (state.receipts.size + 3) + 2
    TM2OutputsInTime SharedReferenceExecution.machine
      (SharedReferenceExecution.EncodedTable.queryPacket SyntaxEncoding.theoremCodec state.cache query)
      (some (SharedReferenceExecution.output
        (state.cache[query]?.map (SharedReferenceExecution.EncodedTable.value SyntaxEncoding.theoremCodec))))
      (4 * payload ^ 2 + 20 * payload + 20) := by
  have run := SharedReferenceExecution.EncodedTable.referenceOutputs
    SyntaxEncoding.theoremCodec state.cache query
  have stored := checked_theoremCache_length definition checked
  have packet := SharedReferenceExecution.packet_length (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows SyntaxEncoding.theoremCodec state.cache)
  have inputBound : (SharedReferenceExecution.EncodedTable.queryPacket
      SyntaxEncoding.theoremCodec state.cache query).length ≤
        (SharedReferenceExecution.naturalKey query).length +
          192 * graphWeight StorageSize.receiptPayload state.receipts.toList +
            state.receipts.size * (state.receipts.size + 3) + 2 := by
    change (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query) _).length ≤ _
    omega
  dsimp only
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  nlinarith [Nat.pow_le_pow_left inputBound 2]


/-- Complete source claims are recovered by the joined resolver and physical
triple decoder. The clock includes every stored goal word. -/
def decodedClaimReferenceOutputs (goals : List Pattern) (query : Nat) :
    let payload := (SharedReferenceExecution.naturalKey query).length +
      222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) + 2
    TM2OutputsInTime SharedReferenceExecution.EncodedTable.decodedMachine
      (SharedReferenceExecution.EncodedTable.queryPacket CertificateDataEncoding.patternCodec
        goals.toArray query)
      (some (SharedReferenceExecution.EncodedTable.decodedOutput
        CertificateDataEncoding.patternCodec goals[query]?))
      (4 * payload ^ 2 + 30 * payload + 50) := by
  have run := SharedReferenceExecution.EncodedTable.decodedReferenceOutputs
    CertificateDataEncoding.patternCodec goals.toArray query
  have stored := claimTable_length goals
  have packet := SharedReferenceExecution.packet_length (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows CertificateDataEncoding.patternCodec goals.toArray)
  have inputBound : (SharedReferenceExecution.EncodedTable.queryPacket
      CertificateDataEncoding.patternCodec goals.toArray query).length ≤
        (SharedReferenceExecution.naturalKey query).length +
          222 * PatternTokens.listWeight goals + goals.length * (goals.length + 3) + 2 := by
    change (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query) _).length ≤ _
    omega
  dsimp only
  simp only [List.getElem?_toArray] at run
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  nlinarith [Nat.pow_le_pow_left inputBound 2]

/-- A successful physically recovered claim selects its original checked HOL
root. The byte-level observation is linked to the existing context invariant. -/
theorem represented_decoded_lookup {state : ProofExecution.State}
    {goals : List Pattern} {roots : List Nat} (represented : Represents state goals roots)
    {query : Nat} {goal : Pattern}
    (found : SharedReferenceExecution.EncodedTable.decodedOutput
      CertificateDataEncoding.patternCodec goals[query]? =
        1 :: Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith
          CertificateDataEncoding.patternCodec goal) :
    ∃ root out, roots[query]? = some root ∧ state.cache[root]? = some out ∧ hasClaim goal out = true := by
  have stored := (SharedReferenceExecution.EncodedTable.decodedOutput_some_iff
    CertificateDataEncoding.patternCodec goals[query]? goal).mp found
  exact represented_lookup represented stored

/-- Complete original premise theorems reach the primitive emitter as original
codec words, after the actual cache lookup, handoff and bit recovery. -/
def checked_decodedTheoremReferenceOutputs (definition : CalculusLanguageDef)
    {state : ProofExecution.State}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state) (query : Nat) :
    let payload := (SharedReferenceExecution.naturalKey query).length +
      192 * graphWeight StorageSize.receiptPayload state.receipts.toList +
        state.receipts.size * (state.receipts.size + 3) + 2
    TM2OutputsInTime SharedReferenceExecution.EncodedTable.decodedMachine
      (SharedReferenceExecution.EncodedTable.queryPacket SyntaxEncoding.theoremCodec state.cache query)
      (some (SharedReferenceExecution.EncodedTable.decodedOutput SyntaxEncoding.theoremCodec
        state.cache[query]?))
      (4 * payload ^ 2 + 30 * payload + 50) := by
  have run := SharedReferenceExecution.EncodedTable.decodedReferenceOutputs
    SyntaxEncoding.theoremCodec state.cache query
  have stored := checked_theoremCache_length definition checked
  have packet := SharedReferenceExecution.packet_length (SharedReferenceExecution.naturalKey query)
    (SharedReferenceExecution.EncodedTable.rows SyntaxEncoding.theoremCodec state.cache)
  have inputBound : (SharedReferenceExecution.EncodedTable.queryPacket
      SyntaxEncoding.theoremCodec state.cache query).length ≤
        (SharedReferenceExecution.naturalKey query).length +
          192 * graphWeight StorageSize.receiptPayload state.receipts.toList +
            state.receipts.size * (state.receipts.size + 3) + 2 := by
    change (SharedReferenceExecution.packet (SharedReferenceExecution.naturalKey query) _).length ≤ _
    omega
  dsimp only
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  nlinarith [Nat.pow_le_pow_left inputBound 2]

open SharedReferenceExecution

def chainedCachePayload (state : ProofExecution.State) (roots : List Nat) (query : Nat) : Nat :=
  (naturalKey query).length + roots.length*(roots.length+state.receipts.size+3) +
    192*graphWeight StorageSize.receiptPayload state.receipts.toList +
      state.receipts.size*(state.receipts.size+3)+6

/-- Chronological source-root and complete theorem resolution charge both
physical tables, including every emitted primitive payload and duplicate root. -/
noncomputable def represented_chainedReferenceOutputs (definition : CalculusLanguageDef)
    {state : ProofExecution.State} {goals : List Pattern} {roots : List Nat}
    (checked : BuildChecked (policy (inferenceRules definition)) [] state)
    (represented : Represents state goals roots) (query : Nat) :
    TM2OutputsInTime ChainedCache.machine
      (ChainedCache.sourcePacket SyntaxEncoding.theoremCodec roots.toArray state.cache query)
      (some (EncodedTable.decodedOutput SyntaxEncoding.theoremCodec
        (ChainedCache.selected roots.toArray state.cache query)))
      (400*(chainedCachePayload state roots query+1)^2) := by
  have executed := ChainedCache.outputs SyntaxEncoding.theoremCodec roots.toArray state.cache query
  have sourceRows := represented_rootTable_length definition checked represented
  have targetRows := checked_theoremCache_length definition checked
  have inputLength := ChainedCache.sourcePacket_length SyntaxEncoding.theoremCodec roots.toArray state.cache query
  have queryLength := packet_length (naturalKey query) (indexed roots.toArray)
  have inputBound : (ChainedCache.sourcePacket SyntaxEncoding.theoremCodec roots.toArray state.cache query).length ≤
      chainedCachePayload state roots query := by
    change (referencePacket roots.toArray query).length = _ at queryLength
    unfold chainedCachePayload
    omega
  refine ⟨executed.toEvalsTo,executed.steps_le_m.trans ?_⟩
  nlinarith [Nat.pow_le_pow_left (Nat.add_le_add_right inputBound 1) 2]

/-- A genuine source claim follows the original context relation through both
cache lookups and the physical decoder to its complete original HOL theorem. -/
theorem represented_chained_lookup {state : ProofExecution.State}
    {goals : List Pattern} {roots : List Nat} (represented : Represents state goals roots)
    {query : Nat} {goal : Pattern} (found : goals[query]? = some goal) :
    ∃ root out, roots[query]? = some root ∧ state.cache[root]? = some out ∧
      hasClaim goal out = true ∧
      EncodedTable.decodedOutput SyntaxEncoding.theoremCodec
        (ChainedCache.selected roots.toArray state.cache query) =
          1 :: Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith SyntaxEncoding.theoremCodec out := by
  obtain ⟨root,out,rootFound,stored,claim⟩ := represented_lookup represented found
  refine ⟨root,out,rootFound,stored,claim,?_⟩
  have selected : ChainedCache.selected roots.toArray state.cache query = some out := by
    simp only [ChainedCache.selected,List.getElem?_toArray,rootFound,Option.bind_some,stored]
  exact (EncodedTable.decodedOutput_some_iff _ _ _).mpr selected

/-- The actual full-word guard is applied to the source context retained by
the original compiler. Both present and absent entries share one program. -/
noncomputable def storedClaimGuardOutputs (goals : List Pattern) (query : Nat) (expected : Pattern) :
    TM2OutputsInTime EncodedTable.ReferenceCheck.machine
      (EncodedTable.ReferenceCheck.sourcePacket CertificateDataEncoding.patternCodec goals.toArray query expected)
      (some [decide (goals[query]? = some expected)])
      (250*((EncodedTable.ReferenceCheck.sourcePacket CertificateDataEncoding.patternCodec
        goals.toArray query expected).length+1)^2) := by
  simpa only [List.getElem?_toArray] using
    EncodedTable.ReferenceCheck.outputs CertificateDataEncoding.patternCodec goals.toArray query expected

/-- A successful executed guard supplies the original claim lookup needed by
the existing representation invariant; a physical address is not enough. -/
theorem represented_executedGuard_lookup {state : ProofExecution.State}
    {goals : List Pattern} {roots : List Nat}
    (represented : Represents state goals roots) {query : Nat} {expected : Pattern}
    (accepted : TM2Outputs EncodedTable.ReferenceCheck.machine
      (EncodedTable.ReferenceCheck.sourcePacket CertificateDataEncoding.patternCodec goals.toArray query expected)
      (some [true])) :
    ∃ root out, roots[query]? = some root ∧ state.cache[root]? = some out ∧
      hasClaim expected out = true ∧
      EncodedTable.decodedOutput SyntaxEncoding.theoremCodec
        (ChainedCache.selected roots.toArray state.cache query) =
          1 :: Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith SyntaxEncoding.theoremCodec out := by
  have unique := Mettapedia.Computability.StackMachineComposition.outputs_unique accepted
    (storedClaimGuardOutputs goals query expected).toTM2Outputs
  have stored : goals[query]? = some expected := of_decide_eq_true (by simpa only [List.cons.injEq, and_true] using unique.symm)
  exact represented_chained_lookup represented stored

/-- A wrong or absent original judgment cannot pass the same executed guard. -/
theorem wrongOrAbsentGuard_refused (goals : List Pattern) (query : Nat) (expected : Pattern)
    (different : goals[query]? ≠ some expected) :
    ¬ Nonempty (TM2Outputs EncodedTable.ReferenceCheck.machine
      (EncodedTable.ReferenceCheck.sourcePacket CertificateDataEncoding.patternCodec goals.toArray query expected)
      (some [true])) := by
  rintro ⟨accepted⟩
  have unique := Mettapedia.Computability.StackMachineComposition.outputs_unique accepted
    (storedClaimGuardOutputs goals query expected).toTM2Outputs
  have stored : goals[query]? = some expected := of_decide_eq_true (by simpa only [List.cons.injEq, and_true] using unique.symm)
  exact different stored


end ExecutedRootCache

end Mettapedia.Languages.HOLLight.InferenceCompilerSize
