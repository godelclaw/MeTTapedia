import Mettapedia.Languages.MM0.Translation.DerivationWeight
import Mettapedia.Languages.MM0.Kernel.ProofSharing
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# MM0 with saved proofs and the first-order calculi with lemmas

A proof graph shares its conclusions: a node cites earlier nodes, and one conclusion may be
cited many times. Unfolding a graph into a tree can make it exponentially larger, so sharing
has to survive translation.

* **A calculus with lemmas.** On a first-order calculus of the inference checker, a
  certificate with sharing is a list of lemmas, each a pattern with an open proof from the
  patterns before it, and an open proof of the claim from all of them (`lemmaChecker`).
  Every accepted claim has a derivation (`lemmaChecker_sound`).
* **MM0 with saved proofs.** MM0 shares conclusions through saved proofs: each is checked
  with the earlier saved conclusions as local hypotheses, and a root checked against all of
  them is sound in the original scope (`Kernel.SavedWitnessesChecked.root_sound`,
  `savedChecker_sound`).
* **The p-simulation.** A entry compiles to one saved proof through the presentation of the
  calculus, as a closed proof does in `CalculusSimulation`: its open proof encodes to an
  open tree of the presentation (`encodeOpen_accepted`), and the tree compiles to an MM0
  witness over the hypotheses that render the earlier lemmas (`compileOpen_checked`). The
  sizes add up lemma by lemma. `lemmaSimulation` records a linear certificate
  bound and a linear declared cost account; its operational realization is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.CalculusSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules FirstOrderCertificates
open CertificateSimulation (patternSize patternSizes rawSize rawSizes compileTime compileFactor)
open Polynomial

/-! ## Open proofs: their weight, and as trees of the presentation -/

mutual
  /-- The size of an open proof: a premise hole counts once. -/
  def openWeight : RawOpenProof → ℕ
    | .premise _ => 1
    | .node ruleInstance children => weights ruleInstance.arguments + openWeights children + 1

  def openWeights : List RawOpenProof → ℕ
    | [] => 0
    | proof :: proofs => openWeight proof + openWeights proofs
end

theorem one_le_openWeight (proof : RawOpenProof) : 1 ≤ openWeight proof := by
  cases proof <;> simp [openWeight]

mutual
  /-- An open proof of the checker as an open tree of the presentation. -/
  def encodeOpen : RawOpenProof → RawOpenProof
    | .premise index => .premise index
    | .node ruleInstance children =>
        .node { ruleId := ruleInstance.ruleId, arguments := ruleInstance.arguments.map patP }
          (encodeOpens children)

  def encodeOpens : List RawOpenProof → List RawOpenProof
    | [] => []
    | proof :: proofs => encodeOpen proof :: encodeOpens proofs
end

mutual
  theorem rawSize_encodeOpen (proof : RawOpenProof) : rawSize (encodeOpen proof) ≤ 22 * openWeight proof := by
    cases proof with
    | premise index => simp [encodeOpen, openWeight, rawSize]
    | node ruleInstance children =>
        have arguments := patternSizes_map_patP ruleInstance.arguments
        have rest := rawSizes_encodeOpens children
        rw [encodeOpen, openWeight]
        simp only [rawSize]
        omega

  theorem rawSizes_encodeOpens (proofs : List RawOpenProof) :
      rawSizes (encodeOpens proofs) ≤ 22 * openWeights proofs := by
    cases proofs with
    | nil => simp [encodeOpens, rawSizes, openWeights]
    | cons proof proofs =>
        have first := rawSize_encodeOpen proof
        have rest := rawSizes_encodeOpens proofs
        rw [encodeOpens, openWeights]
        simp only [rawSizes]
        omega
end

/-- The hypotheses of the presentation that render a context of judgments. -/
def holdsContext (context : List Pattern) : List Pattern := context.map fun premise => holdsP (patP premise)

mutual
  /-- **An open proof the checker accepts encodes to an open tree the presentation accepts**,
  with the context rendered as hypotheses. -/
  theorem encodeOpen_accepted {definition : ValidatedCalculusLanguageDef}
      (firstOrder : FirstOrderCalculus definition.1) (context : List Pattern) :
      ∀ (goal : Pattern) (proof : RawOpenProof), checkOpenRaw definition context goal proof = true →
        SortedFirstOrderRules.Checks universalLanguage (encodedRules definition.1) [] (holdsContext context)
          (encodeOpen proof) (holdsP (patP goal))
    | goal, .premise index, accepted => by
        rw [checkOpenRaw] at accepted
        cases found : context[index]? with
        | none => simp [found] at accepted
        | some premise =>
            simp only [found, decide_eq_true_eq] at accepted
            subst accepted
            rw [encodeOpen]
            exact .premise (by simp [holdsContext, found])
    | goal, .node ruleInstance children, accepted => by
        rw [checkOpenRaw] at accepted
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [instantiated] at accepted
        | some result =>
            obtain ⟨premises, conclusion⟩ := result
            simp only [instantiated, Bool.and_eq_true, decide_eq_true_eq] at accepted
            obtain ⟨concluded, childrenAccepted⟩ := accepted
            obtain ⟨rule, lookup, valid, schemas, schema⟩ := instantiateRule?_some instantiated
            have member := lookupRule?_member lookup
            have formals := metavariables_eq firstOrder member
            have arity : ruleInstance.arguments.length = (ruleNames rule).length := by
              have counted := argumentsValidAt_length valid
              rw [formals, List.length_map] at counted
              exact counted.symm
            have premiseSchemas := firstOrder.premiseSchemas rule member
            have conclusionSchema := firstOrder.conclusionSchema rule member
            rw [formals, instantiateSchemas?, instantiateSchemasAt?_eq arity premiseSchemas,
              Option.some.injEq] at schemas
            rw [formals, instantiateSchema?, instantiateSchemaAt?_eq arity conclusionSchema,
              Option.some.injEq] at schema
            have agree : ∀ name ∈ ruleNames rule,
                bindingValue ((ruleNames rule).zip (ruleInstance.arguments.map patP)) name =
                  patP (bindingValue ((ruleNames rule).zip ruleInstance.arguments) name) :=
              fun name nameMember => bindingValue_map patP nameMember arity
            have conclusionEq :
                (encodeRule rule).row.instConclusion (ruleInstance.arguments.map patP) =
                  holdsP (patP goal) := by
              rw [encodeRule_instConclusion, applyBindings_encodeSchema _ conclusionSchema,
                encodeWith_eq_patP agree conclusionSchema, schema, concluded]
            have premisesEq :
                (encodeRule rule).row.instPremises (ruleInstance.arguments.map patP) =
                  premises.map fun premise => holdsP (patP premise) := by
              rw [instPremises_encodeWith rfl premiseSchemas, ← schemas, substSchemas_eq_map,
                List.map_map]
              apply List.map_congr_left
              intro premise premiseMember
              simp only [Function.comp_apply]
              rw [encodeWith_eq_patP agree (premiseSchemas.member premiseMember)]
            rw [← conclusionEq, encodeOpen]
            exact SortedFirstOrderRules.Checks.rule
              (by rw [lookupRule?_encoded, lookup]; rfl)
              (by simpa [encodeRule] using arity)
              (by simpa [encodeRule] using forall₂_patP arity)
              (fun argument argumentMember => by
                obtain ⟨source, _, rfl⟩ := List.mem_map.mp argumentMember
                exact matchCorrect_patP source)
              (by
                rw [premisesEq]
                exact encodeOpens_accepted firstOrder context premises children childrenAccepted)

  theorem encodeOpens_accepted {definition : ValidatedCalculusLanguageDef}
      (firstOrder : FirstOrderCalculus definition.1) (context : List Pattern) :
      ∀ (premises : List Pattern) (proofs : List RawOpenProof),
        checkOpenRawChildren definition context premises proofs = true →
          SortedFirstOrderRules.ChecksList universalLanguage (encodedRules definition.1) [] (holdsContext context)
            (encodeOpens proofs) (premises.map fun premise => holdsP (patP premise))
    | [], [], _ => .nil
    | premise :: premises, proof :: proofs, accepted => by
        rw [checkOpenRawChildren, Bool.and_eq_true] at accepted
        rw [encodeOpens, List.map_cons]
        exact .cons (encodeOpen_accepted firstOrder context premise proof accepted.1)
          (encodeOpens_accepted firstOrder context premises proofs accepted.2)
    | [], _ :: _, accepted => by simp [checkOpenRawChildren] at accepted
    | _ :: _, [], accepted => by simp [checkOpenRawChildren] at accepted
end

/-! ## The weight of an open derivation's judgments -/

mutual
  /-- The summed weights of the judgments of an open derivation, one more for each; a premise
  hole counts its judgment. -/
  def openJudgmentWeight {definition : ValidatedCalculusLanguageDef} {context : List Pattern} {goal : Pattern} :
      OpenDerivation definition context goal → ℕ
    | .assumption _ => weight goal + 1
    | .byRule _ _ children => weight goal + 1 + openJudgmentWeights children

  def openJudgmentWeights {definition : ValidatedCalculusLanguageDef} {context premises : List Pattern} :
      OpenDerivationList definition context premises → ℕ
    | .nil => 0
    | .cons head tail => openJudgmentWeight head + openJudgmentWeights tail
end

mutual
  /-- **An open certificate weighs at most `2A + 1` times its judgments**, for a calculus whose
  rules cover their formals and have at most `A` of them. -/
  theorem openWeight_eraseOpen_le {definition : ValidatedCalculusLanguageDef} {bound : ℕ}
      (covering : CoveringCalculus definition bound) :
      ∀ {context : List Pattern} {goal : Pattern} (derivation : OpenDerivation definition context goal),
        openWeight derivation.eraseOpen + bound * (weight goal + 1) ≤ (2 * bound + 1) * openJudgmentWeight derivation
    | _, _, .assumption index => by
        rw [OpenDerivation.eraseOpen, openWeight, openJudgmentWeight]
        nlinarith
    | _, goal, @OpenDerivation.byRule _ _ ruleInstance premises _
        (.intro rule lookup valid _ premisesInstantiate conclusionInstantiates) children => by
        obtain ⟨covers, small⟩ := covering rule (rule_member_of_lookup lookup)
        have lengths := argumentsValidAt_length valid
        have each := argument_weight_le covers lengths premisesInstantiate conclusionInstantiates
        have argumentsBound := weights_le_of_forall each
        have childrenBound := openWeights_eraseOpen_le covering children
        have count : ruleInstance.arguments.length ≤ bound := by omega
        rw [OpenDerivation.eraseOpen, openWeight, openJudgmentWeight]
        have product : ruleInstance.arguments.length * (weight goal + weights premises + 1) ≤
            bound * (weight goal + weights premises + 1) := Nat.mul_le_mul_right _ count
        nlinarith [product, argumentsBound, childrenBound]

  theorem openWeights_eraseOpen_le {definition : ValidatedCalculusLanguageDef} {bound : ℕ}
      (covering : CoveringCalculus definition bound) :
      ∀ {context premises : List Pattern} (derivations : OpenDerivationList definition context premises),
        openWeights (OpenDerivationList.eraseOpen derivations) + bound * weights premises ≤
          (2 * bound + 1) * openJudgmentWeights derivations
    | _, _, .nil => by simp [OpenDerivationList.eraseOpen, openWeights, weights, openJudgmentWeights]
    | _, _, .cons head tail => by
        have headBound := openWeight_eraseOpen_le covering head
        have tailBound := openWeights_eraseOpen_le covering tail
        rw [OpenDerivationList.eraseOpen, openWeights, weights, openJudgmentWeights]
        nlinarith [headBound, tailBound]
end

mutual
  @[simp] theorem openJudgmentWeight_ofClosed {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
      {goal : Pattern} (derivation : InferenceChecker.Derivation definition goal) :
      openJudgmentWeight (OpenDerivation.ofClosed (context := context) derivation) = judgmentWeight derivation := by
    cases derivation with
    | byRule ruleInstance application children =>
        rw [OpenDerivation.ofClosed, openJudgmentWeight, judgmentWeight, openJudgmentWeights_ofClosed]

  @[simp] theorem openJudgmentWeights_ofClosed {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
      {premises : List Pattern} (derivations : DerivationList definition premises) :
      openJudgmentWeights (OpenDerivationList.ofClosed (context := context) derivations) =
        judgmentWeights derivations := by
    cases derivations with
    | nil => rw [OpenDerivationList.ofClosed, openJudgmentWeights, judgmentWeights]
    | cons head tail =>
        rw [OpenDerivationList.ofClosed, openJudgmentWeights, judgmentWeights, openJudgmentWeight_ofClosed,
          openJudgmentWeights_ofClosed]
end

/-! ## Closing open derivations -/

theorem nonempty_derivationList {definition : ValidatedCalculusLanguageDef} :
    ∀ {premises : List Pattern}, (∀ premise ∈ premises, Nonempty (InferenceChecker.Derivation definition premise)) →
      Nonempty (DerivationList definition premises)
  | [], _ => ⟨.nil⟩
  | premise :: premises, derived => by
      obtain ⟨head⟩ := derived premise (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨tail⟩ := nonempty_derivationList fun other member => derived other (List.mem_cons_of_mem _ member)
      exact ⟨.cons head tail⟩

/-- An open proof the checker accepts, from derivable premises, gives a derivation. -/
theorem derivation_of_checkOpenRaw {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} {proof : RawOpenProof} (accepted : checkOpenRaw definition context goal proof = true)
    (premises : ∀ premise ∈ context, Nonempty (InferenceChecker.Derivation definition premise)) :
    Nonempty (InferenceChecker.Derivation definition goal) := by
  obtain ⟨derivation, -⟩ := checkOpenRaw_exact_derivation accepted
  exact OpenDerivation.sound_of_ruleApplications (fun pattern => Nonempty (InferenceChecker.Derivation definition pattern))
    (fun ruleInstance premises conclusion application derived => by
      obtain ⟨children⟩ := nonempty_derivationList derived
      exact ⟨.byRule ruleInstance application children⟩)
    premises derivation

/-! ## A first-order calculus with lemmas -/

/-- Lemmas: each a pattern with an open proof from the patterns before it. -/
abbrev Lemmas := List (Pattern × RawOpenProof)

/-- Check every entry from the patterns before it. -/
def checkLemmas (definition : ValidatedCalculusLanguageDef) : List Pattern → Lemmas → Bool
  | _, [] => true
  | earlier, (goal, proof) :: rest =>
      checkOpenRaw definition earlier goal proof && checkLemmas definition (earlier ++ [goal]) rest

/-- A certificate with sharing: the lemmas and an open proof of the claim from all of them. -/
abbrev LemmaCertificate := Lemmas × RawOpenProof

/-- The size of the lemmas: their patterns and their proofs. -/
def lemmasWeight : Lemmas → ℕ
  | [] => 0
  | (goal, proof) :: rest => weight goal + openWeight proof + lemmasWeight rest

theorem checkLemmas_sound {definition : ValidatedCalculusLanguageDef} :
    ∀ {earlier : List Pattern} {lemmas : Lemmas}, checkLemmas definition earlier lemmas = true →
      (∀ premise ∈ earlier, Nonempty (InferenceChecker.Derivation definition premise)) →
      ∀ premise ∈ earlier ++ lemmas.map Prod.fst, Nonempty (InferenceChecker.Derivation definition premise)
  | earlier, [], _, derived => by simpa using derived
  | earlier, (goal, proof) :: rest, accepted, derived => by
      rw [checkLemmas, Bool.and_eq_true] at accepted
      have goalDerived := derivation_of_checkOpenRaw accepted.1 derived
      have extended : ∀ premise ∈ earlier ++ [goal], Nonempty (InferenceChecker.Derivation definition premise) := by
        intro premise member
        rcases List.mem_append.mp member with member | member
        · exact derived premise member
        · rw [List.mem_singleton.mp member]
          exact goalDerived
      have rested := checkLemmas_sound accepted.2 extended
      intro premise member
      apply rested
      simpa using member

section Checkers

variable {definition : ValidatedCalculusLanguageDef} (firstOrder : FirstOrderCalculus definition.1)

/-- The inference checker with lemmas, on first-order claims. -/
def lemmaChecker : SizedChecker FirstOrderClaim LemmaCertificate where
  check claim certificate :=
    checkLemmas definition [] certificate.1 &&
      checkOpenRaw definition (certificate.1.map Prod.fst) claim.1 certificate.2
  claimSize claim := (toSequent firstOrder claim).size
  certificateSize certificate := lemmasWeight certificate.1 + openWeight certificate.2

/-- **Every claim the checker with lemmas accepts has a derivation.** -/
theorem lemmaChecker_sound {claim : FirstOrderClaim} {certificate : LemmaCertificate}
    (accepted : (lemmaChecker firstOrder).check claim certificate = true) :
    Nonempty (InferenceChecker.Derivation definition claim.1) := by
  simp only [lemmaChecker, Bool.and_eq_true] at accepted
  have lemmasDerived := checkLemmas_sound accepted.1 (fun premise member => by cases member)
  exact derivation_of_checkOpenRaw accepted.2 (fun premise member => lemmasDerived premise (by simpa using member))

/-! ## MM0 with saved proofs -/

/-- The MM0 theory of the calculus. -/
abbrev savedTheory := (presentation definition.1 firstOrder).theory

/-- Check every saved proof with the earlier saved conclusions as hypotheses. -/
def checkSaved : List Preterm → List (Preterm × ProofWitness) → Bool
  | _, [] => true
  | hypotheses, (expression, witness) :: rest =>
      ProofWitness.check (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
          (savedTheory firstOrder).theoremSignature [] hypotheses witness expression &&
        checkSaved (hypotheses ++ [expression]) rest

/-- A certificate of MM0 with saved proofs: the saved proofs and the root. -/
abbrev SavedCertificate := List (Preterm × ProofWitness) × ProofWitness

/-- The size of saved proofs: their conclusions and their witnesses. -/
def savedSize : List (Preterm × ProofWitness) → ℕ
  | [] => 0
  | (expression, witness) :: rest => expression.size + Cost.proofSize witness + savedSize rest

/-- The MM0 kernel with saved proofs, on the rendering of first-order claims. -/
def savedChecker : SizedChecker FirstOrderClaim SavedCertificate where
  check claim certificate :=
    checkSaved firstOrder [] certificate.1 &&
      ProofWitness.check (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
        (savedTheory firstOrder).theoremSignature [] (certificate.1.map Prod.fst) certificate.2 (holdsTerm claim.1)
  claimSize claim := (toSequent firstOrder claim).size
  certificateSize certificate := savedSize certificate.1 + Cost.proofSize certificate.2

theorem checkSaved_checked {before : List (Preterm × ProofWitness)}
    (checked : SavedWitnessesChecked (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
      (savedTheory firstOrder).theoremSignature [] [] before) :
    ∀ {rest : List (Preterm × ProofWitness)}, checkSaved firstOrder (before.map Prod.fst) rest = true →
      SavedWitnessesChecked (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
        (savedTheory firstOrder).theoremSignature [] [] (before ++ rest)
  | [], _ => by simpa using checked
  | (expression, witness) :: rest, accepted => by
      rw [checkSaved, Bool.and_eq_true] at accepted
      have recorded := SavedWitnessesChecked.record checked (by simpa using accepted.1)
      have rested := checkSaved_checked recorded (rest := rest) (by simpa using accepted.2)
      simpa using rested

/-- **The MM0 kernel with saved proofs is sound in the original scope.** -/
theorem savedChecker_sound {claim : FirstOrderClaim} {certificate : SavedCertificate}
    (accepted : (savedChecker firstOrder).check claim certificate = true) :
    Kernel.Derives (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
      (savedTheory firstOrder).theoremSignature [] [] (holdsTerm claim.1) := by
  simp only [savedChecker, Bool.and_eq_true] at accepted
  have checked := checkSaved_checked firstOrder (before := []) .nil (by simpa using accepted.1)
  exact SavedWitnessesChecked.root_sound (by simpa using checked) (by simpa using accepted.2)

/-! ## Compiling lemmas into saved proofs -/

/-- An open proof as an MM0 witness, through the presentation. -/
def compileOpen (proof : RawOpenProof) : ProofWitness :=
  (compile? (presentation definition.1 firstOrder) (encodeOpen proof)).getD (.hyp 0)

/-- A entry as a saved proof. -/
def compileLemma (entry : Pattern × RawOpenProof) : Preterm × ProofWitness :=
  (holdsTerm entry.1, compileOpen firstOrder entry.2)

theorem holdsContext_encodes (context : List Pattern) :
    List.Forall₂ (Encodes universalNames) (holdsContext context) (context.map holdsTerm) := by
  induction context with
  | nil => exact .nil
  | cons premise context ih => exact .cons (encodes_holds premise) ih

/-- **A compiled open proof is accepted over the hypotheses that render its context.** -/
theorem compileOpen_checked {context : List Pattern} {goal : Pattern} {proof : RawOpenProof}
    (accepted : checkOpenRaw definition context goal proof = true) :
    ProofWitness.check (savedTheory firstOrder).termSignature (savedTheory firstOrder).definitionSignature
      (savedTheory firstOrder).theoremSignature [] (context.map holdsTerm) (compileOpen firstOrder proof)
        (holdsTerm goal) = true := by
  have encoded := encodeOpen_accepted firstOrder context goal proof accepted
  obtain ⟨sameLanguage, -, sameRules⟩ := presentation_retains firstOrder
  have proved : SortedFirstOrderRules.proof? (presentation definition.1 firstOrder).syntaxSignature.language
      (presentation definition.1 firstOrder).rules [] (holdsContext context) (encodeOpen proof) =
        some (holdsP (patP goal)) := by
    rw [sameLanguage, sameRules]
    exact SortedFirstOrderRules.Checks.eval encoded
  have checked := (checkCompiled_iff (presentation := presentation definition.1 firstOrder) (bound := [])
    (context := []) (by rw [Signature.sorts, sameLanguage]; exact .nil)
    (by rw [Signature.names, sameLanguage]; exact holdsContext_encodes context)
    (by rw [Signature.names, sameLanguage]; exact encodes_holds goal)).mpr proved
  unfold checkCompiled at checked
  unfold compileOpen
  cases compiled : compile? (presentation definition.1 firstOrder) (encodeOpen proof) with
  | none => simp [compiled] at checked
  | some witness => simpa [compiled] using checked

theorem checkSaved_compiled :
    ∀ {earlier : List Pattern} {lemmas : Lemmas}, checkLemmas definition earlier lemmas = true →
      checkSaved firstOrder (earlier.map holdsTerm) (lemmas.map (compileLemma firstOrder)) = true
  | earlier, [], _ => rfl
  | earlier, (goal, proof) :: rest, accepted => by
      rw [checkLemmas, Bool.and_eq_true] at accepted
      have rested := checkSaved_compiled (earlier := earlier ++ [goal]) accepted.2
      rw [List.map_cons, checkSaved, Bool.and_eq_true]
      exact ⟨compileOpen_checked firstOrder accepted.1, by simpa [compileLemma] using rested⟩

/-! ## Sizes and time -/

theorem proofSize_compileOpen (proof : RawOpenProof) :
    Cost.proofSize (compileOpen firstOrder proof) ≤ 44 * openWeight proof := by
  have tree := rawSize_encodeOpen proof
  have one := one_le_openWeight proof
  unfold compileOpen
  cases compiled : compile? (presentation definition.1 firstOrder) (encodeOpen proof) with
  | none => simp [Cost.proofSize]; omega
  | some witness =>
      have := CertificateSimulation.compile_size (encodeOpen proof) compiled
      simp only [Option.getD_some]
      omega

theorem size_holdsTerm (pattern : Pattern) : (holdsTerm pattern).size ≤ 46 * weight pattern := by
  have encoded := (encode_eq_some_iff universalNames _ _).mpr (encodes_holds pattern)
  have bound := CertificateSimulation.encode_size encoded
  have patterns := patternSize_patP pattern
  have positive : 1 ≤ weight pattern := by
    cases pattern <;> simp [weight]
    omega
  simp only [holdsP, patternSize, patternSizes] at bound
  omega

theorem savedSize_compiled : ∀ lemmas : Lemmas,
    savedSize (lemmas.map (compileLemma firstOrder)) ≤ 46 * lemmasWeight lemmas
  | [] => by simp [savedSize, lemmasWeight]
  | (goal, proof) :: rest => by
      have first := size_holdsTerm goal
      have second := proofSize_compileOpen firstOrder proof
      have rested := savedSize_compiled rest
      simp only [List.map_cons, savedSize, compileLemma, lemmasWeight]
      omega

/-- The time to compile one entry: encoding its pattern and compiling its proof. -/
def lemmaTime (entry : Pattern × RawOpenProof) : ℕ :=
  patternSize (holdsP (patP entry.1)) + rawSize (encodeOpen entry.2) +
    compileTime (presentation definition.1 firstOrder) (encodeOpen entry.2) + openWeight entry.2

theorem lemmaTime_le (entry : Pattern × RawOpenProof) :
    lemmaTime firstOrder entry ≤
      (compileFactor (presentation definition.1 firstOrder) * 22 + 46) * (weight entry.1 + openWeight entry.2) := by
  have patterns := patternSize_patP entry.1
  have tree := rawSize_encodeOpen entry.2
  have compiled := CertificateSimulation.compileTime_le (presentation definition.1 firstOrder) (encodeOpen entry.2)
  have scaled : compileFactor (presentation definition.1 firstOrder) * rawSize (encodeOpen entry.2) ≤
      compileFactor (presentation definition.1 firstOrder) * 22 * openWeight entry.2 := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ tree
  simp only [lemmaTime, holdsP, patternSize, patternSizes]
  nlinarith

def lemmasTime : Lemmas → ℕ
  | [] => 0
  | entry :: rest => lemmaTime firstOrder entry + lemmasTime rest

theorem lemmasTime_le : ∀ lemmas : Lemmas,
    lemmasTime firstOrder lemmas ≤ (compileFactor (presentation definition.1 firstOrder) * 22 + 46) * lemmasWeight lemmas
  | [] => by simp [lemmasTime]
  | (goal, proof) :: rest => by
      have first := lemmaTime_le firstOrder (goal, proof)
      have rested := lemmasTime_le rest
      simp only [lemmasTime, lemmasWeight] at *
      nlinarith

/-- Each first-order lemma compiles to one saved MM0 proof, with a certificate
bound of forty-six times its size and a linear declared cost account.
The account is not an operational execution bound. -/
def lemmaSimulation : PSimulation (savedChecker firstOrder) (lemmaChecker firstOrder) where
  translate _ certificate := (certificate.1.map (compileLemma firstOrder), compileOpen firstOrder certificate.2)
  preserves claim certificate accepted := by
    simp only [lemmaChecker, Bool.and_eq_true] at accepted
    simp only [savedChecker, Bool.and_eq_true]
    refine ⟨by simpa using checkSaved_compiled firstOrder (earlier := []) accepted.1, ?_⟩
    have root := compileOpen_checked firstOrder accepted.2
    simpa [compileLemma, List.map_map, Function.comp_def] using root
  sizeBound := ⟨C 46 * X, fun input => by
    have lemmas := savedSize_compiled firstOrder input.2.1
    have root := proofSize_compileOpen firstOrder input.2.2
    simp only [savedChecker, lemmaChecker, SizedChecker.inputSize, eval_mul, eval_C, eval_X]
    nlinarith⟩
  translationTime _ certificate :=
    lemmasTime firstOrder certificate.1 + rawSize (encodeOpen certificate.2) +
      compileTime (presentation definition.1 firstOrder) (encodeOpen certificate.2) + openWeight certificate.2
  timeBound := ⟨C (compileFactor (presentation definition.1 firstOrder) * 22 + 46) * X, fun input => by
    have lemmas := lemmasTime_le firstOrder input.2.1
    have tree := rawSize_encodeOpen input.2.2
    have compiled := CertificateSimulation.compileTime_le (presentation definition.1 firstOrder) (encodeOpen input.2.2)
    have scaled : compileFactor (presentation definition.1 firstOrder) * rawSize (encodeOpen input.2.2) ≤
        compileFactor (presentation definition.1 firstOrder) * 22 * openWeight input.2.2 := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ tree
    simp only [lemmaChecker, SizedChecker.inputSize, eval_mul, eval_C, eval_X]
    nlinarith⟩

end Checkers

end Mettapedia.Languages.MM0.Translation.CalculusSimulation
