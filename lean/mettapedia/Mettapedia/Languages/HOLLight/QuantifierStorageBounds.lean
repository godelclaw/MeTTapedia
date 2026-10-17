import Mettapedia.Languages.HOLLight.QuantifierExpansion
import Mettapedia.Languages.HOLLight.StorageSize
import Mettapedia.Languages.HOLLight.PrimitiveStorageBounds
import Mettapedia.Languages.HOLLight.EqualityStorageBounds

/-!
# Stored payload bounds for universal-instantiation certificates

The account includes all retained theorem hypotheses and axiom dependencies,
term and type provenance, request operands and source origins. The universal
body and its domain are measured as stored parts of the actual submitted
objects, rather than as an extra external size parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.QuantifierStorageBounds

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open QuantifierExpansion GraphExpansion EqualityExpansion PrimitiveTransport
open ProofExecution (Origin)
open DerivedRules (forallAppDB)

/-- The complete actual input payload for one universal-elimination block. -/
def inputUnits (input : Theorem) (argument : CanonicalTerm) (origin : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.canonical argument +
    HOLLight.StorageSize.origin origin

/-- A convenient typed account whose extra fields are already present in
its actual input. -/
def typedInputUnits (input : Theorem) (domain : Ty) (body : DBTerm)
    (argument : CanonicalTerm) (origin : Origin) : Nat :=
  inputUnits input argument origin + OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body

theorem body_size_le (input : Theorem) (domain : Ty) (body : DBTerm)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) :
    OpenTheory.StorageSize.term body ≤ OpenTheory.StorageSize.theoremData input := by
  have inside := (OpenTheory.StorageSize.abstraction_body_le domain body).trans
    (OpenTheory.StorageSize.application_argument_le (ExcludedMiddle.forallDB domain) (.abs domain body))
  change OpenTheory.StorageSize.term body ≤
    OpenTheory.StorageSize.term (forallAppDB domain (.abs domain body)) at inside
  rw [← shape] at inside
  exact inside.trans ((OpenTheory.StorageSize.canonical_term_le input.sequent.concl).trans
    (OpenTheory.StorageSize.theorem_conclusion_le input))

theorem domain_size_le (domain : Ty) (argument : CanonicalTerm)
    (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.ty domain ≤ OpenTheory.StorageSize.canonical argument := by
  rw [← argumentType]
  exact OpenTheory.StorageSize.canonical_type_le argument

/-- Parsing and type admission reveal fields already charged in the supplied
input. They do not introduce an unmeasured body or type. -/
theorem typedInputUnits_le (input : Theorem) (domain : Ty) (body : DBTerm)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    typedInputUnits input domain body argument origin ≤ 2 * inputUnits input argument origin := by
  have bodyBound := body_size_le input domain body shape
  have typeBound := domain_size_le domain argument argumentType
  unfold typedInputUnits inputUnits
  omega

/-- The final theorem retains all input hypotheses and axiom dependencies;
only the explicitly computed instantiated conclusion is added to this bound. -/
theorem specResult_size_le (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.theoremData
      (specResult input domain body checkedBody argument argumentType) ≤
      OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.canonical
        (betaReduced domain body Ty.bool checkedBody argument argumentType) := by
  exact OpenTheory.StorageSize.preserveAxiomsResult_le input input.sequent.hyp _ (Finset.Subset.refl _)

/-- One accepted substitution may copy the actual argument into the stored
body, but its complete resulting theorem has quadratic payload growth. -/
theorem specResult_size_quadratic (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    OpenTheory.StorageSize.theoremData
      (specResult input domain body checkedBody argument argumentType) ≤
      20 * inputUnits input argument origin ^ 2 := by
  have retained := specResult_size_le input domain body checkedBody argument argumentType
  have copied := PrimitiveStorageBounds.betaReduced_size domain body Ty.bool checkedBody argument argumentType
  have bodyBound := body_size_le input domain body shape
  have argumentBound := OpenTheory.StorageSize.canonical_term_le argument
  rw [OpenTheory.StorageSize.boolType_storage] at copied
  have inputBound : OpenTheory.StorageSize.theoremData input ≤ inputUnits input argument origin := by
    unfold inputUnits; omega
  have argumentInputBound : OpenTheory.StorageSize.term argument.term + 1 ≤
      inputUnits input argument origin := by unfold inputUnits; omega
  have productBound := Nat.mul_le_mul (bodyBound.trans inputBound) argumentInputBound
  have positive : 1 ≤ inputUnits input argument origin := by unfold inputUnits; omega
  nlinarith

/-- The raw admitted operation has the same full stored-theorem bound. -/
theorem instantiate?_size (input : Theorem) (argument : CanonicalTerm) (origin : Origin)
    {out : Theorem} (accepted : instantiate? input argument = some out) :
    OpenTheory.StorageSize.theoremData out ≤ 20 * inputUnits input argument origin ^ 2 := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [instantiate?, parsed] at accepted
  | some parsedBody =>
      unfold instantiate? at accepted
      rw [parsed] at accepted
      change (if same : Ty.same parsedBody.domain argument.ty = true then
        some (specResult input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
          ((Ty.same_eq_true_iff _ _).mp same).symm) else none) = some out at accepted
      split at accepted
      · have exactOutput := Option.some.inj accepted
        rw [← exactOutput]
        exact specResult_size_quadratic _ _ _ _ _ _ parsedBody.shape origin
      · contradiction

/-- The complete input of a repeated universal-elimination chain. -/
def chainInputUnits (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData input +
    (arguments.map OpenTheory.StorageSize.canonical).sum + HOLLight.StorageSize.origin origin

theorem inputUnits_le_chain (input : Theorem) (argument : CanonicalTerm)
    (rest : List CanonicalTerm) (origin : Origin) :
    inputUnits input argument origin ≤ chainInputUnits input (argument :: rest) origin := by
  simp only [inputUnits, chainInputUnits, List.map_cons, List.sum_cons]
  omega

/-- An actual successful first instantiation bounds the complete remaining
chain packet, including every argument still to be processed. -/
theorem chainInputUnits_step (input : Theorem) (argument : CanonicalTerm)
    (rest : List CanonicalTerm) (origin : Origin) {out : Theorem}
    (accepted : instantiate? input argument = some out) :
    chainInputUnits out rest origin ≤ 23 * chainInputUnits input (argument :: rest) origin ^ 2 := by
  have output := instantiate?_size input argument origin accepted
  have included := inputUnits_le_chain input argument rest origin
  have squared := Nat.pow_le_pow_left included 2
  have remaining : 1 + (rest.map OpenTheory.StorageSize.canonical).sum + HOLLight.StorageSize.origin origin ≤
      chainInputUnits input (argument :: rest) origin := by
    simp only [chainInputUnits, List.map_cons, List.sum_cons]; omega
  have positive : 1 ≤ chainInputUnits input (argument :: rest) origin := by
    unfold chainInputUnits; omega
  change 1 + OpenTheory.StorageSize.theoremData out +
    (rest.map OpenTheory.StorageSize.canonical).sum + HOLLight.StorageSize.origin origin ≤ _
  nlinarith

private theorem scaledSquare (value budget factor coefficient : Nat)
    (bounded : value ≤ factor * budget) :
    coefficient * value ^ 2 ≤ (coefficient * factor ^ 2) * budget ^ 2 := by
  calc
    coefficient * value ^ 2 ≤ coefficient * (factor * budget) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bounded 2)
    _ = _ := by ring

private theorem truthDB_size : OpenTheory.StorageSize.term PrimitiveSentences.truthDB = 128 := by
  decide +kernel

private theorem identityBool_size : OpenTheory.StorageSize.term PrimitiveSentences.identityBool = 14 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
/-- All eighteen primitive receipts in the computed SPEC plan have a
quadratic full-payload bound. This includes the theorem operands copied into
requests, rather than counting only the displayed result formulas. -/
theorem specExpansion_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    ((specExpansion policy input domain body checkedBody argument argumentType shape origin).requests.map
      (fun request => graphWeight StorageSize.receiptPayload request.witness.1)).sum ≤
      100000000000 * typedInputUnits input domain body argument origin ^ 2 := by
  let n := typedInputUnits input domain body argument origin
  have positive : 1 ≤ n := by unfold n typedInputUnits inputUnits; omega
  have inputBound : OpenTheory.StorageSize.theoremData input ≤ n := by
    unfold n typedInputUnits inputUnits; omega
  have argumentBound : OpenTheory.StorageSize.canonical argument ≤ n := by
    unfold n typedInputUnits inputUnits; omega
  have argumentTerm := (OpenTheory.StorageSize.canonical_term_le argument).trans argumentBound
  have domainBound : OpenTheory.StorageSize.ty domain ≤ n := by
    unfold n typedInputUnits inputUnits; omega
  have bodyBound : OpenTheory.StorageSize.term body ≤ n := by
    unfold n typedInputUnits inputUnits; omega
  have originBound : StorageSize.origin origin ≤ n := by
    unfold n typedInputUnits inputUnits; omega
  have square : n ≤ n ^ 2 := by nlinarith
  let predicate : CanonicalTerm :=
    ⟨.abs domain body, .function domain Ty.bool, DBTerm.inferType_abs_of checkedBody⟩
  let constantTruth : CanonicalTerm :=
    ⟨.abs domain PrimitiveSentences.truthDB, .function domain Ty.bool,
      DBTerm.inferType_abs_of DerivedRules.inferType_truthDB⟩
  let forallBody := CanonicalTerm.equalityDB (.function domain Ty.bool) (.bound 0)
    (.abs domain PrimitiveSentences.truthDB)
  have checkedForallBody : forallBody.inferType [.function domain Ty.bool] = some Ty.bool :=
    DBTerm.inferType_equalityDB (by simp [DBTerm.inferType])
      (DBTerm.inferType_abs_of DerivedRules.inferType_truthDB)
  let forallExpansion := betaExpansion (.function domain Ty.bool) forallBody Ty.bool
    checkedForallBody predicate rfl
  let functionEquation := CanonicalTerm.equalityOfSameType predicate constantTruth rfl
  let functionProof := eqMpResult forallExpansion.conclusion input functionEquation
  let leftApp := betaRedex domain body Ty.bool checkedBody argument argumentType
  let rightApp := betaRedex domain PrimitiveSentences.truthDB Ty.bool
    DerivedRules.inferType_truthDB argument argumentType
  let applicationProof := appResult functionProof (reflexivity argument) leftApp rightApp rfl
  let truthExpansion := betaExpansion domain PrimitiveSentences.truthDB Ty.bool
    DerivedRules.inferType_truthDB argument argumentType
  let applicationTruth := transResult applicationProof truthExpansion.conclusion
    leftApp DerivedRules.truthTerm rfl
  let reversed := symmetryResult applicationTruth leftApp DerivedRules.truthTerm rfl
  let identityTerm : CanonicalTerm :=
    ⟨PrimitiveSentences.identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
  let truthProof := reflexivity identityTerm
  let appliedProof := eqMpResult reversed truthProof leftApp
  let bodyExpansion := betaExpansion domain body Ty.bool checkedBody argument argumentType
  let instantiated := betaReduced domain body Ty.bool checkedBody argument argumentType
  let result := eqMpResult bodyExpansion.conclusion appliedProof instantiated
  have predicateSize : OpenTheory.StorageSize.canonical predicate =
      22 + 2 * OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body := by
    simp only [predicate, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
      OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]; omega
  have predicateBound : OpenTheory.StorageSize.canonical predicate ≤ 25 * n := by omega
  have constantSize : OpenTheory.StorageSize.canonical constantTruth =
      150 + 2 * OpenTheory.StorageSize.ty domain := by
    simp only [constantTruth, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
      OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage, truthDB_size]; omega
  have constantBound : OpenTheory.StorageSize.canonical constantTruth ≤ 152 * n := by omega
  have forallBodySize : OpenTheory.StorageSize.term forallBody =
      209 + 3 * OpenTheory.StorageSize.ty domain := by
    simp only [forallBody, PrimitiveStorageBounds.equalityDB_size,
      OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage,
      OpenTheory.StorageSize.term, truthDB_size]
    have zeroSize : OpenTheory.StorageSize.nat 0 = 1 := rfl
    rw [zeroSize]; omega
  have forallBudget : PrimitiveStorageBounds.betaInputSize (.function domain Ty.bool) forallBody Ty.bool predicate ≤
      300 * n := by
    simp only [PrimitiveStorageBounds.betaInputSize, OpenTheory.StorageSize.functionType_storage,
      OpenTheory.StorageSize.boolType_storage, forallBodySize]; omega
  have truthBudget : PrimitiveStorageBounds.betaInputSize domain PrimitiveSentences.truthDB Ty.bool argument ≤
      150 * n := by
    simp only [PrimitiveStorageBounds.betaInputSize, OpenTheory.StorageSize.boolType_storage, truthDB_size]; omega
  have bodyBudget : PrimitiveStorageBounds.betaInputSize domain body Ty.bool argument ≤ 20 * n := by
    simp only [PrimitiveStorageBounds.betaInputSize, OpenTheory.StorageSize.boolType_storage]; omega
  have forallBlock := (PrimitiveStorageBounds.betaBlock_payload (.function domain Ty.bool) forallBody Ty.bool
    checkedForallBody predicate rfl origin).trans
    (scaledSquare _ n 301 500 (by omega))
  have truthBlock := (PrimitiveStorageBounds.betaBlock_payload domain PrimitiveSentences.truthDB Ty.bool
    DerivedRules.inferType_truthDB argument argumentType origin).trans
    (scaledSquare _ n 151 500 (by omega))
  have bodyBlock := (PrimitiveStorageBounds.betaBlock_payload domain body Ty.bool checkedBody argument argumentType origin).trans
    (scaledSquare _ n 21 500 (by omega))
  have forallConclusion := (PrimitiveStorageBounds.betaExpansion_conclusion_size
    (.function domain Ty.bool) forallBody Ty.bool checkedForallBody predicate rfl).trans
    (scaledSquare _ n 300 80 forallBudget)
  have truthConclusion := (PrimitiveStorageBounds.betaExpansion_conclusion_size
    domain PrimitiveSentences.truthDB Ty.bool DerivedRules.inferType_truthDB argument argumentType).trans
    (scaledSquare _ n 150 80 truthBudget)
  have bodyConclusion := (PrimitiveStorageBounds.betaExpansion_conclusion_size
    domain body Ty.bool checkedBody argument argumentType).trans (scaledSquare _ n 20 80 bodyBudget)
  change OpenTheory.StorageSize.theoremData forallExpansion.conclusion ≤ _ at forallConclusion
  change OpenTheory.StorageSize.theoremData truthExpansion.conclusion ≤ _ at truthConclusion
  change OpenTheory.StorageSize.theoremData bodyExpansion.conclusion ≤ _ at bodyConclusion
  have equationSize := PrimitiveStorageBounds.equalityOfSameType_size predicate constantTruth rfl
  have functionEquationBound : OpenTheory.StorageSize.canonical functionEquation ≤ 225 * n := by
    change OpenTheory.StorageSize.canonical functionEquation = _ at equationSize
    omega
  have leftSize := PrimitiveStorageBounds.betaRedex_size domain body Ty.bool checkedBody argument argumentType
  rw [OpenTheory.StorageSize.boolType_storage] at leftSize
  change OpenTheory.StorageSize.canonical leftApp = _ at leftSize
  have leftBound : OpenTheory.StorageSize.canonical leftApp ≤ 17 * n := by omega
  have rightSize := PrimitiveStorageBounds.betaRedex_size domain PrimitiveSentences.truthDB Ty.bool
    DerivedRules.inferType_truthDB argument argumentType
  rw [OpenTheory.StorageSize.boolType_storage, truthDB_size] at rightSize
  change OpenTheory.StorageSize.canonical rightApp = _ at rightSize
  have rightBound : OpenTheory.StorageSize.canonical rightApp ≤ 144 * n := by omega
  have truthSize : OpenTheory.StorageSize.canonical DerivedRules.truthTerm = 140 := by
    simp only [DerivedRules.truthTerm, OpenTheory.StorageSize.canonical,
      OpenTheory.StorageSize.boolType_storage, truthDB_size]
  have identitySize : OpenTheory.StorageSize.canonical identityTerm = 46 := by
    simp only [identityTerm, OpenTheory.StorageSize.canonical, identityBool_size,
      OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]
  have instantiatedSize := PrimitiveStorageBounds.betaReduced_size domain body Ty.bool checkedBody argument argumentType
  rw [OpenTheory.StorageSize.boolType_storage] at instantiatedSize
  have copied := Nat.mul_le_mul bodyBound (Nat.add_le_add_right argumentTerm 1)
  change OpenTheory.StorageSize.canonical instantiated ≤ _ at instantiatedSize
  have instantiatedBound : OpenTheory.StorageSize.canonical instantiated ≤ 14 * n ^ 2 := by nlinarith
  have argumentRefl := EqualityStorageBounds.reflexivity_size argument
  have truthRefl := EqualityStorageBounds.reflexivity_size identityTerm
  change OpenTheory.StorageSize.theoremData truthProof = _ at truthRefl
  have functionStored := EqualityStorageBounds.eqMpResult_size forallExpansion.conclusion input functionEquation
  have applicationStored := EqualityStorageBounds.appResult_size functionProof (reflexivity argument) leftApp rightApp rfl
  have transStored := EqualityStorageBounds.transResult_size applicationProof truthExpansion.conclusion leftApp DerivedRules.truthTerm rfl
  have reversedStored := EqualityStorageBounds.symmetryResult_size applicationTruth leftApp DerivedRules.truthTerm rfl
  have appliedStored := EqualityStorageBounds.eqMpResult_size reversed truthProof leftApp
  have resultStored := EqualityStorageBounds.eqMpResult_size bodyExpansion.conclusion appliedProof instantiated
  have functionBound : OpenTheory.StorageSize.theoremData functionProof ≤ 8000000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData forallExpansion.conclusion ≤ _ at forallConclusion
    change OpenTheory.StorageSize.theoremData functionProof ≤ _ at functionStored
    omega
  have applicationBound : OpenTheory.StorageSize.theoremData applicationProof ≤ 8100000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData applicationProof ≤ _ at applicationStored
    omega
  have transBound : OpenTheory.StorageSize.theoremData applicationTruth ≤ 10000000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData truthExpansion.conclusion ≤ _ at truthConclusion
    change OpenTheory.StorageSize.theoremData applicationTruth ≤ _ at transStored
    omega
  have reversedBound : OpenTheory.StorageSize.theoremData reversed ≤ 10100000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData reversed ≤ _ at reversedStored
    omega
  have appliedBound : OpenTheory.StorageSize.theoremData appliedProof ≤ 10200000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData appliedProof ≤ _ at appliedStored
    rw [identitySize] at truthRefl
    omega
  have resultBound : OpenTheory.StorageSize.theoremData result ≤ 10300000 * n ^ 2 := by
    change OpenTheory.StorageSize.theoremData bodyExpansion.conclusion ≤ _ at bodyConclusion
    change OpenTheory.StorageSize.theoremData result ≤ _ at resultStored
    omega
  change graphWeight StorageSize.receiptPayload (betaBlock forallExpansion origin).1 ≤ _ at forallBlock
  change graphWeight StorageSize.receiptPayload (betaBlock truthExpansion origin).1 ≤ _ at truthBlock
  change graphWeight StorageSize.receiptPayload (betaBlock bodyExpansion origin).1 ≤ _ at bodyBlock
  have symmetry := EqualityStorageBounds.symmetryBlock_payload applicationTruth leftApp DerivedRules.truthTerm rfl origin
  unfold EqualityStorageBounds.inputUnits at symmetry
  have exactPlan : ((specExpansion policy input domain body checkedBody argument argumentType shape origin).requests.map
      (fun request => graphWeight StorageSize.receiptPayload request.witness.1)).sum =
      graphWeight StorageSize.receiptPayload (betaBlock forallExpansion origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.eqMp forallExpansion.conclusion input)) functionProof origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.refl argument)) (reflexivity argument) origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.mkComb functionProof (reflexivity argument))) applicationProof origin).1 +
      graphWeight StorageSize.receiptPayload (betaBlock truthExpansion origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.trans applicationProof truthExpansion.conclusion)) applicationTruth origin).1 +
      graphWeight StorageSize.receiptPayload (symmetryBlock applicationTruth leftApp DerivedRules.truthTerm rfl origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.refl identityTerm)) truthProof origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.eqMp reversed truthProof)) appliedProof origin).1 +
      graphWeight StorageSize.receiptPayload (betaBlock bodyExpansion origin).1 +
      graphWeight StorageSize.receiptPayload (primitiveBlock (.inference (.eqMp bodyExpansion.conclusion appliedProof)) result origin).1 := by
    simp only [specExpansion, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    dsimp only [predicate, constantTruth, forallBody, forallExpansion, functionEquation, functionProof,
      leftApp, rightApp, applicationProof, truthExpansion, applicationTruth, reversed, identityTerm,
      truthProof, appliedProof, bodyExpansion, instantiated, result]
    ring
  rw [exactPlan]
  simp only [StorageSize.eqMp_payload, StorageSize.refl_payload, StorageSize.app_payload, StorageSize.trans_payload]
  change _ ≤ 100000000000 * n ^ 2
  omega

set_option maxHeartbeats 1000000 in
/-- The actual successful compiled local certificate retains the bounded
plan payload exactly. Relocation does not copy external premise proofs. -/
theorem specTypedBlock?_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specTypedBlock? policy input domain body checkedBody argument argumentType shape origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤ 400000000000 * inputUnits input argument origin ^ 2 := by
  have actual : graphWeight StorageSize.receiptPayload block.1 =
      ((specExpansion policy input domain body checkedBody argument argumentType shape origin).requests.map
        (fun request => graphWeight StorageSize.receiptPayload request.witness.1)).sum := by
    simpa only [start, graphWeight, Array.toList_empty, List.map_nil, List.sum_nil, Nat.zero_add] using
      (StorageSize.finishPlan_payload computed)
  have bounded := specExpansion_payload policy input domain body checkedBody argument argumentType shape origin
  have included := typedInputUnits_le input domain body argument argumentType shape origin
  have scaled := scaledSquare _ (inputUnits input argument origin) 2 100000000000 included
  rw [actual]
  exact bounded.trans scaled

/-- Parsing admission does not change the actual block's payload bound. -/
theorem specBlock?_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specBlock? policy input argument origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤ 400000000000 * inputUnits input argument origin ^ 2 := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [specBlock?, parsed] at computed
  | some parsedBody =>
      unfold specBlock? at computed
      rw [parsed] at computed
      change (if same : Ty.same parsedBody.domain argument.ty = true then
        specTypedBlock? policy input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
          ((Ty.same_eq_true_iff _ _).mp same).symm parsedBody.shape origin else none) = some block at computed
      split at computed
      · exact specTypedBlock?_payload _ _ _ _ _ _ _ _ _ computed
      · contradiction

/-- Successful emission appends the bounded full payload of the actual
compiled block. Its existing prefix remains physically shared. -/
theorem emitSpec_payload {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {argument : CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpec policy input argument inputRoot origin state = some (result, root)) :
    graphWeight StorageSize.receiptPayload result.receipts.toList ≤
      graphWeight StorageSize.receiptPayload state.receipts.toList +
        400000000000 * inputUnits input argument origin ^ 2 := by
  cases computed : specBlock? policy input argument origin with
  | none => simp [emitSpec, computed] at emitted
  | some block =>
      have actual : emitBlock policy [inputRoot] block state = some (result, root) := by
        simpa [emitSpec, computed] using emitted
      rw [StorageSize.emitBlock_payload actual]
      exact Nat.add_le_add_left (specBlock?_payload policy input argument origin computed) _

/-- An explicit bound for a chain's stored receipts and final theorem.
For a fixed number of quantifiers this is a polynomial in the input payload;
the recursive form exposes the growth caused by successive substitutions. -/
def chainPayloadBound : Nat → Nat → Nat
  | 0, units => units
  | count + 1, units =>
      400000000000 * units ^ 2 + chainPayloadBound count (23 * units ^ 2)

theorem chainPayloadBound_mono (count : Nat) : Monotone (chainPayloadBound count) := by
  induction count with
  | zero => intro left right ordered; exact ordered
  | succ count ih =>
      intro left right ordered
      have squared := Nat.pow_le_pow_left ordered 2
      exact Nat.add_le_add (Nat.mul_le_mul_left _ squared) (ih (Nat.mul_le_mul_left _ squared))

/-- The final actual theorem is bounded after every admitted substitution. -/
theorem instantiateMany?_size (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin)
    {out : Theorem} (accepted : instantiateMany? input arguments = some out) :
    OpenTheory.StorageSize.theoremData out ≤
      chainPayloadBound arguments.length (chainInputUnits input arguments origin) := by
  induction arguments generalizing input with
  | nil =>
      have exactOutput := Option.some.inj accepted
      rw [← exactOutput]
      unfold chainInputUnits
      simp only [List.map_nil, List.sum_nil, List.length_nil, chainPayloadBound]
      omega
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [instantiateMany?, first] at accepted
      | some next =>
          have remaining : instantiateMany? next rest = some out := by
            simpa [instantiateMany?, first] using accepted
          have tail := (ih next remaining).trans
            ((chainPayloadBound_mono rest.length) (chainInputUnits_step input argument rest origin first))
          simp only [List.length_cons, chainPayloadBound]
          omega

/-- Full stored receipt payload for successful repeated SPEC emission. -/
theorem emitSpecChain_payload {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {arguments : List CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpecChain policy input arguments inputRoot origin state = some (result, root)) :
    graphWeight StorageSize.receiptPayload result.receipts.toList ≤
      graphWeight StorageSize.receiptPayload state.receipts.toList +
        chainPayloadBound arguments.length (chainInputUnits input arguments origin) := by
  induction arguments generalizing input inputRoot state with
  | nil =>
      cases Option.some.inj emitted
      omega
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [emitSpecChain, first] at emitted
      | some next =>
          cases step : emitSpec policy input argument inputRoot origin state with
          | none => simp [emitSpecChain, first, step] at emitted
          | some nextState =>
              have tail : emitSpecChain policy next rest nextState.2 origin nextState.1 = some (result, root) := by
                simpa [emitSpecChain, first, step] using emitted
              have emittedPrefix := emitSpec_payload step
              have emittedTail := ih tail
              have firstSize := scaledSquare _ (chainInputUnits input (argument :: rest) origin) 1
                400000000000 (by simpa only [Nat.one_mul] using inputUnits_le_chain input argument rest origin)
              have remaining := (chainPayloadBound_mono rest.length)
                (chainInputUnits_step input argument rest origin first)
              simp only [Nat.one_pow, Nat.mul_one] at firstSize
              simp only [List.length_cons, chainPayloadBound]
              omega

/-- The selected standalone local chain certificate has the same bound. -/
theorem specChain?_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate} (computed : specChain? policy input arguments origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤
      chainPayloadBound arguments.length (chainInputUnits input arguments origin) := by
  cases emitted : emitSpecChain policy input arguments 0 origin (start [input]) with
  | none => simp [specChain?, emitted] at computed
  | some result =>
      have exactBlock : finish result.1 result.2 = block := by simpa [specChain?, emitted] using computed
      rw [← exactBlock]
      change graphWeight StorageSize.receiptPayload result.1.receipts.toList ≤ _
      have bounded := emitSpecChain_payload emitted
      change graphWeight StorageSize.receiptPayload result.1.receipts.toList ≤ 0 + _ at bounded
      simpa only [Nat.zero_add] using bounded

/-- The coefficient is fixed by the admitted chain length, independently of
all stored input terms and their contents. -/
def chainCoefficient : Nat → Nat
  | 0 => 1
  | count + 1 => 400000000000 + chainCoefficient count * 23 ^ (2 ^ count)

/-- Successive capture-avoiding substitutions give a fixed-length polynomial,
with every hypothesis and axiom dependency retained in its input variable. -/
theorem chainPayloadBound_polynomial (count units : Nat) (positive : 1 ≤ units) :
    chainPayloadBound count units ≤ chainCoefficient count * units ^ (2 ^ count) := by
  induction count generalizing units with
  | zero => simp [chainPayloadBound, chainCoefficient]
  | succ count ih =>
      have nextPositive : 1 ≤ 23 * units ^ 2 := by nlinarith
      have tail := ih (23 * units ^ 2) nextPositive
      have exponentPositive : 1 ≤ (2 : Nat) ^ count := Nat.one_le_pow _ _ (by decide)
      have exponent : 2 ≤ (2 : Nat) ^ (count + 1) := by rw [pow_succ]; omega
      have first := Nat.mul_le_mul_left 400000000000 (Nat.pow_le_pow_right positive exponent)
      have exponentExact : 2 * (2 : Nat) ^ count = (2 : Nat) ^ (count + 1) := by rw [pow_succ]; omega
      rw [mul_pow, ← pow_mul, exponentExact] at tail
      simp only [chainPayloadBound, chainCoefficient]
      calc
        _ ≤ 400000000000 * units ^ (2 ^ (count + 1)) +
            chainCoefficient count * (23 ^ (2 ^ count) * units ^ (2 ^ (count + 1))) := Nat.add_le_add first tail
        _ = _ := by ring

/-- Exact emitted graph payload admits a polynomial account for every fixed
finite source arity. Binary physical addresses are accounted for separately. -/
theorem specChain?_payload_polynomial (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate} (computed : specChain? policy input arguments origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤ chainCoefficient arguments.length *
      chainInputUnits input arguments origin ^ (2 ^ arguments.length) :=
  (specChain?_payload policy input arguments origin computed).trans
    (chainPayloadBound_polynomial _ _ (by unfold chainInputUnits; omega))

theorem instantiateMany?_size_polynomial (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin)
    {out : Theorem} (accepted : instantiateMany? input arguments = some out) :
    OpenTheory.StorageSize.theoremData out ≤ chainCoefficient arguments.length *
      chainInputUnits input arguments origin ^ (2 ^ arguments.length) :=
  (instantiateMany?_size input arguments origin accepted).trans
    (chainPayloadBound_polynomial _ _ (by unfold chainInputUnits; omega))

/-- Increasing the admitted maximum arity retains a uniform chain account. -/
theorem chainPayloadBound_mono_count (units : Nat) : Monotone (fun count => chainPayloadBound count units) := by
  apply monotone_nat_of_le_succ
  intro count
  have growth : ∀ (count units : Nat), chainPayloadBound count units ≤ chainPayloadBound (count + 1) units := by
    intro count
    induction count with
    | zero =>
        intro units
        have squared : units ≤ units ^ 2 := by
          cases units with
          | zero => simp
          | succ value => nlinarith
        simp only [chainPayloadBound]
        nlinarith
    | succ count ih =>
        intro units
        simp only [chainPayloadBound]
        exact Nat.add_le_add_left (ih (23 * units ^ 2)) _
  exact growth count units

/-- One fixed finite arity supplies one polynomial for every successful block
of that admitted profile, including all shorter chains. -/
theorem specChain?_payload_of_arity (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin) (arity : Nat)
    (admittedArity : arguments.length ≤ arity)
    {block : ProofSystem.Certificate} (computed : specChain? policy input arguments origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤ chainCoefficient arity *
      chainInputUnits input arguments origin ^ (2 ^ arity) :=
  ((specChain?_payload policy input arguments origin computed).trans
    ((chainPayloadBound_mono_count _) admittedArity)).trans
      (chainPayloadBound_polynomial _ _ (by unfold chainInputUnits; omega))

theorem instantiateMany?_size_of_arity (input : Theorem) (arguments : List CanonicalTerm)
    (origin : Origin) (arity : Nat) (admittedArity : arguments.length ≤ arity)
    {out : Theorem} (accepted : instantiateMany? input arguments = some out) :
    OpenTheory.StorageSize.theoremData out ≤ chainCoefficient arity *
      chainInputUnits input arguments origin ^ (2 ^ arity) :=
  ((instantiateMany?_size input arguments origin accepted).trans
    ((chainPayloadBound_mono_count _) admittedArity)).trans
      (chainPayloadBound_polynomial _ _ (by unfold chainInputUnits; omega))

theorem emitSpecChain_payload_of_arity {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {arguments : List CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat} (arity : Nat)
    (admittedArity : arguments.length ≤ arity)
    (emitted : emitSpecChain policy input arguments inputRoot origin state = some (result, root)) :
    graphWeight StorageSize.receiptPayload result.receipts.toList ≤
      graphWeight StorageSize.receiptPayload state.receipts.toList + chainCoefficient arity *
        chainInputUnits input arguments origin ^ (2 ^ arity) := by
  have bounded := emitSpecChain_payload emitted
  have sized := ((chainPayloadBound_mono_count (chainInputUnits input arguments origin)) admittedArity).trans
    (chainPayloadBound_polynomial arity (chainInputUnits input arguments origin) (by unfold chainInputUnits; omega))
  exact bounded.trans (Nat.add_le_add_left sized _)

namespace Controls

/-- The existing binder-bearing argument control has its actual full payload
bounded while retaining a nonempty hypothesis and an axiom dependency. -/
theorem binder_argument_payload (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    ∃ block, specChain? policy QuantifierExpansion.Controls.taggedInput
      [QuantifierExpansion.Controls.identityArgument] origin = some block ∧
      BlockChecked policy [QuantifierExpansion.Controls.taggedInput]
        QuantifierExpansion.Controls.instantiatedReflexivity block ∧
      graphWeight StorageSize.receiptPayload block.1 ≤ chainCoefficient 1 *
        chainInputUnits QuantifierExpansion.Controls.taggedInput
          [QuantifierExpansion.Controls.identityArgument] origin ^ 2 := by
  obtain ⟨block, computed, checked⟩ := QuantifierExpansion.Controls.binder_argument_chain_checked policy origin
  refine ⟨block, computed, checked, ?_⟩
  simpa only [List.length_singleton, pow_one] using specChain?_payload_polynomial policy _ _ origin computed

/-- Wrong-sort data are refused before any successful payload certificate is
claimed. This uses the same raw operation as the positive control. -/
theorem wrong_sort_refused (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    specChain? policy QuantifierExpansion.Controls.taggedInput [DerivedRules.truthTerm] origin = none := by
  simp [specChain?, emitSpecChain, QuantifierExpansion.Controls.wrong_sort_refused]

end Controls

end Mettapedia.Languages.HOLLight.QuantifierStorageBounds
