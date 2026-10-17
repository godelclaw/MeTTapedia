import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives

/-!
# Explicit universal instantiation in HOL Light

Universal instantiation is a chronological graph of the original HOL Light
primitive requests. The quantified theorem occupies one external premise
slot. Beta conversion uses the computed fresh-source BETA/INST expansion;
equality symmetry uses the shared five-request expansion. Full hypothesis
and axiom sets are retained at the final instantiated theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.QuantifierExpansion

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open GraphExpansion EqualityExpansion PrimitiveTransport
open ProofExecution (Origin)
open ExcludedMiddle (forallDB)
open DerivedRules (forallAppDB)
open PrimitiveSentences (truthDB identityBool)

/-- A finite macro plan carries checks for its actual local graph blocks. -/
structure SpecExpansion (policy : AxiomPolicy) [DecidablePred policy] (input : Theorem) where
  requests : List BlockRequest
  conclusion : Theorem
  checked : LocallyChecked policy #[input] requests

/-- A typed universal-elimination plan. Its data are constructed directly from
the actual term, argument and incoming theorem; proof fields do not drive the
construction. -/
def specExpansion (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body))
    (origin : Origin) : SpecExpansion policy input := by
  let predicate : CanonicalTerm :=
    ⟨.abs domain body, .function domain Ty.bool, DBTerm.inferType_abs_of checkedBody⟩
  let constantTruth : CanonicalTerm :=
    ⟨.abs domain truthDB, .function domain Ty.bool,
      DBTerm.inferType_abs_of DerivedRules.inferType_truthDB⟩
  let forallBody := CanonicalTerm.equalityDB (.function domain Ty.bool) (.bound 0)
    (.abs domain truthDB)
  have checkedForallBody : forallBody.inferType [.function domain Ty.bool] = some Ty.bool :=
    DBTerm.inferType_equalityDB (by simp [DBTerm.inferType])
      (DBTerm.inferType_abs_of DerivedRules.inferType_truthDB)
  let forallExpansion := betaExpansion (.function domain Ty.bool) forallBody Ty.bool
    checkedForallBody predicate rfl
  let functionEquation := CanonicalTerm.equalityOfSameType predicate constantTruth rfl
  have forallRedex : betaRedex (.function domain Ty.bool) forallBody Ty.bool
      checkedForallBody predicate rfl = input.sequent.concl := by
    apply CanonicalTerm.ext_term
    exact shape.symm
  have forallReduced : betaReduced (.function domain Ty.bool) forallBody Ty.bool
      checkedForallBody predicate rfl = functionEquation := by
    apply CanonicalTerm.ext_term
    simp [betaReduced, forallBody, functionEquation, predicate, constantTruth,
      CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, DBTerm.instantiateAt,
      DerivedRules.instantiateAt_truthDB]
  have forallView : CanonicalTerm.EqualityViewSemantics
      forallExpansion.conclusion.sequent.concl input.sequent.concl functionEquation := by
    rw [betaExpansion_conclusion]
    refine ⟨(congrArg CanonicalTerm.ty forallRedex).symm, ?_⟩
    change CanonicalTerm.equalityDB Ty.bool
      (betaRedex (.function domain Ty.bool) forallBody Ty.bool checkedForallBody predicate rfl).term
      (betaReduced (.function domain Ty.bool) forallBody Ty.bool checkedForallBody predicate rfl).term = _
    rw [← forallRedex, forallReduced]
    rfl
  let functionProof := eqMpResult forallExpansion.conclusion input functionEquation
  have functionChecked : checkEqMp forallExpansion.conclusion input = some functionProof :=
    eqMpResult_checked _ _ _ _ forallView rfl
  let leftApp := betaRedex domain body Ty.bool checkedBody argument argumentType
  let rightApp := betaRedex domain truthDB Ty.bool DerivedRules.inferType_truthDB argument argumentType
  let applicationProof := appResult functionProof (reflexivity argument) leftApp rightApp rfl
  have applicationChecked : checkApp functionProof (reflexivity argument) = some applicationProof := by
    apply appResult_checked _ _ predicate constantTruth argument argument leftApp rightApp rfl
    · exact equality_view predicate constantTruth rfl
    · exact equality_view argument argument rfl
    · exact ⟨domain, Ty.bool, by simp [predicate], argumentType.symm, rfl⟩
    · exact ⟨domain, Ty.bool, by simp [constantTruth], argumentType.symm, rfl⟩
  let truthExpansion := betaExpansion domain truthDB Ty.bool DerivedRules.inferType_truthDB argument argumentType
  have truthReduced : betaReduced domain truthDB Ty.bool DerivedRules.inferType_truthDB
      argument argumentType = DerivedRules.truthTerm := by
    apply CanonicalTerm.ext_term
    exact DerivedRules.instantiateAt_truthDB argument.term 0
  have truthView : CanonicalTerm.EqualityViewSemantics
      truthExpansion.conclusion.sequent.concl rightApp DerivedRules.truthTerm := by
    rw [betaExpansion_conclusion]
    refine ⟨rfl, ?_⟩
    change CanonicalTerm.equalityDB Ty.bool rightApp.term
      (betaReduced domain truthDB Ty.bool DerivedRules.inferType_truthDB argument argumentType).term = _
    rw [truthReduced]
    rfl
  let applicationTruth := transResult applicationProof truthExpansion.conclusion
    leftApp DerivedRules.truthTerm rfl
  have transChecked : checkTrans applicationProof truthExpansion.conclusion = some applicationTruth :=
    transResult_checked _ _ leftApp rightApp DerivedRules.truthTerm rfl
      (equality_view leftApp rightApp rfl) truthView
  let reversed := symmetryResult applicationTruth leftApp DerivedRules.truthTerm rfl
  let identityTerm : CanonicalTerm :=
    ⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
  let truthProof := reflexivity identityTerm
  have truthConclusion : truthProof.sequent.concl = DerivedRules.truthTerm := by
    apply CanonicalTerm.ext_term
    rfl
  let appliedProof := eqMpResult reversed truthProof leftApp
  have appliedChecked : checkEqMp reversed truthProof = some appliedProof :=
    eqMpResult_checked _ _ DerivedRules.truthTerm leftApp (equality_view DerivedRules.truthTerm leftApp rfl) truthConclusion.symm
  let bodyExpansion := betaExpansion domain body Ty.bool checkedBody argument argumentType
  let instantiated := betaReduced domain body Ty.bool checkedBody argument argumentType
  let result := eqMpResult bodyExpansion.conclusion appliedProof instantiated
  have bodyView : CanonicalTerm.EqualityViewSemantics
      bodyExpansion.conclusion.sequent.concl leftApp instantiated := by
    rw [betaExpansion_conclusion]
    exact equality_view leftApp instantiated rfl
  have resultChecked : checkEqMp bodyExpansion.conclusion appliedProof = some result :=
    eqMpResult_checked _ _ leftApp instantiated bodyView rfl
  let requests : List BlockRequest :=
    [⟨forallExpansion.conclusion, betaBlock forallExpansion origin, [], origin⟩,
     ⟨functionProof, primitiveBlock (.inference (.eqMp forallExpansion.conclusion input)) functionProof origin,
        [1, 0], origin⟩,
     ⟨reflexivity argument, primitiveBlock (.inference (.refl argument)) (reflexivity argument) origin,
        [], origin⟩,
     ⟨applicationProof, primitiveBlock (.inference (.mkComb functionProof (reflexivity argument)))
        applicationProof origin, [2, 3], origin⟩,
     ⟨truthExpansion.conclusion, betaBlock truthExpansion origin, [], origin⟩,
     ⟨applicationTruth, primitiveBlock (.inference (.trans applicationProof truthExpansion.conclusion))
        applicationTruth origin, [4, 5], origin⟩,
     ⟨reversed, symmetryBlock applicationTruth leftApp DerivedRules.truthTerm rfl origin, [6], origin⟩,
     ⟨truthProof, primitiveBlock (.inference (.refl identityTerm)) truthProof origin, [], origin⟩,
     ⟨appliedProof, primitiveBlock (.inference (.eqMp reversed truthProof)) appliedProof origin, [7, 8], origin⟩,
     ⟨bodyExpansion.conclusion, betaBlock bodyExpansion origin, [], origin⟩,
     ⟨result, primitiveBlock (.inference (.eqMp bodyExpansion.conclusion appliedProof)) result origin,
        [10, 9], origin⟩]
  refine ⟨requests, result, ?_⟩
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy forallExpansion origin
  apply LocallyChecked.cons (premises := [forallExpansion.conclusion, input]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp forallExpansion.conclusion input)) functionProof origin functionChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl argument)) (reflexivity argument) origin (reflexivity_checked argument)
  apply LocallyChecked.cons (premises := [functionProof, reflexivity argument]) rfl
  · exact primitiveBlock_checked (.inference (.mkComb functionProof (reflexivity argument))) applicationProof origin applicationChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy truthExpansion origin
  apply LocallyChecked.cons (premises := [applicationProof, truthExpansion.conclusion]) rfl
  · exact primitiveBlock_checked (.inference (.trans applicationProof truthExpansion.conclusion)) applicationTruth origin transChecked
  apply LocallyChecked.cons (premises := [applicationTruth]) rfl
  · exact symmetryBlock_checked policy applicationTruth leftApp DerivedRules.truthTerm rfl
      (equality_view leftApp DerivedRules.truthTerm rfl) origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl identityTerm)) truthProof origin (reflexivity_checked identityTerm)
  apply LocallyChecked.cons (premises := [reversed, truthProof]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp reversed truthProof)) appliedProof origin appliedChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy bodyExpansion origin
  apply LocallyChecked.cons (premises := [bodyExpansion.conclusion, appliedProof]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp bodyExpansion.conclusion appliedProof)) result origin resultChecked
  exact .nil _

/-- The macro plan emits eighteen original primitive rule occurrences. This
counts the graph nodes inside its shared local blocks, including BETA/INST
and the five-node symmetry block. -/
theorem specExpansion_primitiveCount (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    ((specExpansion policy input domain body checkedBody argument argumentType shape origin).requests.map
      (fun request => request.witness.1.length)).sum = 18 := by rfl

/-- Universal instantiation retains the original theorem's full provenance. -/
def specResult (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (betaReduced domain body Ty.bool checkedBody argument argumentType)

theorem specExpansion_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    (specExpansion policy input domain body checkedBody argument argumentType shape origin).conclusion =
      specResult input domain body checkedBody argument argumentType := by
  apply Theorem.ext
  · simp [specExpansion, eqMpResult, appResult, transResult, symmetryResult, reflexivity,
      betaExpansion, substituteTheorem, Theorem.preserveAxiomsResult, Theorem.unionResult,
      Theorem.emptyResult, specResult]
  · apply Sequent.ext
    · simp [specExpansion, eqMpResult, appResult, transResult, symmetryResult, reflexivity,
        betaExpansion, substituteTheorem, TypeCorrectTermSubstitution.applyHypotheses,
        Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult, specResult]
    · rfl

/-- Compile the typed universal-instantiation macro plan through the original
chronological builder. The quantified proof stays in external slot zero. -/
def specTypedBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    Option ProofSystem.Certificate :=
  finishPlan policy (start [input]) #[0]
    (specExpansion policy input domain body checkedBody argument argumentType shape origin).requests 11

theorem specTypedBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    ∃ block, specTypedBlock? policy input domain body checkedBody argument argumentType shape origin = some block ∧
      BlockChecked policy [input] (specResult input domain body checkedBody argument argumentType) block := by
  let expansion := specExpansion policy input domain body checkedBody argument argumentType shape origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[input]) (roots := #[0]) (start_checked policy [input]) rfl
    expansion.checked (index := 11) (conclusion := expansion.conclusion) (by rfl)
  refine ⟨block, computed, ?_⟩
  simpa only [expansion, specExpansion_conclusion] using checked

/-- A successful typed compilation contains exactly the planned primitive
occurrences; the external quantified theorem is not copied into its nodes. -/
theorem specTypedBlock?_size (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specTypedBlock? policy input domain body checkedBody argument argumentType shape origin =
      some block) : block.1.length = 18 := by
  have count := finishPlan_size computed
  simpa only [specExpansion_primitiveCount, start, Array.size_empty, Nat.zero_add] using count

theorem specExpansion_origins (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin) :
    (specExpansion policy input domain body checkedBody argument argumentType shape origin).requests.flatMap
      (fun request => request.witness.1.map (·.origin)) = List.replicate 18 origin := by
  simp [specExpansion, betaBlock, symmetryBlock, primitiveBlock, List.replicate_succ, List.replicate_zero]

theorem specTypedBlock?_origins (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specTypedBlock? policy input domain body checkedBody argument argumentType shape origin =
      some block) : block.1.map (·.origin) = List.replicate 18 origin := by
  have preserved := finishPlan_witnesses computed
  have origins := congrArg (List.map (fun pair => pair.2)) preserved
  simpa [start, List.map_map, Function.comp_def, List.map_flatMap, specExpansion_origins] using origins

/-- A recognized, typed inlined universal formula. The incoming canonical
term remains the authority for its shape and body type. -/
structure UniversalBody (input : CanonicalTerm) where
  domain : Ty
  body : DBTerm
  checkedBody : body.inferType [domain] = some Ty.bool
  shape : input.term = forallAppDB domain (.abs domain body)

/-- Parse the displayed universal term and recheck its boolean body. -/
def universalBody? (input : CanonicalTerm) : Option (UniversalBody input) :=
  match shape : input.term with
  | .app operator (.abs domain body) =>
      if symbol : DBTerm.same operator (forallDB domain) = true then
        match checkedBody : body.inferType [domain] with
        | some type =>
            if boolean : Ty.same type Ty.bool = true then
              some ⟨domain, body,
                checkedBody.trans (congrArg some ((Ty.same_eq_true_iff _ _).mp boolean)),
                by rw [shape, (DBTerm.same_eq_true_iff _ _).mp symbol]; rfl⟩
            else none
        | none => none
      else none
  | _ => none

theorem universalBody?_complete (input : CanonicalTerm) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (shape : input.term = forallAppDB domain (.abs domain body)) :
    universalBody? input = some ⟨domain, body, checkedBody, shape⟩ := by
  rcases input with ⟨term, type, checked⟩
  change term = forallAppDB domain (.abs domain body) at shape
  subst term
  dsimp only [universalBody?, forallAppDB]
  have sameSymbol := (DBTerm.same_eq_true_iff (forallDB domain) (forallDB domain)).mpr rfl
  change (if symbol : DBTerm.same (forallDB domain) (forallDB domain) = true then _ else none) = _
  rw [dif_pos sameSymbol]
  split
  · rename_i type actual
    have same := Option.some.inj (actual.symm.trans checkedBody)
    subst type
    have sameBool := (Ty.same_eq_true_iff Ty.bool Ty.bool).mpr rfl
    rw [dif_pos sameBool]
  · rename_i rejected
    rw [checkedBody] at rejected
    contradiction

/-- Compute the exact instantiated theorem, checking the universal head and
argument sort before constructing its body instance. -/
def instantiate? (input : Theorem) (argument : CanonicalTerm) : Option Theorem := do
  let parsed ← universalBody? input.sequent.concl
  if sameType : Ty.same parsed.domain argument.ty = true then
    pure (specResult input parsed.domain parsed.body parsed.checkedBody argument
      ((Ty.same_eq_true_iff _ _).mp sameType).symm)
  else none

/-- Compute and check the primitive graph for a raw universal theorem. -/
def specBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin) : Option ProofSystem.Certificate := do
  let parsed ← universalBody? input.sequent.concl
  if sameType : Ty.same parsed.domain argument.ty = true then
    specTypedBlock? policy input parsed.domain parsed.body parsed.checkedBody argument
      ((Ty.same_eq_true_iff _ _).mp sameType).symm parsed.shape origin
  else none

theorem instantiate?_eq_some (input : Theorem) (domain : Ty) (body : DBTerm)
    (checkedBody : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = forallAppDB domain (.abs domain body)) :
    instantiate? input argument = some (specResult input domain body checkedBody argument argumentType) := by
  unfold instantiate?
  rw [universalBody?_complete _ domain body checkedBody shape]
  have sameType := (Ty.same_eq_true_iff domain argument.ty).mpr argumentType.symm
  change (if same : Ty.same domain argument.ty = true then
    some (specResult input domain body checkedBody argument ((Ty.same_eq_true_iff _ _).mp same).symm)
    else none) = _
  rw [dif_pos sameType]

/-- Every successful pure instantiation has a computed primitive certificate
with that exact output theorem and no additional proof-authority assumptions. -/
theorem specBlock?_checked_of_instantiate (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin) {out : Theorem}
    (accepted : instantiate? input argument = some out) :
    ∃ block, specBlock? policy input argument origin = some block ∧
      BlockChecked policy [input] out block := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [instantiate?, parsed] at accepted
  | some parsedBody =>
      have step : (if same : Ty.same parsedBody.domain argument.ty = true then
          some (specResult input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
            ((Ty.same_eq_true_iff _ _).mp same).symm) else none) = some out := by
        unfold instantiate? at accepted
        rw [parsed] at accepted
        exact accepted
      split at step
      · rename_i same
        have exactOutput := Option.some.inj step
        obtain ⟨block, computed, checked⟩ := specTypedBlock?_checked policy input parsedBody.domain
          parsedBody.body parsedBody.checkedBody argument
          ((Ty.same_eq_true_iff _ _).mp same).symm parsedBody.shape origin
        refine ⟨block, ?_, exactOutput ▸ checked⟩
        unfold specBlock?
        rw [parsed]
        change (if same' : Ty.same parsedBody.domain argument.ty = true then _ else none) = _
        rw [dif_pos same]
        exact computed
      · contradiction

/-- The graph compiler refuses precisely the raw inputs refused by the pure
typed instantiation operation. Primitive replay cannot introduce a further
failure on a well-formed universal instance. -/
theorem specBlock?_eq_none_iff (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin) :
    specBlock? policy input argument origin = none ↔ instantiate? input argument = none := by
  constructor
  · intro refused
    cases computed : instantiate? input argument with
    | none => rfl
    | some out =>
        obtain ⟨block, emitted, _⟩ := specBlock?_checked_of_instantiate
          policy input argument origin computed
        rw [refused] at emitted
        contradiction
  · intro refused
    cases parsed : universalBody? input.sequent.concl with
    | none => simp [specBlock?, parsed]
    | some parsedBody =>
        unfold instantiate? at refused
        rw [parsed] at refused
        change (if same : Ty.same parsedBody.domain argument.ty = true then
          some (specResult input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
            ((Ty.same_eq_true_iff _ _).mp same).symm) else none) = none at refused
        split at refused
        · contradiction
        · rename_i different
          unfold specBlock?
          rw [parsed]
          change (if same : Ty.same parsedBody.domain argument.ty = true then _ else none) = none
          rw [dif_neg different]

/-- A successful raw graph has exactly the pure operation's output theorem. -/
theorem specBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specBlock? policy input argument origin = some block) :
    ∃ out, instantiate? input argument = some out ∧ BlockChecked policy [input] out block := by
  cases instantiated : instantiate? input argument with
  | none =>
      have refused := (specBlock?_eq_none_iff policy input argument origin).mpr instantiated
      rw [refused] at computed
      contradiction
  | some out =>
      obtain ⟨expected, emitted, checked⟩ := specBlock?_checked_of_instantiate
        policy input argument origin instantiated
      have same := Option.some.inj (emitted.symm.trans computed)
      exact ⟨out, rfl, same ▸ checked⟩

theorem specBlock?_size (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specBlock? policy input argument origin = some block) : block.1.length = 18 := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [specBlock?, parsed] at computed
  | some parsedBody =>
      unfold specBlock? at computed
      rw [parsed] at computed
      change (if same : Ty.same parsedBody.domain argument.ty = true then
        specTypedBlock? policy input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
          ((Ty.same_eq_true_iff _ _).mp same).symm parsedBody.shape origin else none) = some block at computed
      split at computed
      · exact specTypedBlock?_size _ _ _ _ _ _ _ _ _ computed
      · contradiction

theorem specBlock?_origins (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specBlock? policy input argument origin = some block) :
    block.1.map (·.origin) = List.replicate 18 origin := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [specBlock?, parsed] at computed
  | some parsedBody =>
      unfold specBlock? at computed
      rw [parsed] at computed
      change (if same : Ty.same parsedBody.domain argument.ty = true then
        specTypedBlock? policy input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
          ((Ty.same_eq_true_iff _ _).mp same).symm parsedBody.shape origin else none) = some block at computed
      split at computed
      · exact specTypedBlock?_origins _ _ _ _ _ _ _ _ _ computed
      · contradiction

/-- Execute a universal-instantiation block within a larger graph while
retaining the quantified proof's physical root. -/
def emitSpec (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (inputRoot : Nat) (origin : Origin)
    (state : ProofExecution.State) : Option (ProofExecution.State × Nat) := do
  let block ← specBlock? policy input argument origin
  emitBlock policy [inputRoot] block state

theorem emitSpec_checked (policy : AxiomPolicy) [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State}
    (earlier : BuildChecked policy premises state)
    (input : Theorem) (argument : CanonicalTerm) (inputRoot : Nat) (origin : Origin)
    (found : state.cache[inputRoot]? = some input) {out : Theorem}
    (accepted : instantiate? input argument = some out) :
    ∃ result root, emitSpec policy input argument inputRoot origin state = some (result, root) ∧
      BuildChecked policy premises result ∧ result.cache[root]? = some out ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  obtain ⟨block, computed, checked⟩ := specBlock?_checked_of_instantiate policy input argument origin accepted
  have selected : DerivationGraph.lookupPremises state.cache [inputRoot] = some [input] := by
    simp [DerivationGraph.lookupPremises, found]
  obtain ⟨result, root, emitted, resultChecked, rootFound, _, preserved⟩ :=
    emitBlock_checked earlier selected checked
  exact ⟨result, root, by simp [emitSpec, computed, emitted], resultChecked, rootFound, preserved⟩

/-- The external quantified proof must already occupy its physical slot. -/
theorem emitSpec_future_refused (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (argument : CanonicalTerm) (inputRoot : Nat) (origin : Origin)
    (state : ProofExecution.State) (future : state.cache.size ≤ inputRoot) :
    emitSpec policy input argument inputRoot origin state = none := by
  cases computed : specBlock? policy input argument origin with
  | none => simp [emitSpec, computed]
  | some block =>
      have refused := emitBlock_future_refused policy [inputRoot] block state
        (index := inputRoot) (by simp) future
      simp [emitSpec, computed, refused]

/-- Successful emission accounts for the actual eighteen appended nodes in
both the chronological cache and the retained receipt vector. -/
theorem emitSpec_size {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {argument : CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpec policy input argument inputRoot origin state = some (result, root)) :
    result.cache.size = state.cache.size + 18 ∧ result.receipts.size = state.receipts.size + 18 := by
  cases computed : specBlock? policy input argument origin with
  | none => simp [emitSpec, computed] at emitted
  | some block =>
      have actual : emitBlock policy [inputRoot] block state = some (result, root) := by
        simpa [emitSpec, computed] using emitted
      simpa only [specBlock?_size policy input argument origin computed] using emitBlock_size actual

theorem emitSpec_origins {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {argument : CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpec policy input argument inputRoot origin state = some (result, root)) :
    result.receipts.toList.map (·.origin) = state.receipts.toList.map (·.origin) ++ List.replicate 18 origin := by
  cases computed : specBlock? policy input argument origin with
  | none => simp [emitSpec, computed] at emitted
  | some block =>
      have actual : emitBlock policy [inputRoot] block state = some (result, root) := by
        simpa [emitSpec, computed] using emitted
      have preserved := congrArg (List.map (fun pair => pair.2)) (emitBlock_witnesses actual)
      simpa [List.map_map, Function.comp_def, List.map_append,
        specBlock?_origins policy input argument origin computed] using preserved

/-- Instantiate universal binders in their outside-to-inside execution order. -/
def instantiateMany? : Theorem → List CanonicalTerm → Option Theorem
  | input, [] => some input
  | input, argument :: rest => do
      let next ← instantiate? input argument
      instantiateMany? next rest

/-- Append repeated SPEC blocks, reusing each preceding root as the next
quantified premise. The graph stores every primitive occurrence once. -/
def emitSpecChain (policy : AxiomPolicy) [DecidablePred policy] :
    Theorem → List CanonicalTerm → Nat → Origin → ProofExecution.State →
      Option (ProofExecution.State × Nat)
  | _, [], inputRoot, _, state => some (state, inputRoot)
  | input, argument :: rest, inputRoot, origin, state => do
      let next ← instantiate? input argument
      let (result, root) ← emitSpec policy input argument inputRoot origin state
      emitSpecChain policy next rest root origin result

theorem emitSpecChain_checked (policy : AxiomPolicy) [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State}
    (earlier : BuildChecked policy premises state)
    (input : Theorem) (arguments : List CanonicalTerm) (inputRoot : Nat) (origin : Origin)
    (found : state.cache[inputRoot]? = some input) {out : Theorem}
    (accepted : instantiateMany? input arguments = some out) :
    ∃ result root,
      emitSpecChain policy input arguments inputRoot origin state = some (result, root) ∧
      BuildChecked policy premises result ∧ result.cache[root]? = some out ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  induction arguments generalizing input inputRoot state with
  | nil =>
      have exactOutput := Option.some.inj accepted
      exact ⟨state, inputRoot, rfl, earlier, exactOutput ▸ found, fun _ _ same => same⟩
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [instantiateMany?, first] at accepted
      | some next =>
          have remaining : instantiateMany? next rest = some out := by
            change (do
              let value ← instantiate? input argument
              instantiateMany? value rest) = some out at accepted
            rw [first] at accepted
            exact accepted
          obtain ⟨nextState, nextRoot, emitted, nextChecked, nextFound, preserved⟩ :=
            emitSpec_checked policy earlier input argument inputRoot origin found first
          obtain ⟨result, root, computed, checked, rootFound, stillPreserved⟩ :=
            ih nextChecked next nextRoot nextFound remaining
          exact ⟨result, root, by simpa [emitSpecChain, first, emitted] using computed,
            checked, rootFound, fun index fact previous => stillPreserved index fact (preserved index fact previous)⟩

/-- The complete successful computation adds eighteen primitive nodes per
instantiated binder, with no duplication of incoming shared proofs. -/
theorem emitSpecChain_size {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {arguments : List CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpecChain policy input arguments inputRoot origin state = some (result, root)) :
    result.cache.size = state.cache.size + 18 * arguments.length ∧
      result.receipts.size = state.receipts.size + 18 * arguments.length := by
  induction arguments generalizing input inputRoot state with
  | nil =>
      cases Option.some.inj emitted
      simp
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [emitSpecChain, first] at emitted
      | some next =>
          cases step : emitSpec policy input argument inputRoot origin state with
          | none => simp [emitSpecChain, first, step] at emitted
          | some nextState =>
              have tail : emitSpecChain policy next rest nextState.2 origin nextState.1 = some (result, root) := by
                simpa [emitSpecChain, first, step] using emitted
              have added := emitSpec_size step
              have later := ih tail
              simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
              constructor <;> omega

theorem emitSpecChain_origins {policy : AxiomPolicy} [DecidablePred policy]
    {input : Theorem} {arguments : List CanonicalTerm} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : emitSpecChain policy input arguments inputRoot origin state = some (result, root)) :
    result.receipts.toList.map (·.origin) = state.receipts.toList.map (·.origin) ++
      List.replicate (18 * arguments.length) origin := by
  induction arguments generalizing input inputRoot state with
  | nil =>
      cases Option.some.inj emitted
      simp
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [emitSpecChain, first] at emitted
      | some next =>
          cases step : emitSpec policy input argument inputRoot origin state with
          | none => simp [emitSpecChain, first, step] at emitted
          | some nextState =>
              have tail : emitSpecChain policy next rest nextState.2 origin nextState.1 = some (result, root) := by
                simpa [emitSpecChain, first, step] using emitted
              have preserved := ih tail
              rw [emitSpec_origins step] at preserved
              have merged : List.replicate 18 origin ++ List.replicate (18 * rest.length) origin =
                  List.replicate (18 * (rest.length + 1)) origin := by
                rw [← List.replicate_add]
                congr 1
                omega
              simpa only [List.append_assoc, merged, List.length_cons] using preserved

/-- Compile a complete instantiation chain with one external quantified proof. -/
def specChain? (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin) : Option ProofSystem.Certificate := do
  let (result, root) ← emitSpecChain policy input arguments 0 origin (start [input])
  pure (finish result root)

theorem specChain?_checked_of_instantiateMany (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin) {out : Theorem}
    (accepted : instantiateMany? input arguments = some out) :
    ∃ block, specChain? policy input arguments origin = some block ∧ BlockChecked policy [input] out block := by
  obtain ⟨result, root, computed, checked, rootFound, _⟩ := emitSpecChain_checked policy
    (start_checked policy [input]) input arguments 0 origin rfl accepted
  exact ⟨finish result root, by simp [specChain?, computed], finish_checked checked rootFound⟩

theorem specChain?_size (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (arguments : List CanonicalTerm) (origin : Origin)
    {block : ProofSystem.Certificate}
    (computed : specChain? policy input arguments origin = some block) :
    block.1.length = 18 * arguments.length := by
  cases emitted : emitSpecChain policy input arguments 0 origin (start [input]) with
  | none => simp [specChain?, emitted] at computed
  | some result =>
      have same : finish result.1 result.2 = block := by simpa [specChain?, emitted] using computed
      rw [← same]
      simpa only [finish, Array.length_toList, start, Array.size_empty, Nat.zero_add]
        using (emitSpecChain_size emitted).2

/-- A successful instantiation changes only the conclusion. -/
theorem instantiate?_parts (input : Theorem) (argument : CanonicalTerm) {out : Theorem}
    (accepted : instantiate? input argument = some out) :
    out.axioms = input.axioms ∧ out.sequent.hyp = input.sequent.hyp := by
  cases parsed : universalBody? input.sequent.concl with
  | none => simp [instantiate?, parsed] at accepted
  | some parsedBody =>
      unfold instantiate? at accepted
      rw [parsed] at accepted
      change (if same : Ty.same parsedBody.domain argument.ty = true then
          some (specResult input parsedBody.domain parsedBody.body parsedBody.checkedBody argument
            ((Ty.same_eq_true_iff _ _).mp same).symm) else none) = some out at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact ⟨rfl, rfl⟩
      · contradiction

/-- Chaining instantiations is ordinary option composition in execution order. -/
theorem instantiateMany?_append (input : Theorem) (first second : List CanonicalTerm) :
    instantiateMany? input (first ++ second) =
      (instantiateMany? input first).bind (fun next => instantiateMany? next second) := by
  induction first generalizing input with
  | nil => rfl
  | cons argument rest ih =>
      cases step : instantiate? input argument with
      | none => simp [instantiateMany?, step]
      | some next => simpa [instantiateMany?, step] using ih next

/-- Every finite instantiation chain retains all incoming proof dependencies. -/
theorem instantiateMany?_parts (input : Theorem) (arguments : List CanonicalTerm) {out : Theorem}
    (accepted : instantiateMany? input arguments = some out) :
    out.axioms = input.axioms ∧ out.sequent.hyp = input.sequent.hyp := by
  induction arguments generalizing input with
  | nil => cases Option.some.inj accepted; exact ⟨rfl, rfl⟩
  | cons argument rest ih =>
      cases first : instantiate? input argument with
      | none => simp [instantiateMany?, first] at accepted
      | some next =>
          have remaining : instantiateMany? next rest = some out := by
            change (do
              let value ← instantiate? input argument
              instantiateMany? value rest) = some out at accepted
            rw [first] at accepted
            exact accepted
          have firstParts := instantiate?_parts input argument first
          have laterParts := ih next remaining
          exact ⟨laterParts.1.trans firstParts.1, laterParts.2.trans firstParts.2⟩

namespace Controls

def functionDomain : Ty := .function Ty.bool Ty.bool

def reflexiveBody : DBTerm :=
  CanonicalTerm.equalityDB functionDomain (.bound 0) (.bound 0)

theorem reflexiveBody_checked : reflexiveBody.inferType [functionDomain] = some Ty.bool :=
  DBTerm.inferType_equalityDB (by simp [DBTerm.inferType]) (by simp [DBTerm.inferType])

def identityArgument : CanonicalTerm :=
  ⟨identityBool, functionDomain, DerivedRules.inferType_identityBool⟩

def universalReflexivity : CanonicalTerm :=
  ⟨forallAppDB functionDomain (.abs functionDomain reflexiveBody), Ty.bool,
    DerivedRules.inferType_forallAppDB_iff.mpr
      ⟨DBTerm.inferType_abs_of reflexiveBody_checked, rfl⟩⟩

/-- The external input retains both a hypothesis and an axiom tag. -/
def taggedInput : Theorem :=
  Theorem.axiomResult ⟨{DerivedRules.truthTerm}, universalReflexivity⟩
    ⟨rfl, by
      intro hypothesis member
      have same : hypothesis = DerivedRules.truthTerm := by simpa using member
      subst hypothesis
      rfl⟩

def instantiatedReflexivity : Theorem :=
  Theorem.preserveAxiomsResult taggedInput taggedInput.sequent.hyp
    (CanonicalTerm.equalityOfSameType identityArgument identityArgument rfl)

/-- An argument containing a genuine lambda binder is instantiated without
flattening, erasing, or replacing its canonical representation. -/
theorem binder_argument_instantiated :
    instantiate? taggedInput identityArgument = some instantiatedReflexivity := by
  have computed := instantiate?_eq_some taggedInput functionDomain reflexiveBody reflexiveBody_checked
    identityArgument rfl rfl
  have same : specResult taggedInput functionDomain reflexiveBody reflexiveBody_checked
      identityArgument rfl = instantiatedReflexivity := by
    apply Theorem.ext
    · rfl
    · apply Sequent.ext
      · rfl
      · apply CanonicalTerm.ext_term
        simp [specResult, instantiatedReflexivity, betaReduced, reflexiveBody,
          CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, DBTerm.instantiateAt,
          Theorem.preserveAxiomsResult, identityArgument]
  exact computed.trans (congrArg some same)

theorem binder_argument_checked (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    ∃ block, specBlock? policy taggedInput identityArgument origin = some block ∧
      BlockChecked policy [taggedInput] instantiatedReflexivity block :=
  specBlock?_checked_of_instantiate policy taggedInput identityArgument origin binder_argument_instantiated

/-- Successful execution keeps the nonempty source hypothesis and provenance. -/
theorem binder_argument_dependencies :
    instantiatedReflexivity.axioms = {taggedInput.sequent} ∧
      instantiatedReflexivity.sequent.hyp = {DerivedRules.truthTerm} := ⟨rfl, rfl⟩

theorem binder_argument_chain_checked (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    ∃ block, specChain? policy taggedInput [identityArgument] origin = some block ∧
      BlockChecked policy [taggedInput] instantiatedReflexivity block := by
  apply specChain?_checked_of_instantiateMany
  simp [instantiateMany?, binder_argument_instantiated]

theorem wrong_sort_refused : instantiate? taggedInput DerivedRules.truthTerm = none := by
  unfold instantiate?
  rw [universalBody?_complete _ functionDomain reflexiveBody reflexiveBody_checked rfl]
  change (if same : Ty.same functionDomain Ty.bool = true then _ else none) = none
  rw [dif_neg (by simp [Ty.same_eq_true_iff, functionDomain, Ty.function, Ty.bool])]

theorem wrong_sort_graph_refused (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    specBlock? policy taggedInput DerivedRules.truthTerm origin = none :=
  (specBlock?_eq_none_iff policy taggedInput DerivedRules.truthTerm origin).mpr wrong_sort_refused

def nonUniversalInput : Theorem := Theorem.emptyResult ∅ DerivedRules.truthTerm

theorem non_universal_refused : instantiate? nonUniversalInput identityArgument = none := by
  have refused : universalBody? DerivedRules.truthTerm = none := by
    simp [universalBody?, DerivedRules.truthTerm, truthDB, identityBool,
      CanonicalTerm.equalityDB, forallDB, DBTerm.same]
  simp [instantiate?, nonUniversalInput, refused, Theorem.emptyResult]

theorem non_universal_graph_refused (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    specBlock? policy nonUniversalInput identityArgument origin = none :=
  (specBlock?_eq_none_iff policy nonUniversalInput identityArgument origin).mpr non_universal_refused

theorem future_quantified_proof_refused (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin) :
    emitSpec policy taggedInput identityArgument 1 origin (start [taggedInput]) = none :=
  emitSpec_future_refused policy taggedInput identityArgument 1 origin (start [taggedInput]) (by rfl)

end Controls

end Mettapedia.Languages.HOLLight.QuantifierExpansion
