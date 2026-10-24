import Mettapedia.Languages.HOLLight.QuantifierExpansion
import Mettapedia.Languages.OpenTheory.DerivedRulesEta

/-!
# Constructive eta certificates with an explicit axiom policy

A source eta axiom is instantiated by the existing joint type/term
substitution, expanded to INST_TYPE followed by INST. The resulting graph
retains that exact axiom dependency. Its conclusion is the eta equation for
the supplied canonical function, including functions containing lambdas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExtensionalityExpansion

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open GraphExpansion PrimitiveTransport EqualityExpansion HypothesisExpansion
open ProofExecution (Origin)

def etaAxiomTheorem : Theorem := Theorem.axiomResult EtaAxiom.sequent EtaAxiom.sequent_isBool

def etaExpansion (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) : CanonicalTerm :=
  ⟨.abs domain (.app function.term (.bound 0)), .function domain codomain,
    DBTerm.inferType_abs_of (DBTerm.inferType_app_of
      (DBTerm.inferType_weaken_empty (functionType ▸ function.checked) _)
      (by simp [DBTerm.inferType]))⟩

def etaResult (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) : Theorem :=
  Theorem.preserveAxiomsResult etaAxiomTheorem ∅
    (CanonicalTerm.equalityOfSameType (etaExpansion domain codomain function functionType)
      function functionType.symm)

def etaSubstitution (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) : TypeCorrectTermSubstitution :=
  ⟨⟨(EtaAxiom.instantiateTypes domain codomain).raw.types,
    [(⟨EtaAxiom.functionName, .function domain codomain⟩, checkedSource function)]⟩, by
    intro entry member
    simp only [List.mem_singleton] at member
    subst entry
    exact (congrArg CanonicalTerm.ty (checkedSource_exact function)).trans functionType⟩

theorem etaSubstitution_conclusion (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) :
    substituteTheorem (etaSubstitution domain codomain function functionType) etaAxiomTheorem =
      etaResult domain codomain function functionType := by
  apply Theorem.ext
  · rfl
  · apply Sequent.ext
    · simp [substituteTheorem, etaAxiomTheorem, EtaAxiom.sequent, etaResult,
        Theorem.preserveAxiomsResult, Theorem.axiomResult,
        TypeCorrectTermSubstitution.applyHypotheses]
    · apply CanonicalTerm.ext_term
      have distinct : (EtaAxiom.codomainName == EtaAxiom.domainName) = false := by decide
      simp [substituteTheorem, etaSubstitution, etaAxiomTheorem, etaResult,
        Theorem.preserveAxiomsResult, Theorem.axiomResult, EtaAxiom.sequent,
        TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, EtaAxiom.instantiateTypes,
        Eta.equation, Eta.equationDB, Eta.expansionDB, Eta.functionVar,
        TermSubst.applyDB, TermSubst.lookup, TermSubst.keySame, TypeSubst.applyVar,
        TypeSubst.lookup, List.lookup, distinct, CanonicalTerm.equalityOfSameType,
        CanonicalTerm.equalityDB, CanonicalTerm.ofFormulaTranslation, etaExpansion, checkedSource_exact]

def etaAxiomBlock (origin : Origin) : ProofSystem.Certificate :=
  primitiveBlock (.axiom EtaAxiom.sequent) etaAxiomTheorem origin

theorem etaAxiomBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent) (origin : Origin) :
    BlockChecked policy [] etaAxiomTheorem (etaAxiomBlock origin) := by
  apply primitiveBlock_checked (.axiom EtaAxiom.sequent) etaAxiomTheorem origin
  apply (RuleRequest.check_eq_some_iff policy _ _).mpr
  exact ⟨rfl, admitted, EtaAxiom.sequent_isBool, rfl, rfl, rfl⟩

def etaBlock (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) (origin : Origin) :
    ProofSystem.Certificate :=
  let block := substitutionBlock (etaSubstitution domain codomain function functionType) etaAxiomTheorem origin
  ((etaAxiomBlock origin).1 ++ (expandBlock [0] 1 block).1, (expandBlock [0] 1 block).2)

theorem etaBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) (origin : Origin) :
    BlockChecked policy [] (etaResult domain codomain function functionType)
      (etaBlock domain codomain function functionType origin) := by
  have axiomChecked := etaAxiomBlock_checked policy admitted origin
  obtain ⟨initial, replayed, found⟩ := axiomChecked
  have initialEq : initial = #[etaAxiomTheorem] := by
    have step : replayFrom (ruleWitness policy) #[] (etaAxiomBlock origin).1 =
        some #[etaAxiomTheorem] := by
      have primitive := (RuleRequest.check_eq_some_iff policy _ _).mpr
        (show RuleRequest.Semantics policy (.axiom EtaAxiom.sequent) etaAxiomTheorem from
          ⟨rfl, admitted, EtaAxiom.sequent_isBool, rfl, rfl, rfl⟩)
      let node : ProofExecution.Receipt :=
        ⟨etaAxiomTheorem, .axiom EtaAxiom.sequent, [], origin⟩
      have accepted : node.replay (ruleWitness policy) #[] = some #[etaAxiomTheorem] :=
        (ProofSystem.node_replay_iff policy _ _ _).mpr ⟨rfl, primitive, rfl⟩
      change replayFrom (ruleWitness policy) #[] [node] = some #[etaAxiomTheorem]
      simp [replayFrom, accepted]
    exact Option.some.inj (replayed.symm.trans step)
  subst initial
  obtain ⟨final, extended, rootFound⟩ := expandBlock_checked
    (cache := #[etaAxiomTheorem]) (roots := [0]) (premises := [etaAxiomTheorem]) rfl
    (substitutionBlock_checked policy (etaSubstitution domain codomain function functionType)
      etaAxiomTheorem origin)
  refine ⟨final, replayFrom_append (ruleWitness policy) replayed extended, ?_⟩
  simpa [etaBlock, etaSubstitution_conclusion] using rootFound

theorem etaBlock_size (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) (origin : Origin) :
    (etaBlock domain codomain function functionType origin).1.length = 3 := rfl


/-! ## Function extensionality -/

open QuantifierExpansion

def pointwiseBody (codomain : Ty) (left right : CanonicalTerm) : DBTerm :=
  CanonicalTerm.equalityDB codomain (.app left.term (.bound 0)) (.app right.term (.bound 0))

theorem pointwiseBody_checked (domain codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function domain codomain) (rightType : right.ty = .function domain codomain) :
    (pointwiseBody codomain left right).inferType [domain] = some Ty.bool :=
  DBTerm.inferType_equalityDB
    (DBTerm.inferType_app_of (DBTerm.inferType_weaken_empty (leftType ▸ left.checked) _) (by simp))
    (DBTerm.inferType_app_of (DBTerm.inferType_weaken_empty (rightType ▸ right.checked) _) (by simp))

def extResult (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty) : Theorem :=
  Theorem.unionResult input etaAxiomTheorem input.sequent.hyp
    (CanonicalTerm.equalityOfSameType left right sameType)

structure ExtExpansion (policy : AxiomPolicy) [DecidablePred policy] (input : Theorem) where
  requests : List BlockRequest
  conclusion : Theorem
  checked : LocallyChecked policy #[input] requests

set_option maxHeartbeats 3000000 in
def extExpansion (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (input : Theorem) (binder : SourceVar) (codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function binder.ty codomain) (rightType : right.ty = .function binder.ty codomain)
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp)
    (absentLeft : ¬ DBTerm.FreeOccurrence binder left.term)
    (absentRight : ¬ DBTerm.FreeOccurrence binder right.term)
    (specializedBlock : ProofSystem.Certificate)
    (specializedChecked : BlockChecked policy [input]
      (specResult input binder.ty (pointwiseBody codomain left right)
        (pointwiseBody_checked binder.ty codomain left right leftType rightType)
        (CanonicalTerm.free binder) rfl) specializedBlock)
    (origin : Origin) : ExtExpansion policy input := by
  let argument := CanonicalTerm.free binder
  let specialized := specResult input binder.ty (pointwiseBody codomain left right)
    (pointwiseBody_checked binder.ty codomain left right leftType rightType) argument rfl
  let leftApplied := CanonicalTerm.applicationOfFunction left argument codomain (by simp [leftType, argument, CanonicalTerm.free])
  let rightApplied := CanonicalTerm.applicationOfFunction right argument codomain (by simp [rightType, argument, CanonicalTerm.free])
  have specializedView : CanonicalTerm.EqualityViewSemantics specialized.sequent.concl leftApplied rightApplied := by
    refine ⟨rfl, ?_⟩
    simp [specialized, specResult, betaReduced, pointwiseBody, leftApplied, rightApplied,
      CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityDB, Theorem.preserveAxiomsResult,
      DBTerm.instantiateAt, DBTerm.instantiateAt_closed left.checked,
      DBTerm.instantiateAt_closed right.checked]
  let abstracted := abstractionResult binder specialized leftApplied rightApplied rfl
  let leftEta := etaExpansion binder.ty codomain left leftType
  let rightEta := etaExpansion binder.ty codomain right rightType
  have abstractedView : CanonicalTerm.EqualityViewSemantics abstracted.sequent.concl leftEta rightEta := by
    refine ⟨rfl, ?_⟩
    simp [abstracted, abstractionResult, leftEta, rightEta, etaExpansion,
      leftApplied, rightApplied, CanonicalTerm.applicationOfFunction,
      CanonicalTerm.equalityOfSameType, CanonicalTerm.abstractFree, Theorem.preserveAxiomsResult,
      argument, CanonicalTerm.free, DBTerm.closeFreeAt,
      DBTerm.closeFreeAt_of_not_freeOccurrence absentLeft,
      DBTerm.closeFreeAt_of_not_freeOccurrence absentRight]
  let leftProof := etaResult binder.ty codomain left leftType
  let reversed := symmetryResult leftProof leftEta left leftType.symm
  let middle := transResult reversed abstracted left rightEta leftType
  have middleChecked : checkTrans reversed abstracted = some middle :=
    transResult_checked _ _ left leftEta rightEta leftType
      (equality_view left leftEta leftType) abstractedView
  let rightProof := etaResult binder.ty codomain right rightType
  let result := transResult middle rightProof left right (leftType.trans rightType.symm)
  have resultChecked : checkTrans middle rightProof = some result :=
    transResult_checked _ _ left rightEta right (leftType.trans rightType.symm)
      (equality_view left rightEta leftType) (equality_view rightEta right rightType.symm)
  let requests : List BlockRequest :=
    [⟨specialized, specializedBlock, [0], origin⟩,
     ⟨abstracted, abstractionBlock binder specialized leftApplied rightApplied rfl origin, [1], origin⟩,
     ⟨leftProof, etaBlock binder.ty codomain left leftType origin, [], origin⟩,
     ⟨reversed, symmetryBlock leftProof leftEta left leftType.symm origin, [3], origin⟩,
     ⟨middle, primitiveBlock (.inference (.trans reversed abstracted)) middle origin, [4, 2], origin⟩,
     ⟨rightProof, etaBlock binder.ty codomain right rightType origin, [], origin⟩,
     ⟨result, primitiveBlock (.inference (.trans middle rightProof)) result origin, [5, 6], origin⟩]
  refine ⟨requests, result, ?_⟩
  apply LocallyChecked.cons (premises := [input]) rfl
  · exact specializedChecked
  apply LocallyChecked.cons (premises := [specialized]) rfl
  · exact abstractionBlock_checked policy binder specialized leftApplied rightApplied rfl specializedView fresh origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact etaBlock_checked policy admitted binder.ty codomain left leftType origin
  apply LocallyChecked.cons (premises := [leftProof]) rfl
  · exact symmetryBlock_checked policy leftProof leftEta left leftType.symm (equality_view leftEta left leftType.symm) origin
  apply LocallyChecked.cons (premises := [reversed, abstracted]) rfl
  · exact primitiveBlock_checked (.inference (.trans reversed abstracted)) middle origin middleChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact etaBlock_checked policy admitted binder.ty codomain right rightType origin
  apply LocallyChecked.cons (premises := [middle, rightProof]) rfl
  · exact primitiveBlock_checked (.inference (.trans middle rightProof)) result origin resultChecked
  exact .nil _

theorem extExpansion_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (input : Theorem) (binder : SourceVar) (codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function binder.ty codomain) (rightType : right.ty = .function binder.ty codomain)
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp)
    (absentLeft : ¬ DBTerm.FreeOccurrence binder left.term)
    (absentRight : ¬ DBTerm.FreeOccurrence binder right.term)
    (specializedBlock : ProofSystem.Certificate)
    (specializedChecked : BlockChecked policy [input]
      (specResult input binder.ty (pointwiseBody codomain left right)
        (pointwiseBody_checked binder.ty codomain left right leftType rightType)
        (CanonicalTerm.free binder) rfl) specializedBlock) (origin : Origin) :
    (extExpansion policy admitted input binder codomain left right leftType rightType
      fresh absentLeft absentRight specializedBlock specializedChecked origin).conclusion =
      extResult input left right (leftType.trans rightType.symm) := by
  apply Theorem.ext
  · simp only [extExpansion, extResult, transResult, symmetryResult, abstractionResult,
      specResult, etaResult, Theorem.preserveAxiomsResult, Theorem.unionResult]
    ext sequent
    simp only [Finset.mem_union]
    tauto
  · apply Sequent.ext
    · simp [extExpansion, extResult, transResult, symmetryResult, abstractionResult,
        specResult, etaResult, Theorem.preserveAxiomsResult, Theorem.unionResult]
    · rfl



private theorem extExpansion_finished (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (input : Theorem) (binder : SourceVar) (codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function binder.ty codomain) (rightType : right.ty = .function binder.ty codomain)
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp)
    (absentLeft : ¬ DBTerm.FreeOccurrence binder left.term)
    (absentRight : ¬ DBTerm.FreeOccurrence binder right.term)
    (specializedBlock : ProofSystem.Certificate)
    (specializedChecked : BlockChecked policy [input]
      (specResult input binder.ty (pointwiseBody codomain left right)
        (pointwiseBody_checked binder.ty codomain left right leftType rightType)
        (CanonicalTerm.free binder) rfl) specializedBlock) (origin : Origin) :
    ∃ block, finishPlan policy (start [input]) #[0]
      (extExpansion policy admitted input binder codomain left right leftType rightType
        fresh absentLeft absentRight specializedBlock specializedChecked origin).requests 7 = some block ∧
      BlockChecked policy [input] (extResult input left right (leftType.trans rightType.symm)) block := by
  let expansion := extExpansion policy admitted input binder codomain left right leftType rightType
    fresh absentLeft absentRight specializedBlock specializedChecked origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[input]) (roots := #[0]) (start_checked policy [input]) rfl
    expansion.checked (index := 7) (conclusion := expansion.conclusion) (by rfl)
  exact ⟨block, computed, by simpa only [expansion, extExpansion_conclusion] using checked⟩

/-- Construct extensionality from the actual universal theorem and the checked
fresh argument. The finite specialization block is computed, not supplied. -/
def extBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (input : Theorem) (binder : SourceVar) (codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function binder.ty codomain) (rightType : right.ty = .function binder.ty codomain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB binder.ty
      (.abs binder.ty (pointwiseBody codomain left right)))
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp)
    (absentLeft : ¬ DBTerm.FreeOccurrence binder left.term)
    (absentRight : ¬ DBTerm.FreeOccurrence binder right.term)
    (origin : Origin) : Option ProofSystem.Certificate := by
  let specialization := specTypedBlock? policy input binder.ty (pointwiseBody codomain left right)
    (pointwiseBody_checked binder.ty codomain left right leftType rightType) (CanonicalTerm.free binder) rfl shape origin
  have available : specialization.isSome := by
    obtain ⟨block, computed, _⟩ := specTypedBlock?_checked policy input binder.ty (pointwiseBody codomain left right)
      (pointwiseBody_checked binder.ty codomain left right leftType rightType) (CanonicalTerm.free binder) rfl shape origin
    exact Option.isSome_iff_exists.mpr ⟨block, computed⟩
  let block := specialization.get available
  have checked : BlockChecked policy [input]
      (specResult input binder.ty (pointwiseBody codomain left right)
        (pointwiseBody_checked binder.ty codomain left right leftType rightType)
        (CanonicalTerm.free binder) rfl) block := by
    obtain ⟨actual, computed, checked⟩ := specTypedBlock?_checked policy input binder.ty (pointwiseBody codomain left right)
      (pointwiseBody_checked binder.ty codomain left right leftType rightType) (CanonicalTerm.free binder) rfl shape origin
    have same : block = actual := Option.some.inj ((Option.some_get available).trans computed)
    exact same.symm ▸ checked
  exact finishPlan policy (start [input]) #[0]
    (extExpansion policy admitted input binder codomain left right leftType rightType
      fresh absentLeft absentRight block checked origin).requests 7

theorem extBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    (input : Theorem) (binder : SourceVar) (codomain : Ty) (left right : CanonicalTerm)
    (leftType : left.ty = .function binder.ty codomain) (rightType : right.ty = .function binder.ty codomain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB binder.ty
      (.abs binder.ty (pointwiseBody codomain left right)))
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp)
    (absentLeft : ¬ DBTerm.FreeOccurrence binder left.term)
    (absentRight : ¬ DBTerm.FreeOccurrence binder right.term)
    (origin : Origin) :
    ∃ block, extBlock? policy admitted input binder codomain left right leftType rightType
      shape fresh absentLeft absentRight origin = some block ∧
      BlockChecked policy [input] (extResult input left right (leftType.trans rightType.symm)) block := by
  unfold extBlock?
  exact extExpansion_finished policy admitted input binder codomain left right leftType rightType
    fresh absentLeft absentRight _ _ origin

/-- Changed policies cannot authorize the dependency retained by eta's graph. -/
theorem etaResult_refused_without_axiom (policy : AxiomPolicy) [DecidablePred policy]
    (excluded : ¬ policy EtaAxiom.sequent) (domain codomain : Ty) (function : CanonicalTerm)
    (functionType : function.ty = .function domain codomain) (certificate : ProofSystem.Certificate) :
    (ProofSystem.checker policy).check (etaResult domain codomain function functionType) certificate = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have derives := (ProofSystem.checker_authority policy).sound _ _ accepted
  have allowed := derives_only_authorized_axioms policy (derives_shared policy derives)
  exact excluded (allowed EtaAxiom.sequent (Finset.mem_singleton_self _))

end Mettapedia.Languages.HOLLight.ExtensionalityExpansion
