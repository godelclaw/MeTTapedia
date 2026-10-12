import Mettapedia.Languages.HOLLight.MeTTa.CacheUnion
import Mettapedia.Languages.HOLLight.MeTTa.CacheDischarge
import Mettapedia.Languages.HOLLight.MeTTa.CacheInstantiation
import Mettapedia.Languages.HOLLight.MeTTa.Beta
import Mettapedia.Languages.HOLLight.MeTTa.Abstraction
import Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation
import Mettapedia.Languages.OpenTheory.BindingFormation
import Mettapedia.Languages.HOLLight.TheoryBooleanity

/-!
# Inference events earn authorized cache entries

Premises are recovered from an authorized source cache. The existing HOL
calculus supplies the rule; the actual authored dispatcher and publisher
supply the execution. Output formation follows from those recovered
premises, rather than a separately assumed output-formation interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval
open Effects (State)

/-- Reuse the actual source publisher after a concrete inference returns.
This lemma concerns publication only, not logical authorization. -/
private theorem publish_record (constants : Const → Atom) (cache : Cache) (next : Record)
    (operators declarations axioms key tag : Atom) (kind : InferenceKind) (payload first second : Atom)
    (receipts : List ReceiptKeys.Entry)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (origin : next.origin = .expression [.symbol "HOL:Origin", key, Premises.request kind payload first second])
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (inferred : PureReturns program
      (ProofEvents.inferenceEnvironment operators declarations axioms key kind payload first second
        (entries constants cache) receipts) state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) tag])) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
      (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
        (ReceiptKeys.table (⟨key, Premises.request kind payload first second,
          Premises.occurrences kind first second⟩ :: receipts))
        (entries constants ((key, next) :: cache))]) := by
  have returned := ProofEvents.authored_step_inference_return operators declarations axioms key
    (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
    (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
    (Premises.keys (next.dependencies.map (Dependency.atom constants))) tag kind payload first second
    (entries constants cache) receipts bindings state stateKey keyName requestName
    stateCaptured keyCaptured requestCaptured inferred
  simp only [Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh] at returned
  simpa [Publication.afterState, ProofLookup.sourceState, entries, Record.atom, origin,
    Publication.publishedValue, Publication.value, Representation.theoremAtom] using returned

/-- General transitivity, with arbitrary authorized hypotheses, axiom
dependencies and origins. Both premise occurrences survive publication,
including the case in which both keys select the same cache record. -/
theorem authored_trans_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (cache : Cache) (valid : Valid policy world cache) (left right : Record) (first second : Atom)
    (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
    (initial middle final : CanonicalTerm)
    (leftView : CanonicalTerm.EqualityViewSemantics left.conclusion initial middle)
    (rightView : CanonicalTerm.EqualityViewSemantics right.conclusion middle final)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "TRANS", first, second]) :
    ∃ next : Record,
      next.conclusion.term = CanonicalTerm.equalityDB initial.ty initial.term final.term ∧
      next.hypotheses = CacheUnion.hypotheses constants left right ∧
      next.dependencies = CacheUnion.dependencies constants left right ∧
      next.origin = .expression [.symbol "HOL:Origin", key, .expression [.symbol "TRANS", first, second]] ∧
      InferenceRequest.Semantics (.trans left.fact right.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "TRANS", first, second], [first, second]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have leftDerived := stored_lookup_derived policy world cache valid first left firstSelected
  have rightDerived := stored_lookup_derived policy world cache valid second right secondSelected
  have lastChecked : final.term.inferType [] = some initial.ty := by
    rw [leftView.1, rightView.1]
    exact final.checked
  let conclusion := CanonicalTerm.equalityOfSameType initial final (leftView.1.trans rightView.1)
  let origin : Atom := .expression [.symbol "HOL:Origin", key, .expression [.symbol "TRANS", first, second]]
  let next := CacheUnion.record constants left right conclusion origin
  have formed : AnnotationsFormed world.signature conclusion.term := by
    have firstFormed := leftDerived.wellFormed.1.1
    have secondFormed := rightDerived.wellFormed.1.1
    change AnnotationsFormed world.signature left.conclusion.term at firstFormed
    change AnnotationsFormed world.signature right.conclusion.term at secondFormed
    rw [leftView.2] at firstFormed
    rw [rightView.2] at secondFormed
    cases firstFormed with
    | app headFormed _ =>
      cases headFormed with
      | app equalityFormed initialFormed =>
        cases secondFormed with
        | app _ finalFormed => exact .app (.app equalityFormed initialFormed) finalFormed
  have semantics : InferenceRequest.Semantics (.trans left.fact right.fact) next.fact := by
    refine ⟨initial, middle, middle, final, conclusion, leftView, rightView, rfl,
      ⟨leftView.1.trans rightView.1, rfl⟩, ?_⟩
    exact CacheUnion.record_parts world constants identified left right
      leftDerived.wellFormed rightDerived.wellFormed conclusion origin
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms])
    (by
      intro premise member
      simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact leftDerived
      · exact rightDerived)
    (CacheUnion.record_formed world constants left right leftDerived.wellFormed rightDerived.wellFormed
      conclusion formed origin)
  have firstFound : (entries constants cache).lookup first = some
      (Transitivity.theoremValue constants [] initial.ty initial.term middle.term
        (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (left.dependencies.map (Dependency.atom constants)) left.origin) := by
    rw [lookup_entries, firstSelected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, leftView.2]
  have secondFound : (entries constants cache).lookup second = some
      (Transitivity.theoremValue constants [] initial.ty middle.term final.term
        (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (right.dependencies.map (Dependency.atom constants)) right.origin) := by
    rw [lookup_entries, secondSelected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, rightView.2, leftView.1]
  have middleFormed : AnnotationsFormed world.signature middle.term := by
    have annotations := leftDerived.wellFormed.1.1
    change AnnotationsFormed world.signature left.conclusion.term at annotations
    rw [leftView.2] at annotations
    cases annotations with
    | app _ operandFormed => exact operandFormed
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .trans (.symbol "None")
    first second (entries constants cache) receipts
  have inferred := InferenceExecution.authored_infer_trans_return world constants identified equalityIdentity
    bound state [] initial.ty initial.term middle.term middle.term final.term initial.checked lastChecked
    middleFormed middleFormed
    (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (left.dependencies.map (Dependency.atom constants)) (right.dependencies.map (Dependency.atom constants))
    left.origin right.origin operators declarations axioms (ReceiptKeys.table receipts)
    (entries constants cache) first second firstFound secondFound "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "TRANS")]) := by
    simpa [DBTerm.same_eq_true_iff, Transitivity.theoremValue, Representation.theoremAtom,
      Publication.value, next, CacheUnion.record, conclusion, CanonicalTerm.equalityOfSameType, CacheUnion.hypotheses_encoded,
      CacheUnion.dependencies_encoded] using inferred
  have returned := ProofEvents.authored_step_inference_return operators declarations axioms key
    (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
    (Representation.termAtom Representation.registeredOperatorAtom constants [] conclusion.term)
    (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "TRANS")
    .trans (.symbol "None") first second (entries constants cache) receipts
    bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult
  refine ⟨next, rfl, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  simp only [Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh] at returned
  simpa [Publication.afterState, ProofLookup.sourceState, entries, next, CacheUnion.record, origin,
    Record.atom, Publication.publishedValue, Publication.value, Representation.theoremAtom,
    Premises.request, Premises.occurrences] using returned

/-- Different middle terms are refused by the actual dispatcher, even when
both requested premise addresses are occupied by formed equality records. -/
theorem authored_trans_mismatched_middle_refused (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType [] = some type) (rightChecked : right.inferType [] = some type)
    (firstFormed : AnnotationsFormed world.signature middle1)
    (secondFormed : AnnotationsFormed world.signature middle2) (different : middle1 ≠ middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants [] type left middle1 hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Transitivity.theoremValue constants [] type middle2 right hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "TRANS", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  have returned := InferenceExecution.authored_infer_trans_return world constants identified equalityIdentity
    bindings state [] type left middle1 middle2 right leftChecked rightChecked firstFormed secondFormed
    hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts cache first second
    firstFound secondFound stateKey requestKey stateCaptured requestCaptured
  simpa [DBTerm.same_eq_true_iff, different] using returned

/-- General EQ_MP earns Booleanity and formation from its authorized
premises. The source's additional result-type guard is therefore derived,
not an assumed interface for theorem-shaped data. -/
theorem authored_eq_mp_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (cache : Cache) (valid : Valid policy world cache) (equality premise : Record) (first second : Atom)
    (firstSelected : cache.lookup first = some equality) (secondSelected : cache.lookup second = some premise)
    (target : CanonicalTerm)
    (view : CanonicalTerm.EqualityViewSemantics equality.conclusion premise.conclusion target)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "EQ_MP", first, second]) :
    ∃ next : Record, next.conclusion = target ∧
      next.hypotheses = CacheUnion.hypotheses constants equality premise ∧
      next.dependencies = CacheUnion.dependencies constants equality premise ∧
      next.origin = .expression [.symbol "HOL:Origin", key, .expression [.symbol "EQ_MP", first, second]] ∧
      InferenceRequest.Semantics (.eqMp equality.fact premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "EQ_MP", first, second], [first, second]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have equalityDerived := stored_lookup_derived policy world cache valid first equality firstSelected
  have premiseDerived := stored_lookup_derived policy world cache valid second premise secondSelected
  have premiseBoolean : premise.conclusion.ty = Ty.bool := premiseDerived.conclusionBoolean
  have targetBoolean : target.ty = Ty.bool := view.1.symm.trans premiseBoolean
  have targetFormed : AnnotationsFormed world.signature target.term := by
    have formed := equalityDerived.wellFormed.1.1
    change AnnotationsFormed world.signature equality.conclusion.term at formed
    rw [view.2] at formed
    cases formed with
    | app _ rightFormed => exact rightFormed
  have booleanFormed : TypeFormed world.signature Ty.bool :=
    AnnotationsFormed.inferredType world.signature functionArity premiseDerived.wellFormed.1.1
      (ContextFormed.nil _) (by simpa only [Record.fact, premiseBoolean] using premise.conclusion.checked)
  let origin := Atom.expression [.symbol "HOL:Origin", key, .expression [.symbol "EQ_MP", first, second]]
  let next := CacheUnion.record constants equality premise target origin
  have semantics : InferenceRequest.Semantics (.eqMp equality.fact premise.fact) next.fact :=
    ⟨premise.conclusion, target, view, rfl, CacheUnion.record_parts world constants identified equality premise
      equalityDerived.wellFormed premiseDerived.wellFormed target origin⟩
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms])
    (by
      intro parent member
      simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact equalityDerived
      · exact premiseDerived)
    (CacheUnion.record_formed world constants equality premise equalityDerived.wellFormed premiseDerived.wellFormed
      target targetFormed origin)
  have firstFound : (entries constants cache).lookup first = some
      (Transitivity.theoremValue constants [] premise.conclusion.ty premise.conclusion.term target.term
        (equality.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (equality.dependencies.map (Dependency.atom constants)) equality.origin) := by
    rw [lookup_entries, firstSelected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, view.2]
  have secondFound : (entries constants cache).lookup second = some
      (Representation.theoremAtom constants [] premise.conclusion.term
        (premise.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (premise.dependencies.map (Dependency.atom constants)) premise.origin) := by
    rw [lookup_entries, secondSelected]
    rfl
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .eqMp (.symbol "None")
    first second (entries constants cache) receipts
  have inferred := InferenceExecution.authored_infer_eq_mp_return world constants identified equalityIdentity
    bound state [] target.ty premise.conclusion.ty premise.conclusion.term target.term premise.conclusion.term
    target.checked (by simpa only [targetBoolean] using booleanFormed) booleanFormed
    premiseDerived.wellFormed.1.1 premiseDerived.wellFormed.1.1
    (equality.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (premise.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (equality.dependencies.map (Dependency.atom constants)) (premise.dependencies.map (Dependency.atom constants))
    equality.origin premise.origin operators declarations axioms (ReceiptKeys.table receipts)
    (entries constants cache) first second firstFound secondFound "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] target.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "EQ_MP")]) := by
    simpa [DBTerm.same_eq_true_iff, Ty.same_eq_true_iff, targetBoolean, EqualityModusPonens.result,
      Representation.theoremAtom, Publication.value, next, CacheUnion.record,
      CacheUnion.hypotheses_encoded, CacheUnion.dependencies_encoded] using inferred
  refine ⟨next, rfl, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  exact publish_record constants cache next operators declarations axioms key (.symbol "EQ_MP")
    .eqMp (.symbol "None") first second receipts receiptFresh cacheFresh rfl
    bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult

/-- General application congruence uses the registered polymorphic equality
declaration at the inferred codomain. Both application annotations and all
metadata support are constructed from the earned premise derivations. -/
theorem authored_mk_comb_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (cache : Cache) (valid : Valid policy world cache) (functions arguments : Record) (first second : Atom)
    (firstSelected : cache.lookup first = some functions) (secondSelected : cache.lookup second = some arguments)
    (functionLeft functionRight argumentLeft argumentRight : CanonicalTerm) (domain codomain : Ty)
    (functionView : CanonicalTerm.EqualityViewSemantics functions.conclusion functionLeft functionRight)
    (argumentView : CanonicalTerm.EqualityViewSemantics arguments.conclusion argumentLeft argumentRight)
    (functionType : functionLeft.ty = .function domain codomain) (argumentType : argumentLeft.ty = domain)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "MK_COMB", first, second]) :
    ∃ next : Record,
      next.conclusion.term = CanonicalTerm.equalityDB codomain
        (.app functionLeft.term argumentLeft.term) (.app functionRight.term argumentRight.term) ∧
      next.hypotheses = CacheUnion.hypotheses constants functions arguments ∧
      next.dependencies = CacheUnion.dependencies constants functions arguments ∧
      next.origin = .expression [.symbol "HOL:Origin", key, .expression [.symbol "MK_COMB", first, second]] ∧
      InferenceRequest.Semantics (.mkComb functions.fact arguments.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "MK_COMB", first, second], [first, second]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have functionsDerived := stored_lookup_derived policy world cache valid first functions firstSelected
  have argumentsDerived := stored_lookup_derived policy world cache valid second arguments secondSelected
  have leftFunction : functionLeft.ty.destFunction? = some (argumentLeft.ty, codomain) := by
    rw [functionType, argumentType]
    exact Ty.destFunction?_function _ _
  have rightFunction : functionRight.ty.destFunction? = some (argumentRight.ty, codomain) := by
    rw [← functionView.1, functionType, ← argumentView.1, argumentType]
    exact Ty.destFunction?_function _ _
  let applicationLeft := CanonicalTerm.applicationOfFunction functionLeft argumentLeft codomain leftFunction
  let applicationRight := CanonicalTerm.applicationOfFunction functionRight argumentRight codomain rightFunction
  let conclusion := CanonicalTerm.equalityOfSameType applicationLeft applicationRight rfl
  let origin := Atom.expression [.symbol "HOL:Origin", key, .expression [.symbol "MK_COMB", first, second]]
  let next := CacheUnion.record constants functions arguments conclusion origin
  have functionAnnotations : AnnotationsFormed world.signature functionLeft.term ∧
      AnnotationsFormed world.signature functionRight.term := by
    have formed := functionsDerived.wellFormed.1.1
    change AnnotationsFormed world.signature functions.conclusion.term at formed
    rw [functionView.2] at formed
    cases formed with
    | app headFormed rightFormed =>
      cases headFormed with
      | app _ leftFormed => exact ⟨leftFormed, rightFormed⟩
  have argumentAnnotations : AnnotationsFormed world.signature argumentLeft.term ∧
      AnnotationsFormed world.signature argumentRight.term := by
    have formed := argumentsDerived.wellFormed.1.1
    change AnnotationsFormed world.signature arguments.conclusion.term at formed
    rw [argumentView.2] at formed
    cases formed with
    | app headFormed rightFormed =>
      cases headFormed with
      | app _ leftFormed => exact ⟨leftFormed, rightFormed⟩
  have leftFormed : AnnotationsFormed world.signature applicationLeft.term :=
    .app functionAnnotations.1 argumentAnnotations.1
  have rightFormed : AnnotationsFormed world.signature applicationRight.term :=
    .app functionAnnotations.2 argumentAnnotations.2
  have codomainFormed : TypeFormed world.signature codomain :=
    AnnotationsFormed.inferredType world.signature functionArity leftFormed (ContextFormed.nil _) applicationLeft.checked
  have functionsBoolean : functions.conclusion.ty = Ty.bool := functionsDerived.conclusionBoolean
  have booleanFormed : TypeFormed world.signature Ty.bool :=
    AnnotationsFormed.inferredType world.signature functionArity functionsDerived.wellFormed.1.1
      (ContextFormed.nil _) (by simpa only [Record.fact, functionsBoolean] using functions.conclusion.checked)
  have formed : AnnotationsFormed world.signature conclusion.term :=
    PrimitiveEqualityFormation.equation_annotations world.signature equalityParameter codomain functionArity
      booleanFormed codomainFormed equalityRegistered applicationLeft.term applicationRight.term leftFormed rightFormed
  have semantics : InferenceRequest.Semantics (.mkComb functions.fact arguments.fact) next.fact :=
    ⟨functionLeft, functionRight, argumentLeft, argumentRight, applicationLeft, applicationRight, conclusion,
      functionView, argumentView,
      CanonicalTerm.applicationOfFunction_semantics _ _ _ leftFunction,
      CanonicalTerm.applicationOfFunction_semantics _ _ _ rightFunction,
      CanonicalTerm.equalityOfSameType_semantics applicationLeft applicationRight rfl,
      CacheUnion.record_parts world constants identified functions arguments functionsDerived.wellFormed
        argumentsDerived.wellFormed conclusion origin⟩
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms])
    (by
      intro parent member
      simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact functionsDerived
      · exact argumentsDerived)
    (CacheUnion.record_formed world constants functions arguments functionsDerived.wellFormed argumentsDerived.wellFormed
      conclusion formed origin)
  have firstFound : (entries constants cache).lookup first = some
      (Transitivity.theoremValue constants [] (.function domain codomain) functionLeft.term functionRight.term
        (functions.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (functions.dependencies.map (Dependency.atom constants)) functions.origin) := by
    rw [lookup_entries, firstSelected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, functionView.2, functionType]
  have secondFound : (entries constants cache).lookup second = some
      (Transitivity.theoremValue constants [] domain argumentLeft.term argumentRight.term
        (arguments.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (arguments.dependencies.map (Dependency.atom constants)) arguments.origin) := by
    rw [lookup_entries, secondSelected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, argumentView.2, argumentType]
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .mkComb (.symbol "None")
    first second (entries constants cache) receipts
  have inferred := InferenceExecution.authored_infer_mk_comb_return constants equalityIdentity bound state [] domain codomain
    functionLeft.term functionRight.term argumentLeft.term argumentRight.term
    (by simpa only [functionType] using functionLeft.checked)
    (by simpa only [← functionView.1, functionType] using functionRight.checked)
    (by simpa only [argumentType] using argumentLeft.checked)
    (by simpa only [← argumentView.1, argumentType] using argumentRight.checked)
    (functions.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (arguments.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (functions.dependencies.map (Dependency.atom constants)) (arguments.dependencies.map (Dependency.atom constants))
    functions.origin arguments.origin operators declarations axioms (ReceiptKeys.table receipts)
    (entries constants cache) first second firstFound secondFound "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "MK_COMB")]) := by
    simpa [Transitivity.theoremValue, Representation.theoremAtom, Publication.value,
      next, CacheUnion.record, conclusion, CanonicalTerm.equalityOfSameType,
      applicationLeft, applicationRight, CanonicalTerm.applicationOfFunction,
      CacheUnion.hypotheses_encoded, CacheUnion.dependencies_encoded] using inferred
  refine ⟨next, rfl, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  exact publish_record constants cache next operators declarations axioms key (.symbol "MK_COMB")
    .mkComb (.symbol "None") first second receipts receiptFresh cacheFresh rfl
    bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult

/-- Occupied premise addresses do not authorize a different supplied claim:
the actual EQ_MP comparison refuses it before result publication. -/
theorem authored_eq_mp_mismatched_claim_refused (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (rightType equalityType : Ty) (left right claim : DBTerm)
    (rightChecked : right.inferType [] = some rightType)
    (rightTypeFormed : TypeFormed world.signature rightType) (booleanFormed : TypeFormed world.signature Ty.bool)
    (leftFormed : AnnotationsFormed world.signature left) (claimFormed : AnnotationsFormed world.signature claim)
    (different : left ≠ claim)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some (Transitivity.theoremValue constants [] equalityType left right
      hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some (Representation.theoremAtom constants [] claim hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  have returned := InferenceExecution.authored_infer_eq_mp_return world constants identified equalityIdentity
    bindings state [] rightType equalityType left right claim rightChecked rightTypeFormed booleanFormed
    leftFormed claimFormed hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts cache
    first second firstFound secondFound stateKey requestKey stateCaptured requestCaptured
  simpa [DBTerm.same_eq_true_iff, different] using returned

/-- The actual deduction event discharges opposite conclusions and earns its
registered result from both selected premises. Output formation, Boolean
operands and the authorized cache extension follow from those premises. -/
theorem authored_deduct_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (cache : Cache) (valid : Valid policy world cache) (left right : Record) (first second : Atom)
    (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]) :
    ∃ next : Record,
      next.conclusion.term = CanonicalTerm.equalityDB Ty.bool left.conclusion.term right.conclusion.term ∧
      next.hypotheses = CacheDischarge.hypotheses constants left right ∧
      next.dependencies = CacheUnion.dependencies constants left right ∧
      next.origin = .expression [.symbol "HOL:Origin", key, .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]] ∧
      InferenceRequest.Semantics (.deductAntisym left.fact right.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second], [first, second]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have leftDerived := stored_lookup_derived policy world cache valid first left firstSelected
  have rightDerived := stored_lookup_derived policy world cache valid second right secondSelected
  have leftBoolean : left.conclusion.ty = Ty.bool := leftDerived.conclusionBoolean
  have rightBoolean : right.conclusion.ty = Ty.bool := rightDerived.conclusionBoolean
  let conclusion := CanonicalTerm.equalityOfSameType left.conclusion right.conclusion
    (leftBoolean.trans rightBoolean.symm)
  let origin : Atom := .expression [.symbol "HOL:Origin", key, .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]]
  let next := CacheDischarge.record constants left right conclusion origin
  have booleanFormed : TypeFormed world.signature Ty.bool :=
    AnnotationsFormed.inferredType world.signature functionArity leftDerived.wellFormed.1.1
      (ContextFormed.nil _) (by simpa only [Record.fact, leftBoolean] using left.conclusion.checked)
  have formed : AnnotationsFormed world.signature conclusion.term := by
    have annotations := PrimitiveEqualityFormation.equation_annotations world.signature equalityParameter Ty.bool
      functionArity booleanFormed booleanFormed equalityRegistered left.conclusion.term right.conclusion.term
      leftDerived.wellFormed.1.1 rightDerived.wellFormed.1.1
    simpa only [conclusion, CanonicalTerm.equalityOfSameType, leftBoolean] using annotations
  have semantics : InferenceRequest.Semantics (.deductAntisym left.fact right.fact) next.fact :=
    ⟨conclusion, CanonicalTerm.equalityOfSameType_semantics left.conclusion right.conclusion
      (leftBoolean.trans rightBoolean.symm),
      CacheDischarge.record_parts world constants identified left right leftDerived.wellFormed rightDerived.wellFormed
        conclusion origin⟩
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms])
    (by
      intro premise member
      simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact leftDerived
      · exact rightDerived)
    (CacheDischarge.record_formed world constants left right leftDerived.wellFormed rightDerived.wellFormed
      conclusion formed origin)
  have firstFound : (entries constants cache).lookup first = some
      (Representation.theoremAtom constants [] left.conclusion.term
        (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (left.dependencies.map (Dependency.atom constants)) left.origin) := by
    rw [lookup_entries, firstSelected]
    rfl
  have secondFound : (entries constants cache).lookup second = some
      (Representation.theoremAtom constants [] right.conclusion.term
        (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (right.dependencies.map (Dependency.atom constants)) right.origin) := by
    rw [lookup_entries, secondSelected]
    rfl
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .deductAntisym (.symbol "None")
    first second (entries constants cache) receipts
  have inferred := DeductionAntisymmetry.Dispatcher.authored_infer_deduct_return constants equalityIdentity bound state
    [] Ty.bool left.conclusion.term right.conclusion.term
    (by simpa only [leftBoolean] using left.conclusion.checked)
    (by simpa only [rightBoolean] using right.conclusion.checked)
    (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (left.dependencies.map (Dependency.atom constants)) (right.dependencies.map (Dependency.atom constants))
    left.origin right.origin operators declarations axioms (ReceiptKeys.table receipts) first second
    (entries constants cache) firstFound secondFound "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "DEDUCT_ANTISYM_RULE")]) := by
    simpa only [DeductionAntisymmetry.result, Transitivity.theoremValue, Representation.theoremAtom,
      Publication.value, next, CacheDischarge.record, conclusion, CanonicalTerm.equalityOfSameType, leftBoolean,
      CacheDischarge.hypotheses_encoded world constants identified left right leftDerived.wellFormed rightDerived.wellFormed,
      CacheUnion.dependencies_encoded, TheoremMetadata.hypothesisAtom] using inferred
  refine ⟨next, ?_, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  · simp only [next, CacheDischarge.record, conclusion, CanonicalTerm.equalityOfSameType, leftBoolean]
  · exact publish_record constants cache next operators declarations axioms key (.symbol "DEDUCT_ANTISYM_RULE")
      .deductAntisym (.symbol "None") first second receipts receiptFresh cacheFresh rfl
      bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult

/-- Primitive BETA accepts the actual named-variable redex, earns its
registered equality theorem and extends the authorized source cache. It
introduces no hypotheses, dependencies or generalized beta admission. -/
theorem authored_beta_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (needle : SourceVar) (body : CheckedSourceTerm)
    (resolved : TermReading.SourceResolved world.signature (Beta.redex needle body.source))
    (annotations : AnnotationsFormed world.signature ((Beta.redex needle body.source).toDB []))
    (cache : Cache) (valid : Valid policy world cache) (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "BETA", TermReading.sourceAtom (Beta.redex needle body.source)]) :
    ∃ (source : CheckedSourceTerm) (next : Record), source.source = Beta.redex needle body.source ∧
      next.hypotheses = [] ∧ next.dependencies = [] ∧
      next.conclusion.term = CanonicalTerm.equalityDB body.ty
        ((Beta.redex needle body.source).toDB []) body.canonical.term ∧
      InferenceRequest.Semantics (.beta source) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "BETA", TermReading.sourceAtom (Beta.redex needle body.source)], []⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let payload := TermReading.sourceAtom (Beta.redex needle body.source)
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .beta payload
    (.symbol "None") (.symbol "None") (entries constants cache) receipts
  obtain ⟨source, out, sourceShape, semantics, _, dependencies, hypotheses, conclusionShape, inferred⟩ :=
    Beta.authored_beta_shared_derivation world table origins constants equalityIdentity needle body resolved annotations
      bound state axioms (ReceiptKeys.table receipts) (entries constants cache) "state" "request" rfl rfl policy
  have bodyFormed : AnnotationsFormed world.signature body.canonical.term := by
    have annotated := annotations
    have shape : (Beta.redex needle body.source).toDB [] =
        .app (.abs needle.ty (body.source.toDB [needle])) (.free needle) := by
      simp [Beta.redex, SourceTerm.toDB, boundIndex]
    rw [shape] at annotated
    cases annotated with
    | app functionFormed argumentFormed =>
      cases functionFormed with
      | abs _ innerFormed =>
        have opened := AnnotationsFormed.instantiateAt world.signature (.free needle) argumentFormed innerFormed 0
        rw [SourceTerm.instantiateAt_toDB_singleton body.source needle] at opened
        exact opened
  have operandFormed : TypeFormed world.signature body.ty :=
    AnnotationsFormed.inferredType world.signature functionArity bodyFormed (ContextFormed.nil _) body.canonical.checked
  have conclusionFormed : AnnotationsFormed world.signature out.sequent.concl.term := by
    rw [conclusionShape]
    exact PrimitiveEqualityFormation.equation_annotations world.signature equalityParameter body.ty functionArity
      booleanFormed operandFormed equalityRegistered _ _ annotations bodyFormed
  have outFormed : TheoremFormed world.signature out := by
    refine ⟨⟨conclusionFormed, ?_⟩, ?_⟩
    · intro term member
      rw [hypotheses] at member
      simp at member
    · intro sequent member
      rw [dependencies] at member
      simp at member
  have derived : TheoryDerives policy world out := .inference (request := .beta source) semantics
    (by
      refine ⟨by simp [InferenceFormation.types], ?_⟩
      intro term member
      simp only [InferenceFormation.terms, List.mem_singleton] at member
      rw [member]
      simpa only [CheckedSourceTerm.canonical, sourceShape] using annotations)
    (by simp [InferenceRequest.premises]) outFormed
  let next : Record := ⟨[], out.sequent.concl, [],
    .expression [.symbol "HOL:Origin", key, .expression [.symbol "BETA", payload]]⟩
  have factSame : next.fact = out := by
    apply Theorem.ext
    · simpa [next, Record.fact] using dependencies.symm
    · exact Sequent.ext (by simpa [next, Record.fact] using hypotheses.symm) rfl
  have authorized : TheoryDerives policy world next.fact := factSame ▸ derived
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
        (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
        (.symbol "HOL:Nil") (.symbol "BETA")]) := inferred
  refine ⟨source, next, sourceShape, rfl, rfl, conclusionShape, factSame ▸ semantics, authorized,
    insert_valid valid key next authorized, ?_⟩
  exact publish_record constants cache next operators declarations axioms key (.symbol "BETA")
    .beta payload (.symbol "None") (.symbol "None") receipts receiptFresh cacheFresh rfl
    bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult

/-- Closing a variable earns the registered ABS result from an authorized
premise. The actual hypothesis guard establishes the source freshness
condition; the ordered hypotheses and dependencies remain unchanged. -/
theorem authored_abs_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (resolved : TermReading.SourceResolved world.signature (.var needle.name needle.ty))
    (cache : Cache) (valid : Valid policy world cache) (premise : Record) (input : Atom)
    (selected : cache.lookup input = some premise) (left right : CanonicalTerm)
    (view : CanonicalTerm.EqualityViewSemantics premise.conclusion left right)
    (fresh : ¬ FreeInHypotheses needle premise.fact.sequent.hyp)
    (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), input]) :
    ∃ next : Record,
      next.conclusion.term = CanonicalTerm.equalityDB (.function needle.ty left.ty)
        (left.abstractFree needle).term (right.abstractFree needle).term ∧
      next.hypotheses = premise.hypotheses ∧ next.dependencies = premise.dependencies ∧
      InferenceRequest.Semantics (.abs needle premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), input],
            [input]⟩ :: receipts)) (entries constants ((key, next) :: cache))]) := by
  have premiseDerived := stored_lookup_derived policy world cache valid input premise selected
  have annotations : AnnotationsFormed world.signature left.term ∧
      AnnotationsFormed world.signature right.term := by
    have formed := premiseDerived.wellFormed.1.1
    change AnnotationsFormed world.signature premise.conclusion.term at formed
    rw [view.2] at formed
    cases formed with
    | app headFormed rightFormed =>
      cases headFormed with
      | app _ leftFormed => exact ⟨leftFormed, rightFormed⟩
  let abstractLeft := left.abstractFree needle
  let abstractRight := right.abstractFree needle
  have sameType : abstractLeft.ty = abstractRight.ty := by
    simp only [abstractLeft, abstractRight, CanonicalTerm.abstractFree, view.1]
  let conclusion := CanonicalTerm.equalityOfSameType abstractLeft abstractRight sameType
  let payload := TermReading.sourceAtom (.var needle.name needle.ty)
  let next : Record := ⟨premise.hypotheses, conclusion, premise.dependencies,
    .expression [.symbol "HOL:Origin", key, .expression [.symbol "ABS", payload, input]]⟩
  have leftFormed : AnnotationsFormed world.signature abstractLeft.term :=
    AnnotationsFormed.abstractFree world.signature needle needleFormed left annotations.1
  have rightFormed : AnnotationsFormed world.signature abstractRight.term :=
    AnnotationsFormed.abstractFree world.signature needle needleFormed right annotations.2
  have operandFormed : TypeFormed world.signature abstractLeft.ty :=
    AnnotationsFormed.inferredType world.signature functionArity leftFormed (ContextFormed.nil _) abstractLeft.checked
  have premiseBoolean : premise.conclusion.ty = Ty.bool := premiseDerived.conclusionBoolean
  have booleanFormed : TypeFormed world.signature Ty.bool :=
    AnnotationsFormed.inferredType world.signature functionArity premiseDerived.wellFormed.1.1
      (ContextFormed.nil _) (by simpa only [Record.fact, premiseBoolean] using premise.conclusion.checked)
  have conclusionFormed : AnnotationsFormed world.signature conclusion.term :=
    PrimitiveEqualityFormation.equation_annotations world.signature equalityParameter abstractLeft.ty functionArity
      booleanFormed operandFormed equalityRegistered abstractLeft.term abstractRight.term leftFormed rightFormed
  have semantics : InferenceRequest.Semantics (.abs needle premise.fact) next.fact := by
    refine ⟨fresh, left, right, abstractLeft, abstractRight, conclusion, view, rfl, rfl,
      CanonicalTerm.equalityOfSameType_semantics abstractLeft abstractRight sameType, rfl, rfl, rfl⟩
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms, needleFormed])
    (by
      intro parent member
      simp only [InferenceRequest.premises, List.mem_singleton] at member
      exact member ▸ premiseDerived)
    ⟨⟨conclusionFormed, premiseDerived.wellFormed.1.2⟩, premiseDerived.wellFormed.2⟩
  have notOccurs : FreeVariables.Hypotheses.occurs Representation.registeredOperatorAtom
      (Representation.variableAtom Representation.registeredOperatorAtom needle) (premise.hypotheses.map (·.term)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro occurs
    apply fresh
    exact (FreeVariables.Hypotheses.canonical_guard_iff world needle needleFormed premise.hypotheses
      (fun term member => premiseDerived.wellFormed.1.2 term (List.mem_toFinset.mpr member))).mp occurs
  have encodedHypotheses : ((premise.hypotheses.map (·.term)).map
      (Representation.termAtom Representation.registeredOperatorAtom constants [])) =
      premise.hypotheses.map (TheoremMetadata.hypothesisAtom constants) := by
    simp only [List.map_map]
    rfl
  have found : (entries constants cache).lookup input = some
      (Transitivity.theoremValue constants [] left.ty left.term right.term
        ((premise.hypotheses.map (·.term)).map (Representation.termAtom Representation.registeredOperatorAtom constants []))
        (premise.dependencies.map (Dependency.atom constants)) premise.origin) := by
    rw [lookup_entries, selected]
    simp only [Option.map_some, Record.atom, Transitivity.theoremValue, view.2, encodedHypotheses]
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .abs payload
    input (.symbol "None") (entries constants cache) receipts
  have inferred := Abstraction.Dispatcher.authored_infer_abs_return world table origins constants equalityIdentity
    needle needleFormed resolved left.term right.term left.ty annotations.1 annotations.2 left.checked
    (by simpa only [← view.1] using right.checked) (premise.hypotheses.map (·.term))
    (premise.dependencies.map (Dependency.atom constants)) premise.origin axioms (ReceiptKeys.table receipts) input
    (entries constants cache) found bound state "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "ABS")]) := by
    simpa only [notOccurs, Bool.false_eq_true, ↓reduceIte, Abstraction.Primitive.result,
      next, conclusion, CanonicalTerm.equalityOfSameType, abstractLeft, abstractRight, CanonicalTerm.abstractFree,
      encodedHypotheses, Publication.value, Representation.theoremAtom] using inferred
  refine ⟨next, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  exact publish_record constants cache next operators declarations axioms key (.symbol "ABS") .abs payload
    input (.symbol "None") receipts receiptFresh cacheFresh rfl bindings state stateKey keyName requestName
    stateCaptured keyCaptured requestCaptured inferredResult

/-- General source type instantiation retrieves its premise from the
authorized cache, validates the complete maplet inventory and publishes the
actual ordered hypothesis image with unchanged dependency occurrences. -/
theorem authored_inst_type_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (maplets : List (Ty × Ty))
    (resolved : ∀ entry ∈ maplets, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (formed : ∀ entry ∈ maplets, TypeFormed world.signature entry.1 ∧ TypeFormed world.signature entry.2)
    (cache : Cache) (valid : Valid policy world cache) (premise : Record) (input : Atom)
    (selected : cache.lookup input = some premise) (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "INST_TYPE",
      TypeSubstitution.maplets Representation.registeredOperatorAtom maplets, input]) :
    ∃ next : Record,
      next.conclusion = (SourceSubstitution.typeOnlySubstitution maplets).apply premise.conclusion ∧
      next.hypotheses = CacheInstantiation.hypotheses constants
        (SourceSubstitution.typeOnlySubstitution maplets) premise.hypotheses ∧
      next.dependencies = premise.dependencies ∧
      next.origin = .expression [.symbol "HOL:Origin", key, .expression [.symbol "INST_TYPE",
        TypeSubstitution.maplets Representation.registeredOperatorAtom maplets, input]] ∧
      InferenceRequest.Semantics (.instType maplets premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "INST_TYPE",
            TypeSubstitution.maplets Representation.registeredOperatorAtom maplets, input], [input]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have earned := stored_lookup_derived policy world cache valid input premise selected
  let substitution := SourceSubstitution.typeOnlySubstitution maplets
  let payload := TypeSubstitution.maplets Representation.registeredOperatorAtom maplets
  let origin : Atom := .expression [.symbol "HOL:Origin", key, .expression [.symbol "INST_TYPE", payload, input]]
  let next := CacheInstantiation.record constants substitution premise origin
  have preserves : ∀ term, AnnotationsFormed world.signature term.term →
      AnnotationsFormed world.signature (substitution.apply term).term :=
    CacheInstantiation.type_annotations world.signature maplets formed
  have nextFact : next.fact = substituteTheorem substitution premise.fact :=
    CacheInstantiation.record_fact world constants identified substitution premise origin
      (fun term member => preserves term (earned.wellFormed.1.2 term (List.mem_toFinset.mpr member)))
  have semantics : InferenceRequest.Semantics (.instType maplets premise.fact) next.fact := by
    rw [nextFact]
    exact substituteTheorem_semantics substitution premise.fact
  have requestFormed : InferenceFormation.Formed world.signature (.instType maplets premise.fact) := by
    constructor
    · intro type member
      obtain ⟨entry, present, inside⟩ := List.mem_flatMap.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact (formed entry present).1
      · exact (formed entry present).2
    · simp [InferenceFormation.terms]
  have derived : TheoryDerives policy world next.fact := .inference (request := .instType maplets premise.fact)
    semantics requestFormed (by
      intro source member
      have same : source = premise.fact := by simpa only [InferenceRequest.premises, List.mem_singleton] using member
      simpa only [same] using earned)
    (CacheInstantiation.record_formed world constants substitution premise origin earned.wellFormed preserves)
  have found : (entries constants cache).lookup input = some
      (Representation.theoremAtom constants [] premise.conclusion.term
        (premise.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (premise.dependencies.map (Dependency.atom constants)) premise.origin) := by
    rw [lookup_entries, selected]
    rfl
  let bound := ProofEvents.inferenceEnvironment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms key .instType payload input (.symbol "None")
    (entries constants cache) receipts
  have admitted := (TypeMapletValidation.admittedB_eq_true_iff world.signature maplets).mpr formed
  have inferred := TypeInstantiation.Dispatcher.authored_infer_inst_type_return world table origins constants
    maplets resolved premise.hypotheses premise.conclusion (premise.dependencies.map (Dependency.atom constants))
    premise.origin axioms (ReceiptKeys.table receipts) input (entries constants cache) found
    bound state "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "INST_TYPE")]) := by
    simpa only [admitted, ↓reduceIte, next, CacheInstantiation.record,
      CacheInstantiation.type_hypotheses_encoded, TypeInstantiation.Primitive.result,
      Representation.theoremAtom, TheoremMetadata.hypothesisAtom, List.map_nil,
      Publication.value, substitution] using inferred
  refine ⟨next, rfl, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  exact publish_record constants cache next (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms key (.symbol "INST_TYPE") .instType payload input
    (.symbol "None") receipts receiptFresh cacheFresh rfl bindings state stateKey keyName requestName
    stateCaptured keyCaptured requestCaptured inferredResult

/-- Term instantiation retains the source's simultaneous substitution,
capture avoidance and complete maplet validation. Its logical premise is
earned by the same cache lookup used by actual authored execution. -/
theorem authored_inst_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (maplets : List TermMapletReading.Entry)
    (admitted : TermMapletReading.admittedB maplets = true)
    (formed : ∀ entry ∈ maplets, TermMapletReading.EntryFormed world.signature entry)
    (cache : Cache) (valid : Valid policy world cache) (premise : Record) (input : Atom)
    (selected : cache.lookup input = some premise) (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom maplets, input]) :
    ∃ next : Record,
      next.conclusion = (TermMapletReading.substitution maplets admitted).apply premise.conclusion ∧
      next.hypotheses = CacheInstantiation.hypotheses constants
        (TermMapletReading.substitution maplets admitted) premise.hypotheses ∧
      next.dependencies = premise.dependencies ∧
      next.origin = .expression [.symbol "HOL:Origin", key,
        .expression [.symbol "INST", TermMapletReading.sourceAtom maplets, input]] ∧
      InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries maplets) premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "INST", TermMapletReading.sourceAtom maplets, input],
            [input]⟩ :: receipts)) (entries constants ((key, next) :: cache))]) := by
  have earned := stored_lookup_derived policy world cache valid input premise selected
  let substitution := TermMapletReading.substitution maplets admitted
  let payload := TermMapletReading.sourceAtom maplets
  let origin : Atom := .expression [.symbol "HOL:Origin", key, .expression [.symbol "INST", payload, input]]
  let next := CacheInstantiation.record constants substitution premise origin
  have preserves : ∀ term, AnnotationsFormed world.signature term.term →
      AnnotationsFormed world.signature (substitution.apply term).term :=
    CacheInstantiation.term_annotations world.signature maplets admitted formed
  have nextFact : next.fact = substituteTheorem substitution premise.fact :=
    CacheInstantiation.record_fact world constants identified substitution premise origin
      (fun term member => preserves term (earned.wellFormed.1.2 term (List.mem_toFinset.mpr member)))
  have semantics : InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries maplets) premise.fact) next.fact := by
    refine ⟨substitution, TermMapletReading.substitution_admitted maplets admitted, ?_⟩
    rw [nextFact]
    exact substituteTheorem_semantics substitution premise.fact
  have requestFormed : InferenceFormation.Formed world.signature
      (.inst (TermMapletReading.sourceEntries maplets) premise.fact) := by
    constructor
    · simp [InferenceFormation.types]
    · intro term member
      obtain ⟨entry, present, inside⟩ := List.mem_flatMap.mp member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact (formed original originalMember).replacementAnnotations
      · simpa [SourceTerm.toDB, boundIndex] using
          AnnotationsFormed.free (formed original originalMember).keyType
  have derived : TheoryDerives policy world next.fact := .inference
    (request := .inst (TermMapletReading.sourceEntries maplets) premise.fact) semantics requestFormed (by
      intro source member
      have same : source = premise.fact := by simpa only [InferenceRequest.premises, List.mem_singleton] using member
      simpa only [same] using earned)
    (CacheInstantiation.record_formed world constants substitution premise origin earned.wellFormed preserves)
  have found : (entries constants cache).lookup input = some
      (Representation.theoremAtom constants [] premise.conclusion.term
        (premise.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (premise.dependencies.map (Dependency.atom constants)) premise.origin) := by
    rw [lookup_entries, selected]
    rfl
  let bound := ProofEvents.inferenceEnvironment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms key .inst payload input (.symbol "None")
    (entries constants cache) receipts
  have inferred := TermInstantiationRule.Dispatcher.authored_infer_inst_return world table origins constants maplets
    admitted formed premise.hypotheses
    (fun item member => earned.wellFormed.1.2 item (List.mem_toFinset.mpr member))
    premise.conclusion earned.wellFormed.1.1 (premise.dependencies.map (Dependency.atom constants))
    premise.origin axioms (ReceiptKeys.table receipts) input (entries constants cache) found
    bound state "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value
        (Premises.keys (next.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Representation.termAtom Representation.registeredOperatorAtom constants [] next.conclusion.term)
        (Premises.keys (next.dependencies.map (Dependency.atom constants))) (.symbol "INST")]) := by
    simpa only [next, CacheInstantiation.record, CacheInstantiation.term_hypotheses_encoded,
      TermInstantiationRule.Primitive.result, Representation.theoremAtom,
      TheoremMetadata.hypothesisAtom, List.map_nil, Publication.value, substitution] using inferred
  refine ⟨next, rfl, rfl, rfl, rfl, semantics, derived, insert_valid valid key next derived, ?_⟩
  exact publish_record constants cache next (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms key (.symbol "INST") .inst payload input (.symbol "None")
    receipts receiptFresh cacheFresh rfl bindings state stateKey keyName requestName stateCaptured keyCaptured
    requestCaptured inferredResult

end Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory
