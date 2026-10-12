import Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution

/-!
# Deduction antisymmetry in the authored checker

The source operation discharges the opposite conclusion from each hypothesis
list before taking their ordered union. Its actual execution retains the
dependency union and the rule origin. Registered term identities justify the
interpretation of those exact lists as erased shared HOL hypothesis sets.

The dispatcher reads both premise occurrences through the existing cache
lookup. Rule preservation requires derivations of those cached premises;
the validity of a complete insertion history is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DeductionAntisymmetry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State)
open Representation (termAtom theoremAtom registeredOperatorAtom)

def hypotheses (left right : Atom) (first second : List Atom) : List Atom :=
  Transitivity.union (first.filter (fun entry => entry != right))
    (second.filter (fun entry => entry != left))

def result (constants : Const → Atom) (positions : List Ty) (type : Ty) (left right : DBTerm)
    (hyps1 hyps2 deps1 deps2 : List Atom) : Atom :=
  .expression [.symbol "Some", Transitivity.theoremValue constants positions type left right
    (hypotheses (termAtom registeredOperatorAtom constants positions left)
      (termAtom registeredOperatorAtom constants positions right) hyps1 hyps2)
    (Transitivity.union deps1 deps2) (.symbol "DEDUCT_ANTISYM_RULE")]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:deduct-antisym"))[0]'(by decide)
private def resultBody : Atom := .expression [.symbol "hol-light:theorem-eq",
  .expression [.symbol "hol-light:union",
    .expression [.symbol "hol-light:remove", .var "conclusion2", .var "hyps1"],
    .expression [.symbol "hol-light:remove", .var "conclusion1", .var "hyps2"]],
  .var "conclusion1", .var "conclusion2",
  .expression [.symbol "hol-light:union", .var "deps1", .var "deps2"], .symbol "DEDUCT_ANTISYM_RULE"]
private def cases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps1",
        .var "conclusion1", .var "deps1", .var "origin1"]],
      .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps2",
        .var "conclusion2", .var "deps2", .var "origin2"]]], resultBody),
   (.var "malformed", .symbol "None")]
private def environment (first second : Atom) : Subst := [("second", second), ("first", first)]
private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "first", .var "second"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (first second : Atom) :
    clauses program "hol-light:deduct-antisym" [first, second] = [.evaluate (environment first second) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:deduct-antisym") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "first", .var "second"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (type : Ty) (left right : DBTerm)
    (leftTyped : left.inferType positions = some type) (rightTyped : right.inferType positions = some type)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) :
    PureReturns program (environment (.expression [.symbol "Some", theoremAtom constants positions left hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremAtom constants positions right hyps2 deps2 origin2])) state equation.body state
      (result constants positions type left right hyps1 hyps2 deps1 deps2) := by
  let first := Atom.expression [.symbol "Some", theoremAtom constants positions left hyps1 deps1 origin1]
  let second := Atom.expression [.symbol "Some", theoremAtom constants positions right hyps2 deps2 origin2]
  let before := environment first second
  let bound := [("origin2", origin2), ("deps2", Premises.keys deps2),
    ("conclusion2", termAtom registeredOperatorAtom constants positions right), ("hyps2", Premises.keys hyps2),
    ("origin1", origin1), ("deps1", Premises.keys deps1),
    ("conclusion1", termAtom registeredOperatorAtom constants positions left), ("hyps1", Premises.keys hyps1)] ++ before
  rw [shape]
  apply case_returns program before bound state state state _ (.expression [first, second])
    resultBody _ _ cases (read_cases_encoded cases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [cases, bound, before, first, second, environment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold resultBody result hypotheses
    apply Equality.authored_theorem_equality_computed_return constants bound state positions left right type
      leftTyped rightTyped equalityIdentity _ _ (.symbol "DEDUCT_ANTISYM_RULE")
    · exact ListOperations.Union.authored_union_computed_return bound state
        (hyps1.filter (fun entry => entry != termAtom registeredOperatorAtom constants positions right))
        (hyps2.filter (fun entry => entry != termAtom registeredOperatorAtom constants positions left)) _ _
        (ListOperations.Removal.authored_remove_return bound state
          (termAtom registeredOperatorAtom constants positions right) hyps1 "conclusion2" "hyps1"
          (by simp [bound, applySubst, Subst.lookup]) (by simp [bound, applySubst, Subst.lookup]))
        (ListOperations.Removal.authored_remove_return bound state
          (termAtom registeredOperatorAtom constants positions left) hyps2 "conclusion1" "hyps2"
          (by simp [bound, applySubst, Subst.lookup]) (by simp [bound, applySubst, Subst.lookup]))
    · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "conclusion1"
    · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "conclusion2"
    · exact ListOperations.Union.authored_union_return bound state deps1 deps2 "deps1" "deps2"
        (by simp [bound, applySubst, Subst.lookup]) (by simp [bound, applySubst, Subst.lookup])
    · exact symbol_returns program bound state "DEDUCT_ANTISYM_RULE"

/-- Both premise expressions are evaluated before the actual rule body.
The output lists retain precisely the authored discharge and union order. -/
theorem authored_deduct_computed_return (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left right : DBTerm)
    (leftTyped : left.inferType positions = some type) (rightTyped : right.inferType positions = some type)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 firstExpression secondExpression : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state
      (.expression [.symbol "Some", theoremAtom constants positions left hyps1 deps1 origin1]))
    (secondReturned : PureReturns program bindings state secondExpression state
      (.expression [.symbol "Some", theoremAtom constants positions right hyps2 deps2 origin2])) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:deduct-antisym", firstExpression, secondExpression]) state
      (result constants positions type left right hyps1 hyps2 deps1 deps2) :=
  authored_binary_call_returns program bindings
    (environment (.expression [.symbol "Some", theoremAtom constants positions left hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremAtom constants positions right hyps2 deps2 origin2]))
    state state state state "hol-light:deduct-antisym" firstExpression secondExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) firstReturned secondReturned
    (clause _ _) (body_returns constants equalityIdentity state positions type left right leftTyped rightTyped
      hyps1 hyps2 deps1 deps2 origin1 origin2) (by decide)

private theorem missing_first_body_returns (state : State) (second : Atom) :
    PureReturns program (environment (.symbol "None") second) state equation.body state (.symbol "None") := by
  let before := environment (.symbol "None") second
  let bound := ("malformed", .expression [.symbol "None", second]) :: before
  rw [shape]
  apply case_returns program before bound state state state _ (.expression [.symbol "None", second])
    (.symbol "None") _ _ cases (read_cases_encoded cases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [cases, bound, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · exact symbol_returns program bound state "None"

/-- A missing first premise is refused independently of the second value.
Both argument occurrences still execute according to the source call rule. -/
theorem authored_deduct_first_missing_return (bindings : Subst) (state : State)
    (second firstExpression secondExpression : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state (.symbol "None"))
    (secondReturned : PureReturns program bindings state secondExpression state second) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:deduct-antisym", firstExpression, secondExpression]) state (.symbol "None") :=
  authored_binary_call_returns program bindings (environment (.symbol "None") second)
    state state state state "hol-light:deduct-antisym" firstExpression secondExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) firstReturned secondReturned
    (clause _ _) (missing_first_body_returns state second) (by decide)

namespace Dispatcher

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "hol-light:deduct-antisym",
  .expression [.symbol "hol-light:known", .var "state", .var "first"],
  .expression [.symbol "hol-light:known", .var "state", .var "second"]]
private def environment (source request : Atom) : Subst := [("request", request), ("state", source)]
private theorem shape : equation.body = .expression [.symbol "case", .var "request",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (source request : Atom) :
    clauses program "hol-light:infer" [source, request] = [.evaluate (environment source request) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:infer") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem selection (source first second : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]))
      (.expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]) cases =
      some ([("second", second), ("first", first)] ++
        environment source (.expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]), selected) := by
  have initial : cases =
      ((cases[0]'(by decide)) :: (cases[1]'(by decide)) :: (cases[2]'(by decide)) ::
       (cases[3]'(by decide)) :: (cases[4]'(by decide)) :: (cases[5]'(by decide)) ::
       (cases[6]'(by decide)) ::
       (.expression [.symbol "DEDUCT_ANTISYM_RULE", .var "first", .var "second"], selected) :: cases.drop 8) := by decide
  have first : (cases[0]'(by decide)).1 = .expression [.symbol "REFL", .var "term"] := by decide
  have secondRule : (cases[1]'(by decide)).1 = .expression [.symbol "TRANS", .var "first", .var "second"] := by decide
  have third : (cases[2]'(by decide)).1 = .expression [.symbol "MK_COMB", .var "first", .var "second"] := by decide
  have fourth : (cases[3]'(by decide)).1 = .expression [.symbol "ABS", .var "variable", .var "premise"] := by decide
  have fifth : (cases[4]'(by decide)).1 = .expression [.symbol "BETA", .var "term"] := by decide
  have sixth : (cases[5]'(by decide)).1 = .expression [.symbol "ASSUME", .var "term"] := by decide
  have seventh : (cases[6]'(by decide)).1 = .expression [.symbol "EQ_MP", .var "first", .var "second"] := by decide
  rw [initial]
  simp only [SpaceSemantics.selectCase, first, secondRule, third, fourth, fifth, sixth, seventh]
  simp [environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The dispatcher obtains both occurrences through its real first-match
cache operation; it does not accept caller-supplied theorem records. -/
theorem authored_infer_deduct_return (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left right : DBTerm)
    (leftTyped : left.inferType positions = some type) (rightTyped : right.inferType positions = some type)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts first second : Atom)
    (cache : List (Atom × Atom))
    (firstFound : cache.lookup first = some (theoremAtom constants positions left hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some (theoremAtom constants positions right hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (result constants positions type left right hyps1 hyps2 deps1 deps2) := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]
  let before := environment source request
  let bound := [("second", second), ("first", first)] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source first second
    · unfold selected
      apply authored_deduct_computed_return constants equalityIdentity bound state positions type left right
        leftTyped rightTyped hyps1 hyps2 deps1 deps2 origin1 origin2
      · simpa only [firstFound, Lookup.answer] using ProofLookup.authored_known_return bound state
          operators declarations axioms receipts first cache "state" "first"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])
      · simpa only [secondFound, Lookup.answer] using ProofLookup.authored_known_return bound state
          operators declarations axioms receipts second cache "state" "second"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])

/-- Missing proof authority is not repaired by the other cache entry. The
actual dispatcher returns refusal and preserves the source world. -/
theorem authored_infer_deduct_missing_refused (bindings : Subst) (state : State)
    (operators declarations axioms receipts first second : Atom) (cache : List (Atom × Atom))
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]
  let before := environment source request
  let bound := [("second", second), ("first", first)] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source first second
    · unfold selected
      apply authored_deduct_first_missing_return bound state (Lookup.answer (cache.lookup second))
      · exact ProofLookup.missing_proof_refused bound state operators declarations axioms receipts first cache "state" "first"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup]) missing
      · exact ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])

end Dispatcher

/-- The actual two discharge lists have exactly the shared rule's erased
hypothesis support. Registered identities are required only on these formed
terms; unknown vocabulary is not assigned a global identity interpretation. -/
theorem hypotheses_support (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (left right : CanonicalTerm) (hyps1 hyps2 : List CanonicalTerm)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left.term)
    (rightFormed : SignatureFormation.AnnotationsFormed world.signature right.term)
    (firstFormed : ∀ hypothesis ∈ hyps1, SignatureFormation.AnnotationsFormed world.signature hypothesis.term)
    (secondFormed : ∀ hypothesis ∈ hyps2, SignatureFormation.AnnotationsFormed world.signature hypothesis.term) :
    (hypotheses (TheoremMetadata.hypothesisAtom constants left) (TheoremMetadata.hypothesisAtom constants right)
      (hyps1.map (TheoremMetadata.hypothesisAtom constants))
      (hyps2.map (TheoremMetadata.hypothesisAtom constants))).toFinset =
      ((hyps1.toFinset.erase right) ∪ (hyps2.toFinset.erase left)).image (TheoremMetadata.hypothesisAtom constants) := by
  have unionSupport (first second : List Atom) : (Transitivity.union first second).toFinset =
      first.toFinset ∪ second.toFinset := by
    ext item
    simp only [List.mem_toFinset, Finset.mem_union, Transitivity.union_support]
  unfold hypotheses
  rw [unionSupport, TheoremMetadata.remove_encoded_support world constants identified right rightFormed hyps1 firstFormed,
    TheoremMetadata.remove_encoded_support world constants identified left leftFormed hyps2 secondFormed,
    Finset.image_union]

/-- Two admitted cached derivations yield the shared deduction rule through
actual authored dispatch. The Boolean carrier follows from their derivations;
source list order and provenance are retained alongside the logical support. -/
theorem authored_deduct_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (policy : AxiomPolicy) (left right : Theorem)
    (leftDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) left)
    (rightDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) right)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left.sequent.concl.term)
    (rightFormed : SignatureFormation.AnnotationsFormed world.signature right.sequent.concl.term)
    (hyps1 hyps2 : List CanonicalTerm) (deps1 deps2 : List Sequent)
    (firstHypSupport : hyps1.toFinset = left.sequent.hyp) (secondHypSupport : hyps2.toFinset = right.sequent.hyp)
    (firstDepSupport : deps1.toFinset = left.axioms) (secondDepSupport : deps2.toFinset = right.axioms)
    (firstFormed : ∀ hypothesis ∈ hyps1, SignatureFormation.AnnotationsFormed world.signature hypothesis.term)
    (secondFormed : ∀ hypothesis ∈ hyps2, SignatureFormation.AnnotationsFormed world.signature hypothesis.term)
    (axiomAtom : Sequent → Atom) (origin1 origin2 operators declarations axioms receipts first second : Atom)
    (cache : List (Atom × Atom))
    (firstFound : cache.lookup first = some (theoremAtom constants [] left.sequent.concl.term
      (hyps1.map (TheoremMetadata.hypothesisAtom constants)) (deps1.map axiomAtom) origin1))
    (secondFound : cache.lookup second = some (theoremAtom constants [] right.sequent.concl.term
      (hyps2.map (TheoremMetadata.hypothesisAtom constants)) (deps2.map axiomAtom) origin2))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]) :
    ∃ out : Theorem, InferenceRequest.Semantics (.deductAntisym left right) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.sequent.hyp = (left.sequent.hyp.erase right.sequent.concl) ∪ (right.sequent.hyp.erase left.sequent.concl) ∧
      out.axioms = left.axioms ∪ right.axioms ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", theoremAtom constants [] out.sequent.concl.term
          (hypotheses (TheoremMetadata.hypothesisAtom constants left.sequent.concl)
            (TheoremMetadata.hypothesisAtom constants right.sequent.concl)
            (hyps1.map (TheoremMetadata.hypothesisAtom constants)) (hyps2.map (TheoremMetadata.hypothesisAtom constants)))
          (Transitivity.union (deps1.map axiomAtom) (deps2.map axiomAtom)) (.symbol "DEDUCT_ANTISYM_RULE")]) ∧
      (hypotheses (TheoremMetadata.hypothesisAtom constants left.sequent.concl)
        (TheoremMetadata.hypothesisAtom constants right.sequent.concl)
        (hyps1.map (TheoremMetadata.hypothesisAtom constants)) (hyps2.map (TheoremMetadata.hypothesisAtom constants))).toFinset =
          out.sequent.hyp.image (TheoremMetadata.hypothesisAtom constants) ∧
      (Transitivity.union (deps1.map axiomAtom) (deps2.map axiomAtom)).toFinset = out.axioms.image axiomAtom := by
  have leftBoolean : left.sequent.concl.ty = Ty.bool := (derives_isBool leftDerives).1
  have rightBoolean : right.sequent.concl.ty = Ty.bool := (derives_isBool rightDerives).1
  let equality := CanonicalTerm.equalityOfSameType left.sequent.concl right.sequent.concl
    (leftBoolean.trans rightBoolean.symm)
  let out := Theorem.unionResult left right
    ((left.sequent.hyp.erase right.sequent.concl) ∪ (right.sequent.hyp.erase left.sequent.concl)) equality
  have semantics : InferenceRequest.Semantics (.deductAntisym left right) out :=
    ⟨equality, CanonicalTerm.equalityOfSameType_semantics _ _ _, rfl, rfl, rfl⟩
  have derives := InferenceRequest.Semantics.shared_derivation policy semantics (by
    intro premise member
    simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftDerives
    · exact rightDerives)
  have leftTyped : left.sequent.concl.term.inferType [] = some Ty.bool := by
    simpa only [leftBoolean] using left.sequent.concl.checked
  have rightTyped : right.sequent.concl.term.inferType [] = some Ty.bool := by
    simpa only [rightBoolean] using right.sequent.concl.checked
  have returned := Dispatcher.authored_infer_deduct_return constants equalityIdentity bindings state [] Ty.bool
    left.sequent.concl.term right.sequent.concl.term leftTyped rightTyped
    (hyps1.map (TheoremMetadata.hypothesisAtom constants)) (hyps2.map (TheoremMetadata.hypothesisAtom constants))
    (deps1.map axiomAtom) (deps2.map axiomAtom) origin1 origin2 operators declarations axioms receipts first second
    cache firstFound secondFound stateKey requestKey stateCaptured requestCaptured
  refine ⟨out, semantics, derives, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [result, Transitivity.theoremValue, out, Theorem.unionResult, equality,
      CanonicalTerm.equalityOfSameType, leftBoolean, TheoremMetadata.hypothesisAtom] using returned
  · simpa only [out, Theorem.unionResult, firstHypSupport, secondHypSupport] using
      hypotheses_support world constants identified left.sequent.concl right.sequent.concl hyps1 hyps2
        leftFormed rightFormed firstFormed secondFormed
  · simpa only [out, Theorem.unionResult, firstDepSupport, secondDepSupport] using
      TheoremMetadata.union_encoded_support axiomAtom deps1 deps2

namespace Controls

private def proposition : CanonicalTerm :=
  ⟨.free ⟨Name.global "p", Ty.bool⟩, Ty.bool, by simp [DBTerm.inferType]⟩
private def assumption : Theorem := Theorem.emptyResult {proposition} proposition
private def key : Atom := .symbol "assumption"
private def operators : Atom := OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators
  (fun _ => .symbol "HOL:Primitive")
private def declarations : Atom := DeclarationTable.tableAtom DeclarationTable.sourcePrimitive DeclarationTable.primitiveIdentity
private def cache : List (Atom × Atom) :=
  [(key, theoremAtom DeclarationTable.primitiveIdentity [] proposition.term
    ([proposition, proposition].map (TheoremMetadata.hypothesisAtom DeclarationTable.primitiveIdentity)) [] (.symbol "ASSUME"))]
private def captured : Subst :=
  [("request", .expression [.symbol "DEDUCT_ANTISYM_RULE", key, key]),
   ("state", ProofLookup.sourceState operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") cache)]
private theorem boolean_formed : SignatureFormation.TypeFormed SourceProfile.primitiveContext.signature Ty.bool :=
  DefinitionAdapters.ContextControls.boolean_formed.mono
    (DefinitionAdapters.ContextControls.core_includes.trans
      (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

/-- Both premise positions legitimately reuse the same admitted assumption.
Discharge removes all repeated p occurrences from each source list and yields
a derivation of p=p with no remaining hypotheses or axiom dependencies. -/
theorem repeated_premise_discharge_checked (state : State) :
    ∃ out : Theorem, Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out ∧
      out.sequent.hyp = ∅ ∧ out.axioms = ∅ ∧
      PureReturns program captured state (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
        (.expression [.symbol "Some", theoremAtom DeclarationTable.primitiveIdentity [] out.sequent.concl.term
          [] [] (.symbol "DEDUCT_ANTISYM_RULE")]) := by
  have assumptionSemantics : AssumeSemantics proposition assumption := ⟨rfl, rfl, rfl, rfl⟩
  have assumptionDerives := derives_of_nullary_check emptyAxiomPolicy (.core (.assume proposition)) assumption rfl True.intro
    ((checkAssume_eq_some_iff _ _).mpr assumptionSemantics)
  have formed : SignatureFormation.AnnotationsFormed SourceProfile.primitiveContext.signature proposition.term :=
    .free boolean_formed
  have hypFormed : ∀ hypothesis ∈ [proposition, proposition],
      SignatureFormation.AnnotationsFormed SourceProfile.primitiveContext.signature hypothesis.term := by
    intro hypothesis member
    have same : hypothesis = proposition := by simpa using member
    cases same
    exact formed
  obtain ⟨out, -, derives, hypSupport, depSupport, returned, -, -⟩ := authored_deduct_shared_derivation
    SourceProfile.primitiveContext DeclarationTable.primitiveIdentity (DeclarationTable.primitiveIdentity_identifies _) rfl
    emptyAxiomPolicy assumption assumption assumptionDerives assumptionDerives formed formed
    [proposition, proposition] [proposition, proposition] [] [] (by simp [assumption, Theorem.emptyResult])
    (by simp [assumption, Theorem.emptyResult]) rfl rfl hypFormed hypFormed (fun _ => .symbol "unused-axiom")
    (.symbol "ASSUME") (.symbol "ASSUME") operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") key key cache
    (by simp [cache, assumption, Theorem.emptyResult]) (by simp [cache, assumption, Theorem.emptyResult])
    captured state "state" "request" (by simp [captured, applySubst, Subst.lookup])
    (by simp [captured, applySubst, Subst.lookup])
  refine ⟨out, derives, ?_, ?_, ?_⟩
  · simpa only [assumption, Theorem.emptyResult, Finset.erase_singleton, Finset.empty_union] using hypSupport
  · simpa only [assumption, Theorem.emptyResult, Finset.empty_union] using depSupport
  · simpa [hypotheses, assumption, Theorem.emptyResult, Transitivity.union] using returned

end Controls

end Mettapedia.Languages.HOLLight.MeTTa.DeductionAntisymmetry
