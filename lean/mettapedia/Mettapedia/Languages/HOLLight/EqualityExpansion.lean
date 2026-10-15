import Mettapedia.Languages.HOLLight.GraphExpansion

/-!
# Explicit equality-rule expansion for HOL Light

Symmetry is a five-node graph of original REFL, MK_COMB and EQ_MP requests.
It preserves the input theorem's full hypothesis and axiom sets and shares
one operand-reflexivity proof. Concrete blocks compose through the existing
chronological graph builder; no additional equality rule is admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.EqualityExpansion

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open ProofExecution (Origin Receipt)
open GraphExpansion

/-- Exact reflexivity output, with no axioms or hypotheses. -/
def reflexivity (term : CanonicalTerm) : Theorem :=
  Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType term term rfl)

theorem reflexivity_checked (term : CanonicalTerm) : checkRefl term = some (reflexivity term) := by
  apply (checkRefl_eq_some_iff _ _).mpr
  exact ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩

theorem equality_view (left right : CanonicalTerm) (sameType : left.ty = right.ty) :
    CanonicalTerm.EqualityViewSemantics (CanonicalTerm.equalityOfSameType left right sameType) left right :=
  ⟨sameType, rfl⟩

/-- Exact binary equality-elimination output, retaining both dependency sets. -/
def eqMpResult (equation premise : Theorem) (right : CanonicalTerm) : Theorem :=
  Theorem.unionResult equation premise (equation.sequent.hyp ∪ premise.sequent.hyp) right

theorem eqMpResult_checked (equation premise : Theorem) (left right : CanonicalTerm)
    (view : CanonicalTerm.EqualityViewSemantics equation.sequent.concl left right)
    (matching : left = premise.sequent.concl) :
    checkEqMp equation premise = some (eqMpResult equation premise right) :=
  (checkEqMp_eq_some_iff _ _ _).mpr ⟨left, right, view, matching, rfl, rfl, rfl⟩

/-- Exact MK_COMB output for its checked applications. -/
def appResult (functionEquality argumentEquality : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) : Theorem :=
  Theorem.unionResult functionEquality argumentEquality
    (functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp)
    (CanonicalTerm.equalityOfSameType left right sameType)

theorem appResult_checked (functionEquality argumentEquality : Theorem)
    (functionLeft functionRight argumentLeft argumentRight left right : CanonicalTerm)
    (sameType : left.ty = right.ty)
    (functionView : CanonicalTerm.EqualityViewSemantics functionEquality.sequent.concl functionLeft functionRight)
    (argumentView : CanonicalTerm.EqualityViewSemantics argumentEquality.sequent.concl argumentLeft argumentRight)
    (leftApplication : CanonicalTerm.ApplicationSemantics functionLeft argumentLeft left)
    (rightApplication : CanonicalTerm.ApplicationSemantics functionRight argumentRight right) :
    checkApp functionEquality argumentEquality = some (appResult functionEquality argumentEquality left right sameType) :=
  (checkApp_eq_some_iff _ _ _).mpr ⟨functionLeft, functionRight, argumentLeft, argumentRight,
    left, right, _, functionView, argumentView, leftApplication, rightApplication,
    CanonicalTerm.equalityOfSameType_semantics left right sameType, rfl, rfl, rfl⟩

/-- HOL Light's primitive TRANS retains all hypotheses and axiom dependencies. -/
def transResult (first second : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) : Theorem :=
  Theorem.unionResult first second (first.sequent.hyp ∪ second.sequent.hyp)
    (CanonicalTerm.equalityOfSameType left right sameType)

theorem transResult_checked (first second : Theorem) (left middle right : CanonicalTerm)
    (sameType : left.ty = right.ty)
    (firstView : CanonicalTerm.EqualityViewSemantics first.sequent.concl left middle)
    (secondView : CanonicalTerm.EqualityViewSemantics second.sequent.concl middle right) :
    checkTrans first second = some (transResult first second left right sameType) :=
  (checkTrans_eq_some_iff _ _ _).mpr ⟨left, middle, middle, right, _, firstView, secondView, rfl,
    CanonicalTerm.equalityOfSameType_semantics left right sameType, rfl, rfl, rfl⟩

def equalityConstant (operand : CanonicalTerm) : CanonicalTerm :=
  CanonicalTerm.constant Const.equality (Ty.equality operand.ty)

def partialLeft (left : CanonicalTerm) : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction (equalityConstant left) left (.function left.ty Ty.bool) (by simp [equalityConstant, CanonicalTerm.constant, Ty.equality])

def partialRight (left right : CanonicalTerm) (sameType : left.ty = right.ty) : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction (equalityConstant left) right (.function left.ty Ty.bool)
    (by simp [equalityConstant, CanonicalTerm.constant, Ty.equality, ← sameType])

def headCongruence (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType (partialLeft left) (partialRight left right sameType) rfl)

def fullCongruence (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType
      (CanonicalTerm.equalityOfSameType left left rfl)
      (CanonicalTerm.equalityOfSameType right left sameType.symm) rfl)

def symmetryResult (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType right left sameType.symm)

theorem headCongruence_checked (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right) :
    checkApp (reflexivity (equalityConstant left)) input =
      some (headCongruence input left right sameType) := by
  apply (checkApp_eq_some_iff _ _ _).mpr
  refine ⟨equalityConstant left, equalityConstant left, left, right,
    partialLeft left, partialRight left right sameType, _,
    equality_view _ _ rfl, view,
    CanonicalTerm.applicationOfFunction_semantics _ _ _ _,
    CanonicalTerm.applicationOfFunction_semantics _ _ _ _,
    CanonicalTerm.equalityOfSameType_semantics (partialLeft left) (partialRight left right sameType) rfl, ?_⟩
  simp [HasParts, headCongruence, reflexivity, Theorem.preserveAxiomsResult, Theorem.emptyResult]

theorem fullCongruence_checked (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    checkApp (headCongruence input left right sameType) (reflexivity left) =
      some (fullCongruence input left right sameType) := by
  apply (checkApp_eq_some_iff _ _ _).mpr
  refine ⟨partialLeft left, partialRight left right sameType, left, left,
    CanonicalTerm.equalityOfSameType left left rfl,
    CanonicalTerm.equalityOfSameType right left sameType.symm, _,
    equality_view (partialLeft left) (partialRight left right sameType) rfl, equality_view left left rfl, ?_, ?_,
    CanonicalTerm.equalityOfSameType_semantics (CanonicalTerm.equalityOfSameType left left rfl)
      (CanonicalTerm.equalityOfSameType right left sameType.symm) rfl, ?_⟩
  · exact ⟨left.ty, Ty.bool, by simp [partialLeft, CanonicalTerm.applicationOfFunction], rfl, rfl⟩
  · refine ⟨left.ty, Ty.bool, by simp [partialRight, CanonicalTerm.applicationOfFunction], rfl, ?_⟩
    simp [partialRight, CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType,
      equalityConstant, CanonicalTerm.constant, CanonicalTerm.equalityDB, sameType]
  · simp [HasParts, fullCongruence, headCongruence, reflexivity,
      Theorem.preserveAxiomsResult, Theorem.emptyResult]

theorem symmetryResult_checked (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    checkEqMp (fullCongruence input left right sameType) (reflexivity left) =
      some (symmetryResult input left right sameType) := by
  apply (checkEqMp_eq_some_iff _ _ _).mpr
  refine ⟨CanonicalTerm.equalityOfSameType left left rfl,
    CanonicalTerm.equalityOfSameType right left sameType.symm,
    equality_view (CanonicalTerm.equalityOfSameType left left rfl)
      (CanonicalTerm.equalityOfSameType right left sameType.symm) rfl, rfl, ?_⟩
  simp [HasParts, symmetryResult, fullCongruence, reflexivity,
    Theorem.preserveAxiomsResult, Theorem.emptyResult]

/-- Five actual HOL Light primitive requests reverse a checked equation.
The reflexivity of the left operand is stored once and used twice. -/
def symmetryBlock (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (origin : Origin) : ProofSystem.Certificate :=
  ([⟨reflexivity (equalityConstant left), .inference (.refl (equalityConstant left)), [], origin⟩,
    ⟨headCongruence input left right sameType,
      .inference (.mkComb (reflexivity (equalityConstant left)) input), [1, 0], origin⟩,
    ⟨reflexivity left, .inference (.refl left), [], origin⟩,
    ⟨fullCongruence input left right sameType,
      .inference (.mkComb (headCongruence input left right sameType) (reflexivity left)), [2, 3], origin⟩,
    ⟨symmetryResult input left right sameType,
      .inference (.eqMp (fullCongruence input left right sameType) (reflexivity left)), [4, 3], origin⟩], 5)

theorem symmetryBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right) (origin : Origin) :
    BlockChecked policy [input] (symmetryResult input left right sameType)
      (symmetryBlock input left right sameType origin) := by
  let nodes := (symmetryBlock input left right sameType origin).1
  have nodeCount : nodes.length = 5 := rfl
  let c0 := #[input]
  let c1 := c0.push (reflexivity (equalityConstant left))
  let c2 := c1.push (headCongruence input left right sameType)
  let c3 := c2.push (reflexivity left)
  let c4 := c3.push (fullCongruence input left right sameType)
  let c5 := c4.push (symmetryResult input left right sameType)
  have n0 : nodes[0].replay (ruleWitness policy) c0 = some c1 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, reflexivity_checked _, rfl⟩
  have n1 : nodes[1].replay (ruleWitness policy) c1 = some c2 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, headCongruence_checked input left right sameType view, rfl⟩
  have n2 : nodes[2].replay (ruleWitness policy) c2 = some c3 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, reflexivity_checked _, rfl⟩
  have n3 : nodes[3].replay (ruleWitness policy) c3 = some c4 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, fullCongruence_checked input left right sameType, rfl⟩
  have n4 : nodes[4].replay (ruleWitness policy) c4 = some c5 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, symmetryResult_checked input left right sameType, rfl⟩
  refine ⟨c5, ?_, ?_⟩
  · change replayFrom (ruleWitness policy) c0
      [nodes[0], nodes[1], nodes[2], nodes[3], nodes[4]] = some c5
    simp [replayFrom, n0, n1, n2, n3, n4]
  · rfl


/-- Symmetry emits five primitive occurrences and retains a single shared
left-operand reflexivity node. -/
theorem symmetryBlock_size (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) (origin : Origin) :
    (symmetryBlock input left right sameType origin).1.length = 5 := rfl

/-- The derived equality does not add axioms or change the premise's
hypotheses. -/
theorem symmetryResult_parts (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    HasParts (symmetryResult input left right sameType) input.axioms input.sequent.hyp
      (CanonicalTerm.equalityOfSameType right left sameType.symm) := ⟨rfl, rfl, rfl⟩

/-- The concrete symmetry block is consumed by the existing checked builder. -/
def emitSymmetry (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (inputRoot : Nat) (origin : Origin) (state : ProofExecution.State) :
    Option (ProofExecution.State × Nat) :=
  emitBlock policy [inputRoot] (symmetryBlock input left right sameType origin) state

theorem emitSymmetry_checked (policy : AxiomPolicy) [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State}
    (earlier : BuildChecked policy premises state)
    (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right)
    (inputRoot : Nat) (found : state.cache[inputRoot]? = some input) (origin : Origin) :
    ∃ result root,
      emitSymmetry policy input left right sameType inputRoot origin state = some (result, root) ∧
      BuildChecked policy premises result ∧
      result.cache[root]? = some (symmetryResult input left right sameType) ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  have selected : lookupPremises state.cache [inputRoot] = some [input] := by
    simp [lookupPremises, found]
  obtain ⟨result, root, emitted, checked, rootFound, _, preserved⟩ := emitBlock_checked earlier selected
    (symmetryBlock_checked policy input left right sameType view origin)
  exact ⟨result, root, emitted, checked, rootFound, preserved⟩

theorem emitSymmetry_future_refused (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (inputRoot : Nat) (origin : Origin) (state : ProofExecution.State)
    (future : state.cache.size ≤ inputRoot) :
    emitSymmetry policy input left right sameType inputRoot origin state = none :=
  emitBlock_future_refused policy [inputRoot] _ state (by simp) future

end Mettapedia.Languages.HOLLight.EqualityExpansion
