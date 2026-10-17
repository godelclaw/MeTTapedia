import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.HOLLight.ProofDataEncoding
import Mettapedia.Languages.HOLLight.TemplateInstantiationMachine

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
open GraphExpansion PrimitiveTransport

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

/-- An explicit two-beta expansion uses two genuine source BETA/INST pairs,
argument reflexivity, MK_COMB and HOL Light's primitive TRANS. -/
structure DoubleBetaExpansion where
  first : BetaExpansion
  second : BetaExpansion
  argument : CanonicalTerm
  application : Theorem
  conclusion : Theorem
  applicationChecked : checkApp first.conclusion (reflexivity argument) = some application
  transChecked : checkTrans application second.conclusion = some conclusion

def doubleBetaExpansion (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second) :
    DoubleBetaExpansion := by
  have innerChecked : (DBTerm.abs second body).inferType [first] = some (.function second codomain) := by
    simp [DBTerm.inferType, bodyChecked]
  let firstExpansion := betaExpansion first (.abs second body) (.function second codomain) innerChecked left leftType
  let functionBefore := betaRedex first (.abs second body) (.function second codomain) innerChecked left leftType
  let functionAfter := betaReduced first (.abs second body) (.function second codomain) innerChecked left leftType
  let nextBody := DBTerm.instantiateAt left.term 1 body
  have nextChecked : nextBody.inferType [second] = some codomain := by
    have checked : (DBTerm.abs second nextBody).inferType [] = some (.function second codomain) := by
      simpa [functionAfter, betaReduced, nextBody, DBTerm.instantiateAt] using functionAfter.checked
    obtain ⟨actualCodomain, result, typeEqual⟩ := DBTerm.inferType_abs_eq_some_iff.mp checked
    have codomainEqual : actualCodomain = codomain := (Ty.function_inj typeEqual).2.symm
    simpa [codomainEqual] using result
  let secondExpansion := betaExpansion second nextBody codomain nextChecked right rightType
  let whole := CanonicalTerm.applicationOfFunction functionBefore right codomain (by simp [functionBefore, betaRedex, rightType])
  let middle := CanonicalTerm.applicationOfFunction functionAfter right codomain (by simp [functionAfter, betaReduced, rightType])
  let reduced := betaReduced second nextBody codomain nextChecked right rightType
  let lifted := appResult firstExpansion.conclusion (reflexivity right) whole middle rfl
  let result := transResult lifted secondExpansion.conclusion whole reduced rfl
  have firstView : CanonicalTerm.EqualityViewSemantics firstExpansion.conclusion.sequent.concl functionBefore functionAfter := by
    rw [show firstExpansion.conclusion = _ from betaExpansion_conclusion first (.abs second body) (.function second codomain) innerChecked left leftType]
    exact equality_view functionBefore functionAfter rfl
  have secondView : CanonicalTerm.EqualityViewSemantics secondExpansion.conclusion.sequent.concl middle reduced := by
    rw [show secondExpansion.conclusion = _ from betaExpansion_conclusion second nextBody codomain nextChecked right rightType]
    refine ⟨rfl, ?_⟩
    simp [middle, reduced, functionAfter, betaRedex, betaReduced, nextBody, Theorem.emptyResult, CanonicalTerm.applicationOfFunction,
      CanonicalTerm.equalityOfSameType, DBTerm.instantiateAt]
  refine ⟨firstExpansion, secondExpansion, right, lifted, result, ?_, ?_⟩
  · exact appResult_checked _ _ functionBefore functionAfter right right whole middle rfl firstView
      (equality_view right right rfl)
      (CanonicalTerm.applicationOfFunction_semantics _ _ _ _)
      (CanonicalTerm.applicationOfFunction_semantics _ _ _ _)
  · exact transResult_checked _ _ whole middle reduced rfl (equality_view whole middle rfl) secondView

theorem doubleBetaExpansion_parts (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second) :
    let expansion := doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType
    expansion.conclusion.axioms = ∅ ∧ expansion.conclusion.sequent.hyp = ∅ ∧
      expansion.conclusion.sequent.concl.term =
        CanonicalTerm.equalityDB codomain (.app (.app (.abs first (.abs second body)) left.term) right.term)
          (DBTerm.instantiateAt right.term 0 (DBTerm.instantiateAt left.term 1 body)) := by
  simp [doubleBetaExpansion, transResult, appResult, reflexivity,
    betaExpansion_conclusion, Theorem.unionResult, Theorem.emptyResult,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType,
    betaRedex, betaReduced, DBTerm.instantiateAt]

def doubleBetaBlock (expansion : DoubleBetaExpansion) (origin : Origin) : ProofSystem.Certificate :=
  ([⟨expansion.first.intermediate, .inference (.beta expansion.first.source), [], origin⟩,
    ⟨expansion.first.conclusion, .inference (.inst expansion.first.entries expansion.first.intermediate), [0], origin⟩,
    ⟨reflexivity expansion.argument, .inference (.refl expansion.argument), [], origin⟩,
    ⟨expansion.application, .inference (.mkComb expansion.first.conclusion (reflexivity expansion.argument)), [1, 2], origin⟩,
    ⟨expansion.second.intermediate, .inference (.beta expansion.second.source), [], origin⟩,
    ⟨expansion.second.conclusion, .inference (.inst expansion.second.entries expansion.second.intermediate), [4], origin⟩,
    ⟨expansion.conclusion, .inference (.trans expansion.application expansion.second.conclusion), [3, 5], origin⟩], 6)

theorem doubleBetaBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (expansion : DoubleBetaExpansion) (origin : Origin) :
    BlockChecked policy [] expansion.conclusion (doubleBetaBlock expansion origin) := by
  let nodes := (doubleBetaBlock expansion origin).1
  have length : nodes.length = 7 := rfl
  let c0 : Array Theorem := #[]
  let c1 := c0.push expansion.first.intermediate
  let c2 := c1.push expansion.first.conclusion
  let c3 := c2.push (reflexivity expansion.argument)
  let c4 := c3.push expansion.application
  let c5 := c4.push expansion.second.intermediate
  let c6 := c5.push expansion.second.conclusion
  let c7 := c6.push expansion.conclusion
  have n0 : nodes[0].replay (ruleWitness policy) c0 = some c1 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.first.betaChecked, rfl⟩
  have n1 : nodes[1].replay (ruleWitness policy) c1 = some c2 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.first.instChecked, rfl⟩
  have n2 : nodes[2].replay (ruleWitness policy) c2 = some c3 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, reflexivity_checked _, rfl⟩
  have n3 : nodes[3].replay (ruleWitness policy) c3 = some c4 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.applicationChecked, rfl⟩
  have n4 : nodes[4].replay (ruleWitness policy) c4 = some c5 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.second.betaChecked, rfl⟩
  have n5 : nodes[5].replay (ruleWitness policy) c5 = some c6 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.second.instChecked, rfl⟩
  have n6 : nodes[6].replay (ruleWitness policy) c6 = some c7 := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.transChecked, rfl⟩
  refine ⟨c7, ?_, rfl⟩
  change replayFrom (ruleWitness policy) c0
    [nodes[0], nodes[1], nodes[2], nodes[3], nodes[4], nodes[5], nodes[6]] = some c7
  simp [replayFrom, n0, n1, n2, n3, n4, n5, n6]


namespace Emission

set_option backward.isDefEq.respectTransparency false

open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open ProofDataEncoding
open Mettapedia.Logic.DerivationGraph
open _root_.Computability Turing Polynomial

def unaryRequest {arity : Nat} (tag : Nat) (operand : Indexed.Template Alphabet arity) :
    Indexed.Template Alphabet arity :=
  Templates.pair (Templates.literal (.atom 0))
    (Templates.pair (Templates.literal (.atom tag)) operand)

def binaryRequest {arity : Nat} (tag : Nat)
    (first second : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  unaryRequest tag (Templates.pair first second)

/-- Receipt packing retains the existing ordered parent list and physical
origin field; the surrounding bytes are the original product markers. -/
def receiptTemplate {arity : Nat} (conclusion witness origin : Indexed.Template Alphabet arity)
    (parents : List Nat) : Indexed.Template Alphabet arity :=
  Templates.pair conclusion (Templates.pair witness
    (Templates.pair (Templates.literal ((Codec.list Codec.nat).put parents)) origin))

def listTemplate {arity : Nat} : List (Indexed.Template Alphabet arity) →
    Indexed.Template Alphabet arity
  | [] => Templates.literal (.atom 0)
  | first :: rest => Templates.pair first (listTemplate rest)

/-- Lower an occurrence's three payload fields without changing its ordered
parent references. The existing graph node is also the template carrier. -/
def nodeTemplate {arity : Nat}
    (node : Mettapedia.Logic.DerivationGraph.Node
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity)) : Indexed.Template Alphabet arity :=
  receiptTemplate node.conclusion node.witness node.origin node.parents

/-- The assembled graph is packed with the original certificate product and
list markers, after the existing assembler has relocated its addresses. -/
def certificateTemplate {arity : Nat}
    (block : List (Mettapedia.Logic.DerivationGraph.Node
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity)) × Nat) : Indexed.Template Alphabet arity :=
  Templates.pair (listTemplate (block.1.map nodeTemplate)) (Templates.literal (.atom block.2))

theorem nodeTemplate_exact {arity : Nat} (fields : Fin arity → List Alphabet)
    (node : Mettapedia.Logic.DerivationGraph.Node
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity)) (receipt : Receipt)
    (conclusion : Indexed.instantiate node.conclusion fields = encodeWith theoremCodec receipt.conclusion)
    (witness : Indexed.instantiate node.witness fields = encodeWith requestCodec receipt.witness)
    (origin : Indexed.instantiate node.origin fields = encodeWith originCodec receipt.origin)
    (parents : node.parents = receipt.parents) :
    Indexed.instantiate (nodeTemplate node) fields = encodeWith receiptCodec receipt := by
  simp only [nodeTemplate, receiptTemplate, Templates.pair_exact, Templates.literal_exact,
    conclusion, witness, origin, parents]
  simp [encodeWith, receiptCodec, Codec.prod, Codec.mapped, encodeData_pair]

theorem listTemplate_exact {arity : Nat} {nodes : List (Indexed.Template Alphabet arity)}
    {receipts : List Receipt} (fields : Fin arity → List Alphabet)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node fields = encodeWith receiptCodec receipt) nodes receipts) :
    Indexed.instantiate (listTemplate nodes) fields = encodeWith (Codec.list receiptCodec) receipts := by
  induction aligned with
  | nil => rfl
  | @cons node receipt nodes receipts first rest ih =>
      simp only [listTemplate, Templates.pair_exact, first, ih]
      simp [encodeWith, Codec.list, Codec.putList, encodeData_pair]

theorem certificateTemplate_exact {arity : Nat}
    (nodes : List (Mettapedia.Logic.DerivationGraph.Node
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity))) (receipts : List Receipt) (root : Nat)
    (fields : Fin arity → List Alphabet)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate (nodeTemplate node) fields = encodeWith receiptCodec receipt) nodes receipts) :
    Indexed.instantiate (certificateTemplate (nodes, root)) fields =
      encodeCertificate (receipts, root) := by
  have mapped : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node fields = encodeWith receiptCodec receipt)
      (nodes.map nodeTemplate) receipts := by
    induction aligned with
    | nil => exact .nil
    | cons first rest ih => exact .cons first ih
  have packed := listTemplate_exact fields mapped
  simp only [certificateTemplate, Templates.pair_exact, packed, Templates.literal_exact]
  simp [encodeCertificate, certificateCodec, encodeWith, Codec.prod, Codec.nat, encodeData_pair]

/-- Component-wise lowering of the existing node vector suffices for exact
whole-certificate storage. This retains all authored occurrences. -/
theorem certificateTemplate_of_nodes {arity : Nat}
    (nodes : List (Node (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)))
    (receipts : List Receipt) (root : Nat) (fields : Fin arity → List Alphabet)
    (aligned : nodes.map (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)) =
      receipts.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec))) :
    Indexed.instantiate (certificateTemplate (nodes, root)) fields = encodeCertificate (receipts, root) := by
  apply certificateTemplate_exact
  induction nodes generalizing receipts with
  | nil =>
      cases receipts with
      | nil => exact .nil
      | cons receipt rest => simp at aligned
  | cons node rest ih =>
      cases receipts with
      | nil => simp at aligned
      | cons receipt remaining =>
          simp only [List.map_cons] at aligned
          obtain ⟨head, tail⟩ := List.cons.inj aligned
          apply List.Forall₂.cons
          · apply nodeTemplate_exact fields node receipt
            · exact congrArg (fun node => node.conclusion) head
            · exact congrArg (fun node => node.witness) head
            · exact congrArg (fun node => node.origin) head
            · exact congrArg (fun node => node.parents) head
          · exact ih remaining tail

/-- Compose complete field plans using the existing node payload map. This
does not move, merge or remove any physical occurrence. -/
def substituteNodes {sourceArity targetArity : Nat}
    (slots : Fin sourceArity → Indexed.Template Alphabet targetArity)
    (nodes : List (Node (Indexed.Template Alphabet sourceArity)
      (Indexed.Template Alphabet sourceArity) (Indexed.Template Alphabet sourceArity))) :
    List (Node (Indexed.Template Alphabet targetArity)
      (Indexed.Template Alphabet targetArity) (Indexed.Template Alphabet targetArity)) :=
  nodes.map (Node.map (fun template => Templates.substitute template slots)
    (fun template => Templates.substitute template slots) (fun template => Templates.substitute template slots))

theorem substituteNodes_exact {sourceArity targetArity : Nat}
    (slots : Fin sourceArity → Indexed.Template Alphabet targetArity)
    (nodes : List (Node (Indexed.Template Alphabet sourceArity)
      (Indexed.Template Alphabet sourceArity) (Indexed.Template Alphabet sourceArity)))
    (fields : Fin targetArity → List Alphabet) :
    (substituteNodes slots nodes).map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)) =
      nodes.map (Node.map
        (fun template => Indexed.instantiate template (fun slot => Indexed.instantiate (slots slot) fields))
        (fun template => Indexed.instantiate template (fun slot => Indexed.instantiate (slots slot) fields))
        (fun template => Indexed.instantiate template (fun slot => Indexed.instantiate (slots slot) fields))) := by
  simp [substituteNodes, List.map_map, Node.map, Templates.substitute_exact]

/-- The original five-node symmetry expansion is a fixed indexed word plan.
Only the authored dependency sets and operand type are static. The complete
input theorem, both operand terms and origin remain independently supplied
physical fields, and repeated uses make repeated copies. -/
def symmetryNodes (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) : List (Node (Indexed.Template Alphabet 4)
      (Indexed.Template Alphabet 4) (Indexed.Template Alphabet 4)) :=
  let input : Indexed.Template Alphabet 4 := [.inr 0]
  let left : Indexed.Template Alphabet 4 := [.inr 1]
  let right : Indexed.Template Alphabet 4 := [.inr 2]
  let origin : Indexed.Template Alphabet 4 := [.inr 3]
  let operator := Templates.literal (putTerm (.const Const.equality (Ty.equality operandType)))
  let operatorCanonical := Templates.canonical (Ty.equality operandType) operator
  let operatorProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality (Ty.equality operandType) operator operator))
  let head := Templates.theoremTemplate axioms hypotheses
    (Templates.canonical Ty.bool (Templates.equality (.function operandType Ty.bool)
      (Templates.application operator left) (Templates.application operator right)))
  let leftCanonical := Templates.canonical operandType left
  let leftProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality operandType left left))
  let full := Templates.theoremTemplate axioms hypotheses
    (Templates.canonical Ty.bool (Templates.equality Ty.bool
      (Templates.equality operandType left left) (Templates.equality operandType right left)))
  let reversed := Templates.theoremTemplate axioms hypotheses
    (Templates.canonical Ty.bool (Templates.equality operandType right left))
  [⟨operatorProof, unaryRequest 0 operatorCanonical, [], origin⟩,
   ⟨head, binaryRequest 2 operatorProof input, [1, 0], origin⟩,
   ⟨leftProof, unaryRequest 0 leftCanonical, [], origin⟩,
   ⟨full, binaryRequest 2 head leftProof, [2, 3], origin⟩,
   ⟨reversed, binaryRequest 6 full leftProof, [4, 3], origin⟩]

/-- The same local node plan serves standalone emission and chronological
assembly with other blocks. -/
def symmetryTemplate (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) : Indexed.Template Alphabet 4 :=
  certificateTemplate (symmetryNodes axioms hypotheses operandType, 5)

/-- Field framing separates complete byte words by a marker outside the
original five-symbol alphabet. It performs no decoding or logical checking. -/
def symmetryFields (input : Theorem) (left right : CanonicalTerm) (origin : Origin) :
    Fin 4 → List Alphabet :=
  ![encodeWith theoremCodec input, encodeWith dbTermCodec left.term,
    encodeWith dbTermCodec right.term, encodeWith originCodec origin]

def symmetryInput (input : Theorem) (left right : CanonicalTerm) (origin : Origin) :
    List (Option Alphabet) := Indexed.argumentWire (symmetryFields input left right origin)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem symmetryNodes_exact (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) (input : Theorem) (left right : CanonicalTerm)
    (inputAxioms : input.axioms = axioms) (inputHypotheses : input.sequent.hyp = hypotheses)
    (leftType : left.ty = operandType) (rightType : right.ty = operandType)
    (origin : Origin) :
    (symmetryNodes axioms hypotheses operandType).map
      (Node.map (fun template => Indexed.instantiate template (symmetryFields input left right origin))
        (fun template => Indexed.instantiate template (symmetryFields input left right origin))
        (fun template => Indexed.instantiate template (symmetryFields input left right origin))) =
      (symmetryBlock input left right (leftType.trans rightType.symm) origin).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  simp [symmetryNodes, Node.map, unaryRequest, binaryRequest,
    Templates.theoremTemplate, Templates.canonical, Templates.equality, Templates.application,
    symmetryFields,
    symmetryBlock, reflexivity, equalityConstant, headCongruence, partialLeft, partialRight,
    fullCongruence, symmetryResult, Theorem.emptyResult, Theorem.preserveAxiomsResult,
    CanonicalTerm.constant, CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType,
    inputAxioms, inputHypotheses, leftType, rightType, requestCodec, putRequest, putInference, canonicalCodec, theoremCodec, sequentCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped,
    encodeWith, encodeData_pair, putTerm, CanonicalTerm.equalityDB, List.append_assoc]


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem symmetry_exact (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) (input : Theorem) (left right : CanonicalTerm)
    (inputAxioms : input.axioms = axioms) (inputHypotheses : input.sequent.hyp = hypotheses)
    (leftType : left.ty = operandType) (rightType : right.ty = operandType)
    (origin : Origin) :
    Indexed.instantiate (symmetryTemplate axioms hypotheses operandType)
      (symmetryFields input left right origin) =
      encodeCertificate (symmetryBlock input left right (leftType.trans rightType.symm) origin) := by
  exact certificateTemplate_of_nodes
    (symmetryNodes axioms hypotheses operandType)
    (symmetryBlock input left right (leftType.trans rightType.symm) origin).1 5
    (symmetryFields input left right origin)
    (symmetryNodes_exact axioms hypotheses operandType input left right inputAxioms
      inputHypotheses leftType rightType origin)

/-- This clock is attached to the actual indexed copier and charges every
supplied input theorem byte, operand occurrence and origin byte. -/
def symmetryOutputs (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) (input : Theorem) (left right : CanonicalTerm)
    (inputAxioms : input.axioms = axioms) (inputHypotheses : input.sequent.hyp = hypotheses)
    (leftType : left.ty = operandType) (rightType : right.ty = operandType)
    (origin : Origin) :
    TM2OutputsInTime (Indexed.machine (symmetryTemplate axioms hypotheses operandType))
      (symmetryInput input left right origin)
      (some (encodeCertificate (symmetryBlock input left right (leftType.trans rightType.symm) origin)))
      (4 * ((symmetryTemplate axioms hypotheses operandType).length + 1) *
        ((symmetryInput input left right origin).length + 1)) := by
  have ran := Indexed.outputs (symmetryTemplate axioms hypotheses operandType)
    (symmetryFields input left right origin)
  have same := symmetry_exact axioms hypotheses operandType input left right inputAxioms
    inputHypotheses leftType rightType origin
  exact same ▸ ran

/-- Bytes emitted by the phase decode to the same original proof graph. Its
logical authorization remains with the ordinary HOL Light block checker. -/
theorem symmetry_decodes (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (operandType : Ty) (input : Theorem) (left right : CanonicalTerm)
    (inputAxioms : input.axioms = axioms) (inputHypotheses : input.sequent.hyp = hypotheses)
    (leftType : left.ty = operandType) (rightType : right.ty = operandType)
    (origin : Origin) :
    decodeCertificate (Indexed.instantiate (symmetryTemplate axioms hypotheses operandType)
      (symmetryFields input left right origin)) =
      some (symmetryBlock input left right (leftType.trans rightType.symm) origin) := by
  rw [symmetry_exact axioms hypotheses operandType input left right inputAxioms inputHypotheses
    leftType rightType origin, decodeCertificate_encodeCertificate]

/-- The fixed BETA witness is computed by the original named-source
algorithm. Its full source and intermediate theorem bytes become literal
control data; only the supplied argument and origin are variable fields. -/
def betaSeed (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) : BetaExpansion :=
  betaExpansion domain body codomain checkedBody (CanonicalTerm.free (betaNeedle domain body)) rfl

/-- The original BETA/INST block stores both full operand representations.
The raw term field realizes substitution through the existing scoped template
compiler; the named field is the original checkedSource output. -/
def betaTemplate (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) : Indexed.Template Alphabet 3 :=
  let seed := betaSeed domain body codomain checkedBody
  let operand : Indexed.Template Alphabet 3 := [.inr 0]
  let named : Indexed.Template Alphabet 3 := [.inr 1]
  let origin : Indexed.Template Alphabet 3 := [.inr 2]
  let redex := Templates.application (Templates.literal (putTerm (.abs domain body))) operand
  let reduced := Templates.single 0 (TemplateInstantiationMachine.compile 0 body)
  let conclusion := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain redex reduced))
  let argumentSource := Templates.pair named (Templates.literal (putTy domain))
  let entries := Templates.pair
    (Templates.pair argumentSource
      (Templates.literal (putSourceTerm (.var (betaNeedle domain body).name domain))))
    (Templates.literal (.atom 0))
  let inst := unaryRequest 9
    (Templates.pair entries (Templates.literal (theoremCodec.put seed.intermediate)))
  Templates.pair (listTemplate
    [receiptTemplate (Templates.literal (theoremCodec.put seed.intermediate))
      (Templates.literal (requestCodec.put (.inference (.beta seed.source)))) origin [],
     receiptTemplate conclusion inst origin [0]])
    (Templates.literal (.atom 1))

/-- Dynamic source data remains on a physical field stack. This stage does
not claim that it computes the original named representative by itself. -/
def betaFields (argument : CanonicalTerm) (origin : Origin) : Fin 3 → List Alphabet :=
  ![encodeWith dbTermCodec argument.term,
    encodeWith sourceTermCodec (checkedSource argument).source, encodeWith originCodec origin]

def betaInput (argument : CanonicalTerm) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (betaFields argument origin)

set_option maxRecDepth 4096 in
theorem beta_exact (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) (origin : Origin) :
    Indexed.instantiate (betaTemplate domain body codomain checkedBody) (betaFields argument origin) =
      encodeCertificate (betaBlock (betaExpansion domain body codomain checkedBody argument argumentType) origin) := by
  have sourceType : (checkedSource argument).ty = domain :=
    (congrArg CanonicalTerm.ty (checkedSource_exact argument)).trans argumentType
  have sourceSame : (betaExpansion domain body codomain checkedBody argument argumentType).source =
      (betaSeed domain body codomain checkedBody).source := rfl
  have intermediateSame : (betaExpansion domain body codomain checkedBody argument argumentType).intermediate =
      (betaSeed domain body codomain checkedBody).intermediate := rfl
  have entriesSame : (betaExpansion domain body codomain checkedBody argument argumentType).entries =
      [(checkedSource argument, .var (betaNeedle domain body).name domain)] := rfl
  have reduced := TemplateInstantiationMachine.compile_exact 0 body argument.term
  have reducedSlot : Indexed.instantiate
      (Templates.single 0 (TemplateInstantiationMachine.compile 0 body)) (betaFields argument origin) =
      encodeWith dbTermCodec (DBTerm.instantiateAt argument.term 0 body) := by
    rw [Templates.single_exact]
    exact reduced
  simp only [betaTemplate, betaBlock, sourceSame, intermediateSame, entriesSame,
    betaExpansion_conclusion, receiptTemplate, unaryRequest, listTemplate,
    Templates.theoremTemplate, Templates.canonical, Templates.equality, Templates.application,
    Templates.pair_exact, Templates.literal_exact, Indexed.instantiate_hole, Indexed.instantiate_nil,
    reducedSlot]
  simp [betaFields, encodeCertificate, certificateCodec, receiptCodec, requestCodec, putRequest, putInference,
    canonicalCodec, theoremCodec, sequentCodec, termMapletCodec, checkedSourceCodec, sourceTermCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped, Codec.list, Codec.putList, Codec.nat,
    encodeWith, encodeData_pair, Theorem.emptyResult,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, betaRedex, betaReduced,
    putTerm, sourceType, List.append_assoc]

/-- Actual BETA/INST byte construction has a linear transition account for
each fixed authored body and its original complete operand fields. -/
def betaOutputs (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) (origin : Origin) :
    TM2OutputsInTime (Indexed.machine (betaTemplate domain body codomain checkedBody))
      (betaInput argument origin)
      (some (encodeCertificate (betaBlock (betaExpansion domain body codomain checkedBody argument argumentType) origin)))
      (4 * ((betaTemplate domain body codomain checkedBody).length + 1) *
        ((betaInput argument origin).length + 1)) := by
  have ran := Indexed.outputs (betaTemplate domain body codomain checkedBody) (betaFields argument origin)
  have same := beta_exact domain body codomain checkedBody argument argumentType origin
  exact same ▸ ran

/-- The actual second beta body retains the first closed operand at its
original index and its original type. -/
theorem betaSecond_checked (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left : CanonicalTerm) (leftType : left.ty = first) :
    (DBTerm.instantiateAt left.term 1 body).inferType [second] = some codomain := by
  simpa using DBTerm.inferType_instantiateAt left.term body first
    (by simpa [leftType] using left.checked) [second] bodyChecked

private def seedConstant (type : Ty) : CanonicalTerm :=
  CanonicalTerm.constant (.mk (Name.global "template.seed") .undefined) type

/-- Static compilation is admitted by the existing source representative
algorithm on a typed closed constant. Its bytes do not occur in emitted
proofs: it only establishes that the fixed slot plan has a result. -/
theorem betaSecond_compile_isSome (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain) :
    (TemplateInstantiationMachine.Named.compile 1 body [betaNeedle second body]).isSome := by
  let replacement := seedConstant first
  let source : SourceTerm := .const (.mk (Name.global "template.seed") .undefined) first
  have empty : freeNames replacement.term = [] := rfl
  have contextIndependent : ∀ binders, named? replacement.term binders = some source := fun _ => rfl
  have checked := betaSecond_checked first second codomain body bodyChecked replacement rfl
  have scope : DBTerm.LooseBelow [betaNeedle second body].length
      (DBTerm.instantiateAt replacement.term 1 body) := DBTerm.looseBelow_of_inferType checked
  have names := TemplateInstantiationMachine.Named.freeNames_instantiateAt replacement.term empty 1 body
  have unique : ([betaNeedle second body].map Var.name).Nodup := by simp
  have fresh : ∀ name ∈ freeNames (DBTerm.instantiateAt replacement.term 1 body),
      name ∉ [betaNeedle second body].map Var.name := by
    rw [names]
    intro name member
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact fun equal => betaNeedle_fresh second body (equal ▸ member)
  have computed := TemplateInstantiationMachine.Named.named_computed _ _ scope unique fresh
  have exactResult := TemplateInstantiationMachine.Named.compile_exact replacement.term source empty
    contextIndependent 1 body [betaNeedle second body]
  rw [computed] at exactResult
  cases compiled : TemplateInstantiationMachine.Named.compile 1 body [betaNeedle second body] with
  | none => simp [compiled] at exactResult
  | some template => rfl

/-- The second BETA source has a dynamic first operand but a fixed authored
binder plan. The same named-template compiler retains all original names. -/
def betaSecondSourceTemplate (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain) : Template Alphabet :=
  let needle := betaNeedle second body
  let bodyTemplate := (TemplateInstantiationMachine.Named.compile 1 body [needle]).get
    (betaSecond_compile_isSome first second codomain body bodyChecked)
  let header := [4] ++ [4] ++ encodeData (.atom 2) ++ [4] ++
    [4] ++ encodeData (.atom 3) ++ [4] ++ encodeWith nameCodec needle.name ++
    [4] ++ encodeWith tyCodec second
  let suffix := encodeWith sourceTermCodec (.var needle.name second) ++ encodeWith tyCodec codomain
  header.map some ++ bodyTemplate ++ suffix.map some

set_option maxRecDepth 4096 in
theorem betaSecondSource_exact (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left : CanonicalTerm) (leftType : left.ty = first) (source : SourceTerm)
    (empty : freeNames left.term = [])
    (contextIndependent : ∀ binders, named? left.term binders = some source) :
    instantiate (betaSecondSourceTemplate first second codomain body bodyChecked)
      (encodeWith sourceTermCodec source) =
      encodeWith checkedSourceCodec (betaSource second (DBTerm.instantiateAt left.term 1 body) codomain
        (betaSecond_checked first second codomain body bodyChecked left leftType)) := by
  let needle := betaNeedle second body
  let nextBody := DBTerm.instantiateAt left.term 1 body
  let checked := betaSecond_checked first second codomain body bodyChecked left leftType
  let bodyTemplate := (TemplateInstantiationMachine.Named.compile 1 body [needle]).get
    (betaSecond_compile_isSome first second codomain body bodyChecked)
  have compiled : TemplateInstantiationMachine.Named.compile 1 body [needle] = some bodyTemplate :=
    (Option.some_get _).symm
  have names := TemplateInstantiationMachine.Named.freeNames_instantiateAt left.term empty 1 body
  have needleSame : betaNeedle second nextBody = needle := by
    simp only [betaNeedle, nextBody, names, needle]
  have scope : DBTerm.LooseBelow [needle].length nextBody := DBTerm.looseBelow_of_inferType checked
  have unique : ([needle].map Var.name).Nodup := by simp
  have fresh : ∀ name ∈ freeNames nextBody, name ∉ [needle].map Var.name := by
    rw [show freeNames nextBody = freeNames body from names]
    intro name member
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact fun equal => betaNeedle_fresh second body (equal ▸ member)
  have bodyExact := TemplateInstantiationMachine.Named.compiled_named_exact left.term source empty
    contextIndependent 1 body [needle] bodyTemplate compiled scope unique fresh
  simp only [betaSecondSourceTemplate, instantiate_append, instantiate_literals]
  change _ ++ instantiate bodyTemplate (encodeWith sourceTermCodec source) ++ _ = _
  rw [bodyExact]
  dsimp only [nextBody, needle] at needleSame
  simp only [betaSource, needleSame, checkedSourceCodec, Codec.prod, Codec.mapped, encodeWith,
    sourceTermCodec, tyCodec, putSourceTerm, encodeData_pair, List.append_assoc]
  simp only [List.cons_append, List.nil_append, List.append_assoc, needle]

/-- The original dynamic second BETA source is built by actual word copying;
its fixed authored plan contributes no unbounded run-time register. -/
def betaSecondSourceOutputs (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left : CanonicalTerm) (leftType : left.ty = first) (source : SourceTerm)
    (empty : freeNames left.term = [])
    (contextIndependent : ∀ binders, named? left.term binders = some source) :
    TM2OutputsInTime (machine (betaSecondSourceTemplate first second codomain body bodyChecked))
      (encodeWith sourceTermCodec source)
      (some (encodeWith checkedSourceCodec (betaSource second (DBTerm.instantiateAt left.term 1 body) codomain
        (betaSecond_checked first second codomain body bodyChecked left leftType))))
      (4 * ((betaSecondSourceTemplate first second codomain body bodyChecked).length + 1) *
        ((encodeWith sourceTermCodec source).length + 1)) := by
  have ran := Mettapedia.Computability.WordTemplateMachine.outputs
    (betaSecondSourceTemplate first second codomain body bodyChecked) (encodeWith sourceTermCodec source)
  have same := betaSecondSource_exact first second codomain body bodyChecked left leftType source
    empty contextIndependent
  exact same ▸ ran

/-- Two original substitution passes are compiled into the same indexed plan,
retaining the finite formal interval and each complete operand occurrence. -/
def twoSubstitutions {arity : Nat} (depth : Nat) (body : DBTerm)
    (first second : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  Templates.substitute (TemplateInstantiationMachine.Indexed.compile 2 depth body) ![first, second]

theorem twoSubstitutions_exact {arity : Nat} (depth : Nat) (body : DBTerm)
    (first second : Indexed.Template Alphabet arity) (words : Fin arity → List Alphabet)
    (left right : CanonicalTerm)
    (firstExact : Indexed.instantiate first words = encodeWith dbTermCodec left.term)
    (secondExact : Indexed.instantiate second words = encodeWith dbTermCodec right.term) :
    Indexed.instantiate (twoSubstitutions depth body first second) words =
      encodeWith dbTermCodec (DBTerm.instantiateAt left.term depth
        (DBTerm.instantiateAt right.term (depth + 1) body)) := by
  rw [twoSubstitutions, Templates.substitute_exact]
  have fields : (fun index : Fin 2 => Indexed.instantiate (![first, second] index) words) =
      TemplateInstantiationMachine.Indexed.argumentWords [left, right] := by
    funext index
    fin_cases index <;> simp [TemplateInstantiationMachine.Indexed.argumentWords, firstExact, secondExact,
      TemplateInstantiationMachine.termWire, dbTermCodec, encodeWith]
  rw [fields]
  simpa [TemplateInstantiationMachine.Indexed.sequence, TemplateInstantiationMachine.termWire,
    dbTermCodec, encodeWith] using TemplateInstantiationMachine.Indexed.compile_exact [left, right] depth body

/-- The seven-node original double-beta graph has only five dynamic fields:
two complete raw operands, their original named representatives and origin.
The second named BETA witness is computed by the same fixed-body plan. -/
def doubleBetaNodes (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain) :
    List (Node (Indexed.Template Alphabet 5) (Indexed.Template Alphabet 5)
      (Indexed.Template Alphabet 5)) :=
  let innerChecked : (DBTerm.abs second body).inferType [first] = some (.function second codomain) := by
    simp [DBTerm.inferType, bodyChecked]
  let seed := betaSeed first (.abs second body) (.function second codomain) innerChecked
  let left : Indexed.Template Alphabet 5 := [.inr 0]
  let right : Indexed.Template Alphabet 5 := [.inr 1]
  let leftSource : Indexed.Template Alphabet 5 := [.inr 2]
  let rightSource : Indexed.Template Alphabet 5 := [.inr 3]
  let origin : Indexed.Template Alphabet 5 := [.inr 4]
  let nextBody := Templates.single 0 (TemplateInstantiationMachine.compile 1 body)
  let before := Templates.application (Templates.literal (putTerm (.abs first (.abs second body)))) left
  let after := Templates.pair (Templates.literal (.atom 4))
    (Templates.pair (Templates.literal (putTy second)) nextBody)
  let firstConclusion := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality (.function second codomain) before after))
  let firstEntries := Templates.pair
    (Templates.pair (Templates.pair leftSource (Templates.literal (putTy first)))
      (Templates.literal (putSourceTerm (.var (betaNeedle first (.abs second body)).name first))))
    (Templates.literal (.atom 0))
  let firstInst := unaryRequest 9
    (Templates.pair firstEntries (Templates.literal (theoremCodec.put seed.intermediate)))
  let rightCanonical := Templates.canonical second right
  let rightProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality second right right))
  let whole := Templates.application before right
  let middle := Templates.application after right
  let applicationProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain whole middle))
  let needle := betaNeedle second body
  let needleTerm := Templates.literal (putTerm (.free needle))
  let secondSource := Templates.single 2 (betaSecondSourceTemplate first second codomain body bodyChecked)
  let secondIntermediate := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain
      (Templates.application after needleTerm) (twoSubstitutions 0 body needleTerm left)))
  let secondEntries := Templates.pair
    (Templates.pair (Templates.pair rightSource (Templates.literal (putTy second)))
      (Templates.literal (putSourceTerm (.var needle.name second))))
    (Templates.literal (.atom 0))
  let secondConclusion := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain middle (twoSubstitutions 0 body right left)))
  let final := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain whole (twoSubstitutions 0 body right left)))
  [⟨Templates.literal (theoremCodec.put seed.intermediate),
      Templates.literal (requestCodec.put (.inference (.beta seed.source))), [], origin⟩,
   ⟨firstConclusion, firstInst, [0], origin⟩,
   ⟨rightProof, unaryRequest 0 rightCanonical, [], origin⟩,
   ⟨applicationProof, binaryRequest 2 firstConclusion rightProof, [1, 2], origin⟩,
   ⟨secondIntermediate, unaryRequest 4 secondSource, [], origin⟩,
   ⟨secondConclusion, unaryRequest 9 (Templates.pair secondEntries secondIntermediate), [4], origin⟩,
   ⟨final, binaryRequest 1 applicationProof secondConclusion, [3, 5], origin⟩]

def doubleBetaTemplate (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain) : Indexed.Template Alphabet 5 :=
  certificateTemplate (doubleBetaNodes first second codomain body bodyChecked, 6)

def doubleBetaFields (left right : CanonicalTerm) (origin : Origin) : Fin 5 → List Alphabet :=
  ![encodeWith dbTermCodec left.term, encodeWith dbTermCodec right.term,
    encodeWith sourceTermCodec (checkedSource left).source,
    encodeWith sourceTermCodec (checkedSource right).source, encodeWith originCodec origin]

def doubleBetaInput (left right : CanonicalTerm) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (doubleBetaFields left right origin)

/-- The stored first BETA theorem is the ordinary free-binder beta equation,
independent of the operand supplied to the later INST node. -/
theorem betaIntermediate_exact (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    (betaExpansion domain body codomain checkedBody argument argumentType).intermediate =
      Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType
        (betaRedex domain body codomain checkedBody (CanonicalTerm.free (betaNeedle domain body)) rfl)
        (betaReduced domain body codomain checkedBody (CanonicalTerm.free (betaNeedle domain body)) rfl) rfl) := by
  apply Theorem.ext
  · rfl
  · apply Sequent.ext
    · rfl
    · apply CanonicalTerm.ext_term
      simp only [betaExpansion, Theorem.emptyResult, CanonicalTerm.equalityOfSameType,
        betaReduced, betaRedex, CanonicalTerm.free,
        CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex]
      have image := betaSource_term domain body codomain checkedBody
      simp only [CheckedSourceTerm.canonical] at image
      rw [image]
      rfl

theorem betaEntries_exact (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    (betaExpansion domain body codomain checkedBody argument argumentType).entries =
      [(checkedSource argument, .var (betaNeedle domain body).name domain)] := rfl

theorem betaExpansion_source_exact (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    (betaExpansion domain body codomain checkedBody argument argumentType).source =
      betaSource domain body codomain checkedBody := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem doubleBetaNodes_exact (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (origin : Origin) :
    (doubleBetaNodes first second codomain body bodyChecked).map
      (Node.map (fun template => Indexed.instantiate template (doubleBetaFields left right origin))
        (fun template => Indexed.instantiate template (doubleBetaFields left right origin))
        (fun template => Indexed.instantiate template (doubleBetaFields left right origin))) =
      (doubleBetaBlock
        (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) origin).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  let fields := doubleBetaFields left right origin
  let leftSlot : Indexed.Template Alphabet 5 := [.inr 0]
  let rightSlot : Indexed.Template Alphabet 5 := [.inr 1]
  let needle := betaNeedle second body
  let needleSlot : Indexed.Template Alphabet 5 := Templates.literal (putTerm (.free needle))
  have leftExact : Indexed.instantiate leftSlot fields = encodeWith dbTermCodec left.term := by
    simp [leftSlot, fields, doubleBetaFields]
  have rightExact : Indexed.instantiate rightSlot fields = encodeWith dbTermCodec right.term := by
    simp [rightSlot, fields, doubleBetaFields]
  have nextSlot : Indexed.instantiate (Templates.single 0 (TemplateInstantiationMachine.compile 1 body)) fields =
      encodeWith dbTermCodec (DBTerm.instantiateAt left.term 1 body) := by
    rw [Templates.single_exact]
    exact TemplateInstantiationMachine.compile_exact 1 body left.term
  have reducedSlot := twoSubstitutions_exact 0 body rightSlot leftSlot fields right left rightExact leftExact
  have freeExact : Indexed.instantiate needleSlot fields =
      encodeWith dbTermCodec (CanonicalTerm.free needle).term := Templates.literal_exact _ _
  have intermediateSlot := twoSubstitutions_exact 0 body needleSlot leftSlot fields
    (CanonicalTerm.free needle) left freeExact leftExact
  have sourceSlot : Indexed.instantiate
      (Templates.single 2 (betaSecondSourceTemplate first second codomain body bodyChecked)) fields =
      encodeWith checkedSourceCodec (betaSource second (DBTerm.instantiateAt left.term 1 body) codomain
        (betaSecond_checked first second codomain body bodyChecked left leftType)) := by
    rw [Templates.single_exact]
    exact betaSecondSource_exact first second codomain body bodyChecked left leftType
      (checkedSource left).source leftEmpty leftNamed
  have needleSame : betaNeedle second (DBTerm.instantiateAt left.term 1 body) = needle := by
    simp only [betaNeedle, TemplateInstantiationMachine.Named.freeNames_instantiateAt left.term leftEmpty, needle]
  have leftSourceType : (checkedSource left).ty = first :=
    (congrArg CanonicalTerm.ty (checkedSource_exact left)).trans leftType
  have rightSourceType : (checkedSource right).ty = second :=
    (congrArg CanonicalTerm.ty (checkedSource_exact right)).trans rightType
  dsimp only [fields, leftSlot, rightSlot, needleSlot, needle] at nextSlot reducedSlot intermediateSlot sourceSlot needleSame
  simp only [doubleBetaNodes, Node.map, List.map_cons, List.map_nil, unaryRequest, binaryRequest,
    Templates.theoremTemplate, Templates.canonical, Templates.equality, Templates.application,
    Templates.pair_exact, Templates.literal_exact, Indexed.instantiate_hole, Indexed.instantiate_nil,
    nextSlot, reducedSlot, intermediateSlot, sourceSlot]
  simp [Node.map, doubleBetaFields, doubleBetaBlock, doubleBetaExpansion, betaSeed, betaExpansion_source_exact,
    betaIntermediate_exact, betaEntries_exact, betaExpansion_conclusion, needleSame,
    appResult, transResult, reflexivity, Theorem.unionResult, Theorem.emptyResult,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType, CanonicalTerm.free,
    betaRedex, betaReduced, DBTerm.instantiateAt, rightType, leftSourceType, rightSourceType,
    requestCodec, putRequest, putInference,
    canonicalCodec, theoremCodec, sequentCodec, termMapletCodec, checkedSourceCodec, sourceTermCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped, Codec.list, Codec.putList,
    encodeWith, encodeData_pair, putTerm, CanonicalTerm.equalityDB, List.append_assoc]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem doubleBeta_exact (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (origin : Origin) :
    Indexed.instantiate (doubleBetaTemplate first second codomain body bodyChecked)
      (doubleBetaFields left right origin) =
      encodeCertificate (doubleBetaBlock
        (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) origin) := by
  exact certificateTemplate_of_nodes
    (doubleBetaNodes first second codomain body bodyChecked)
    (doubleBetaBlock
      (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) origin).1 6
    (doubleBetaFields left right origin)
    (doubleBetaNodes_exact first second codomain body bodyChecked left right leftType rightType
      leftEmpty leftNamed origin)

/-- The complete original seven-node block is emitted by actual finite-field
copying. The clock charges all operand representations and all origin bytes. -/
def doubleBetaOutputs (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (origin : Origin) :
    TM2OutputsInTime (Indexed.machine (doubleBetaTemplate first second codomain body bodyChecked))
      (doubleBetaInput left right origin)
      (some (encodeCertificate (doubleBetaBlock
        (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) origin)))
      (4 * ((doubleBetaTemplate first second codomain body bodyChecked).length + 1) *
        ((doubleBetaInput left right origin).length + 1)) := by
  have ran := Indexed.outputs (doubleBetaTemplate first second codomain body bodyChecked)
    (doubleBetaFields left right origin)
  have same := doubleBeta_exact first second codomain body bodyChecked left right leftType rightType
    leftEmpty leftNamed origin
  exact same ▸ ran

/-- Byte decoding retains the exact original graph and its chronological
root, rather than certifying a different emitted proof representation. -/
theorem doubleBeta_decodes (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (origin : Origin) :
    decodeCertificate (Indexed.instantiate (doubleBetaTemplate first second codomain body bodyChecked)
      (doubleBetaFields left right origin)) =
      some (doubleBetaBlock
        (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) origin) := by
  rw [doubleBeta_exact first second codomain body bodyChecked left right leftType rightType
    leftEmpty leftNamed origin, decodeCertificate_encodeCertificate]

/-- The original checker accepts the emitted bytes at their exact ordinary
HOL conclusion; no emitter-specific semantic authority is introduced. -/
theorem doubleBeta_emitted_checked (policy : AxiomPolicy) [DecidablePred policy]
    (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (origin : Origin) :
    (decodeCertificate (Indexed.instantiate (doubleBetaTemplate first second codomain body bodyChecked)
      (doubleBetaFields left right origin))).map
      ((ProofSystem.checker policy).check
        (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType).conclusion) =
      some true := by
  rw [doubleBeta_decodes first second codomain body bodyChecked left right leftType rightType
    leftEmpty leftNamed origin, Option.map_some]
  congr 1
  apply (ProofSystem.checker_check_iff policy _ _).mpr
  exact doubleBetaBlock_checked policy _ origin

/-- A fixed authored primitive block retains all original theorem, request
and parent bytes, while the originating rule occurrence stays dynamic. -/
def stampedBlock (origin : Origin) (block : ProofSystem.Certificate) : ProofSystem.Certificate :=
  (block.1.map (fun receipt => {receipt with origin := origin}), block.2)

def blockNodes (block : ProofSystem.Certificate) : List (Node
    (Indexed.Template Alphabet 1) (Indexed.Template Alphabet 1) (Indexed.Template Alphabet 1)) :=
  block.1.map fun receipt =>
    ⟨Templates.literal (theoremCodec.put receipt.conclusion),
      Templates.literal (requestCodec.put receipt.witness), receipt.parents, [.inr 0]⟩

def blockTemplate (block : ProofSystem.Certificate) : Indexed.Template Alphabet 1 :=
  certificateTemplate (blockNodes block, block.2)

def originFields (origin : Origin) : Fin 1 → List Alphabet := ![encodeWith originCodec origin]

theorem blockNodes_exact (block : ProofSystem.Certificate) (origin : Origin) :
    (blockNodes block).map
      (Node.map (fun template => Indexed.instantiate template (originFields origin))
        (fun template => Indexed.instantiate template (originFields origin))
        (fun template => Indexed.instantiate template (originFields origin))) =
      (stampedBlock origin block).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  simp [blockNodes, Node.map, originFields, stampedBlock, List.map_map, encodeWith]

set_option maxRecDepth 4096 in
theorem block_exact (block : ProofSystem.Certificate) (origin : Origin) :
    Indexed.instantiate (blockTemplate block) (originFields origin) =
      encodeCertificate (stampedBlock origin block) := by
  exact certificateTemplate_of_nodes (blockNodes block) (stampedBlock origin block).1 block.2
    (originFields origin) (blockNodes_exact block origin)

/-- Static primitive blocks are copied through the same finite-word machine;
all dynamic origin bytes and every stored original field are charged. -/
def blockOutputs (block : ProofSystem.Certificate) (origin : Origin) :
    TM2OutputsInTime (Indexed.machine (blockTemplate block)) (Indexed.argumentWire (originFields origin))
      (some (encodeCertificate (stampedBlock origin block)))
      (4 * ((blockTemplate block).length + 1) * ((Indexed.argumentWire (originFields origin)).length + 1)) := by
  have ran := Indexed.outputs (blockTemplate block) (originFields origin)
  have same := block_exact block origin
  exact same ▸ ran

/-- A local primitive request stores its full claim and witness fields and
uses exactly the original consecutive external-parent vector. -/
def primitiveNodes {arity : Nat} (parentCount : Nat)
    (claim request origin : Indexed.Template Alphabet arity) : List (Node
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)) :=
  [⟨claim, request, List.range parentCount, origin⟩]

def primitiveTemplate {arity : Nat} (parentCount : Nat)
    (claim request origin : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  certificateTemplate (primitiveNodes parentCount claim request origin, parentCount)

/-- Lowering a primitive node preserves its original parent vector and
all three encoded payload fields. -/
theorem primitiveNodes_exact {arity : Nat} (parentCount : Nat)
    (claimPlan requestPlan originPlan : Indexed.Template Alphabet arity)
    (fields : Fin arity → List Alphabet) (request : RuleRequest) (claim : Theorem) (origin : Origin)
    (parentsExact : request.premises.length = parentCount)
    (claimExact : Indexed.instantiate claimPlan fields = encodeWith theoremCodec claim)
    (requestExact : Indexed.instantiate requestPlan fields = encodeWith requestCodec request)
    (originExact : Indexed.instantiate originPlan fields = encodeWith originCodec origin) :
    (primitiveNodes parentCount claimPlan requestPlan originPlan).map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)) =
      (primitiveBlock request claim origin).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  simp only [primitiveNodes, primitiveBlock, List.map_cons, List.map_nil, Node.map,
    parentsExact, claimExact, requestExact, originExact]

/-- Exact local node payloads determine the exact final claim field. -/
theorem lastConclusion_exact {arity : Nat}
    (nodes : List (Node (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)))
    (actual : List ProofExecution.Receipt) (plan : Indexed.Template Alphabet arity)
    (claim : Theorem) (fields : Fin arity → List Alphabet)
    (nodesExact : nodes.map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)) =
      actual.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))
    (planLast : nodes.getLast?.map Node.conclusion = some plan)
    (claimLast : actual.getLast?.map Node.conclusion = some claim) :
    Indexed.instantiate plan fields = encodeWith theoremCodec claim := by
  have observed := congrArg (fun values => values.getLast?.map Node.conclusion) nodesExact
  have observed' :
      (nodes.getLast?.map Node.conclusion).map (fun template => Indexed.instantiate template fields) =
      (actual.getLast?.map Node.conclusion).map (encodeWith theoremCodec) := by
    simpa only [List.getLast?_map, Option.map_map, Function.comp_def, Node.map] using observed
  rw [planLast, claimLast] at observed'
  exact Option.some.inj observed'

/-- Reflexivity field emission is the original primitive REFL request,
with its checked type and complete canonical equality claim. -/
theorem reflexivityNodes_exact {arity : Nat}
    (termPlan originPlan : Indexed.Template Alphabet arity)
    (fields : Fin arity → List Alphabet) (term : CanonicalTerm) (type : Ty)
    (sameType : term.ty = type) (origin : Origin)
    (termExact : Indexed.instantiate termPlan fields = encodeWith dbTermCodec term.term)
    (originExact : Indexed.instantiate originPlan fields = encodeWith originCodec origin) :
    (primitiveNodes 0
      (Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool (Templates.equality type termPlan termPlan)))
      (unaryRequest 0 (Templates.canonical type termPlan)) originPlan).map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)) =
      (primitiveBlock (.inference (.refl term)) (reflexivity term) origin).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  apply primitiveNodes_exact 0 _ _ _ fields (.inference (.refl term)) (reflexivity term) origin rfl
  · apply Templates.theoremTemplate_exact ∅ ∅ _ fields (reflexivity term) rfl rfl
    apply Templates.canonical_exact Ty.bool _ fields (CanonicalTerm.equalityOfSameType term term rfl) rfl
    simpa only [CanonicalTerm.equalityOfSameType, sameType] using
      Templates.equality_exact type termPlan termPlan fields term.term term.term termExact termExact
  · have canonicalExact := Templates.canonical_exact type termPlan fields term sameType termExact
    simp only [unaryRequest, Templates.pair_exact, Templates.literal_exact, canonicalExact,
      encodeWith, requestCodec, putRequest, putInference, encodeData_pair, List.cons_append]
  · exact originExact

theorem primitive_exact {arity : Nat} (parentCount : Nat)
    (claimPlan requestPlan originPlan : Indexed.Template Alphabet arity)
    (fields : Fin arity → List Alphabet) (request : RuleRequest) (claim : Theorem) (origin : Origin)
    (parentsExact : request.premises.length = parentCount)
    (claimExact : Indexed.instantiate claimPlan fields = encodeWith theoremCodec claim)
    (requestExact : Indexed.instantiate requestPlan fields = encodeWith requestCodec request)
    (originExact : Indexed.instantiate originPlan fields = encodeWith originCodec origin) :
    Indexed.instantiate (primitiveTemplate parentCount claimPlan requestPlan originPlan) fields =
      encodeCertificate (primitiveBlock request claim origin) := by
  simp only [primitiveTemplate, primitiveNodes, certificateTemplate, List.map_cons, List.map_nil,
    nodeTemplate, listTemplate, receiptTemplate, Templates.pair_exact,
    Templates.literal_exact, claimExact, requestExact, originExact]
  simp only [primitiveBlock, parentsExact, encodeCertificate, certificateCodec, receiptCodec,
    Codec.prod, Codec.mapped, Codec.list, Codec.putList, Codec.nat, encodeWith, encodeData_pair]
  rfl

/-- The same concrete indexed machine serializes primitive fields, with a
clock attached to each scanned byte and each literal template occurrence. -/
def primitiveOutputs {arity : Nat} (parentCount : Nat)
    (claimPlan requestPlan originPlan : Indexed.Template Alphabet arity)
    (fields : Fin arity → List Alphabet) (request : RuleRequest) (claim : Theorem) (origin : Origin)
    (parentsExact : request.premises.length = parentCount)
    (claimExact : Indexed.instantiate claimPlan fields = encodeWith theoremCodec claim)
    (requestExact : Indexed.instantiate requestPlan fields = encodeWith requestCodec request)
    (originExact : Indexed.instantiate originPlan fields = encodeWith originCodec origin) :
    TM2OutputsInTime (Indexed.machine (primitiveTemplate parentCount claimPlan requestPlan originPlan))
      (Indexed.argumentWire fields) (some (encodeCertificate (primitiveBlock request claim origin)))
      (4 * ((primitiveTemplate parentCount claimPlan requestPlan originPlan).length + 1) *
        ((Indexed.argumentWire fields).length + 1)) := by
  have ran := Indexed.outputs (primitiveTemplate parentCount claimPlan requestPlan originPlan) fields
  have same := primitive_exact parentCount claimPlan requestPlan originPlan fields request claim origin
    parentsExact claimExact requestExact originExact
  exact same ▸ ran

end Emission

end Mettapedia.Languages.HOLLight.EqualityExpansion
