import Mettapedia.Languages.HOLLight.FirstOrder.Steps
import Mettapedia.Languages.MM0.Translation.LemmaSimulation

/-!
# The size of the proof of one node

The proof a translation builds for a node is at most polynomial in the size of the node's
request (`ruleProof_weight`). An open certificate weighs at most thirty-five times the
judgments of its derivation (`CalculusSimulation.openWeight_eraseOpen_le`, with seventeen
formals per rule at most). The judgments of a core are its computed judgment, the cited
judgments, and the judgments of the closed derivations beside them, which `Sizes` bounds
builder by builder.

The bounds compose through `Within size factor degree value`, which says
`value ≤ factor * (size + 1) ^ degree`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (OpenDerivation OpenDerivationList RawOpenProof)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (weight weights openWeight openJudgmentWeight openJudgmentWeights openJudgmentWeight_ofClosed
    openWeight_eraseOpen_le judgmentWeight judgmentWeights substSchema substSchemas)
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)

/-! ## The size of a request -/

/-- The size of a rule request: the encodings of its data, premises included. -/
def requestSize : RuleRequest → ℕ
  | .inference (.refl term) => weight (groundP (encodeTerm term.term)) + weight (groundP (encodeTy term.ty))
  | .inference (.assume term) => weight (groundP (encodeTerm term.term)) + weight (groundP (encodeTy term.ty))
  | .inference (.trans left right) => weight (sequentJ left.sequent) + weight (sequentJ right.sequent)
  | .inference (.mkComb functions arguments) =>
      weight (sequentJ functions.sequent) + weight (sequentJ arguments.sequent)
  | .inference (.abs binder input) => weight (freeVarP binder) + weight (sequentJ input.sequent)
  | .inference (.beta source) =>
      weight (groundP (encodeSourceTerm source.source)) + weight (groundP (encodeTy source.ty))
  | .inference (.eqMp equality premise) => weight (sequentJ equality.sequent) + weight (sequentJ premise.sequent)
  | .inference (.deductAntisym left right) => weight (sequentJ left.sequent) + weight (sequentJ right.sequent)
  | .inference (.instType entries input) => weight (typeMapletsP entries) + weight (sequentJ input.sequent)
  | .inference (.inst maplets input) => weight (termMapletsP maplets) + weight (sequentJ input.sequent)
  | .axiom sequent => weight (sequentJ sequent)

/-! ## Polynomial envelopes -/

/-- `value ≤ factor * (size + 1) ^ degree`. -/
def Within (size factor degree value : ℕ) : Prop := value ≤ factor * (size + 1) ^ degree

namespace Within

variable {size : ℕ}

theorem of_le {value : ℕ} (le : value ≤ size) : Within size 1 1 value := by
  unfold Within
  simp only [pow_one, one_mul]
  omega

theorem const (constant : ℕ) : Within size constant 0 constant := by
  unfold Within
  simp

theorem le_of {value value' factor degree : ℕ} (le : value' ≤ value) (within : Within size factor degree value) :
    Within size factor degree value' :=
  le_trans le within

theorem raise {value factor degree factor' degree' : ℕ} (within : Within size factor degree value)
    (factors : factor ≤ factor') (degrees : degree ≤ degree') : Within size factor' degree' value := by
  unfold Within at *
  calc value ≤ factor * (size + 1) ^ degree := within
    _ ≤ factor' * (size + 1) ^ degree' := Nat.mul_le_mul factors (Nat.pow_le_pow_right (by omega) degrees)

theorem add {first second factor factor' degree degree' : ℕ} (left : Within size factor degree first)
    (right : Within size factor' degree' second) :
    Within size (factor + factor') (max degree degree') (first + second) := by
  have left' := left.raise le_rfl (le_max_left degree degree')
  have right' := right.raise le_rfl (le_max_right degree degree')
  unfold Within at *
  rw [Nat.add_mul]
  exact Nat.add_le_add left' right'

theorem mul {first second factor factor' degree degree' : ℕ} (left : Within size factor degree first)
    (right : Within size factor' degree' second) :
    Within size (factor * factor') (degree + degree') (first * second) := by
  unfold Within at *
  calc first * second ≤ (factor * (size + 1) ^ degree) * (factor' * (size + 1) ^ degree') := Nat.mul_le_mul left right
    _ = factor * factor' * (size + 1) ^ (degree + degree') := by ring

theorem add_const {value factor degree : ℕ} (within : Within size factor degree value) (constant : ℕ) :
    Within size (factor + constant) degree (value + constant) := by
  unfold Within at *
  have one : 1 ≤ (size + 1) ^ degree := Nat.one_le_pow _ _ (by omega)
  rw [Nat.add_mul]
  exact Nat.add_le_add within (by nlinarith)

theorem scale {value factor degree : ℕ} (within : Within size factor degree value) (constant : ℕ) :
    Within size (constant * factor) degree (constant * value) := by
  unfold Within at *
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ within

/-- A size bound transfers to a larger size. -/
theorem enlarge {size' value factor degree : ℕ} (within : Within size factor degree value) (le : size ≤ size') :
    Within size' factor degree value := by
  unfold Within at *
  exact le_trans within (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

end Within

/-! ## The judgments of the open constructions -/

section Structure

variable {definition : ValidatedCalculusLanguageDef} {context : List Pattern}

theorem openJudgmentWeight_recastOpen {first second : Pattern} (same : first = second)
    (derivation : OpenDerivation definition context first) :
    openJudgmentWeight (recastOpen same derivation) = openJudgmentWeight derivation := by
  subst same
  rfl

theorem openJudgmentWeight_fireOpenAt {r : RuleSchema} (member : r ∈ definition.1.rules) (shape : RuleShape r)
    (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : OpenDerivationList definition context premises) :
    openJudgmentWeight (fireOpenAt member shape arguments arity valid premisesEq conclusionEq children) =
      weight conclusion + 1 + openJudgmentWeights children := by
  unfold fireOpenAt
  rw [openJudgmentWeight]

theorem openJudgmentWeight_asThmOpen {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : sequentHypothesesP sequent = hypotheses) (conclusionEq : sequentConclusionP sequent = conclusion)
    (derivation : OpenDerivation definition context (sequentJ sequent)) :
    openJudgmentWeight (asThmOpen hypothesesEq conclusionEq derivation) = openJudgmentWeight derivation :=
  openJudgmentWeight_recastOpen _ derivation

theorem openJudgmentWeight_premiseLeaf {index : Nat} {goal : Pattern} {leaf : OpenDerivation definition context goal}
    (found : premiseLeaf (definition := definition) (context := context) index goal = some leaf) :
    openJudgmentWeight leaf = weight goal + 1 := by
  unfold premiseLeaf at found
  split_ifs at found with bound same
  cases found
  rw [openJudgmentWeight_recastOpen, openJudgmentWeight, same]

theorem openJudgmentWeights_cons {premise : Pattern} {premises : List Pattern}
    (head : OpenDerivation definition context premise) (tail : OpenDerivationList definition context premises) :
    openJudgmentWeights (OpenDerivationList.cons head tail) = openJudgmentWeight head + openJudgmentWeights tail := by
  rw [openJudgmentWeights]

theorem openJudgmentWeights_nil :
    openJudgmentWeights (OpenDerivationList.nil : OpenDerivationList definition context []) = 0 := by
  rw [openJudgmentWeights]

theorem judgmentWeight_recast {first second : Pattern} (same : first = second)
    (derivation : Derivation definition first) : judgmentWeight (recast same derivation) = judgmentWeight derivation := by
  subst same
  rfl

end Structure

/-! ## The weights of rendered data -/

theorem weight_thmJ (hypotheses conclusion : Pattern) :
    weight (thmJ hypotheses conclusion) = 10 + weight hypotheses + weight conclusion := by
  simp only [thmJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Thm".length = 7 from rfl]
  omega

theorem weight_sequentJ (sequent : Sequent) :
    weight (sequentJ sequent) =
      10 + weight (treesP (hypothesisTrees sequent.hyp)) + weight (groundP (encodeTerm sequent.concl.term)) := by
  rw [sequentJ, weight_thmJ, sequentHypothesesP_eq_treesP, sequentConclusionP_eq]

theorem weight_appTermP (function argument : Pattern) :
    weight (appTermP function argument) = 308 + weight function + weight argument := by
  rw [appTermP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termAppLabel = 23 from rfl]
  omega

theorem weight_absTermP (type body : Pattern) : weight (absTermP type body) = 319 + weight type + weight body := by
  rw [absTermP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termAbsLabel = 24 from rfl]
  omega

theorem weight_freeTermP (name type : Pattern) : weight (freeTermP name type) = 286 + weight name + weight type := by
  rw [freeTermP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termFreeLabel = 21 from rfl]
  omega

theorem weight_constTermP (constant type : Pattern) :
    weight (constTermP constant type) = 275 + weight constant + weight type := by
  rw [constTermP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termConstLabel = 20 from rfl]
  omega

theorem weight_functionTyP (domain codomain : Pattern) :
    weight (functionTyP domain codomain) = 3621 + weight domain + weight codomain := by
  rw [functionTyP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show tyOpLabel = 7 from rfl,
    weight_treeP_sum, show listLabel = 5 from rfl]
  have : weight functionOpP = 3379 := weight_functionOp
  omega

theorem weight_equalityTermP (type left right : Pattern) :
    weight (equalityTermP type left right) =
      8133 + weight equalityConstP + weight boolP + 2 * weight type + weight left + weight right := by
  rw [equalityTermP, weight_appTermP, weight_appTermP, weight_constTermP, weight_functionTyP, weight_functionTyP]
  omega

/-! ## Parts of terms weigh no more than the terms -/

theorem weight_eqLeft_le (term : DBTerm) :
    weight (groundP (encodeTerm (eqLeft term))) ≤ weight (groundP (encodeTerm term)) := by
  unfold eqLeft
  split
  · rename_i function left right
    rw [weight_encodeTerm_app, weight_encodeTerm_app]
    omega
  · exact le_rfl

theorem weight_eqRight_le (term : DBTerm) :
    weight (groundP (encodeTerm (eqRight term))) ≤ weight (groundP (encodeTerm term)) := by
  unfold eqRight
  split
  · rename_i function right
    rw [weight_encodeTerm_app]
    omega
  · exact le_rfl

theorem weight_tysP_head_le (type : Ty) (rest : List Ty) :
    weight (groundP (encodeTy type)) ≤ weight (tysP (type :: rest)) := by
  rw [weight_tysP_cons]
  omega

theorem weight_eqOperand_le (term : DBTerm) :
    weight (groundP (encodeTy (eqOperand term))) ≤ weight (groundP (encodeTerm term)) + weight boolP := by
  unfold eqOperand
  split
  · rename_i constant operator operand rest left right
    have head := weight_tysP_head_le operand rest
    rw [weight_encodeTerm_app, weight_encodeTerm_app, weight_encodeTerm_const, weight_encodeTy_op]
    omega
  · exact Nat.le_add_left _ _

theorem weight_domainOf_le (type : Ty) :
    weight (groundP (encodeTy (domainOf type))) ≤ weight (groundP (encodeTy type)) + weight boolP := by
  unfold domainOf
  split
  · rename_i operator domain rest
    have head := weight_tysP_head_le domain rest
    rw [weight_encodeTy_op]
    omega
  · exact Nat.le_add_left _ _

theorem weight_codomainOf_le (type : Ty) :
    weight (groundP (encodeTy (codomainOf type))) ≤ weight (groundP (encodeTy type)) + weight boolP := by
  unfold codomainOf
  split
  · rename_i operator domain codomain
    rw [weight_encodeTy_op, weight_tysP_cons, weight_tysP_cons]
    omega
  · exact Nat.le_add_left _ _

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms) {context : List Pattern}

/-! ## The judgments of the open rules -/

theorem openReflRule_weight {t a : Pattern} (valid : ∀ argument ∈ [t, a], Valid argument)
    (typed : OpenDerivation definition context (typeOfJ nilP t a)) :
    openJudgmentWeight (openReflRule calculus valid typed) =
      weight (thmJ nilP (equalityTermP a t t)) + 1 + openJudgmentWeight typed := by
  unfold openReflRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openAssumeRule_weight {t : Pattern} (valid : ∀ argument ∈ [t], Valid argument)
    (typed : OpenDerivation definition context (typeOfJ nilP t boolP)) :
    openJudgmentWeight (openAssumeRule calculus valid typed) =
      weight (thmJ (consP t nilP) t) + 1 + openJudgmentWeight typed := by
  unfold openAssumeRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openTransRule_weight {h1 h2 h a l m r : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, l, m, r], Valid argument)
    (left : OpenDerivation definition context (thmJ h1 (equalityTermP a l m)))
    (right : OpenDerivation definition context (thmJ h2 (equalityTermP a m r)))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    openJudgmentWeight (openTransRule calculus valid left right union) =
      weight (thmJ h (equalityTermP a l r)) + 1 +
        (openJudgmentWeight left + (openJudgmentWeight right + openJudgmentWeight union)) := by
  unfold openTransRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openMkCombRule_weight {h1 h2 h a b f g x y : Pattern}
    (valid : ∀ argument ∈ [h1, h2, h, a, b, f, g, x, y], Valid argument)
    (functions : OpenDerivation definition context (thmJ h1 (equalityTermP (functionTyP a b) f g)))
    (arguments : OpenDerivation definition context (thmJ h2 (equalityTermP a x y)))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    openJudgmentWeight (openMkCombRule calculus valid functions arguments union) =
      weight (thmJ h (equalityTermP b (appTermP f x) (appTermP g y))) + 1 +
        (openJudgmentWeight functions + (openJudgmentWeight arguments + openJudgmentWeight union)) := by
  unfold openMkCombRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openAbsRule_weight {h a s t x b s2 t2 : Pattern} (valid : ∀ argument ∈ [h, a, s, t, x, b, s2, t2], Valid argument)
    (input : OpenDerivation definition context (thmJ h (equalityTermP a s t)))
    (named : OpenDerivation definition context (wfJ "Name" x))
    (typedBinder : OpenDerivation definition context (wfJ "Ty" b))
    (fresh : OpenDerivation definition context (notFreeAllJ (freeTermP x b) h))
    (leftClosed : OpenDerivation definition context (closeJ (freeTermP x b) unaryZeroP s s2))
    (rightClosed : OpenDerivation definition context (closeJ (freeTermP x b) unaryZeroP t t2)) :
    openJudgmentWeight (openAbsRule calculus valid input named typedBinder fresh leftClosed rightClosed) =
      weight (thmJ h (equalityTermP (functionTyP b a) (absTermP b s2) (absTermP b t2))) + 1 +
        (openJudgmentWeight input + (openJudgmentWeight named + (openJudgmentWeight typedBinder +
          (openJudgmentWeight fresh + (openJudgmentWeight leftClosed + openJudgmentWeight rightClosed))))) := by
  unfold openAbsRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openBetaRule_weight {x a t body u reduced : Pattern}
    (valid : ∀ argument ∈ [x, a, t, body, u, reduced], Valid argument)
    (converted : OpenDerivation definition context (toDBJ nilP (sourceAppP (sourceAbsP x a t) (sourceVarP x a))
      (appTermP (absTermP a body) (freeTermP x a))))
    (typed : OpenDerivation definition context (typeOfJ nilP (appTermP (absTermP a body) (freeTermP x a)) u))
    (instantiated : OpenDerivation definition context (instantiateJ (freeTermP x a) unaryZeroP body reduced)) :
    openJudgmentWeight (openBetaRule calculus valid converted typed instantiated) =
      weight (thmJ nilP (equalityTermP u (appTermP (absTermP a body) (freeTermP x a)) reduced)) + 1 +
        (openJudgmentWeight converted + (openJudgmentWeight typed + openJudgmentWeight instantiated)) := by
  unfold openBetaRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openEqMpRule_weight {h1 h2 h a p q : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, p, q], Valid argument)
    (equality : OpenDerivation definition context (thmJ h1 (equalityTermP a p q)))
    (premise : OpenDerivation definition context (thmJ h2 p))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    openJudgmentWeight (openEqMpRule calculus valid equality premise union) =
      weight (thmJ h q) + 1 + (openJudgmentWeight equality + (openJudgmentWeight premise + openJudgmentWeight union)) := by
  unfold openEqMpRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openDeductAntisymRule_weight {h1 h2 k1 k2 h p q a : Pattern}
    (valid : ∀ argument ∈ [h1, h2, k1, k2, h, p, q, a], Valid argument)
    (left : OpenDerivation definition context (thmJ h1 p)) (right : OpenDerivation definition context (thmJ h2 q))
    (leftTyped : OpenDerivation definition context (typeOfJ nilP p a))
    (rightTyped : OpenDerivation definition context (typeOfJ nilP q a))
    (leftErase : OpenDerivation definition context (eraseJ q h1 k1))
    (rightErase : OpenDerivation definition context (eraseJ p h2 k2))
    (union : OpenDerivation definition context (unionJ k1 k2 h)) :
    openJudgmentWeight (openDeductAntisymRule calculus valid left right leftTyped rightTyped leftErase rightErase union) =
      weight (thmJ h (equalityTermP a p q)) + 1 +
        (openJudgmentWeight left + (openJudgmentWeight right + (openJudgmentWeight leftTyped +
          (openJudgmentWeight rightTyped + (openJudgmentWeight leftErase + (openJudgmentWeight rightErase +
            openJudgmentWeight union)))))) := by
  unfold openDeductAntisymRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openInstRule_weight {h c ms table h1 h2 c2 : Pattern}
    (valid : ∀ argument ∈ [h, c, ms, table, h1, h2, c2], Valid argument)
    (input : OpenDerivation definition context (thmJ h c))
    (admitted : OpenDerivation definition context (admitTmJ ms table))
    (hypotheses : OpenDerivation definition context (tmApplyListJ table h h1))
    (sorted : OpenDerivation definition context (sortJ h1 h2))
    (concluded : OpenDerivation definition context (tmApplyJ table c c2)) :
    openJudgmentWeight (openInstRule calculus valid input admitted hypotheses sorted concluded) =
      weight (thmJ h2 c2) + 1 + (openJudgmentWeight input + (openJudgmentWeight admitted +
        (openJudgmentWeight hypotheses + (openJudgmentWeight sorted + openJudgmentWeight concluded)))) := by
  unfold openInstRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

theorem openInstTypeRule_weight {h c es h1 h2 c2 : Pattern} (valid : ∀ argument ∈ [h, c, es, h1, h2, c2], Valid argument)
    (input : OpenDerivation definition context (thmJ h c))
    (entries : OpenDerivation definition context (wfJ "TypeMaplets" es))
    (hypotheses : OpenDerivation definition context (termTyActListJ es h h1))
    (sorted : OpenDerivation definition context (sortJ h1 h2))
    (concluded : OpenDerivation definition context (termTyActJ es c c2)) :
    openJudgmentWeight (openInstTypeRule calculus valid input entries hypotheses sorted concluded) =
      weight (thmJ h2 c2) + 1 + (openJudgmentWeight input + (openJudgmentWeight entries +
        (openJudgmentWeight hypotheses + (openJudgmentWeight sorted + openJudgmentWeight concluded)))) := by
  unfold openInstTypeRule fireOpenAt
  rw [openJudgmentWeight]
  simp only [openJudgmentWeights_cons, openJudgmentWeights_nil, Nat.add_zero]

/-! ## The judgments of the cores -/

theorem reflCore_weight (term : CanonicalTerm) :
    openJudgmentWeight (reflCore calculus (context := context) term) =
      weight (thmJ nilP (equalityTermP (groundP (encodeTy term.ty)) (groundP (encodeTerm term.term))
        (groundP (encodeTerm term.term)))) + 1 +
      judgmentWeight (deriveTypeOf calculus [] term.term term.ty term.checked) := by
  unfold reflCore
  rw [openReflRule_weight]
  erw [openJudgmentWeight_ofClosed]
  rfl

theorem assumeCore_weight (term : CanonicalTerm) (isBool : term.ty = Ty.bool) :
    openJudgmentWeight (assumeCore calculus (context := context) term isBool) =
      weight (thmJ (consP (groundP (encodeTerm term.term)) nilP) (groundP (encodeTerm term.term))) + 1 +
      judgmentWeight (deriveTypeOf calculus [] term.term Ty.bool (by rw [term.checked, isBool])) := by
  unfold assumeCore
  rw [openAssumeRule_weight]
  erw [openJudgmentWeight_ofClosed]
  rfl

theorem transCore_weight (left right : Theorem)
    (leftShape : left.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqLeft left.sequent.concl.term) (eqRight left.sequent.concl.term))
    (rightShape : right.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqRight left.sequent.concl.term) (eqRight right.sequent.concl.term))
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    openJudgmentWeight (transCore calculus left right leftShape rightShape leftDerived rightDerived) =
      weight (thmJ (treesP (treeUnion (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)))
        (equalityTermP (groundP (encodeTy (eqOperand left.sequent.concl.term)))
          (groundP (encodeTerm (eqLeft left.sequent.concl.term)))
          (groundP (encodeTerm (eqRight right.sequent.concl.term))))) + 1 +
      (openJudgmentWeight leftDerived + (openJudgmentWeight rightDerived +
        judgmentWeight (deriveUnion calculus (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)))) := by
  unfold transCore
  rw [openTransRule_weight, openJudgmentWeight_asThmOpen, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed]

theorem mkCombCore_weight (functions arguments : Theorem)
    (functionShape : functions.sequent.concl.term = CanonicalTerm.equalityDB
      (Ty.function (domainOf (eqOperand functions.sequent.concl.term))
        (codomainOf (eqOperand functions.sequent.concl.term)))
      (eqLeft functions.sequent.concl.term) (eqRight functions.sequent.concl.term))
    (argumentShape : arguments.sequent.concl.term = CanonicalTerm.equalityDB
      (domainOf (eqOperand functions.sequent.concl.term))
      (eqLeft arguments.sequent.concl.term) (eqRight arguments.sequent.concl.term))
    (functionsDerived : OpenDerivation definition context (sequentJ functions.sequent))
    (argumentsDerived : OpenDerivation definition context (sequentJ arguments.sequent)) :
    openJudgmentWeight (mkCombCore calculus functions arguments functionShape argumentShape functionsDerived
        argumentsDerived) =
      weight (thmJ (treesP (treeUnion (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp)))
        (equalityTermP (groundP (encodeTy (codomainOf (eqOperand functions.sequent.concl.term))))
          (appTermP (groundP (encodeTerm (eqLeft functions.sequent.concl.term)))
            (groundP (encodeTerm (eqLeft arguments.sequent.concl.term))))
          (appTermP (groundP (encodeTerm (eqRight functions.sequent.concl.term)))
            (groundP (encodeTerm (eqRight arguments.sequent.concl.term)))))) + 1 +
      (openJudgmentWeight functionsDerived + (openJudgmentWeight argumentsDerived +
        judgmentWeight (deriveUnion calculus (hypothesisTrees functions.sequent.hyp)
          (hypothesisTrees arguments.sequent.hyp)))) := by
  unfold mkCombCore
  rw [openMkCombRule_weight, openJudgmentWeight_asThmOpen, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed]

theorem eqMpCore_weight (equality premise : Theorem)
    (equalityShape : equality.sequent.concl.term = CanonicalTerm.equalityDB
      (eqOperand equality.sequent.concl.term) (eqLeft equality.sequent.concl.term)
      (eqRight equality.sequent.concl.term))
    (premiseShape : premise.sequent.concl.term = eqLeft equality.sequent.concl.term)
    (equalityDerived : OpenDerivation definition context (sequentJ equality.sequent))
    (premiseDerived : OpenDerivation definition context (sequentJ premise.sequent)) :
    openJudgmentWeight (eqMpCore calculus equality premise equalityShape premiseShape equalityDerived premiseDerived) =
      weight (thmJ (treesP (treeUnion (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp)))
        (groundP (encodeTerm (eqRight equality.sequent.concl.term)))) + 1 +
      (openJudgmentWeight equalityDerived + (openJudgmentWeight premiseDerived +
        judgmentWeight (deriveUnion calculus (hypothesisTrees equality.sequent.hyp)
          (hypothesisTrees premise.sequent.hyp)))) := by
  unfold eqMpCore
  rw [openEqMpRule_weight, openJudgmentWeight_asThmOpen, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed]

theorem deductAntisymCore_weight (left right : Theorem) (types : left.sequent.concl.ty = right.sequent.concl.ty)
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    openJudgmentWeight (deductAntisymCore calculus left right types leftDerived rightDerived) =
      weight (thmJ (treesP (treeUnion (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
          (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))))
        (equalityTermP (groundP (encodeTy left.sequent.concl.ty)) (groundP (encodeTerm left.sequent.concl.term))
          (groundP (encodeTerm right.sequent.concl.term)))) + 1 +
      (openJudgmentWeight leftDerived + (openJudgmentWeight rightDerived +
        (judgmentWeight (deriveTypeOf calculus [] left.sequent.concl.term left.sequent.concl.ty
          left.sequent.concl.checked) +
        (judgmentWeight (deriveTypeOf calculus [] right.sequent.concl.term right.sequent.concl.ty
          right.sequent.concl.checked) +
        (judgmentWeight (deriveErase calculus (encodeCanonical right.sequent.concl) (hypothesisTrees left.sequent.hyp)) +
        (judgmentWeight (deriveErase calculus (encodeCanonical left.sequent.concl) (hypothesisTrees right.sequent.hyp)) +
          judgmentWeight (deriveUnion calculus (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
            (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))))))))) := by
  unfold deductAntisymCore
  rw [openDeductAntisymRule_weight, openJudgmentWeight_asThmOpen, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed,
    openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed]
  erw [judgmentWeight_recast, judgmentWeight_recast, judgmentWeight_recast]
  rfl

theorem absCore_weight (binder : SourceVar) (input : Theorem)
    (inputShape : input.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand input.sequent.concl.term)
      (eqLeft input.sequent.concl.term) (eqRight input.sequent.concl.term))
    (absent : ∀ term ∈ (sortedHypotheses input.sequent.hyp).map CanonicalTerm.term,
      DBTerm.hasFree binder term = false)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    openJudgmentWeight (absCore calculus binder input inputShape absent inputDerived) =
      weight (thmJ (sequentHypothesesP input.sequent)
        (equalityTermP (functionTyP (groundP (encodeTy binder.ty)) (groundP (encodeTy (eqOperand input.sequent.concl.term))))
          (absTermP (groundP (encodeTy binder.ty))
            (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqLeft input.sequent.concl.term)))))
          (absTermP (groundP (encodeTy binder.ty))
            (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqRight input.sequent.concl.term))))))) + 1 +
      (openJudgmentWeight inputDerived + (judgmentWeight (deriveName calculus binder.name) +
        (judgmentWeight (deriveTy calculus binder.ty) +
        (judgmentWeight (deriveNotFreeAll calculus binder _ absent) +
        (judgmentWeight (deriveClose calculus binder 0 (eqLeft input.sequent.concl.term)) +
          judgmentWeight (deriveClose calculus binder 0 (eqRight input.sequent.concl.term))))))) := by
  unfold absCore
  rw [openAbsRule_weight, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed,
    openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed]
  erw [judgmentWeight_recast (derivation := deriveNotFreeAll calculus binder _ absent)]
  rfl

theorem betaCore_weight (source : CheckedSourceTerm) (name : Name) (type : Ty) (bodySource : SourceTerm)
    (sourceShape : source.source = .app (.abs name type bodySource) (.var name type))
    (checked : (source.source.toDB []).inferType [] = some source.ty) :
    openJudgmentWeight (betaCore calculus (context := context) source name type bodySource sourceShape) =
      weight (thmJ nilP (equalityTermP (groundP (encodeTy source.ty))
        (appTermP (absTermP (groundP (encodeTy type)) (groundP (encodeTerm (bodySource.toDB [⟨name, type⟩]))))
          (freeTermP (groundP (encodeName name)) (groundP (encodeTy type))))
        (groundP (encodeTerm (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])))))) + 1 +
      (judgmentWeight (deriveToDB calculus [] source.source) +
        (judgmentWeight (deriveTypeOf calculus [] _ source.ty checked) +
          judgmentWeight (deriveInstantiate calculus (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])))) := by
  unfold betaCore
  dsimp only
  rw [openBetaRule_weight]
  erw [openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed]
  erw [judgmentWeight_recast, judgmentWeight_recast]
  rfl

theorem instCore_weight (maplets : List SourceSubstitution.TermMaplet) (input : Theorem)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    openJudgmentWeight (instCore calculus maplets input admissible inputDerived) =
      weight (thmJ (treesP (actedHypotheses (tableAction (SourceSubstitution.termEntries maplets)) input))
        (groundP (encodeTerm (tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term)))) + 1 +
      (openJudgmentWeight inputDerived + (judgmentWeight (deriveAdmit calculus maplets admissible) +
        (judgmentWeight (deriveTmApplyList calculus (SourceSubstitution.termEntries maplets)
          ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)) +
        (judgmentWeight (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
          (tableAction (SourceSubstitution.termEntries maplets))).map encodeTerm)) +
          judgmentWeight (deriveTmApply calculus (SourceSubstitution.termEntries maplets) input.sequent.concl.term))))) := by
  unfold instCore
  rw [openInstRule_weight, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed,
    openJudgmentWeight_ofClosed]
  erw [judgmentWeight_recast]

theorem instTypeCore_weight (entries : List (Ty × Ty)) (input : Theorem)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    openJudgmentWeight (instTypeCore calculus entries input inputDerived) =
      weight (thmJ (treesP (actedHypotheses (termTypeAction entries) input))
        (groundP (encodeTerm (termTypeAction entries input.sequent.concl.term)))) + 1 +
      (openJudgmentWeight inputDerived + (judgmentWeight (deriveTypeMaplets calculus entries) +
        (judgmentWeight (deriveTermTyActList calculus entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)) +
        (judgmentWeight (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
          (termTypeAction entries)).map encodeTerm)) +
          judgmentWeight (deriveTermTyAct calculus entries input.sequent.concl.term))))) := by
  unfold instTypeCore
  rw [openInstTypeRule_weight, openJudgmentWeight_asThmOpen]
  erw [openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed, openJudgmentWeight_ofClosed,
    openJudgmentWeight_ofClosed]
  erw [judgmentWeight_recast]

theorem axiomCore_weight (sequent : Sequent) (member : sequent ∈ axioms) :
    openJudgmentWeight (axiomCore calculus (context := context) sequent member) = weight (sequentJ sequent) + 1 := by
  unfold axiomCore
  dsimp only
  erw [openJudgmentWeight_ofClosed]
  unfold fireAt fire
  rw [judgmentWeight_recast, judgmentWeight]
  rw [show substSchema (ruleValues (rule ("hol.axiom-" ++ toString (axioms.idxOf sequent)) [] [] (sequentJ sequent)) [])
      (rule ("hol.axiom-" ++ toString (axioms.idxOf sequent)) [] [] (sequentJ sequent)).conclusion = sequentJ sequent from
    by simp only [rule]; exact substSchema_sequentJ _ _]
  rfl

/-! ## Closed builders as envelopes -/

theorem judgmentWeight_le_of {goal : Pattern} (derivation : Derivation definition goal) {count heaviest : ℕ}
    (counted : nodeCount derivation ≤ count) (weighed : maxJudgment derivation ≤ heaviest) :
    judgmentWeight derivation ≤ count * (heaviest + 1) :=
  le_trans (judgmentWeight_le derivation) (Nat.mul_le_mul counted (Nat.add_le_add_right weighed 1))

theorem weight_boolP : weight boolP = 6465 := by decide +kernel

theorem weight_equalityConstP : weight equalityConstP = 2022 := by decide +kernel

theorem weight_unaryZero : weight (groundP (encodeUnary 0)) = 306 := by
  rw [weight_encodeUnary]

/-! Each builder's judgments, as a polynomial in a measure `X` of its data. -/

include calculus in
theorem typeOf_within {size factor degree : ℕ} (term : DBTerm) (type : Ty) (typed : term.inferType [] = some type)
    (measured : Within size factor degree (weight (groundP (encodeTerm term)))) :
    Within size ((factor + 1) * (factor + 10) * (40 * factor + 761)) (degree + degree + degree)
      (judgmentWeight (deriveTypeOf calculus [] term type typed)) := by
  have counted := deriveTypeOf_count calculus [] term type typed
  have weighed := deriveTypeOf_max calculus [] term type typed
  rw [weight_contextP_nil] at counted weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTypeOf calculus [] term type typed) ≤
      (weight (groundP (encodeTerm term)) + 1) * (weight (groundP (encodeTerm term)) + 10) *
        (40 * weight (groundP (encodeTerm term)) + 761) := by
    refine le_trans bound (le_of_eq ?_)
    ring
  exact (((measured.add_const 1).mul (measured.add_const 10)).mul ((measured.scale 40).add_const 761)).le_of shaped

include calculus in
theorem union_within {size factor degree : ℕ} (firsts seconds : List LabeledTree)
    (measured : Within size factor degree (weight (treesP firsts) + weight (treesP seconds))) :
    Within size (factor * factor * (2 * factor + 14)) (degree + degree + degree)
      (judgmentWeight (deriveUnion calculus firsts seconds)) := by
  have counted := deriveUnion_count calculus firsts seconds
  have weighed := deriveUnion_max calculus firsts seconds
  have unioned := weight_treeUnion firsts seconds
  rw [weight_unionJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveUnion calculus firsts seconds) ≤
      (weight (treesP firsts) + weight (treesP seconds)) * (weight (treesP firsts) + weight (treesP seconds)) *
        (2 * (weight (treesP firsts) + weight (treesP seconds)) + 14) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  exact ((measured.mul measured).mul ((measured.scale 2).add_const 14)).le_of shaped

include calculus in
theorem erase_within {size factor degree : ℕ} (tree : LabeledTree) (trees : List LabeledTree)
    (measured : Within size factor degree (weight (groundP tree) + weight (treesP trees))) :
    Within size (factor * (factor + 2) * (2 * factor + 14)) (degree + degree + degree)
      (judgmentWeight (deriveErase calculus tree trees)) := by
  have counted := deriveErase_count calculus tree trees
  have weighed := deriveErase_max calculus tree trees
  have erased := weight_treeErase tree trees
  rw [weight_eraseJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveErase calculus tree trees) ≤
      (weight (groundP tree) + weight (treesP trees)) * (weight (groundP tree) + weight (treesP trees) + 2) *
        (2 * (weight (groundP tree) + weight (treesP trees)) + 14) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by omega))
  exact ((measured.mul (measured.add_const 2)).mul ((measured.scale 2).add_const 14)).le_of shaped

include calculus in
theorem name_within {size factor degree : ℕ} (name : Name)
    (measured : Within size factor degree (weight (groundP (encodeName name)))) :
    Within size (factor * (factor + 13)) (degree + degree) (judgmentWeight (deriveName calculus name)) := by
  have counted := deriveName_count calculus name
  have weighed := le_of_eq (deriveName_max calculus name)
  rw [weight_wfJ, show "Name".length = 4 from rfl] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveName calculus name) ≤
      weight (groundP (encodeName name)) * (weight (groundP (encodeName name)) + 13) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  exact (measured.mul (measured.add_const 13)).le_of shaped

include calculus in
theorem ty_within {size factor degree : ℕ} (type : Ty)
    (measured : Within size factor degree (weight (groundP (encodeTy type)))) :
    Within size (factor * (factor + 11)) (degree + degree) (judgmentWeight (deriveTy calculus type)) := by
  have counted := deriveTy_count calculus type
  have weighed := le_of_eq (deriveTy_max calculus type)
  rw [weight_wfJ, show "Ty".length = 2 from rfl] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTy calculus type) ≤
      weight (groundP (encodeTy type)) * (weight (groundP (encodeTy type)) + 11) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  exact (measured.mul (measured.add_const 11)).le_of shaped

include calculus in
theorem notFreeAll_within {size factor degree : ℕ} (needle : SourceVar) (terms : List DBTerm)
    (absent : ∀ term ∈ terms, DBTerm.hasFree needle term = false)
    (measured : Within size factor degree (weight (termsP terms) + weight (freeVarP needle))) :
    Within size (factor * (factor + 2) * (factor + 18)) (degree + degree + degree)
      (judgmentWeight (deriveNotFreeAll calculus needle terms absent)) := by
  have counted := deriveNotFreeAll_count calculus needle terms absent
  have weighed := deriveNotFreeAll_max calculus needle terms absent
  rw [weight_notFreeAllJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveNotFreeAll calculus needle terms absent) ≤
      (weight (termsP terms) + weight (freeVarP needle)) * (weight (termsP terms) + weight (freeVarP needle) + 2) *
        (weight (termsP terms) + weight (freeVarP needle) + 18) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by omega))
  exact ((measured.mul (measured.add_const 2)).mul (measured.add_const 18)).le_of shaped

include calculus in
theorem close_within {size factor degree : ℕ} (needle : SourceVar) (term : DBTerm)
    (measured : Within size factor degree (weight (groundP (encodeTerm term)) + weight (freeVarP needle))) :
    Within size (factor * (factor + 2) * (factor * (factor + 4) + 321)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveClose calculus needle 0 term)) := by
  have counted := deriveClose_count calculus needle 0 term
  have weighed := deriveClose_max calculus needle 0 term
  have closed := weight_closeFreeAt needle 0 term
  rw [weight_closeJ, weight_unaryZero] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveClose calculus needle 0 term) ≤
      (weight (groundP (encodeTerm term)) + weight (freeVarP needle)) *
        (weight (groundP (encodeTerm term)) + weight (freeVarP needle) + 2) *
        ((weight (groundP (encodeTerm term)) + weight (freeVarP needle)) *
          (weight (groundP (encodeTerm term)) + weight (freeVarP needle) + 4) + 321) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul (measured.add_const 2)).mul ((measured.mul (measured.add_const 4)).add_const 321)).le_of shaped

include calculus in
theorem instantiate_within {size factor degree : ℕ} (replacement term : DBTerm)
    (measured : Within size factor degree (weight (groundP (encodeTerm term)) + weight (groundP (encodeTerm replacement)))) :
    Within size (factor * (factor + 308) * (factor * (factor + 2) + 327)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveInstantiate calculus replacement 0 term)) := by
  have counted := deriveInstantiate_count calculus replacement 0 term
  have weighed := deriveInstantiate_max calculus replacement 0 term
  have instantiated := weight_instantiateAt replacement 0 term
  rw [weight_instantiateJ, weight_unaryZero] at weighed
  rw [weight_unaryZero] at counted
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveInstantiate calculus replacement 0 term) ≤
      (weight (groundP (encodeTerm term)) + weight (groundP (encodeTerm replacement))) *
        (weight (groundP (encodeTerm term)) + weight (groundP (encodeTerm replacement)) + 308) *
        ((weight (groundP (encodeTerm term)) + weight (groundP (encodeTerm replacement))) *
          (weight (groundP (encodeTerm term)) + weight (groundP (encodeTerm replacement)) + 2) + 327) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul (measured.add_const 308)).mul ((measured.mul (measured.add_const 2)).add_const 327)).le_of shaped

include calculus in
theorem toDB_within {size factor degree : ℕ} (source : SourceTerm)
    (measured : Within size factor degree (weight (groundP (encodeSourceTerm source)))) :
    Within size (2 * (factor + 1) * (2 * factor + 11) * (4 * ((2 * factor + 11) * (2 * factor + 11)) + 1))
      (degree + degree + (degree + degree)) (judgmentWeight (deriveToDB calculus [] source)) := by
  have counted := deriveToDB_count calculus [] source
  have weighed := deriveToDB_max calculus [] source
  rw [weight_bindersP_nil] at counted weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveToDB calculus [] source) ≤
      2 * (weight (groundP (encodeSourceTerm source)) + 1) * (2 * weight (groundP (encodeSourceTerm source)) + 11) *
        (4 * ((2 * weight (groundP (encodeSourceTerm source)) + 11) *
          (2 * weight (groundP (encodeSourceTerm source)) + 11)) + 1) := by
    refine le_trans bound (le_of_eq ?_)
    ring
  exact ((((measured.add_const 1).scale 2).mul ((measured.scale 2).add_const 11)).mul
    (((((measured.scale 2).add_const 11).mul ((measured.scale 2).add_const 11)).scale 4).add_const 1)).le_of shaped

include calculus in
theorem sort_within {size factor degree : ℕ} (trees : List LabeledTree)
    (measured : Within size factor degree (weight (treesP trees))) :
    Within size (factor * factor * (2 * factor + 12)) (degree + degree + degree)
      (judgmentWeight (deriveSort calculus trees)) := by
  have counted := deriveSort_count calculus trees
  have weighed := deriveSort_max calculus trees
  have sorted := weight_treeSort trees
  rw [weight_sortJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveSort calculus trees) ≤
      weight (treesP trees) * weight (treesP trees) * (2 * weight (treesP trees) + 12) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  exact ((measured.mul measured).mul ((measured.scale 2).add_const 12)).le_of shaped

include calculus in
theorem typeMaplets_within {size factor degree : ℕ} (entries : List (Ty × Ty))
    (measured : Within size factor degree (weight (typeMapletsP entries))) :
    Within size (factor * (factor + 20)) (degree + degree) (judgmentWeight (deriveTypeMaplets calculus entries)) := by
  have counted := deriveTypeMaplets_count calculus entries
  have weighed := le_of_eq (deriveTypeMaplets_max calculus entries)
  rw [weight_wfJ, show "TypeMaplets".length = 11 from rfl] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTypeMaplets calculus entries) ≤
      weight (typeMapletsP entries) * (weight (typeMapletsP entries) + 20) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  exact (measured.mul (measured.add_const 20)).le_of shaped

include calculus in
theorem termTyActList_within {size factor degree : ℕ} (entries : List (Ty × Ty)) (terms : List DBTerm)
    (measured : Within size factor degree (weight (termsP terms) + weight (typeMapletsP entries))) :
    Within size (factor * (factor + 2) * (factor * (factor + 2) + 22)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveTermTyActList calculus entries terms)) := by
  have counted := deriveTermTyActList_count calculus entries terms
  have weighed := deriveTermTyActList_max calculus entries terms
  have acted := weight_termTypeActionList entries terms
  rw [weight_termTyActListJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTermTyActList calculus entries terms) ≤
      (weight (termsP terms) + weight (typeMapletsP entries)) *
        (weight (termsP terms) + weight (typeMapletsP entries) + 2) *
        ((weight (termsP terms) + weight (typeMapletsP entries)) *
          (weight (termsP terms) + weight (typeMapletsP entries) + 2) + 22) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul (measured.add_const 2)).mul ((measured.mul (measured.add_const 2)).add_const 22)).le_of shaped

include calculus in
theorem termTyAct_within {size factor degree : ℕ} (entries : List (Ty × Ty)) (term : DBTerm)
    (measured : Within size factor degree (weight (groundP (encodeTerm term)) + weight (typeMapletsP entries))) :
    Within size (factor * (factor + 2) * (factor * (factor + 2) + 18)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveTermTyAct calculus entries term)) := by
  have counted := deriveTermTyAct_count calculus entries term
  have weighed := deriveTermTyAct_max calculus entries term
  have acted := weight_termTypeAction entries term
  rw [weight_termTyActJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTermTyAct calculus entries term) ≤
      (weight (groundP (encodeTerm term)) + weight (typeMapletsP entries)) *
        (weight (groundP (encodeTerm term)) + weight (typeMapletsP entries) + 2) *
        ((weight (groundP (encodeTerm term)) + weight (typeMapletsP entries)) *
          (weight (groundP (encodeTerm term)) + weight (typeMapletsP entries) + 2) + 18) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul (measured.add_const 2)).mul ((measured.mul (measured.add_const 2)).add_const 18)).le_of shaped

include calculus in
theorem tmApplyList_within {size factor degree : ℕ} (entries : List (SourceVar × CheckedSourceTerm))
    (terms : List DBTerm) (measured : Within size factor degree (weight (termsP terms) + weight (tableP entries))) :
    Within size (factor * (2 * factor + 2) * (factor * (factor + 2) + 20)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveTmApplyList calculus entries terms)) := by
  have counted := deriveTmApplyList_count calculus entries terms
  have weighed := deriveTmApplyList_max calculus entries terms
  have acted := weight_tableActionList entries terms
  rw [weight_tmApplyListJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTmApplyList calculus entries terms) ≤
      (weight (termsP terms) + weight (tableP entries)) * (2 * (weight (termsP terms) + weight (tableP entries)) + 2) *
        ((weight (termsP terms) + weight (tableP entries)) *
          (weight (termsP terms) + weight (tableP entries) + 2) + 20) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul ((measured.scale 2).add_const 2)).mul
    ((measured.mul (measured.add_const 2)).add_const 20)).le_of shaped

include calculus in
theorem tmApply_within {size factor degree : ℕ} (entries : List (SourceVar × CheckedSourceTerm)) (term : DBTerm)
    (measured : Within size factor degree (weight (groundP (encodeTerm term)) + weight (tableP entries))) :
    Within size (factor * (2 * factor + 2) * (factor * (factor + 2) + 17)) (degree + degree + (degree + degree))
      (judgmentWeight (deriveTmApply calculus entries term)) := by
  have counted := deriveTmApply_count calculus entries term
  have weighed := deriveTmApply_max calculus entries term
  have acted := weight_tableAction entries term
  rw [weight_tmApplyJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveTmApply calculus entries term) ≤
      (weight (groundP (encodeTerm term)) + weight (tableP entries)) *
        (2 * (weight (groundP (encodeTerm term)) + weight (tableP entries)) + 2) *
        ((weight (groundP (encodeTerm term)) + weight (tableP entries)) *
          (weight (groundP (encodeTerm term)) + weight (tableP entries) + 2) + 17) :=
    le_trans bound (Nat.mul_le_mul (by nlinarith) (by nlinarith))
  exact ((measured.mul ((measured.scale 2).add_const 2)).mul
    ((measured.mul (measured.add_const 2)).add_const 17)).le_of shaped

/-! ## Facts about rendered sequents -/

theorem hypotheses_le_sequentJ (sequent : Sequent) :
    weight (treesP (hypothesisTrees sequent.hyp)) + 10 ≤ weight (sequentJ sequent) := by
  rw [weight_sequentJ]
  omega

theorem conclusion_le_sequentJ (sequent : Sequent) :
    weight (groundP (encodeTerm sequent.concl.term)) + 10 ≤ weight (sequentJ sequent) := by
  rw [weight_sequentJ]
  omega

theorem weight_termsP_sortedHypotheses (sequent : Sequent) :
    weight (termsP ((sortedHypotheses sequent.hyp).map CanonicalTerm.term)) = weight (treesP (hypothesisTrees sequent.hyp)) := by
  rw [← sequentHypothesesP_eq_termsP, sequentHypothesesP_eq_treesP]

theorem weight_type_le (term : CanonicalTerm) :
    weight (groundP (encodeTy term.ty)) ≤ 20 * weight (groundP (encodeTerm term.term)) + 9 := by
  have inferred := weight_inferType [] term.term term.ty term.checked
  rw [weight_contextP_nil] at inferred
  exact inferred

/-! ## The cores within their requests -/

theorem reflCore_within (term : CanonicalTerm) :
    Within (requestSize (.inference (.refl term))) 40000 3 (openJudgmentWeight (reflCore calculus (context := context) term)) := by
  rw [reflCore_weight]
  have sized : requestSize (.inference (.refl term)) =
      weight (groundP (encodeTerm term.term)) + weight (groundP (encodeTy term.ty)) := rfl
  have root : weight (thmJ nilP (equalityTermP (groundP (encodeTy term.ty)) (groundP (encodeTerm term.term))
      (groundP (encodeTerm term.term)))) ≤ 2 * requestSize (.inference (.refl term)) + 16639 := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, weight_nilP, sized]
    omega
  have typed := typeOf_within calculus term.term term.ty term.checked
    (Within.of_le (size := requestSize (.inference (.refl term))) (by omega))
  exact ((((((Within.of_le le_rfl).scale 2).add_const 16639).le_of root).add_const 1).add typed).raise
    (by norm_num) (by norm_num)

theorem assumeCore_within (term : CanonicalTerm) (isBool : term.ty = Ty.bool) :
    Within (requestSize (.inference (.assume term))) 40000 3
      (openJudgmentWeight (assumeCore calculus (context := context) term isBool)) := by
  rw [assumeCore_weight]
  have sized : requestSize (.inference (.assume term)) =
      weight (groundP (encodeTerm term.term)) + weight (groundP (encodeTy term.ty)) := rfl
  have root : weight (thmJ (consP (groundP (encodeTerm term.term)) nilP) (groundP (encodeTerm term.term))) ≤
      2 * requestSize (.inference (.assume term)) + 31 := by
    rw [weight_thmJ, weight_consP, weight_nilP, sized]
    omega
  have typed := typeOf_within calculus term.term Ty.bool (by rw [term.checked, isBool])
    (Within.of_le (size := requestSize (.inference (.assume term))) (by omega))
  exact ((((((Within.of_le le_rfl).scale 2).add_const 31).le_of root).add_const 1).add typed).raise
    (by norm_num) (by norm_num)

theorem transCore_within (left right : Theorem)
    (leftShape : left.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqLeft left.sequent.concl.term) (eqRight left.sequent.concl.term))
    (rightShape : right.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqRight left.sequent.concl.term) (eqRight right.sequent.concl.term))
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent))
    (leftWeight : openJudgmentWeight leftDerived = weight (sequentJ left.sequent) + 1)
    (rightWeight : openJudgmentWeight rightDerived = weight (sequentJ right.sequent) + 1) :
    Within (requestSize (.inference (.trans left right))) 40000 3
      (openJudgmentWeight (transCore calculus left right leftShape rightShape leftDerived rightDerived)) := by
  rw [transCore_weight, leftWeight, rightWeight]
  have sized : requestSize (.inference (.trans left right)) =
      weight (sequentJ left.sequent) + weight (sequentJ right.sequent) := rfl
  have leftParts := hypotheses_le_sequentJ left.sequent
  have rightParts := hypotheses_le_sequentJ right.sequent
  have leftConcl := conclusion_le_sequentJ left.sequent
  have rightConcl := conclusion_le_sequentJ right.sequent
  have unioned := weight_treeUnion (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)
  have operand := weight_eqOperand_le left.sequent.concl.term
  have leftSide := weight_eqLeft_le left.sequent.concl.term
  have rightSide := weight_eqRight_le right.sequent.concl.term
  have root : weight (thmJ (treesP (treeUnion (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)))
      (equalityTermP (groundP (encodeTy (eqOperand left.sequent.concl.term)))
        (groundP (encodeTerm (eqLeft left.sequent.concl.term)))
        (groundP (encodeTerm (eqRight right.sequent.concl.term))))) ≤
      5 * requestSize (.inference (.trans left right)) + 29560 := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, sized]
    rw [weight_boolP] at operand
    omega
  have union := union_within calculus (size := requestSize (.inference (.trans left right)))
    (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp) (Within.of_le (by omega))
  have leftW : Within (requestSize (.inference (.trans left right))) (1 + 1) 1 (weight (sequentJ left.sequent) + 1) :=
    (Within.of_le (by omega)).add_const 1
  have rightW : Within (requestSize (.inference (.trans left right))) (1 + 1) 1 (weight (sequentJ right.sequent) + 1) :=
    (Within.of_le (by omega)).add_const 1
  exact (((((((Within.of_le le_rfl).scale 5).add_const 29560).le_of root).add_const 1).add
    (leftW.add (rightW.add union))).raise (by norm_num) (by norm_num))

theorem mkCombCore_within (functions arguments : Theorem)
    (functionShape : functions.sequent.concl.term = CanonicalTerm.equalityDB
      (Ty.function (domainOf (eqOperand functions.sequent.concl.term))
        (codomainOf (eqOperand functions.sequent.concl.term)))
      (eqLeft functions.sequent.concl.term) (eqRight functions.sequent.concl.term))
    (argumentShape : arguments.sequent.concl.term = CanonicalTerm.equalityDB
      (domainOf (eqOperand functions.sequent.concl.term))
      (eqLeft arguments.sequent.concl.term) (eqRight arguments.sequent.concl.term))
    (functionsDerived : OpenDerivation definition context (sequentJ functions.sequent))
    (argumentsDerived : OpenDerivation definition context (sequentJ arguments.sequent))
    (functionsWeight : openJudgmentWeight functionsDerived = weight (sequentJ functions.sequent) + 1)
    (argumentsWeight : openJudgmentWeight argumentsDerived = weight (sequentJ arguments.sequent) + 1) :
    Within (requestSize (.inference (.mkComb functions arguments))) 60000 3
      (openJudgmentWeight (mkCombCore calculus functions arguments functionShape argumentShape functionsDerived
        argumentsDerived)) := by
  rw [mkCombCore_weight, functionsWeight, argumentsWeight]
  have sized : requestSize (.inference (.mkComb functions arguments)) =
      weight (sequentJ functions.sequent) + weight (sequentJ arguments.sequent) := rfl
  have leftParts := hypotheses_le_sequentJ functions.sequent
  have rightParts := hypotheses_le_sequentJ arguments.sequent
  have leftConcl := conclusion_le_sequentJ functions.sequent
  have rightConcl := conclusion_le_sequentJ arguments.sequent
  have unioned := weight_treeUnion (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp)
  have operand := weight_eqOperand_le functions.sequent.concl.term
  have codomain := weight_codomainOf_le (eqOperand functions.sequent.concl.term)
  have functionLeft := weight_eqLeft_le functions.sequent.concl.term
  have functionRight := weight_eqRight_le functions.sequent.concl.term
  have argumentLeft := weight_eqLeft_le arguments.sequent.concl.term
  have argumentRight := weight_eqRight_le arguments.sequent.concl.term
  have root : weight (thmJ (treesP (treeUnion (hypothesisTrees functions.sequent.hyp)
        (hypothesisTrees arguments.sequent.hyp)))
      (equalityTermP (groundP (encodeTy (codomainOf (eqOperand functions.sequent.concl.term))))
        (appTermP (groundP (encodeTerm (eqLeft functions.sequent.concl.term)))
          (groundP (encodeTerm (eqLeft arguments.sequent.concl.term))))
        (appTermP (groundP (encodeTerm (eqRight functions.sequent.concl.term)))
          (groundP (encodeTerm (eqRight arguments.sequent.concl.term)))))) ≤
      5 * requestSize (.inference (.mkComb functions arguments)) + 43000 := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, weight_appTermP, weight_appTermP, sized]
    rw [weight_boolP] at operand codomain
    omega
  have union := union_within calculus (size := requestSize (.inference (.mkComb functions arguments)))
    (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp) (Within.of_le (by omega))
  have leftW : Within (requestSize (.inference (.mkComb functions arguments))) (1 + 1) 1
      (weight (sequentJ functions.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  have rightW : Within (requestSize (.inference (.mkComb functions arguments))) (1 + 1) 1
      (weight (sequentJ arguments.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((((((Within.of_le le_rfl).scale 5).add_const 43000).le_of root).add_const 1).add
    (leftW.add (rightW.add union))).raise (by norm_num) (by norm_num))

theorem eqMpCore_within (equality premise : Theorem)
    (equalityShape : equality.sequent.concl.term = CanonicalTerm.equalityDB
      (eqOperand equality.sequent.concl.term) (eqLeft equality.sequent.concl.term)
      (eqRight equality.sequent.concl.term))
    (premiseShape : premise.sequent.concl.term = eqLeft equality.sequent.concl.term)
    (equalityDerived : OpenDerivation definition context (sequentJ equality.sequent))
    (premiseDerived : OpenDerivation definition context (sequentJ premise.sequent))
    (equalityWeight : openJudgmentWeight equalityDerived = weight (sequentJ equality.sequent) + 1)
    (premiseWeight : openJudgmentWeight premiseDerived = weight (sequentJ premise.sequent) + 1) :
    Within (requestSize (.inference (.eqMp equality premise))) 40000 3
      (openJudgmentWeight (eqMpCore calculus equality premise equalityShape premiseShape equalityDerived
        premiseDerived)) := by
  rw [eqMpCore_weight, equalityWeight, premiseWeight]
  have sized : requestSize (.inference (.eqMp equality premise)) =
      weight (sequentJ equality.sequent) + weight (sequentJ premise.sequent) := rfl
  have leftParts := hypotheses_le_sequentJ equality.sequent
  have rightParts := hypotheses_le_sequentJ premise.sequent
  have leftConcl := conclusion_le_sequentJ equality.sequent
  have unioned := weight_treeUnion (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp)
  have rightSide := weight_eqRight_le equality.sequent.concl.term
  have root : weight (thmJ (treesP (treeUnion (hypothesisTrees equality.sequent.hyp)
        (hypothesisTrees premise.sequent.hyp))) (groundP (encodeTerm (eqRight equality.sequent.concl.term)))) ≤
      2 * requestSize (.inference (.eqMp equality premise)) + 10 := by
    rw [weight_thmJ, sized]
    omega
  have union := union_within calculus (size := requestSize (.inference (.eqMp equality premise)))
    (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp) (Within.of_le (by omega))
  have leftW : Within (requestSize (.inference (.eqMp equality premise))) (1 + 1) 1
      (weight (sequentJ equality.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  have rightW : Within (requestSize (.inference (.eqMp equality premise))) (1 + 1) 1
      (weight (sequentJ premise.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((((((Within.of_le le_rfl).scale 2).add_const 10).le_of root).add_const 1).add
    (leftW.add (rightW.add union))).raise (by norm_num) (by norm_num))

theorem deductAntisymCore_within (left right : Theorem) (types : left.sequent.concl.ty = right.sequent.concl.ty)
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent))
    (leftWeight : openJudgmentWeight leftDerived = weight (sequentJ left.sequent) + 1)
    (rightWeight : openJudgmentWeight rightDerived = weight (sequentJ right.sequent) + 1) :
    Within (requestSize (.inference (.deductAntisym left right))) 200000 3
      (openJudgmentWeight (deductAntisymCore calculus left right types leftDerived rightDerived)) := by
  rw [deductAntisymCore_weight, leftWeight, rightWeight]
  have sized : requestSize (.inference (.deductAntisym left right)) =
      weight (sequentJ left.sequent) + weight (sequentJ right.sequent) := rfl
  have leftParts := hypotheses_le_sequentJ left.sequent
  have rightParts := hypotheses_le_sequentJ right.sequent
  have leftConcl := conclusion_le_sequentJ left.sequent
  have rightConcl := conclusion_le_sequentJ right.sequent
  have leftErased := weight_treeErase (encodeCanonical right.sequent.concl) (hypothesisTrees left.sequent.hyp)
  have rightErased := weight_treeErase (encodeCanonical left.sequent.concl) (hypothesisTrees right.sequent.hyp)
  rw [treeErase_hypothesisTrees] at leftErased rightErased
  have unioned := weight_treeUnion (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
    (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))
  have typed := weight_type_le left.sequent.concl
  have root : weight (thmJ (treesP (treeUnion (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
        (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))))
      (equalityTermP (groundP (encodeTy left.sequent.concl.ty)) (groundP (encodeTerm left.sequent.concl.term))
        (groundP (encodeTerm right.sequent.concl.term)))) ≤
      42 * requestSize (.inference (.deductAntisym left right)) + 16650 := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, sized]
    omega
  have encodedRight : weight (groundP (encodeCanonical right.sequent.concl)) =
      weight (groundP (encodeTerm right.sequent.concl.term)) := rfl
  have encodedLeft : weight (groundP (encodeCanonical left.sequent.concl)) =
      weight (groundP (encodeTerm left.sequent.concl.term)) := rfl
  have leftTyped := typeOf_within calculus left.sequent.concl.term left.sequent.concl.ty left.sequent.concl.checked
    (Within.of_le (size := requestSize (.inference (.deductAntisym left right))) (by omega))
  have rightTyped := typeOf_within calculus right.sequent.concl.term right.sequent.concl.ty right.sequent.concl.checked
    (Within.of_le (size := requestSize (.inference (.deductAntisym left right))) (by omega))
  have leftErase := erase_within calculus (size := requestSize (.inference (.deductAntisym left right)))
    (encodeCanonical right.sequent.concl) (hypothesisTrees left.sequent.hyp) (Within.of_le (by omega))
  have rightErase := erase_within calculus (size := requestSize (.inference (.deductAntisym left right)))
    (encodeCanonical left.sequent.concl) (hypothesisTrees right.sequent.hyp) (Within.of_le (by omega))
  have union := union_within calculus (size := requestSize (.inference (.deductAntisym left right)))
    (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
    (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl)) (Within.of_le (by omega))
  have leftW : Within (requestSize (.inference (.deductAntisym left right))) (1 + 1) 1
      (weight (sequentJ left.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  have rightW : Within (requestSize (.inference (.deductAntisym left right))) (1 + 1) 1
      (weight (sequentJ right.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((((((Within.of_le le_rfl).scale 42).add_const 16650).le_of root).add_const 1).add
    (leftW.add (rightW.add (leftTyped.add (rightTyped.add (leftErase.add (rightErase.add union))))))).raise
    (by norm_num) (by norm_num))

/-! ## Admission -/

theorem admitCost_within {size value : ℕ} (small : value ≤ size) : Within size 376 4 (admitCost value) := by
  have shaped : admitCost value =
      (value + 1) + (2 * (value + 1) * (2 * value + 11) +
        ((2 * value + 11) * value + 1) * ((2 * value + 11) * value + 10)) := by
    unfold admitCost
    ring
  have measured := Within.of_le small
  have doubled := (measured.scale 2).add_const 11
  rw [shaped]
  exact ((measured.add_const 1).add ((((measured.add_const 1).scale 2).mul doubled).add
    (((doubled.mul measured).add_const 1).mul ((doubled.mul measured).add_const 10)))).raise
    (by norm_num) (by norm_num)

theorem admitMax_within {size value : ℕ} (small : value ≤ size) : Within size 1997 2 (admitMax value) := by
  have shaped : admitMax value =
      800 + value + (4 * ((2 * value + 11) * (2 * value + 11)) + 40 * ((2 * value + 11) * value)) := by
    unfold admitMax
    ring
  have measured := Within.of_le small
  have doubled := (measured.scale 2).add_const 11
  rw [shaped]
  exact (((Within.const 800).add measured).add (((doubled.mul doubled).scale 4).add ((doubled.mul measured).scale 40))).raise
    (by norm_num) (by norm_num)

theorem admit_within {size : ℕ} (maplets : List SourceSubstitution.TermMaplet)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets) (small : weight (termMapletsP maplets) ≤ size) :
    Within size 1000000 7 (judgmentWeight (deriveAdmit calculus maplets admissible)) := by
  have counted := deriveAdmit_count calculus maplets admissible
  have weighed := deriveAdmit_max calculus maplets admissible
  have table := weight_tableP_termEntries maplets
  rw [weight_admitTmJ] at weighed
  have bound := judgmentWeight_le_of _ counted weighed
  have shaped : judgmentWeight (deriveAdmit calculus maplets admissible) ≤
      (weight (termMapletsP maplets) * admitCost (weight (termMapletsP maplets))) *
        (15 + weight (termMapletsP maplets) +
          weight (termMapletsP maplets) * (2 * weight (termMapletsP maplets) + 12) +
          admitMax (weight (termMapletsP maplets))) :=
    le_trans bound (Nat.mul_le_mul_left _ (by omega))
  have measured := Within.of_le small
  exact ((measured.mul (admitCost_within small)).mul ((((Within.const 15).add measured).add
    (measured.mul ((measured.scale 2).add_const 12))).add (admitMax_within small))).le_of shaped |>.raise
    (by norm_num) (by norm_num)

/-! ## The remaining cores within their requests -/

theorem absCore_within (binder : SourceVar) (input : Theorem)
    (inputShape : input.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand input.sequent.concl.term)
      (eqLeft input.sequent.concl.term) (eqRight input.sequent.concl.term))
    (absent : ∀ term ∈ (sortedHypotheses input.sequent.hyp).map CanonicalTerm.term,
      DBTerm.hasFree binder term = false)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent))
    (inputWeight : openJudgmentWeight inputDerived = weight (sequentJ input.sequent) + 1) :
    Within (requestSize (.inference (.abs binder input))) 100000 4
      (openJudgmentWeight (absCore calculus binder input inputShape absent inputDerived)) := by
  rw [absCore_weight, inputWeight]
  have sized : requestSize (.inference (.abs binder input)) = weight (freeVarP binder) + weight (sequentJ input.sequent) :=
    rfl
  have parts := hypotheses_le_sequentJ input.sequent
  have concl := conclusion_le_sequentJ input.sequent
  have binderParts := weight_freeVarP binder
  have hypotheses := weight_termsP_sortedHypotheses input.sequent
  have operand := weight_eqOperand_le input.sequent.concl.term
  have leftSide := weight_eqLeft_le input.sequent.concl.term
  have rightSide := weight_eqRight_le input.sequent.concl.term
  rw [weight_boolP] at operand
  have leftClosed := weight_closeFreeAt binder 0 (eqLeft input.sequent.concl.term)
  have rightClosed := weight_closeFreeAt binder 0 (eqRight input.sequent.concl.term)
  have leftSmall : weight (groundP (encodeTerm (eqLeft input.sequent.concl.term))) ≤
      requestSize (.inference (.abs binder input)) := by omega
  have rightSmall : weight (groundP (encodeTerm (eqRight input.sequent.concl.term))) ≤
      requestSize (.inference (.abs binder input)) := by omega
  have leftClosedSmall : weight (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqLeft input.sequent.concl.term)))) ≤
      requestSize (.inference (.abs binder input)) * (requestSize (.inference (.abs binder input)) + 3) :=
    le_trans leftClosed (by nlinarith)
  have rightClosedSmall :
      weight (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqRight input.sequent.concl.term)))) ≤
        requestSize (.inference (.abs binder input)) * (requestSize (.inference (.abs binder input)) + 3) :=
    le_trans rightClosed (by nlinarith)
  have root : weight (thmJ (sequentHypothesesP input.sequent)
      (equalityTermP (functionTyP (groundP (encodeTy binder.ty)) (groundP (encodeTy (eqOperand input.sequent.concl.term))))
        (absTermP (groundP (encodeTy binder.ty))
          (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqLeft input.sequent.concl.term)))))
        (absTermP (groundP (encodeTy binder.ty))
          (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqRight input.sequent.concl.term))))))) ≤
      2 * (requestSize (.inference (.abs binder input)) * (requestSize (.inference (.abs binder input)) + 3)) +
        (7 * requestSize (.inference (.abs binder input)) + 37440) := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, weight_functionTyP, weight_absTermP,
      weight_absTermP, sequentHypothesesP_eq_treesP]
    omega
  have measured := Within.of_le (le_refl (requestSize (.inference (.abs binder input))))
  have rootW := ((((measured.mul (measured.add_const 3)).scale 2).add ((measured.scale 7).add_const 37440))).le_of root
  have named := name_within calculus binder.name (Within.of_le (size := requestSize (.inference (.abs binder input)))
    (by omega))
  have typedBinder := ty_within calculus binder.ty (Within.of_le (size := requestSize (.inference (.abs binder input)))
    (by omega))
  have fresh := notFreeAll_within calculus binder _ absent
    (Within.of_le (size := requestSize (.inference (.abs binder input))) (by omega))
  have closedLeft := close_within calculus binder (eqLeft input.sequent.concl.term)
    (Within.of_le (size := requestSize (.inference (.abs binder input))) (by omega))
  have closedRight := close_within calculus binder (eqRight input.sequent.concl.term)
    (Within.of_le (size := requestSize (.inference (.abs binder input))) (by omega))
  have inputW : Within (requestSize (.inference (.abs binder input))) (1 + 1) 1
      (weight (sequentJ input.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((rootW.add_const 1).add (inputW.add (named.add (typedBinder.add (fresh.add
    (closedLeft.add closedRight)))))).raise (by norm_num) (by norm_num))

theorem betaCore_within (source : CheckedSourceTerm) (name : Name) (type : Ty) (bodySource : SourceTerm)
    (sourceShape : source.source = .app (.abs name type bodySource) (.var name type)) :
    Within (requestSize (.inference (.beta source))) 1000000000000 8
      (openJudgmentWeight (betaCore calculus (context := context) source name type bodySource sourceShape)) := by
  have checked : (source.source.toDB []).inferType [] = some source.ty := by
    rw [← source.checked]
    exact DBTerm.inferType_toDB [] source.source
  rw [betaCore_weight calculus source name type bodySource sourceShape checked]
  have sized : requestSize (.inference (.beta source)) =
      weight (groundP (encodeSourceTerm source.source)) + weight (groundP (encodeTy source.ty)) := rfl
  have shapeWeight := congrArg (fun term => weight (groundP (encodeSourceTerm term))) sourceShape
  simp only [weight_sourceApp, weight_sourceAbs, weight_sourceVar] at shapeWeight
  have converted := weight_toDB [] source.source
  rw [weight_bindersP_nil] at converted
  have bodyConverted := weight_toDB [⟨name, type⟩] bodySource
  rw [weight_bindersP_cons, weight_bindersP_nil, weight_freeVarP] at bodyConverted
  have freeWeight := weight_encodeTerm_free ⟨name, type⟩
  have instantiated := weight_instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])
  set Q := requestSize (.inference (.beta source)) with hQ
  have nameSmall : weight (groundP (encodeName name)) ≤ Q := by omega
  have typeSmall : weight (groundP (encodeTy type)) ≤ Q := by omega
  have bodySmall : weight (groundP (encodeSourceTerm bodySource)) ≤ Q := by omega
  have sourceSmall : weight (groundP (encodeSourceTerm source.source)) ≤ Q := by omega
  have measured := Within.of_le (le_refl Q)
  have convertedW : Within Q (2 * 1 + 11) (1 + 1) (weight (groundP (encodeTerm (source.source.toDB [])))) :=
    (((measured.scale 2).add_const 11).mul measured).le_of (le_trans converted (by nlinarith))
  have bodyW : Within Q (3 * 1 + 309) (1 + 1) (weight (groundP (encodeTerm (bodySource.toDB [⟨name, type⟩])))) :=
    (((measured.scale 3).add_const 309).mul measured).le_of (le_trans bodyConverted (by nlinarith))
  have freeW : Within Q (1 + 286) 1 (weight (groundP (encodeTerm (.free ⟨name, type⟩)))) :=
    (measured.add_const 286).le_of (by simp only [freeWeight]; omega)
  have toDB := toDB_within calculus source.source (Within.of_le sourceSmall)
  have typed := typeOf_within calculus (source.source.toDB []) source.ty checked convertedW
  have instance' := instantiate_within calculus (.free ⟨name, type⟩) (bodySource.toDB [⟨name, type⟩]) (bodyW.add freeW)
  have instW : Within Q ((3 * 1 + 309) * (1 + 286 + 1)) (1 + 1 + 1)
      (weight (groundP (encodeTerm (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩]))))) :=
    (bodyW.mul (freeW.add_const 1)).le_of instantiated
  have root : weight (thmJ nilP (equalityTermP (groundP (encodeTy source.ty))
      (appTermP (absTermP (groundP (encodeTy type)) (groundP (encodeTerm (bodySource.toDB [⟨name, type⟩]))))
        (freeTermP (groundP (encodeName name)) (groundP (encodeTy type))))
      (groundP (encodeTerm (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])))))) ≤
      5 * Q + 17552 + (weight (groundP (encodeTerm (bodySource.toDB [⟨name, type⟩]))) +
        weight (groundP (encodeTerm (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩]))))) := by
    rw [weight_thmJ, weight_equalityTermP, weight_boolP, weight_equalityConstP, weight_nilP, weight_appTermP,
      weight_absTermP, weight_freeTermP]
    omega
  have rootW := (((measured.scale 5).add_const 17552).add (bodyW.add instW)).le_of root
  exact (((rootW.add_const 1).add (toDB.add (typed.add instance'))).raise (by norm_num) (by norm_num))

theorem instCore_within (maplets : List SourceSubstitution.TermMaplet) (input : Theorem)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent))
    (inputWeight : openJudgmentWeight inputDerived = weight (sequentJ input.sequent) + 1) :
    Within (requestSize (.inference (.inst maplets input))) 10000000 9
      (openJudgmentWeight (instCore calculus maplets input admissible inputDerived)) := by
  rw [instCore_weight, inputWeight]
  have sized : requestSize (.inference (.inst maplets input)) =
      weight (termMapletsP maplets) + weight (sequentJ input.sequent) := rfl
  set Q := requestSize (.inference (.inst maplets input)) with hQ
  have parts := hypotheses_le_sequentJ input.sequent
  have concl := conclusion_le_sequentJ input.sequent
  have hypotheses := weight_termsP_sortedHypotheses input.sequent
  have table := weight_tableP_termEntries maplets
  have acted := weight_tableActionList (SourceSubstitution.termEntries maplets)
    ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
  have concluded := weight_tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term
  have sortedLe := weight_treeSort ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
    (tableAction (SourceSubstitution.termEntries maplets))).map encodeTerm)
  rw [← termsP_eq_treesP] at sortedLe
  have measured := Within.of_le (le_refl Q)
  have mapletsSmall : weight (termMapletsP maplets) ≤ Q := by omega
  have tableW : Within Q (1 * (2 * 1 + 12)) (1 + 1) (weight (tableP (SourceSubstitution.termEntries maplets))) :=
    ((Within.of_le mapletsSmall).mul ((Within.of_le mapletsSmall).scale 2 |>.add_const 12)).le_of table
  have hypothesesW : Within Q 1 1 (weight (termsP ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term))) :=
    Within.of_le (by omega)
  have conclW : Within Q 1 1 (weight (groundP (encodeTerm input.sequent.concl.term))) := Within.of_le (by omega)
  have actedW : Within Q (1 * (1 * (2 * 1 + 12) + 1)) (1 + (1 + 1))
      (weight (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
        (tableAction (SourceSubstitution.termEntries maplets))))) :=
    (hypothesesW.mul (tableW.add_const 1)).le_of acted
  have conclActedW : Within Q (1 * (1 * (2 * 1 + 12) + 1)) (1 + (1 + 1))
      (weight (groundP (encodeTerm (tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term)))) :=
    (conclW.mul (tableW.add_const 1)).le_of concluded
  have admitted := admit_within calculus maplets admissible mapletsSmall
  have applied := tmApplyList_within calculus (SourceSubstitution.termEntries maplets)
    ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term) (hypothesesW.add tableW)
  have sortedW := sort_within calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
    (tableAction (SourceSubstitution.termEntries maplets))).map encodeTerm) (by rw [← termsP_eq_treesP]; exact actedW)
  have appliedConcl := tmApply_within calculus (SourceSubstitution.termEntries maplets) input.sequent.concl.term
    (conclW.add tableW)
  have root : weight (thmJ (treesP (actedHypotheses (tableAction (SourceSubstitution.termEntries maplets)) input))
      (groundP (encodeTerm (tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term)))) ≤
      10 + (weight (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
        (tableAction (SourceSubstitution.termEntries maplets)))) +
        weight (groundP (encodeTerm (tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term)))) := by
    rw [weight_thmJ]
    unfold actedHypotheses
    omega
  have rootW := ((Within.const 10).add (actedW.add conclActedW)).le_of root
  have inputW : Within Q (1 + 1) 1 (weight (sequentJ input.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((rootW.add_const 1).add (inputW.add (admitted.add (applied.add (sortedW.add appliedConcl))))).raise
    (by norm_num) (by norm_num))

theorem instTypeCore_within (entries : List (Ty × Ty)) (input : Theorem)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent))
    (inputWeight : openJudgmentWeight inputDerived = weight (sequentJ input.sequent) + 1) :
    Within (requestSize (.inference (.instType entries input))) 10000 6
      (openJudgmentWeight (instTypeCore calculus entries input inputDerived)) := by
  rw [instTypeCore_weight, inputWeight]
  have sized : requestSize (.inference (.instType entries input)) =
      weight (typeMapletsP entries) + weight (sequentJ input.sequent) := rfl
  set Q := requestSize (.inference (.instType entries input)) with hQ
  have parts := hypotheses_le_sequentJ input.sequent
  have concl := conclusion_le_sequentJ input.sequent
  have hypotheses := weight_termsP_sortedHypotheses input.sequent
  have acted := weight_termTypeActionList entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
  have concluded := weight_termTypeAction entries input.sequent.concl.term
  have sortedLe := weight_treeSort ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
    (termTypeAction entries)).map encodeTerm)
  rw [← termsP_eq_treesP] at sortedLe
  have entriesW : Within Q 1 1 (weight (typeMapletsP entries)) := Within.of_le (by omega)
  have hypothesesW : Within Q 1 1 (weight (termsP ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term))) :=
    Within.of_le (by omega)
  have conclW : Within Q 1 1 (weight (groundP (encodeTerm input.sequent.concl.term))) := Within.of_le (by omega)
  have actedW : Within Q (1 * (1 + 1)) (1 + 1)
      (weight (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map (termTypeAction entries)))) :=
    (hypothesesW.mul (entriesW.add_const 1)).le_of acted
  have conclActedW : Within Q (1 * (1 + 1)) (1 + 1)
      (weight (groundP (encodeTerm (termTypeAction entries input.sequent.concl.term)))) :=
    (conclW.mul (entriesW.add_const 1)).le_of concluded
  have mapped := typeMaplets_within calculus entries entriesW
  have applied := termTyActList_within calculus entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
    (Within.of_le (size := Q) (by omega))
  have sortedW := sort_within calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
    (termTypeAction entries)).map encodeTerm) (by rw [← termsP_eq_treesP]; exact actedW)
  have appliedConcl := termTyAct_within calculus entries input.sequent.concl.term (Within.of_le (size := Q) (by omega))
  have root : weight (thmJ (treesP (actedHypotheses (termTypeAction entries) input))
      (groundP (encodeTerm (termTypeAction entries input.sequent.concl.term)))) ≤
      10 + (weight (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map (termTypeAction entries))) +
        weight (groundP (encodeTerm (termTypeAction entries input.sequent.concl.term)))) := by
    rw [weight_thmJ]
    unfold actedHypotheses
    omega
  have rootW := ((Within.const 10).add (actedW.add conclActedW)).le_of root
  have inputW : Within Q (1 + 1) 1 (weight (sequentJ input.sequent) + 1) := (Within.of_le (by omega)).add_const 1
  exact (((rootW.add_const 1).add (inputW.add (mapped.add (applied.add (sortedW.add appliedConcl))))).raise
    (by norm_num) (by norm_num))

theorem axiomCore_within (sequent : Sequent) (member : sequent ∈ axioms) :
    Within (requestSize (.axiom sequent)) 2 1 (openJudgmentWeight (axiomCore calculus (context := context) sequent member)) := by
  rw [axiomCore_weight]
  exact (Within.of_le (le_refl _)).add_const 1

/-! ## The proof of a node -/

/-- The envelope every node's proof lies within. -/
abbrev nodeFactor : ℕ := 35 * 1000000000000

include calculus in
theorem openWeight_le_of_within {goal : Pattern} (derivation : OpenDerivation definition context goal)
    {size factor degree : ℕ} (within : Within size factor degree (openJudgmentWeight derivation))
    (factors : factor ≤ 1000000000000) (degrees : degree ≤ 9) :
    openWeight derivation.eraseOpen ≤ nodeFactor * (size + 1) ^ 9 := by
  have covered := openWeight_eraseOpen_le (holCalculus_covering calculus) derivation
  have raised := within.raise factors degrees
  unfold Within at raised
  simp only [nodeFactor]
  omega

theorem noProof_weight (size : ℕ) : openWeight noProof ≤ nodeFactor * (size + 1) ^ 9 := by
  have one : 1 ≤ (size + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
  simp only [noProof, openWeight, nodeFactor]
  omega

include calculus in
/-- **The proof of a node is at most polynomial in the size of its request.** -/
theorem ruleProof_weight (parents : List Nat) : ∀ request : RuleRequest,
    openWeight (ruleProof calculus (context := context) parents request) ≤
      nodeFactor * (requestSize request + 1) ^ 9
  | .inference (.refl term) => by
      simp only [ruleProof, inferenceProof]
      exact openWeight_le_of_within calculus _ (reflCore_within calculus term) (by norm_num) (by norm_num)
  | .inference (.assume term) => by
      simp only [ruleProof, inferenceProof]
      split
      · exact openWeight_le_of_within calculus _ (assumeCore_within calculus term _) (by norm_num) (by norm_num)
      · exact noProof_weight _
  | .inference (.trans left right) => by
      simp only [ruleProof, inferenceProof]
      split
      · next leftLeaf rightLeaf leftFound rightFound =>
          split
          · split
            · exact openWeight_le_of_within calculus _ (transCore_within calculus left right _ _ leftLeaf rightLeaf
                (openJudgmentWeight_premiseLeaf leftFound) (openJudgmentWeight_premiseLeaf rightFound))
                (by norm_num) (by norm_num)
            · exact noProof_weight _
          · exact noProof_weight _
      · exact noProof_weight _
  | .inference (.mkComb functions arguments) => by
      simp only [ruleProof, inferenceProof]
      split
      · next functionsLeaf argumentsLeaf functionsFound argumentsFound =>
          split
          · split
            · exact openWeight_le_of_within calculus _ (mkCombCore_within calculus functions arguments _ _
                functionsLeaf argumentsLeaf (openJudgmentWeight_premiseLeaf functionsFound)
                (openJudgmentWeight_premiseLeaf argumentsFound)) (by norm_num) (by norm_num)
            · exact noProof_weight _
          · exact noProof_weight _
      · exact noProof_weight _
  | .inference (.abs binder input) => by
      simp only [ruleProof, inferenceProof]
      split
      · next inputLeaf inputFound =>
          split
          · split
            · exact openWeight_le_of_within calculus _ (absCore_within calculus binder input _ _ inputLeaf
                (openJudgmentWeight_premiseLeaf inputFound)) (by norm_num) (by norm_num)
            · exact noProof_weight _
          · exact noProof_weight _
      · exact noProof_weight _
  | .inference (.beta source) => by
      simp only [ruleProof, inferenceProof]
      split
      · exact openWeight_le_of_within calculus _ (betaCore_within calculus source _ _ _ _) (by norm_num) (by norm_num)
      · exact noProof_weight _
  | .inference (.eqMp equality premise) => by
      simp only [ruleProof, inferenceProof]
      split
      · next equalityLeaf premiseLeaf' equalityFound premiseFound =>
          split
          · split
            · exact openWeight_le_of_within calculus _ (eqMpCore_within calculus equality premise _ _ equalityLeaf
                premiseLeaf' (openJudgmentWeight_premiseLeaf equalityFound)
                (openJudgmentWeight_premiseLeaf premiseFound)) (by norm_num) (by norm_num)
            · exact noProof_weight _
          · exact noProof_weight _
      · exact noProof_weight _
  | .inference (.deductAntisym left right) => by
      simp only [ruleProof, inferenceProof]
      split
      · next leftLeaf rightLeaf leftFound rightFound =>
          split
          · exact openWeight_le_of_within calculus _ (deductAntisymCore_within calculus left right _ leftLeaf rightLeaf
              (openJudgmentWeight_premiseLeaf leftFound) (openJudgmentWeight_premiseLeaf rightFound))
              (by norm_num) (by norm_num)
          · exact noProof_weight _
      · exact noProof_weight _
  | .inference (.instType entries input) => by
      simp only [ruleProof, inferenceProof]
      split
      · next inputLeaf inputFound =>
          exact openWeight_le_of_within calculus _ (instTypeCore_within calculus entries input inputLeaf
            (openJudgmentWeight_premiseLeaf inputFound)) (by norm_num) (by norm_num)
      · exact noProof_weight _
  | .inference (.inst maplets input) => by
      simp only [ruleProof, inferenceProof]
      split
      · next inputLeaf inputFound =>
          split
          · exact openWeight_le_of_within calculus _ (instCore_within calculus maplets input _ inputLeaf
              (openJudgmentWeight_premiseLeaf inputFound)) (by norm_num) (by norm_num)
          · exact noProof_weight _
      · exact noProof_weight _
  | .axiom sequent => by
      simp only [ruleProof]
      split
      · exact openWeight_le_of_within calculus _ (axiomCore_within calculus sequent _) (by norm_num) (by norm_num)
      · exact noProof_weight _

end Calculus

end Mettapedia.Languages.HOLLight.FirstOrder
