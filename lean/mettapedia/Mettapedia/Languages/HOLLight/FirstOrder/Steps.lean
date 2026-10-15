import Mettapedia.Languages.HOLLight.FirstOrder.Sizes
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Each inference of HOL Light as one open derivation

A node of a proof graph cites earlier theorems. Its step derives the node's rendered sequent
with the rendered sequents of the cited theorems standing as premises: an open derivation
whose premise holes are filled by assumptions, or, in a tree, by the derivations of the
subtrees.

A step is a function of the node and its premises. The data each rule needs is read off
the premises by total projections (`eqOperand`, `eqLeft`, `eqRight`, `domainOf`,
`codomainOf`, `redexBinder`, `redexBody`); the rule's semantics supplies only the proofs
that the projections return the right parts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
  (OpenDerivation OpenDerivationList RawOpenProof checkOpenRaw checkOpenRawChildren checkOpenRaw_erase)
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules (checkSchema checkSchemas checkSchema_iff checkSchemas_iff)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (substSchema substSchemas bindingValue instantiateSchemaAt?_eq instantiateSchemasAt?_eq)
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)

/-! ## Reading the parts of terms -/

/-- The operand type of an equality term. -/
def eqOperand : DBTerm → Ty
  | .app (.app (.const _ (.op _ (operand :: _))) _) _ => operand
  | _ => Ty.bool

/-- The left side of an equality term. -/
def eqLeft : DBTerm → DBTerm
  | .app (.app _ left) _ => left
  | term => term

/-- The right side of an equality term. -/
def eqRight : DBTerm → DBTerm
  | .app _ right => right
  | term => term

@[simp] theorem eqOperand_equalityDB (operand : Ty) (left right : DBTerm) :
    eqOperand (CanonicalTerm.equalityDB operand left right) = operand := rfl

@[simp] theorem eqLeft_equalityDB (operand : Ty) (left right : DBTerm) :
    eqLeft (CanonicalTerm.equalityDB operand left right) = left := rfl

@[simp] theorem eqRight_equalityDB (operand : Ty) (left right : DBTerm) :
    eqRight (CanonicalTerm.equalityDB operand left right) = right := rfl

/-- An equality term is the equality of its parts. -/
theorem equalityDB_parts {term : DBTerm} {operand : Ty} {left right : DBTerm}
    (shape : term = CanonicalTerm.equalityDB operand left right) :
    term = CanonicalTerm.equalityDB (eqOperand term) (eqLeft term) (eqRight term) := by
  subst shape
  rfl

/-- The domain of a function type. -/
def domainOf : Ty → Ty
  | .op _ (domain :: _) => domain
  | _ => Ty.bool

/-- The codomain of a function type. -/
def codomainOf : Ty → Ty
  | .op _ [_, codomain] => codomain
  | _ => Ty.bool

@[simp] theorem domainOf_function (domain codomain : Ty) : domainOf (Ty.function domain codomain) = domain := rfl

@[simp] theorem codomainOf_function (domain codomain : Ty) :
    codomainOf (Ty.function domain codomain) = codomain := rfl

/-- The binder of a beta redex `(λx. t) x`. -/
def redexBinder : SourceTerm → SourceVar
  | .app (.abs name type _) _ => ⟨name, type⟩
  | _ => ⟨Name.global "", Ty.bool⟩

/-- The body of a beta redex `(λx. t) x`. -/
def redexBody : SourceTerm → SourceTerm
  | .app (.abs _ _ body) _ => body
  | term => term

@[simp] theorem redexBinder_redex (name : Name) (type : Ty) (body : SourceTerm) :
    redexBinder (.app (.abs name type body) (.var name type)) = ⟨name, type⟩ := rfl

@[simp] theorem redexBody_redex (name : Name) (type : Ty) (body : SourceTerm) :
    redexBody (.app (.abs name type body) (.var name type)) = body := rfl

/-! ## Firing a rule in an open derivation -/

/-- The rule application that `fire` records. -/
theorem fire_application {definition : ValidatedCalculusLanguageDef} {r : RuleSchema}
    (member : r ∈ definition.1.rules) (shape : RuleShape r) (arguments : List Pattern)
    (arity : arguments.length = r.metavariables.length) (valid : ∀ argument ∈ arguments, Valid argument) :
    RuleApplication definition ⟨r.id, arguments⟩ (substSchemas (ruleValues r arguments) r.premises)
      (substSchema (ruleValues r arguments) r.conclusion) :=
  have arity' : arguments.length = (r.metavariables.map Prod.fst).length := by simpa using arity
  .intro r (lookupRule?_eq_some_of_mem definition member)
    (by rw [shape.formals]; exact argumentsValidAt_of_valid arity' valid)
    (RuleSchema.sideConditionsHold_of_empty _ _ shape.sides)
    (by
      rw [shape.formals]
      exact instantiateSchemasAt?_sound
        (instantiateSchemasAt?_eq arity' ((checkSchemas_iff _ _).mp shape.premisesSchema)))
    (by
      rw [shape.formals]
      exact instantiateSchemaAt?_sound
        (instantiateSchemaAt?_eq arity' ((checkSchema_iff _ _).mp shape.conclusionSchema)))

/-- An open derivation read at an equal judgment. -/
def recastOpen {definition : ValidatedCalculusLanguageDef} {context : List Pattern} {first second : Pattern}
    (same : first = second) (derivation : OpenDerivation definition context first) :
    OpenDerivation definition context second :=
  same ▸ derivation

/-- Fire a rule at the judgments its instantiation computes, over open premises. -/
def fireOpenAt {definition : ValidatedCalculusLanguageDef} {context : List Pattern} {r : RuleSchema}
    (member : r ∈ definition.1.rules) (shape : RuleShape r) (arguments : List Pattern)
    (arity : arguments.length = r.metavariables.length) (valid : ∀ argument ∈ arguments, Valid argument)
    {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : OpenDerivationList definition context premises) : OpenDerivation definition context conclusion :=
  .byRule ⟨r.id, arguments⟩
    (by rw [← premisesEq, ← conclusionEq]; exact fire_application member shape arguments arity valid) children

/-- A closed derivation in an open context. -/
abbrev closedIn {definition : ValidatedCalculusLanguageDef} {context : List Pattern} {goal : Pattern}
    (derivation : Derivation definition goal) : OpenDerivation definition context goal :=
  OpenDerivation.ofClosed derivation

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms) {context : List Pattern}

/-! ## The inference rules over open premises -/

include calculus in
def openReflRule {t a : Pattern} (valid : ∀ argument ∈ [t, a], Valid argument)
    (typed : OpenDerivation definition context (typeOfJ nilP t a)) :
    OpenDerivation definition context (thmJ nilP (equalityTermP a t t)) :=
  fireOpenAt (r := inferenceRules[0]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [t, a] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons typed .nil)

include calculus in
def openAssumeRule {t : Pattern} (valid : ∀ argument ∈ [t], Valid argument)
    (typed : OpenDerivation definition context (typeOfJ nilP t boolP)) :
    OpenDerivation definition context (thmJ (consP t nilP) t) :=
  fireOpenAt (r := inferenceRules[1]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [t] rfl valid (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons typed .nil)

include calculus in
def openTransRule {h1 h2 h a l m r : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, l, m, r], Valid argument)
    (left : OpenDerivation definition context (thmJ h1 (equalityTermP a l m)))
    (right : OpenDerivation definition context (thmJ h2 (equalityTermP a m r)))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    OpenDerivation definition context (thmJ h (equalityTermP a l r)) :=
  fireOpenAt (r := inferenceRules[2]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, l, m, r] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons left (.cons right (.cons union .nil)))

include calculus in
def openMkCombRule {h1 h2 h a b f g x y : Pattern}
    (valid : ∀ argument ∈ [h1, h2, h, a, b, f, g, x, y], Valid argument)
    (functions : OpenDerivation definition context (thmJ h1 (equalityTermP (functionTyP a b) f g)))
    (arguments : OpenDerivation definition context (thmJ h2 (equalityTermP a x y)))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    OpenDerivation definition context (thmJ h (equalityTermP b (appTermP f x) (appTermP g y))) :=
  fireOpenAt (r := inferenceRules[3]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, b, f, g, x, y] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons functions (.cons arguments (.cons union .nil)))

include calculus in
def openAbsRule {h a s t x b s2 t2 : Pattern} (valid : ∀ argument ∈ [h, a, s, t, x, b, s2, t2], Valid argument)
    (input : OpenDerivation definition context (thmJ h (equalityTermP a s t)))
    (named : OpenDerivation definition context (wfJ "Name" x))
    (typedBinder : OpenDerivation definition context (wfJ "Ty" b))
    (fresh : OpenDerivation definition context (notFreeAllJ (freeTermP x b) h))
    (leftClosed : OpenDerivation definition context (closeJ (freeTermP x b) unaryZeroP s s2))
    (rightClosed : OpenDerivation definition context (closeJ (freeTermP x b) unaryZeroP t t2)) :
    OpenDerivation definition context (thmJ h (equalityTermP (functionTyP b a) (absTermP b s2) (absTermP b t2))) :=
  fireOpenAt (r := inferenceRules[4]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, a, s, t, x, b, s2, t2] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons input (.cons named (.cons typedBinder (.cons fresh (.cons leftClosed (.cons rightClosed .nil))))))

include calculus in
def openBetaRule {x a t body u reduced : Pattern} (valid : ∀ argument ∈ [x, a, t, body, u, reduced], Valid argument)
    (converted : OpenDerivation definition context (toDBJ nilP (sourceAppP (sourceAbsP x a t) (sourceVarP x a))
      (appTermP (absTermP a body) (freeTermP x a))))
    (typed : OpenDerivation definition context (typeOfJ nilP (appTermP (absTermP a body) (freeTermP x a)) u))
    (instantiated : OpenDerivation definition context (instantiateJ (freeTermP x a) unaryZeroP body reduced)) :
    OpenDerivation definition context
      (thmJ nilP (equalityTermP u (appTermP (absTermP a body) (freeTermP x a)) reduced)) :=
  fireOpenAt (r := inferenceRules[5]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [x, a, t, body, u, reduced] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons converted (.cons typed (.cons instantiated .nil)))

include calculus in
def openEqMpRule {h1 h2 h a p q : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, p, q], Valid argument)
    (equality : OpenDerivation definition context (thmJ h1 (equalityTermP a p q)))
    (premise : OpenDerivation definition context (thmJ h2 p))
    (union : OpenDerivation definition context (unionJ h1 h2 h)) :
    OpenDerivation definition context (thmJ h q) :=
  fireOpenAt (r := inferenceRules[6]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, p, q] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules]) (.cons equality (.cons premise (.cons union .nil)))

include calculus in
def openDeductAntisymRule {h1 h2 k1 k2 h p q a : Pattern}
    (valid : ∀ argument ∈ [h1, h2, k1, k2, h, p, q, a], Valid argument)
    (left : OpenDerivation definition context (thmJ h1 p)) (right : OpenDerivation definition context (thmJ h2 q))
    (leftTyped : OpenDerivation definition context (typeOfJ nilP p a))
    (rightTyped : OpenDerivation definition context (typeOfJ nilP q a))
    (leftErase : OpenDerivation definition context (eraseJ q h1 k1))
    (rightErase : OpenDerivation definition context (eraseJ p h2 k2))
    (union : OpenDerivation definition context (unionJ k1 k2 h)) :
    OpenDerivation definition context (thmJ h (equalityTermP a p q)) :=
  fireOpenAt (r := inferenceRules[7]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, k1, k2, h, p, q, a] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons left (.cons right (.cons leftTyped (.cons rightTyped (.cons leftErase (.cons rightErase
      (.cons union .nil)))))))

include calculus in
def openInstRule {h c ms table h1 h2 c2 : Pattern}
    (valid : ∀ argument ∈ [h, c, ms, table, h1, h2, c2], Valid argument)
    (input : OpenDerivation definition context (thmJ h c))
    (admitted : OpenDerivation definition context (admitTmJ ms table))
    (hypotheses : OpenDerivation definition context (tmApplyListJ table h h1))
    (sorted : OpenDerivation definition context (sortJ h1 h2))
    (concluded : OpenDerivation definition context (tmApplyJ table c c2)) :
    OpenDerivation definition context (thmJ h2 c2) :=
  fireOpenAt (r := instantiationRules[0]) (member_of_instantiationRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, c, ms, table, h1, h2, c2] rfl valid
    (by fire_simp [instantiationRules]) (by fire_simp [instantiationRules])
    (.cons input (.cons admitted (.cons hypotheses (.cons sorted (.cons concluded .nil)))))

include calculus in
def openInstTypeRule {h c es h1 h2 c2 : Pattern} (valid : ∀ argument ∈ [h, c, es, h1, h2, c2], Valid argument)
    (input : OpenDerivation definition context (thmJ h c))
    (entries : OpenDerivation definition context (wfJ "TypeMaplets" es))
    (hypotheses : OpenDerivation definition context (termTyActListJ es h h1))
    (sorted : OpenDerivation definition context (sortJ h1 h2))
    (concluded : OpenDerivation definition context (termTyActJ es c c2)) :
    OpenDerivation definition context (thmJ h2 c2) :=
  fireOpenAt (r := instantiationRules[1]) (member_of_instantiationRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, c, es, h1, h2, c2] rfl valid
    (by fire_simp [instantiationRules]) (by fire_simp [instantiationRules])
    (.cons input (.cons entries (.cons hypotheses (.cons sorted (.cons concluded .nil)))))

/-! ## Rendered sequents as `Thm` judgments -/

/-- An open derivation of a rendered sequent as one of its `Thm` judgment, with computed sides. -/
def asThmOpen {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : sequentHypothesesP sequent = hypotheses) (conclusionEq : sequentConclusionP sequent = conclusion)
    (derivation : OpenDerivation definition context (sequentJ sequent)) :
    OpenDerivation definition context (thmJ hypotheses conclusion) :=
  recastOpen (by rw [← hypothesesEq, ← conclusionEq]; rfl) derivation

/-- An open derivation of a `Thm` judgment as one of the rendered sequent it is. -/
def ofThmOpen {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : hypotheses = sequentHypothesesP sequent) (conclusionEq : conclusion = sequentConclusionP sequent)
    (derivation : OpenDerivation definition context (thmJ hypotheses conclusion)) :
    OpenDerivation definition context (sequentJ sequent) :=
  recastOpen (by rw [hypothesesEq, conclusionEq]; rfl) derivation

theorem sequentConclusionP_eq (sequent : Sequent) :
    sequentConclusionP sequent = groundP (encodeTerm sequent.concl.term) := rfl

/-- The rendered conclusion of an equation, as the calculus writes equations. -/
theorem sequentConclusionP_of_equality {sequent : Sequent} {operand : Ty} {left right : DBTerm}
    (shape : sequent.concl.term = CanonicalTerm.equalityDB operand left right) :
    sequentConclusionP sequent =
      equalityTermP (groundP (encodeTy operand)) (groundP (encodeTerm left)) (groundP (encodeTerm right)) := by
  rw [sequentConclusionP_of_term shape]
  rfl

/-- The rendered conclusion of an equation between functions. -/
theorem sequentConclusionP_of_functionEquality {sequent : Sequent} {domain codomain : Ty} {left right : DBTerm}
    (shape : sequent.concl.term = CanonicalTerm.equalityDB (Ty.function domain codomain) left right) :
    sequentConclusionP sequent =
      equalityTermP (functionTyP (groundP (encodeTy domain)) (groundP (encodeTy codomain)))
        (groundP (encodeTerm left)) (groundP (encodeTerm right)) := by
  rw [sequentConclusionP_of_term shape]
  rfl

/-! ## The cores: computed judgments from decidable facts about the data

A core derives the judgment a rule computes from its data. Its hypotheses are facts the
data either has or lacks, decided by structural comparisons, so a translation can build a
core without running HOL Light's kernel. The steps below identify the computed judgment
with the rendered sequent of the node, using the rule's semantics. -/

include calculus in
/-- The core of `REFL`. -/
def reflCore (term : CanonicalTerm) :
    OpenDerivation definition context (thmJ nilP (equalityTermP (groundP (encodeTy term.ty))
      (groundP (encodeTerm term.term)) (groundP (encodeTerm term.term)))) :=
  openReflRule calculus (by simp) (closedIn (deriveTypeOf calculus [] term.term term.ty term.checked))

include calculus in
/-- The core of `ASSUME`. -/
def assumeCore (term : CanonicalTerm) (isBool : term.ty = Ty.bool) :
    OpenDerivation definition context
      (thmJ (consP (groundP (encodeTerm term.term)) nilP) (groundP (encodeTerm term.term))) :=
  openAssumeRule calculus (by simp)
    (closedIn (deriveTypeOf calculus [] term.term Ty.bool (by rw [term.checked, isBool])))

include calculus in
/-- The core of `TRANS`. -/
def transCore (left right : Theorem)
    (leftShape : left.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqLeft left.sequent.concl.term) (eqRight left.sequent.concl.term))
    (rightShape : right.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqRight left.sequent.concl.term) (eqRight right.sequent.concl.term))
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (treeUnion (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)))
        (equalityTermP (groundP (encodeTy (eqOperand left.sequent.concl.term)))
          (groundP (encodeTerm (eqLeft left.sequent.concl.term)))
          (groundP (encodeTerm (eqRight right.sequent.concl.term))))) :=
  openTransRule calculus (by simp)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_equality leftShape) leftDerived)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_equality rightShape) rightDerived)
    (closedIn (deriveUnion calculus (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)))

include calculus in
/-- The core of `MK_COMB`. -/
def mkCombCore (functions arguments : Theorem)
    (functionShape : functions.sequent.concl.term = CanonicalTerm.equalityDB
      (Ty.function (domainOf (eqOperand functions.sequent.concl.term))
        (codomainOf (eqOperand functions.sequent.concl.term)))
      (eqLeft functions.sequent.concl.term) (eqRight functions.sequent.concl.term))
    (argumentShape : arguments.sequent.concl.term = CanonicalTerm.equalityDB
      (domainOf (eqOperand functions.sequent.concl.term))
      (eqLeft arguments.sequent.concl.term) (eqRight arguments.sequent.concl.term))
    (functionsDerived : OpenDerivation definition context (sequentJ functions.sequent))
    (argumentsDerived : OpenDerivation definition context (sequentJ arguments.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (treeUnion (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp)))
        (equalityTermP (groundP (encodeTy (codomainOf (eqOperand functions.sequent.concl.term))))
          (appTermP (groundP (encodeTerm (eqLeft functions.sequent.concl.term)))
            (groundP (encodeTerm (eqLeft arguments.sequent.concl.term))))
          (appTermP (groundP (encodeTerm (eqRight functions.sequent.concl.term)))
            (groundP (encodeTerm (eqRight arguments.sequent.concl.term)))))) :=
  openMkCombRule calculus (by simp)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_functionEquality functionShape)
      functionsDerived)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_equality argumentShape) argumentsDerived)
    (closedIn (deriveUnion calculus (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp)))

include calculus in
/-- The core of `ABS`. -/
def absCore (binder : SourceVar) (input : Theorem)
    (inputShape : input.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand input.sequent.concl.term)
      (eqLeft input.sequent.concl.term) (eqRight input.sequent.concl.term))
    (absent : ∀ term ∈ (sortedHypotheses input.sequent.hyp).map CanonicalTerm.term,
      DBTerm.hasFree binder term = false)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context (thmJ (sequentHypothesesP input.sequent)
      (equalityTermP (functionTyP (groundP (encodeTy binder.ty)) (groundP (encodeTy (eqOperand input.sequent.concl.term))))
        (absTermP (groundP (encodeTy binder.ty))
          (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqLeft input.sequent.concl.term)))))
        (absTermP (groundP (encodeTy binder.ty))
          (groundP (encodeTerm (DBTerm.closeFreeAt binder 0 (eqRight input.sequent.concl.term))))))) :=
  openAbsRule calculus (by simp) (asThmOpen rfl (sequentConclusionP_of_equality inputShape) inputDerived)
    (closedIn (deriveName calculus binder.name)) (closedIn (deriveTy calculus binder.ty))
    (closedIn (recast (second := notFreeAllJ (freeVarP binder) (sequentHypothesesP input.sequent))
      (by rw [sequentHypothesesP_eq_termsP]) (deriveNotFreeAll calculus binder _ absent)))
    (closedIn (deriveClose calculus binder 0 (eqLeft input.sequent.concl.term)))
    (closedIn (deriveClose calculus binder 0 (eqRight input.sequent.concl.term)))

include calculus in
/-- The core of `BETA` at the redex `(λx. t) x`. -/
def betaCore (source : CheckedSourceTerm) (name : Name) (type : Ty) (bodySource : SourceTerm)
    (sourceShape : source.source = .app (.abs name type bodySource) (.var name type)) :
    OpenDerivation definition context (thmJ nilP (equalityTermP (groundP (encodeTy source.ty))
      (appTermP (absTermP (groundP (encodeTy type)) (groundP (encodeTerm (bodySource.toDB [⟨name, type⟩]))))
        (freeTermP (groundP (encodeName name)) (groundP (encodeTy type))))
      (groundP (encodeTerm (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])))))) :=
  have toDBEq : source.source.toDB [] =
      .app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩) := by
    rw [sourceShape]
    simp [SourceTerm.toDB, boundIndex]
  have checked : (source.source.toDB []).inferType [] = some source.ty := by
    rw [← source.checked]
    exact DBTerm.inferType_toDB [] source.source
  openBetaRule calculus (x := groundP (encodeName name)) (a := groundP (encodeTy type))
    (t := groundP (encodeSourceTerm bodySource)) (by simp)
    (closedIn (recast (second := toDBJ (bindersP [])
        (groundP (encodeSourceTerm (.app (.abs name type bodySource) (.var name type))))
        (groundP (encodeTerm (.app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩)))))
      (by rw [toDBEq, sourceShape]) (deriveToDB calculus [] source.source)))
    (closedIn (recast (second := typeOfJ (contextP [])
        (groundP (encodeTerm (.app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩))))
        (groundP (encodeTy source.ty)))
      (by rw [toDBEq]) (deriveTypeOf calculus [] _ source.ty checked)))
    (closedIn (deriveInstantiate calculus (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])))

include calculus in
/-- The core of `EQ_MP`. -/
def eqMpCore (equality premise : Theorem)
    (equalityShape : equality.sequent.concl.term = CanonicalTerm.equalityDB
      (eqOperand equality.sequent.concl.term) (eqLeft equality.sequent.concl.term)
      (eqRight equality.sequent.concl.term))
    (premiseShape : premise.sequent.concl.term = eqLeft equality.sequent.concl.term)
    (equalityDerived : OpenDerivation definition context (sequentJ equality.sequent))
    (premiseDerived : OpenDerivation definition context (sequentJ premise.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (treeUnion (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp)))
        (groundP (encodeTerm (eqRight equality.sequent.concl.term)))) :=
  openEqMpRule calculus (by simp)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_equality equalityShape) equalityDerived)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_term premiseShape) premiseDerived)
    (closedIn (deriveUnion calculus (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp)))

include calculus in
/-- The core of `DEDUCT_ANTISYM_RULE`. -/
def deductAntisymCore (left right : Theorem) (types : left.sequent.concl.ty = right.sequent.concl.ty)
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (treeUnion (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
          (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))))
        (equalityTermP (groundP (encodeTy left.sequent.concl.ty)) (groundP (encodeTerm left.sequent.concl.term))
          (groundP (encodeTerm right.sequent.concl.term)))) :=
  openDeductAntisymRule calculus (by simp)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_eq _) leftDerived)
    (asThmOpen (sequentHypothesesP_eq_treesP _) (sequentConclusionP_eq _) rightDerived)
    (closedIn (deriveTypeOf calculus [] left.sequent.concl.term left.sequent.concl.ty left.sequent.concl.checked))
    (closedIn (recast (second := typeOfJ (contextP []) (groundP (encodeTerm right.sequent.concl.term))
        (groundP (encodeTy left.sequent.concl.ty))) (by rw [← types])
      (deriveTypeOf calculus [] right.sequent.concl.term right.sequent.concl.ty right.sequent.concl.checked)))
    (closedIn (recast (second := eraseJ (groundP (encodeCanonical right.sequent.concl))
        (treesP (hypothesisTrees left.sequent.hyp))
        (treesP (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl)))) (by rw [treeErase_hypothesisTrees])
      (deriveErase calculus (encodeCanonical right.sequent.concl) (hypothesisTrees left.sequent.hyp))))
    (closedIn (recast (second := eraseJ (groundP (encodeCanonical left.sequent.concl))
        (treesP (hypothesisTrees right.sequent.hyp))
        (treesP (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl)))) (by rw [treeErase_hypothesisTrees])
      (deriveErase calculus (encodeCanonical left.sequent.concl) (hypothesisTrees right.sequent.hyp))))
    (closedIn (deriveUnion calculus (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
      (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))))

/-- The sorted image of a theorem's hypotheses under an action on terms. -/
def actedHypotheses (action : DBTerm → DBTerm) (input : Theorem) : List LabeledTree :=
  treeSort ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map action).map encodeTerm)

include calculus in
/-- The core of `INST`. -/
def instCore (maplets : List SourceSubstitution.TermMaplet) (input : Theorem)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (actedHypotheses (tableAction (SourceSubstitution.termEntries maplets)) input))
        (groundP (encodeTerm (tableAction (SourceSubstitution.termEntries maplets) input.sequent.concl.term)))) :=
  openInstRule calculus (by simp) (asThmOpen (sequentHypothesesP_eq_termsP _) (sequentConclusionP_eq _) inputDerived)
    (closedIn (deriveAdmit calculus maplets admissible))
    (closedIn (deriveTmApplyList calculus (SourceSubstitution.termEntries maplets)
      ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)))
    (closedIn (recast (second := sortJ
        (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
          (tableAction (SourceSubstitution.termEntries maplets))))
        (treesP (actedHypotheses (tableAction (SourceSubstitution.termEntries maplets)) input)))
      (by rw [← termsP_eq_treesP]; rfl)
      (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
        (tableAction (SourceSubstitution.termEntries maplets))).map encodeTerm))))
    (closedIn (deriveTmApply calculus (SourceSubstitution.termEntries maplets) input.sequent.concl.term))

include calculus in
/-- The core of `INST_TYPE`. -/
def instTypeCore (entries : List (Ty × Ty)) (input : Theorem)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context
      (thmJ (treesP (actedHypotheses (termTypeAction entries) input))
        (groundP (encodeTerm (termTypeAction entries input.sequent.concl.term)))) :=
  openInstTypeRule calculus (by simp) (asThmOpen (sequentHypothesesP_eq_termsP _) (sequentConclusionP_eq _) inputDerived)
    (closedIn (deriveTypeMaplets calculus entries))
    (closedIn (deriveTermTyActList calculus entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)))
    (closedIn (recast (second := sortJ
        (termsP (((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map (termTypeAction entries)))
        (treesP (actedHypotheses (termTypeAction entries) input)))
      (by rw [← termsP_eq_treesP]; rfl)
      (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
        (termTypeAction entries)).map encodeTerm))))
    (closedIn (deriveTermTyAct calculus entries input.sequent.concl.term))

include calculus in
/-- The core of an axiom the calculus lists. -/
def axiomCore (sequent : Sequent) (member : sequent ∈ axioms) :
    OpenDerivation definition context (sequentJ sequent) :=
  have indexed : (sequent, axioms.idxOf sequent) ∈ axioms.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]
  have ruleMember : rule ("hol.axiom-" ++ toString (axioms.idxOf sequent)) [] [] (sequentJ sequent) ∈
      definition.1.rules :=
    member_of_holRules calculus (by
      simp only [holRules, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨_, indexed, rfl⟩))
  closedIn (fireAt (conclusion := sequentJ sequent) ruleMember
    (rule_shape ⟨by simp [checkSchemas], checkSchema_sequentJ [] sequent⟩) [] rfl
    (by simp) (by simp [rule, substSchemas]) (by simp only [rule]; exact substSchema_sequentJ _ _) .nil)

/-! ## The steps: the core, read at the node's sequent -/

include calculus in
/-- `REFL`. -/
def reflStep {term : CanonicalTerm} {out : Theorem} (semantics : ReflSemantics term out) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  ofThmOpen
    (by
      obtain ⟨_, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_empty]
      rfl)
    (by
      obtain ⟨equality, ⟨-, shape⟩, -, -, conclEq⟩ := semantics
      have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB term.ty term.term term.term := by
        rw [conclEq, shape]
      rw [sequentConclusionP_of_term conclusionTerm]
      rfl)
    (reflCore calculus term)

include calculus in
/-- `ASSUME`. -/
def assumeStep {term : CanonicalTerm} {out : Theorem} (semantics : AssumeSemantics term out) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  ofThmOpen
    (by
      obtain ⟨-, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_singleton]
      rfl)
    (by
      obtain ⟨-, -, -, conclEq⟩ := semantics
      rw [sequentConclusionP_of_term (congrArg CanonicalTerm.term conclEq)])
    (assumeCore calculus term (by obtain ⟨isBool, -⟩ := semantics; exact isBool))

theorem transLeftShape {left right out : Theorem} (semantics : TransSemantics left right out) :
    left.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqLeft left.sequent.concl.term) (eqRight left.sequent.concl.term) := by
  obtain ⟨_, _, _, _, _, ⟨-, shape⟩, -⟩ := semantics
  exact equalityDB_parts shape

theorem transRightShape {left right out : Theorem} (semantics : TransSemantics left right out) :
    right.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqRight left.sequent.concl.term) (eqRight right.sequent.concl.term) := by
  obtain ⟨first, middle, middle', last, _, ⟨firstTypes, leftShape⟩, ⟨-, rightShape⟩, rfl, -⟩ := semantics
  rw [rightShape, leftShape, eqOperand_equalityDB, eqRight_equalityDB, eqRight_equalityDB, firstTypes]

include calculus in
/-- `TRANS`. -/
def transStep {left right out : Theorem} (semantics : TransSemantics left right out)
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand left.sequent.concl.term)
      (eqLeft left.sequent.concl.term) (eqRight right.sequent.concl.term) := by
    obtain ⟨first, middle, middle', last, equality, ⟨-, leftShape⟩, ⟨-, rightShape⟩, rfl, ⟨-, shape⟩, -, -, conclEq⟩ :=
      semantics
    rw [conclEq, shape, leftShape, rightShape, eqOperand_equalityDB, eqLeft_equalityDB, eqRight_equalityDB]
  ofThmOpen
    (by
      obtain ⟨_, _, _, _, _, -, -, -, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (transCore calculus left right (transLeftShape semantics) (transRightShape semantics) leftDerived rightDerived)

theorem appFunctionShape {functions arguments out : Theorem}
    (semantics : AppSemantics functions arguments out) :
    functions.sequent.concl.term = CanonicalTerm.equalityDB
      (Ty.function (domainOf (eqOperand functions.sequent.concl.term))
        (codomainOf (eqOperand functions.sequent.concl.term)))
      (eqLeft functions.sequent.concl.term) (eqRight functions.sequent.concl.term) := by
  obtain ⟨leftFunction, rightFunction, leftArgument, rightArgument, leftApplication, rightApplication, equality,
    ⟨-, shape⟩, -, ⟨domain, codomain, recognized, -, -⟩, -⟩ := semantics
  have functionTyEq : leftFunction.ty = Ty.function domain codomain :=
    (Ty.destFunction?_eq_some_iff _ _ _).mp recognized
  rw [shape]
  simp only [eqOperand_equalityDB, eqLeft_equalityDB, eqRight_equalityDB]
  rw [functionTyEq, domainOf_function, codomainOf_function]

theorem appArgumentShape {functions arguments out : Theorem}
    (semantics : AppSemantics functions arguments out) :
    arguments.sequent.concl.term = CanonicalTerm.equalityDB
      (domainOf (eqOperand functions.sequent.concl.term))
      (eqLeft arguments.sequent.concl.term) (eqRight arguments.sequent.concl.term) := by
  obtain ⟨leftFunction, rightFunction, leftArgument, rightArgument, leftApplication, rightApplication, equality,
    ⟨-, functionShape⟩, ⟨-, argumentShape⟩, ⟨domain, codomain, recognized, domainEq, -⟩, -⟩ := semantics
  have functionTyEq : leftFunction.ty = Ty.function domain codomain :=
    (Ty.destFunction?_eq_some_iff _ _ _).mp recognized
  rw [argumentShape, functionShape]
  simp only [eqOperand_equalityDB, eqLeft_equalityDB, eqRight_equalityDB]
  rw [functionTyEq, domainOf_function, domainEq]

include calculus in
/-- `MK_COMB`. -/
def mkCombStep {functions arguments out : Theorem} (semantics : AppSemantics functions arguments out)
    (functionsDerived : OpenDerivation definition context (sequentJ functions.sequent))
    (argumentsDerived : OpenDerivation definition context (sequentJ arguments.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB
      (codomainOf (eqOperand functions.sequent.concl.term))
      (.app (eqLeft functions.sequent.concl.term) (eqLeft arguments.sequent.concl.term))
      (.app (eqRight functions.sequent.concl.term) (eqRight arguments.sequent.concl.term)) := by
    obtain ⟨leftFunction, rightFunction, leftArgument, rightArgument, leftApplication, rightApplication, equality,
      ⟨-, functionShape⟩, ⟨-, argumentShape⟩, ⟨domain, codomain, recognized, -, leftApplied⟩,
      ⟨-, -, -, -, rightApplied⟩, ⟨-, shape⟩, -, -, conclEq⟩ := semantics
    have functionTyEq : leftFunction.ty = Ty.function domain codomain :=
      (Ty.destFunction?_eq_some_iff _ _ _).mp recognized
    have codomainEq : leftApplication.ty = codomain := by
      have typed := leftApplication.checked
      rw [leftApplied] at typed
      obtain ⟨domain'', functionTyped, argumentTyped⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
      rw [leftFunction.checked, functionTyEq] at functionTyped
      exact ((Ty.function_inj (Option.some.inj functionTyped)).2).symm
    rw [conclEq, shape, codomainEq, leftApplied, rightApplied, functionShape, argumentShape]
    simp only [eqOperand_equalityDB, eqLeft_equalityDB, eqRight_equalityDB]
    rw [functionTyEq, codomainOf_function]
  ofThmOpen
    (by
      obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (mkCombCore calculus functions arguments (appFunctionShape semantics) (appArgumentShape semantics) functionsDerived
      argumentsDerived)

theorem absInputShape {binder : SourceVar} {input out : Theorem} (semantics : AbsSemantics binder input out) :
    input.sequent.concl.term = CanonicalTerm.equalityDB (eqOperand input.sequent.concl.term)
      (eqLeft input.sequent.concl.term) (eqRight input.sequent.concl.term) := by
  obtain ⟨-, _, _, _, _, _, ⟨-, shape⟩, -⟩ := semantics
  exact equalityDB_parts shape

theorem absAbsent {binder : SourceVar} {input out : Theorem} (semantics : AbsSemantics binder input out) :
    ∀ term ∈ (sortedHypotheses input.sequent.hyp).map CanonicalTerm.term, DBTerm.hasFree binder term = false := by
  obtain ⟨notFree, -⟩ := semantics
  intro term member
  obtain ⟨hypothesis, hypothesisMember, rfl⟩ := List.mem_map.mp member
  cases occurs : DBTerm.hasFree binder hypothesis.term
  · rfl
  · exact absurd ⟨hypothesis, by simpa [sortedHypotheses] using hypothesisMember,
      (DBTerm.hasFree_eq_true_iff _ _).mp occurs⟩ notFree

include calculus in
/-- `ABS`. -/
def absStep {binder : SourceVar} {input out : Theorem} (semantics : AbsSemantics binder input out)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB
      (Ty.function binder.ty (eqOperand input.sequent.concl.term))
      (.abs binder.ty (DBTerm.closeFreeAt binder 0 (eqLeft input.sequent.concl.term)))
      (.abs binder.ty (DBTerm.closeFreeAt binder 0 (eqRight input.sequent.concl.term))) := by
    obtain ⟨-, left, right, leftAbs, rightAbs, equality, ⟨-, inputShape⟩, leftAbstracted, rightAbstracted,
      ⟨-, shape⟩, -, -, conclEq⟩ := semantics
    have leftAbsEq : leftAbs = left.abstractFree binder := CanonicalTerm.ext_term leftAbstracted
    have rightAbsEq : rightAbs = right.abstractFree binder := CanonicalTerm.ext_term rightAbstracted
    subst leftAbsEq rightAbsEq
    rw [conclEq, shape, inputShape]
    simp only [eqOperand_equalityDB, eqLeft_equalityDB, eqRight_equalityDB]
    rfl
  ofThmOpen
    (by
      obtain ⟨-, _, _, _, _, _, -, -, -, -, -, hypEq, -⟩ := semantics
      unfold sequentHypothesesP
      rw [hypEq])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (absCore calculus binder input (absInputShape semantics) (absAbsent semantics) inputDerived)

include calculus in
/-- `BETA` at the redex `(λx. t) x`, with its parts given. -/
def betaStepAt {source : CheckedSourceTerm} {out : Theorem} (name : Name) (type : Ty) (bodySource : SourceTerm)
    (sourceShape : source.source = .app (.abs name type bodySource) (.var name type))
    (semantics : SourceBetaSemantics source out) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have toDBEq : source.source.toDB [] =
      .app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩) := by
    rw [sourceShape]
    simp [SourceTerm.toDB, boundIndex]
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB source.ty
      (.app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩))
      (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])) := by
    obtain ⟨-, reduced, equality, ⟨domain, body, argument, wholeShape, reducedShape⟩, ⟨-, shape⟩, -, -,
      conclEq⟩ := semantics
    have redexTerm : source.canonical.term =
        .app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩) := toDBEq
    rw [redexTerm] at wholeShape
    injection wholeShape with functionEq argumentEq
    injection functionEq with domainEq bodyEq
    have reducedTerm : reduced.term =
        DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩]) := by
      rw [reducedShape, ← argumentEq, ← bodyEq]
    rw [conclEq, shape, ← redexTerm, ← reducedTerm]
    rfl
  ofThmOpen
    (by
      obtain ⟨-, _, _, -, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_empty]
      rfl)
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (betaCore calculus source name type bodySource sourceShape)

theorem redex_parts {source : SourceTerm} (trivial : TrivialBetaRedex source) :
    source = .app (.abs (redexBinder source).name (redexBinder source).ty (redexBody source))
      (.var (redexBinder source).name (redexBinder source).ty) := by
  obtain ⟨name, type, body, shape⟩ := trivialBetaRedex_shape trivial
  subst shape
  rfl

include calculus in
/-- `BETA`. -/
def betaStep {source : CheckedSourceTerm} {out : Theorem} (semantics : SourceBetaSemantics source out) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  betaStepAt calculus (redexBinder source.source).name (redexBinder source.source).ty (redexBody source.source)
    (redex_parts semantics.1) semantics

theorem eqMpEqualityShape {equality premise out : Theorem} (semantics : EqMpSemantics equality premise out) :
    equality.sequent.concl.term = CanonicalTerm.equalityDB
      (eqOperand equality.sequent.concl.term) (eqLeft equality.sequent.concl.term)
      (eqRight equality.sequent.concl.term) := by
  obtain ⟨_, _, ⟨-, shape⟩, -⟩ := semantics
  exact equalityDB_parts shape

theorem eqMpPremiseShape {equality premise out : Theorem} (semantics : EqMpSemantics equality premise out) :
    premise.sequent.concl.term = eqLeft equality.sequent.concl.term := by
  obtain ⟨left, right, ⟨-, shape⟩, same, -⟩ := semantics
  rw [shape, eqLeft_equalityDB, same]

include calculus in
/-- `EQ_MP`. -/
def eqMpStep {equality premise out : Theorem} (semantics : EqMpSemantics equality premise out)
    (equalityDerived : OpenDerivation definition context (sequentJ equality.sequent))
    (premiseDerived : OpenDerivation definition context (sequentJ premise.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have conclusionTerm : out.sequent.concl.term = eqRight equality.sequent.concl.term := by
    obtain ⟨left, right, ⟨-, shape⟩, -, -, -, conclEq⟩ := semantics
    rw [shape, eqRight_equalityDB, conclEq]
  ofThmOpen
    (by
      obtain ⟨_, _, -, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm])
    (eqMpCore calculus equality premise (eqMpEqualityShape semantics) (eqMpPremiseShape semantics) equalityDerived
      premiseDerived)

include calculus in
/-- `DEDUCT_ANTISYM_RULE`. -/
def deductAntisymStep {left right out : Theorem} (semantics : DeductAntisymSemantics left right out)
    (leftDerived : OpenDerivation definition context (sequentJ left.sequent))
    (rightDerived : OpenDerivation definition context (sequentJ right.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB left.sequent.concl.ty
      left.sequent.concl.term right.sequent.concl.term := by
    obtain ⟨equality, ⟨-, shape⟩, -, -, conclEq⟩ := semantics
    rw [conclEq, shape]
  ofThmOpen
    (by
      obtain ⟨_, -, -, hypEq, -⟩ := semantics
      rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deductAntisymCore calculus left right (by obtain ⟨_, ⟨types, -⟩, -⟩ := semantics; exact types)
      leftDerived rightDerived)

include calculus in
/-- `INST`. -/
def instStep {maplets : List SourceSubstitution.TermMaplet} {input out : Theorem}
    (semantics : ∃ substitution, SourceSubstitution.admitTermSubstitution maplets = some substitution ∧
      TheoremSubstitutionSemantics substitution input out)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  ofThmOpen
    (by
      obtain ⟨substitution, admitted, -, hypothesesImage, -⟩ := semantics
      have action : ∀ term : DBTerm,
          substitution.raw.applyDB term = tableAction (SourceSubstitution.termEntries maplets) term := by
        intro term
        rw [SourceSubstitution.admittedTermSubstitution_raw admitted]
        rfl
      have hypEq : out.sequent.hyp = input.sequent.hyp.image substitution.apply := by
        ext term
        rw [hypothesesImage term, Finset.mem_image]
        constructor
        · rintro ⟨source, member, termEq⟩
          exact ⟨source, member, CanonicalTerm.ext_term termEq.symm⟩
        · rintro ⟨source, member, rfl⟩
          exact ⟨source, member, rfl⟩
      unfold actedHypotheses
      rw [treeSort_image_hypothesisTrees _ (apply := substitution.apply) (fun term => action term.term), ← hypEq,
        sequentHypothesesP_eq_treesP])
    (by
      obtain ⟨substitution, admitted, -, -, conclusionImage⟩ := semantics
      have action : ∀ term : DBTerm,
          substitution.raw.applyDB term = tableAction (SourceSubstitution.termEntries maplets) term := by
        intro term
        rw [SourceSubstitution.admittedTermSubstitution_raw admitted]
        rfl
      rw [sequentConclusionP_of_term conclusionImage, action])
    (instCore calculus maplets input
      (by
        obtain ⟨substitution, admitted, -⟩ := semantics
        exact (SourceSubstitution.admitTermSubstitution_isSome_iff maplets).mp (by rw [admitted]; rfl))
      inputDerived)

include calculus in
/-- `INST_TYPE`. -/
def instTypeStep {entries : List (Ty × Ty)} {input out : Theorem}
    (semantics : TheoremSubstitutionSemantics (SourceSubstitution.typeOnlySubstitution entries) input out)
    (inputDerived : OpenDerivation definition context (sequentJ input.sequent)) :
    OpenDerivation definition context (sequentJ out.sequent) :=
  ofThmOpen
    (by
      obtain ⟨-, hypothesesImage, -⟩ := semantics
      have hypEq : out.sequent.hyp =
          input.sequent.hyp.image (SourceSubstitution.typeOnlySubstitution entries).apply := by
        ext term
        rw [hypothesesImage term, Finset.mem_image]
        constructor
        · rintro ⟨source, member, termEq⟩
          exact ⟨source, member, CanonicalTerm.ext_term termEq.symm⟩
        · rintro ⟨source, member, rfl⟩
          exact ⟨source, member, rfl⟩
      unfold actedHypotheses
      rw [treeSort_image_hypothesisTrees _ (apply := (SourceSubstitution.typeOnlySubstitution entries).apply)
        (fun term => applyDB_typeOnly entries term.term), ← hypEq, sequentHypothesesP_eq_treesP])
    (by
      obtain ⟨-, -, conclusionImage⟩ := semantics
      rw [sequentConclusionP_of_term conclusionImage]
      exact congrArg (fun term => groundP (encodeTerm term)) (applyDB_typeOnly entries _).symm)
    (instTypeCore calculus entries input inputDerived)

include calculus in
/-- An axiom of the calculus. -/
def axiomStep {sequent : Sequent} (member : sequent ∈ axioms) {out : Theorem}
    (semantics : AxiomSemantics sequent out) : OpenDerivation definition context (sequentJ out.sequent) :=
  have outEq : out.sequent = sequent := by
    obtain ⟨-, -, hypEq, conclEq⟩ := semantics
    exact Sequent.ext hypEq conclEq
  recastOpen (congrArg sequentJ outEq.symm) (axiomCore calculus sequent member)

/-! ## A step for every rule -/

include calculus in
/-- The step of one inference, from open derivations of its premises in order. -/
def inferenceStep : (request : InferenceRequest) → {out : Theorem} → request.Semantics out →
    ((index : Fin request.premises.length) →
      OpenDerivation definition context (sequentJ (request.premises.get index).sequent)) →
    OpenDerivation definition context (sequentJ out.sequent)
  | .refl _, _, semantics, _ => reflStep calculus semantics
  | .assume _, _, semantics, _ => assumeStep calculus semantics
  | .trans _ _, _, semantics, premise =>
      transStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
        (premise ⟨1, by simp [InferenceRequest.premises]⟩)
  | .mkComb _ _, _, semantics, premise =>
      mkCombStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
        (premise ⟨1, by simp [InferenceRequest.premises]⟩)
  | .abs _ _, _, semantics, premise => absStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
  | .beta _, _, semantics, _ => betaStep calculus semantics
  | .eqMp _ _, _, semantics, premise =>
      eqMpStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
        (premise ⟨1, by simp [InferenceRequest.premises]⟩)
  | .deductAntisym _ _, _, semantics, premise =>
      deductAntisymStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
        (premise ⟨1, by simp [InferenceRequest.premises]⟩)
  | .instType _ _, _, semantics, premise =>
      instTypeStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)
  | .inst _ _, _, semantics, premise => instStep calculus semantics (premise ⟨0, by simp [InferenceRequest.premises]⟩)

include calculus in
/-- The step of one node: an inference, or an axiom the calculus lists. -/
def ruleStep {policy : AxiomPolicy} (inList : ∀ sequent, policy sequent → sequent ∈ axioms) :
    (request : RuleRequest) → {out : Theorem} → request.Semantics policy out →
    ((index : Fin request.premises.length) →
      OpenDerivation definition context (sequentJ (request.premises.get index).sequent)) →
    OpenDerivation definition context (sequentJ out.sequent)
  | .inference request, _, semantics, premise => inferenceStep calculus request semantics premise
  | .axiom sequent, _, semantics, _ => axiomStep calculus (inList sequent semantics.2.1) semantics.2.2

/-! ## Proofs a translation builds without the kernel

The proof of a node is the erasure of its core, built when structural comparisons on the
data succeed: the cited judgments stand at the cited positions, and the terms have the
shapes the rule reads. Under the rule's semantics every comparison succeeds and the proof
is the erasure of the node's step (`ruleProof_accepted`). -/

theorem eraseOpen_recastOpen {first second : Pattern} (same : first = second)
    (derivation : OpenDerivation definition context first) :
    (recastOpen same derivation).eraseOpen = derivation.eraseOpen := by
  subst same
  rfl

/-- An open derivation's erasure is accepted at every judgment equal to its own. -/
theorem accepted_of_derivation {goal goal' : Pattern} (same : goal' = goal)
    (derivation : OpenDerivation definition context goal') :
    checkOpenRaw definition context goal derivation.eraseOpen = true := by
  rw [← eraseOpen_recastOpen same derivation]
  exact checkOpenRaw_erase _

@[simp] theorem eraseOpen_ofThmOpen {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : hypotheses = sequentHypothesesP sequent) (conclusionEq : conclusion = sequentConclusionP sequent)
    (derivation : OpenDerivation definition context (thmJ hypotheses conclusion)) :
    (ofThmOpen hypothesesEq conclusionEq derivation).eraseOpen = derivation.eraseOpen :=
  eraseOpen_recastOpen _ derivation

/-- The premise hole at a position of the context, read at the judgment it holds. -/
def premiseLeaf (index : Nat) (goal : Pattern) : Option (OpenDerivation definition context goal) :=
  if bound : index < context.length then
    if same : context.get ⟨index, bound⟩ = goal then some (recastOpen same (.assumption ⟨index, bound⟩)) else none
  else none

theorem premiseLeaf_some {index : Nat} {goal : Pattern} (found : context[index]? = some goal) :
    ∃ leaf, premiseLeaf (definition := definition) (context := context) index goal = some leaf := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp found
  have same : context.get ⟨index, bound⟩ = goal := by simpa using value
  exact ⟨_, by unfold premiseLeaf; rw [dif_pos bound, dif_pos same]⟩

/-- The proof standing for a node the comparisons reject. -/
def noProof : RawOpenProof := .premise 0

include calculus in
/-- The proof of one inference from the context, citing the given positions. -/
def inferenceProof (parents : List Nat) : InferenceRequest → RawOpenProof
  | .refl term => (reflCore calculus (context := context) term).eraseOpen
  | .assume term =>
      if isBool : Ty.same term.ty Ty.bool = true then
        (assumeCore calculus (context := context) term ((Ty.same_eq_true_iff _ _).mp isBool)).eraseOpen
      else noProof
  | .trans left right =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0) (sequentJ left.sequent),
        premiseLeaf (definition := definition) (context := context) (parents.getD 1 0) (sequentJ right.sequent) with
      | some leftLeaf, some rightLeaf =>
          if leftShape : DBTerm.same left.sequent.concl.term (CanonicalTerm.equalityDB
              (eqOperand left.sequent.concl.term) (eqLeft left.sequent.concl.term)
              (eqRight left.sequent.concl.term)) = true then
            if rightShape : DBTerm.same right.sequent.concl.term (CanonicalTerm.equalityDB
                (eqOperand left.sequent.concl.term) (eqRight left.sequent.concl.term)
                (eqRight right.sequent.concl.term)) = true then
              (transCore calculus left right ((DBTerm.same_eq_true_iff _ _).mp leftShape)
                ((DBTerm.same_eq_true_iff _ _).mp rightShape) leftLeaf rightLeaf).eraseOpen
            else noProof
          else noProof
      | _, _ => noProof
  | .mkComb functions arguments =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0)
          (sequentJ functions.sequent),
        premiseLeaf (definition := definition) (context := context) (parents.getD 1 0)
          (sequentJ arguments.sequent) with
      | some functionsLeaf, some argumentsLeaf =>
          if functionShape : DBTerm.same functions.sequent.concl.term (CanonicalTerm.equalityDB
              (Ty.function (domainOf (eqOperand functions.sequent.concl.term))
                (codomainOf (eqOperand functions.sequent.concl.term)))
              (eqLeft functions.sequent.concl.term) (eqRight functions.sequent.concl.term)) = true then
            if argumentShape : DBTerm.same arguments.sequent.concl.term (CanonicalTerm.equalityDB
                (domainOf (eqOperand functions.sequent.concl.term))
                (eqLeft arguments.sequent.concl.term) (eqRight arguments.sequent.concl.term)) = true then
              (mkCombCore calculus functions arguments ((DBTerm.same_eq_true_iff _ _).mp functionShape)
                ((DBTerm.same_eq_true_iff _ _).mp argumentShape) functionsLeaf argumentsLeaf).eraseOpen
            else noProof
          else noProof
      | _, _ => noProof
  | .abs binder input =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0) (sequentJ input.sequent) with
      | some inputLeaf =>
          if inputShape : DBTerm.same input.sequent.concl.term (CanonicalTerm.equalityDB
              (eqOperand input.sequent.concl.term) (eqLeft input.sequent.concl.term)
              (eqRight input.sequent.concl.term)) = true then
            if absent : ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).all
                (fun term => !DBTerm.hasFree binder term) = true then
              (absCore calculus binder input ((DBTerm.same_eq_true_iff _ _).mp inputShape)
                (fun term member => by simpa using List.all_eq_true.mp absent term member) inputLeaf).eraseOpen
            else noProof
          else noProof
      | none => noProof
  | .beta source =>
      if sourceShape : SourceTerm.same source.source (.app (.abs (redexBinder source.source).name
          (redexBinder source.source).ty (redexBody source.source))
          (.var (redexBinder source.source).name (redexBinder source.source).ty)) = true then
        (betaCore calculus (context := context) source (redexBinder source.source).name (redexBinder source.source).ty
          (redexBody source.source) ((SourceTerm.same_eq_true_iff _ _).mp sourceShape)).eraseOpen
      else noProof
  | .eqMp equality premise =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0)
          (sequentJ equality.sequent),
        premiseLeaf (definition := definition) (context := context) (parents.getD 1 0)
          (sequentJ premise.sequent) with
      | some equalityLeaf, some premiseLeaf =>
          if equalityShape : DBTerm.same equality.sequent.concl.term (CanonicalTerm.equalityDB
              (eqOperand equality.sequent.concl.term) (eqLeft equality.sequent.concl.term)
              (eqRight equality.sequent.concl.term)) = true then
            if premiseShape : DBTerm.same premise.sequent.concl.term (eqLeft equality.sequent.concl.term) = true then
              (eqMpCore calculus equality premise ((DBTerm.same_eq_true_iff _ _).mp equalityShape)
                ((DBTerm.same_eq_true_iff _ _).mp premiseShape) equalityLeaf premiseLeaf).eraseOpen
            else noProof
          else noProof
      | _, _ => noProof
  | .deductAntisym left right =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0) (sequentJ left.sequent),
        premiseLeaf (definition := definition) (context := context) (parents.getD 1 0) (sequentJ right.sequent) with
      | some leftLeaf, some rightLeaf =>
          if types : Ty.same left.sequent.concl.ty right.sequent.concl.ty = true then
            (deductAntisymCore calculus left right ((Ty.same_eq_true_iff _ _).mp types) leftLeaf rightLeaf).eraseOpen
          else noProof
      | _, _ => noProof
  | .instType entries input =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0) (sequentJ input.sequent) with
      | some inputLeaf => (instTypeCore calculus entries input inputLeaf).eraseOpen
      | none => noProof
  | .inst maplets input =>
      match premiseLeaf (definition := definition) (context := context) (parents.getD 0 0) (sequentJ input.sequent) with
      | some inputLeaf =>
          if admissible : maplets.all SourceSubstitution.termMapletB = true then
            (instCore calculus maplets input
              ((SourceSubstitution.all_termMapletB_eq_true_iff maplets).mp admissible) inputLeaf).eraseOpen
          else noProof
      | none => noProof

include calculus in
/-- The proof of one node: an inference, or an axiom the calculus lists. -/
def ruleProof (parents : List Nat) : RuleRequest → RawOpenProof
  | .inference request => inferenceProof calculus (context := context) parents request
  | .axiom sequent =>
      if member : sequent ∈ axioms then (axiomCore calculus (context := context) sequent member).eraseOpen
      else noProof

include calculus in
/-- **Under its semantics, the proof of an inference is accepted at the node's sequent**, when
the cited positions hold the renderings of its premises. -/
theorem inferenceProof_accepted (parents : List Nat) : ∀ (request : InferenceRequest) {out : Theorem},
    request.Semantics out →
    (∀ index : Fin request.premises.length,
      context[parents.getD index 0]? = some (sequentJ (request.premises.get index).sequent)) →
    checkOpenRaw definition context (sequentJ out.sequent)
      (inferenceProof calculus (context := context) parents request) = true
  | .refl term, out, semantics, _ => by
      have accepted := checkOpenRaw_erase (reflStep calculus (context := context) semantics)
      simp only [reflStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof]
      exact accepted
  | .assume term, out, semantics, _ => by
      have accepted := checkOpenRaw_erase (assumeStep calculus (context := context) semantics)
      simp only [assumeStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof]
      rw [dif_pos ((Ty.same_eq_true_iff _ _).mpr semantics.1)]
      exact accepted
  | .trans left right, out, semantics, premises => by
      have leftAt : context[parents.getD 0 0]? = some (sequentJ left.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      have rightAt : context[parents.getD 1 0]? = some (sequentJ right.sequent) :=
        premises ⟨1, by simp [InferenceRequest.premises]⟩
      obtain ⟨leftLeaf, leftFound⟩ := premiseLeaf_some (definition := definition) leftAt
      obtain ⟨rightLeaf, rightFound⟩ := premiseLeaf_some (definition := definition) rightAt
      have accepted := checkOpenRaw_erase (transStep calculus semantics leftLeaf rightLeaf)
      simp only [transStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, leftFound, rightFound]
      rw [dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (transLeftShape semantics)),
        dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (transRightShape semantics))]
      exact accepted
  | .mkComb functions arguments, out, semantics, premises => by
      have functionsAt : context[parents.getD 0 0]? = some (sequentJ functions.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      have argumentsAt : context[parents.getD 1 0]? = some (sequentJ arguments.sequent) :=
        premises ⟨1, by simp [InferenceRequest.premises]⟩
      obtain ⟨functionsLeaf, functionsFound⟩ := premiseLeaf_some (definition := definition) functionsAt
      obtain ⟨argumentsLeaf, argumentsFound⟩ := premiseLeaf_some (definition := definition) argumentsAt
      have accepted := checkOpenRaw_erase (mkCombStep calculus semantics functionsLeaf argumentsLeaf)
      simp only [mkCombStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, functionsFound, argumentsFound]
      rw [dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (appFunctionShape semantics)),
        dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (appArgumentShape semantics))]
      exact accepted
  | .abs binder input, out, semantics, premises => by
      have inputAt : context[parents.getD 0 0]? = some (sequentJ input.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      obtain ⟨inputLeaf, inputFound⟩ := premiseLeaf_some (definition := definition) inputAt
      have accepted := checkOpenRaw_erase (absStep calculus semantics inputLeaf)
      simp only [absStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, inputFound]
      rw [dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (absInputShape semantics)),
        dif_pos (List.all_eq_true.mpr fun term member => by simp [absAbsent semantics term member])]
      exact accepted
  | .beta source, out, semantics, _ => by
      have accepted := checkOpenRaw_erase (betaStep calculus (context := context) semantics)
      simp only [betaStep, betaStepAt, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof]
      rw [dif_pos ((SourceTerm.same_eq_true_iff _ _).mpr (redex_parts semantics.1))]
      exact accepted
  | .eqMp equality premise, out, semantics, premises => by
      have equalityAt : context[parents.getD 0 0]? = some (sequentJ equality.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      have premiseAt : context[parents.getD 1 0]? = some (sequentJ premise.sequent) :=
        premises ⟨1, by simp [InferenceRequest.premises]⟩
      obtain ⟨equalityLeaf, equalityFound⟩ := premiseLeaf_some (definition := definition) equalityAt
      obtain ⟨premiseLeaf', premiseFound⟩ := premiseLeaf_some (definition := definition) premiseAt
      have accepted := checkOpenRaw_erase (eqMpStep calculus semantics equalityLeaf premiseLeaf')
      simp only [eqMpStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, equalityFound, premiseFound]
      rw [dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (eqMpEqualityShape semantics)),
        dif_pos ((DBTerm.same_eq_true_iff _ _).mpr (eqMpPremiseShape semantics))]
      exact accepted
  | .deductAntisym left right, out, semantics, premises => by
      have leftAt : context[parents.getD 0 0]? = some (sequentJ left.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      have rightAt : context[parents.getD 1 0]? = some (sequentJ right.sequent) :=
        premises ⟨1, by simp [InferenceRequest.premises]⟩
      obtain ⟨leftLeaf, leftFound⟩ := premiseLeaf_some (definition := definition) leftAt
      obtain ⟨rightLeaf, rightFound⟩ := premiseLeaf_some (definition := definition) rightAt
      have accepted := checkOpenRaw_erase (deductAntisymStep calculus semantics leftLeaf rightLeaf)
      simp only [deductAntisymStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, leftFound, rightFound]
      have types : left.sequent.concl.ty = right.sequent.concl.ty := by
        obtain ⟨_, ⟨types, -⟩, -⟩ := semantics
        exact types
      rw [dif_pos ((Ty.same_eq_true_iff _ _).mpr types)]
      exact accepted
  | .instType entries input, out, semantics, premises => by
      have inputAt : context[parents.getD 0 0]? = some (sequentJ input.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      obtain ⟨inputLeaf, inputFound⟩ := premiseLeaf_some (definition := definition) inputAt
      have accepted := checkOpenRaw_erase (instTypeStep calculus semantics inputLeaf)
      simp only [instTypeStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, inputFound]
      exact accepted
  | .inst maplets input, out, semantics, premises => by
      have inputAt : context[parents.getD 0 0]? = some (sequentJ input.sequent) :=
        premises ⟨0, by simp [InferenceRequest.premises]⟩
      obtain ⟨inputLeaf, inputFound⟩ := premiseLeaf_some (definition := definition) inputAt
      have accepted := checkOpenRaw_erase (instStep calculus semantics inputLeaf)
      simp only [instStep, eraseOpen_ofThmOpen] at accepted
      simp only [inferenceProof, inputFound]
      have admissible : maplets.all SourceSubstitution.termMapletB = true := by
        obtain ⟨substitution, admitted, -⟩ := semantics
        exact (SourceSubstitution.all_termMapletB_eq_true_iff maplets).mpr
          ((SourceSubstitution.admitTermSubstitution_isSome_iff maplets).mp (by rw [admitted]; rfl))
      rw [dif_pos admissible]
      exact accepted

include calculus in
/-- **Under its semantics, the proof of a node is accepted at the node's sequent.** -/
theorem ruleProof_accepted {policy : AxiomPolicy} (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    (parents : List Nat) : ∀ (request : RuleRequest) {out : Theorem}, request.Semantics policy out →
    (∀ index : Fin request.premises.length,
      context[parents.getD index 0]? = some (sequentJ (request.premises.get index).sequent)) →
    checkOpenRaw definition context (sequentJ out.sequent) (ruleProof calculus (context := context) parents request) = true
  | .inference request, _, semantics, premises => inferenceProof_accepted calculus parents request semantics premises
  | .axiom sequent, _, semantics, _ => by
      have accepted := checkOpenRaw_erase
        (axiomStep calculus (context := context) (inList sequent semantics.2.1) semantics.2.2)
      simp only [axiomStep, eraseOpen_recastOpen] at accepted
      simp only [ruleProof]
      rw [dif_pos (inList sequent semantics.2.1)]
      exact accepted

end Calculus

end Mettapedia.Languages.HOLLight.FirstOrder
