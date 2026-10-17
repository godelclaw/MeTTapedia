import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumSyntax
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSum
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumRules
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentInterpretation

/-!
# Combining primitive alphabets without changing their meanings

The semantic scopes and values of each original declaration are retained.
The comparison traverses all expressions, including dependent binders,
logical assumptions and mixed substitutions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

open _root_.CategoryTheory Mettapedia.TypeTheory
open External (bindResult)

universe u v w
variable {S : Symbols.{v}} {T : Symbols.{w}} {C : Type u} [Category.{u} C]

/-- The two declaration alphabets share the same semantic world category. -/
def model (left : ModelData S C) (right : ModelData T C) : ModelData (symbols S T) C where
  typeParameters := fun symbol => match symbol with
    | .inl symbol => left.typeParameters symbol
    | .inr symbol => right.typeParameters symbol
  typeFamily := fun symbol => match symbol with
    | .inl symbol => left.typeFamily symbol
    | .inr symbol => right.typeFamily symbol
  termParameters := fun symbol => match symbol with
    | .inl symbol => left.termParameters symbol
    | .inr symbol => right.termParameters symbol
  termType := fun symbol => match symbol with
    | .inl symbol => left.termType symbol
    | .inr symbol => right.termType symbol
  termValue := fun symbol => match symbol with
    | .inl symbol => left.termValue symbol
    | .inr symbol => right.termValue symbol
  predicateParameters := fun symbol => match symbol with
    | .inl symbol => left.predicateParameters symbol
    | .inr symbol => right.predicateParameters symbol
  predicateValue := fun symbol => match symbol with
    | .inl symbol => left.predicateValue symbol
    | .inr symbol => right.predicateValue symbol

variable (left : ModelData S C) (right : ModelData T C)

@[simp] theorem typeParameters_left (symbol : S.TypeSymbol) : (model left right).typeParameters (.inl symbol) = left.typeParameters symbol := rfl
@[simp] theorem termParameters_left (symbol : S.TermSymbol) : (model left right).termParameters (.inl symbol) = left.termParameters symbol := rfl
@[simp] theorem predicateParameters_left (symbol : S.PredicateSymbol) : (model left right).predicateParameters (.inl symbol) = left.predicateParameters symbol := rfl
@[simp] theorem familyAt_left {P : Cᵒᵖ ⥤ Type u} (symbol : S.TypeSymbol) (arguments : P ⟶ (left.typeParameters symbol).1) : (model left right).familyAt (.inl symbol) arguments = left.familyAt symbol arguments := rfl
@[simp] theorem primitiveAt_left {P : Cᵒᵖ ⥤ Type u} (symbol : S.TermSymbol) (arguments : P ⟶ (left.termParameters symbol).1) : (model left right).primitiveAt (.inl symbol) arguments = left.primitiveAt symbol arguments := rfl
@[simp] theorem predicateAt_left {P : Cᵒᵖ ⥤ Type u} (symbol : S.PredicateSymbol) (arguments : P ⟶ (left.predicateParameters symbol).1) : (model left right).predicateAt (.inl symbol) arguments = left.predicateAt symbol arguments := rfl
@[simp] theorem typeParameters_right (symbol : T.TypeSymbol) : (model left right).typeParameters (.inr symbol) = right.typeParameters symbol := rfl
@[simp] theorem termParameters_right (symbol : T.TermSymbol) : (model left right).termParameters (.inr symbol) = right.termParameters symbol := rfl
@[simp] theorem predicateParameters_right (symbol : T.PredicateSymbol) : (model left right).predicateParameters (.inr symbol) = right.predicateParameters symbol := rfl
@[simp] theorem familyAt_right {P : Cᵒᵖ ⥤ Type u} (symbol : T.TypeSymbol) (arguments : P ⟶ (right.typeParameters symbol).1) : (model left right).familyAt (.inr symbol) arguments = right.familyAt symbol arguments := rfl
@[simp] theorem primitiveAt_right {P : Cᵒᵖ ⥤ Type u} (symbol : T.TermSymbol) (arguments : P ⟶ (right.termParameters symbol).1) : (model left right).primitiveAt (.inr symbol) arguments = right.primitiveAt symbol arguments := rfl
@[simp] theorem predicateAt_right {P : Cᵒᵖ ⥤ Type u} (symbol : T.PredicateSymbol) (arguments : P ⟶ (right.predicateParameters symbol).1) : (model left right).predicateAt (.inr symbol) arguments = right.predicateAt symbol arguments := rfl

mutual
@[simp] theorem evaluateType_left : {n : Nat} →
    (expression : TypeExpr S n) → (scope : Scope C n) →
      (model left right).evaluateType scope (typeLeft expression) =
        left.evaluateType scope expression
  | _, .family symbol arguments, scope => by
      simp only [typeLeft, ModelData.evaluateType, evaluateTerm_left]; rfl
  | _, .propositions, scope => rfl
  | _, .pi domain body, scope => by
      simp only [typeLeft, ModelData.evaluateType, evaluateType_left]; rfl
  | _, .sigma domain body, scope => by
      simp only [typeLeft, ModelData.evaluateType, evaluateType_left]; rfl
  | _, .comprehension domain predicate, scope => by
      simp only [typeLeft, ModelData.evaluateType, evaluateType_left, evaluatePredicateLift_left]
@[simp] theorem evaluateTerm_left : {n : Nat} →
    (expression : TermExpr S n) → (scope : Scope C n) →
      (model left right).evaluateTerm scope (termLeft expression) =
        left.evaluateTerm scope expression
  | _, .var index, scope => rfl
  | _, .primitive symbol arguments, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateTerm_left]; rfl
  | _, .lam domain codomain body, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left]; rfl
  | _, .app domain body function argument, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left]; rfl
  | _, .pair domain body first second, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left]; rfl
  | _, .fst domain body pair, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left]; rfl
  | _, .snd domain body pair, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left]; rfl
  | _, .sigmaElim domain body motive branch pair, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluateTerm_left, ModelData.sumEliminate?, ModelData.sums]
  | _, .quote predicate, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluatePredicateLift_left]
  | _, .refine domain predicate value, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluatePredicateLift_left, evaluateTerm_left]
  | _, .forget domain predicate value, scope => by
      simp only [termLeft, ModelData.evaluateTerm, evaluateType_left, evaluatePredicateLift_left, evaluateTerm_left]
@[simp] theorem evaluatePredicateLift_left : {n : Nat} →
    (expression : PropExpr S n) → (scope : Scope C n) →
      (model left right).evaluatePredicateLift scope (propLeft expression) =
        left.evaluatePredicateLift scope expression
  | _, .atom symbol arguments, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluateTerm_left]; rfl
  | _, .truth, scope => rfl
  | _, .falsehood, scope => rfl
  | _, .and first second, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluatePredicateLift_left]
  | _, .or first second, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluatePredicateLift_left]
  | _, .implies first second, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluatePredicateLift_left]
  | _, .all domain predicate, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluateType_left, evaluatePredicateLift_left]
  | _, .exists domain predicate, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluateType_left, evaluatePredicateLift_left]
  | _, .holds term, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluateTerm_left]
  | _, .image type, scope => by
      simp only [propLeft, ModelData.evaluatePredicateLift, evaluateType_left]

end

@[simp] theorem evaluatePredicate_left {n : Nat}
    (expression : PropExpr S n) (scope : Scope C n) :
    (model left right).evaluatePredicate scope (propLeft expression) =
      left.evaluatePredicate scope expression := by
  unfold ModelData.evaluatePredicate
  rw [evaluatePredicateLift_left]

@[simp] theorem evaluateContext_left : {n : Nat} →
    (context : ContextExpr S n) →
      (model left right).evaluateContext (contextLeft context) = left.evaluateContext context
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [contextLeft, ModelData.evaluateContext, evaluateContext_left, evaluateType_left]
  | _, .assume previous predicate => by
      simp only [contextLeft, ModelData.evaluateContext, evaluateContext_left, evaluatePredicate_left]

@[simp] theorem evaluateSubstitution_left {n m : Nat} (source : Scope C n)
    (target : Scope C m) (mapping : Substitution S m n) :
    (model left right).evaluateSubstitution source target (fun position => termLeft (mapping position)) =
      left.evaluateSubstitution source target mapping := by
  unfold ModelData.evaluateSubstitution
  congr 1
  funext position
  exact evaluateTerm_left left right (mapping position) source

mutual
@[simp] theorem evaluateType_right : {n : Nat} →
    (expression : TypeExpr T n) → (scope : Scope C n) →
      (model left right).evaluateType scope (typeRight expression) =
        right.evaluateType scope expression
  | _, .family symbol arguments, scope => by
      simp only [typeRight, ModelData.evaluateType, evaluateTerm_right]; rfl
  | _, .propositions, scope => rfl
  | _, .pi domain body, scope => by
      simp only [typeRight, ModelData.evaluateType, evaluateType_right]; rfl
  | _, .sigma domain body, scope => by
      simp only [typeRight, ModelData.evaluateType, evaluateType_right]; rfl
  | _, .comprehension domain predicate, scope => by
      simp only [typeRight, ModelData.evaluateType, evaluateType_right, evaluatePredicateLift_right]
@[simp] theorem evaluateTerm_right : {n : Nat} →
    (expression : TermExpr T n) → (scope : Scope C n) →
      (model left right).evaluateTerm scope (termRight expression) =
        right.evaluateTerm scope expression
  | _, .var index, scope => rfl
  | _, .primitive symbol arguments, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateTerm_right]; rfl
  | _, .lam domain codomain body, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right]; rfl
  | _, .app domain body function argument, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right]; rfl
  | _, .pair domain body first second, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right]; rfl
  | _, .fst domain body pair, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right]; rfl
  | _, .snd domain body pair, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right]; rfl
  | _, .sigmaElim domain body motive branch pair, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluateTerm_right, ModelData.sumEliminate?, ModelData.sums]
  | _, .quote predicate, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluatePredicateLift_right]
  | _, .refine domain predicate value, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluatePredicateLift_right, evaluateTerm_right]
  | _, .forget domain predicate value, scope => by
      simp only [termRight, ModelData.evaluateTerm, evaluateType_right, evaluatePredicateLift_right, evaluateTerm_right]
@[simp] theorem evaluatePredicateLift_right : {n : Nat} →
    (expression : PropExpr T n) → (scope : Scope C n) →
      (model left right).evaluatePredicateLift scope (propRight expression) =
        right.evaluatePredicateLift scope expression
  | _, .atom symbol arguments, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluateTerm_right]; rfl
  | _, .truth, scope => rfl
  | _, .falsehood, scope => rfl
  | _, .and first second, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluatePredicateLift_right]
  | _, .or first second, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluatePredicateLift_right]
  | _, .implies first second, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluatePredicateLift_right]
  | _, .all domain predicate, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluateType_right, evaluatePredicateLift_right]
  | _, .exists domain predicate, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluateType_right, evaluatePredicateLift_right]
  | _, .holds term, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluateTerm_right]
  | _, .image type, scope => by
      simp only [propRight, ModelData.evaluatePredicateLift, evaluateType_right]

end

@[simp] theorem evaluatePredicate_right {n : Nat}
    (expression : PropExpr T n) (scope : Scope C n) :
    (model left right).evaluatePredicate scope (propRight expression) =
      right.evaluatePredicate scope expression := by
  unfold ModelData.evaluatePredicate
  rw [evaluatePredicateLift_right]

@[simp] theorem evaluateContext_right : {n : Nat} →
    (context : ContextExpr T n) →
      (model left right).evaluateContext (contextRight context) = right.evaluateContext context
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [contextRight, ModelData.evaluateContext, evaluateContext_right, evaluateType_right]
  | _, .assume previous predicate => by
      simp only [contextRight, ModelData.evaluateContext, evaluateContext_right, evaluatePredicate_right]

@[simp] theorem evaluateSubstitution_right {n m : Nat} (source : Scope C n)
    (target : Scope C m) (mapping : Substitution T m n) :
    (model left right).evaluateSubstitution source target (fun position => termRight (mapping position)) =
      right.evaluateSubstitution source target mapping := by
  unfold ModelData.evaluateSubstitution
  congr 1
  funext position
  exact evaluateTerm_right left right (mapping position) source

/-- Each component retains every native judgment, including equations,
entailments and dependent substitutions, with exactly the original meaning. -/
theorem interprets_left_iff {A B : Symbols.{v}}
    (first : ModelData A C) (second : ModelData B C) (judgment : Judgment A) :
    Interprets (model first second) (judgmentLeft judgment) ↔ Interprets first judgment := by
  cases judgment <;> simp [judgmentLeft, Interprets]

theorem interprets_right_iff {A B : Symbols.{v}}
    (first : ModelData A C) (second : ModelData B C) (judgment : Judgment B) :
    Interprets (model first second) (judgmentRight judgment) ↔ Interprets second judgment := by
  cases judgment <;> simp [judgmentRight, Interprets]

/-- The ordinary disjoint signature sum has the combined interpretation when
both original primitive interpretations realize their actual declarations. -/
theorem realization (leftSignature : Signature S) (rightSignature : Signature T)
    (leftRealized : SignatureRealization left leftSignature)
    (rightRealized : SignatureRealization right rightSignature) :
    SignatureRealization (model left right) (signature leftSignature rightSignature) where
  typeHeader symbol := by
    cases symbol with
    | inl symbol =>
        change (model left right).evaluateContext (contextLeft (leftSignature.typeParameters symbol)) =
          some (left.typeParameters symbol)
        rw [evaluateContext_left]
        exact leftRealized.typeHeader symbol
    | inr symbol =>
        change (model left right).evaluateContext (contextRight (rightSignature.typeParameters symbol)) =
          some (right.typeParameters symbol)
        rw [evaluateContext_right]
        exact rightRealized.typeHeader symbol
  termHeader symbol := by
    cases symbol with
    | inl symbol =>
        change (model left right).evaluateContext (contextLeft (leftSignature.termParameters symbol)) =
          some (left.termParameters symbol)
        rw [evaluateContext_left]
        exact leftRealized.termHeader symbol
    | inr symbol =>
        change (model left right).evaluateContext (contextRight (rightSignature.termParameters symbol)) =
          some (right.termParameters symbol)
        rw [evaluateContext_right]
        exact rightRealized.termHeader symbol
  predicateHeader symbol := by
    cases symbol with
    | inl symbol =>
        change (model left right).evaluateContext (contextLeft (leftSignature.predicateParameters symbol)) =
          some (left.predicateParameters symbol)
        rw [evaluateContext_left]
        exact leftRealized.predicateHeader symbol
    | inr symbol =>
        change (model left right).evaluateContext (contextRight (rightSignature.predicateParameters symbol)) =
          some (right.predicateParameters symbol)
        rw [evaluateContext_right]
        exact rightRealized.predicateHeader symbol
  termResult symbol := by
    cases symbol with
    | inl symbol =>
        change (model left right).evaluateType (left.termParameters symbol)
          (typeLeft (leftSignature.termResult symbol)) = some (left.termType symbol)
        rw [evaluateType_left]
        exact leftRealized.termResult symbol
    | inr symbol =>
        change (model left right).evaluateType (right.termParameters symbol)
          (typeRight (rightSignature.termResult symbol)) = some (right.termType symbol)
        rw [evaluateType_right]
        exact rightRealized.termResult symbol

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum
