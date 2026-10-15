import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSum

/-!
# Genuine native models compose along the disjoint declaration alphabet

Both original primitive models retain their parameter scopes, families,
sections and predicate meanings. The common native evaluator preserves the
complete dependent grammar through each actual syntax inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeModelSum

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open SignatureSum

universe u v z
variable {S : Symbols.{v}} {T : Symbols.{z}} {W : Type u} [Category.{u} W]

def model (left : ModelData S W) (right : ModelData T W) : ModelData (symbols S T) W where
  typeParameters symbol := match symbol with
    | .inl original => left.typeParameters original
    | .inr original => right.typeParameters original
  typeFamily symbol := match symbol with
    | .inl original => left.typeFamily original
    | .inr original => right.typeFamily original
  termParameters symbol := match symbol with
    | .inl original => left.termParameters original
    | .inr original => right.termParameters original
  termType symbol := match symbol with
    | .inl original => left.termType original
    | .inr original => right.termType original
  termValue symbol := match symbol with
    | .inl original => left.termValue original
    | .inr original => right.termValue original
  predicateParameters symbol := match symbol with
    | .inl original => left.predicateParameters original
    | .inr original => right.predicateParameters original
  predicateValue symbol := match symbol with
    | .inl original => left.predicateValue original
    | .inr original => right.predicateValue original

variable (left : ModelData S W) (right : ModelData T W)

@[simp] theorem type_scope_left (symbol : S.TypeSymbol) :
    (model left right).typeParameters (.inl symbol) = left.typeParameters symbol := rfl

@[simp] theorem term_scope_left (symbol : S.TermSymbol) :
    (model left right).termParameters (.inl symbol) = left.termParameters symbol := rfl

@[simp] theorem predicate_scope_left (symbol : S.PredicateSymbol) :
    (model left right).predicateParameters (.inl symbol) = left.predicateParameters symbol := rfl

@[simp] theorem family_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.TypeSymbol)
    (arguments : P ⟶ (left.typeParameters symbol).1) :
    (model left right).familyAt (.inl symbol) arguments = left.familyAt symbol arguments := rfl

@[simp] theorem primitive_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.TermSymbol)
    (arguments : P ⟶ (left.termParameters symbol).1) :
    (model left right).primitiveAt (.inl symbol) arguments = left.primitiveAt symbol arguments := rfl

@[simp] theorem predicate_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.PredicateSymbol)
    (arguments : P ⟶ (left.predicateParameters symbol).1) :
    (model left right).predicateAt (.inl symbol) arguments = left.predicateAt symbol arguments := rfl

@[simp] theorem type_scope_right (symbol : T.TypeSymbol) :
    (model left right).typeParameters (.inr symbol) = right.typeParameters symbol := rfl

@[simp] theorem term_scope_right (symbol : T.TermSymbol) :
    (model left right).termParameters (.inr symbol) = right.termParameters symbol := rfl

@[simp] theorem predicate_scope_right (symbol : T.PredicateSymbol) :
    (model left right).predicateParameters (.inr symbol) = right.predicateParameters symbol := rfl

@[simp] theorem family_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.TypeSymbol)
    (arguments : P ⟶ (right.typeParameters symbol).1) :
    (model left right).familyAt (.inr symbol) arguments = right.familyAt symbol arguments := rfl

@[simp] theorem primitive_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.TermSymbol)
    (arguments : P ⟶ (right.termParameters symbol).1) :
    (model left right).primitiveAt (.inr symbol) arguments = right.primitiveAt symbol arguments := rfl

@[simp] theorem predicate_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.PredicateSymbol)
    (arguments : P ⟶ (right.predicateParameters symbol).1) :
    (model left right).predicateAt (.inr symbol) arguments = right.predicateAt symbol arguments := rfl

mutual

theorem type_left (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : TypeExpr S n),
    (model left right).evaluateType context (typeLeft expression) = left.evaluateType context expression
  | _, context, .family symbol arguments => by
      simp only [typeLeft, ModelData.evaluateType, type_scope_left, family_at_left]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termLeft (arguments position))) =
          fun position => left.evaluateTerm context (arguments position) := by
        funext position
        exact term_left left right context (arguments position)
      exact congrArg
        (fun values : Fin (S.typeArity symbol) → Option (NativeValue context.1) =>
          Calculi.NativeDependent.External.bindResult ((left.typeParameters symbol).2.assemble? values) (fun parsed => some (left.familyAt symbol parsed))) argumentsEqual
  | _, _, .propositions => rfl
  | _, context, .pi domain body => by
      simp only [typeLeft, ModelData.evaluateType, type_left left right context domain,
        type_left left right _ body, ModelData.products]
  | _, context, .sigma domain body => by
      simp only [typeLeft, ModelData.evaluateType, type_left left right context domain,
        type_left left right _ body, ModelData.sums]
  | _, context, .comprehension domain predicate => by
      simp only [typeLeft, ModelData.evaluateType, type_left left right context domain,
        prop_left left right _ predicate]

theorem term_left (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : TermExpr S n),
    (model left right).evaluateTerm context (termLeft expression) = left.evaluateTerm context expression
  | _, _, .var _ => rfl
  | _, context, .primitive symbol arguments => by
      simp only [termLeft, ModelData.evaluateTerm, term_scope_left, primitive_at_left]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termLeft (arguments position))) =
          fun position => left.evaluateTerm context (arguments position) := by
        funext position
        exact term_left left right context (arguments position)
      exact congrArg
        (fun values : Fin (S.termArity symbol) → Option (NativeValue context.1) =>
          Calculi.NativeDependent.External.bindResult ((left.termParameters symbol).2.assemble? values) (fun parsed => some (left.primitiveAt symbol parsed))) argumentsEqual
  | _, context, .lam domain codomain body => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ codomain, term_left left right _ body, ModelData.lambda?, ModelData.products]
  | _, context, .app domain body function argument => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ body, term_left left right context function,
        term_left left right context argument, ModelData.application?, ModelData.products]
  | _, context, .pair domain body first second => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ body, term_left left right context first,
        term_left left right context second, ModelData.pair?, ModelData.sums]
  | _, context, .fst domain body pair => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ body, term_left left right context pair, ModelData.first?, ModelData.sums]
  | _, context, .snd domain body pair => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ body, term_left left right context pair, ModelData.second?, ModelData.sums]
  | _, context, .sigmaElim domain body motive branch pair => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        type_left left right _ body, type_left left right _ motive,
        term_left left right _ branch, term_left left right context pair,
        ModelData.sumEliminate?, ModelData.sums]
  | _, context, .quote predicate => by
      simp only [termLeft, ModelData.evaluateTerm, prop_left left right context predicate]
  | _, context, .refine domain predicate term => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        prop_left left right _ predicate, term_left left right context term]
  | _, context, .forget domain predicate term => by
      simp only [termLeft, ModelData.evaluateTerm, type_left left right context domain,
        prop_left left right _ predicate, term_left left right context term]

theorem prop_left (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : PropExpr S n),
    (model left right).evaluatePredicateLift context (propLeft expression) = left.evaluatePredicateLift context expression
  | _, context, .atom symbol arguments => by
      simp only [propLeft, ModelData.evaluatePredicateLift, predicate_scope_left, predicate_at_left]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termLeft (arguments position))) =
          fun position => left.evaluateTerm context (arguments position) := by
        funext position
        exact term_left left right context (arguments position)
      exact congrArg
        (fun values : Fin (S.predicateArity symbol) → Option (NativeValue context.1) =>
          ULift.up (Calculi.NativeDependent.External.bindResult ((left.predicateParameters symbol).2.assemble? values) (fun parsed => some (left.predicateAt symbol parsed)))) argumentsEqual
  | _, _, .truth => rfl
  | _, _, .falsehood => rfl
  | _, context, .and first second => by
      simp only [propLeft, ModelData.evaluatePredicateLift, prop_left left right context first,
        prop_left left right context second]
  | _, context, .or first second => by
      simp only [propLeft, ModelData.evaluatePredicateLift, prop_left left right context first,
        prop_left left right context second]
  | _, context, .implies first second => by
      simp only [propLeft, ModelData.evaluatePredicateLift, prop_left left right context first,
        prop_left left right context second]
  | _, context, .all domain predicate => by
      simp only [propLeft, ModelData.evaluatePredicateLift, type_left left right context domain,
        prop_left left right _ predicate]
  | _, context, .exists domain predicate => by
      simp only [propLeft, ModelData.evaluatePredicateLift, type_left left right context domain,
        prop_left left right _ predicate]
  | _, context, .holds term => by
      simp only [propLeft, ModelData.evaluatePredicateLift, term_left left right context term]
  | _, context, .image type => by
      simp only [propLeft, ModelData.evaluatePredicateLift, type_left left right context type]

end

theorem context_left (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : ContextExpr S n),
    (model left right).evaluateContext (contextLeft context) = left.evaluateContext context
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [contextLeft, ModelData.evaluateContext, context_left left right previous,
        type_left left right _ type]
  | _, .assume previous predicate => by
      simp only [contextLeft, ModelData.evaluateContext, context_left left right previous,
        ModelData.evaluatePredicate, prop_left left right _ predicate]

mutual

theorem type_right (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : TypeExpr T n),
    (model left right).evaluateType context (typeRight expression) = right.evaluateType context expression
  | _, context, .family symbol arguments => by
      simp only [typeRight, ModelData.evaluateType, type_scope_right, family_at_right]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termRight (arguments position))) =
          fun position => right.evaluateTerm context (arguments position) := by
        funext position
        exact term_right left right context (arguments position)
      exact congrArg
        (fun values : Fin (T.typeArity symbol) → Option (NativeValue context.1) =>
          Calculi.NativeDependent.External.bindResult ((right.typeParameters symbol).2.assemble? values) (fun parsed => some (right.familyAt symbol parsed))) argumentsEqual
  | _, _, .propositions => rfl
  | _, context, .pi domain body => by
      simp only [typeRight, ModelData.evaluateType, type_right left right context domain,
        type_right left right _ body, ModelData.products]
  | _, context, .sigma domain body => by
      simp only [typeRight, ModelData.evaluateType, type_right left right context domain,
        type_right left right _ body, ModelData.sums]
  | _, context, .comprehension domain predicate => by
      simp only [typeRight, ModelData.evaluateType, type_right left right context domain,
        prop_right left right _ predicate]

theorem term_right (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : TermExpr T n),
    (model left right).evaluateTerm context (termRight expression) = right.evaluateTerm context expression
  | _, _, .var _ => rfl
  | _, context, .primitive symbol arguments => by
      simp only [termRight, ModelData.evaluateTerm, term_scope_right, primitive_at_right]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termRight (arguments position))) =
          fun position => right.evaluateTerm context (arguments position) := by
        funext position
        exact term_right left right context (arguments position)
      exact congrArg
        (fun values : Fin (T.termArity symbol) → Option (NativeValue context.1) =>
          Calculi.NativeDependent.External.bindResult ((right.termParameters symbol).2.assemble? values) (fun parsed => some (right.primitiveAt symbol parsed))) argumentsEqual
  | _, context, .lam domain codomain body => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ codomain, term_right left right _ body, ModelData.lambda?, ModelData.products]
  | _, context, .app domain body function argument => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ body, term_right left right context function,
        term_right left right context argument, ModelData.application?, ModelData.products]
  | _, context, .pair domain body first second => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ body, term_right left right context first,
        term_right left right context second, ModelData.pair?, ModelData.sums]
  | _, context, .fst domain body pair => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ body, term_right left right context pair, ModelData.first?, ModelData.sums]
  | _, context, .snd domain body pair => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ body, term_right left right context pair, ModelData.second?, ModelData.sums]
  | _, context, .sigmaElim domain body motive branch pair => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        type_right left right _ body, type_right left right _ motive,
        term_right left right _ branch, term_right left right context pair,
        ModelData.sumEliminate?, ModelData.sums]
  | _, context, .quote predicate => by
      simp only [termRight, ModelData.evaluateTerm, prop_right left right context predicate]
  | _, context, .refine domain predicate term => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        prop_right left right _ predicate, term_right left right context term]
  | _, context, .forget domain predicate term => by
      simp only [termRight, ModelData.evaluateTerm, type_right left right context domain,
        prop_right left right _ predicate, term_right left right context term]

theorem prop_right (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : Scope W n) (expression : PropExpr T n),
    (model left right).evaluatePredicateLift context (propRight expression) = right.evaluatePredicateLift context expression
  | _, context, .atom symbol arguments => by
      simp only [propRight, ModelData.evaluatePredicateLift, predicate_scope_right, predicate_at_right]
      have argumentsEqual : (fun position => (model left right).evaluateTerm context (termRight (arguments position))) =
          fun position => right.evaluateTerm context (arguments position) := by
        funext position
        exact term_right left right context (arguments position)
      exact congrArg
        (fun values : Fin (T.predicateArity symbol) → Option (NativeValue context.1) =>
          ULift.up (Calculi.NativeDependent.External.bindResult ((right.predicateParameters symbol).2.assemble? values) (fun parsed => some (right.predicateAt symbol parsed)))) argumentsEqual
  | _, _, .truth => rfl
  | _, _, .falsehood => rfl
  | _, context, .and first second => by
      simp only [propRight, ModelData.evaluatePredicateLift, prop_right left right context first,
        prop_right left right context second]
  | _, context, .or first second => by
      simp only [propRight, ModelData.evaluatePredicateLift, prop_right left right context first,
        prop_right left right context second]
  | _, context, .implies first second => by
      simp only [propRight, ModelData.evaluatePredicateLift, prop_right left right context first,
        prop_right left right context second]
  | _, context, .all domain predicate => by
      simp only [propRight, ModelData.evaluatePredicateLift, type_right left right context domain,
        prop_right left right _ predicate]
  | _, context, .exists domain predicate => by
      simp only [propRight, ModelData.evaluatePredicateLift, type_right left right context domain,
        prop_right left right _ predicate]
  | _, context, .holds term => by
      simp only [propRight, ModelData.evaluatePredicateLift, term_right left right context term]
  | _, context, .image type => by
      simp only [propRight, ModelData.evaluatePredicateLift, type_right left right context type]

end

theorem context_right (left : ModelData S W) (right : ModelData T W) : ∀ {n : Nat} (context : ContextExpr T n),
    (model left right).evaluateContext (contextRight context) = right.evaluateContext context
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [contextRight, ModelData.evaluateContext, context_right left right previous,
        type_right left right _ type]
  | _, .assume previous predicate => by
      simp only [contextRight, ModelData.evaluateContext, context_right left right previous,
        ModelData.evaluatePredicate, prop_right left right _ predicate]


theorem realization (source : Signature S) (target : Signature T)
    (sourceRealized : SignatureRealization left source)
    (targetRealized : SignatureRealization right target) :
    SignatureRealization (model left right) (SignatureSum.signature source target) where
  typeHeader symbol := by
    cases symbol with
    | inl original => exact (context_left left right _).trans (sourceRealized.typeHeader original)
    | inr original => exact (context_right left right _).trans (targetRealized.typeHeader original)
  termHeader symbol := by
    cases symbol with
    | inl original => exact (context_left left right _).trans (sourceRealized.termHeader original)
    | inr original => exact (context_right left right _).trans (targetRealized.termHeader original)
  predicateHeader symbol := by
    cases symbol with
    | inl original => exact (context_left left right _).trans (sourceRealized.predicateHeader original)
    | inr original => exact (context_right left right _).trans (targetRealized.predicateHeader original)
  termResult symbol := by
    cases symbol with
    | inl original => exact (type_left left right _ _).trans (sourceRealized.termResult original)
    | inr original => exact (type_right left right _ _).trans (targetRealized.termResult original)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeModelSum
