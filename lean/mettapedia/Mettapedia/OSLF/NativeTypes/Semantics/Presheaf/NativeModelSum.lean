import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSum

/-!
# Native models use the common disjoint signature interpretation

The general native dependent implementation owns model composition and
preservation through both syntax inclusions. These OSLF readouts retain
its existing public interfaces while sharing that one implementation.
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

def model (left : ModelData S W) (right : ModelData T W) : ModelData (symbols S T) W :=
  SignatureSum.model left right

variable (left : ModelData S W) (right : ModelData T W)

@[simp] theorem type_scope_left (symbol : S.TypeSymbol) :
    (model left right).typeParameters (.inl symbol) = left.typeParameters symbol :=
  SignatureSum.typeParameters_left left right symbol

@[simp] theorem term_scope_left (symbol : S.TermSymbol) :
    (model left right).termParameters (.inl symbol) = left.termParameters symbol :=
  SignatureSum.termParameters_left left right symbol

@[simp] theorem predicate_scope_left (symbol : S.PredicateSymbol) :
    (model left right).predicateParameters (.inl symbol) = left.predicateParameters symbol :=
  SignatureSum.predicateParameters_left left right symbol

@[simp] theorem family_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.TypeSymbol)
    (arguments : P ⟶ (left.typeParameters symbol).1) :
    (model left right).familyAt (.inl symbol) arguments = left.familyAt symbol arguments :=
  SignatureSum.familyAt_left left right symbol arguments

@[simp] theorem primitive_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.TermSymbol)
    (arguments : P ⟶ (left.termParameters symbol).1) :
    (model left right).primitiveAt (.inl symbol) arguments = left.primitiveAt symbol arguments :=
  SignatureSum.primitiveAt_left left right symbol arguments

@[simp] theorem predicate_at_left {P : Wᵒᵖ ⥤ Type u} (symbol : S.PredicateSymbol)
    (arguments : P ⟶ (left.predicateParameters symbol).1) :
    (model left right).predicateAt (.inl symbol) arguments = left.predicateAt symbol arguments :=
  SignatureSum.predicateAt_left left right symbol arguments

@[simp] theorem type_scope_right (symbol : T.TypeSymbol) :
    (model left right).typeParameters (.inr symbol) = right.typeParameters symbol :=
  SignatureSum.typeParameters_right left right symbol

@[simp] theorem term_scope_right (symbol : T.TermSymbol) :
    (model left right).termParameters (.inr symbol) = right.termParameters symbol :=
  SignatureSum.termParameters_right left right symbol

@[simp] theorem predicate_scope_right (symbol : T.PredicateSymbol) :
    (model left right).predicateParameters (.inr symbol) = right.predicateParameters symbol :=
  SignatureSum.predicateParameters_right left right symbol

@[simp] theorem family_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.TypeSymbol)
    (arguments : P ⟶ (right.typeParameters symbol).1) :
    (model left right).familyAt (.inr symbol) arguments = right.familyAt symbol arguments :=
  SignatureSum.familyAt_right left right symbol arguments

@[simp] theorem primitive_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.TermSymbol)
    (arguments : P ⟶ (right.termParameters symbol).1) :
    (model left right).primitiveAt (.inr symbol) arguments = right.primitiveAt symbol arguments :=
  SignatureSum.primitiveAt_right left right symbol arguments

@[simp] theorem predicate_at_right {P : Wᵒᵖ ⥤ Type u} (symbol : T.PredicateSymbol)
    (arguments : P ⟶ (right.predicateParameters symbol).1) :
    (model left right).predicateAt (.inr symbol) arguments = right.predicateAt symbol arguments :=
  SignatureSum.predicateAt_right left right symbol arguments

theorem type_left (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : TypeExpr S n) :
    (model left right).evaluateType context (typeLeft expression) = left.evaluateType context expression :=
  SignatureSum.evaluateType_left left right expression context

theorem term_left (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : TermExpr S n) :
    (model left right).evaluateTerm context (termLeft expression) = left.evaluateTerm context expression :=
  SignatureSum.evaluateTerm_left left right expression context

theorem prop_left (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : PropExpr S n) :
    (model left right).evaluatePredicateLift context (propLeft expression) = left.evaluatePredicateLift context expression :=
  SignatureSum.evaluatePredicateLift_left left right expression context

theorem context_left (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : ContextExpr S n) :
    (model left right).evaluateContext (contextLeft context) = left.evaluateContext context :=
  SignatureSum.evaluateContext_left left right context

theorem type_right (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : TypeExpr T n) :
    (model left right).evaluateType context (typeRight expression) = right.evaluateType context expression :=
  SignatureSum.evaluateType_right left right expression context

theorem term_right (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : TermExpr T n) :
    (model left right).evaluateTerm context (termRight expression) = right.evaluateTerm context expression :=
  SignatureSum.evaluateTerm_right left right expression context

theorem prop_right (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : Scope W n) (expression : PropExpr T n) :
    (model left right).evaluatePredicateLift context (propRight expression) = right.evaluatePredicateLift context expression :=
  SignatureSum.evaluatePredicateLift_right left right expression context

theorem context_right (left : ModelData S W) (right : ModelData T W) {n : Nat}
    (context : ContextExpr T n) :
    (model left right).evaluateContext (contextRight context) = right.evaluateContext context :=
  SignatureSum.evaluateContext_right left right context

theorem realization (source : Signature S) (target : Signature T)
    (sourceRealized : SignatureRealization left source)
    (targetRealized : SignatureRealization right target) :
    SignatureRealization (model left right) (SignatureSum.signature source target) :=
  SignatureSum.realization left right source target sourceRealized targetRealized

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeModelSum
