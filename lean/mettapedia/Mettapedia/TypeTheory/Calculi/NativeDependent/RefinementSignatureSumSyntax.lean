import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContexts

/-!
# Disjoint native alphabets and their syntax inclusions

The two symbol origins remain distinct even when their declarations have equal
headers. Each inclusion traverses the full dependent type, term and proposition
syntax, preserving every binder, annotation and ordered primitive argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

universe u v
variable {S : Symbols.{u}} {T : Symbols.{v}}

abbrev symbols (S : Symbols.{u}) (T : Symbols.{v}) : Symbols.{max u v} where
  TypeSymbol := Sum S.TypeSymbol T.TypeSymbol
  TermSymbol := Sum S.TermSymbol T.TermSymbol
  PredicateSymbol := Sum S.PredicateSymbol T.PredicateSymbol
  typeArity := Sum.elim S.typeArity T.typeArity
  termArity := Sum.elim S.termArity T.termArity
  predicateArity := Sum.elim S.predicateArity T.predicateArity

mutual

def typeLeft : {n : Nat} → TypeExpr S n → TypeExpr (symbols S T) n
  | _, .family symbol arguments => .family (Sum.inl symbol) (fun position => termLeft (arguments position))
  | _, .propositions => .propositions
  | _, .pi domain body => .pi (typeLeft domain) (typeLeft body)
  | _, .sigma domain body => .sigma (typeLeft domain) (typeLeft body)
  | _, .comprehension domain predicate => .comprehension (typeLeft domain) (propLeft predicate)

def termLeft : {n : Nat} → TermExpr S n → TermExpr (symbols S T) n
  | _, .var index => .var index
  | _, .primitive symbol arguments => .primitive (Sum.inl symbol) (fun position => termLeft (arguments position))
  | _, .lam domain codomain body => .lam (typeLeft domain) (typeLeft codomain) (termLeft body)
  | _, .app domain body function argument => .app (typeLeft domain) (typeLeft body) (termLeft function) (termLeft argument)
  | _, .pair domain body first second => .pair (typeLeft domain) (typeLeft body) (termLeft first) (termLeft second)
  | _, .fst domain body pair => .fst (typeLeft domain) (typeLeft body) (termLeft pair)
  | _, .snd domain body pair => .snd (typeLeft domain) (typeLeft body) (termLeft pair)
  | _, .sigmaElim domain body motive branch pair => .sigmaElim (typeLeft domain) (typeLeft body) (typeLeft motive) (termLeft branch) (termLeft pair)
  | _, .quote predicate => .quote (propLeft predicate)
  | _, .refine domain predicate value => .refine (typeLeft domain) (propLeft predicate) (termLeft value)
  | _, .forget domain predicate value => .forget (typeLeft domain) (propLeft predicate) (termLeft value)

def propLeft : {n : Nat} → PropExpr S n → PropExpr (symbols S T) n
  | _, .atom symbol arguments => .atom (Sum.inl symbol) (fun position => termLeft (arguments position))
  | _, .truth => .truth
  | _, .falsehood => .falsehood
  | _, .and first second => .and (propLeft first) (propLeft second)
  | _, .or first second => .or (propLeft first) (propLeft second)
  | _, .implies first second => .implies (propLeft first) (propLeft second)
  | _, .all domain predicate => .all (typeLeft domain) (propLeft predicate)
  | _, .exists domain predicate => .exists (typeLeft domain) (propLeft predicate)
  | _, .holds term => .holds (termLeft term)
  | _, .image type => .image (typeLeft type)

end

def contextLeft : {n : Nat} → ContextExpr S n → ContextExpr (symbols S T) n
  | _, .nil => .nil
  | _, .snoc previous type => .snoc (contextLeft previous) (typeLeft type)
  | _, .assume previous predicate => .assume (contextLeft previous) (propLeft predicate)

mutual

def typeRight : {n : Nat} → TypeExpr T n → TypeExpr (symbols S T) n
  | _, .family symbol arguments => .family (Sum.inr symbol) (fun position => termRight (arguments position))
  | _, .propositions => .propositions
  | _, .pi domain body => .pi (typeRight domain) (typeRight body)
  | _, .sigma domain body => .sigma (typeRight domain) (typeRight body)
  | _, .comprehension domain predicate => .comprehension (typeRight domain) (propRight predicate)

def termRight : {n : Nat} → TermExpr T n → TermExpr (symbols S T) n
  | _, .var index => .var index
  | _, .primitive symbol arguments => .primitive (Sum.inr symbol) (fun position => termRight (arguments position))
  | _, .lam domain codomain body => .lam (typeRight domain) (typeRight codomain) (termRight body)
  | _, .app domain body function argument => .app (typeRight domain) (typeRight body) (termRight function) (termRight argument)
  | _, .pair domain body first second => .pair (typeRight domain) (typeRight body) (termRight first) (termRight second)
  | _, .fst domain body pair => .fst (typeRight domain) (typeRight body) (termRight pair)
  | _, .snd domain body pair => .snd (typeRight domain) (typeRight body) (termRight pair)
  | _, .sigmaElim domain body motive branch pair => .sigmaElim (typeRight domain) (typeRight body) (typeRight motive) (termRight branch) (termRight pair)
  | _, .quote predicate => .quote (propRight predicate)
  | _, .refine domain predicate value => .refine (typeRight domain) (propRight predicate) (termRight value)
  | _, .forget domain predicate value => .forget (typeRight domain) (propRight predicate) (termRight value)

def propRight : {n : Nat} → PropExpr T n → PropExpr (symbols S T) n
  | _, .atom symbol arguments => .atom (Sum.inr symbol) (fun position => termRight (arguments position))
  | _, .truth => .truth
  | _, .falsehood => .falsehood
  | _, .and first second => .and (propRight first) (propRight second)
  | _, .or first second => .or (propRight first) (propRight second)
  | _, .implies first second => .implies (propRight first) (propRight second)
  | _, .all domain predicate => .all (typeRight domain) (propRight predicate)
  | _, .exists domain predicate => .exists (typeRight domain) (propRight predicate)
  | _, .holds term => .holds (termRight term)
  | _, .image type => .image (typeRight type)

end

def contextRight : {n : Nat} → ContextExpr T n → ContextExpr (symbols S T) n
  | _, .nil => .nil
  | _, .snoc previous type => .snoc (contextRight previous) (typeRight type)
  | _, .assume previous predicate => .assume (contextRight previous) (propRight predicate)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

