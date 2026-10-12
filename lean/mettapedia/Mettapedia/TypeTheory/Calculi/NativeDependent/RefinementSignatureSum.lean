import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumSyntax

/-!
# The earned disjoint union of ranked native signatures

Ranks and contextual declaration headers come from the two original
signatures. Earlier-symbol obligations are transported through the actual
syntax inclusions; neither alphabet supplies new unproved admission fields.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

universe u v
variable {S : Symbols.{u}} {T : Symbols.{v}}

structure Ranks (S : Symbols.{u}) where
  typeRank : S.TypeSymbol → Nat
  termRank : S.TermSymbol → Nat
  predicateRank : S.PredicateSymbol → Nat

def ranks (D : Signature S) : Ranks S := ⟨D.typeRank, D.termRank, D.predicateRank⟩

def sumRanks (left : Ranks S) (right : Ranks T) : Ranks (symbols S T) :=
  ⟨Sum.elim left.typeRank right.typeRank,
   Sum.elim left.termRank right.termRank,
   Sum.elim left.predicateRank right.predicateRank⟩

mutual

@[simp] theorem typeLeft_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : TypeExpr S n),
      (typeLeft expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before left.typeRank left.termRank left.predicateRank bound
  | _, .family symbol arguments => by
      simp only [typeLeft, TypeExpr.before, sumRanks, Sum.elim_inl]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termLeft_before left right bound (arguments position)
  | _, .propositions => by
      rfl
  | _, .pi domain body => by
      simp only [TypeExpr.before, typeLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body]
  | _, .sigma domain body => by
      simp only [TypeExpr.before, typeLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body]
  | _, .comprehension domain predicate => by
      simp only [TypeExpr.before, typeLeft, typeLeft_before left right bound domain, propLeft_before left right bound predicate]

@[simp] theorem termLeft_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : TermExpr S n),
      (termLeft expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before left.typeRank left.termRank left.predicateRank bound
  | _, .var index => by
      rfl
  | _, .primitive symbol arguments => by
      simp only [termLeft, TermExpr.before, sumRanks, Sum.elim_inl]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termLeft_before left right bound (arguments position)
  | _, .lam domain codomain body => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound codomain, termLeft_before left right bound body]
  | _, .app domain body function argument => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body, termLeft_before left right bound function, termLeft_before left right bound argument]
  | _, .pair domain body first second => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body, termLeft_before left right bound first, termLeft_before left right bound second]
  | _, .fst domain body pair => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body, termLeft_before left right bound pair]
  | _, .snd domain body pair => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body, termLeft_before left right bound pair]
  | _, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, typeLeft_before left right bound body, typeLeft_before left right bound motive, termLeft_before left right bound branch, termLeft_before left right bound pair]
  | _, .quote predicate => by
      simp only [TermExpr.before, termLeft, propLeft_before left right bound predicate]
  | _, .refine domain predicate value => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, propLeft_before left right bound predicate, termLeft_before left right bound value]
  | _, .forget domain predicate value => by
      simp only [TermExpr.before, termLeft, typeLeft_before left right bound domain, propLeft_before left right bound predicate, termLeft_before left right bound value]

@[simp] theorem propLeft_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : PropExpr S n),
      (propLeft expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before left.typeRank left.termRank left.predicateRank bound
  | _, .atom symbol arguments => by
      simp only [propLeft, PropExpr.before, sumRanks, Sum.elim_inl]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termLeft_before left right bound (arguments position)
  | _, .truth => by
      rfl
  | _, .falsehood => by
      rfl
  | _, .and first second => by
      simp only [PropExpr.before, propLeft, propLeft_before left right bound first, propLeft_before left right bound second]
  | _, .or first second => by
      simp only [PropExpr.before, propLeft, propLeft_before left right bound first, propLeft_before left right bound second]
  | _, .implies first second => by
      simp only [PropExpr.before, propLeft, propLeft_before left right bound first, propLeft_before left right bound second]
  | _, .all domain predicate => by
      simp only [PropExpr.before, propLeft, typeLeft_before left right bound domain, propLeft_before left right bound predicate]
  | _, .exists domain predicate => by
      simp only [PropExpr.before, propLeft, typeLeft_before left right bound domain, propLeft_before left right bound predicate]
  | _, .holds term => by
      simp only [PropExpr.before, propLeft, termLeft_before left right bound term]
  | _, .image type => by
      simp only [PropExpr.before, propLeft, typeLeft_before left right bound type]

end

@[simp] theorem contextLeft_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (context : ContextExpr S n),
      (contextLeft context).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      context.before left.typeRank left.termRank left.predicateRank bound
  | _, .nil => Iff.rfl
  | _, .snoc previous type => by
      simp only [contextLeft, ContextExpr.before, contextLeft_before left right bound previous,
        typeLeft_before left right bound type]
  | _, .assume previous predicate => by
      simp only [contextLeft, ContextExpr.before, contextLeft_before left right bound previous,
        propLeft_before left right bound predicate]

mutual

@[simp] theorem typeRight_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : TypeExpr T n),
      (typeRight expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before right.typeRank right.termRank right.predicateRank bound
  | _, .family symbol arguments => by
      simp only [typeRight, TypeExpr.before, sumRanks, Sum.elim_inr]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termRight_before left right bound (arguments position)
  | _, .propositions => by
      rfl
  | _, .pi domain body => by
      simp only [TypeExpr.before, typeRight, typeRight_before left right bound domain, typeRight_before left right bound body]
  | _, .sigma domain body => by
      simp only [TypeExpr.before, typeRight, typeRight_before left right bound domain, typeRight_before left right bound body]
  | _, .comprehension domain predicate => by
      simp only [TypeExpr.before, typeRight, typeRight_before left right bound domain, propRight_before left right bound predicate]

@[simp] theorem termRight_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : TermExpr T n),
      (termRight expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before right.typeRank right.termRank right.predicateRank bound
  | _, .var index => by
      rfl
  | _, .primitive symbol arguments => by
      simp only [termRight, TermExpr.before, sumRanks, Sum.elim_inr]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termRight_before left right bound (arguments position)
  | _, .lam domain codomain body => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound codomain, termRight_before left right bound body]
  | _, .app domain body function argument => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound body, termRight_before left right bound function, termRight_before left right bound argument]
  | _, .pair domain body first second => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound body, termRight_before left right bound first, termRight_before left right bound second]
  | _, .fst domain body pair => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound body, termRight_before left right bound pair]
  | _, .snd domain body pair => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound body, termRight_before left right bound pair]
  | _, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, typeRight_before left right bound body, typeRight_before left right bound motive, termRight_before left right bound branch, termRight_before left right bound pair]
  | _, .quote predicate => by
      simp only [TermExpr.before, termRight, propRight_before left right bound predicate]
  | _, .refine domain predicate value => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, propRight_before left right bound predicate, termRight_before left right bound value]
  | _, .forget domain predicate value => by
      simp only [TermExpr.before, termRight, typeRight_before left right bound domain, propRight_before left right bound predicate, termRight_before left right bound value]

@[simp] theorem propRight_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (expression : PropExpr T n),
      (propRight expression).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      expression.before right.typeRank right.termRank right.predicateRank bound
  | _, .atom symbol arguments => by
      simp only [propRight, PropExpr.before, sumRanks, Sum.elim_inr]
      apply and_congr Iff.rfl
      exact forall_congr' fun position => termRight_before left right bound (arguments position)
  | _, .truth => by
      rfl
  | _, .falsehood => by
      rfl
  | _, .and first second => by
      simp only [PropExpr.before, propRight, propRight_before left right bound first, propRight_before left right bound second]
  | _, .or first second => by
      simp only [PropExpr.before, propRight, propRight_before left right bound first, propRight_before left right bound second]
  | _, .implies first second => by
      simp only [PropExpr.before, propRight, propRight_before left right bound first, propRight_before left right bound second]
  | _, .all domain predicate => by
      simp only [PropExpr.before, propRight, typeRight_before left right bound domain, propRight_before left right bound predicate]
  | _, .exists domain predicate => by
      simp only [PropExpr.before, propRight, typeRight_before left right bound domain, propRight_before left right bound predicate]
  | _, .holds term => by
      simp only [PropExpr.before, propRight, termRight_before left right bound term]
  | _, .image type => by
      simp only [PropExpr.before, propRight, typeRight_before left right bound type]

end

@[simp] theorem contextRight_before (left : Ranks S) (right : Ranks T) (bound : Nat) :
    ∀ {n : Nat} (context : ContextExpr T n),
      (contextRight context).before (sumRanks left right).typeRank
        (sumRanks left right).termRank (sumRanks left right).predicateRank bound ↔
      context.before right.typeRank right.termRank right.predicateRank bound
  | _, .nil => Iff.rfl
  | _, .snoc previous type => by
      simp only [contextRight, ContextExpr.before, contextRight_before left right bound previous,
        typeRight_before left right bound type]
  | _, .assume previous predicate => by
      simp only [contextRight, ContextExpr.before, contextRight_before left right bound previous,
        propRight_before left right bound predicate]

def signature (left : Signature S) (right : Signature T) : Signature (symbols S T) where
  typeRank := (sumRanks (ranks left) (ranks right)).typeRank
  termRank := (sumRanks (ranks left) (ranks right)).termRank
  predicateRank := (sumRanks (ranks left) (ranks right)).predicateRank
  typeParameters := fun symbol => match symbol with
    | .inl symbol => contextLeft (left.typeParameters symbol)
    | .inr symbol => contextRight (right.typeParameters symbol)
  termParameters := fun symbol => match symbol with
    | .inl symbol => contextLeft (left.termParameters symbol)
    | .inr symbol => contextRight (right.termParameters symbol)
  predicateParameters := fun symbol => match symbol with
    | .inl symbol => contextLeft (left.predicateParameters symbol)
    | .inr symbol => contextRight (right.predicateParameters symbol)
  termResult := fun symbol => match symbol with
    | .inl symbol => typeLeft (left.termResult symbol)
    | .inr symbol => typeRight (right.termResult symbol)
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (contextLeft_before (ranks left) (ranks right) _ _).mpr (left.typeParameters_before symbol)
    | inr symbol =>
        exact (contextRight_before (ranks left) (ranks right) _ _).mpr (right.typeParameters_before symbol)
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (contextLeft_before (ranks left) (ranks right) _ _).mpr (left.termParameters_before symbol)
    | inr symbol =>
        exact (contextRight_before (ranks left) (ranks right) _ _).mpr (right.termParameters_before symbol)
  predicateParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (contextLeft_before (ranks left) (ranks right) _ _).mpr (left.predicateParameters_before symbol)
    | inr symbol =>
        exact (contextRight_before (ranks left) (ranks right) _ _).mpr (right.predicateParameters_before symbol)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (typeLeft_before (ranks left) (ranks right) _ _).mpr (left.termResult_before symbol)
    | inr symbol =>
        exact (typeRight_before (ranks left) (ranks right) _ _).mpr (right.termResult_before symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

