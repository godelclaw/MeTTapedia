import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumSyntax

/-!
# Syntax inclusion commutes with every scoped renaming

Protected variables in dependent binders remain protected. Constructor and
predicate arguments retain their original order under both symbol inclusions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

universe u v
variable {S : Symbols.{u}} {T : Symbols.{v}}

mutual

@[simp] theorem typeLeft_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TypeExpr S n),
    typeLeft (T := T) (S := S) (expression.rename mapping) = (typeLeft expression).rename mapping
  | _, _, mapping, .family symbol arguments => by
      simp only [TypeExpr.rename, typeLeft]
      congr 1
      funext position
      exact termLeft_rename mapping (arguments position)
  | _, _, mapping, .propositions => by
      rfl
  | _, _, mapping, .pi domain body => by
      simp only [TypeExpr.rename, typeLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body]
  | _, _, mapping, .sigma domain body => by
      simp only [TypeExpr.rename, typeLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body]
  | _, _, mapping, .comprehension domain predicate => by
      simp only [TypeExpr.rename, typeLeft, typeLeft_rename mapping domain, propLeft_rename (liftRenaming mapping) predicate]

@[simp] theorem termLeft_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TermExpr S n),
    termLeft (T := T) (S := S) (expression.rename mapping) = (termLeft expression).rename mapping
  | _, _, mapping, .var index => by
      rfl
  | _, _, mapping, .primitive symbol arguments => by
      simp only [TermExpr.rename, termLeft]
      congr 1
      funext position
      exact termLeft_rename mapping (arguments position)
  | _, _, mapping, .lam domain codomain body => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) codomain, termLeft_rename (liftRenaming mapping) body]
  | _, _, mapping, .app domain body function argument => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body, termLeft_rename mapping function, termLeft_rename mapping argument]
  | _, _, mapping, .pair domain body first second => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body, termLeft_rename mapping first, termLeft_rename mapping second]
  | _, _, mapping, .fst domain body pair => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body, termLeft_rename mapping pair]
  | _, _, mapping, .snd domain body pair => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body, termLeft_rename mapping pair]
  | _, _, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, typeLeft_rename (liftRenaming mapping) body, typeLeft_rename (liftRenaming mapping) motive, termLeft_rename (liftRenaming (liftRenaming mapping)) branch, termLeft_rename mapping pair]
  | _, _, mapping, .quote predicate => by
      simp only [TermExpr.rename, termLeft, propLeft_rename mapping predicate]
  | _, _, mapping, .refine domain predicate value => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, propLeft_rename (liftRenaming mapping) predicate, termLeft_rename mapping value]
  | _, _, mapping, .forget domain predicate value => by
      simp only [TermExpr.rename, termLeft, typeLeft_rename mapping domain, propLeft_rename (liftRenaming mapping) predicate, termLeft_rename mapping value]

@[simp] theorem propLeft_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : PropExpr S n),
    propLeft (T := T) (S := S) (expression.rename mapping) = (propLeft expression).rename mapping
  | _, _, mapping, .atom symbol arguments => by
      simp only [PropExpr.rename, propLeft]
      congr 1
      funext position
      exact termLeft_rename mapping (arguments position)
  | _, _, mapping, .truth => by
      rfl
  | _, _, mapping, .falsehood => by
      rfl
  | _, _, mapping, .and first second => by
      simp only [PropExpr.rename, propLeft, propLeft_rename mapping first, propLeft_rename mapping second]
  | _, _, mapping, .or first second => by
      simp only [PropExpr.rename, propLeft, propLeft_rename mapping first, propLeft_rename mapping second]
  | _, _, mapping, .implies first second => by
      simp only [PropExpr.rename, propLeft, propLeft_rename mapping first, propLeft_rename mapping second]
  | _, _, mapping, .all domain predicate => by
      simp only [PropExpr.rename, propLeft, typeLeft_rename mapping domain, propLeft_rename (liftRenaming mapping) predicate]
  | _, _, mapping, .exists domain predicate => by
      simp only [PropExpr.rename, propLeft, typeLeft_rename mapping domain, propLeft_rename (liftRenaming mapping) predicate]
  | _, _, mapping, .holds term => by
      simp only [PropExpr.rename, propLeft, termLeft_rename mapping term]
  | _, _, mapping, .image type => by
      simp only [PropExpr.rename, propLeft, typeLeft_rename mapping type]

end

@[simp] theorem contextLeft_lookup :
    ∀ {n : Nat} (context : ContextExpr S n) (index : Fin n),
      (contextLeft (S := S) (T := T) context).lookup index = typeLeft (context.lookup index)
  | _, .nil, index => Fin.elim0 index
  | _, .snoc previous type, index => by
      cases index using Fin.cases <;>
        simp only [contextLeft, ContextExpr.lookup_zero, ContextExpr.lookup_succ,
          typeLeft_rename, contextLeft_lookup]
  | _, .assume previous predicate, index => contextLeft_lookup previous index

mutual

@[simp] theorem typeRight_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TypeExpr T n),
    typeRight (T := T) (S := S) (expression.rename mapping) = (typeRight expression).rename mapping
  | _, _, mapping, .family symbol arguments => by
      simp only [TypeExpr.rename, typeRight]
      congr 1
      funext position
      exact termRight_rename mapping (arguments position)
  | _, _, mapping, .propositions => by
      rfl
  | _, _, mapping, .pi domain body => by
      simp only [TypeExpr.rename, typeRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body]
  | _, _, mapping, .sigma domain body => by
      simp only [TypeExpr.rename, typeRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body]
  | _, _, mapping, .comprehension domain predicate => by
      simp only [TypeExpr.rename, typeRight, typeRight_rename mapping domain, propRight_rename (liftRenaming mapping) predicate]

@[simp] theorem termRight_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TermExpr T n),
    termRight (T := T) (S := S) (expression.rename mapping) = (termRight expression).rename mapping
  | _, _, mapping, .var index => by
      rfl
  | _, _, mapping, .primitive symbol arguments => by
      simp only [TermExpr.rename, termRight]
      congr 1
      funext position
      exact termRight_rename mapping (arguments position)
  | _, _, mapping, .lam domain codomain body => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) codomain, termRight_rename (liftRenaming mapping) body]
  | _, _, mapping, .app domain body function argument => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body, termRight_rename mapping function, termRight_rename mapping argument]
  | _, _, mapping, .pair domain body first second => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body, termRight_rename mapping first, termRight_rename mapping second]
  | _, _, mapping, .fst domain body pair => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body, termRight_rename mapping pair]
  | _, _, mapping, .snd domain body pair => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body, termRight_rename mapping pair]
  | _, _, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, typeRight_rename (liftRenaming mapping) body, typeRight_rename (liftRenaming mapping) motive, termRight_rename (liftRenaming (liftRenaming mapping)) branch, termRight_rename mapping pair]
  | _, _, mapping, .quote predicate => by
      simp only [TermExpr.rename, termRight, propRight_rename mapping predicate]
  | _, _, mapping, .refine domain predicate value => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, propRight_rename (liftRenaming mapping) predicate, termRight_rename mapping value]
  | _, _, mapping, .forget domain predicate value => by
      simp only [TermExpr.rename, termRight, typeRight_rename mapping domain, propRight_rename (liftRenaming mapping) predicate, termRight_rename mapping value]

@[simp] theorem propRight_rename : ∀ {n m : Nat} (mapping : Renaming n m) (expression : PropExpr T n),
    propRight (T := T) (S := S) (expression.rename mapping) = (propRight expression).rename mapping
  | _, _, mapping, .atom symbol arguments => by
      simp only [PropExpr.rename, propRight]
      congr 1
      funext position
      exact termRight_rename mapping (arguments position)
  | _, _, mapping, .truth => by
      rfl
  | _, _, mapping, .falsehood => by
      rfl
  | _, _, mapping, .and first second => by
      simp only [PropExpr.rename, propRight, propRight_rename mapping first, propRight_rename mapping second]
  | _, _, mapping, .or first second => by
      simp only [PropExpr.rename, propRight, propRight_rename mapping first, propRight_rename mapping second]
  | _, _, mapping, .implies first second => by
      simp only [PropExpr.rename, propRight, propRight_rename mapping first, propRight_rename mapping second]
  | _, _, mapping, .all domain predicate => by
      simp only [PropExpr.rename, propRight, typeRight_rename mapping domain, propRight_rename (liftRenaming mapping) predicate]
  | _, _, mapping, .exists domain predicate => by
      simp only [PropExpr.rename, propRight, typeRight_rename mapping domain, propRight_rename (liftRenaming mapping) predicate]
  | _, _, mapping, .holds term => by
      simp only [PropExpr.rename, propRight, termRight_rename mapping term]
  | _, _, mapping, .image type => by
      simp only [PropExpr.rename, propRight, typeRight_rename mapping type]

end

@[simp] theorem contextRight_lookup :
    ∀ {n : Nat} (context : ContextExpr T n) (index : Fin n),
      (contextRight (S := S) (T := T) context).lookup index = typeRight (context.lookup index)
  | _, .nil, index => Fin.elim0 index
  | _, .snoc previous type, index => by
      cases index using Fin.cases <;>
        simp only [contextRight, ContextExpr.lookup_zero, ContextExpr.lookup_succ,
          typeRight_rename, contextRight_lookup]
  | _, .assume previous predicate, index => contextRight_lookup previous index

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

