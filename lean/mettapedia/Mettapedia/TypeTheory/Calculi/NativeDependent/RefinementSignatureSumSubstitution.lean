import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumRenaming

/-!
# Symbol inclusion commutes with complete dependent substitution

Both inclusions preserve substitution beneath dependent binders, as well as
the full pair-elimination branch. A substituted witness keeps its symbol origin.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

universe u v
variable {S : Symbols.{u}} {T : Symbols.{v}}

abbrev substitutionLeft {n m : Nat} (substitution : Substitution S n m) :
    Substitution (symbols S T) n m := fun index => termLeft (substitution index)

@[simp] theorem substitutionLeft_lift {n m : Nat} (substitution : Substitution S n m) :
    substitutionLeft (S := S) (T := T) (liftSubstitution substitution) =
      liftSubstitution (substitutionLeft substitution) := by
  funext index
  cases index using Fin.cases
  · rfl
  · simp only [substitutionLeft, liftSubstitution_succ, termLeft_rename]

mutual

@[simp] theorem typeLeft_substitute :
    ∀ {n m : Nat} (substitution : Substitution S n m) (expression : TypeExpr S n),
      typeLeft (S := S) (T := T) (expression.substitute substitution) =
        (typeLeft expression).substitute (substitutionLeft substitution)
  | _, _, substitution, .family symbol arguments => by
      simp only [TypeExpr.substitute, typeLeft]
      congr 1
      funext position
      exact termLeft_substitute substitution (arguments position)
  | _, _, substitution, .propositions => by
      rfl
  | _, _, substitution, .pi domain body => by
      simp only [TypeExpr.substitute, typeLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .sigma domain body => by
      simp only [TypeExpr.substitute, typeLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .comprehension domain predicate => by
      simp only [TypeExpr.substitute, typeLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, propLeft_substitute (liftSubstitution substitution) predicate]

@[simp] theorem termLeft_substitute :
    ∀ {n m : Nat} (substitution : Substitution S n m) (expression : TermExpr S n),
      termLeft (S := S) (T := T) (expression.substitute substitution) =
        (termLeft expression).substitute (substitutionLeft substitution)
  | _, _, substitution, .var index => by
      rfl
  | _, _, substitution, .primitive symbol arguments => by
      simp only [TermExpr.substitute, termLeft]
      congr 1
      funext position
      exact termLeft_substitute substitution (arguments position)
  | _, _, substitution, .lam domain codomain body => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) codomain, termLeft_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .app domain body function argument => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body, termLeft_substitute substitution function, termLeft_substitute substitution argument]
  | _, _, substitution, .pair domain body first second => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body, termLeft_substitute substitution first, termLeft_substitute substitution second]
  | _, _, substitution, .fst domain body pair => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body, termLeft_substitute substitution pair]
  | _, _, substitution, .snd domain body pair => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body, termLeft_substitute substitution pair]
  | _, _, substitution, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, typeLeft_substitute (liftSubstitution substitution) body, typeLeft_substitute (liftSubstitution substitution) motive, termLeft_substitute (liftSubstitution (liftSubstitution substitution)) branch, termLeft_substitute substitution pair]
  | _, _, substitution, .quote predicate => by
      simp only [TermExpr.substitute, termLeft, propLeft_substitute substitution predicate]
  | _, _, substitution, .refine domain predicate value => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, propLeft_substitute (liftSubstitution substitution) predicate, termLeft_substitute substitution value]
  | _, _, substitution, .forget domain predicate value => by
      simp only [TermExpr.substitute, termLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, propLeft_substitute (liftSubstitution substitution) predicate, termLeft_substitute substitution value]

@[simp] theorem propLeft_substitute :
    ∀ {n m : Nat} (substitution : Substitution S n m) (expression : PropExpr S n),
      propLeft (S := S) (T := T) (expression.substitute substitution) =
        (propLeft expression).substitute (substitutionLeft substitution)
  | _, _, substitution, .atom symbol arguments => by
      simp only [PropExpr.substitute, propLeft]
      congr 1
      funext position
      exact termLeft_substitute substitution (arguments position)
  | _, _, substitution, .truth => by
      rfl
  | _, _, substitution, .falsehood => by
      rfl
  | _, _, substitution, .and first second => by
      simp only [PropExpr.substitute, propLeft, propLeft_substitute substitution first, propLeft_substitute substitution second]
  | _, _, substitution, .or first second => by
      simp only [PropExpr.substitute, propLeft, propLeft_substitute substitution first, propLeft_substitute substitution second]
  | _, _, substitution, .implies first second => by
      simp only [PropExpr.substitute, propLeft, propLeft_substitute substitution first, propLeft_substitute substitution second]
  | _, _, substitution, .all domain predicate => by
      simp only [PropExpr.substitute, propLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, propLeft_substitute (liftSubstitution substitution) predicate]
  | _, _, substitution, .exists domain predicate => by
      simp only [PropExpr.substitute, propLeft, substitutionLeft_lift, typeLeft_substitute substitution domain, propLeft_substitute (liftSubstitution substitution) predicate]
  | _, _, substitution, .holds term => by
      simp only [PropExpr.substitute, propLeft, termLeft_substitute substitution term]
  | _, _, substitution, .image type => by
      simp only [PropExpr.substitute, propLeft, typeLeft_substitute substitution type]

end

abbrev substitutionRight {n m : Nat} (substitution : Substitution T n m) :
    Substitution (symbols S T) n m := fun index => termRight (substitution index)

@[simp] theorem substitutionRight_lift {n m : Nat} (substitution : Substitution T n m) :
    substitutionRight (S := S) (T := T) (liftSubstitution substitution) =
      liftSubstitution (substitutionRight substitution) := by
  funext index
  cases index using Fin.cases
  · rfl
  · simp only [substitutionRight, liftSubstitution_succ, termRight_rename]

mutual

@[simp] theorem typeRight_substitute :
    ∀ {n m : Nat} (substitution : Substitution T n m) (expression : TypeExpr T n),
      typeRight (S := S) (T := T) (expression.substitute substitution) =
        (typeRight expression).substitute (substitutionRight substitution)
  | _, _, substitution, .family symbol arguments => by
      simp only [TypeExpr.substitute, typeRight]
      congr 1
      funext position
      exact termRight_substitute substitution (arguments position)
  | _, _, substitution, .propositions => by
      rfl
  | _, _, substitution, .pi domain body => by
      simp only [TypeExpr.substitute, typeRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .sigma domain body => by
      simp only [TypeExpr.substitute, typeRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .comprehension domain predicate => by
      simp only [TypeExpr.substitute, typeRight, substitutionRight_lift, typeRight_substitute substitution domain, propRight_substitute (liftSubstitution substitution) predicate]

@[simp] theorem termRight_substitute :
    ∀ {n m : Nat} (substitution : Substitution T n m) (expression : TermExpr T n),
      termRight (S := S) (T := T) (expression.substitute substitution) =
        (termRight expression).substitute (substitutionRight substitution)
  | _, _, substitution, .var index => by
      rfl
  | _, _, substitution, .primitive symbol arguments => by
      simp only [TermExpr.substitute, termRight]
      congr 1
      funext position
      exact termRight_substitute substitution (arguments position)
  | _, _, substitution, .lam domain codomain body => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) codomain, termRight_substitute (liftSubstitution substitution) body]
  | _, _, substitution, .app domain body function argument => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body, termRight_substitute substitution function, termRight_substitute substitution argument]
  | _, _, substitution, .pair domain body first second => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body, termRight_substitute substitution first, termRight_substitute substitution second]
  | _, _, substitution, .fst domain body pair => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body, termRight_substitute substitution pair]
  | _, _, substitution, .snd domain body pair => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body, termRight_substitute substitution pair]
  | _, _, substitution, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, typeRight_substitute (liftSubstitution substitution) body, typeRight_substitute (liftSubstitution substitution) motive, termRight_substitute (liftSubstitution (liftSubstitution substitution)) branch, termRight_substitute substitution pair]
  | _, _, substitution, .quote predicate => by
      simp only [TermExpr.substitute, termRight, propRight_substitute substitution predicate]
  | _, _, substitution, .refine domain predicate value => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, propRight_substitute (liftSubstitution substitution) predicate, termRight_substitute substitution value]
  | _, _, substitution, .forget domain predicate value => by
      simp only [TermExpr.substitute, termRight, substitutionRight_lift, typeRight_substitute substitution domain, propRight_substitute (liftSubstitution substitution) predicate, termRight_substitute substitution value]

@[simp] theorem propRight_substitute :
    ∀ {n m : Nat} (substitution : Substitution T n m) (expression : PropExpr T n),
      propRight (S := S) (T := T) (expression.substitute substitution) =
        (propRight expression).substitute (substitutionRight substitution)
  | _, _, substitution, .atom symbol arguments => by
      simp only [PropExpr.substitute, propRight]
      congr 1
      funext position
      exact termRight_substitute substitution (arguments position)
  | _, _, substitution, .truth => by
      rfl
  | _, _, substitution, .falsehood => by
      rfl
  | _, _, substitution, .and first second => by
      simp only [PropExpr.substitute, propRight, propRight_substitute substitution first, propRight_substitute substitution second]
  | _, _, substitution, .or first second => by
      simp only [PropExpr.substitute, propRight, propRight_substitute substitution first, propRight_substitute substitution second]
  | _, _, substitution, .implies first second => by
      simp only [PropExpr.substitute, propRight, propRight_substitute substitution first, propRight_substitute substitution second]
  | _, _, substitution, .all domain predicate => by
      simp only [PropExpr.substitute, propRight, substitutionRight_lift, typeRight_substitute substitution domain, propRight_substitute (liftSubstitution substitution) predicate]
  | _, _, substitution, .exists domain predicate => by
      simp only [PropExpr.substitute, propRight, substitutionRight_lift, typeRight_substitute substitution domain, propRight_substitute (liftSubstitution substitution) predicate]
  | _, _, substitution, .holds term => by
      simp only [PropExpr.substitute, propRight, termRight_substitute substitution term]
  | _, _, substitution, .image type => by
      simp only [PropExpr.substitute, propRight, typeRight_substitute substitution type]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

