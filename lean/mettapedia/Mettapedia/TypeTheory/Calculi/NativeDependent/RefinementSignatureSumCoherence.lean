import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumRules

/-!
# Disjoint signature inclusions preserve local judgments and premises

The comparison covers every original local native rule. Both constructor
inclusions preserve the complete substituted conclusion and every ordered
premise, including pair packing and refinement projection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

universe u
variable {S T : Symbols.{u}} {left : Signature S} {right : Signature T}

@[simp] theorem substitutionLeft_empty {n : Nat} :
    substitutionLeft (S := S) (T := T) (Fin.elim0 : Substitution S 0 n) = Fin.elim0 := by
  funext index
  exact Fin.elim0 index

@[simp] theorem substitutionRight_empty {n : Nat} :
    substitutionRight (S := S) (T := T) (Fin.elim0 : Substitution T 0 n) = Fin.elim0 := by
  funext index
  exact Fin.elim0 index

@[simp] theorem substitutionLeft_extend {n m : Nat}
    (substitution : Substitution S n m) (term : TermExpr S m) :
    substitutionLeft (S := S) (T := T) (extendSubstitution substitution term) =
      extendSubstitution (substitutionLeft substitution) (termLeft term) := by
  funext index
  cases index using Fin.cases <;> rfl

@[simp] theorem substitutionLeft_instantiate {n : Nat} (term : TermExpr S n) :
    substitutionLeft (S := S) (T := T) (instantiate term) = instantiate (termLeft term) := by
  funext index
  cases index using Fin.cases <;> rfl

@[simp] theorem substitutionLeft_components {n : Nat} (first second : TermExpr S n) :
    substitutionLeft (S := S) (T := T) (instantiateComponents first second) =
      instantiateComponents (termLeft first) (termLeft second) := by
  simp only [instantiateComponents, substitutionLeft_extend, substitutionLeft_instantiate]

@[simp] theorem substitutionLeft_compose {n m k : Nat}
    (first : Substitution S n m) (second : Substitution S m k) :
    substitutionLeft (S := S) (T := T) (composeSubstitution first second) =
      composeSubstitution (substitutionLeft first) (substitutionLeft second) := by
  funext index
  exact termLeft_substitute second (first index)

@[simp] theorem substitutionLeft_pack {n : Nat}
    (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    substitutionLeft (S := S) (T := T) (packSubstitution domain body) =
      packSubstitution (typeLeft domain) (typeLeft body) := by
  funext index
  cases index using Fin.cases
  · simp only [substitutionLeft, packSubstitution_zero, genericPair, termLeft, typeLeft_rename]
  · rfl

@[simp] theorem substitutionLeft_comprehension {n : Nat}
    (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    substitutionLeft (S := S) (T := T) (comprehensionProjection domain predicate) =
      comprehensionProjection (typeLeft domain) (propLeft predicate) := by
  funext index
  cases index using Fin.cases
  · simp only [substitutionLeft, comprehensionProjection, Fin.cases_zero, termLeft,
      typeLeft_rename, propLeft_rename]
  · rfl

@[simp] theorem substitutionRight_extend {n m : Nat}
    (substitution : Substitution T n m) (term : TermExpr T m) :
    substitutionRight (S := S) (T := T) (extendSubstitution substitution term) =
      extendSubstitution (substitutionRight substitution) (termRight term) := by
  funext index
  cases index using Fin.cases <;> rfl

@[simp] theorem substitutionRight_instantiate {n : Nat} (term : TermExpr T n) :
    substitutionRight (S := S) (T := T) (instantiate term) = instantiate (termRight term) := by
  funext index
  cases index using Fin.cases <;> rfl

@[simp] theorem substitutionRight_components {n : Nat} (first second : TermExpr T n) :
    substitutionRight (S := S) (T := T) (instantiateComponents first second) =
      instantiateComponents (termRight first) (termRight second) := by
  simp only [instantiateComponents, substitutionRight_extend, substitutionRight_instantiate]

@[simp] theorem substitutionRight_compose {n m k : Nat}
    (first : Substitution T n m) (second : Substitution T m k) :
    substitutionRight (S := S) (T := T) (composeSubstitution first second) =
      composeSubstitution (substitutionRight first) (substitutionRight second) := by
  funext index
  exact termRight_substitute second (first index)

@[simp] theorem substitutionRight_pack {n : Nat}
    (domain : TypeExpr T n) (body : TypeExpr T (n + 1)) :
    substitutionRight (S := S) (T := T) (packSubstitution domain body) =
      packSubstitution (typeRight domain) (typeRight body) := by
  funext index
  cases index using Fin.cases
  · simp only [substitutionRight, packSubstitution_zero, genericPair, termRight, typeRight_rename]
  · rfl

@[simp] theorem substitutionRight_comprehension {n : Nat}
    (domain : TypeExpr T n) (predicate : PropExpr T (n + 1)) :
    substitutionRight (S := S) (T := T) (comprehensionProjection domain predicate) =
      comprehensionProjection (typeRight domain) (propRight predicate) := by
  funext index
  cases index using Fin.cases
  · simp only [substitutionRight, comprehensionProjection, Fin.cases_zero, termRight,
      typeRight_rename, propRight_rename]
  · rfl

attribute [local simp] ruleLeft ruleRight RuleCode.conclusion RuleCode.premises
  judgmentLeft judgmentRight contextLeft contextRight typeLeft typeRight
  termLeft termRight propLeft propRight signature

theorem ruleLeft_conclusion (rule : RuleCode left) :
    (ruleLeft (right := right) rule).conclusion = judgmentLeft (T := T) rule.conclusion := by
  cases rule <;> first | rfl | simp

theorem ruleRight_conclusion (rule : RuleCode right) :
    (ruleRight (left := left) rule).conclusion = judgmentRight (S := S) rule.conclusion := by
  cases rule <;> first | rfl | simp

theorem ruleLeft_premises (rule : RuleCode left) :
    (ruleLeft (right := right) rule).premises = rule.premises.map (judgmentLeft (T := T)) := by
  cases rule <;> first | rfl | simp

theorem ruleRight_premises (rule : RuleCode right) :
    (ruleRight (left := left) rule).premises = rule.premises.map (judgmentRight (S := S)) := by
  cases rule <;> first | rfl | simp

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

