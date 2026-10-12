import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgments
/-!
# Computational equality for the full native dependent syntax

Finite primitive argument vectors are compared pointwise. Mutual structural
recursion compares dependent types, terms and propositions, including arbitrary
Pi/Sigma domains, comprehension, mixed assumption contexts and annotated motives.
Judgment comparison first checks the context lengths before comparing scoped
payloads. Only equality of independently supplied primitive symbol types is used.
-/

set_option autoImplicit false
universe u
namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
variable {S : Symbols.{u}} [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]
mutual
 def TypeExpr.decEq : {n : Nat} → (a b : TypeExpr S n) → Decidable (a = b)
  | _, .family s a, .family t b => by
     by_cases h : s = t
     · subst t
       letI : ∀ i, Decidable (a i = b i) := fun i => TermExpr.decEq (a i) (b i)
       letI : Decidable (a = b) := decidable_of_iff (∀ i, a i = b i) ⟨funext, congrFun⟩
       exact decidable_of_iff (a = b) (by simp)
     · exact isFalse (fun same => h (by cases same; rfl))
  | _, .propositions, .propositions => isTrue rfl
  | _, .pi a b, .pi c d => by
     letI := TypeExpr.decEq a c
     letI := TypeExpr.decEq b d
     exact decidable_of_iff (a = c ∧ b = d) (by simp)
  | _, .sigma a b, .sigma c d => by
     letI := TypeExpr.decEq a c
     letI := TypeExpr.decEq b d
     exact decidable_of_iff (a = c ∧ b = d) (by simp)
  | _, .comprehension a b, .comprehension c d => by
     letI := TypeExpr.decEq a c
     letI := PropExpr.decEq b d
     exact decidable_of_iff (a = c ∧ b = d) (by simp)
  | _, .family _ _, .propositions
  | _, .family _ _, .pi _ _
  | _, .family _ _, .sigma _ _
  | _, .family _ _, .comprehension _ _
  | _, .propositions, .family _ _
  | _, .propositions, .pi _ _
  | _, .propositions, .sigma _ _
  | _, .propositions, .comprehension _ _
  | _, .pi _ _, .family _ _
  | _, .pi _ _, .propositions
  | _, .pi _ _, .sigma _ _
  | _, .pi _ _, .comprehension _ _
  | _, .sigma _ _, .family _ _
  | _, .sigma _ _, .propositions
  | _, .sigma _ _, .pi _ _
  | _, .sigma _ _, .comprehension _ _
  | _, .comprehension _ _, .family _ _
  | _, .comprehension _ _, .propositions
  | _, .comprehension _ _, .pi _ _
  | _, .comprehension _ _, .sigma _ _ => isFalse (by intro same; cases same)
 def TermExpr.decEq : {n : Nat} → (a b : TermExpr S n) → Decidable (a = b)
  | _, .var i, .var j => decidable_of_iff (i = j) (by simp)
  | _, .primitive s a, .primitive t b => by
     by_cases h : s = t
     · subst t
       letI : ∀ i, Decidable (a i = b i) := fun i => TermExpr.decEq (a i) (b i)
       letI : Decidable (a = b) := decidable_of_iff (∀ i, a i = b i) ⟨funext, congrFun⟩
       exact decidable_of_iff (a = b) (by simp)
     · exact isFalse (fun same => h (by cases same; rfl))
  | _, .lam a b c, .lam k l m => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TermExpr.decEq c m
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
  | _, .app a b c d, .app k l m n => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TermExpr.decEq c m
     letI := TermExpr.decEq d n
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m ∧ d = n) (by simp)
  | _, .pair a b c d, .pair k l m n => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TermExpr.decEq c m
     letI := TermExpr.decEq d n
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m ∧ d = n) (by simp)
  | _, .fst a b c, .fst k l m => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TermExpr.decEq c m
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
  | _, .snd a b c, .snd k l m => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TermExpr.decEq c m
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
  | _, .sigmaElim a b c d e, .sigmaElim k l m n o => by
     letI := TypeExpr.decEq a k
     letI := TypeExpr.decEq b l
     letI := TypeExpr.decEq c m
     letI := TermExpr.decEq d n
     letI := TermExpr.decEq e o
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m ∧ d = n ∧ e = o) (by simp)
  | _, .quote a, .quote k => by
     letI := PropExpr.decEq a k
     exact decidable_of_iff (a = k) (by simp)
  | _, .refine a b c, .refine k l m => by
     letI := TypeExpr.decEq a k
     letI := PropExpr.decEq b l
     letI := TermExpr.decEq c m
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
  | _, .forget a b c, .forget k l m => by
     letI := TypeExpr.decEq a k
     letI := PropExpr.decEq b l
     letI := TermExpr.decEq c m
     exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
  | _, .var _, .primitive _ _
  | _, .var _, .lam _ _ _
  | _, .var _, .app _ _ _ _
  | _, .var _, .pair _ _ _ _
  | _, .var _, .fst _ _ _
  | _, .var _, .snd _ _ _
  | _, .var _, .sigmaElim _ _ _ _ _
  | _, .var _, .quote _
  | _, .var _, .refine _ _ _
  | _, .var _, .forget _ _ _
  | _, .primitive _ _, .var _
  | _, .primitive _ _, .lam _ _ _
  | _, .primitive _ _, .app _ _ _ _
  | _, .primitive _ _, .pair _ _ _ _
  | _, .primitive _ _, .fst _ _ _
  | _, .primitive _ _, .snd _ _ _
  | _, .primitive _ _, .sigmaElim _ _ _ _ _
  | _, .primitive _ _, .quote _
  | _, .primitive _ _, .refine _ _ _
  | _, .primitive _ _, .forget _ _ _
  | _, .lam _ _ _, .var _
  | _, .lam _ _ _, .primitive _ _
  | _, .lam _ _ _, .app _ _ _ _
  | _, .lam _ _ _, .pair _ _ _ _
  | _, .lam _ _ _, .fst _ _ _
  | _, .lam _ _ _, .snd _ _ _
  | _, .lam _ _ _, .sigmaElim _ _ _ _ _
  | _, .lam _ _ _, .quote _
  | _, .lam _ _ _, .refine _ _ _
  | _, .lam _ _ _, .forget _ _ _
  | _, .app _ _ _ _, .var _
  | _, .app _ _ _ _, .primitive _ _
  | _, .app _ _ _ _, .lam _ _ _
  | _, .app _ _ _ _, .pair _ _ _ _
  | _, .app _ _ _ _, .fst _ _ _
  | _, .app _ _ _ _, .snd _ _ _
  | _, .app _ _ _ _, .sigmaElim _ _ _ _ _
  | _, .app _ _ _ _, .quote _
  | _, .app _ _ _ _, .refine _ _ _
  | _, .app _ _ _ _, .forget _ _ _
  | _, .pair _ _ _ _, .var _
  | _, .pair _ _ _ _, .primitive _ _
  | _, .pair _ _ _ _, .lam _ _ _
  | _, .pair _ _ _ _, .app _ _ _ _
  | _, .pair _ _ _ _, .fst _ _ _
  | _, .pair _ _ _ _, .snd _ _ _
  | _, .pair _ _ _ _, .sigmaElim _ _ _ _ _
  | _, .pair _ _ _ _, .quote _
  | _, .pair _ _ _ _, .refine _ _ _
  | _, .pair _ _ _ _, .forget _ _ _
  | _, .fst _ _ _, .var _
  | _, .fst _ _ _, .primitive _ _
  | _, .fst _ _ _, .lam _ _ _
  | _, .fst _ _ _, .app _ _ _ _
  | _, .fst _ _ _, .pair _ _ _ _
  | _, .fst _ _ _, .snd _ _ _
  | _, .fst _ _ _, .sigmaElim _ _ _ _ _
  | _, .fst _ _ _, .quote _
  | _, .fst _ _ _, .refine _ _ _
  | _, .fst _ _ _, .forget _ _ _
  | _, .snd _ _ _, .var _
  | _, .snd _ _ _, .primitive _ _
  | _, .snd _ _ _, .lam _ _ _
  | _, .snd _ _ _, .app _ _ _ _
  | _, .snd _ _ _, .pair _ _ _ _
  | _, .snd _ _ _, .fst _ _ _
  | _, .snd _ _ _, .sigmaElim _ _ _ _ _
  | _, .snd _ _ _, .quote _
  | _, .snd _ _ _, .refine _ _ _
  | _, .snd _ _ _, .forget _ _ _
  | _, .sigmaElim _ _ _ _ _, .var _
  | _, .sigmaElim _ _ _ _ _, .primitive _ _
  | _, .sigmaElim _ _ _ _ _, .lam _ _ _
  | _, .sigmaElim _ _ _ _ _, .app _ _ _ _
  | _, .sigmaElim _ _ _ _ _, .pair _ _ _ _
  | _, .sigmaElim _ _ _ _ _, .fst _ _ _
  | _, .sigmaElim _ _ _ _ _, .snd _ _ _
  | _, .sigmaElim _ _ _ _ _, .quote _
  | _, .sigmaElim _ _ _ _ _, .refine _ _ _
  | _, .sigmaElim _ _ _ _ _, .forget _ _ _
  | _, .quote _, .var _
  | _, .quote _, .primitive _ _
  | _, .quote _, .lam _ _ _
  | _, .quote _, .app _ _ _ _
  | _, .quote _, .pair _ _ _ _
  | _, .quote _, .fst _ _ _
  | _, .quote _, .snd _ _ _
  | _, .quote _, .sigmaElim _ _ _ _ _
  | _, .quote _, .refine _ _ _
  | _, .quote _, .forget _ _ _
  | _, .refine _ _ _, .var _
  | _, .refine _ _ _, .primitive _ _
  | _, .refine _ _ _, .lam _ _ _
  | _, .refine _ _ _, .app _ _ _ _
  | _, .refine _ _ _, .pair _ _ _ _
  | _, .refine _ _ _, .fst _ _ _
  | _, .refine _ _ _, .snd _ _ _
  | _, .refine _ _ _, .sigmaElim _ _ _ _ _
  | _, .refine _ _ _, .quote _
  | _, .refine _ _ _, .forget _ _ _
  | _, .forget _ _ _, .var _
  | _, .forget _ _ _, .primitive _ _
  | _, .forget _ _ _, .lam _ _ _
  | _, .forget _ _ _, .app _ _ _ _
  | _, .forget _ _ _, .pair _ _ _ _
  | _, .forget _ _ _, .fst _ _ _
  | _, .forget _ _ _, .snd _ _ _
  | _, .forget _ _ _, .sigmaElim _ _ _ _ _
  | _, .forget _ _ _, .quote _
  | _, .forget _ _ _, .refine _ _ _ => isFalse (by intro same; cases same)
 def PropExpr.decEq : {n : Nat} → (a b : PropExpr S n) → Decidable (a = b)
  | _, .atom s a, .atom t b => by
     by_cases h : s = t
     · subst t
       letI : ∀ i, Decidable (a i = b i) := fun i => TermExpr.decEq (a i) (b i)
       letI : Decidable (a = b) := decidable_of_iff (∀ i, a i = b i) ⟨funext, congrFun⟩
       exact decidable_of_iff (a = b) (by simp)
     · exact isFalse (fun same => h (by cases same; rfl))
  | _, .truth, .truth => isTrue rfl
  | _, .falsehood, .falsehood => isTrue rfl
  | _, .and a b, .and k l => by
     letI := PropExpr.decEq a k
     letI := PropExpr.decEq b l
     exact decidable_of_iff (a = k ∧ b = l) (by simp)
  | _, .or a b, .or k l => by
     letI := PropExpr.decEq a k
     letI := PropExpr.decEq b l
     exact decidable_of_iff (a = k ∧ b = l) (by simp)
  | _, .implies a b, .implies k l => by
     letI := PropExpr.decEq a k
     letI := PropExpr.decEq b l
     exact decidable_of_iff (a = k ∧ b = l) (by simp)
  | _, .all a b, .all k l => by
     letI := TypeExpr.decEq a k
     letI := PropExpr.decEq b l
     exact decidable_of_iff (a = k ∧ b = l) (by simp)
  | _, .exists a b, .exists k l => by
     letI := TypeExpr.decEq a k
     letI := PropExpr.decEq b l
     exact decidable_of_iff (a = k ∧ b = l) (by simp)
  | _, .holds a, .holds k => by
     letI := TermExpr.decEq a k
     exact decidable_of_iff (a = k) (by simp)
  | _, .image a, .image k => by
     letI := TypeExpr.decEq a k
     exact decidable_of_iff (a = k) (by simp)
  | _, .atom _ _, .truth
  | _, .atom _ _, .falsehood
  | _, .atom _ _, .and _ _
  | _, .atom _ _, .or _ _
  | _, .atom _ _, .implies _ _
  | _, .atom _ _, .all _ _
  | _, .atom _ _, .exists _ _
  | _, .atom _ _, .holds _
  | _, .atom _ _, .image _
  | _, .truth, .atom _ _
  | _, .truth, .falsehood
  | _, .truth, .and _ _
  | _, .truth, .or _ _
  | _, .truth, .implies _ _
  | _, .truth, .all _ _
  | _, .truth, .exists _ _
  | _, .truth, .holds _
  | _, .truth, .image _
  | _, .falsehood, .atom _ _
  | _, .falsehood, .truth
  | _, .falsehood, .and _ _
  | _, .falsehood, .or _ _
  | _, .falsehood, .implies _ _
  | _, .falsehood, .all _ _
  | _, .falsehood, .exists _ _
  | _, .falsehood, .holds _
  | _, .falsehood, .image _
  | _, .and _ _, .atom _ _
  | _, .and _ _, .truth
  | _, .and _ _, .falsehood
  | _, .and _ _, .or _ _
  | _, .and _ _, .implies _ _
  | _, .and _ _, .all _ _
  | _, .and _ _, .exists _ _
  | _, .and _ _, .holds _
  | _, .and _ _, .image _
  | _, .or _ _, .atom _ _
  | _, .or _ _, .truth
  | _, .or _ _, .falsehood
  | _, .or _ _, .and _ _
  | _, .or _ _, .implies _ _
  | _, .or _ _, .all _ _
  | _, .or _ _, .exists _ _
  | _, .or _ _, .holds _
  | _, .or _ _, .image _
  | _, .implies _ _, .atom _ _
  | _, .implies _ _, .truth
  | _, .implies _ _, .falsehood
  | _, .implies _ _, .and _ _
  | _, .implies _ _, .or _ _
  | _, .implies _ _, .all _ _
  | _, .implies _ _, .exists _ _
  | _, .implies _ _, .holds _
  | _, .implies _ _, .image _
  | _, .all _ _, .atom _ _
  | _, .all _ _, .truth
  | _, .all _ _, .falsehood
  | _, .all _ _, .and _ _
  | _, .all _ _, .or _ _
  | _, .all _ _, .implies _ _
  | _, .all _ _, .exists _ _
  | _, .all _ _, .holds _
  | _, .all _ _, .image _
  | _, .exists _ _, .atom _ _
  | _, .exists _ _, .truth
  | _, .exists _ _, .falsehood
  | _, .exists _ _, .and _ _
  | _, .exists _ _, .or _ _
  | _, .exists _ _, .implies _ _
  | _, .exists _ _, .all _ _
  | _, .exists _ _, .holds _
  | _, .exists _ _, .image _
  | _, .holds _, .atom _ _
  | _, .holds _, .truth
  | _, .holds _, .falsehood
  | _, .holds _, .and _ _
  | _, .holds _, .or _ _
  | _, .holds _, .implies _ _
  | _, .holds _, .all _ _
  | _, .holds _, .exists _ _
  | _, .holds _, .image _
  | _, .image _, .atom _ _
  | _, .image _, .truth
  | _, .image _, .falsehood
  | _, .image _, .and _ _
  | _, .image _, .or _ _
  | _, .image _, .implies _ _
  | _, .image _, .all _ _
  | _, .image _, .exists _ _
  | _, .image _, .holds _ => isFalse (by intro same; cases same)
end


instance {n : Nat} : DecidableEq (TypeExpr S n) := TypeExpr.decEq
instance {n : Nat} : DecidableEq (TermExpr S n) := TermExpr.decEq
instance {n : Nat} : DecidableEq (PropExpr S n) := PropExpr.decEq

def ContextExpr.decEq : {n : Nat} → (a b : ContextExpr S n) → Decidable (a = b)
  | _, .nil, .nil => isTrue rfl
  | _, .snoc a b, .snoc c d => by
      letI := ContextExpr.decEq a c
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
  | _, .assume a b, .assume c d => by
      letI := ContextExpr.decEq a c
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
  | _, .nil, .assume _ _
  | _, .assume _ _, .nil
  | _, .snoc _ _, .assume _ _
  | _, .assume _ _, .snoc _ _ => isFalse (by intro same; cases same)

instance {n : Nat} : DecidableEq (ContextExpr S n) := ContextExpr.decEq
instance {n m : Nat} : DecidableEq (Substitution S n m) := fun x y =>
  decidable_of_iff (∀ i, x i = y i) ⟨funext, congrFun⟩

def Judgment.decEq : (a b : Judgment S) → Decidable (a = b)
 | @Judgment.context _ n a, @Judgment.context _ n' k => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.type _ n a b, @Judgment.type _ n' k l => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.term _ n a b c, @Judgment.term _ n' k l m => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.substitution _ n arity a b c, @Judgment.substitution _ n' arity' k l m => by
    by_cases hn : n = n'
    · subst n'
      by_cases hm : arity = arity'
      · subst arity'
        exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
      · exact isFalse (fun same => hm (by cases same; rfl))
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.contextEq _ n a b, @Judgment.contextEq _ n' k l => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.typeEq _ n a b c, @Judgment.typeEq _ n' k l m => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.termEq _ n a b c d, @Judgment.termEq _ n' k l m z => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l ∧ c = m ∧ d = z) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.substitutionEq _ n arity a b c d, @Judgment.substitutionEq _ n' arity' k l m z => by
    by_cases hn : n = n'
    · subst n'
      by_cases hm : arity = arity'
      · subst arity'
        exact decidable_of_iff (a = k ∧ b = l ∧ c = m ∧ d = z) (by simp)
      · exact isFalse (fun same => hm (by cases same; rfl))
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.predicate _ n a b, @Judgment.predicate _ n' k l => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.entails _ n a b, @Judgment.entails _ n' k l => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | @Judgment.predicateEq _ n a b c, @Judgment.predicateEq _ n' k l m => by
    by_cases hn : n = n'
    · subst n'
      exact decidable_of_iff (a = k ∧ b = l ∧ c = m) (by simp)
    · exact isFalse (fun same => hn (by cases same; rfl))
 | .context _, .type _ _
 | .context _, .term _ _ _
 | .context _, .substitution _ _ _
 | .context _, .contextEq _ _
 | .context _, .typeEq _ _ _
 | .context _, .termEq _ _ _ _
 | .context _, .substitutionEq _ _ _ _
 | .context _, .predicate _ _
 | .context _, .entails _ _
 | .context _, .predicateEq _ _ _
 | .type _ _, .context _
 | .type _ _, .term _ _ _
 | .type _ _, .substitution _ _ _
 | .type _ _, .contextEq _ _
 | .type _ _, .typeEq _ _ _
 | .type _ _, .termEq _ _ _ _
 | .type _ _, .substitutionEq _ _ _ _
 | .type _ _, .predicate _ _
 | .type _ _, .entails _ _
 | .type _ _, .predicateEq _ _ _
 | .term _ _ _, .context _
 | .term _ _ _, .type _ _
 | .term _ _ _, .substitution _ _ _
 | .term _ _ _, .contextEq _ _
 | .term _ _ _, .typeEq _ _ _
 | .term _ _ _, .termEq _ _ _ _
 | .term _ _ _, .substitutionEq _ _ _ _
 | .term _ _ _, .predicate _ _
 | .term _ _ _, .entails _ _
 | .term _ _ _, .predicateEq _ _ _
 | .substitution _ _ _, .context _
 | .substitution _ _ _, .type _ _
 | .substitution _ _ _, .term _ _ _
 | .substitution _ _ _, .contextEq _ _
 | .substitution _ _ _, .typeEq _ _ _
 | .substitution _ _ _, .termEq _ _ _ _
 | .substitution _ _ _, .substitutionEq _ _ _ _
 | .substitution _ _ _, .predicate _ _
 | .substitution _ _ _, .entails _ _
 | .substitution _ _ _, .predicateEq _ _ _
 | .contextEq _ _, .context _
 | .contextEq _ _, .type _ _
 | .contextEq _ _, .term _ _ _
 | .contextEq _ _, .substitution _ _ _
 | .contextEq _ _, .typeEq _ _ _
 | .contextEq _ _, .termEq _ _ _ _
 | .contextEq _ _, .substitutionEq _ _ _ _
 | .contextEq _ _, .predicate _ _
 | .contextEq _ _, .entails _ _
 | .contextEq _ _, .predicateEq _ _ _
 | .typeEq _ _ _, .context _
 | .typeEq _ _ _, .type _ _
 | .typeEq _ _ _, .term _ _ _
 | .typeEq _ _ _, .substitution _ _ _
 | .typeEq _ _ _, .contextEq _ _
 | .typeEq _ _ _, .termEq _ _ _ _
 | .typeEq _ _ _, .substitutionEq _ _ _ _
 | .typeEq _ _ _, .predicate _ _
 | .typeEq _ _ _, .entails _ _
 | .typeEq _ _ _, .predicateEq _ _ _
 | .termEq _ _ _ _, .context _
 | .termEq _ _ _ _, .type _ _
 | .termEq _ _ _ _, .term _ _ _
 | .termEq _ _ _ _, .substitution _ _ _
 | .termEq _ _ _ _, .contextEq _ _
 | .termEq _ _ _ _, .typeEq _ _ _
 | .termEq _ _ _ _, .substitutionEq _ _ _ _
 | .termEq _ _ _ _, .predicate _ _
 | .termEq _ _ _ _, .entails _ _
 | .termEq _ _ _ _, .predicateEq _ _ _
 | .substitutionEq _ _ _ _, .context _
 | .substitutionEq _ _ _ _, .type _ _
 | .substitutionEq _ _ _ _, .term _ _ _
 | .substitutionEq _ _ _ _, .substitution _ _ _
 | .substitutionEq _ _ _ _, .contextEq _ _
 | .substitutionEq _ _ _ _, .typeEq _ _ _
 | .substitutionEq _ _ _ _, .termEq _ _ _ _
 | .substitutionEq _ _ _ _, .predicate _ _
 | .substitutionEq _ _ _ _, .entails _ _
 | .substitutionEq _ _ _ _, .predicateEq _ _ _
 | .predicate _ _, .context _
 | .predicate _ _, .type _ _
 | .predicate _ _, .term _ _ _
 | .predicate _ _, .substitution _ _ _
 | .predicate _ _, .contextEq _ _
 | .predicate _ _, .typeEq _ _ _
 | .predicate _ _, .termEq _ _ _ _
 | .predicate _ _, .substitutionEq _ _ _ _
 | .predicate _ _, .entails _ _
 | .predicate _ _, .predicateEq _ _ _
 | .entails _ _, .context _
 | .entails _ _, .type _ _
 | .entails _ _, .term _ _ _
 | .entails _ _, .substitution _ _ _
 | .entails _ _, .contextEq _ _
 | .entails _ _, .typeEq _ _ _
 | .entails _ _, .termEq _ _ _ _
 | .entails _ _, .substitutionEq _ _ _ _
 | .entails _ _, .predicate _ _
 | .entails _ _, .predicateEq _ _ _
 | .predicateEq _ _ _, .context _
 | .predicateEq _ _ _, .type _ _
 | .predicateEq _ _ _, .term _ _ _
 | .predicateEq _ _ _, .substitution _ _ _
 | .predicateEq _ _ _, .contextEq _ _
 | .predicateEq _ _ _, .typeEq _ _ _
 | .predicateEq _ _ _, .termEq _ _ _ _
 | .predicateEq _ _ _, .substitutionEq _ _ _ _
 | .predicateEq _ _ _, .predicate _ _
 | .predicateEq _ _ _, .entails _ _
    => isFalse (by intro same; cases same)

instance : DecidableEq (Judgment S) := Judgment.decEq

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
