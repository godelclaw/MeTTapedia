import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-! # Uniform earlier-declaration laws for a bounded native alphabet -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EarlierDeclarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}}

mutual

theorem typeEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) : ∀ {n : Nat} (expression : TypeExpr S n),
    expression.before D.typeRank D.termRank D.predicateRank bound
  | _, .family symbol arguments => ⟨types symbol, fun position =>
      termEarlier D bound types terms predicates (arguments position)⟩
  | _, .propositions => True.intro
  | _, .pi first second => ⟨typeEarlier D bound types terms predicates first,
      typeEarlier D bound types terms predicates second⟩
  | _, .sigma first second => ⟨typeEarlier D bound types terms predicates first,
      typeEarlier D bound types terms predicates second⟩
  | _, .comprehension domain predicate => ⟨typeEarlier D bound types terms predicates domain,
      propEarlier D bound types terms predicates predicate⟩

theorem termEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) : ∀ {n : Nat} (expression : TermExpr S n),
    expression.before D.typeRank D.termRank D.predicateRank bound
  | _, .var _ => True.intro
  | _, .primitive symbol arguments => ⟨terms symbol, fun position =>
      termEarlier D bound types terms predicates (arguments position)⟩
  | _, .lam domain codomain body => ⟨typeEarlier D bound types terms predicates domain,
      typeEarlier D bound types terms predicates codomain,
      termEarlier D bound types terms predicates body⟩
  | _, .app domain body function argument => ⟨typeEarlier D bound types terms predicates domain,
      typeEarlier D bound types terms predicates body,
      termEarlier D bound types terms predicates function,
      termEarlier D bound types terms predicates argument⟩
  | _, .pair domain body first second => ⟨typeEarlier D bound types terms predicates domain,
      typeEarlier D bound types terms predicates body,
      termEarlier D bound types terms predicates first,
      termEarlier D bound types terms predicates second⟩
  | _, .fst domain body pair => ⟨typeEarlier D bound types terms predicates domain,
      typeEarlier D bound types terms predicates body,
      termEarlier D bound types terms predicates pair⟩
  | _, .snd domain body pair => ⟨typeEarlier D bound types terms predicates domain,
      typeEarlier D bound types terms predicates body,
      termEarlier D bound types terms predicates pair⟩
  | _, .sigmaElim domain body motive branch pair =>
      ⟨typeEarlier D bound types terms predicates domain,
       typeEarlier D bound types terms predicates body,
       typeEarlier D bound types terms predicates motive,
       termEarlier D bound types terms predicates branch,
       termEarlier D bound types terms predicates pair⟩
  | _, .quote predicate => propEarlier D bound types terms predicates predicate
  | _, .refine domain predicate value => ⟨typeEarlier D bound types terms predicates domain,
      propEarlier D bound types terms predicates predicate,
      termEarlier D bound types terms predicates value⟩
  | _, .forget domain predicate value => ⟨typeEarlier D bound types terms predicates domain,
      propEarlier D bound types terms predicates predicate,
      termEarlier D bound types terms predicates value⟩

theorem propEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) : ∀ {n : Nat} (expression : PropExpr S n),
    expression.before D.typeRank D.termRank D.predicateRank bound
  | _, .atom symbol arguments => ⟨predicates symbol, fun position =>
      termEarlier D bound types terms predicates (arguments position)⟩
  | _, .truth => True.intro
  | _, .falsehood => True.intro
  | _, .and first second => ⟨propEarlier D bound types terms predicates first,
      propEarlier D bound types terms predicates second⟩
  | _, .or first second => ⟨propEarlier D bound types terms predicates first,
      propEarlier D bound types terms predicates second⟩
  | _, .implies first second => ⟨propEarlier D bound types terms predicates first,
      propEarlier D bound types terms predicates second⟩
  | _, .all domain predicate => ⟨typeEarlier D bound types terms predicates domain,
      propEarlier D bound types terms predicates predicate⟩
  | _, .exists domain predicate => ⟨typeEarlier D bound types terms predicates domain,
      propEarlier D bound types terms predicates predicate⟩
  | _, .holds proposition => termEarlier D bound types terms predicates proposition
  | _, .image expression => typeEarlier D bound types terms predicates expression

end

theorem contextEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) : ∀ {n : Nat} (context : ContextExpr S n),
    context.before D.typeRank D.termRank D.predicateRank bound
  | _, .nil => True.intro
  | _, .snoc previous expression => ⟨contextEarlier D bound types terms predicates previous,
      typeEarlier D bound types terms predicates expression⟩
  | _, .assume previous predicate => ⟨contextEarlier D bound types terms predicates previous,
      propEarlier D bound types terms predicates predicate⟩

theorem judgmentEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) (judgment : Judgment S) : judgment.before D bound := by
  cases judgment <;> simp only [Judgment.before]
  all_goals repeat' constructor
  all_goals first
    | apply contextEarlier D bound types terms predicates
    | apply typeEarlier D bound types terms predicates
    | apply termEarlier D bound types terms predicates
    | apply propEarlier D bound types terms predicates
    | intro position; apply termEarlier D bound types terms predicates

theorem derivationEarlier (D : Signature S) (bound : Nat)
    (types : ∀ symbol, D.typeRank symbol < bound)
    (terms : ∀ symbol, D.termRank symbol < bound)
    (predicates : ∀ symbol, D.predicateRank symbol < bound) : ∀ {judgment : Judgment S} (tree : Derivation D judgment),
    tree.before bound
  | _, .node rule premises => ⟨judgmentEarlier D bound types terms predicates rule.val.conclusion,
      fun position => derivationEarlier D bound types terms predicates (premises position)⟩

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EarlierDeclarations
