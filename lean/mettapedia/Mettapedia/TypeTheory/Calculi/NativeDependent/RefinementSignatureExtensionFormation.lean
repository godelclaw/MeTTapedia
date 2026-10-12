import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtension

/-!
# Header formation in left-preserving native extensions

Rank preservation and the actual contextual header equations transport the
full formation derivations, including every premise's earlier-symbol proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureExtension

open SignatureSum Mettapedia.TypeTheory

universe u
variable {S T : Symbols.{u}} (source : Signature S)
    (target : Signature (SignatureSum.symbols S T)) (comparison : Preserves source target)

def extraRanks : Ranks T :=
  ⟨fun symbol => target.typeRank (.inr symbol),
   fun symbol => target.termRank (.inr symbol),
   fun symbol => target.predicateRank (.inr symbol)⟩

include comparison

theorem typeRanks :
    target.typeRank = (sumRanks (ranks source) (extraRanks target)).typeRank := by
  funext symbol
  cases symbol with
  | inl symbol => exact comparison.typeRank symbol
  | inr symbol => rfl

theorem termRanks :
    target.termRank = (sumRanks (ranks source) (extraRanks target)).termRank := by
  funext symbol
  cases symbol with
  | inl symbol => exact comparison.termRank symbol
  | inr symbol => rfl

theorem predicateRanks :
    target.predicateRank = (sumRanks (ranks source) (extraRanks target)).predicateRank := by
  funext symbol
  cases symbol with
  | inl symbol => exact comparison.predicateRank symbol
  | inr symbol => rfl

@[simp] theorem context_before {n : Nat} (expression : ContextExpr S n) (bound : Nat) :
    (contextLeft expression).before target.typeRank target.termRank target.predicateRank bound ↔
      expression.before source.typeRank source.termRank source.predicateRank bound := by
  rw [typeRanks source target comparison, termRanks source target comparison,
    predicateRanks source target comparison]
  exact contextLeft_before (ranks source) (extraRanks target) bound expression

@[simp] theorem type_before {n : Nat} (expression : TypeExpr S n) (bound : Nat) :
    (typeLeft expression).before target.typeRank target.termRank target.predicateRank bound ↔
      expression.before source.typeRank source.termRank source.predicateRank bound := by
  rw [typeRanks source target comparison, termRanks source target comparison,
    predicateRanks source target comparison]
  exact typeLeft_before (ranks source) (extraRanks target) bound expression

@[simp] theorem term_before {n : Nat} (expression : TermExpr S n) (bound : Nat) :
    (termLeft expression).before target.typeRank target.termRank target.predicateRank bound ↔
      expression.before source.typeRank source.termRank source.predicateRank bound := by
  rw [typeRanks source target comparison, termRanks source target comparison,
    predicateRanks source target comparison]
  exact termLeft_before (ranks source) (extraRanks target) bound expression

@[simp] theorem prop_before {n : Nat} (expression : PropExpr S n) (bound : Nat) :
    (propLeft expression).before target.typeRank target.termRank target.predicateRank bound ↔
      expression.before source.typeRank source.termRank source.predicateRank bound := by
  rw [typeRanks source target comparison, termRanks source target comparison,
    predicateRanks source target comparison]
  exact propLeft_before (ranks source) (extraRanks target) bound expression

theorem judgment_before (judgment : Judgment S) (bound : Nat) :
    (judgmentLeft judgment).before target bound ↔ judgment.before source bound := by
  cases judgment <;>
    simp only [judgmentLeft, Judgment.before, substitutionLeft,
      context_before source target comparison, type_before source target comparison,
      term_before source target comparison, prop_before source target comparison]

theorem derivation_before : ∀ {judgment : Judgment S}
    (tree : Derivation source judgment) (bound : Nat), tree.before bound →
    (derivation source target comparison tree).before bound
  | _, .node original hypotheses, bound, earlier => by
      change (rule source target original.val).conclusion.before target bound ∧
        ∀ position, Derivation.before bound (cast
          (congrArg (JudgmentDerivation.Derivation (judgmentSignature target))
            ((map source target comparison).hypothesis original position))
          (derivation source target comparison
            (hypotheses ((map source target comparison).position original position))))
      constructor
      · rw [conclusion source target comparison]
        exact (judgment_before source target comparison original.val.conclusion bound).mpr earlier.1
      · intro position
        exact (before_cast ((map source target comparison).hypothesis original position) _ bound).mpr
          (derivation_before
            (hypotheses ((map source target comparison).position original position))
            bound (earlier.2 ((map source target comparison).position original position)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureExtension
