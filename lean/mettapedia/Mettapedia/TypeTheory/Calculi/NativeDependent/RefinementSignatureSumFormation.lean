import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumDerivations

/-!
# Earlier-symbol formation survives native signature inclusion

Both declaration alphabets retain their original ranks. The complete
translated derivation retains every earlier-symbol obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

open Mettapedia.TypeTheory

universe u
variable {S T : Symbols.{u}} (left : Signature S) (right : Signature T)

@[simp] theorem before_cast {D : Signature S} {first second : Judgment S}
    (equal : first = second) (tree : Derivation D first) (bound : Nat) :
    (cast (congrArg (Derivation D) equal) tree).before bound ↔ tree.before bound := by
  cases equal
  rfl

@[simp] theorem contextLeft_signature_before {n : Nat}
    (expression : ContextExpr S n) (bound : Nat) :
    (contextLeft expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before left.typeRank left.termRank left.predicateRank bound :=
  contextLeft_before (ranks left) (ranks right) bound expression

@[simp] theorem typeLeft_signature_before {n : Nat}
    (expression : TypeExpr S n) (bound : Nat) :
    (typeLeft expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before left.typeRank left.termRank left.predicateRank bound :=
  typeLeft_before (ranks left) (ranks right) bound expression

@[simp] theorem termLeft_signature_before {n : Nat}
    (expression : TermExpr S n) (bound : Nat) :
    (termLeft expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before left.typeRank left.termRank left.predicateRank bound :=
  termLeft_before (ranks left) (ranks right) bound expression

@[simp] theorem propLeft_signature_before {n : Nat}
    (expression : PropExpr S n) (bound : Nat) :
    (propLeft expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before left.typeRank left.termRank left.predicateRank bound :=
  propLeft_before (ranks left) (ranks right) bound expression

@[simp] theorem judgmentLeft_before (judgment : Judgment S) (bound : Nat) :
    (judgmentLeft judgment).before (signature left right) bound ↔
      judgment.before left bound := by
  cases judgment <;> simp [judgmentLeft, Judgment.before, substitutionLeft]

theorem derivationLeft_before : ∀ {judgment : Judgment S}
    (tree : Derivation left judgment) (bound : Nat), tree.before bound →
    (derivationLeft left right tree).before bound
  | _, .node rule premises, bound, earlier => by
      change (ruleLeft rule.val).conclusion.before (signature left right) bound ∧
        ∀ position, Derivation.before bound (cast
          (congrArg (JudgmentDerivation.Derivation (judgmentSignature (signature left right)))
            ((mapLeft left right).hypothesis rule position))
          (derivationLeft left right
            (premises ((mapLeft left right).position rule position))))
      constructor
      · rw [ruleLeft_conclusion]
        exact (judgmentLeft_before left right rule.val.conclusion bound).mpr earlier.1
      · intro position
        exact (before_cast ((mapLeft left right).hypothesis rule position) _ bound).mpr
          (derivationLeft_before (premises ((mapLeft left right).position rule position))
            bound (earlier.2 ((mapLeft left right).position rule position)))

@[simp] theorem contextRight_signature_before {n : Nat}
    (expression : ContextExpr T n) (bound : Nat) :
    (contextRight expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before right.typeRank right.termRank right.predicateRank bound :=
  contextRight_before (ranks left) (ranks right) bound expression

@[simp] theorem typeRight_signature_before {n : Nat}
    (expression : TypeExpr T n) (bound : Nat) :
    (typeRight expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before right.typeRank right.termRank right.predicateRank bound :=
  typeRight_before (ranks left) (ranks right) bound expression

@[simp] theorem termRight_signature_before {n : Nat}
    (expression : TermExpr T n) (bound : Nat) :
    (termRight expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before right.typeRank right.termRank right.predicateRank bound :=
  termRight_before (ranks left) (ranks right) bound expression

@[simp] theorem propRight_signature_before {n : Nat}
    (expression : PropExpr T n) (bound : Nat) :
    (propRight expression).before (signature left right).typeRank
      (signature left right).termRank (signature left right).predicateRank bound ↔
    expression.before right.typeRank right.termRank right.predicateRank bound :=
  propRight_before (ranks left) (ranks right) bound expression

@[simp] theorem judgmentRight_before (judgment : Judgment T) (bound : Nat) :
    (judgmentRight judgment).before (signature left right) bound ↔
      judgment.before right bound := by
  cases judgment <;> simp [judgmentRight, Judgment.before, substitutionRight]

theorem derivationRight_before : ∀ {judgment : Judgment T}
    (tree : Derivation right judgment) (bound : Nat), tree.before bound →
    (derivationRight left right tree).before bound
  | _, .node rule premises, bound, earlier => by
      change (ruleRight rule.val).conclusion.before (signature left right) bound ∧
        ∀ position, Derivation.before bound (cast
          (congrArg (JudgmentDerivation.Derivation (judgmentSignature (signature left right)))
            ((mapRight left right).hypothesis rule position))
          (derivationRight left right
            (premises ((mapRight left right).position rule position))))
      constructor
      · rw [ruleRight_conclusion]
        exact (judgmentRight_before left right rule.val.conclusion bound).mpr earlier.1
      · intro position
        exact (before_cast ((mapRight left right).hypothesis rule position) _ bound).mpr
          (derivationRight_before (premises ((mapRight left right).position rule position))
            bound (earlier.2 ((mapRight left right).position rule position)))

def headers (first : HeaderFormation left) (second : HeaderFormation right) :
    HeaderFormation (signature left right) where
  typeHeader := fun symbol => match symbol with
    | .inl symbol => derivationLeft left right (first.typeHeader symbol)
    | .inr symbol => derivationRight left right (second.typeHeader symbol)
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact derivationLeft_before left right _ _ (first.typeHeader_before symbol)
    | inr symbol => exact derivationRight_before left right _ _ (second.typeHeader_before symbol)
  termHeader := fun symbol => match symbol with
    | .inl symbol => derivationLeft left right (first.termHeader symbol)
    | .inr symbol => derivationRight left right (second.termHeader symbol)
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact derivationLeft_before left right _ _ (first.termHeader_before symbol)
    | inr symbol => exact derivationRight_before left right _ _ (second.termHeader_before symbol)
  termResult := fun symbol => match symbol with
    | .inl symbol => derivationLeft left right (first.termResult symbol)
    | .inr symbol => derivationRight left right (second.termResult symbol)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact derivationLeft_before left right _ _ (first.termResult_before symbol)
    | inr symbol => exact derivationRight_before left right _ _ (second.termResult_before symbol)
  predicateHeader := fun symbol => match symbol with
    | .inl symbol => derivationLeft left right (first.predicateHeader symbol)
    | .inr symbol => derivationRight left right (second.predicateHeader symbol)
  predicateHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact derivationLeft_before left right _ _ (first.predicateHeader_before symbol)
    | inr symbol => exact derivationRight_before left right _ _ (second.predicateHeader_before symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

