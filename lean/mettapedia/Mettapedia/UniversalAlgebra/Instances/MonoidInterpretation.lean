import Mettapedia.UniversalAlgebra.Instances.MonoidWord
import Mettapedia.UniversalAlgebra.Instances.FreeMonoidNormalization
import Mettapedia.UniversalAlgebra.GSLT.ContextualRewriting
import Mettapedia.UniversalAlgebra.EquationSystemInterpretation
import Mettapedia.UniversalAlgebra.InterpretabilityOrder
import Mettapedia.UniversalAlgebra.Instances.MonoidConsequenceInvariance
import Mettapedia.UniversalAlgebra.SemanticService.Interpretation

/-!
# Interpretation controls for monoid equation systems

The monoid equations interpret canonically in their commutative extension.
A redundant extension interprets in both directions.  In contrast, the
identity operation map cannot interpret the commutative extension back in the
monoid equations, because commutativity fails in a free noncommutative monoid.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra
open FreeNormalization

namespace Term

theorem swappedSingletons_ne {word : List Nat} (nonempty : word ≠ [])
    (belowTwo : ∀ index ∈ word, index < 2) :
    word.flatMap (fun index => if index = 0 then [false] else [true]) ≠
      word.flatMap (fun index => if index = 0 then [true] else [false]) := by
  cases word with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have headBelow : head < 2 := belowTwo head (by simp)
      have headCases : head = 0 ∨ head = 1 := by omega
      rcases headCases with rfl | rfl <;> simp

end Term

namespace Signature.Interpretation

variable (interpretation : Signature.Interpretation signature signature)

/-- The binary operation induced by a monoid-signature interpretation in the
free Boolean monoid. -/
def freeBoolMul
    (left right : FreeMonoid Bool) : FreeMonoid Bool :=
  (interpretation.operation .mul).1.evaluateBelow
    (mathlibModel (FreeMonoid Bool))
    (fun position => if position.val = 0 then left else right)
    (interpretation.operation .mul).2

/-- The nullary operation induced by a monoid-signature interpretation in the
free Boolean monoid. -/
def freeBoolOne
    (interpretation : Signature.Interpretation signature signature) :
    FreeMonoid Bool :=
  (interpretation.operation .one).1.evaluateBelow
    (mathlibModel (FreeMonoid Bool)) Fin.elim0
    (interpretation.operation .one).2

@[simp] theorem evaluate_mul_reduct
    (valuation : Nat → FreeMonoid Bool) (left right : Term signature) :
    (mul left right).evaluate
        ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation =
      freeBoolMul interpretation
        (left.evaluate
          ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation)
        (right.evaluate
          ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation) :=
  by
    unfold mul freeBoolMul Model.reduct
    simp only [Term.evaluate]
    congr 2
    funext position
    by_cases first : position.val = 0 <;> simp [first]

@[simp] theorem evaluate_one_reduct
    (valuation : Nat → FreeMonoid Bool) :
    one.evaluate
        ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation =
      freeBoolOne interpretation := by
  unfold one freeBoolOne Model.reduct
  simp only [Term.evaluate]
  congr 2
  funext position
  exact Fin.elim0 position

/-- The interpreted multiplication's free word is obtained by replacing
formal variables zero and one in its operation template. -/
theorem toList_freeBoolMul
    (left right : FreeMonoid Bool) :
    FreeMonoid.toList (freeBoolMul interpretation left right) =
      (Term.variableWord (interpretation.operation .mul).1).flatMap
        (fun index =>
          if _below : index < 2
          then FreeMonoid.toList
            (if index = 0 then left else right)
          else []) := by
  exact Term.toList_evaluateBelow_freeMonoid
    (fun position => if position.val = 0 then left else right)
    (interpretation.operation .mul).1
    (interpretation.operation .mul).2

/-- The template's variable bound removes the unused out-of-range branch. -/
theorem toList_freeBoolMul_words
    (left right : FreeMonoid Bool) :
    FreeMonoid.toList (freeBoolMul interpretation left right) =
      (Term.variableWord (interpretation.operation .mul).1).flatMap
        (fun index => if index = 0 then left.toList else right.toList) := by
  rw [toList_freeBoolMul]
  apply List.flatMap_congr
  intro index member
  have below : index < 2 := Term.variableWord_mem_lt (interpretation.operation .mul).2 member
  by_cases zero : index = 0 <;> simp [below, zero]

/-- A nullary interpreted monoid term has no variable occurrences and hence
evaluates to the native free-monoid unit. -/
theorem toList_freeBoolOne
    (interpretation : Signature.Interpretation signature signature) :
    FreeMonoid.toList (freeBoolOne interpretation) = [] := by
  erw [freeBoolOne, Term.toList_evaluateBelow_freeMonoid]
  rw [Term.variableWord_eq_nil_of_variablesBelow_zero
    (interpretation.operation .one).2]
  rfl

end Signature.Interpretation

/-- The identity operation map interprets the monoid equations in their
commutative extension. -/
def interpretationInCommutative :
    EquationSystem.Interpretation equationSystem
      commutativeEquationSystem where
  symbols := Signature.Interpretation.id signature
  axiom_consequence equation member := by
    simpa only [Equation.translate_id] using
      consequence_lifts_to_commutative
        (EquationalConsequence.of_mem member)

/-- Positive control: the commutative extension is at least as expressive as
the monoid system under algebraic interpretation. -/
theorem monoid_isInterpretableIn_commutative :
    equationSystem.IsInterpretableIn commutativeEquationSystem :=
  ⟨interpretationInCommutative⟩

/-- The redundant extension and the original monoid equations interpret one
another through their shared symbols. -/
theorem derivedExtension_mutuallyInterpretable :
    derivedExtension.IsInterpretableIn equationSystem ∧
      equationSystem.IsInterpretableIn derivedExtension :=
  ⟨⟨EquationSystem.Interpretation.ofSameConsequences
      derivedExtension_sameConsequences⟩,
    ⟨EquationSystem.Interpretation.ofSameConsequences
      derivedExtension_sameConsequences.symm⟩⟩

/-- Commutativity is not generated by the ordinary monoid equations. -/
theorem commutativity_not_consequence :
    ¬ EquationalConsequence equationSystem (mul x y, mul y x) := by
  intro derivation
  have result := consequence_holds_in_monoid derivation (FreeMonoid Bool)
    (fun index => if index = 0 then FreeMonoid.ofList [false]
      else FreeMonoid.ofList [true])
  have listResult := congrArg FreeMonoid.toList result
  simp [x, y] at listResult

/-- Strong negative control: the commutative-monoid equations have no
algebraic interpretation at all in the ordinary monoid equations.  Any binary
monoid term is an ordered word in its arguments; a nonempty word cannot equal
the word obtained by swapping every occurrence of variables zero and one. -/
theorem commutative_not_interpretableIn_monoid :
    ¬ commutativeEquationSystem.IsInterpretableIn equationSystem := by
  rintro ⟨interpretation⟩
  let targetModel : Model signature (FreeMonoid Bool) :=
    mathlibModel (FreeMonoid Bool)
  have targetSatisfies : targetModel.Satisfies equationSystem :=
    mathlibModel_satisfies (FreeMonoid Bool)
  have sourceSatisfies :
      (targetModel.reduct interpretation.symbols).Satisfies
        commutativeEquationSystem :=
    interpretation.reduct_satisfies targetModel targetSatisfies

  have leftUnitMember : (mul one x, x) ∈ commutativeEquationSystem := by
    change (mul one x, x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_left _ (by simp [equationSystem])
  let generator : FreeMonoid Bool := FreeMonoid.of false
  let unitValuation : Nat → FreeMonoid Bool :=
    fun index => if index = 0 then generator else 1
  have unitEquality :=
    sourceSatisfies (mul one x, x) leftUnitMember unitValuation
  have unitLaw :
      Signature.Interpretation.freeBoolMul interpretation.symbols
          (Signature.Interpretation.freeBoolOne interpretation.symbols)
          generator = generator := by
    simpa only [Signature.Interpretation.evaluate_mul_reduct,
      Signature.Interpretation.evaluate_one_reduct, x, Term.evaluate,
      targetModel, unitValuation, if_pos] using unitEquality

  let multiplicationTemplate := (interpretation.symbols.operation .mul).1
  have multiplicationBounded : multiplicationTemplate.VariablesBelow 2 :=
    (interpretation.symbols.operation .mul).2
  have multiplicationWordNonempty :
      Term.variableWord multiplicationTemplate ≠ [] := by
    intro wordEmpty
    dsimp only [multiplicationTemplate] at wordEmpty
    have listLaw := congrArg FreeMonoid.toList unitLaw
    simp [Signature.Interpretation.toList_freeBoolMul_words, wordEmpty, generator] at listLaw

  have commutativityMember : (mul x y, mul y x) ∈
      commutativeEquationSystem := by
    change (mul x y, mul y x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_right _ (by simp)
  let commutativityValuation : Nat → FreeMonoid Bool :=
    fun index => if index = 0 then FreeMonoid.of false
      else FreeMonoid.of true
  have commutativityEquality := sourceSatisfies
    (mul x y, mul y x) commutativityMember commutativityValuation
  have commutativityLaw :
      Signature.Interpretation.freeBoolMul interpretation.symbols
          (FreeMonoid.of false) (FreeMonoid.of true) =
        Signature.Interpretation.freeBoolMul interpretation.symbols
          (FreeMonoid.of true) (FreeMonoid.of false) := by
    simpa only [Signature.Interpretation.evaluate_mul_reduct,
      x, y, Term.evaluate, targetModel, commutativityValuation, if_pos, if_neg,
      Nat.one_ne_zero, if_false] using commutativityEquality

  have wordLaw := congrArg FreeMonoid.toList commutativityLaw
  simp only [Signature.Interpretation.toList_freeBoolMul_words, FreeMonoid.toList_of] at wordLaw
  exact Term.swappedSingletons_ne multiplicationWordNonempty
    (fun index member => Term.variableWord_mem_lt multiplicationBounded member) wordLaw

/-- Negative control: no interpretation with the canonical identity symbol
map sends the commutative equations back into the monoid equations. -/
theorem no_identitySymbol_interpretation_of_commutative_in_monoid :
    ¬ ∃ interpretation : EquationSystem.Interpretation
        commutativeEquationSystem equationSystem,
      interpretation.symbols = Signature.Interpretation.id signature :=
  fun ⟨interpretation, _⟩ => commutative_not_interpretableIn_monoid ⟨interpretation⟩

/-- The commutative extension is strictly above the monoid equations in the
algebraic-interpretability preorder. -/
theorem monoid_strictlyBelow_commutative :
    EquationSystem.InterpretabilityOrder.of equationSystem <
      EquationSystem.InterpretabilityOrder.of commutativeEquationSystem := by
  constructor
  · exact monoid_isInterpretableIn_commutative
  · exact commutative_not_interpretableIn_monoid

/-- The canonical monoid interpretation gives a semantic simulation between
the corresponding SemanticService theory objects. -/
theorem commutativeTheory_semanticallySimulates_monoidTheory :
    Mettapedia.Logic.TheorySimulation.SemanticallySimulates
      (SemanticService.theoryObject commutativeEquationSystem)
      (SemanticService.theoryObject equationSystem) :=
  SemanticService.semanticallySimulates interpretationInCommutative

/-! ## Word observations of contextual execution -/

/-- Orientation changes directed dynamics, but its conversion closure has exactly the word kernel. -/
theorem variableWord_eq_iff_convertibility (orientation : Orientation equationSystem)
    (left right : Term signature) :
    Term.variableWord left = Term.variableWord right ↔
      Relation.EqvGen (ContextualStep orientation) left right :=
  consequence_iff_variableWord_eq.symm.trans
    (consequence_iff_convertibility equationSystem orientation left right)

theorem contextualStep_preserves_variableWord {orientation : Orientation equationSystem}
    {left right : Term signature} (step : ContextualStep orientation left right) :
    Term.variableWord left = Term.variableWord right :=
  (variableWord_eq_iff_convertibility orientation left right).mpr (Relation.EqvGen.rel _ _ step)

theorem contextualRun_preserves_variableWord {orientation : Orientation equationSystem}
    {left right : Term signature}
    (execution : Relation.ReflTransGen (ContextualStep orientation) left right) :
    Term.variableWord left = Term.variableWord right := by
  induction execution with
  | refl => rfl
  | tail _ step agrees => exact agrees.trans (contextualStep_preserves_variableWord step)

end Mettapedia.UniversalAlgebra.Monoid
