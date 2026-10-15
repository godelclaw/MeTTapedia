import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilnerQuotient
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Functor.Const

/-!
# Coherent restriction of complete finite-depth observations

The actual observation quotients form a presheaf over the depth order.
Restriction sends a supplied original state to its smaller-depth class and
obeys identity and composition. Bounded modal predicates and whole supplied
dependent witnesses compare through these same restriction maps.

Depth is an observation parameter. No price, executor or funding schedule is
assigned by this diagram.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.FiniteDepth

open _root_.CategoryTheory _root_.Opposite

universe uAtom uLabel uValue

variable {S : GSLT} (M : System.{uAtom, uLabel} S)

theorem rounds_restrict (smaller larger : Nat) (within : smaller ≤ larger)
    {first second : S.Term} (related : Rounds M larger first second) :
    Rounds M smaller first second := by
  induction larger with
  | zero =>
      have same : smaller = 0 := Nat.eq_zero_of_le_zero within
      subst smaller
      exact related
  | succ larger inductionHypothesis =>
      rcases Nat.eq_or_lt_of_le within with same | strict
      · subst smaller
        exact related
      · exact inductionHypothesis (Nat.le_of_lt_succ strict)
          (rounds_drop M larger related)

def restriction (smaller larger : Nat) (within : smaller ≤ larger) :
    Approximation M larger → Approximation M smaller :=
  Quotient.lift (fun state => (⟦state⟧ : Approximation M smaller))
    (fun _ _ related => Quotient.sound (rounds_restrict M smaller larger within related))

theorem restriction_state (smaller larger : Nat) (within : smaller ≤ larger) (state : S.Term) :
    restriction M smaller larger within ⟦state⟧ = (⟦state⟧ : Approximation M smaller) := rfl

theorem restriction_surjective (smaller larger : Nat) (within : smaller ≤ larger) :
    Function.Surjective (restriction M smaller larger within) := by
  intro value
  refine Quotient.inductionOn value ?_
  intro state
  exact ⟨⟦state⟧, rfl⟩

theorem restriction_identity (depth : Nat) (value : Approximation M depth) :
    restriction M depth depth le_rfl value = value := by
  refine Quotient.inductionOn value ?_
  intro state
  rfl

theorem restriction_composition (first middle last : Nat)
    (before : first ≤ middle) (after : middle ≤ last) (value : Approximation M last) :
    restriction M first middle before (restriction M middle last after value) =
      restriction M first last (le_trans before after) value := by
  refine Quotient.inductionOn value ?_
  intro state
  rfl

def observationClasses : Natᵒᵖ ⥤ Type where
  obj depth := Approximation M depth.unop
  map change := TypeCat.ofHom (restriction M _ _ (leOfHom change.unop))
  map_id depth := by
    apply ConcreteCategory.hom_ext
    intro value
    exact restriction_identity M depth.unop value
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (restriction_composition M _ _ _ (leOfHom second.unop) (leOfHom first.unop) value).symm

def stateClassifications :
    (Functor.const Natᵒᵖ).obj S.Term ⟶ observationClasses M where
  app depth := TypeCat.ofHom (fun state => (⟦state⟧ : Approximation M depth.unop))
  naturality first second change := by
    apply ConcreteCategory.hom_ext
    intro state
    rfl

theorem bounded_formula_restriction (formula : Formula M.Atom M.Label)
    (smaller larger : Nat) (bounded : formula.depth ≤ smaller) (within : smaller ≤ larger)
    (value : Approximation M larger) :
    formulaPredicate M smaller formula bounded (restriction M smaller larger within value) ↔
      formulaPredicate M larger formula (le_trans bounded within) value := by
  refine Quotient.inductionOn value ?_
  intro state
  exact Iff.rfl

def pullFamily {smaller larger : Nat} (within : smaller ≤ larger)
    (family : Approximation M smaller → Type uValue) : Approximation M larger → Type uValue :=
  fun value => family (restriction M smaller larger within value)

theorem pullFamily_identity (depth : Nat) (family : Approximation M depth → Type uValue) :
    pullFamily M le_rfl family = family := by
  funext value
  exact congrArg family (restriction_identity M depth value)

theorem pullFamily_composition {first middle last : Nat}
    (before : first ≤ middle) (after : middle ≤ last) (family : Approximation M first → Type uValue) :
    pullFamily M after (pullFamily M before family) = pullFamily M (le_trans before after) family := by
  funext value
  exact congrArg family (restriction_composition M first middle last before after value)

def suppliedWitnessComparison {smaller larger : Nat} (within : smaller ≤ larger)
    (family : Approximation M smaller → Type uValue) (state : S.Term) :
    pullFamily M within family (⟦state⟧ : Approximation M larger) ≃
      family (⟦state⟧ : Approximation M smaller) :=
  Equiv.cast (congrArg family (restriction_state M smaller larger within state))

theorem supplied_witness_recovered {smaller larger : Nat} (within : smaller ≤ larger)
    (family : Approximation M smaller → Type uValue) (state : S.Term)
    (witness : family (⟦state⟧ : Approximation M smaller)) :
    (suppliedWitnessComparison M within family state)
      ((suppliedWitnessComparison M within family state).symm witness) = witness :=
  (suppliedWitnessComparison M within family state).apply_symm_apply witness

end Mettapedia.GSLT.HennessyMilner.FiniteDepth
