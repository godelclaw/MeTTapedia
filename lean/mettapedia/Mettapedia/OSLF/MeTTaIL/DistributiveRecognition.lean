import Mettapedia.OSLF.MeTTaIL.DistributiveLaws

/-!
# Reading a distributive declaration off a language

A language declares Meredith's distributive structure with its own grammar and equations: a bag
constructor declaring a flattening algebra with a unit (the composition), a set constructor declaring
a flattening algebra without one (the summation), a constant that both absorb into themselves, and
composition distributing over a sum of two. `recognize` reads that declaration (`Decl`) off the core
language of a sort:

- the composition is the bag constructor of the sort whose algebra has a unit;
- the summation is the set constructor of the sort whose algebra has none;
- the absorbing element is a constant `a` with the equations `{a, P} = a` for both collections;
- composition distributes: `{P, [Q + R]} = [{P, Q} + {P, R}]`.

`recognize_valid`: a recognized declaration is valid. Each recognized equation holds in the model of
the declaration for every instance (`absorbs_equal`, `distributes_equal`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Distributive

open Syntax

/-- A bare collection constructor of a sort: its collection kind and declared algebra. -/
def collectionAlgebra? (category : String) (rule : GrammarRule) : Option (CollType × CollectionAlgebra) :=
  match rule.bareParams, rule.algebra? with
  | [.simple _ (.collection kind (.base element))], some algebra =>
      if rule.category = category ∧ element = category ∧ algebra.flatten = true then some (kind, algebra) else none
  | _, _ => none

/-- The equation `{a, P} = a` of a collection kind, in either orientation. -/
def absorbsShape (kind : CollType) (absorbing : String) (equation : Equation) : Bool :=
  equation.premises.isEmpty &&
    match equation.left, equation.right with
    | .collection actual [.apply label [], .fvar _] none, .apply label' [] =>
        decide (actual = kind ∧ label = absorbing ∧ label' = absorbing)
    | .apply label' [], .collection actual [.apply label [], .fvar _] none =>
        decide (actual = kind ∧ label = absorbing ∧ label' = absorbing)
    | _, _ => false

/-- The equation `{P, [Q + R]} = [{P, Q} + {P, R}]`, with three distinct metavariables, in either
orientation. -/
def distributesShape (product sum : CollType) (equation : Equation) : Bool :=
  let oriented (left right : Pattern) : Bool :=
    match left, right with
    | .collection p₁ [.fvar x, .collection s₁ [.fvar y, .fvar z] none] none,
        .collection s₂ [.collection p₂ [.fvar x₂, .fvar y₂] none,
          .collection p₃ [.fvar x₃, .fvar z₃] none] none =>
        decide (p₁ = product ∧ p₂ = product ∧ p₃ = product ∧ s₁ = sum ∧ s₂ = sum ∧
          x₂ = x ∧ x₃ = x ∧ y₂ = y ∧ z₃ = z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z)
    | _, _ => false
  equation.premises.isEmpty && (oriented equation.left equation.right || oriented equation.right equation.left)

/-- **The distributive declaration of a sort**, when the language makes one. -/
def recognize (language : LanguageDef) (category : String) : Option Decl := do
  let (product, productAlgebra) ← language.terms.findSome? fun rule =>
    match collectionAlgebra? category rule with
    | some (kind, algebra) => if kind = .hashBag ∧ algebra.unit.isSome then some (kind, algebra) else none
    | none => none
  let unit ← productAlgebra.unit
  let sum ← language.terms.findSome? fun rule =>
    match collectionAlgebra? category rule with
    | some (kind, algebra) => if kind = .hashSet ∧ algebra.unit = none then some kind else none
    | none => none
  let absorbing ← language.terms.findSome? fun rule =>
    if rule.params = [] ∧ rule.category = category ∧ rule.label ≠ unit ∧
        language.equations.any (absorbsShape product rule.label) ∧
        language.equations.any (absorbsShape sum rule.label) then some rule.label else none
  if language.equations.any (distributesShape product sum) then
    some ⟨product, unit, sum, absorbing⟩
  else none

theorem recognize_some {language : LanguageDef} {category : String} {decl : Decl}
    (found : recognize language category = some decl) :
    decl.product = .hashBag ∧ decl.sum = .hashSet ∧ decl.unit ≠ decl.absorbing ∧
      language.equations.any (absorbsShape decl.product decl.absorbing) = true ∧
      language.equations.any (absorbsShape decl.sum decl.absorbing) = true ∧
      language.equations.any (distributesShape decl.product decl.sum) = true := by
  unfold recognize at found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨⟨product, productAlgebra⟩, productFound, unit, unitFound, sum, sumFound, absorbing, absorbingFound,
    rest⟩ := found
  split at rest
  · rename_i distributes
    cases rest
    obtain ⟨rule, _, productOk⟩ := List.exists_of_findSome?_eq_some productFound
    split at productOk
    · split at productOk
      · rename_i kind algebra _ shape
        cases productOk
        obtain ⟨sumRule, _, sumOk⟩ := List.exists_of_findSome?_eq_some sumFound
        split at sumOk
        · split at sumOk
          · rename_i sumKind sumAlgebra _ sumShape
            cases sumOk
            obtain ⟨absorbingRule, _, absorbingOk⟩ := List.exists_of_findSome?_eq_some absorbingFound
            split at absorbingOk
            · rename_i conditions
              cases absorbingOk
              exact ⟨shape.1, sumShape.1, Ne.symm conditions.2.2.1, by simpa using conditions.2.2.2.1,
                by simpa using conditions.2.2.2.2, distributes⟩
            · cases absorbingOk
          · cases sumOk
        · cases sumOk
      · cases productOk
    · cases productOk
  · cases rest

/-- **A recognized declaration is valid.** -/
theorem recognize_valid {language : LanguageDef} {category : String} {decl : Decl}
    (found : recognize language category = some decl) : decl.Valid := by
  obtain ⟨product, sum, unitAbsorbing, _⟩ := recognize_some found
  exact ⟨by rw [product, sum]; decide, product, by rw [sum]; rfl, unitAbsorbing⟩

/-- **The absorbing element absorbs a composition**: every instance of `{a, P} = a` is an equality of
the model. -/
theorem absorbs_product_equal (decl : Decl) (process : Pattern) :
    Equal decl (.collection decl.product [.apply decl.absorbing [], process] none) (.apply decl.absorbing []) :=
  .rel _ _ (.inr (.inr (Step.absorbProduct (before := []) (after := [process]))))

/-- **The absorbing element absorbs a sum.** -/
theorem absorbs_sum_equal (decl : Decl) (process : Pattern) :
    Equal decl (.collection decl.sum [.apply decl.absorbing [], process] none) (.apply decl.absorbing []) :=
  .rel _ _ (.inr (.inr (Step.absorbSum (before := []) (after := [process]))))

/-- **Composition distributes over a sum of two**: every instance of
`{P, [Q + R]} = [{P, Q} + {P, R}]` is an equality of the model. -/
theorem distributes_equal (decl : Decl) (first second third : Pattern) :
    Equal decl (.collection decl.product [first, .collection decl.sum [second, third] none] none)
      (.collection decl.sum [.collection decl.product [first, second] none,
        .collection decl.product [first, third] none] none) :=
  .rel _ _ (.inr (.inr (Step.distribute (before := [first]) (after := []) (summands := [second, third])
    (by simp))))

end Mettapedia.OSLF.MeTTaIL.Distributive
