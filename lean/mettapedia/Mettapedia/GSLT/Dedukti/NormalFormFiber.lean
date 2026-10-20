import Mettapedia.GSLT.Dedukti.PeanoFiber
import Mettapedia.GSLT.Dedukti.Separation
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# The normal-form fiber of the λΠ-calculus modulo rewriting

The checker of the λΠ-calculus modulo rewriting decides conversion by reducing
both sides to normal form and comparing the results.  Call a theory and a set
`S` of terms (for instance the typed terms of a context) **in the normal-form
fiber** when that procedure is correct on `S`: every term of `S` has a normal
form, and two terms of `S` are convertible exactly when their normal forms are
equal (`Mettapedia.Logic.Relation.DecidedOn`).

## Where the fiber is

* For a set closed under steps, the fiber is weak normalization together with
  the Church–Rosser property on the set (`decidedOn_iff_churchRosser`, in
  `NormalFormDecision`).
* **For a confluent theory, the fiber is exactly where reduction normalizes**
  (`decidedOn_iff_weaklyNormalizingOn_of_confluent`), on every set, closed
  under steps or not.  An orthogonal theory is confluent
  (`confluent_of_orthogonal`), so for the orthogonal algebraic theories the
  fiber is exactly weak normalization (`decidedOn_iff_weaklyNormalizingOn_of_orthogonal`).
  Orthogonality alone does not put a theory in the fiber: the single rule
  `add x y ↪ add y x` passes the orthogonality test and `add x y` has no
  normal form (`orthogonal_not_in_fiber`).
* Inhabited: conversion of closed arithmetic expressions under the recursion
  rules of addition is decided by normal forms (`PeanoFiber.peano_decidedOn`).

## The operational reading

The GSLT of a step relation has a native OSLF type observing undirected
conversion (`IndexedOperational.satisfies_conversionNativeType_iff`).  On a
set in the fiber, that observation holds between two terms exactly when the
normal forms computed by directed steps are equal
(`satisfies_conversionNativeType_iff_normalForm_eq`); for the recursion rules
of addition it relates `2 + 3` with `5` and not with `4`
(`peano_oslf_two_plus_three`).  Outside the fiber the observation keeps its
meaning, but the running engine does not decide it.

## Three boundaries

Each is a property of conversion that no theory with that conversion can have
in the fiber, stated for the sets of terms that exhibit it.

* **Nondeterminism.**  With the two rules `choose x y ↪ x` and
  `choose x y ↪ y`, the term `choose x y` has two distinct normal forms, so no
  set containing it is decided by normal forms
  (`withChoice_not_decidedOn`).  Conversion with choice identifies every two
  terms (`withChoice_conv_all`).
* **Identified variables.**  In a theory whose rules are headed by constants,
  variables are normal, so a conversion that identifies two distinct
  variables (proof irrelevance does) is decided by normal forms on no set
  containing them (`not_decidedOn_of_conv_vars`); the same holds for a
  variable and its eta-expansion (`not_decidedOn_of_conv_eta`).
* **Symmetry.**  A conversion that makes a binary operator commutative on
  variables, and keeps `f u x` apart from `f v x`, is decided by normal forms
  on no set containing `f x y` and `f y x`, in any theory with closed
  definitions (`Commutativity.not_decidedOn_of_commutative`).

The first boundary is shared with the meet-closed fiber of least sufficient
bubbles, where disjunction is the obstruction; the second and the third are
specific to deciding an equation by orienting it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.NormalFormFiber

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn WeaklyNormalizingOn
  decidedOn_of_confluent)

variable {theory : Theory}

/-! ## Where the fiber is -/

/-- **For a confluent theory, conversion is decided by normal forms exactly
where reduction normalizes.** -/
theorem decidedOn_iff_weaklyNormalizingOn_of_confluent (confluent : Confluent (Step theory))
    (S : Set Term) : DecidedOn (Step theory) S ↔ WeaklyNormalizingOn (Step theory) S :=
  ⟨fun decided => decided.1, decidedOn_of_confluent confluent⟩

/-- **For an orthogonal theory, conversion is decided by normal forms exactly
where reduction normalizes.** -/
theorem decidedOn_iff_weaklyNormalizingOn_of_orthogonal (orthogonal : theory.Orthogonal)
    (S : Set Term) : DecidedOn (Step theory) S ↔ WeaklyNormalizingOn (Step theory) S :=
  decidedOn_iff_weaklyNormalizingOn_of_confluent (confluent_of_orthogonal orthogonal) S

/-- **Orthogonality does not put a theory in the fiber**: the commutation rule
passes the orthogonality test, and conversion is decided by normal forms on no
set containing `add x y`. -/
theorem orthogonal_not_in_fiber :
    orthogonalCheck [Commutativity.Witness.commRule] = true ∧
      ∀ S : Set Term, Commutativity.op Commutativity.Witness.add (.var 0) (.var 1) ∈ S →
        ¬ DecidedOn (Step Commutativity.Witness.commTheory) S := by
  refine ⟨Commutativity.Witness.commTheory_check, fun S member decided => ?_⟩
  obtain ⟨normal, normalForm⟩ := decided.1 _ member
  exact Commutativity.Witness.commTheory_no_normalForm normal normalForm

/-! ## Boundaries -/

/-- Two distinct convertible normal terms of `S` block the decision. -/
theorem not_decidedOn_of_conv_normal {S : Set Term} {first second : Term}
    (firstMember : first ∈ S) (secondMember : second ∈ S)
    (firstNormal : IsNormal (Step theory) first) (secondNormal : IsNormal (Step theory) second)
    (distinct : first ≠ second) (converted : Conv theory first second) :
    ¬ DecidedOn (Step theory) S := fun decided =>
  distinct ((decided.2 first firstMember second secondMember first second
    ⟨.refl, firstNormal⟩ ⟨.refl, secondNormal⟩).mp converted)

/-- **A conversion identifying two distinct variables is outside the fiber**,
in every theory whose rules are headed by constants. -/
theorem not_decidedOn_of_conv_vars (headed : theory.Headed) {S : Set Term} {first second : Nat}
    (distinct : first ≠ second) (firstMember : .var first ∈ S) (secondMember : .var second ∈ S)
    (converted : Conv theory (.var first) (.var second)) : ¬ DecidedOn (Step theory) S :=
  not_decidedOn_of_conv_normal firstMember secondMember (var_normal headed first)
    (var_normal headed second) (by simpa using distinct) converted

/-- The eta-expansion `λ y : A. x y` of a variable is normal when `A` is, in a
theory whose rules are headed by constants. -/
theorem etaExpansion_normal (headed : theory.Headed) {domain : Term}
    (domainNormal : IsNormal (Step theory) domain) (index : Nat) :
    IsNormal (Step theory) (.lam domain (.app (.var (index + 1)) (.var 0))) := by
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact domainNormal _ inner
  · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · rcases root.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
      · cases same
      · simp [headConst] at head
    · exact var_normal headed _ _ inner'
    · exact var_normal headed _ _ inner'

/-- **Eta on a variable is outside the fiber**, in every theory whose rules
are headed by constants. -/
theorem not_decidedOn_of_conv_eta (headed : theory.Headed) {S : Set Term} {domain : Term}
    (domainNormal : IsNormal (Step theory) domain) (index : Nat)
    (variableMember : .var index ∈ S)
    (expansionMember : .lam domain (.app (.var (index + 1)) (.var 0)) ∈ S)
    (converted : Conv theory (.var index) (.lam domain (.app (.var (index + 1)) (.var 0)))) :
    ¬ DecidedOn (Step theory) S :=
  not_decidedOn_of_conv_normal variableMember expansionMember (var_normal headed index)
    (etaExpansion_normal headed domainNormal index) (by simp) converted

/-- **Choice is outside the fiber**: `choose x y` has the two normal forms `x`
and `y`. -/
theorem withChoice_not_decidedOn (headed : theory.Headed) {S : Set Term}
    (member : choose (.var 0) (.var 1) ∈ S) : ¬ DecidedOn (Step (withChoice theory)) S := by
  intro decided
  have choiceHeaded := withChoice_headed headed
  have same := decided.normalForm_unique member
    ⟨.single (step_choose_left theory (.var 0) (.var 1)), var_normal choiceHeaded 0⟩
    ⟨.single (step_choose_right theory (.var 0) (.var 1)), var_normal choiceHeaded 1⟩
  simp at same

/-! ## The operational reading: OSLF conversion observations -/

/-- **In the fiber, the OSLF conversion observation is decided by the running
engine.**  The native conversion type of the GSLT of a step relation observes
undirected conversion (`satisfies_conversionNativeType_iff`); on a set in the
normal-form fiber it holds between two terms exactly when the normal forms
computed by directed steps are equal. -/
theorem satisfies_conversionNativeType_iff_normalForm_eq {α : Type} {step : α → α → Prop}
    {S : Set α} (decided : DecidedOn step S) {left right : α} (leftMember : left ∈ S)
    (rightMember : right ∈ S) {leftNormal rightNormal : α}
    (leftNormalForm : IsNormalFormOf step left leftNormal)
    (rightNormalForm : IsNormalFormOf step right rightNormal) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF (Mettapedia.GSLT.IndexedOperational.conversionTheory step)).satisfies (S := ())
        left (Mettapedia.GSLT.IndexedOperational.conversionNativeType step right).pred ↔ leftNormal = rightNormal :=
  (Mettapedia.GSLT.IndexedOperational.satisfies_conversionNativeType_iff step left right).trans
    (decided.2 left leftMember right rightMember leftNormal rightNormal leftNormalForm
      rightNormalForm)

/-! ## Controls: every hypothesis above is met -/

/-- The recursion rules of addition are in the fiber on closed arithmetic
expressions, through the orthogonal characterization. -/
theorem peano_in_fiber :
    DecidedOn (Step PeanoFiber.peanoTheory) {term | PeanoFiber.IsArith term} :=
  (decidedOn_iff_weaklyNormalizingOn_of_orthogonal PeanoFiber.peano_orthogonal _).mpr
    PeanoFiber.peano_weaklyNormalizing

/-- Choice over the empty theory: `choose x y` is decided by normal forms on no
set containing it. -/
theorem emptyChoice_not_decidedOn :
    ¬ DecidedOn (Step (withChoice Theory.empty)) {choose (.var 0) (.var 1)} :=
  withChoice_not_decidedOn Theory.empty_headed rfl

/-- Choice over the empty theory identifies two variables, so no set containing
them is decided by normal forms. -/
theorem emptyChoice_vars_not_decidedOn :
    ¬ DecidedOn (Step (withChoice Theory.empty)) {.var 0, .var 1} :=
  not_decidedOn_of_conv_vars (withChoice_headed Theory.empty_headed) (by decide)
    (Or.inl rfl) (Or.inr rfl) (withChoice_conv_all Theory.empty _ _)

/-- Choice over the empty theory converts a variable with its eta-expansion,
so no set containing both is decided by normal forms. -/
theorem emptyChoice_eta_not_decidedOn :
    ¬ DecidedOn (Step (withChoice Theory.empty))
      {.var 0, .lam (.srt .type) (.app (.var 1) (.var 0))} :=
  not_decidedOn_of_conv_eta (withChoice_headed Theory.empty_headed)
    (srt_normal (withChoice_headed Theory.empty_headed) .type) 0 (Or.inl rfl) (Or.inr rfl)
    (withChoice_conv_all Theory.empty _ _)

theorem arith_two_plus_three :
    PeanoFiber.IsArith (PeanoFiber.plus (PeanoFiber.numeral 2) (PeanoFiber.numeral 3)) :=
  .plus (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))

theorem arith_five : PeanoFiber.IsArith (PeanoFiber.numeral 5) :=
  .succ (.succ (.succ (.succ (.succ .zero))))

theorem arith_four : PeanoFiber.IsArith (PeanoFiber.numeral 4) :=
  .succ (.succ (.succ (.succ .zero)))

theorem two_plus_three_normalForm : IsNormalFormOf (Step PeanoFiber.peanoTheory)
    (PeanoFiber.plus (PeanoFiber.numeral 2) (PeanoFiber.numeral 3)) (PeanoFiber.numeral 5) :=
  ⟨PeanoFiber.reduces_plus_numerals 2 3, PeanoFiber.numeral_normal 5⟩

/-- The OSLF conversion observation of the recursion rules of addition relates
`2 + 3` with `5`, and not with `4`, read off normal forms. -/
theorem peano_oslf_two_plus_three :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (Mettapedia.GSLT.IndexedOperational.conversionTheory (Step PeanoFiber.peanoTheory))).satisfies (S := ())
        (PeanoFiber.plus (PeanoFiber.numeral 2) (PeanoFiber.numeral 3))
        (Mettapedia.GSLT.IndexedOperational.conversionNativeType (Step PeanoFiber.peanoTheory) (PeanoFiber.numeral 5)).pred ∧
      ¬ (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (Mettapedia.GSLT.IndexedOperational.conversionTheory (Step PeanoFiber.peanoTheory))).satisfies (S := ())
        (PeanoFiber.plus (PeanoFiber.numeral 2) (PeanoFiber.numeral 3))
        (Mettapedia.GSLT.IndexedOperational.conversionNativeType (Step PeanoFiber.peanoTheory) (PeanoFiber.numeral 4)).pred :=
  ⟨(satisfies_conversionNativeType_iff_normalForm_eq PeanoFiber.peano_decidedOn arith_two_plus_three
      arith_five two_plus_three_normalForm ⟨.refl, PeanoFiber.numeral_normal 5⟩).mpr rfl,
    fun holds => absurd (PeanoFiber.numeral_injective
      ((satisfies_conversionNativeType_iff_normalForm_eq PeanoFiber.peano_decidedOn
        arith_two_plus_three arith_four two_plus_three_normalForm
        ⟨.refl, PeanoFiber.numeral_normal 4⟩).mp holds)) (by decide)⟩

#print axioms decidedOn_iff_weaklyNormalizingOn_of_confluent
#print axioms decidedOn_iff_weaklyNormalizingOn_of_orthogonal
#print axioms orthogonal_not_in_fiber
#print axioms not_decidedOn_of_conv_vars
#print axioms not_decidedOn_of_conv_eta
#print axioms withChoice_not_decidedOn
#print axioms peano_in_fiber
#print axioms emptyChoice_not_decidedOn
#print axioms emptyChoice_vars_not_decidedOn
#print axioms emptyChoice_eta_not_decidedOn
#print axioms satisfies_conversionNativeType_iff_normalForm_eq
#print axioms peano_oslf_two_plus_three

end Mettapedia.GSLT.Dedukti.NormalFormFiber
