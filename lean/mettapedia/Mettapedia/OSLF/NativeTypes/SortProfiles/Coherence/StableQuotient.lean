import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableConsequences
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableSource

open Mettapedia.OSLF.Framework

/-!
# Executable sort reading on typed display equation classes

The generated argument/result slots determine a partial sort evaluator.
For a checked stable profile its value descends to arbitrary display terms
modulo typed equation instances, operation contexts and equation detours.
Rejected formation remains absent rather than acquiring a result sort.

This quotient uses the compiled display type-former signature. It does not
identify its terms with every scoped pattern of the operational language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

def displaySort (profile : Profile S) (valuation : Nat → HSort) (term : Term S) : Option HSort :=
  term.evaluate (partialModel profile) (fun index => some (valuation index))

theorem displaySort_exact (profile : Profile S) (valuation : Nat → HSort)
    (term : Term S) (sort : HSort) :
    displaySort profile valuation term = some sort ↔ Formed profile valuation term sort :=
  evaluate_iff_formed profile valuation term sort

theorem displaySort_rejection_exact (profile : Profile S) (valuation : Nat → HSort)
    (term : Term S) :
    displaySort profile valuation term = none ↔ ∀ sort, ¬ Formed profile valuation term sort := by
  constructor
  · intro rejected sort formed
    have accepted := (displaySort_exact profile valuation term sort).mpr formed
    rw [rejected] at accepted
    cases accepted
  · intro unformed
    cases computed : displaySort profile valuation term with
    | none => rfl
    | some sort => exact False.elim (unformed sort ((displaySort_exact _ _ _ _).mp computed))

theorem displaySort_equation_invariant {profile : Profile S} {system : EquationSystem S}
    (stable : Stable system profile) (valuation : Nat → HSort) (first second : Term S)
    (equivalent : TypedDisplayConvertibility profile system valuation first second) :
    displaySort profile valuation first = displaySort profile valuation second := by
  apply Option.ext
  intro sort
  rw [displaySort_exact, displaySort_exact]
  exact typed_display_quotient_formation stable valuation first second equivalent sort

def typedDisplaySetoid (profile : Profile S) (system : EquationSystem S)
    (valuation : Nat → HSort) : Setoid (Term S) where
  r := TypedDisplayConvertibility profile system valuation
  iseqv := ⟨Relation.EqvGen.refl, fun equivalent => Relation.EqvGen.symm _ _ equivalent,
    fun first second => Relation.EqvGen.trans _ _ _ first second⟩

abbrev TypedDisplayQuotient (profile : Profile S) (system : EquationSystem S)
    (valuation : Nat → HSort) := Quotient (typedDisplaySetoid profile system valuation)

/-- The computed sort has no dependence on the selected representative of
the checked typed equation class. -/
def quotientSort (profile : Profile S) (system : EquationSystem S)
    (stable : Stable system profile) (valuation : Nat → HSort) :
    TypedDisplayQuotient profile system valuation → Option HSort :=
  Quotient.lift (displaySort profile valuation)
    (displaySort_equation_invariant stable valuation)

theorem quotientSort_class_exact (profile : Profile S) (system : EquationSystem S)
    (stable : Stable system profile) (valuation : Nat → HSort) (term : Term S) (sort : HSort) :
    quotientSort profile system stable valuation
      (Quotient.mk (typedDisplaySetoid profile system valuation) term) = some sort ↔
      Formed profile valuation term sort :=
  displaySort_exact profile valuation term sort

/-- Checking the original authored equation package earns the sort readout
for all terms of its generated finite display signature, at every depth. -/
theorem source_checked_display_sort
    (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (profile : Profile (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (checked : checkStableLanguage? language profile = some true)
    (valuation : Nat → HSort)
    (first second : Term (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (equivalent : TypedDisplayConvertibility profile
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equations language).system valuation first second) :
    displaySort profile valuation first = displaySort profile valuation second := by
  have accepted := (checkStableCompiled?_some_iff
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equations language) profile true).mp checked
  exact displaySort_equation_invariant
    ((checkStable_iff _ _).mp accepted.2) valuation first second equivalent

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
