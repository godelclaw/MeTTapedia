import Mettapedia.Languages.MM0.Kernel.Conversion

/-!
# Conversion in definition-free MM0 theories

Without definition bodies, typed conversion relates exactly equal expressions.
This isolates the conversion boundary for compiling first-order rule theories:
conversion nodes can be removed without changing a derivation's conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-- Congruence, symmetry, and transitivity cannot change an expression when
there is no definition available to unfold. -/
theorem Converts.eq_of_no_definitions
    {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {left right : Preterm} {sort : Nat}
    (noDefinitions : ∀ symbol, definitions symbol = none)
    (conversion : Converts signature definitions context left right sort) :
    left = right := by
  induction conversion using Converts.rec
      (motive_2 := fun left right _ _ => left = right) with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | congruence _ _ ih => rw [ih]
  | unfold _ unfolded _ =>
      cases unfolded with
      | intro _ bodyLookup _ _ _ =>
          rw [noDefinitions] at bodyLookup
          cases bodyLookup
  | nil => rfl
  | cons _ _ _ _ ihHead ihTail => exact congrArg₂ List.cons ihHead ihTail

/-- Definition-free conversion is equality together with saturated typing;
syntactic equality alone does not supply the typing premise. -/
theorem converts_iff_eq_and_typed_of_no_definitions
    {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {left right : Preterm} {sort : Nat}
    (noDefinitions : ∀ symbol, definitions symbol = none) :
    Converts signature definitions context left right sort ↔
      left = right ∧ Preterm.HasType signature context left [] sort := by
  constructor
  · intro conversion
    exact ⟨conversion.eq_of_no_definitions noDefinitions, conversion.typed.1⟩
  · rintro ⟨rfl, typed⟩
    exact .refl typed

example {signature : TermSignature} {context : Context} {expression : Preterm}
    {sort : Nat} (typed : Preterm.HasType signature context expression [] sort) :
    Converts signature (fun _ => none) context expression expression sort :=
  .refl typed

example (signature : TermSignature) (context : Context) (sort : Nat) :
    ¬ Converts signature (fun _ => none) context (.term 0) (.term 1) sort := by
  intro conversion
  have equality := conversion.eq_of_no_definitions (fun _ => rfl)
  cases equality

end Mettapedia.Languages.MM0.Kernel
