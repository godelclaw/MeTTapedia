import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodon
import Mettapedia.Languages.Megalodon.NaturalTheoryProfile

/-!
# The optional Megalodon natural profile on the authored carrier

The option interface is realized so that its preferred infinite function and
omitted point are the existing authored successor and zero. This proves an
actual representation comparison rather than identifying arbitrary choices.
Native proof replay and exact assumption admission are qualified separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodonProfile

open IndexedInductiveNatVec
open Mettapedia.Languages.Megalodon

universe u

noncomputable def choosePreferred {A : Type u} (default preferred : A)
    (predicate : A → Prop) : A := by
  classical
  exact if preferredHolds : predicate preferred then preferred
    else if inhabited : ∃ value, predicate value then Classical.choose inhabited else default

theorem choosePreferred_selects {A : Type u} (default preferred : A) :
    NaturalTheoryProfile.Selects (choosePreferred default preferred) := by
  classical
  intro predicate inhabited
  by_cases preferredHolds : predicate preferred
  · simp [choosePreferred, preferredHolds]
  · simpa [choosePreferred, preferredHolds, inhabited] using Classical.choose_spec inhabited

theorem choosePreferred_of_holds {A : Type u} (default preferred : A)
    {predicate : A → Prop} (holds : predicate preferred) :
    choosePreferred default preferred predicate = preferred := by
  classical
  simp [choosePreferred, holds]

theorem successorIsInfinite : NaturalTheoryProfile.InfiniteFunction Natural.succ := by
  refine ⟨Natural.succ_injective, ?_⟩
  intro onto
  obtain ⟨number, same⟩ := onto Natural.zero
  exact Natural.succ_ne_zero number same

noncomputable def sourceOptions : NaturalTheoryProfile.CarrierOptions Natural.Carrier where
  classical := fun _ notNot => Classical.byContradiction notNot
  chooseNumber := choosePreferred Natural.zero Natural.zero
  chooseFunction := choosePreferred id Natural.succ
  selectsNumber := choosePreferred_selects Natural.zero Natural.zero
  selectsFunction := choosePreferred_selects id Natural.succ
  infinity := ⟨Natural.succ, successorIsInfinite⟩

theorem selected_successor_eq :
    NaturalTheoryProfile.successor sourceOptions = Natural.succ := by
  unfold NaturalTheoryProfile.successor sourceOptions
  exact choosePreferred_of_holds id Natural.succ successorIsInfinite

theorem selected_zero_eq : NaturalTheoryProfile.zero sourceOptions = Natural.zero := by
  have omitted : NaturalTheoryProfile.Omitted
      (NaturalTheoryProfile.successor sourceOptions) Natural.zero := by
    intro number same
    rw [selected_successor_eq] at same
    exact Natural.succ_ne_zero number same
  unfold NaturalTheoryProfile.zero sourceOptions
  exact choosePreferred_of_holds Natural.zero Natural.zero omitted

theorem source_generated (number : Natural.Carrier) :
    NaturalTheoryProfile.Generated sourceOptions number := by
  unfold NaturalTheoryProfile.Generated
  rw [selected_zero_eq, selected_successor_eq]
  intro predicate initial closed
  exact IndexedInductiveNaturalHOL.induction predicate initial closed number

noncomputable def sourceSelection {A : Type u} (start : A) :
    NaturalTheoryProfile.ResultSelection A where
  choose := choosePreferred start start
  selects := choosePreferred_selects start start

/-- The profile's selected recursion function is exactly the maintained source
eliminator, despite being constructed through an independently chosen graph. -/
theorem source_recursor_agrees {A : Type u} (start : A) (step : Natural.Carrier → A → A)
    (number : Natural.Carrier) :
    NaturalTheoryProfile.recursor sourceOptions (sourceSelection start) start step number =
      IndexedInductiveNaturalHOL.recurse start step number := by
  unfold NaturalTheoryProfile.recursor
  rw [selected_zero_eq, selected_successor_eq]
  exact IndexedInductiveNaturalMegalodon.source_selector_agrees start step
    (choosePreferred start start) (choosePreferred_selects start start) number

/-- The selected optional profile supplies total source recursion with the
actual zero/successor equations and generated-carrier uniqueness. -/
theorem source_recursion {A : Type u} (start : A) (step : Natural.Carrier → A → A) :
    ∃ function : Natural.Carrier → A,
      function Natural.zero = start ∧
      (∀ number, function (Natural.succ number) = step number (function number)) ∧
      ∀ candidate : Natural.Carrier → A, candidate Natural.zero = start →
        (∀ number, candidate (Natural.succ number) = step number (candidate number)) →
        ∀ number, function number = candidate number := by
  refine ⟨IndexedInductiveNaturalHOL.recurse start step,
    IndexedInductiveNaturalHOL.recurse_zero start step,
    IndexedInductiveNaturalHOL.recurse_succ start step, ?_⟩
  intro candidate atZero atSuccessor number
  exact (IndexedInductiveNaturalMegalodon.source_recursion_graph start step number).agrees
    candidate atZero (fun n _ _ => atSuccessor n)

/-- The carrier option is substantive: replacing the preferred successor by a
constant function makes the infinity witness false. -/
theorem constant_successor_refused :
    ¬ NaturalTheoryProfile.InfiniteFunction (fun _ : Natural.Carrier => Natural.zero) := by
  rintro ⟨injective, _⟩
  have same := injective (a₁ := Natural.zero) (a₂ := Natural.succ Natural.zero) rfl
  exact Natural.succ_ne_zero Natural.zero same.symm

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodonProfile
