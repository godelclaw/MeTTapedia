import Mathlib

/-!
The small trusted boundary used to reflect a strict polynomial certificate:
a unit combination of selected parent generators extends by zero to the full
family, and therefore rules out a common zero of that family.
-/

namespace Krenn.CertificateReflection

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Extend coefficients on a selected finite subfamily by zero. -/
def padCoefficients [DecidableEq ι] (selected : Finset ι) (c : ι → R) : ι → R :=
  fun i => if i ∈ selected then c i else 0

/-- A unit combination of selected generators is also a unit combination of
the complete parent family. -/
theorem pad_unitCombination [DecidableEq ι] (selected : Finset ι) (c f : ι → R)
    (hunit : ∑ i ∈ selected, c i * f i = 1) :
    ∑ i, padCoefficients selected c i * f i = 1 := by
  simpa [padCoefficients] using hunit

/-- A strict unit combination contradicts a simultaneous zero of all parent
generators. -/
theorem noCommonZero_of_unitCombination [Nontrivial R] (c f : ι → R)
    (hunit : ∑ i, c i * f i = 1) : ¬ ∀ i, f i = 0 := by
  intro hzero
  have hzeroOne : (0 : R) = 1 := by
    rw [← hunit]
    simp [hzero]
  exact zero_ne_one hzeroOne

/-- Certificate-reflection interface: a strict certificate over any selected
subfamily rules out a common zero of the complete parent family. -/
theorem noCommonZero_of_subfamilyUnitCombination [Nontrivial R]
    [DecidableEq ι] (selected : Finset ι) (c f : ι → R)
    (hunit : ∑ i ∈ selected, c i * f i = 1) : ¬ ∀ i, f i = 0 := by
  exact noCommonZero_of_unitCombination (padCoefficients selected c) f
    (pad_unitCombination selected c f hunit)

end Krenn.CertificateReflection
