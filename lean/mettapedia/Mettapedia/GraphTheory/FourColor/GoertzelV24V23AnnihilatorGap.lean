import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# The annihilator step in v23 Theorem 4.9 is not an equivalence

The source's annular spanning proof derives `Uᗮ ∩ W = {0}` and concludes
`W ≤ U`.  That implication requires an additional relationship between `U`
and `W` (for example `U ≤ W` in the finite-dimensional situation at hand).
The following two-dimensional `ZMod 2` countermodel proves that the bare
implication is false.

This does not refute the source's desired spanning inclusion.  It refutes the
specific inference used to obtain it and therefore isolates the missing
membership/spanning argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24V23AnnihilatorGap

/-- The two-dimensional ambient vector space used by the countermodel. -/
abbrev Vec := Fin 2 → ZMod 2

/-- The standard bilinear form. -/
def dot (left right : Vec) : ZMod 2 :=
  left 0 * right 0 + left 1 * right 1

/-- The target line `W = span (1,0)`. -/
def InW (value : Vec) : Prop := value 1 = 0

/-- The transverse line `U = span (1,1)`. -/
def InU (value : Vec) : Prop := value 0 = value 1

def ones : Vec := fun _ => 1

def firstBasis : Vec := fun index => if index = 0 then 1 else 0

/-- The relative annihilator of `U` inside `W` is trivial. -/
theorem eq_zero_of_inW_of_orthogonal_to_U
    (value : Vec) (hW : InW value)
    (horthogonal : ∀ test, InU test → dot value test = 0) :
    value = 0 := by
  have hones : InU ones := by
    rfl
  have hdot := horthogonal ones hones
  have hsecond : value 1 = 0 := hW
  have hfirst : value 0 = 0 := by
    simpa [dot, ones, hsecond] using hdot
  funext index
  fin_cases index
  · exact hfirst
  · exact hW

theorem firstBasis_inW : InW firstBasis := by
  simp [InW, firstBasis]

theorem firstBasis_not_inU : ¬InU firstBasis := by
  simp [InU, firstBasis]

/-- **Checked countermodel to the v23 annihilator inference.**  Triviality of
`Uᗮ ∩ W` does not imply `W ≤ U`. -/
theorem trivial_relative_annihilator_but_not_contained :
    (∀ value, InW value →
      (∀ test, InU test → dot value test = 0) → value = 0) ∧
    ¬(∀ value, InW value → InU value) := by
  constructor
  · exact eq_zero_of_inW_of_orthogonal_to_U
  · intro hcontained
    exact firstBasis_not_inU (hcontained firstBasis firstBasis_inW)

end GoertzelV24V23AnnihilatorGap

end Mettapedia.GraphTheory.FourColor
