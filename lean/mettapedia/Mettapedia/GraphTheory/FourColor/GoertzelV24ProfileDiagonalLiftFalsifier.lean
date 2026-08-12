import Mathlib.Data.Fin.Basic

/-!
# Color-projected seam support does not force a full-profile diagonal

The source splice needs a diagonal witness in the complete finite profile:
cut colors, connectivity, and capped face progress must return together.
Equality after projecting a transfer relation to boundary colors is weaker.

The two-state example below makes the distinction explicit.  Both full
profiles have the same boundary color word, and the removed piece supports
the off-diagonal transition `0 → 1`.  Its projected seam support is therefore
nonempty and agrees with the retained color support, but it has no diagonal
full-profile entry.  Thus a color-word seam audit cannot by itself discharge
the full-profile diagonal lift.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ProfileDiagonalLiftFalsifier

/-- The smallest profile carrier on which an off-diagonal transition exists. -/
abbrev TestProfile := Fin 2

/-- Both test profiles display the same boundary color word. -/
def testProfileWord (_profile : TestProfile) : Unit := ()

/-- The removed test piece supports exactly the transition `0 → 1`. -/
def testTransfer (left right : TestProfile) : Prop :=
  left = 0 ∧ right = 1

/-- The retained test context accepts its unique boundary word. -/
def testRetainedWordSupport (_word : Unit) : Prop := True

/-- Color-projected seam support forgets whether the two full profiles agree. -/
def testProjectedSeamSupport (word : Unit) : Prop :=
  ∃ left right : TestProfile,
    testProfileWord left = word ∧
      testProfileWord right = word ∧
        testTransfer left right

/-- Full-profile diagonal support retains equality of the profile state. -/
def testFullProfileDiagonalSupport (word : Unit) : Prop :=
  ∃ profile : TestProfile,
    testProfileWord profile = word ∧ testTransfer profile profile

/-- The retained and removed color-word supports agree in the test. -/
theorem testRetainedWordSupport_iff_projectedSeamSupport (word : Unit) :
    testRetainedWordSupport word ↔ testProjectedSeamSupport word := by
  cases word
  constructor
  · intro _
    exact ⟨0, 1, rfl, rfl, rfl, rfl⟩
  · intro _
    trivial

/-- Nevertheless the unique boundary word has no full-profile diagonal. -/
theorem not_testFullProfileDiagonalSupport :
    ¬ testFullProfileDiagonalSupport () := by
  rintro ⟨profile, _hword, hleft, hright⟩
  have : (0 : TestProfile) = 1 := hleft.symm.trans hright
  exact Fin.zero_ne_one this

/-- Hence equality of color-projected seam supports does not imply the
fiberwise full-profile diagonal property consumed by the splice lift. -/
theorem projectedSeamSupportAgreement_not_fullProfileDiagonalLift :
    (∀ word, testRetainedWordSupport word ↔ testProjectedSeamSupport word) ∧
      ¬ (∀ word, testRetainedWordSupport word →
        testFullProfileDiagonalSupport word) := by
  refine ⟨testRetainedWordSupport_iff_projectedSeamSupport, ?_⟩
  intro hlift
  exact not_testFullProfileDiagonalSupport (hlift () trivial)

end GoertzelV24ProfileDiagonalLiftFalsifier

end Mettapedia.GraphTheory.FourColor
