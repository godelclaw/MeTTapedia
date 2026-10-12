import Mettapedia.GSLT.LanguageDef.PropositionalHilbertPresentations
import Foundation.Propositional.Kripke.Logic.Cl
import Foundation.Propositional.ClassicalSemantics.Hilbert

/-!
# What the propositional presentations mean

The propositional rule presentations derive exactly the theorems of the
standard Hilbert systems. The `Foundation` library proves those systems
sound and complete: the intuitionistic one for Kripke frames, the classical
one for truth tables. So derivability in each presentation is validity in
the corresponding semantics.

The two presentations differ by one rule, and the difference is real:
some formula is derivable with excluded middle and not without it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PropositionalHilbert

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open LO LO.Propositional

theorem AtomsBelow.mono {small large : ℕ} (inside : small ≤ large) :
    ∀ {φ : Formula ℕ}, AtomsBelow small φ → AtomsBelow large φ
  | .atom _, below => Nat.lt_of_lt_of_le below inside
  | .falsum, _ => trivial
  | .and _ _, below => ⟨AtomsBelow.mono inside below.1, AtomsBelow.mono inside below.2⟩
  | .or _ _, below => ⟨AtomsBelow.mono inside below.1, AtomsBelow.mono inside below.2⟩
  | .imp _ _, below => ⟨AtomsBelow.mono inside below.1, AtomsBelow.mono inside below.2⟩

/-- Every formula mentions finitely many atoms. -/
theorem exists_atomsBelow : ∀ φ : Formula ℕ, ∃ count, AtomsBelow count φ
  | .atom a => ⟨a + 1, Nat.lt_succ_self a⟩
  | .falsum => ⟨0, trivial⟩
  | .and φ ψ => by
      obtain ⟨left, leftBelow⟩ := exists_atomsBelow φ
      obtain ⟨right, rightBelow⟩ := exists_atomsBelow ψ
      exact ⟨max left right, leftBelow.mono (le_max_left _ _), rightBelow.mono (le_max_right _ _)⟩
  | .or φ ψ => by
      obtain ⟨left, leftBelow⟩ := exists_atomsBelow φ
      obtain ⟨right, rightBelow⟩ := exists_atomsBelow ψ
      exact ⟨max left right, leftBelow.mono (le_max_left _ _), rightBelow.mono (le_max_right _ _)⟩
  | .imp φ ψ => by
      obtain ⟨left, leftBelow⟩ := exists_atomsBelow φ
      obtain ⟨right, rightBelow⟩ := exists_atomsBelow ψ
      exact ⟨max left right, leftBelow.mono (le_max_left _ _), rightBelow.mono (le_max_right _ _)⟩

/-- **The intuitionistic rules derive exactly the formulas valid on every
Kripke frame.** -/
theorem derives_iff_kripke {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    Derives language (rules false) (context count) [] (encode φ) ↔
      Kripke.FrameClass.Int ⊧ φ :=
  (derives_iff_int below).trans
    ⟨fun provable => Sound.sound provable, fun valid => Complete.complete valid⟩

/-- **With excluded middle the rules derive exactly the tautologies.** -/
theorem derives_iff_tautology {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    Derives language (rules true) (context count) [] (encode φ) ↔ φ.Tautology :=
  (derives_iff_cl below).trans ⟨Cl.soundness, Cl.completeness⟩

/-- Everything derivable without excluded middle is derivable with it. -/
theorem classical_of_intuitionistic {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ)
    (derived : Derives language (rules false) (context count) [] (encode φ)) :
    Derives language (rules true) (context count) [] (encode φ) :=
  (derives_iff_cl below).mpr
    ((Entailment.strictlyWeakerThan_iff.mp
      (inferInstance : Propositional.Int ⪱ Propositional.Cl)).1 ((derives_iff_int below).mp derived))

/-- **Excluded middle is not derivable from the other rules.** Some formula
is derivable with it and not without it. -/
theorem excludedMiddle_adds :
    ∃ (count : ℕ) (φ : Formula ℕ), AtomsBelow count φ ∧
      Derives language (rules true) (context count) [] (encode φ) ∧
      ¬ Derives language (rules false) (context count) [] (encode φ) := by
  obtain ⟨-, φ, unprovable, provable⟩ := Entailment.strictlyWeakerThan_iff.mp
    (inferInstance : Propositional.Int ⪱ Propositional.Cl)
  obtain ⟨count, below⟩ := exists_atomsBelow φ
  exact ⟨count, φ, below, (derives_iff_cl below).mpr provable,
    fun derived => unprovable ((derives_iff_int below).mp derived)⟩

end Mettapedia.GSLT.LanguageDef.PropositionalHilbert
