import Mettapedia.Languages.MM0.Translation.FirstOrderPropositionalMeaning
import Mettapedia.Logic.HOL.PropositionalSlice

/-!
# What MM0 acceptance means in HOL

The intuitionistic and classical propositional theories generated for MM0
accept a proof of a formula exactly when HOL proves the formula, read as a
closed HOL formula whose atoms are propositional constants:

* intuitionistic: exactly when HOL proves it without excluded middle, and
  exactly when it holds at every world of every Kripke-Henkin general model
  of HOL (`accepted_iff_hol`, `accepted_iff_kripkeHenkin`);
* classical: exactly when HOL proves it from the excluded-middle schema, and
  exactly when every extensional Henkin model of HOL satisfies it
  (`accepted_iff_hol_em`, `accepted_iff_henkin`).

Each statement composes the exactness of MM0 for the generated theory, the
agreement of the presentation with the Hilbert system, and the propositional
slice of HOL.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning

open Mettapedia.GSLT.LanguageDef.PropositionalHilbert
open FirstOrderPropositionalMeaning
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.PropositionalSlice
open Kernel
open LO LO.Propositional

/-- The MM0 checker accepts some proof of the term of the formula, in the
context of `count` formula variables. -/
abbrev Accepted (classical : Bool) (count : ℕ) (φ : LO.Propositional.Formula ℕ) : Prop :=
  ∃ witness, ProofWitness.check (presentation classical).theory.termSignature
    (presentation classical).theory.definitionSignature
    (presentation classical).theory.theoremSignature
    (targetContext count) [] witness (encodeTerm φ) = true

/-! ## Without excluded middle -/

theorem accepted_iff_int {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) : Accepted false count φ ↔ Propositional.Int ⊢ φ :=
  (mm0_checks_iff_hilbert below).trans Logic.iff_provable.symm

/-- **MM0 accepts in the intuitionistic theory exactly what HOL proves
without excluded middle.** -/
theorem accepted_iff_hol {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) :
    Accepted false count φ ↔ ClosedTheorySet.Provable (∅ : ClosedTheorySet Atom) (embed φ) :=
  (accepted_iff_int below).trans provable_iff_int.symm

/-- **MM0 accepts in the intuitionistic theory exactly what holds at every
world of every Kripke-Henkin general model of HOL.** -/
theorem accepted_iff_kripkeHenkin {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) :
    Accepted false count φ ↔
      ∀ (N : KripkeHenkinGeneral.{0, 0, 0} AtomBase Atom) (W : N.World),
        N.denote (embed φ) N.emptyVal W :=
  (accepted_iff_hol below).trans provable_iff_kripkeHenkin

/-! ## With excluded middle -/

theorem accepted_iff_cl {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) : Accepted true count φ ↔ Propositional.Cl ⊢ φ :=
  (mm0_checks_iff_hilbert below).trans Logic.iff_provable.symm

/-- **MM0 accepts in the classical theory exactly what HOL proves from the
excluded-middle schema.** -/
theorem accepted_iff_hol_em {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) :
    Accepted true count φ ↔ ClosedTheorySet.Provable (EMSchema Atom) (embedP φ) :=
  (accepted_iff_cl below).trans provable_em_iff_cl.symm

/-- **MM0 accepts in the classical theory exactly what every extensional
Henkin model of HOL satisfies.** -/
theorem accepted_iff_henkin {count : ℕ} {φ : LO.Propositional.Formula ℕ}
    (below : AtomsBelow count φ) :
    Accepted true count φ ↔
      ∀ (N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom)),
        N.FunctionsRespectEqv → N.models (embedP φ) :=
  (accepted_iff_hol_em below).trans provable_em_iff_henkin

/-! ## Controls -/

theorem peirce_below : AtomsBelow 2 peirce :=
  ⟨⟨⟨show 0 < 2 by decide, show 1 < 2 by decide⟩, show 0 < 2 by decide⟩, show 0 < 2 by decide⟩

/-- Peirce's law has an accepted MM0 proof in the classical theory and none
in the intuitionistic theory. -/
theorem peirce_accepted :
    Accepted true 2 peirce ∧ ¬ Accepted false 2 peirce :=
  ⟨(accepted_iff_hol_em peirce_below).mpr peirce_separates.1,
    fun accepted => peirce_separates.2 ((accepted_iff_hol peirce_below).mp accepted)⟩

/-- A Kripke-Henkin general model of HOL refutes Peirce's law. -/
example : ¬ ∀ (N : KripkeHenkinGeneral.{0, 0, 0} AtomBase Atom) (W : N.World),
    N.denote (embed peirce) N.emptyVal W :=
  fun valid => peirce_accepted.2 ((accepted_iff_kripkeHenkin peirce_below).mpr valid)

end Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning
