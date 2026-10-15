import Mettapedia.Logic.HOL.PropositionalSlice
import Mettapedia.Logic.InstitutionBorrowing

/-!
# Routes from propositional logic into HOL, with and without excluded middle

Four logics are read on the same propositional formulas: intuitionistic and
classical propositional logic (`intTheory`, `clTheory`), and the HOL calculus
of this library without and with the excluded-middle schema (`holTheory`,
`holEMTheory`), each through the propositional slice.  The identity on
formulas is a route between them wherever theorems are carried to theorems.

* **Conservative routes.**  Intuitionistic logic into HOL without excluded
  middle (`intToHol_conservative`) and classical logic into HOL with the schema
  (`clToHolEM_conservative`): borrowing the HOL prover decides exactly the
  source theorems.
* **A route that adds a commitment.**  HOL without excluded middle into HOL
  with it carries theorems to theorems and is not conservative: it certifies
  excluded middle and Peirce's law (`holToHolEM_adds_classical_laws`).
* **Borrowing along it reaches a false conclusion.**  Reading intuitionistic
  logic through classical HOL (`intToHolEM`) certifies excluded middle, which
  intuitionistic logic does not prove (`intToHolEM_borrows_excluded_middle`).
* **Route choice.**  Out of intuitionistic logic, the route into HOL without
  excluded middle has strictly fewer commitments than the route into HOL with
  it, and it is the least route (`route_choice`).

The commitment added here, classical reasoning, is the one a host adds when it
receives a constructive logic into a classical one.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.PropositionalSliceRoutes

open LO LO.Propositional
open Mettapedia.Logic.HOL.PropositionalSlice
open Mettapedia.Logic.HOL.ClosedTheorySet
open Mettapedia.Logic.InstitutionBorrowing

/-- Intuitionistic propositional theorems. -/
def intTheory : Set PropFormula := {formula | Propositional.Int ⊢ formula}

/-- Classical propositional theorems. -/
def clTheory : Set PropFormula := {formula | Propositional.Cl ⊢ formula}

/-- Formulas whose image HOL proves without excluded middle. -/
def holTheory : Set PropFormula := {formula | Provable (∅ : ClosedTheorySet Atom) (embed formula)}

/-- Formulas whose image HOL proves from the excluded-middle schema. -/
def holEMTheory : Set PropFormula := {formula | Provable (EMSchema Atom) (embedP formula)}

/-- Excluded middle for the first atom. -/
abbrev excludedMiddle : PropFormula := .atom 0 ⋎ ∼(.atom 0)

theorem int_le_cl {formula : PropFormula} (proved : Propositional.Int ⊢ formula) :
    Propositional.Cl ⊢ formula :=
  Entailment.WeakerThan.pbl proved

/-- Intuitionistic logic read in HOL without excluded middle. -/
def intToHol : TheoryRoute intTheory holTheory where
  translate formula := formula
  preserves _ proved := provable_iff_int.mpr proved

/-- Classical logic read in HOL with the excluded-middle schema. -/
def clToHolEM : TheoryRoute clTheory holEMTheory where
  translate formula := formula
  preserves _ proved := provable_em_iff_cl.mpr proved

/-- HOL without excluded middle read in HOL with it. -/
def holToHolEM : TheoryRoute holTheory holEMTheory where
  translate formula := formula
  preserves _ proved := provable_em_iff_cl.mpr (int_le_cl (provable_iff_int.mp proved))

/-- Intuitionistic logic read in HOL with the excluded-middle schema. -/
def intToHolEM : TheoryRoute intTheory holEMTheory := intToHol.comp holToHolEM

/-- **Conservative**: HOL without excluded middle proves the image of exactly
the intuitionistic theorems. -/
theorem intToHol_conservative : intToHol.Conservative :=
  fun _ certified => provable_iff_int.mp certified

/-- **Conservative**: HOL with the schema proves the image of exactly the
classical theorems. -/
theorem clToHolEM_conservative : clToHolEM.Conservative :=
  fun _ certified => provable_em_iff_cl.mp certified

/-- **The classical extension adds commitments**: excluded middle and Peirce's
law are certified by HOL with the schema and not proved without it. -/
theorem holToHolEM_adds_classical_laws :
    excludedMiddle ∈ holToHolEM.addedCommitments ∧ peirce ∈ holToHolEM.addedCommitments :=
  ⟨⟨excludedMiddle_provable_em, excludedMiddle_not_provable⟩,
    ⟨peirce_separates.1, peirce_separates.2⟩⟩

theorem holToHolEM_not_conservative : ¬ holToHolEM.Conservative := by
  rw [TheoryRoute.conservative_iff_addedCommitments_eq_empty]
  intro empty
  have member := holToHolEM_adds_classical_laws.1
  rw [empty] at member
  exact member

/-- **Borrowing classical HOL's prover for intuitionistic logic reaches a
false conclusion**: it certifies excluded middle, which intuitionistic logic
does not prove. -/
theorem intToHolEM_borrows_excluded_middle :
    excludedMiddle ∈ intToHolEM.borrowed ∧ excludedMiddle ∉ intTheory :=
  ⟨excludedMiddle_provable_em,
    fun proved => excludedMiddle_not_provable (provable_iff_int.mpr proved)⟩

theorem intToHolEM_not_conservative : ¬ intToHolEM.Conservative :=
  fun conservative => intToHolEM_borrows_excluded_middle.2
    (conservative intToHolEM_borrows_excluded_middle.1)

/-- The commitments of the classical route out of intuitionistic logic are
exactly the commitments its second leg adds. -/
theorem intToHolEM_addedCommitments :
    intToHolEM.addedCommitments = intToHol.translate ⁻¹' holToHolEM.addedCommitments \ intTheory := by
  rw [intToHolEM, TheoryRoute.addedCommitments_comp,
    (intToHol.conservative_iff_addedCommitments_eq_empty).mp intToHol_conservative,
    Set.empty_union]

/-- **Route choice out of intuitionistic logic**: the route into HOL without
excluded middle is conservative, hence least, and strictly below the route
into classical HOL. -/
theorem route_choice :
    intToHol.Conservative ∧ intToHol.FewerCommitments intToHolEM ∧
      ¬ intToHolEM.FewerCommitments intToHol :=
  ⟨intToHol_conservative, intToHol.fewerCommitments_comp holToHolEM,
    fun fewer => intToHolEM_not_conservative
      (Set.Subset.trans fewer intToHol_conservative)⟩

#print axioms intToHol_conservative
#print axioms clToHolEM_conservative
#print axioms holToHolEM_adds_classical_laws
#print axioms intToHolEM_borrows_excluded_middle
#print axioms intToHolEM_addedCommitments
#print axioms route_choice

end Mettapedia.Logic.HOL.PropositionalSliceRoutes
