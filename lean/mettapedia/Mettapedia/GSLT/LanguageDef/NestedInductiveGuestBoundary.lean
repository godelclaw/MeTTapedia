import Mettapedia.TypeTheory.IndexedContainerInduction
import Mettapedia.TypeTheory.IndexedPolynomialEquivalence
import Mettapedia.TypeTheory.PositiveInductiveScenarios
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuest

/-!
# Why the direct guest compiler cannot encode a nested recursive field

The current indexed guest compiler assigns one recursive child and one
induction hypothesis to every direct recursive field.  A registered nested
field has one child at every position of its container shape.  The distinction
is witnessed below by a two-element list: the real nested branch has two
recursive positions, while a one-field direct surrogate has one.

`IndexedContainer.InductionBundle` is the missing interface at this boundary.
Its list instance packages a dependent hypothesis for every list position.
An object-language guest adapter must next realize that bundle with formed
syntax and substitution laws before it may publish nested recursor or iota
receipts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NestedInductiveGuestBoundary

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.PositiveInductiveBlock
open Mettapedia.TypeTheory.PositiveInductiveScenarios

namespace Search

abbrev nestedCode := PositiveInductiveScenarios.Search.branchCode

def nestedShape : Code.Shape nestedCode
    PositiveInductiveScenarios.Search.environment
    PositiveInductiveScenarios.Search.rootIndex := by
  change Σ _shape : Nat, ULift (PLift (() = ()))
  exact ⟨2, ⟨⟨rfl⟩⟩⟩

abbrev NestedPosition := Code.Position nestedCode nestedShape

/-- What the existing direct guest compiler could express if it treated the
whole list field as one direct recursive child. -/
def directSurrogate : Description.Code PositiveInductiveScenarios.Search.interface [] :=
  .recursive () (.result ())

def directShape : Description.Shape directSurrogate PUnit.unit () :=
  ⟨⟨rfl⟩⟩

abbrev DirectPosition := Description.Position directSurrogate directShape

def nestedPositionEquiv : NestedPosition ≃ Sum (Fin 2) PEmpty := by
  change Sum (Mettapedia.TypeTheory.IndexedContainer.Examples.list.Position
    (nestedShape.1)) PEmpty ≃ Sum (Fin 2) PEmpty
  change Sum (Fin 2) PEmpty ≃ Sum (Fin 2) PEmpty
  exact Equiv.refl _

def directPositionEquiv (shape : Description.Shape directSurrogate PUnit.unit ()) :
    Description.Position directSurrogate shape ≃ Option PEmpty := by
  change Option PEmpty ≃ Option PEmpty
  exact Equiv.refl _

theorem nested_position_card : Fintype.card (Sum (Fin 2) PEmpty) = 2 := by
  simp

theorem direct_position_card : Fintype.card (Option PEmpty) = 1 := by
  simp

/-- Two list children cannot be represented by the direct compiler's single
recursive slot. -/
theorem nested_positions_not_direct :
    ¬ Nonempty (NestedPosition ≃ DirectPosition) := by
  rintro ⟨equivalent⟩
  let concrete : Sum (Fin 2) PEmpty ≃ Option PEmpty :=
    nestedPositionEquiv.symm.trans (equivalent.trans (directPositionEquiv directShape))
  have cards := Fintype.card_congr concrete
  rw [nested_position_card, direct_position_card] at cards
  omega

/-- Consequently the true nested constructor polynomial is not signature-
equivalent to the one-recursive-field surrogate. -/
theorem nested_polynomial_not_direct_surrogate :
    ¬ Nonempty (SignatureEquiv
      (Code.polynomial nestedCode)
      (Description.polynomial directSurrogate)) := by
  rintro ⟨equivalent⟩
  let concrete : Sum (Fin 2) PEmpty ≃ Option PEmpty :=
    nestedPositionEquiv.symm.trans
      ((equivalent.position nestedShape).trans
        (directPositionEquiv (equivalent.shape _ _ nestedShape)))
  have cards := Fintype.card_congr concrete
  rw [nested_position_card, direct_position_card] at cards
  omega

/-- The existing direct field counter sees only the surrogate's one recursive
field; it cannot manufacture the second list position. -/
theorem direct_surrogate_fieldCount :
    IndexedInductive.Guest.fieldCount directSurrogate = 1 := by
  rfl

/-- Positive replacement contract: the registered list bundle is equivalent
to one dependent induction hypothesis for every actual list position. -/
noncomputable def listPositionBundle (motive : Bool → Type) (values : List Bool) :
    (IndexedContainer.listInductionBundle motive).Bundle
        (IndexedContainer.Examples.listExtensionEquiv Bool values) ≃
      (∀ position : IndexedContainer.Examples.list.Position
          (IndexedContainer.Examples.listExtensionEquiv Bool values).1,
        motive ((IndexedContainer.Examples.listExtensionEquiv Bool values).2 position)) :=
  (IndexedContainer.listInductionBundle motive).exact _

#print axioms nested_position_card
#print axioms direct_position_card
#print axioms nested_positions_not_direct
#print axioms nested_polynomial_not_direct_surrogate
#print axioms direct_surrogate_fieldCount
#print axioms listPositionBundle

end Search

end Mettapedia.GSLT.LanguageDef.NestedInductiveGuestBoundary
