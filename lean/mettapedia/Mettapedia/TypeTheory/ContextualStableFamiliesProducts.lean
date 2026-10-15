import Mettapedia.TypeTheory.ContextualProductSections

/-!
# Complete stable products in the original families model

The original dependent function operations satisfy beta, eta and the actual
contextual substitution laws. This supplies the source capability needed
by the complete native family and generated-term comparisons, retaining
the original type and term carriers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualStableFamiliesProducts

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualProductSections

universe w

theorem eta : ContextualPiEta.PiEta Families.products.{w}
    Families.products_substitution.1 := by
  intro context domain codomain function
  funext environment argument
  rfl

def products : StableProducts (familiesCwf.{w}) where
  operations := Families.products
  beta := PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts
  substitution := Families.products_substitution
  eta := eta

end Mettapedia.TypeTheory.ContextualStableFamiliesProducts
