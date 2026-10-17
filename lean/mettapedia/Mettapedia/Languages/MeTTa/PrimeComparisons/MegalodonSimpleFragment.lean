import Mettapedia.Languages.Megalodon.SimpleTypeFragment
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding

/-!
# One simple fragment checked in two independently specified kernels

The same intrinsic source term has a Mathdata typing and a typing in every
dependent package satisfying the stated formation interface. The two target
terms are actual translations, not a cast between theorem capsules or an
identification of logical foundations. The dependent package may have
additional equality, universe or declaration rules.

This joins the two typing comparisons only. Substitution and beta preservation
on the dependent side are supplied by `TypedEqualityEmbedding`; a corresponding
general Mathdata substitution comparison is not asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonSimpleFragment

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.Languages.Megalodon

/-- Actual source terms, rather than an untyped encoding of their spelling,
are accepted in both target typing judgments. -/
theorem common_typing {R : Presentation.Rules Tower.Head}
    (heads : TypedEqualityEmbedding.HeadRules R)
    (base depth : Nat) (environment : MathdataKernel.Environment)
    {context : List Ty} {selected : Ty} (source : Term context selected) :
    MathdataKernel.inferTerm environment depth
        (context.map (SimpleTypeFragment.type base)) (SimpleTypeFragment.term base source) =
      some (SimpleTypeFragment.type base selected) ∧
    Presentation.TypedEquality.Typed R (TowerDTT.eraseContext context)
      (TowerDTT.eraseTerm source) (TowerDTT.eraseTypeAt context.length selected) :=
  ⟨SimpleTypeFragment.term_infers base depth environment source,
    TypedEqualityEmbedding.term_typed heads source⟩

theorem cumulative_tower_common_typing (base depth : Nat)
    (environment : MathdataKernel.Environment)
    {context : List Ty} {selected : Ty} (source : Term context selected) :
    MathdataKernel.inferTerm environment depth
        (context.map (SimpleTypeFragment.type base)) (SimpleTypeFragment.term base source) =
      some (SimpleTypeFragment.type base selected) ∧
    Presentation.TypedEquality.Typed Tower.rules (TowerDTT.eraseContext context)
      (TowerDTT.eraseTerm source) (TowerDTT.eraseTypeAt context.length selected) :=
  common_typing TypedEqualityEmbedding.towerHeads base depth environment source

#print axioms common_typing
#print axioms cumulative_tower_common_typing

end Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonSimpleFragment
