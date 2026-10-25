import Mettapedia.TypeTheory.HypercubeSortRenaming
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# The sort spine decides elaborability at fixed formation and conversion

A kernel of the lambda cube is fixed by its sorts and sort axioms, by the
product rules it may form, and by the conversion its typing uses.
`HypercubeBubbles` shows that the product rules (the vertex) and the conversion
(the bubble) are independent choices. This module shows that the sort axioms
are a third choice that neither of them determines, and that it decides
whether the kernel's derivations can be translated into any explicit checker
that is sound for a meaning refuting the paradox judgment.

* **Same products, same conversion, different spine** (`spine_separates`).
  The universal-sort profile of `TypeInTypeParadox` has exactly the product
  rules of the simply typed vertex, and both kernels use beta conversion. With
  the standard axiom `∗ : □` no closed term has type `Π p : ∗. p`; with `∗ : ∗`
  Hurkens' term has it.
* **The standard spine meets the hypotheses** (`standard_spine_meaning`). Every
  derivation of the simply typed vertex with beta is a derivation of the
  calculus of constructions, and that calculus does not derive the paradox
  judgment.
* **No sound translation of the universal sort**
  (`no_sound_translation_of_universalSort`). A translation of the universal
  sort's derivations, under any bubble containing beta, into a checker that is
  sound for a meaning refuting the translated paradox judgment does not exist.
* **No sound translation of a commuting merge**
  (`no_sound_translation_of_commutingMerge`). The same holds for every
  functional target that receives the calculus of constructions and the
  kind-result prototype along sort maps agreeing on their shared sorts
  (`HypercubeSortRenaming.commuting_functional_cocone_inconsistent`).

These are consequences of the existing consistency and paradox theorems. Their
content is the placement: a parameter space for kernels that elaborate into
sound explicit checkers carries the sort spine as its own coordinate, and the
region of that space where such elaboration exists has no common upper vertex
for these two profiles.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SortSpineElaborationBoundary

open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef.LF (Srt)
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.TypeTheory.HypercubeBubbles

universe uClaim uCertificate uSort

/-- The universal-sort profile and the simply typed vertex have the same
product rules. -/
theorem universalSort_products :
    TypeInTypeParadox.typeInType.products = simplyTypedProducts := rfl

/-- They differ only in the axiom of the sort of types. -/
theorem universalSort_axiom :
    TypeInTypeParadox.typeInType.sortAxiom .type = some .type ∧
      (vertex simplyTypedProducts).sortAxiom .type = some .kind :=
  ⟨rfl, rfl⟩

/-- **The spine separates kernels with the same products and conversion.**
With the universal sort the paradox judgment is derivable under beta; at the
simply typed vertex with the standard axiom no closed term has the paradox
type. -/
theorem spine_separates :
    TypeInTypeParadox.typeInType.products = simplyTypedProducts ∧
      TypedUnder TypeInTypeParadox.typeInType (bubbleConv betaRoot) []
        (.term TypeInTypeParadox.paradoxTerm TypeInTypeParadox.falsumTerm .type) ∧
      ∀ (term : PTerm) (sort : Srt),
        ¬ Kernel simplyTypedProducts betaRoot [] (.term term TypeInTypeParadox.falsumTerm sort) :=
  ⟨universalSort_products, universalTop_inconsistent (fun step => step),
    fun term sort => vertex_consistent (fun rule member => by
      simp only [simplyTypedProducts, List.mem_singleton] at member
      subst member
      simp [constructionProducts, constructions]) (fun step => step) term sort⟩

/-- **Positive control.** The meaning "derivable in the calculus of
constructions" contains every derivation of the simply typed vertex with beta
and refutes the paradox judgment, so the hypotheses of the impossibility below
can be met at the standard spine. -/
theorem standard_spine_meaning :
    (∀ {context : SortedCtx} {judgment : Judgment},
      Kernel simplyTypedProducts betaRoot context judgment → Derives constructions context judgment) ∧
    ¬ Derives constructions []
      (.term TypeInTypeParadox.paradoxTerm TypeInTypeParadox.falsumTerm .type) := by
  refine ⟨fun derivation => ?_, paradox_not_constructions .type⟩
  have widened : Kernel constructionProducts betaRoot _ _ :=
    Kernel.mono (fun rule member => by
      simp only [simplyTypedProducts, List.mem_singleton] at member
      subst member
      simp [constructionProducts, constructions]) (fun step => step) derivation
  exact (derives_iff_kernel_beta constructionProducts).mpr widened

/-- **No sound translation of the universal sort.** Under any bubble that
contains beta, no translation sends every derivation of the universal-sort
kernel to an accepted certificate of a checker that is sound for a meaning
refuting the translated paradox judgment. -/
theorem no_sound_translation_of_universalSort {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) {Meaning : Claim → Prop} (sound : checker.Sound Meaning)
    {steps : PTerm → PTerm → Prop}
    (includesBeta : ∀ {source target : PTerm}, betaRoot source target → steps source target)
    (translate : SortedCtx → Judgment → Claim)
    (translates : ∀ {context : SortedCtx} {judgment : Judgment},
      TypedUnder TypeInTypeParadox.typeInType (bubbleConv steps) context judgment →
        ∃ certificate, checker.check (translate context judgment) certificate = true)
    (refutes : ¬ Meaning (translate []
      (.term TypeInTypeParadox.paradoxTerm TypeInTypeParadox.falsumTerm .type))) :
    False := by
  obtain ⟨certificate, accepted⟩ := translates (universalTop_inconsistent includesBeta)
  exact refutes (sound _ certificate accepted)

/-- **No sound translation of a commuting merge.** A functional target that
receives the calculus of constructions and the kind-result prototype along
sort maps agreeing on their shared sorts derives the collapsed paradox, so its
derivations have no translation into a checker sound for a meaning that
refutes the translated paradox judgment. -/
theorem no_sound_translation_of_commutingMerge
    {TargetSort : Type uSort} {target : GenericPureTypeSystem.Profile TargetSort}
    (fromCoc : GenericPureTypeSystem.Morphism
      (GenericPureTypeSystem.TwoSort.ofLFProfile constructions) target)
    (fromPrototype : GenericPureTypeSystem.Morphism
      (GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype) target)
    (agreesType : fromCoc.onSort .type = fromPrototype.onSort .type)
    (agreesKind : fromCoc.onSort .kind = fromPrototype.onSort .kind)
    (functional : GenericPureTypeSystem.Functional target)
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) {Meaning : Claim → Prop} (sound : checker.Sound Meaning)
    (translate : GenericPureTypeSystem.SortedCtx TargetSort →
      GenericPureTypeSystem.Judgment TargetSort → Claim)
    (translates : ∀ {context : GenericPureTypeSystem.SortedCtx TargetSort}
      {judgment : GenericPureTypeSystem.Judgment TargetSort},
      GenericPureTypeSystem.Derives target context judgment →
        ∃ certificate, checker.check (translate context judgment) certificate = true)
    (refutes : ¬ Meaning (translate []
      (.term (HypercubeSortRenaming.collapsedParadox (fromCoc.onSort .type))
        (HypercubeSortRenaming.collapsedFalsum (fromCoc.onSort .type)) (fromCoc.onSort .type)))) :
    False := by
  obtain ⟨certificate, accepted⟩ := translates
    (HypercubeSortRenaming.commuting_functional_cocone_inconsistent fromCoc fromPrototype
      agreesType agreesKind functional)
  exact refutes (sound _ certificate accepted)

#print axioms spine_separates
#print axioms standard_spine_meaning
#print axioms no_sound_translation_of_universalSort
#print axioms no_sound_translation_of_commutingMerge

end Mettapedia.TypeTheory.SortSpineElaborationBoundary
