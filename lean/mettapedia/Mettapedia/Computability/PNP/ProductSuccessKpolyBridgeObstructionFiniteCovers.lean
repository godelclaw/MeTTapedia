import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionEquivalences
/-!
# P vs NP crux: finite-cover consequences

Consequences extracting finite predictor-image covers, representative-index covers, and quotient-code presentations from true product-bound-only or fielded-switching-only exact-visible bridges.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- Any true product-bound-only bridge supplies a finite predictor-image cover
for the chosen exact-visible family. -/
theorem finitePredictorCover_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true product-bound-only bridge supplies an actual finite representative
index cover for the chosen exact-visible family. -/
theorem finiteIndexRepresentativeCover_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true product-bound-only bridge supplies a finite quotient-code
presentation for the chosen exact-visible family. -/
theorem finitePredictorQuotient_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorQuotient (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorQuotient
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true fielded-switching-only bridge supplies a finite predictor-image
cover for the chosen exact-visible family. -/
theorem finitePredictorCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

/-- Any true fielded-switching-only bridge supplies an actual finite
representative index cover for the chosen exact-visible family. -/
theorem finiteIndexRepresentativeCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

/-- Any true fielded-switching-only bridge supplies a finite quotient-code
presentation for the chosen exact-visible family. -/
theorem finitePredictorQuotient_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorQuotient (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorQuotient
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

end Mettapedia.Computability.PNP
