import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionCore
/-!
# P vs NP crux: product/fielded bridge equivalences

Equivalence theorems identifying product-bound-only and fielded-switching-only bridges with the finite-image obligations they must actually provide.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- For one fixed exact-visible family, a product-bound-to-compression bridge
has exactly the same mathematical content as a product-bound-to-finite-image
bridge. -/
theorem productBoundSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  constructor
  · intro h hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (h hprod)
  · intro h hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hprod)

/-- Once the product bound is actually true, deriving exact-visible compression
from that product bound is equivalent to giving the finite predictor-image
cover itself. -/
theorem productBound_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  constructor
  · intro h
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hprod)
  · intro hcover _hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        hcover

/-- The global product-bound-only bridge is exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (hbridge (Index := Index) G hprod)
  · intro hbridge Index G hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (hbridge (Index := Index) G hprod)

/-- For one fixed exact-visible family, a fielded-certificate-to-compression
bridge has exactly the same mathematical content as a
fielded-certificate-to-finite-image bridge. -/
theorem fieldedSwitchingSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  constructor
  · intro h hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (h hfield)
  · intro h hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hfield)

/-- Once the fielded switching certificate is actually true, deriving
exact-visible compression from that certificate is equivalent to giving the
finite predictor-image cover itself. -/
theorem fieldedSwitching_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  constructor
  · intro h
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hfield)
  · intro hcover _hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        hcover

/-- The global fielded-switching-only bridge is exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (hbridge (Index := Index) G hfield)
  · intro hbridge Index G hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (hbridge (Index := Index) G hfield)

/-- A product-bound-only bridge to the full clocked finite-learning payload has
exactly the same semantic content as finite predictor-image covers for every
exact-visible family.  Rephrasing the target as a bundled learning payload does
not remove the missing finite-image theorem. -/
theorem productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hprod
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mp
        (hbridge (Index := Index) G hprod)
  · intro hbridge Index G hprod
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mpr
        (hbridge (Index := Index) G hprod)

/-- A fielded-switching-only bridge to the full clocked finite-learning payload
has exactly the same semantic content as finite predictor-image covers for
every exact-visible family. -/
theorem fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mp
        (hbridge (Index := Index) G hfield)
  · intro hbridge Index G hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mpr
        (hbridge (Index := Index) G hfield)

/-- Any product-bound-only clocked-payload bridge immediately gives the older
exact-visible compression bridge. -/
theorem productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro Index G hprod
  exact
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) (hbridge (Index := Index) G hprod)

/-- Any fielded-switching-only clocked-payload bridge immediately gives the
older exact-visible compression bridge. -/
theorem fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro Index G hfield
  exact
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) (hbridge (Index := Index) G hfield)

end Mettapedia.Computability.PNP
