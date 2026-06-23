import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.PNPv13RouteSynthesis

/-!
# P vs NP crux: product success alone does not give Kpoly compression

The v13 switching layer proves finite product-success bounds from fielded
half-success certificates.  Those facts live over finite event histories.  The
exact-visible `Kpoly` compression target, however, is a statement about the
image of a predictor family on the post-switch surface `u = (z, a, b)`.

This file formalizes the missing bridge as a counterexample: a bridge that uses
only the product bound, or only a fielded switching certificate, would have to
compress every exact-visible switched family.  The full Boolean family on the
exact visible surface refutes that below the surface-cardinality threshold.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- The fielded v13 finite tower product bound from an existing history. -/
def V13FieldedProductBoundFrom (Ω : Type u) [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  2 ^ items.length *
      finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
    finiteHistoryCount Ω hist

/-- The full Boolean-rule family on the exact manuscript-visible post-switch
surface.  Its index is the rule itself. -/
def fullExactVisibleRuleFamily (Z : Type v) (k : ℕ) :
    ExactVisibleSwitchedFamily Z k (ExactVisibleRule Z k) where
  predict rule := rule

/-- The full exact-visible family realizes every Boolean rule on the visible
post-switch surface. -/
theorem fullExactVisibleRuleFamily_surjective (Z : Type v) (k : ℕ) :
    Function.Surjective (fullExactVisibleRuleFamily Z k).predict := by
  intro rule
  exact ⟨rule, rfl⟩

/-- A product-bound-only `Kpoly` bridge would assert that the finite tower
product bound, without any semantic relation to the exact-visible predictor
family, forces an `s`-bit exact visible compression target for every family. -/
def ProductBoundOnlyExactVisibleCompressionBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldedProductBoundFrom Ω hist items →
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s

/-- The finite-image semantic content that a product-bound bridge must supply
for one fixed exact-visible predictor family. -/
def ProductBoundSemanticFiniteImageBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  V13FieldedProductBoundFrom Ω hist items → G.FinitePredictorCover (2 ^ s)

/-- A fielded-switching-only `Kpoly` bridge would assert that a fixed-field v13
certificate, without any semantic relation to the exact-visible predictor
family, forces an `s`-bit exact visible compression target for every family. -/
def FieldedSwitchingOnlyExactVisibleCompressionBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldSwitchingInstantiatedFrom hist items →
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s

/-- The finite-image semantic content that a fielded-switching bridge must
supply for one fixed exact-visible predictor family. -/
def FieldedSwitchingSemanticFiniteImageBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  V13FieldSwitchingInstantiatedFrom hist items →
    G.FinitePredictorCover (2 ^ s)

/-- A product-bound-only bridge to the full clocked finite-learning payload
would assert that the finite tower product bound, without any semantic relation
to the exact-visible predictor family, forces the full payload for every
family. -/
def ProductBoundOnlyClockedKpolyFiniteLearningBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) [Fintype Z] (k s clock : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldedProductBoundFrom Ω hist items →
    ClockedKpolyFiniteLearningPayload G s clock

/-- A fielded-switching-only bridge to the full clocked finite-learning payload
would assert that the fixed-field certificate, without any semantic relation to
the exact-visible predictor family, forces the full payload for every family. -/
def FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) [Fintype Z] (k s clock : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldSwitchingInstantiatedFrom hist items →
    ClockedKpolyFiniteLearningPayload G s clock

end Mettapedia.Computability.PNP
