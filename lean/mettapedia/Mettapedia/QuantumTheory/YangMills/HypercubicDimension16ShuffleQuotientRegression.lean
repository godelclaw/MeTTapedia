import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ShuffleQuotient

/-!
# Regression checks for the global-to-local shuffle quotient
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ShuffleQuotientRegression

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16ShuffleQuotient

theorem oneOwner_degreeFourteen_semantic_card :
    Fintype.card (SemanticShuffleQuotient 1 14) = 268435456 := by
  rw [card_oneOwnerSemanticShuffleQuotient]
  norm_num

theorem localization_hypercubic_equivariant
    {fieldCount derivativeCount : ℕ} (h : Hypercubic4)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    localize (word.hypercubicAct h) =
      (localize word).hypercubicAct h :=
  localize_hypercubicAct h word

theorem every_existing_shuffle_row_is_sound
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    localize
        (orderedDerivativeWordEquivGlobal carrier.1.1
          (dimension16DerivativeCount carrier.1)
          carrier.2.derivativeWord) =
      localize
        (orderedDerivativeWordEquivGlobal carrier.1.1
          (dimension16DerivativeCount carrier.1)
          (swapDerivativePositions carrier.2 site.left site.right).derivativeWord) :=
  derivativeShuffleSite_localize_eq site

end HypercubicDimension16ShuffleQuotientRegression
end YangMills
end QuantumTheory
end Mettapedia
