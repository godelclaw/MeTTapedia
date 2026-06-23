import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleUniformSection

/-!
# PNP `Kpoly` support/full-rule anchors: exact decoders

Observed-rule factorization, injectivity, and exact-decoder-to-surjectivity anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: the reachable-support quotient is only the pullback
of the exact-visible family along `visibleOf`. -/
theorem kpolyCoverage_anchor_supportFullRule_outputFamily_factorsThrough_predictorFamily
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily :=
  supportFullRule_outputFamily_factorsThrough_predictorFamily visibleOf

/-- Route-coverage anchor: exact recovery from the observed quotient forces
the support map to hit every exact-visible input. -/
theorem kpolyCoverage_anchor_supportFullRule_observedRuleMap_injective_forces_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf :=
  supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective visibleOf hinj

/-- Route-coverage anchor: any exact decoder from observed block-output traces
to full exact-visible rules forces the support map to hit every exact-visible
input. -/
theorem kpolyCoverage_anchor_supportFullRule_exactDecoder_forces_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf :=
  supportFullRule_exactDecoder_forces_visibleOf_surjective
    visibleOf decode hdecode


end Mettapedia.Computability.PNP
