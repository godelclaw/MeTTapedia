import Mettapedia.Computability.PNP.CanonicalZABERMInterface
import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces

/-!
# PNP `Kpoly` coverage: canonical ZAB ERM route

This module isolates the optional manuscript-facing canonical exact
`(zfeat(z), a, b)` ERM recovery route from the broad `Kpoly` compression-bridge
coverage surface.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: the final manuscript-facing canonical exact
`(zfeat(z), a, b)` ERM recovery interface already lands on the exact-visible /
finite-image surface tracked by the stop-grade `Kpoly` packet.  Any such route
supplies the concrete visible-budget compression target, all three equivalent
finite-image presentations, the bundled clocked finite-learning payload at the
same budget, and the usual strict-budget non-surjectivity consequence. -/
def CanonicalZABERMRouteCoverage : Prop :=
  ∀ {Z : Type*} [Fintype Z] {r k clock : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index} {q : ℝ≥0∞},
      CanonicalZABERMRecoveryData
          (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q →
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) ∧
        G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) ∧
        G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) ∧
        G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) ∧
        ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock ∧
        (r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ Function.Surjective G.predict)

@[simp] theorem canonicalZABERMRouteCoverage :
    CanonicalZABERMRouteCoverage := by
  intro Z _ r k clock Index μ zfeat G q h
  refine ⟨h.compressionTarget, h.finitePredictorCover, h.finiteIndexRepresentativeCover,
    h.finitePredictorQuotient, ?_, ?_⟩
  · exact
      clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
        (Z := Z) (k := k) (s := r + 2 * k + 1) (clock := clock) (Index := Index)
        h.compressionTarget
  · intro hs
    exact h.not_surjective_predict_of_lt_surfaceCard hs

end Mettapedia.Computability.PNP
