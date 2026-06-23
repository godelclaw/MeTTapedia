import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily

/-!
# Actual switched-local support transfer

Observed-output families, uniform visible sections, and the transfer from
observed-output covers to exact-visible predictor covers.
-/

namespace Mettapedia.Computability.PNP

universe v u w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type*} {Block : Type*}

/-- The family of actually observed output functions over blocks. -/
def outputFamily (T : ActualSwitchedLocalInterface Z k Index Block) :
    IndexedPredictorFamily Index Block where
  predict := T.output

@[simp] theorem outputFamily_predict
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    T.outputFamily.predict i phi = T.output i phi := rfl

/-- A uniform section from exact visible inputs back to actual blocks.  This is
the missing reachability hypothesis needed to transfer an observed-output
compression theorem to the full exact-visible local-rule family. -/
def HasUniformVisibleSection
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (sec : ExactVisiblePostSwitchSurface Z k → Block) : Prop :=
  ∀ i u, T.visibleInput i (sec u) = u

/-- With a uniform visible section, the exact-visible predictor family is the
pullback of the actually observed block-output family. -/
theorem predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec) :
    T.predictorFamily.FactorsThrough sec T.outputFamily := by
  intro i u
  calc
    T.predictorFamily.predict i u = T.localRule i u := rfl
    _ = T.localRule i (T.visibleInput i (sec u)) := by
      rw [hsec i u]
    _ = T.output i (sec u) := (T.output_eq_visibleInput i (sec u)).symm
    _ = T.outputFamily.predict i (sec u) := rfl

/-- Therefore any finite observed-output cover transfers to the exact-visible
predictor family once the uniform visible section is supplied. -/
theorem predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {N : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_of_factorsThrough
      (G := T.predictorFamily) (H := T.outputFamily) (view := sec)
      (T.predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection hsec)
      hcover

/-- The same transfer stated as an exact bit-budget theorem. -/
theorem predictorFamily_hasBitBudget_of_outputFamily_hasBitBudget
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {s : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    T.predictorFamily.HasBitBudget s := by
  exact
    IndexedPredictorFamily.hasBitBudget_of_factorsThrough
      (G := T.predictorFamily) (H := T.outputFamily) (view := sec)
      (T.predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection hsec)
      hbudget

/-- Consequently the current clocked `Kpoly` finite-learning payload follows
from an observed-output bit budget only under the uniform visible section
hypothesis. -/
theorem clockedKpolyFiniteLearningPayload_of_outputFamily_hasBitBudget
    [Fintype Z]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {s clock : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (G := T.predictorFamily) (s := s) (clock := clock)
      (T.predictorFamily_hasBitBudget_of_outputFamily_hasBitBudget hsec hbudget)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
