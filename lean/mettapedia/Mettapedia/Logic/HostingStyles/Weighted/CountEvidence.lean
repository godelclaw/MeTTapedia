import Mettapedia.GSLT.Causality.DoCalculus.QueryCounts

/-!
# Duplicating a match doubles an observation

With `Counts` as the weights, a translation that records every match twice
turns one call to `Counts.revise` into two positive observations.
`poolObservational` is that one call on the observational coordinate of a
`QueryState`. Revising after the translation is not the translation of the
revised state. Pooling the fibre back, by undoing the doubling, makes the two
orders agree.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.GSLT.Causality.DoCalculus

/-- Record every stored observation twice. -/
def scaleCounts (counts : Counts) : Counts where
  pos := counts.pos * 2
  neg := counts.neg * 2

/-- Pool a doubled fibre back to one observation per source event. -/
def unscaleCounts (counts : Counts) : Counts where
  pos := counts.pos / 2
  neg := counts.neg / 2

/-- The same doubling, on the observational coordinate of a query. -/
def scaleQuery (state : QueryState) : QueryState where
  observational := scaleCounts state.observational
  interventional := state.interventional

/-- The same pooling, on the observational coordinate of a query. -/
def unscaleQuery (state : QueryState) : QueryState where
  observational := unscaleCounts state.observational
  interventional := state.interventional

/-- **Positive.** Doubling a state and pooling it returns the state. -/
theorem unscale_scale (counts : Counts) : unscaleCounts (scaleCounts counts) = counts := by
  cases counts with
  | mk pos neg =>
    simp [unscaleCounts, scaleCounts]

/-- **Negative.** Doubling is not the identity on a single positive observation. -/
theorem scale_not_id : scaleCounts (Counts.revise ⟨0, 0⟩ true) ≠ Counts.revise ⟨0, 0⟩ true := by
  intro same
  have posEq : (scaleCounts (Counts.revise ⟨0, 0⟩ true)).pos =
      (Counts.revise ⟨0, 0⟩ true).pos := congrArg Counts.pos same
  simp [scaleCounts, Counts.revise] at posEq

/-- One observational revision, as a query state. -/
def oneObservation : QueryState := poolObservational ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ true

theorem one_observation_is_revise :
    oneObservation.observational = Counts.revise ⟨0, 0⟩ true ∧
      oneObservation.interventional = ⟨0, 0⟩ := by
  constructor <;> rfl

/-- **One observation becomes two** under the doubling translation. -/
theorem duplication_turns_one_into_two :
    (scaleQuery oneObservation).observational.pos = 2 ∧
      oneObservation.observational.pos = 1 := by
  constructor
  · simp [scaleQuery, oneObservation, scaleCounts, poolObservational, Counts.revise]
  · rfl

/-- Revising the translated state is not translating the revised state. -/
theorem revise_scale_ne_scale_revise (counts : Counts) :
    (scaleCounts counts).revise true ≠ scaleCounts (counts.revise true) := by
  intro same
  cases counts
  have posEq := congrArg Counts.pos same
  simp [scaleCounts, Counts.revise] at posEq
  omega

theorem revise_query_ne_translate_query (counts : Counts) :
    poolObservational (scaleQuery ⟨counts, ⟨0, 0⟩⟩) true ≠
      scaleQuery (poolObservational ⟨counts, ⟨0, 0⟩⟩ true) := by
  intro same
  have observational := congrArg QueryState.observational same
  simp [poolObservational, scaleQuery] at observational
  exact revise_scale_ne_scale_revise counts observational

/-- Doubling the observational fibre leaves an interventional ratio alone.
One `poolInterventional` revises that ratio once; it does not double it. -/
theorem interventional_ratio_not_duplicated :
    (scaleQuery ⟨countsOfRatio 1 2, countsOfRatio 1 2⟩).interventional = countsOfRatio 1 2 ∧
      (poolInterventional (scaleQuery ⟨countsOfRatio 1 2, countsOfRatio 1 2⟩) true).interventional =
        (countsOfRatio 1 2).revise true ∧
      (poolInterventional (scaleQuery ⟨countsOfRatio 1 2, countsOfRatio 1 2⟩) true).observational =
        scaleCounts (countsOfRatio 1 2) := by
  refine ⟨rfl, rfl, rfl⟩

/-- **With the correction the two orders agree.** Pooling the doubled fibre
back to one observation makes revising and translating commute. -/
theorem corrected_orders_agree (counts : Counts) :
    unscaleCounts (scaleCounts (counts.revise true)) =
      (unscaleCounts (scaleCounts counts)).revise true := by
  rw [unscale_scale, unscale_scale]

theorem corrected_query_orders_agree (counts : Counts) :
    unscaleQuery (scaleQuery (poolObservational ⟨counts, ⟨0, 0⟩⟩ true)) =
      poolObservational (unscaleQuery (scaleQuery ⟨counts, ⟨0, 0⟩⟩)) true := by
  simp [unscaleQuery, scaleQuery, poolObservational, corrected_orders_agree]

end Mettapedia.Logic.HostingStyles.Weighted
