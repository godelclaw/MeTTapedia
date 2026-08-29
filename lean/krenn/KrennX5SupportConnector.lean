import KrennX5NormalizationConnector

/-!
The semantic support connector for the
`X = {01,02,03,04,15}` orbit.

The orbit census chooses one live off-diagonal channel on each of the five
physical support edges.  The other ten physical edges have no off-diagonal
channel.  This module proves that the exact symmetry and integral gauge
normalization preserve that support statement, and packages the normalized
witness in a representative-indexed predicate.
-/

namespace Krenn.X5SupportConnector

open MonochromaticQuantumGraph
open Krenn.X5Symmetry
open Krenn.X5GaugeNormalizationData
open Krenn.X5OrbitWitness

/-- Vanishing of every off-diagonal channel outside
`{01,02,03,04,15}`. -/
structure OutsideX5 (W : WeightsN 6 3 ℂ) : Prop where
  outside05 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 0 5 i j) = 0
  outside12 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 2 i j) = 0
  outside13 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 3 i j) = 0
  outside14 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 4 i j) = 0
  outside23 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 3 i j) = 0
  outside24 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 4 i j) = 0
  outside25 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 5 i j) = 0
  outside34 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 3 4 i j) = 0
  outside35 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 3 5 i j) = 0
  outside45 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 4 5 i j) = 0

/-- A labelled X5 support chart: the chosen channel on each support edge is
live, and every off-diagonal channel outside the five physical edges is zero. -/
structure SupportChart (choice : CaseChoice) (W : WeightsN 6 3 ℂ) : Prop where
  live : ∀ slot, W (supportEntry choice slot) ≠ 0
  outside : OutsideX5 W

/-- The unlabelled physical X5 support condition.  It asserts that each of
the five supported physical edges has at least one live off-diagonal channel,
without choosing that channel in advance. -/
structure PhysicalX5Support (W : WeightsN 6 3 ℂ) : Prop where
  live : ∀ slot, ∃ channel,
    W (MonochromaticQuantumGraph.mkEdge
      (supportEndpoints slot).1 (supportEndpoints slot).2
      (offDiagonalColours channel).1 (offDiagonalColours channel).2) ≠ 0
  outside : OutsideX5 W

noncomputable def PhysicalX5Support.choice {W : WeightsN 6 3 ℂ}
    (support : PhysicalX5Support W) : CaseChoice :=
  fun slot => Classical.choose (support.live slot)

theorem PhysicalX5Support.toSupportChart {W : WeightsN 6 3 ℂ}
    (support : PhysicalX5Support W) :
    SupportChart support.choice W := by
  refine ⟨?_, support.outside⟩
  intro slot
  exact Classical.choose_spec (support.live slot)

/-- The representative-indexed normalized predicate shared by all 336 case
bridges.  It deliberately says nothing about the other channels on the five
supported physical edges. -/
structure NormalizedRepresentative (representative : Fin 336)
    (W : WeightsN 6 3 ℂ) : Prop extends OutsideX5 W where
  selected : ∀ slot, W ((datum representative).selected slot) = 1

set_option maxHeartbeats 10000000 in
theorem OutsideX5.transportToAction (leaf : LeafSymmetry)
    (colour : ColourSymmetry) (W : WeightsN 6 3 ℂ)
    (outside : OutsideX5 W) :
    OutsideX5 (transportToAction leaf colour W) := by
  rcases outside with ⟨h05, h12, h13, h14, h23, h24, h25, h34, h35, h45⟩
  constructor <;> intro i j hij
  all_goals fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases leaf <;> fin_cases colour <;>
    simp [Krenn.X5Symmetry.transportToAction,
      Krenn.OfficialGauge.relabelColours,
      relabelVertices, LeafSymmetry.inverse, ColourSymmetry.inverse,
      leafEquiv, colourEquiv, Equiv.swap_apply_def,
      MonochromaticQuantumGraph.mkEdge]
  all_goals first
    | simpa [MonochromaticQuantumGraph.mkEdge] using h05 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h12 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h13 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h14 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h23 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h24 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h25 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h34 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h35 _ _ (by decide)
    | simpa [MonochromaticQuantumGraph.mkEdge] using h45 _ _ (by decide)

theorem OutsideX5.of_same_zero_support
    (source target : WeightsN 6 3 ℂ)
    (same : ∀ edge, target edge = 0 ↔ source edge = 0)
    (outside : OutsideX5 source) : OutsideX5 target := by
  constructor
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 0 5 i j)).2 (outside.outside05 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 1 2 i j)).2 (outside.outside12 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 1 3 i j)).2 (outside.outside13 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 1 4 i j)).2 (outside.outside14 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 2 3 i j)).2 (outside.outside23 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 2 4 i j)).2 (outside.outside24 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 2 5 i j)).2 (outside.outside25 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 3 4 i j)).2 (outside.outside34 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 3 5 i j)).2 (outside.outside35 i j hij)
  · intro i j hij
    exact (same (MonochromaticQuantumGraph.mkEdge 4 5 i j)).2 (outside.outside45 i j hij)

/-- Every official witness in a labelled X5 support chart transports and
normalizes to its exact audited representative predicate. -/
theorem exists_normalized_representative
    (choice : CaseChoice) (W : WeightsN 6 3 ℂ)
    (hW : EqSystemN 6 3 W) (chart : SupportChart choice W) :
    ∃ (representative : Fin 336) (leaf : LeafSymmetry)
        (colour : ColourSymmetry) (normalized : WeightsN 6 3 ℂ),
      actCase leaf colour choice = representativeChoice representative ∧
      EqSystemN 6 3 normalized ∧
      NormalizedRepresentative representative normalized := by
  obtain ⟨representative, leaf, colour, normalized, action,
      normalizedSystem, sameSupport, selected⟩ :=
    Krenn.X5NormalizationConnector.exists_representative_normalized_witness
      choice W hW chart.live
  have transportedOutside : OutsideX5 (transportToAction leaf colour W) :=
    chart.outside.transportToAction leaf colour W
  have normalizedOutside : OutsideX5 normalized :=
    OutsideX5.of_same_zero_support _ _ sameSupport transportedOutside
  exact ⟨representative, leaf, colour, normalized, action,
    normalizedSystem, ⟨normalizedOutside, selected⟩⟩

/-- An unlabelled physical X5 witness is routed to one of the exact 336
normalized representatives.  This is the support-to-finite-census connector:
the representative label is produced by the proof rather than assumed. -/
theorem PhysicalX5Support.exists_normalized_representative
    (W : WeightsN 6 3 ℂ) (hW : EqSystemN 6 3 W)
    (support : PhysicalX5Support W) :
    ∃ (representative : Fin 336) (leaf : LeafSymmetry)
        (colour : ColourSymmetry) (normalized : WeightsN 6 3 ℂ),
      actCase leaf colour support.choice = representativeChoice representative ∧
      EqSystemN 6 3 normalized ∧
      NormalizedRepresentative representative normalized :=
  Krenn.X5SupportConnector.exists_normalized_representative
    support.choice W hW support.toSupportChart

#print axioms Krenn.X5SupportConnector.OutsideX5.transportToAction
#print axioms Krenn.X5SupportConnector.exists_normalized_representative
#print axioms Krenn.X5SupportConnector.PhysicalX5Support.exists_normalized_representative

end Krenn.X5SupportConnector
