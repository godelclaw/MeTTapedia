import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityAlternative

/-!
# Colour-indexed connectivity along a coherent deletion path

The fixed-colour transition layer follows one selected Tait colour.  The
source closed-web profile ultimately observes two complementary Kempe
families, so this file first records the conservative internal refinement:
the boundary-connectivity state for every one of the three Tait colours.

This is still a semantic state.  Each coordinate is the exact reachability
relation of the corresponding central-augmented colour-class graph against
the fixed ambient pairing.  It is not identified with a raw sweep state or
with the source's two-role profile.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ColorIndexedConnectivityTransition

open CentralAugmentedColorClass
open AlternatingComponentLocalization
open AlternatingSiteGeometry
open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivity
open DeletionPathConnectivityState
open DeletionPathLocalization
open FixedColorConnectivityTransition
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24ResidualDefectDescent
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.Logic
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The fixed finite boundary state for one explicitly chosen Tait colour. -/
def colorConnectivityStateAt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (colour : Fin 3) (index : Fin 9) : SimpleGraph PathBoundarySlot :=
  pathConnectivityState
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer colour index) family

/-- The conservative three-colour connectivity state at one path coordinate. -/
def colorIndexedConnectivityStateAt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (index : Fin 9) : Fin 3 → SimpleGraph PathBoundarySlot :=
  fun colour =>
    colorConnectivityStateAt rotation minimal family minimizer pair colour index

/-- The graph-independent carrier of the complete three-colour connectivity
state. -/
abbrev ColorIndexedConnectivityState :=
  Fin 3 → SimpleGraph PathBoundarySlot

/-- Exact semantic interpretation of one colour coordinate. -/
theorem colorConnectivityStateAt_reachable_iff
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (colour : Fin 3) (index : Fin 9) (left right : PathBoundarySlot) :
    (colorConnectivityStateAt rotation minimal family minimizer pair colour
        index).Reachable left right ↔
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer colour index).Reachable
        (pathBoundaryVertex family left) (pathBoundaryVertex family right) :=
  pathConnectivityState_reachable_iff _ _ _ _

/-- The indexed state projects to the previously selected fixed-colour state. -/
@[simp]
theorem colorConnectivityStateAt_sweepColour
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (index : Fin 9) :
    colorConnectivityStateAt rotation minimal family minimizer pair
        (sweepColour rotation minimal family minimizer pair) index =
      fixedConnectivityStateAt rotation minimal family minimizer pair index :=
  rfl

/-- All three labelled connectivity relations agree at the selected endpoints. -/
def ColorIndexedConnectivitySynchronized
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) : Prop :=
  colorIndexedConnectivityStateAt rotation minimal family minimizer pair
      pair.first =
    colorIndexedConnectivityStateAt rotation minimal family minimizer pair
      pair.second

/-- Synchronization of the conservative state implies synchronization of the
completed matching component used by the residual-return sweep. -/
theorem connectivitySynchronized_of_colorIndexed
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (hsynchronized : ColorIndexedConnectivitySynchronized rotation minimal
      family minimizer pair) :
    ConnectivitySynchronized rotation minimal family minimizer pair := by
  unfold ColorIndexedConnectivitySynchronized at hsynchronized
  have hselected := congrFun hsynchronized
    (sweepColour rotation minimal family minimizer pair)
  unfold colorIndexedConnectivityStateAt at hselected
  unfold ConnectivitySynchronized
  rw [← fixedConnectivityStateAt_first rotation minimal family minimizer pair,
    ← fixedConnectivityStateAt_second rotation minimal family minimizer pair]
  simpa only [colorConnectivityStateAt_sweepColour] using hselected

/-- One adjacent path step changes reachability for one explicit Tait colour. -/
structure ColorLocalConnectivityTransitionReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) where
  colour : Fin 3
  index : Fin 8
  left : PathBoundarySlot
  right : PathBoundarySlot
  reachabilityDiffers : ¬
    ((pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer colour index.castSucc).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer colour index.succ).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right))

/-- The complete finite observable of a colour-local transition. -/
abbrev ColorLocalConnectivityTransitionCode :=
  Fin 3 × Fin 8 × PathBoundarySlot × PathBoundarySlot

theorem card_colorLocalConnectivityTransitionCode :
    Fintype.card ColorLocalConnectivityTransitionCode = 194400 := by
  simp [ColorLocalConnectivityTransitionCode]

/-- Forget only proof fields from a colour-local transition receipt. -/
def ColorLocalConnectivityTransitionReceipt.toCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : ColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    ColorLocalConnectivityTransitionCode :=
  (receipt.colour, receipt.index, receipt.left, receipt.right)

/-- The finite code loses no data: the omitted field is a proposition. -/
theorem ColorLocalConnectivityTransitionReceipt.toCode_injective
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    Function.Injective
      (ColorLocalConnectivityTransitionReceipt.toCode rotation minimal family
        minimizer pair) := by
  intro first second hcode
  cases first with
  | mk firstColour firstIndex firstLeft firstRight firstDiffers =>
      cases second with
      | mk secondColour secondIndex secondLeft secondRight secondDiffers =>
          simp only [ColorLocalConnectivityTransitionReceipt.toCode,
            Prod.mk.injEq] at hcode
          rcases hcode with ⟨rfl, rfl, rfl, rfl⟩
          rfl

/-- Inequality of one colour coordinate exposes exact labelled boundary slots. -/
theorem exists_boundary_slots_of_colorConnectivityStateAt_ne
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (colour : Fin 3) (first second : Fin 9)
    (hne : colorConnectivityStateAt rotation minimal family minimizer pair
        colour first ≠
      colorConnectivityStateAt rotation minimal family minimizer pair
        colour second) :
    ∃ left right : PathBoundarySlot, ¬
      ((pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer colour first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer colour second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right)) := by
  classical
  have hnotAll : ¬ ∀ left right : PathBoundarySlot,
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer colour first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer colour second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right) := by
    intro hall
    apply hne
    exact (pathConnectivityState_eq_iff
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer colour first)
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer colour second) family).2 hall
  by_contra hnone
  apply hnotAll
  intro left right
  by_contra hdiffers
  exact hnone ⟨left, right, hdiffers⟩

/-- The complete three-colour state either agrees at the endpoints or one
colour has an explicitly localized adjacent transition. -/
theorem colorIndexedSynchronized_or_localTransition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    ColorIndexedConnectivitySynchronized rotation minimal family minimizer pair ∨
      Nonempty (ColorLocalConnectivityTransitionReceipt
        rotation minimal family minimizer pair) := by
  classical
  by_cases hsynchronized : ColorIndexedConnectivitySynchronized rotation
      minimal family minimizer pair
  · exact Or.inl hsynchronized
  · right
    have hcolour : ∃ colour : Fin 3,
        colorConnectivityStateAt rotation minimal family minimizer pair colour
            pair.first ≠
          colorConnectivityStateAt rotation minimal family minimizer pair colour
            pair.second := by
      by_contra hnone
      apply hsynchronized
      unfold ColorIndexedConnectivitySynchronized
      funext colour
      unfold colorIndexedConnectivityStateAt
      by_contra hne
      exact hnone ⟨colour, hne⟩
    rcases hcolour with ⟨colour, hendpoint⟩
    rcases PathConstraint.exists_adjacent_ne_of_ne
        (fun index : Fin 9 => colorConnectivityStateAt rotation minimal family
          minimizer pair colour index) hendpoint with ⟨index, hstate⟩
    rcases exists_boundary_slots_of_colorConnectivityStateAt_ne rotation
        minimal family minimizer pair colour index.castSucc index.succ hstate with
      ⟨left, right, hdiffers⟩
    exact ⟨⟨colour, index, left, right, hdiffers⟩⟩

/-- The two graphs in a colour-local transition are literally equal outside
the union of the two adjacent deletion footprints. -/
theorem ColorLocalConnectivityTransitionReceipt.deleteLocalFootprint_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : ColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer receipt.colour receipt.index.castSucc).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) =
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer receipt.colour receipt.index.succ).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) := by
  simpa only [pathFixedColorAlternatingGraph] using
    (fixedColorAlternatingGraphs_delete_overlapFootprints_eq
      minimizer.pairing minimizer.supported
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ)
      (matchingState rotation minimal family pair.pathSection
        receipt.index.castSucc).coloring
      (matchingState rotation minimal family pair.pathSection
        receipt.index.succ).coloring
      (pair.pathSection.compatible receipt.index).2 receipt.colour)

/-- Every colour-local transition is supported on at most ten ambient edges. -/
theorem ColorLocalConnectivityTransitionReceipt.card_edgeDisagreement_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : ColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (SimpleGraph.edgeDisagreementFinset
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer receipt.colour receipt.index.castSucc)
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer receipt.colour receipt.index.succ)).card ≤ 10 := by
  apply (Finset.card_le_card
    (SimpleGraph.edgeDisagreementFinset_subset_of_deleteEdges_eq _ _ _
      (receipt.deleteLocalFootprint_eq rotation minimal family minimizer pair))).trans
  exact card_overlapFootprintValues_le _ _

end

end ColorIndexedConnectivityTransition

end Mettapedia.GraphTheory.FourColor.Compositional
