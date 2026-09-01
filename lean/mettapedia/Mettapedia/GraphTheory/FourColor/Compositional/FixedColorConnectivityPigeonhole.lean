import Mathlib.Data.Fintype.Pigeonhole
import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityAlternative

/-!
# Repeated fixed-colour connectivity transitions across mesh rows

The local fixed-colour alternative has one finite observable: the followed
colour, the adjacent deletion-path coordinate, and the two labelled boundary
slots whose reachability changes.  This file packages that observable across
rows and applies the finite pigeonhole principle.

Equal codes record equal transition *shapes*.  They do not by themselves
identify the ambient pieces or justify a physical splice; that later geometric
compatibility theorem remains an explicit consumer obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FixedColorConnectivityPigeonhole

open AlternatingComponentLocalization
open AlternatingSiteGeometry
open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open FixedColorConnectivityAlternative
open FixedColorConnectivityTransition
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open SparseNoncentralMeshAtlas

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a : Nat}

/-- The complete row-independent observable of a local fixed-colour
connectivity transition. -/
abbrev FixedColorRowTransitionCode :=
  Fin 3 × FixedColorConnectivityTransitionCode

theorem card_fixedColorRowTransitionCode :
    Fintype.card FixedColorRowTransitionCode = 194400 := by
  simp [FixedColorRowTransitionCode,
    FixedColorConnectivityTransitionCode]

/-- A row together with a coherent sweep pair and an actual nonsynchronized
adjacent transition for the one fixed endpoint colour. -/
structure FixedColorRowTransitionReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) where
  pair : CoherentGeometricSweepPairReceipt rotation minimal
    (coloringFamily rotation minimal ordered minimizer row) minimizer
  transition : FixedColorLocalConnectivityTransitionReceipt rotation minimal
    (coloringFamily rotation minimal ordered minimizer row) minimizer pair

/-- Forget the proof and ambient-row data while retaining the followed colour
and every observable of the local connectivity change. -/
def FixedColorRowTransitionReceipt.toCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a)
    (receipt : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer row) : FixedColorRowTransitionCode :=
  (sweepColour rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair,
    FixedColorConnectivityAlternative.FixedColorLocalConnectivityTransitionReceipt.toCode
      rotation minimal (coloringFamily rotation minimal ordered minimizer row)
      minimizer receipt.pair receipt.transition)

/-- Equality of row-transition codes is exactly equality of the four recorded
observables.  In particular, no ambient-carrier identification is hidden in
the finite code. -/
theorem FixedColorRowTransitionReceipt.toCode_eq_iff
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow) :
    first.toCode rotation minimal ordered minimizer firstRow =
        second.toCode rotation minimal ordered minimizer secondRow ↔
      sweepColour rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow)
          minimizer first.pair =
        sweepColour rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow)
          minimizer second.pair ∧
      first.transition.index = second.transition.index ∧
      first.transition.left = second.transition.left ∧
      first.transition.right = second.transition.right := by
  simp only [FixedColorRowTransitionReceipt.toCode,
    FixedColorConnectivityAlternative.FixedColorLocalConnectivityTransitionReceipt.toCode,
    Prod.mk.injEq]

/-- If neither of the first two row alternatives is available, the row carries
a local fixed-colour transition receipt. -/
theorem nonempty_fixedColorRowTransitionReceipt_of_no_horn_of_no_synchronized
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a)
    (hnoHorn : ∀ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      ¬ HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment)
    (hnoSynchronized : ∀ pair : CoherentGeometricSweepPairReceipt
        rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer,
      ¬ ConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair) :
    Nonempty (FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer row) := by
  rcases branchingOrBoundary_or_synchronized_or_fixedColorLocalTransition
      rotation minimal ordered minimizer row with
    hhorn | ⟨pair, hsynchronized | htransition⟩
  · rcases hhorn with ⟨assignment, hbranchingOrBoundary⟩
    exact (hnoHorn assignment hbranchingOrBoundary).elim
  · exact (hnoSynchronized pair hsynchronized).elim
  · rcases htransition with ⟨transition⟩
    exact ⟨⟨pair, transition⟩⟩

/-- If more rows carry only the local-transition alternative than there are
observable transition codes, two distinct rows carry equal codes.

This is a finite-state synchronization theorem, not a splice theorem: the
returned receipts still remember their distinct ambient rows, and a consumer
must prove the additional geometric compatibility needed for replacement. -/
theorem exists_distinct_rows_with_equal_fixedColorTransitionCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : 194400 < a)
    (hnoHorn : ∀ (row : Fin a) (assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row)),
      ¬ HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment)
    (hnoSynchronized : ∀ (row : Fin a)
        (pair : CoherentGeometricSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer),
      ¬ ConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair) :
    ∃ (first second : Fin a)
        (firstReceipt : FixedColorRowTransitionReceipt rotation minimal
          ordered minimizer first)
        (secondReceipt : FixedColorRowTransitionReceipt rotation minimal
          ordered minimizer second),
      first ≠ second ∧
        firstReceipt.toCode rotation minimal ordered minimizer first =
          secondReceipt.toCode rotation minimal ordered minimizer second := by
  let receipt : ∀ row : Fin a,
      FixedColorRowTransitionReceipt rotation minimal ordered minimizer row :=
    fun row => Classical.choice
      (nonempty_fixedColorRowTransitionReceipt_of_no_horn_of_no_synchronized
        rotation minimal ordered minimizer row (hnoHorn row)
        (hnoSynchronized row))
  let code : Fin a → FixedColorRowTransitionCode := fun row =>
    (receipt row).toCode rotation minimal ordered minimizer row
  have hcard : Fintype.card FixedColorRowTransitionCode <
      Fintype.card (Fin a) := by
    simpa [card_fixedColorRowTransitionCode] using hrows
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt code hcard
  exact ⟨first, second, receipt first, receipt second, hne, heq⟩

/-- Consumer-facing mesh alternative.  A sufficiently tall ordered mesh
either exposes one of the two already useful row alternatives, or repeats the
complete fixed-colour transition observable on two distinct rows. -/
theorem branchingOrBoundary_or_synchronized_or_repeatedFixedColorTransition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : 194400 < a) :
    (∃ (row : Fin a) (assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row)),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      (∃ (row : Fin a)
          (pair : CoherentGeometricSweepPairReceipt rotation minimal
            (coloringFamily rotation minimal ordered minimizer row) minimizer),
        ConnectivitySynchronized rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer pair) ∨
      ∃ (first second : Fin a)
          (firstReceipt : FixedColorRowTransitionReceipt rotation minimal
            ordered minimizer first)
          (secondReceipt : FixedColorRowTransitionReceipt rotation minimal
            ordered minimizer second),
        first ≠ second ∧
          firstReceipt.toCode rotation minimal ordered minimizer first =
            secondReceipt.toCode rotation minimal ordered minimizer second := by
  classical
  by_cases hhorn : ∃ (row : Fin a) (assignment : TaitAssignment
      (coloringFamily rotation minimal ordered minimizer row)),
    HasBranchingOrBoundary
      (coloringFamily rotation minimal ordered minimizer row) assignment
  · exact Or.inl hhorn
  · right
    by_cases hsynchronized : ∃ (row : Fin a)
        (pair : CoherentGeometricSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer),
      ConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair
    · exact Or.inl hsynchronized
    · right
      exact exists_distinct_rows_with_equal_fixedColorTransitionCode rotation
        minimal ordered minimizer hrows
        (fun row assignment hbranchingOrBoundary =>
          hhorn ⟨row, assignment, hbranchingOrBoundary⟩)
        (fun row pair hsynchronization =>
          hsynchronized ⟨row, pair, hsynchronization⟩)

end

end FixedColorConnectivityPigeonhole

end Mettapedia.GraphTheory.FourColor.Compositional
