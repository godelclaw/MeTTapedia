import Mathlib.Data.Fintype.Pigeonhole
import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityFrameSemantics
import Mettapedia.GraphTheory.FourColor.Compositional.FullProfileConnectivityAlternative

/-!
# Framed colour-indexed transitions on complete-profile mesh rows

The local colour-indexed alternative is useful globally only when the same
observable transition recurs with the same row-arm choices and the same
labelled boundary-connectivity relations on both sides of the change.  This
file records exactly that finite frame while retaining the unchanged
complete-profile sweep receipt at each physical row.

The frame is an internal residual-matching observable.  It is not identified
with the two-role closed-web profile from the source.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FullProfileColorConnectivityFrame

open AlternatingSiteGeometry
open ColorIndexedConnectivityTransition
open CoherentFullProfileSweep
open DeletionAtlasPath
open DeletionPathConnectivityState
open FixedColorConnectivityTransition
open FixedColorConnectivityFrame
open FixedColorConnectivityFrameSemantics
open FullProfileConnectivityAlternative
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MeshJunctionAlternatingGeometry
open SimpleGraph
open SimpleGraphDartRotation
open SparseNoncentralMeshAtlas

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a : Nat}

/-- A physical mesh row together with its unchanged complete-profile sweep
pair and one explicit colour-local connectivity transition. -/
structure FullProfileColorRowTransitionReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) where
  pair : CoherentFullProfileSweepPairReceipt rotation minimal
    (coloringFamily rotation minimal ordered minimizer row) minimizer
  transition : ColorLocalConnectivityTransitionReceipt rotation minimal
    (coloringFamily rotation minimal ordered minimizer row) minimizer pair.base

/-- The row-independent finite frame: the local transition code, both arm
choices, and the complete three-colour connectivity states immediately before
and after the transition. -/
abbrev FullProfileColorTransitionFrameCode :=
  ColorLocalConnectivityTransitionCode × Bool × Bool ×
    ColorIndexedConnectivityState × ColorIndexedConnectivityState

/-- Forget ambient vertices and proof fields while retaining every observable
needed to compare the same transition at two physical rows. -/
def fullProfileColorTransitionFrameCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a)
    (receipt : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer row) : FullProfileColorTransitionFrameCode :=
  (receipt.transition.toCode rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair.base,
    selectedIncomingArmBit rotation ordered minimizer row
      receipt.transition.index.castSucc,
    selectedIncomingArmBit rotation ordered minimizer row
      receipt.transition.index.succ,
    colorIndexedConnectivityStateAt rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair.base receipt.transition.index.castSucc,
    colorIndexedConnectivityStateAt rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair.base receipt.transition.index.succ)

/-- Equality of framed codes exposes its five components without identifying
the two ambient row carriers. -/
theorem fullProfileColorTransitionFrameCode_eq_iff
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow) :
    fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
        firstRow first =
      fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
        secondRow second ↔
      first.transition.toCode rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base =
        second.transition.toCode rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base ∧
      selectedIncomingArmBit rotation ordered minimizer firstRow
          first.transition.index.castSucc =
        selectedIncomingArmBit rotation ordered minimizer secondRow
          second.transition.index.castSucc ∧
      selectedIncomingArmBit rotation ordered minimizer firstRow
          first.transition.index.succ =
        selectedIncomingArmBit rotation ordered minimizer secondRow
          second.transition.index.succ ∧
      colorIndexedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base first.transition.index.castSucc =
        colorIndexedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base second.transition.index.castSucc ∧
      colorIndexedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base first.transition.index.succ =
        colorIndexedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base second.transition.index.succ := by
  simp only [fullProfileColorTransitionFrameCode, Prod.mk.injEq]

/-- If neither useful row alternative occurs, the row carries a framed local
transition on the same complete-profile pair. -/
theorem nonempty_fullProfileColorRowTransitionReceipt_of_no_horn_of_no_synchronized
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
    (hnoSynchronized : ∀ pair : CoherentFullProfileSweepPairReceipt
        rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer,
      ¬ ColorIndexedConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer
        pair.base) :
    Nonempty (FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer row) := by
  rcases branchingOrBoundary_or_fullProfilePair_with_colorIndexedAlternative
      rotation minimal ordered minimizer row with
    hhorn | ⟨pair, hsynchronized | htransition⟩
  · rcases hhorn with ⟨assignment, hbranchingOrBoundary⟩
    exact (hnoHorn assignment hbranchingOrBoundary).elim
  · exact (hnoSynchronized pair hsynchronized).elim
  · rcases htransition with ⟨transition⟩
    exact ⟨⟨pair, transition⟩⟩

/-- More physical rows than finite frames force the same complete observable
on two distinct rows.  The threshold remains symbolic so Lean never evaluates
the enormous adjacency-matrix cardinal as a closed numeral. -/
theorem exists_distinct_rows_with_equal_fullProfileColorTransitionFrame
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : Nat.card FullProfileColorTransitionFrameCode < a)
    (supply : ∀ row : Fin a,
      Nonempty (FullProfileColorRowTransitionReceipt rotation minimal ordered
        minimizer row)) :
    ∃ (first second : Fin a)
        (firstReceipt : FullProfileColorRowTransitionReceipt rotation minimal
          ordered minimizer first)
        (secondReceipt : FullProfileColorRowTransitionReceipt rotation minimal
          ordered minimizer second),
      first ≠ second ∧
        fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
            first firstReceipt =
          fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
            second secondReceipt := by
  letI : Fintype FullProfileColorTransitionFrameCode := Fintype.ofFinite _
  let receipt : ∀ row : Fin a,
      FullProfileColorRowTransitionReceipt rotation minimal ordered minimizer
        row := fun row => Classical.choice (supply row)
  let code : Fin a → FullProfileColorTransitionFrameCode := fun row =>
    fullProfileColorTransitionFrameCode rotation minimal ordered minimizer row
      (receipt row)
  have hcard : Fintype.card FullProfileColorTransitionFrameCode <
      Fintype.card (Fin a) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using hrows
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt code hcard
  exact ⟨first, second, receipt first, receipt second, hne, heq⟩

/-- The semantic content of equal colour-indexed transition frames. -/
structure FullProfileColorTransitionSemanticAgreement
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow) : Prop where
  transitionCode :
    first.transition.toCode rotation minimal
        (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
        first.pair.base =
      second.transition.toCode rotation minimal
        (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
        second.pair.base
  beforeUsesIncoming :
    (selectedRowStep rotation ordered minimizer firstRow
          first.transition.index.castSucc =
        incomingRowStep rotation ordered firstRow
          (sparseJunctionColumn first.transition.index.castSucc)) ↔
      selectedRowStep rotation ordered minimizer secondRow
          second.transition.index.castSucc =
        incomingRowStep rotation ordered secondRow
          (sparseJunctionColumn second.transition.index.castSucc)
  afterUsesIncoming :
    (selectedRowStep rotation ordered minimizer firstRow
          first.transition.index.succ =
        incomingRowStep rotation ordered firstRow
          (sparseJunctionColumn first.transition.index.succ)) ↔
      selectedRowStep rotation ordered minimizer secondRow
          second.transition.index.succ =
        incomingRowStep rotation ordered secondRow
          (sparseJunctionColumn second.transition.index.succ)
  beforeReachability : ∀ colour left right,
    (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow)
          first.pair.base.pathSection minimizer colour
          first.transition.index.castSucc).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) right) ↔
      (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow)
          second.pair.base.pathSection minimizer colour
          second.transition.index.castSucc).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) right)
  afterReachability : ∀ colour left right,
    (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow)
          first.pair.base.pathSection minimizer colour
          first.transition.index.succ).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) right) ↔
      (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow)
          second.pair.base.pathSection minimizer colour
          second.transition.index.succ).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) right)

/-- Equal finite frames give exact three-colour reachability agreement on the
common labelled boundary carrier. -/
theorem semanticAgreement_of_fullProfileColorTransitionFrame_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FullProfileColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow)
    (hframe :
      fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
          firstRow first =
        fullProfileColorTransitionFrameCode rotation minimal ordered minimizer
          secondRow second) :
    FullProfileColorTransitionSemanticAgreement rotation minimal ordered
      minimizer firstRow secondRow first second := by
  have hcomponents :=
    (fullProfileColorTransitionFrameCode_eq_iff rotation minimal ordered
      minimizer firstRow secondRow first second).1 hframe
  refine
    { transitionCode := hcomponents.1
      beforeUsesIncoming := ?_
      afterUsesIncoming := ?_
      beforeReachability := ?_
      afterReachability := ?_ }
  · rw [← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      ← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      hcomponents.2.1]
  · rw [← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      ← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      hcomponents.2.2.1]
  · intro colour left right
    have hstate :
        colorConnectivityStateAt rotation minimal
            (coloringFamily rotation minimal ordered minimizer firstRow)
            minimizer first.pair.base colour first.transition.index.castSucc =
          colorConnectivityStateAt rotation minimal
            (coloringFamily rotation minimal ordered minimizer secondRow)
            minimizer second.pair.base colour
            second.transition.index.castSucc := by
      simpa only [colorIndexedConnectivityStateAt] using
        congrFun hcomponents.2.2.2.1 colour
    constructor
    · intro hreachable
      have hstateReachable :=
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base colour first.transition.index.castSucc left right).2
          hreachable
      rw [hstate] at hstateReachable
      exact
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base colour second.transition.index.castSucc left right).1
          hstateReachable
    · intro hreachable
      have hstateReachable :=
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base colour second.transition.index.castSucc left right).2
          hreachable
      rw [← hstate] at hstateReachable
      exact
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base colour first.transition.index.castSucc left right).1
          hstateReachable
  · intro colour left right
    have hstate :
        colorConnectivityStateAt rotation minimal
            (coloringFamily rotation minimal ordered minimizer firstRow)
            minimizer first.pair.base colour first.transition.index.succ =
          colorConnectivityStateAt rotation minimal
            (coloringFamily rotation minimal ordered minimizer secondRow)
            minimizer second.pair.base colour second.transition.index.succ := by
      simpa only [colorIndexedConnectivityStateAt] using
        congrFun hcomponents.2.2.2.2 colour
    constructor
    · intro hreachable
      have hstateReachable :=
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base colour first.transition.index.succ left right).2
          hreachable
      rw [hstate] at hstateReachable
      exact
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base colour second.transition.index.succ left right).1
          hstateReachable
    · intro hreachable
      have hstateReachable :=
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair.base colour second.transition.index.succ left right).2
          hreachable
      rw [← hstate] at hstateReachable
      exact
        (colorConnectivityStateAt_reachable_iff rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair.base colour first.transition.index.succ left right).1
          hstateReachable

/-- Consumer-facing mesh theorem: a sufficiently tall ordered mesh exposes a
branching/boundary horn, one fully colour-synchronized complete-profile pair,
or the same framed colour-local transition at two distinct physical rows. -/
theorem branchingOrBoundary_or_colorSynchronized_or_repeatedFullProfileColorFrame
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : Nat.card FullProfileColorTransitionFrameCode < a) :
    (∃ (row : Fin a) (assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row)),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      (∃ (row : Fin a)
          (pair : CoherentFullProfileSweepPairReceipt rotation minimal
            (coloringFamily rotation minimal ordered minimizer row) minimizer),
        ColorIndexedConnectivitySynchronized rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer
          pair.base) ∨
      ∃ (first second : Fin a)
          (firstReceipt : FullProfileColorRowTransitionReceipt rotation minimal
            ordered minimizer first)
          (secondReceipt : FullProfileColorRowTransitionReceipt rotation minimal
            ordered minimizer second),
        first ≠ second ∧
          FullProfileColorTransitionSemanticAgreement rotation minimal ordered
            minimizer first second firstReceipt secondReceipt := by
  classical
  by_cases hhorn : ∃ (row : Fin a) (assignment : TaitAssignment
      (coloringFamily rotation minimal ordered minimizer row)),
    HasBranchingOrBoundary
      (coloringFamily rotation minimal ordered minimizer row) assignment
  · exact Or.inl hhorn
  · right
    by_cases hsynchronized : ∃ (row : Fin a)
        (pair : CoherentFullProfileSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer),
      ColorIndexedConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer
        pair.base
    · exact Or.inl hsynchronized
    · right
      rcases exists_distinct_rows_with_equal_fullProfileColorTransitionFrame
          rotation minimal ordered minimizer hrows (fun row =>
            nonempty_fullProfileColorRowTransitionReceipt_of_no_horn_of_no_synchronized
              rotation minimal ordered minimizer row
              (fun assignment hbranchingOrBoundary =>
                hhorn ⟨row, assignment, hbranchingOrBoundary⟩)
              (fun pair hsynchronization =>
                hsynchronized ⟨row, pair, hsynchronization⟩)) with
        ⟨first, second, firstReceipt, secondReceipt, hne, hframe⟩
      exact ⟨first, second, firstReceipt, secondReceipt, hne,
        semanticAgreement_of_fullProfileColorTransitionFrame_eq rotation
          minimal ordered minimizer first second firstReceipt secondReceipt
          hframe⟩

end

end FullProfileColorConnectivityFrame

end Mettapedia.GraphTheory.FourColor.Compositional
