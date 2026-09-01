import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityTransition

/-!
# Finite fixed-colour connectivity alternatives on a mesh row

This file packages the fixed-colour transition theorem in the quantifier
shape used by the sparse mesh atlas.  A row either exposes an existing
branching/boundary horn, or carries one coherent geometric sweep pair whose
endpoint connectivity is synchronized, or has one adjacent connectivity
change supported on at most ten edges.

The nonsynchronized receipt has a fixed finite code: one of eight adjacent
path steps and two of the ninety labelled boundary slots.  This code records
the exact observable transition without treating a change of locally absent
colour as a separate state.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FixedColorConnectivityAlternative

open AlternatingComponentLocalization
open AlternatingSiteGeometry
open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivityState
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

/-- The complete finite observable carried by a local fixed-colour
connectivity transition: its adjacent path coordinate and the two labelled
boundary slots whose reachability changes. -/
abbrev FixedColorConnectivityTransitionCode :=
  Fin 8 × PathBoundarySlot × PathBoundarySlot

theorem card_fixedColorConnectivityTransitionCode :
    Fintype.card FixedColorConnectivityTransitionCode = 64800 := by
  simp [FixedColorConnectivityTransitionCode]

/-- Forget the proof fields of a local transition while retaining every
observable choice. -/
def FixedColorLocalConnectivityTransitionReceipt.toCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    FixedColorConnectivityTransitionCode :=
  (receipt.index, receipt.left, receipt.right)

/-- The finite code loses no information about a transition receipt; its
remaining field is a proof and is propositionally irrelevant. -/
theorem FixedColorLocalConnectivityTransitionReceipt.toCode_injective
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    Function.Injective
      (FixedColorLocalConnectivityTransitionReceipt.toCode
        rotation minimal family minimizer pair) := by
  intro first second hcode
  cases first with
  | mk firstIndex firstLeft firstRight firstDiffers =>
      cases second with
      | mk secondIndex secondLeft secondRight secondDiffers =>
          simp only [FixedColorLocalConnectivityTransitionReceipt.toCode,
            Prod.mk.injEq] at hcode
          rcases hcode with ⟨rfl, rfl, rfl⟩
          rfl

/-- Every actual local transition changes only edges in its two deletion
footprints. -/
theorem FixedColorLocalConnectivityTransitionReceipt.edgeDisagreement_subset_localFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    SimpleGraph.edgeDisagreementFinset
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          receipt.index.castSucc)
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          receipt.index.succ) ⊆
      overlapFootprintValues
        (family.data receipt.index.castSucc)
        (family.data receipt.index.succ) :=
  SimpleGraph.edgeDisagreementFinset_subset_of_deleteEdges_eq _ _ _
    (receipt.deleteLocalFootprint_eq rotation minimal family minimizer pair)

/-- Quantitative form of local fixed-colour continuity: consecutive graphs
in a genuine transition disagree on at most ten ambient edges. -/
theorem FixedColorLocalConnectivityTransitionReceipt.card_edgeDisagreement_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (SimpleGraph.edgeDisagreementFinset
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        receipt.index.castSucc)
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        receipt.index.succ)).card ≤ 10 :=
  (Finset.card_le_card
    (edgeDisagreement_subset_localFootprint rotation minimal family minimizer
      pair receipt)).trans
    (receipt.card_localFootprint_le
      rotation minimal family minimizer pair)

variable {a : Nat}

/-- Consumer-facing row alternative.  The sparse mesh atlas either exposes
its existing branching/boundary horn, or supplies one coherent pair for which
connectivity is synchronized or changes in one explicitly finite local
transition. -/
theorem branchingOrBoundary_or_synchronized_or_fixedColorLocalTransition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (∃ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      ∃ pair : CoherentGeometricSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer,
        ConnectivitySynchronized rotation minimal
            (coloringFamily rotation minimal ordered minimizer row) minimizer pair ∨
          Nonempty (FixedColorLocalConnectivityTransitionReceipt
            rotation minimal
              (coloringFamily rotation minimal ordered minimizer row)
              minimizer pair) := by
  rcases branchingOrBoundary_or_hasCoherentGeometricSweepPair
      rotation minimal ordered minimizer row with hhorn | hpair
  · exact Or.inl hhorn
  · change Nonempty (CoherentGeometricSweepPairReceipt rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer) at hpair
    rcases hpair with ⟨pair⟩
    exact Or.inr ⟨pair,
      synchronized_or_fixedColorLocalTransition rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair⟩

end

end FixedColorConnectivityAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
