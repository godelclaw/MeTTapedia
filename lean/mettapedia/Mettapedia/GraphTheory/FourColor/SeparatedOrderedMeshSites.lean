import Mettapedia.GraphTheory.FourColor.SeparatedPairDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue

/-!
# Ambient-separated deletion sites supplied by a long ordered row

The two endpoint maps of the selected row steps are separately injective.
In a cubic graph, the twice-closed neighborhood of two vertices has at most
32 vertices, so it blocks at most 64 selected steps.  A row with at least
65 intervals therefore supplies, for every selected source, a target whose
closed deletion neighborhood is disjoint from the source's.

This is ambient separation with all lateral attachments included.  It
eliminates literal common-core repair at the supplied pair in the exact
least-counterexample class.  The branching/boundary alternatives remain;
neither is asserted to be a long strand or a physical replacement.
-/

namespace Mettapedia.GraphTheory.FourColor.SeparatedOrderedMeshSites

open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24RotationMultigraphAdapter GoertzelV24TwoEdgeCutMinimality
open SeparatedPairDeletion SimpleGraph SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {a n : Nat}
  (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))

abbrev siteData (row : Fin a) (column : Fin n) : AdjacentPairData G :=
  (selectedGlobalKempeSite rotation minimal ordered
    (globalRowStep rotation ordered row column)).data

/-- Every chosen source has an ambient-separated target; neither the target
nor a separation receipt is assumed. -/
theorem exists_separated_rowSite (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      Separated (siteData rotation minimal ordered row source)
        (siteData rotation minimal ordered row target) := by
  let s := deleted (siteData rotation minimal ordered row source)
  let forbidden := close G (close G s)
  have hdegree (v : V) : G.degree v ≤ 3 := by
    exact Nat.le_of_eq ((rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic) v)
  have hs : s.card ≤ 2 := by
    calc
      s.card ≤ ({(siteData rotation minimal ordered row source).secondVertex} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hclose := card_close_le 3 hdegree s
  have htwice := card_close_le 3 hdegree (close G s)
  have hcard : forbidden.card ≤ 32 := by dsimp [forbidden]; omega
  obtain ⟨target, hfirst, hsecond⟩ :=
    exists_rowStep_avoiding rotation ordered row forbidden (by omega)
  have hfirst' : (siteData rotation minimal ordered row target).firstVertex ∉ forbidden := by
    simpa only [siteData,
      (selectedGlobalKempeSite rotation minimal ordered
        (globalRowStep rotation ordered row target)).first_eq,
      globalFirstVertex_globalRowStep] using hfirst
  have hsecond' : (siteData rotation minimal ordered row target).secondVertex ∉ forbidden := by
    simpa only [siteData,
      (selectedGlobalKempeSite rotation minimal ordered
        (globalRowStep rotation ordered row target)).second_eq,
      globalSecondVertex_globalRowStep] using hsecond
  refine ⟨target, ?_, ?_⟩
  · intro heq
    subst target
    apply hfirst'
    exact subset_close _ (subset_close s (by simp [s, deleted]))
  · apply disjoint_close_of_avoid_twice
    intro v hv
    simp only [deleted, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hfirst'
    · exact hsecond'

/-- A supplied separated pair has disjoint sets of common-core restrictions
of proper nonzero deletion colourings, independently of representative choices. -/
theorem exists_rowSite_with_no_commonCore_agreement
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ sourceColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
      ∀ targetColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row target).firstVertex
          (siteData rotation minimal ordered row target).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ sourceColor → IsTaitEdgeColoring _ targetColor →
          CommonCoreColoringsDisagree
            (siteData rotation minimal ordered row source)
            (siteData rotation minimal ordered row target) sourceColor targetColor := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  refine ⟨target, hne, fun sourceColor targetColor hs ht => ?_⟩
  exact not_commonCore_eq_of_minimal _ _ sourceColor targetColor hs ht rotation minimal hsep

/-- The strict-repair alternative is removed for all representatives at one
geometrically supplied pair, not just for a selected nine-site assignment. -/
theorem exists_rowSite_forcing_branching_or_boundary
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ sourceColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
      ∀ targetColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row target).firstVertex
          (siteData rotation minimal ordered row target).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ sourceColor → IsTaitEdgeColoring _ targetColor →
          HasCommonCoreBranchingDiscrepancy
              (siteData rotation minimal ordered row source)
              (siteData rotation minimal ordered row target) sourceColor targetColor ∨
            FirstTaitOrbitReachesSecondPair
              (siteData rotation minimal ordered row source)
              (siteData rotation minimal ordered row target) sourceColor := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  refine ⟨target, hne, fun sourceColor targetColor hs ht => ?_⟩
  exact branching_or_taitReachesSecondPair_of_separated _ _ sourceColor targetColor
    hs ht rotation minimal hsep

end
end Mettapedia.GraphTheory.FourColor.SeparatedOrderedMeshSites
