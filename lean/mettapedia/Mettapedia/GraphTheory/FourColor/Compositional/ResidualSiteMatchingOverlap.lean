import Mettapedia.GraphTheory.FourColor.Compositional.DeletionColorMatching
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshColoringAtlas

/-!
# Finite overlap states for provenanced residual matchings

At each mesh site, the residual construction selects a perfect matching by
choosing one colour absent from the four boundary requests.  Two such local
matchings agree on their common retained edges once two finite coordinates
agree: the absent-colour index and the existing Boolean common-restriction
coordinate of the deletion colourings.

This module packages precisely those coordinates.  It proves a pointwise
consumer theorem and no global synchronization claim.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteMatchingOverlap

open Amplitude
open DeletionColorMatching
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open ResidualSiteProvenance
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- The two finite coordinates controlling whether two provenanced local
matchings agree on their shared retained carrier. -/
structure MatchingOverlapState where
  sourceAbsent : Fin 3
  targetAbsent : Fin 3
  commonRestrictionAgrees : Bool
deriving DecidableEq, Fintype

/-- There are exactly `3 · 3 · 2 = 18` matching-overlap states. -/
theorem card_matchingOverlapState : Fintype.card MatchingOverlapState = 18 := by
  decide

namespace MatchingOverlapState

/-- The matching-overlap state is compatible exactly when the two sites use
the same colour class and their deletion colourings agree on the common core. -/
def Compatible (state : MatchingOverlapState) : Prop :=
  state.sourceAbsent = state.targetAbsent ∧
    state.commonRestrictionAgrees = true

instance (state : MatchingOverlapState) : Decidable state.Compatible :=
  by
    unfold Compatible
    infer_instance

end MatchingOverlapState

/-- Evaluate the finite overlap state of two deletion-matching states. -/
def matchingOverlapState
    {sourceData targetData : AdjacentPairData G}
    (source : DeletionMatchingState sourceData)
    (target : DeletionMatchingState targetData) : MatchingOverlapState where
  sourceAbsent := source.absentColor
  targetAbsent := target.absentColor
  commonRestrictionAgrees :=
    commonRestrictionAgreementBit sourceData targetData
      source.coloring target.coloring

/-- Compatibility of the finite state forces two completed deletion
matchings to agree on every common retained ambient edge. -/
theorem deletionMatchingStates_agree_on_common_retained_edge
    {sourceData targetData : AdjacentPairData G}
    (source : DeletionMatchingState sourceData)
    (target : DeletionMatchingState targetData)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hcompatible : (matchingOverlapState source target).Compatible)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge sourceData edge)
    (htarget : IsRetainedAmbientEdge targetData edge) :
    edge.1 ∈ edges (source.pairing hcubic).toPerm ↔
      edge.1 ∈ edges (target.pairing hcubic).toPerm := by
  rcases hcompatible with ⟨habsent, hagrees⟩
  change source.absentColor = target.absentColor at habsent
  change commonRestrictionAgreementBit sourceData targetData
    source.coloring target.coloring = true at hagrees
  simp only [DeletionMatchingState.pairing]
  rw [centralCompletionPairing_mem_retainedEdge_iff sourceData hcubic
    source.coloring source.isTait source.absentColor
    source.absentAtBoundary edge hsource]
  rw [centralCompletionPairing_mem_retainedEdge_iff targetData hcubic
    target.coloring target.isTait target.absentColor
    target.absentAtBoundary edge htarget]
  have hcolour := coloring_eq_on_common_retained_edge
    sourceData targetData source.coloring target.coloring
    edge hsource htarget hagrees
  rw [hcolour, habsent]

/-- Forget the mesh indexing of a provenance receipt and retain its generic
deletion-matching state. -/
def provenanceDeletionMatchingState
    {rotation : SimpleGraphDartRotation.Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {step : GlobalMeshStep rotation ordered}
    (receipt : GlobalSitePairingProvenance
      rotation minimal ordered step) :
    DeletionMatchingState receipt.site.data where
  coloring := receipt.site.base
  isTait := receipt.site.baseTait
  absentColor := receipt.absentColor
  absentAtBoundary := receipt.absentAtBoundary

/-- Evaluate the generic finite state on two provenanced mesh sites. -/
def globalMatchingOverlapState
    {rotation : SimpleGraphDartRotation.Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {sourceStep targetStep : GlobalMeshStep rotation ordered}
    (source : GlobalSitePairingProvenance
      rotation minimal ordered sourceStep)
    (target : GlobalSitePairingProvenance
      rotation minimal ordered targetStep) : MatchingOverlapState :=
  matchingOverlapState (provenanceDeletionMatchingState source)
    (provenanceDeletionMatchingState target)

/-- A compatible finite overlap state forces the two provenanced matchings
to make the same decision on every ambient edge retained at both sites. -/
theorem pairings_agree_on_common_retained_edge
    {rotation : SimpleGraphDartRotation.Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {sourceStep targetStep : GlobalMeshStep rotation ordered}
    (source : GlobalSitePairingProvenance
      rotation minimal ordered sourceStep)
    (target : GlobalSitePairingProvenance
      rotation minimal ordered targetStep)
    (hcompatible : (globalMatchingOverlapState source target).Compatible)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source.site.data edge)
    (htarget : IsRetainedAmbientEdge target.site.data edge) :
    edge.1 ∈ edges source.pairing.toPerm ↔
      edge.1 ∈ edges target.pairing.toPerm := by
  simpa [globalMatchingOverlapState, provenanceDeletionMatchingState,
    DeletionMatchingState.pairing,
    GlobalSitePairingProvenance.pairing] using
    deletionMatchingStates_agree_on_common_retained_edge
      (provenanceDeletionMatchingState source)
      (provenanceDeletionMatchingState target)
      (incidentEdgeFinset_card_eq_three rotation minimal)
      hcompatible edge hsource htarget

/-- Any disagreement between the two completed matchings on a common
retained edge certifies failure of their finite compatibility state. -/
theorem matchingOverlapState_not_compatible_of_pairing_disagreement
    {rotation : SimpleGraphDartRotation.Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {sourceStep targetStep : GlobalMeshStep rotation ordered}
    (source : GlobalSitePairingProvenance
      rotation minimal ordered sourceStep)
    (target : GlobalSitePairingProvenance
      rotation minimal ordered targetStep)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source.site.data edge)
    (htarget : IsRetainedAmbientEdge target.site.data edge)
    (hdisagrees : ¬ (edge.1 ∈ edges source.pairing.toPerm ↔
      edge.1 ∈ edges target.pairing.toPerm)) :
    ¬ (globalMatchingOverlapState source target).Compatible := by
  intro hcompatible
  exact hdisagrees
    (pairings_agree_on_common_retained_edge source target hcompatible
      edge hsource htarget)

/-- **Nine-site matching-overlap obstruction.**  For any provenanced
matching choices on nine distinct intervals of one mesh row, two sites have
an incompatible finite overlap state.  Thus finite-state repetition alone
cannot supply a globally compatible matching atlas; the common-core
disagreement residue must be resolved. -/
theorem exists_incompatible_pair_in_any_nine_row_intervals
    {n : Nat}
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (receipt : ∀ index : Fin 9,
      GlobalSitePairingProvenance rotation minimal ordered
        (globalRowStep rotation ordered row (slot index))) :
    ∃ first second : Fin 9,
      ¬ (globalMatchingOverlapState
        (receipt first) (receipt second)).Compatible := by
  obtain ⟨first, second, hfalse⟩ :=
    exists_disagreement_in_any_nine_row_intervals
      rotation minimal ordered row slot
  refine ⟨first, second, ?_⟩
  intro hcompatible
  have htrue := hcompatible.2
  change commonRestrictionAgreementBit
      (receipt first).site.data (receipt second).site.data
      (receipt first).site.base (receipt second).site.base = true at htrue
  rw [(receipt first).site_eq_selected,
    (receipt second).site_eq_selected] at htrue
  rw [hfalse] at htrue
  contradiction

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteMatchingOverlap
