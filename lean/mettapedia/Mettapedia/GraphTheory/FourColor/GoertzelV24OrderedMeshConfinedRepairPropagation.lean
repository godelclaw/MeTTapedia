import Mettapedia.GraphTheory.FourColor.GoertzelV24KempeLiftConfinement
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreLocalizationResidue

/-!
# Confined periodic repair forces disagreement propagation

The generic lift theorem now records that a non-boundary Kempe lift changes
no edge outside the exact common deletion.  This file carries that stronger
receipt through the finite nine-site repair dynamics.

The result removes the localized-collateral-loss horn: at an anchored trade,
the gained and lost partners must themselves disagree.  It does not yet show
that repeated disagreement propagation terminates at branching or at the
boundary, and therefore does not claim wall exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshConfinedRepairPropagation

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24KempeLiftConfinement
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshCommonCoreLocalizationResidue
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A strict Tait repair whose lifted Kempe sequence is pointwise unchanged
outside the exact common deletion. -/
def HasStrictConfinedTaitCommonCoreRepair
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  ∃ repaired,
    TaitKempeReachable sourceColoring repaired ∧
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      repaired ∧
    firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        repaired =
      secondDeletionCommonCoreColoring
        (first := source.firstVertex) (second := source.secondVertex)
        targetColoring ∧
    repaired ≠ sourceColoring ∧
    AgreesOutsideEmbedding sourceColoring repaired
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)

/-- The Tait common-core trichotomy with its full support receipt retained in
the strict-repair horn. -/
theorem branching_or_taitReachesSecondPair_or_strictConfinedTaitRepair
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hsource : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      sourceColoring)
    (htarget : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
      targetColoring)
    (hdisagrees : CommonCoreColoringsDisagree source target
      sourceColoring targetColoring) :
    HasCommonCoreBranchingDiscrepancy source target
        sourceColoring targetColoring ∨
      FirstTaitOrbitReachesSecondPair source target sourceColoring ∨
      HasStrictConfinedTaitCommonCoreRepair source target
        sourceColoring targetColoring := by
  let sourceCommon := firstDeletionCommonCoreColoring
    (third := target.firstVertex) (fourth := target.secondVertex)
    sourceColoring
  let targetCommon := secondDeletionCommonCoreColoring
    (first := source.firstVertex) (second := source.secondVertex)
    targetColoring
  have hsourceCommon : IsTaitEdgeColoring
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) sourceCommon :=
    isTaitEdgeColoring_firstDeletionCommonCoreColoring sourceColoring hsource
  have htargetCommon : IsTaitEdgeColoring
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) targetCommon :=
    isTaitEdgeColoring_secondDeletionCommonCoreColoring targetColoring htarget
  by_cases hreachable : TaitKempeReachable sourceCommon targetCommon
  · rcases firstTaitOrbitReachesSecondPair_or_exists_confinedLiftedColoring
      source target sourceColoring hsource targetCommon hreachable with
      hboundary |
        ⟨repaired, hrepaired, hrepairedTait, hrestriction, hconfined⟩
    · exact Or.inr (Or.inl hboundary)
    · right
      right
      refine ⟨repaired, hrepaired, hrepairedTait, hrestriction, ?_, hconfined⟩
      intro heq
      subst repaired
      exact hdisagrees hrestriction
  · left
    exact exists_not_locallySwapRelated_of_not_taitKempeReachable
      sourceCommon targetCommon hsourceCommon htargetCommon hreachable

variable {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

/-- A nine-site strict repair together with the fact that its repaired
coordinate changes only on the exact common deletion with the gained
partner. -/
def NineSiteConfinedStrictRepairStep
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (source target : NineSiteTaitAssignment rotation minimal ordered row slot) :
    Prop :=
  ∃ repaired gainedPartner : Fin 9,
    repaired ≠ gainedPartner ∧
    TaitKempeReachable (source repaired).1 (target repaired).1 ∧
    CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot repaired)
      (rowSiteData rotation minimal ordered row slot gainedPartner)
      (source repaired).1 (source gainedPartner).1 ∧
    firstDeletionCommonCoreColoring
        (third := (rowSiteData rotation minimal ordered row slot
          gainedPartner).firstVertex)
        (fourth := (rowSiteData rotation minimal ordered row slot
          gainedPartner).secondVertex)
        (target repaired).1 =
      secondDeletionCommonCoreColoring
        (first := (rowSiteData rotation minimal ordered row slot
          repaired).firstVertex)
        (second := (rowSiteData rotation minimal ordered row slot
          repaired).secondVertex)
        (source gainedPartner).1 ∧
    (target repaired).1 ≠ (source repaired).1 ∧
    (∀ index, index ≠ repaired → target index = source index) ∧
    AgreesOutsideEmbedding (source repaired).1 (target repaired).1
      (deletedTwoPairsToFirstDeletionEmbedding G
        (rowSiteData rotation minimal ordered row slot repaired).firstVertex
        (rowSiteData rotation minimal ordered row slot repaired).secondVertex
        (rowSiteData rotation minimal ordered row slot
          gainedPartner).firstVertex
        (rowSiteData rotation minimal ordered row slot
          gainedPartner).secondVertex)

/-- Forgetting confinement gives the previous strict-repair relation. -/
theorem NineSiteConfinedStrictRepairStep.toStrictRepairStep
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteConfinedStrictRepairStep
      rotation minimal ordered row slot source target) :
    NineSiteStrictRepairStep rotation minimal ordered row slot source target := by
  rcases hstep with
    ⟨repaired, gainedPartner, hne, hreachable, hdisagrees,
      hagrees, hstrict, hother, _hconfined⟩
  exact ⟨repaired, gainedPartner, hne, hreachable, hdisagrees,
    hagrees, hstrict, hother⟩

/-- All ambient edges on which at least one ordered pair of the nine current
deletion colourings disagrees. -/
noncomputable def NineSiteAmbientDisagreementUnion
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.biUnion fun pair : Fin 9 × Fin 9 =>
    ambientDisagreementSupport
      (rowSiteData rotation minimal ordered row slot pair.1)
      (rowSiteData rotation minimal ordered row slot pair.2)
      (assignment pair.1).1 (assignment pair.2).1

theorem mem_nineSiteAmbientDisagreementUnion_iff
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot)
    (edge : G.edgeSet) :
    edge ∈ NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot assignment ↔
      ∃ first second : Fin 9,
        edge ∈ ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          (assignment first).1 (assignment second).1 := by
  classical
  simp [NineSiteAmbientDisagreementUnion]

/-- A confined one-coordinate repair cannot introduce a new ambient edge
into the union of pairwise disagreement supports. -/
theorem nineSiteAmbientDisagreementUnion_antitone
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteConfinedStrictRepairStep
      rotation minimal ordered row slot source target) :
    NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot target ⊆
      NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot source := by
  classical
  rcases hstep with
    ⟨repaired, gainedPartner, hne, _hreachable, _hsourceDisagrees,
      htargetGainedAgreesSource, _hstrict, hother, hconfined⟩
  intro edge hedge
  rcases (mem_nineSiteAmbientDisagreementUnion_iff
      rotation minimal ordered row slot target edge).1 hedge with
    ⟨first, second, hedgePair⟩
  have hsourceGained : CommonCoreAgrees
      (rowSiteData rotation minimal ordered row slot repaired)
      (rowSiteData rotation minimal ordered row slot gainedPartner)
      (target repaired).1 (source gainedPartner).1 :=
    htargetGainedAgreesSource
  have hincident (partner : Fin 9) (hpartner : partner ≠ repaired)
      (hpair : edge ∈ ambientDisagreementSupport
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot partner)
        (target repaired).1 (target partner).1) :
      edge ∈ NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot source := by
    have hpartnerEq : target partner = source partner :=
      hother partner hpartner
    have hpairSourcePartner : edge ∈ ambientDisagreementSupport
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot partner)
        (target repaired).1 (source partner).1 := by
      simpa [hpartnerEq] using hpair
    have htransport :=
      ambientDisagreementSupport_subset_union_of_confined_left_update
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot partner)
        (source repaired).1 (target repaired).1
        (source gainedPartner).1 (source partner).1
        hsourceGained hconfined hpairSourcePartner
    rcases Finset.mem_union.1 htransport with hold | hgained
    · exact (mem_nineSiteAmbientDisagreementUnion_iff
        rotation minimal ordered row slot source edge).2
          ⟨repaired, partner, hold⟩
    · exact (mem_nineSiteAmbientDisagreementUnion_iff
        rotation minimal ordered row slot source edge).2
          ⟨gainedPartner, partner, hgained⟩
  by_cases hfirst : first = repaired
  · subst first
    by_cases hsecond : second = repaired
    · subst second
      have hempty := ambientDisagreementSupport_self
        (rowSiteData rotation minimal ordered row slot repaired)
        (target repaired).1
      have : edge ∈ (∅ : Finset G.edgeSet) := by
        rwa [← hempty]
      simp at this
    · exact hincident second hsecond hedgePair
  · by_cases hsecond : second = repaired
    · subst second
      have horiented : edge ∈ ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot first)
          (target repaired).1 (target first).1 := by
        rw [← ambientDisagreementSupport_symm]
        exact hedgePair
      exact hincident first hfirst horiented
    · have hfirstEq : target first = source first := hother first hfirst
      have hsecondEq : target second = source second := hother second hsecond
      apply (mem_nineSiteAmbientDisagreementUnion_iff
        rotation minimal ordered row slot source edge).2
      refine ⟨first, second, ?_⟩
      simpa [hfirstEq, hsecondEq] using hedgePair

/-- The ambient disagreement union is antitone along every finite confined
repair run. -/
theorem reflTransGen_nineSiteAmbientDisagreementUnion_antitone
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (run : Relation.ReflTransGen
      (NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot) source target) :
    NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot target ⊆
      NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot source := by
  induction run with
  | refl => exact Finset.Subset.rfl
  | tail run step ih =>
      intro edge hedge
      exact ih (nineSiteAmbientDisagreementUnion_antitone
        rotation minimal ordered row slot step hedge)

/-- Every displayed step inside a closed confined-repair run preserves the
whole ambient disagreement carrier exactly. -/
theorem nineSiteAmbientDisagreementUnion_eq_of_step_in_closed_run
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {base source target :
      NineSiteTaitAssignment rotation minimal ordered row slot}
    (outboundRun : Relation.ReflTransGen
      (NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot) base source)
    (step : NineSiteConfinedStrictRepairStep
      rotation minimal ordered row slot source target)
    (returnRun : Relation.ReflTransGen
      (NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot) target base) :
    NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot target =
      NineSiteAmbientDisagreementUnion
        rotation minimal ordered row slot source := by
  apply Finset.Subset.antisymm
  · exact nineSiteAmbientDisagreementUnion_antitone
      rotation minimal ordered row slot step
  · exact (reflTransGen_nineSiteAmbientDisagreementUnion_antitone
      rotation minimal ordered row slot outboundRun).trans
        (reflTransGen_nineSiteAmbientDisagreementUnion_antitone
          rotation minimal ordered row slot returnRun)

/-- A nonempty closed confined-repair chain has a first step which preserves
the full ambient disagreement carrier. -/
theorem exists_carrierPreservingStep_of_confinedRepairCycle
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (source : NineSiteTaitAssignment rotation minimal ordered row slot)
    (cycle : Relation.TransGen
      (NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot) source source) :
    ∃ target,
      NineSiteConfinedStrictRepairStep
          rotation minimal ordered row slot source target ∧
        NineSiteAmbientDisagreementUnion
            rotation minimal ordered row slot target =
          NineSiteAmbientDisagreementUnion
            rotation minimal ordered row slot source := by
  rcases (Relation.TransGen.head'_iff).1 cycle with
    ⟨target, step, returnRun⟩
  exact ⟨target, step,
    nineSiteAmbientDisagreementUnion_eq_of_step_in_closed_run
      rotation minimal ordered row slot Relation.ReflTransGen.refl
        step returnRun⟩

/-- Every nine-site state either exposes the geometric horns or has a
confined strict-repair successor. -/
theorem branchingOrBoundary_or_exists_confinedStrictRepairStep
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) :
    HasNineSiteBranchingOrBoundary rotation minimal ordered row slot assignment ∨
      ∃ target, NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot assignment target := by
  let coloring := fun index : Fin 9 => (assignment index).1
  have tait : ∀ index : Fin 9,
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex)
        (coloring index) := fun index => (assignment index).2
  obtain ⟨first, second, hne, hdisagrees, _oldResidue⟩ :=
    exists_taitCommonCoreResidue_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  rcases branching_or_taitReachesSecondPair_or_strictConfinedTaitRepair
      (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)
      (coloring first) (coloring second) (tait first) (tait second)
      hdisagrees with
    hbranch | hboundary | hrepair
  · exact Or.inl ⟨first, second, Or.inl hbranch⟩
  · exact Or.inl ⟨first, second, Or.inr hboundary⟩
  · right
    rcases hrepair with
      ⟨repaired, hreachable, hrepairedTait, hagrees, hstrict, hconfined⟩
    let target : NineSiteTaitAssignment rotation minimal ordered row slot :=
      Function.update assignment first ⟨repaired, hrepairedTait⟩
    refine ⟨target, first, second, hne, ?_, hdisagrees, ?_, ?_, ?_, ?_⟩
    · simpa [target] using hreachable
    · simpa [target, coloring] using hagrees
    · simpa [target] using hstrict
    · intro index hindex
      simp [target, hindex]
    · simpa [target] using hconfined

/-- If the geometric horns are absent from every state, the confined repair
relation has a nonempty directed cycle. -/
theorem exists_confinedStrictRepairCycle_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ assignment,
      Relation.TransGen
        (NineSiteConfinedStrictRepairStep
          rotation minimal ordered row slot) assignment assignment := by
  let initial : NineSiteTaitAssignment rotation minimal ordered row slot :=
    fun index =>
      ⟨(selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot index))).base,
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot index))).baseTait⟩
  letI : Nonempty
      (NineSiteTaitAssignment rotation minimal ordered row slot) := ⟨initial⟩
  letI : Fintype
      (NineSiteTaitAssignment rotation minimal ordered row slot) := by
    unfold NineSiteTaitAssignment
    infer_instance
  apply exists_transGen_cycle_of_finite_serial
  intro assignment
  exact (branchingOrBoundary_or_exists_confinedStrictRepairStep
    rotation minimal ordered row slot assignment).resolve_left (hno assignment)

/-- A closed run of confined repairs still has a collateral agreement loss,
because forgetting confinement gives the old strictly-growing agreement
argument. -/
theorem exists_collateralAgreementLoss_of_confinedStrictRepairCycle
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {assignment : NineSiteTaitAssignment rotation minimal ordered row slot}
    (cycle : Relation.TransGen
      (NineSiteConfinedStrictRepairStep rotation minimal ordered row slot)
      assignment assignment) :
    ∃ source target,
      NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot source target ∧
      HasCollateralAgreementLoss
        rotation minimal ordered row slot source target := by
  by_contra hnone
  have hnoLoss : ∀ {source target},
      NineSiteConfinedStrictRepairStep
          rotation minimal ordered row slot source target →
        ¬ HasCollateralAgreementLoss
          rotation minimal ordered row slot source target := by
    intro source target hstep hloss
    exact hnone ⟨source, target, hstep, hloss⟩
  have hstrictRun {source target}
      (run : Relation.TransGen
        (NineSiteConfinedStrictRepairStep
          rotation minimal ordered row slot) source target) :
      NineSiteAgreementPairs rotation minimal ordered row slot source ⊂
        NineSiteAgreementPairs rotation minimal ordered row slot target := by
    induction run with
    | single hstep =>
        exact nineSiteAgreementPairs_ssubset_of_not_collateralLoss
          rotation minimal ordered row slot hstep.toStrictRepairStep
          (hnoLoss hstep)
    | tail hpath hstep ih =>
        exact ih.trans
          (nineSiteAgreementPairs_ssubset_of_not_collateralLoss
            rotation minimal ordered row slot hstep.toStrictRepairStep
            (hnoLoss hstep))
  have himpossible := hstrictRun cycle
  exact himpossible.ne rfl

/-- Common-core disagreement is irreflexive at one site and one colouring. -/
theorem not_commonCoreColoringsDisagree_self
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) :
    ¬ CommonCoreColoringsDisagree data data coloring coloring := by
  apply (commonCoreAgrees_iff_not_coloringsDisagree
    data data coloring coloring).1
  apply (commonCoreAgrees_iff_ambient data data coloring coloring).2
  intro _edge _hfirst _hsecond
  rfl

/-- **Forced disagreement propagation.**  With branching and boundary
reaching globally absent, an anchored periodic repair cannot lose agreement
only inside its gained partner's deleted footprint.  Some repair therefore
ends with its gained and lost partners disagreeing on their exact common
deletion. -/
theorem exists_partnerDisagreement_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ source target repaired gainedPartner lostPartner,
      NineSiteConfinedStrictRepairStep
        rotation minimal ordered row slot source target ∧
      repaired ≠ gainedPartner ∧
      CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target gainedPartner).1 (target lostPartner).1 ∧
      ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (target repaired).1 (target lostPartner).1 ⊆
        ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (target gainedPartner).1 (target lostPartner).1 := by
  obtain ⟨assignment, cycle⟩ :=
    exists_confinedStrictRepairCycle_of_no_branchingOrBoundary
      rotation minimal ordered row slot hno
  obtain ⟨source, target, hstep, hloss⟩ :=
    exists_collateralAgreementLoss_of_confinedStrictRepairCycle
      rotation minimal ordered row slot cycle
  rcases hstep with
    ⟨repaired, gainedPartner, hne, hreachable, hsourceGainedDisagrees,
      htargetGainedAgreesSource, hstrict, hother, hconfined⟩
  rcases hloss with
    ⟨lostFirst, lostSecond, hsourceLostAgrees, htargetLostDisagrees⟩
  have hlossTouches : lostFirst = repaired ∨ lostSecond = repaired := by
    by_contra hnot
    push Not at hnot
    apply hsourceLostAgrees
    simpa [hother lostFirst hnot.1, hother lostSecond hnot.2] using
      htargetLostDisagrees
  have hpropagate (lostPartner : Fin 9)
      (hlostNe : lostPartner ≠ repaired)
      (hsourceRepairedLostAgrees :
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (source repaired).1 (source lostPartner).1)
      (htargetRepairedLostDisagrees :
        CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (target repaired).1 (target lostPartner).1) :
      CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target gainedPartner).1 (target lostPartner).1 := by
    by_contra hpartnerAgrees
    have hgainedEq : target gainedPartner = source gainedPartner :=
      hother gainedPartner hne.symm
    have hlostEq : target lostPartner = source lostPartner :=
      hother lostPartner hlostNe
    have hrepairGained : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (target repaired).1 (target gainedPartner).1 := by
      rw [hgainedEq]
      exact htargetGainedAgreesSource
    have hgainedLost : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target gainedPartner).1 (target lostPartner).1 :=
      (commonCoreAgrees_iff_not_coloringsDisagree
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target gainedPartner).1 (target lostPartner).1).2 hpartnerAgrees
    have hbefore : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (source repaired).1 (source lostPartner).1 :=
      (commonCoreAgrees_iff_not_coloringsDisagree
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (source repaired).1 (source lostPartner).1).2
        hsourceRepairedLostAgrees
    have hafterOldLost := commonCoreAgrees_of_confined_left_update
      (rowSiteData rotation minimal ordered row slot repaired)
      (rowSiteData rotation minimal ordered row slot gainedPartner)
      (rowSiteData rotation minimal ordered row slot lostPartner)
      (source repaired).1 (target repaired).1
      (target gainedPartner).1 (source lostPartner).1
      hrepairGained (by simpa [hlostEq] using hgainedLost)
      hbefore hconfined
    have hafter : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target repaired).1 (target lostPartner).1 := by
      simpa [hlostEq] using hafterOldLost
    exact htargetRepairedLostDisagrees hafter
  have hpropagateSupport (lostPartner : Fin 9)
      (hlostNe : lostPartner ≠ repaired)
      (hsourceRepairedLostAgrees :
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (source repaired).1 (source lostPartner).1) :
      ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (target repaired).1 (target lostPartner).1 ⊆
        ambientDisagreementSupport
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostPartner)
          (target gainedPartner).1 (target lostPartner).1 := by
    have hgainedEq : target gainedPartner = source gainedPartner :=
      hother gainedPartner hne.symm
    have hlostEq : target lostPartner = source lostPartner :=
      hother lostPartner hlostNe
    have hrepairGained : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (target repaired).1 (source gainedPartner).1 :=
      htargetGainedAgreesSource
    have hbefore : CommonCoreAgrees
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (source repaired).1 (source lostPartner).1 :=
      (commonCoreAgrees_iff_not_coloringsDisagree
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (source repaired).1 (source lostPartner).1).2
        hsourceRepairedLostAgrees
    simpa [hgainedEq, hlostEq] using
      (ambientDisagreementSupport_subset_of_confined_left_update
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (source repaired).1 (target repaired).1
        (source gainedPartner).1 (source lostPartner).1
        hrepairGained hbefore hconfined)
  rcases hlossTouches with hfirst | hsecond
  · subst lostFirst
    have hlostNe : lostSecond ≠ repaired := by
      intro heq
      subst lostSecond
      exact (not_commonCoreColoringsDisagree_self
        (rowSiteData rotation minimal ordered row slot repaired)
        (target repaired).1) htargetLostDisagrees
    exact ⟨source, target, repaired, gainedPartner, lostSecond,
      ⟨repaired, gainedPartner, hne, hreachable,
        hsourceGainedDisagrees, htargetGainedAgreesSource, hstrict,
        hother, hconfined⟩,
      hne, hpropagate lostSecond hlostNe
        hsourceLostAgrees htargetLostDisagrees,
      hpropagateSupport lostSecond hlostNe hsourceLostAgrees⟩
  · subst lostSecond
    have hlostNe : lostFirst ≠ repaired := by
      intro heq
      subst lostFirst
      exact (not_commonCoreColoringsDisagree_self
        (rowSiteData rotation minimal ordered row slot repaired)
        (target repaired).1) htargetLostDisagrees
    have hsourceOriented :
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostFirst)
          (source repaired).1 (source lostFirst).1 := by
      apply (commonCoreAgrees_iff_not_coloringsDisagree
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot lostFirst)
        (source repaired).1 (source lostFirst).1).1
      apply commonCoreAgrees_symm
      exact (commonCoreAgrees_iff_not_coloringsDisagree
        (rowSiteData rotation minimal ordered row slot lostFirst)
        (rowSiteData rotation minimal ordered row slot repaired)
        (source lostFirst).1 (source repaired).1).2 hsourceLostAgrees
    have htargetOriented := coloringsDisagree_symm
      (rowSiteData rotation minimal ordered row slot lostFirst)
      (rowSiteData rotation minimal ordered row slot repaired)
      (target lostFirst).1 (target repaired).1 htargetLostDisagrees
    exact ⟨source, target, repaired, gainedPartner, lostFirst,
      ⟨repaired, gainedPartner, hne, hreachable,
        hsourceGainedDisagrees, htargetGainedAgreesSource, hstrict,
        hother, hconfined⟩,
      hne, hpropagate lostFirst hlostNe
        hsourceOriented htargetOriented,
      hpropagateSupport lostFirst hlostNe hsourceOriented⟩

end

end GoertzelV24OrderedMeshConfinedRepairPropagation

end Mettapedia.GraphTheory.FourColor
